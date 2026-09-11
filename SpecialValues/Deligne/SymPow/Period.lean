/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Order.ArchimedeanDiscrete

/-!
# The real and imaginary periods of a lattice

Deligne's conjecture for `Sym^k h¹(E)` divides its transcendental part by the periods `Ω⁺` and
`Ω⁻` of `E`, so a faithful statement of it needs those two numbers to be *determined* by the
lattice rather than supplied by hand: an `Ω⁺` free to be chosen could be chosen to be the
`L`-value, and the conjecture would say nothing. This file pins them down, on mathlib's
`PeriodPair`.

`IsRealPeriod Λ Ω` says that the real elements of `Λ` are exactly the integer multiples of `Ω`,
and `IsImagPeriod Λ Ω` says the same of the purely imaginary ones. `PeriodPair.realPeriod` and
`PeriodPair.imagPeriod` then *derive* the two periods from the lattice rather than leaving them
to be supplied, which is what lets a statement about an elliptic curve name them.
`IsRealPeriod.unique` and `IsImagPeriod.unique` are what make these hypotheses determining: two
real periods of the same lattice differ by a sign, and the sign is absorbed by the rescaling
theorem of `blueprint/src/sympow.tex` §`thm:conjecture-rescale`.

## Existence

Unlike the `L`-function of `SpecialValues/Deligne/SymPow/LFunction.lean`, whose existence is
symmetric power functoriality and is assumed, the periods exist unconditionally:
`PeriodPair.exists_isRealPeriod` and `PeriodPair.exists_isImagPeriod` produce them for every
`PeriodPair`. The mechanism is `AddSubgroup.exists_inf_span_eq_zmultiples` — a discrete
additive subgroup of a real normed space meets a real line in an infinite cyclic subgroup —
applied to the lines `ℝ ∙ 1` and `ℝ ∙ I`. Discreteness is mathlib's
`instance : DiscreteTopology L.lattice`.

What is *not* unconditional is that the periods are nonzero, and the reason is that a
`PeriodPair` need not be stable under complex conjugation. `IsRealPeriod.ne_zero` and
`IsImagPeriod.ne_zero` therefore carry stability as an explicit hypothesis. For the lattice of
an elliptic curve over `ℚ` it holds, but deriving it from `PeriodPair.Uniformises` needs the
uniformisation theorem, which mathlib does not have; see `blueprint/src/sympow.tex`
§`rem:lattice-conj`.

## Main results

* `AddSubgroup.exists_inf_span_eq_zmultiples`: a discrete additive subgroup of a real normed
  space meets a real line in an infinite cyclic subgroup.
* `PeriodPair.Uniformises`: the hypothesis fixing which lattice is the period lattice of a
  Weierstrass model `y² = 4x³ - g₂ x - g₃`.
* `IsRealPeriod`, `IsImagPeriod`, and `IsRealPeriod.unique`, `IsImagPeriod.unique`.
* `PeriodPair.exists_isRealPeriod`, `PeriodPair.exists_isImagPeriod`.
* `PeriodPair.realPeriod`, `PeriodPair.imagPeriod`, the periods themselves, with
  `IsRealPeriod.eq_or_eq_neg_realPeriod` and `IsImagPeriod.eq_or_eq_neg_imagPeriod` bounding the
  choice they make to a sign, and `PeriodPair.realPeriod_ne_zero`,
  `PeriodPair.imagPeriod_ne_zero`.
-/

open Complex ComplexConjugate Topology

/-! ### Discrete subgroups meet a line in a cyclic group -/

section Line

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A discrete additive subgroup of a real normed space meets the line `ℝ ∙ v` in an infinite
cyclic subgroup. -/
theorem AddSubgroup.exists_inf_span_eq_zmultiples (Λ : AddSubgroup E) [DiscreteTopology Λ]
    {v : E} (hv : v ≠ 0) :
    ∃ w : E, Λ ⊓ (ℝ ∙ v).toAddSubgroup = AddSubgroup.zmultiples w := by
  set S : AddSubgroup ℝ := Λ.comap (LinearMap.toSpanSingleton ℝ E v).toAddMonoidHom
  have hmemS : ∀ t : ℝ, t ∈ S ↔ t • v ∈ Λ := fun _ ↦ Iff.rfl
  have : DiscreteTopology S := by
    have hemb : IsEmbedding fun t : S ↦ ((t : ℝ) • v : E) :=
      (isClosedEmbedding_smul_left hv).isEmbedding.comp IsEmbedding.subtypeVal
    have : DiscreteTopology ((Λ : Set E)) := inferInstanceAs (DiscreteTopology Λ)
    exact (hemb.codRestrict (Λ : Set E) fun t ↦ (hmemS t).mp t.2).discreteTopology
  obtain ⟨a, ha⟩ := S.isAddCyclic_iff_exists_zmultiples_eq_top.mp
    (AddSubgroup.discrete_iff_addCyclic.mpr inferInstance)
  refine ⟨a • v, ?_⟩
  ext z
  simp only [AddSubgroup.mem_inf, Submodule.mem_toAddSubgroup, Submodule.mem_span_singleton,
    AddSubgroup.mem_zmultiples_iff]
  constructor
  · rintro ⟨hz, t, rfl⟩
    have ht : t ∈ S := (hmemS t).mpr hz
    rw [← ha] at ht
    obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp ht
    exact ⟨n, by rw [← smul_assoc, hn]⟩
  · rintro ⟨n, rfl⟩
    have hmul : (n • a) • v = n • (a • v) := smul_assoc n a v
    refine ⟨?_, n • a, hmul⟩
    rw [← hmul]
    exact (hmemS _).mp (ha ▸ AddSubgroup.mem_zmultiples_iff.mpr ⟨n, rfl⟩)

end Line

/-! ### Uniformisation -/

namespace PeriodPair

/-- `L` uniformises the Weierstrass model `y² = 4x³ - g₂ x - g₃` when its lattice invariants are
`g₂` and `g₃`. -/
def Uniformises (L : PeriodPair) (g₂ g₃ : ℚ) : Prop := L.g₂ = g₂ ∧ L.g₃ = g₃

end PeriodPair

/-! ### The two periods -/

/-- `Ω` is a real period of the lattice `Λ`: the real elements of `Λ` are exactly the integer
multiples of `Ω`. -/
def IsRealPeriod (Λ : Submodule ℤ ℂ) (Ω : ℂ) : Prop :=
  Λ.toAddSubgroup ⊓ (ℝ ∙ (1 : ℂ)).toAddSubgroup = AddSubgroup.zmultiples Ω

/-- `Ω` is an imaginary period of the lattice `Λ`: the purely imaginary elements of `Λ` are
exactly the integer multiples of `Ω`. -/
def IsImagPeriod (Λ : Submodule ℤ ℂ) (Ω : ℂ) : Prop :=
  Λ.toAddSubgroup ⊓ (ℝ ∙ I).toAddSubgroup = AddSubgroup.zmultiples Ω

variable {Λ : Submodule ℤ ℂ} {Ω Ω₁ Ω₂ : ℂ}

/-- The generator of a cyclic additive subgroup lies in it. -/
private theorem mem_of_eq_zmultiples {M : Type*} [AddGroup M] {A : AddSubgroup M} {x : M}
    (h : A = AddSubgroup.zmultiples x) : x ∈ A := h ▸ AddSubgroup.mem_zmultiples x

theorem IsRealPeriod.mem (h : IsRealPeriod Λ Ω) : Ω ∈ Λ := (mem_of_eq_zmultiples h).1

theorem IsImagPeriod.mem (h : IsImagPeriod Λ Ω) : Ω ∈ Λ := (mem_of_eq_zmultiples h).1

theorem IsRealPeriod.conj_eq (h : IsRealPeriod Λ Ω) : conj Ω = Ω := by
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp (mem_of_eq_zmultiples h).2
  rw [← ht]
  simp

theorem IsImagPeriod.conj_eq_neg (h : IsImagPeriod Λ Ω) : conj Ω = -Ω := by
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp (mem_of_eq_zmultiples h).2
  rw [← ht]
  simp

/-- Two generators of the same cyclic subgroup of a torsion-free group differ by a unit of `ℤ`. -/
private theorem eq_or_eq_neg_of_zmultiples_eq {M : Type*} [AddCommGroup M] [IsAddTorsionFree M]
    {x y : M} (h : AddSubgroup.zmultiples x = AddSubgroup.zmultiples y) : x = y ∨ x = -y := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact Or.inl (by simpa [eq_comm] using mem_of_eq_zmultiples h)
  · rcases (AddSubgroup.zmultiples_eq_zmultiples_iff
      (not_isOfFinAddOrder_of_isAddTorsionFree hx)).mp h with h' | h'
    · exact Or.inl h'
    · exact Or.inr (by rw [← h', neg_neg])

theorem IsRealPeriod.unique (h₁ : IsRealPeriod Λ Ω₁) (h₂ : IsRealPeriod Λ Ω₂) :
    Ω₁ = Ω₂ ∨ Ω₁ = -Ω₂ :=
  eq_or_eq_neg_of_zmultiples_eq (h₁.symm.trans h₂)

theorem IsImagPeriod.unique (h₁ : IsImagPeriod Λ Ω₁) (h₂ : IsImagPeriod Λ Ω₂) :
    Ω₁ = Ω₂ ∨ Ω₁ = -Ω₂ :=
  eq_or_eq_neg_of_zmultiples_eq (h₁.symm.trans h₂)

/-! ### Existence -/

namespace PeriodPair

variable (L : PeriodPair)

instance : DiscreteTopology L.lattice.toAddSubgroup :=
  inferInstanceAs (DiscreteTopology L.lattice)

theorem exists_isRealPeriod : ∃ Ω, IsRealPeriod L.lattice Ω :=
  L.lattice.toAddSubgroup.exists_inf_span_eq_zmultiples one_ne_zero

theorem exists_isImagPeriod : ∃ Ω, IsImagPeriod L.lattice Ω :=
  L.lattice.toAddSubgroup.exists_inf_span_eq_zmultiples I_ne_zero

/-- A generator of the subgroup of real elements of the lattice of `L`. -/
noncomputable def realPeriod : ℂ := L.exists_isRealPeriod.choose

/-- A generator of the subgroup of purely imaginary elements of the lattice of `L`. -/
noncomputable def imagPeriod : ℂ := L.exists_isImagPeriod.choose

theorem isRealPeriod_realPeriod : IsRealPeriod L.lattice L.realPeriod :=
  L.exists_isRealPeriod.choose_spec

theorem isImagPeriod_imagPeriod : IsImagPeriod L.lattice L.imagPeriod :=
  L.exists_isImagPeriod.choose_spec

end PeriodPair

/-- Every real period of the lattice of `L` is `± L.realPeriod`, so the choice in
`PeriodPair.realPeriod` is a choice of sign and nothing more. -/
theorem IsRealPeriod.eq_or_eq_neg_realPeriod {L : PeriodPair} (h : IsRealPeriod L.lattice Ω) :
    Ω = L.realPeriod ∨ Ω = -L.realPeriod :=
  h.unique L.isRealPeriod_realPeriod

/-- Every imaginary period of the lattice of `L` is `± L.imagPeriod`. -/
theorem IsImagPeriod.eq_or_eq_neg_imagPeriod {L : PeriodPair} (h : IsImagPeriod L.lattice Ω) :
    Ω = L.imagPeriod ∨ Ω = -L.imagPeriod :=
  h.unique L.isImagPeriod_imagPeriod

/-! ### Nondegeneracy -/

/-- The two periods of a `PeriodPair` are `ℝ`-independent, so its lattice is not contained in
any real line. -/
private theorem PeriodPair.not_forall_mem_lattice_smul (L : PeriodPair) (v : ℂ) :
    ¬ ∀ z ∈ L.lattice, ∃ t : ℝ, z = t • v := by
  intro hline
  obtain ⟨t₁, h₁⟩ := hline L.ω₁ L.ω₁_mem_lattice
  obtain ⟨t₂, h₂⟩ := hline L.ω₂ L.ω₂_mem_lattice
  obtain ⟨-, e₂⟩ := LinearIndependent.pair_iff.mp L.indep t₂ (-t₁)
    (by rw [h₁, h₂, smul_smul, smul_smul]; module)
  exact L.indep.ne_zero 0 (by simp [h₁, neg_eq_zero.mp e₂])

theorem IsRealPeriod.ne_zero {L : PeriodPair} (h : IsRealPeriod L.lattice Ω)
    (hconj : ∀ z ∈ L.lattice, conj z ∈ L.lattice) : Ω ≠ 0 := by
  rintro rfl
  -- with `Ω = 0` the real elements of the lattice are just `0`, so `z + conj z = 2 Re z` vanishes
  -- for every `z` in it and the whole lattice lies on the line `ℝ ∙ I`.
  refine L.not_forall_mem_lattice_smul I fun z hz ↦ ⟨z.im, ?_⟩
  have hmem : z + conj z ∈ L.lattice.toAddSubgroup ⊓ (ℝ ∙ (1 : ℂ)).toAddSubgroup :=
    AddSubgroup.mem_inf.mpr ⟨add_mem hz (hconj z hz), Submodule.mem_span_singleton.mpr
      ⟨2 * z.re, by rw [Complex.add_conj, Complex.real_smul, mul_one]⟩⟩
  rw [h, AddSubgroup.zmultiples_zero_eq_bot] at hmem
  have hre : z.re = 0 := by
    have hz0 := AddSubgroup.mem_bot.mp hmem
    rw [Complex.add_conj] at hz0
    simpa using hz0
  refine Complex.ext ?_ ?_
  · simpa using hre
  · simp

theorem IsImagPeriod.ne_zero {L : PeriodPair} (h : IsImagPeriod L.lattice Ω)
    (hconj : ∀ z ∈ L.lattice, conj z ∈ L.lattice) : Ω ≠ 0 := by
  rintro rfl
  -- dually, `z - conj z = 2 i Im z` vanishes and the lattice lies on the real line `ℝ ∙ 1`.
  refine L.not_forall_mem_lattice_smul 1 fun z hz ↦ ⟨z.re, ?_⟩
  have hmem : z - conj z ∈ L.lattice.toAddSubgroup ⊓ (ℝ ∙ I).toAddSubgroup :=
    AddSubgroup.mem_inf.mpr ⟨sub_mem hz (hconj z hz), Submodule.mem_span_singleton.mpr
      ⟨2 * z.im, by rw [Complex.sub_conj, Complex.real_smul]⟩⟩
  rw [h, AddSubgroup.zmultiples_zero_eq_bot] at hmem
  have him : z.im = 0 := by
    have hz0 := AddSubgroup.mem_bot.mp hmem
    rw [Complex.sub_conj] at hz0
    simpa using hz0
  refine Complex.ext ?_ ?_
  · simp
  · simpa using him

namespace PeriodPair

theorem realPeriod_ne_zero {L : PeriodPair}
    (hconj : ∀ z ∈ L.lattice, conj z ∈ L.lattice) : L.realPeriod ≠ 0 :=
  L.isRealPeriod_realPeriod.ne_zero hconj

theorem imagPeriod_ne_zero {L : PeriodPair}
    (hconj : ∀ z ∈ L.lattice, conj z ∈ L.lattice) : L.imagPeriod ≠ 0 :=
  L.isImagPeriod_imagPeriod.ne_zero hconj

end PeriodPair
