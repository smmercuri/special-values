/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import SpecialValues.Deligne.Gamma
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.FieldTheory.Galois.Notation
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs

/-!
# The shared framework for Deligne's conjecture

Deligne's conjecture is a single assertion instantiated at many different classes of motive.
This file isolates the data and the assertions that every instance shares, so that GL(1),
GL(2), Hecke characters and the rest are *instances* rather than restatements.

Mathlib has no category of motives, and none is built here. A `Deligne.Pkg` is the tuple
`(L, E, w, γ, c, σ)` — an `L`-function, a value field, a weight, the shifts of an archimedean
Gamma factor, a period and a Galois action on a type `Ω` of objects — which is exactly the data
required to state the conjecture for the objects of `Ω`. In the literature the objects are
motives and most of these fields are derived from them; in lieu of a formal definition of a
motive, the expected behaviour of the data is characterised through proposition fields.

The Galois action is a field rather than a `MulAction` instance, because an instance almost
always defines its action explicitly and the action is not canonical in `Ω`. It is a genuine
action of `Gal(ℂ/ℚ)` — a monoid homomorphism into `Equiv.Perm Ω` — so `galoisAction σ` is
invertible, with inverse `galoisAction σ⁻¹`.

## Main definitions

* `Deligne.Pkg`: the data of Deligne's conjecture for a type of objects, with the value fields
  required to consist of algebraic numbers and the periods required not to vanish at critical
  integers.
* `Deligne.Pkg.IsCritical`: the critical integers, *computed* from the Gamma factor rather than
  supplied. Criticality is the absence of a pole of the archimedean factor at the two points `n`
  and `w + 1 - n` exchanged by the functional equation, and that is what it says: the order in
  mathlib's sense (`meromorphicOrderAt`) is non-negative at both. An instance cannot choose its
  own critical set, because it supplies the Hodge data — the shifts and the weight — rather than
  a function: for GL(1), the shifts of mathlib's own `DirichletCharacter.gammaFactor`, see
  `Deligne.GL1.gammaFactor_pkg`. `Deligne.Pkg.isCritical_iff` turns the condition into arithmetic
  on the shifts, which is the form an instance checks it in.
* `Deligne.Pkg.normalizedValue`: the critical value divided by its period.
* `Deligne.Pkg.IsArithmetic`, `Deligne.Pkg.IsEquivariant`: the two halves of the conjecture,
  and `Deligne.Pkg.Conjecture` their conjunction.
* `Deligne.Pkg.IsArithmetic.isAlgebraic`: algebraicity asserts at least that the normalised
  critical value is algebraic, whatever value field an instance chooses.
* `Deligne.Pkg.isCritical_galoisAction_iff`: criticality is invariant under the Galois action,
  a consequence of the field `gammaShifts_galoisAction`.
* `Deligne.Pkg.HasCriticalInteger`: the object has a critical integer at all.
* `Deligne.Pkg.conjecture_of_forall_not_isCritical`, `Deligne.Pkg.conjecture_of_L_eq_zero`,
  `Deligne.Pkg.conjecture_of_period_eq_mul_L`: the trivial cases — no critical integers, a
  vanishing `L`-function, or a period that is a rescaling of the `L`-value on the Galois orbit
  of `M`.
* `Deligne.Pkg.IsArithmetic.isEquivariant_of_valueField_eq_bot`: over the value field `ℚ`,
  equivariance follows from algebraicity.

## Design notes

The design arguments — why the `L`-function is a field although
`Deligne.Pkg.conjecture_of_period_eq_mul_L` shows no field law can stop a period being defined
from it, why nondegeneracy is a predicate (`Deligne.Pkg.HasCriticalInteger`) rather than a field,
and why the value field is bounded by `valueField_isAlgebraic` — are set out in
`blueprint/src/framework.tex`, §§`sec:no-L-field` and `sec:guards`. Direct sums of packages,
Galois descent and rescaling by rationals live on the `pkg-extras` branch. The one obligation
the framework cannot state is recorded here: every instance proves
`Deligne.Pkg.HasCriticalInteger` alongside its main theorem, together with a characterisation
theorem identifying its `IsCritical` with an independently and concretely specified condition,
stated without reference to this framework.
-/

/-! ### Intermediate fields and the rationals -/

namespace IntermediateField

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- An `F`-algebra endomorphism of `E` fixes the bottom intermediate field pointwise. -/
theorem apply_eq_self_of_mem_bot (f : E →ₐ[F] E) {x : E} (hx : x ∈ (⊥ : IntermediateField F E)) :
    f x = x := by
  obtain ⟨q, rfl⟩ := mem_bot.mp hx
  exact f.commutes q

/-- The elements of the bottom intermediate field are algebraic. -/
theorem isAlgebraic_of_mem_bot {x : E} (hx : x ∈ (⊥ : IntermediateField F E)) :
    IsAlgebraic F x := by
  obtain ⟨q, rfl⟩ := mem_bot.mp hx
  exact isAlgebraic_algebraMap q

/-- An intermediate field is algebraic over `F` exactly when it lies in the algebraic closure
of `F` in `E`. -/
theorem forall_isAlgebraic_iff_le {s : IntermediateField F E} :
    (∀ x ∈ s, IsAlgebraic F x) ↔ s ≤ algebraicClosure F E :=
  forall₂_congr fun _ _ ↦ mem_algebraicClosure_iff.symm

end IntermediateField

/-! ### The framework -/

namespace Deligne

/-- A Deligne package on a type `Ω` of objects is the tuple `(L, E, w, γ, c, σ)` of an
`L`-function, a value field, a weight, the shifts of a Gamma factor, a period and a Galois action
on `Ω`: the data required to state Deligne's conjecture for the objects of `Ω`, thought of as
pure motives over `ℚ` of a common weight `w`. -/
structure Pkg (Ω : Type*) where
  /-- The analytic `L`-function `L(M, s)`. -/
  L : Ω → ℂ → ℂ
  /-- The value field `E(M)`. -/
  valueField : Ω → IntermediateField ℚ ℂ
  /-- The weight `w(M)`: the functional equation exchanges `s` and `w(M) + 1 - s`. -/
  weight : Ω → ℤ
  /-- The shifts of the archimedean Gamma factor, `γ(M, s) = ∏ a, Γℝ(s + a)` with `a` ranging over
  `gammaShifts M` with multiplicity. Supplying the shifts rather than a bare function `ℂ → ℂ` is
  what makes `Deligne.Pkg.IsCritical` genuinely computed; see
  `Complex.meromorphicOrderAt_prodGammaℝ_nonneg_iff`. -/
  gammaShifts : Ω → Multiset ℤ
  /-- Deligne's period `c⁺(M(n))`. -/
  period : Ω → ℤ → ℂ
  /-- The Galois action `σ ↦ (M ↦ Mᵟ)`. -/
  galoisAction : Gal(ℂ/ℚ) →* Equiv.Perm Ω
  /-- Conjugate objects have the same weight. -/
  weight_galoisAction (σ : Gal(ℂ/ℚ)) (M : Ω) : weight (galoisAction σ M) = weight M
  /-- Conjugate objects have the same Hodge numbers. -/
  gammaShifts_galoisAction (σ : Gal(ℂ/ℚ)) (M : Ω) :
    gammaShifts (galoisAction σ M) = gammaShifts M
  /-- The value field transports along the action. -/
  valueField_galoisAction (σ : Gal(ℂ/ℚ)) (M : Ω) :
    valueField (galoisAction σ M) = (valueField M).map σ
  /-- The value field is algebraic over `ℚ`, which bounds it away from `ℂ`. -/
  valueField_isAlgebraic (M : Ω) {x : ℂ} (hx : x ∈ valueField M) : IsAlgebraic ℚ x
  /-- No period at a critical integer vanishes, criticality being written out on the shifts as
  in `Deligne.Pkg.isCritical_iff`. -/
  -- `Deligne.Pkg.IsCritical` is defined from a package and so cannot be named here; the
  -- hypothesis prevents the junk case `· / 0 = 0 ∈ valueField`.
  period_ne_zero' (M : Ω) (n : ℤ)
    (h₁ : ∀ a ∈ gammaShifts M, Odd (n + a) ∨ 0 < n + a)
    (h₂ : ∀ a ∈ gammaShifts M, Odd (weight M + 1 - n + a) ∨ 0 < weight M + 1 - n + a) :
    period M n ≠ 0

namespace Pkg

variable {Ω : Type*} {F : Pkg Ω}

/-- The archimedean Gamma factor `γ(M, s) = ∏ a, Γℝ(s + a)`, determined by the shifts. -/
noncomputable def gammaFactor (M : Ω) (s : ℂ) : ℂ :=
  Complex.prodGammaℝ (F.gammaShifts M) s

/-- `n` is critical for `M` when `γ(M, ·)` has a pole at neither `n` nor `w + 1 - n`, the two
points exchanged by the functional equation. -/
def IsCritical (M : Ω) (n : ℤ) : Prop :=
  0 ≤ meromorphicOrderAt (F.gammaFactor M) (n : ℂ) ∧
    0 ≤ meromorphicOrderAt (F.gammaFactor M) ((F.weight M + 1 - n : ℤ) : ℂ)

/-- Criticality written out as a condition on the shifts and the weight alone: `Γℝ` has poles
exactly at the non-positive even integers, so `γ(M, ·)` is regular at an integer `m` exactly when
`m + a` is odd or positive for every shift `a`. -/
lemma isCritical_iff (M : Ω) (n : ℤ) :
    F.IsCritical M n ↔ (∀ a ∈ F.gammaShifts M, Odd (n + a) ∨ 0 < n + a) ∧
      ∀ a ∈ F.gammaShifts M, Odd (F.weight M + 1 - n + a) ∨ 0 < F.weight M + 1 - n + a := by
  have hgf : F.gammaFactor M = Complex.prodGammaℝ (F.gammaShifts M) := rfl
  simp only [IsCritical, hgf, Complex.meromorphicOrderAt_prodGammaℝ_intCast_nonneg_iff]

/-- A `Γℂ` factor confines the critical set to `1 ≤ n ≤ w`. Since
`Γℂ(s) = Γℝ(s) Γℝ(s + 1)`, such a factor contributes the shifts `0` and `1`; one of `n`, `n + 1`
is even, and `Γℝ` has a pole at every non-positive even integer, so regularity at an integer `t`
already forces `1 ≤ t`. Apply that at `t = n` and at `t = w + 1 - n`. -/
theorem isCritical_le_weight {M : Ω} (h₀ : (0 : ℤ) ∈ F.gammaShifts M)
    (h₁ : (1 : ℤ) ∈ F.gammaShifts M) {n : ℤ} (hn : F.IsCritical M n) :
    1 ≤ n ∧ n ≤ F.weight M := by
  rw [isCritical_iff] at hn
  obtain ⟨hl, hr⟩ := hn
  have a₀ := hl 0 h₀
  have a₁ := hl 1 h₁
  have b₀ := hr 0 h₀
  have b₁ := hr 1 h₁
  simp only [Int.odd_iff] at a₀ a₁ b₀ b₁
  omega

/-- The period at a critical integer does not vanish. -/
lemma period_ne_zero (M : Ω) (n : ℤ) (h : F.IsCritical M n) : F.period M n ≠ 0 :=
  F.period_ne_zero' M n ((isCritical_iff M n).1 h).1 ((isCritical_iff M n).1 h).2

/-- The normalised critical value `L(M, n) / c⁺(M(n))`. -/
noncomputable def normalizedValue (M : Ω) (n : ℤ) : ℂ :=
  F.L M n / F.period M n

/-- Algebraicity at `M`: every normalised critical value lies in `E(M)`. -/
def IsArithmetic (M : Ω) : Prop :=
  ∀ (n : ℤ), F.IsCritical M n → F.normalizedValue M n ∈ F.valueField M

/-- Equivariance at `M`: every automorphism of `ℂ` carries a normalised critical value to the
normalised critical value of the transported object. -/
def IsEquivariant (M : Ω) : Prop :=
  ∀ (σ : Gal(ℂ/ℚ)) (n : ℤ), F.IsCritical M n →
    σ (F.normalizedValue M n) = F.normalizedValue (F.galoisAction σ M) n

/-- Deligne's conjecture for `(L, E, w, γ, c, σ)` at the object `M` consists of arithmeticity and
equivariance. -/
abbrev Conjecture (M : Ω) : Prop := F.IsArithmetic M ∧ F.IsEquivariant M

/-- Criticality is invariant under the Galois action, since conjugate objects have the same
shifts. -/
lemma isCritical_galoisAction_iff (σ : Gal(ℂ/ℚ)) (M : Ω) (n : ℤ) :
    F.IsCritical (F.galoisAction σ M) n ↔ F.IsCritical M n := by
  simp only [isCritical_iff, F.gammaShifts_galoisAction, F.weight_galoisAction]

/-! ### Nondegeneracy -/

/-- `M` has at least one critical integer. -/
def HasCriticalInteger (F : Pkg Ω) (M : Ω) : Prop :=
  ∃ n : ℤ, F.IsCritical M n

/-- Algebraicity says something whatever the value field is: at every critical integer it asserts
at least that the normalised value is an algebraic number. No choice of `valueField` can weaken
this, because a value field consists of algebraic numbers. Contrast
`Deligne.Pkg.conjecture_of_period_eq_mul_L`, the degenerate shape that no field law excludes. -/
theorem IsArithmetic.isAlgebraic {M : Ω} (h : F.IsArithmetic M) {n : ℤ}
    (hn : F.IsCritical M n) : IsAlgebraic ℚ (F.normalizedValue M n) :=
  F.valueField_isAlgebraic M (h n hn)

/-! ### Trivial cases

Some cases are trivial, either mathematically or by the choice of formalization of `Pkg`. -/

/-- Empty critical set: if `M` has no critical integers, then the formal conjecture is vacuously
true. This occurs in nature, for example the Dedekind zeta function of an imaginary
quadratic field has no critical integers [Ne99]. -/
theorem conjecture_of_forall_not_isCritical {M : Ω} (h : ∀ n : ℤ, ¬ F.IsCritical M n) :
    F.Conjecture M :=
  ⟨fun n hn ↦ absurd hn (h n), fun _ n hn ↦ absurd hn (h n)⟩

-- `Conjecture` is an `abbrev` for a conjunction, so its head unfolds to `And` and dot notation
-- does not resolve to this lemma
/-- An object with no critical integers satisfies the conjecture. -/
theorem Conjecture.of_not_hasCriticalInteger {M : Ω} (h : ¬ F.HasCriticalInteger M) :
    F.Conjecture M :=
  conjecture_of_forall_not_isCritical fun n hn ↦ h ⟨n, hn⟩

/-- Vanishing L-function: if the L-function vanishes at the critical points on the Galois orbit
of `M`, then the formal conjecture is trivially true. -/
theorem conjecture_of_L_eq_zero {M : Ω}
    (h : ∀ (σ : Gal(ℂ/ℚ)) (n : ℤ), F.IsCritical M n → F.L (F.galoisAction σ M) n = 0) :
    F.Conjecture M := by
  have hM : ∀ n, F.IsCritical M n → F.L M n = 0 := fun n hn ↦ by simpa using h 1 n hn
  refine ⟨fun n hn ↦ ?_, fun σ n hn ↦ ?_⟩
  · simp [normalizedValue, hM n hn]
  · simp [normalizedValue, hM n hn, h σ n hn]

/-- Trivial period: if on the Galois orbit of `M`, the supplied period is some rescaling of the
`L`-function at critical integers, then the formal conjecture is trivially true. -/
theorem conjecture_of_period_eq_mul_L {M : Ω} (e : ℤ → F.valueField M)
    (h : ∀ (σ : Gal(ℂ/ℚ)) (n : ℤ), F.IsCritical M n →
      F.period (F.galoisAction σ M) n = σ (e n) * F.L (F.galoisAction σ M) n) :
    F.Conjecture M := by
  have hL (σ : Gal(ℂ/ℚ)) (n : ℤ) (hn : F.IsCritical M n) :
      F.L (F.galoisAction σ M) n ≠ 0 := right_ne_zero_of_mul <|
    h σ n hn ▸ F.period_ne_zero _ n ((F.isCritical_galoisAction_iff σ M n).2 hn)
  have hval (σ : Gal(ℂ/ℚ)) (n : ℤ) (hn : F.IsCritical M n) :
      F.normalizedValue (F.galoisAction σ M) n = (σ (e n))⁻¹ := by
    rw [normalizedValue, h σ n hn, mul_comm, ← div_div, div_self (hL σ n hn), one_div]
  have hM (n : ℤ) (hn : F.IsCritical M n) : F.normalizedValue M n = (e n : ℂ)⁻¹ := by
    simpa using hval 1 n hn
  exact ⟨fun n hn ↦ hM n hn ▸ inv_mem (e n).2, fun σ n hn ↦ by rw [hM n hn, hval σ n hn, map_inv₀]⟩

/-! ### Rational coefficients -/

/-- For an object with value field `ℚ` that the Galois action fixes, equivariance is already
contained in algebraicity. -/
theorem IsArithmetic.isEquivariant_of_valueField_eq_bot {M : Ω} (h : F.IsArithmetic M)
    (hE : F.valueField M = ⊥) (hgal : ∀ σ : Gal(ℂ/ℚ), F.galoisAction σ M = M) :
    F.IsEquivariant M := fun σ n hn ↦ by
  rw [hgal σ]
  refine IntermediateField.apply_eq_self_of_mem_bot (σ : ℂ →ₐ[ℚ] ℂ) ?_
  rw [← hE]
  exact h n hn

end Pkg

end Deligne
