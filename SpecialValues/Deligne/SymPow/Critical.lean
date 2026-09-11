/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import SpecialValues.Deligne.Pkg
import Mathlib.Data.Multiset.Bind

/-!
# The symmetric powers of an elliptic curve: Hodge data and critical set

The archimedean factor of a motive is determined by its Hodge numbers and by `F_∞`, and by
nothing else — no `L`-function and no period. So for `Sym^k h¹(E)`, with `E` an elliptic curve
over `ℚ`, the critical set is computable outright, and that is what this file computes, for
every `k`.

`h¹(E)` has Hodge types `(1,0)` and `(0,1)`, so `Sym^k h¹(E)` is pure of weight `k` and rank
`k + 1` with `h^{p,q} = 1` for every `p + q = k`. Deligne's recipe contributes a `Γℂ(s - p)` for
each pair `p < q`, and `Γℂ(s) = Γℝ(s) Γℝ(s + 1)` splits it into the shifts `-p` and `-p + 1`.
For `k = 2m` even the line `H^{m,m}` contributes one further `Γℝ`, whose shift is the *even*
member of `{-m, -m + 1}`: `F_∞` acts on `H^{m,m}` as `+1`, and Deligne's convention indexes the
two eigenspaces by `±(-1)^m` rather than by `±1` — a distinction that is invisible at weight `0`
and decides the `k ≡ 0` versus `k ≡ 2 (mod 4)` dichotomy below. That multiset is
`Deligne.SymPow.shifts`, and `Deligne.SymPow.card_shifts` is the rank check on it.

## The trichotomy

Writing `k = 2m + 1` or `k = 2m`, the critical set of `Sym^k h¹(E)` is

* `{m + 1}` for `k` odd — the centre `(w + 1) / 2` of the functional equation, an integer
  exactly because the weight is odd. This is the case Deligne's conjecture is interesting in,
  and for `k = 1` it is the critical point `s = 1` of the elliptic curve itself;
* `{m, m + 1}` for `k ≡ 2 (mod 4)`, which includes the symmetric square;
* empty for `4 ∣ k` with `k ≥ 4`, so the conjecture holds there vacuously
  (`Deligne.SymPow.conjecture_of_four_dvd`). That is not progress: it is the analogue of
  `h⁰(Spec K)` for `K` not totally real, and it is why `Deligne.Pkg.HasCriticalInteger` is proved
  separately in the two cases above;
* and `k = 0`, excluded from the previous clause, is `ℚ(0)`, whose critical set is that of `ζ`
  (`Deligne.SymPow.isCritical_iff_of_eq_zero`).

## What is deliberately absent

This file states no conjecture. Deligne's conjecture for `Sym^k h¹(E)` needs the `L`-function
and Deligne's period `c⁺`, and a `Prop` quantified over packages constrained only in their
archimedean data is a statement about the quantifier rather than about `E` — it is made true by
`L := 0` and false by `L := π`, neither of which the hypothesis touches. Pinning `L` and `c⁺`
is `blueprint/src/sympow.tex` §§`sec:sympow-L`, `sec:sympow-period`; everything here is what
the Hodge data alone determines.

## Main results

* `Deligne.SymPow.shifts`: the `Γℝ`-shifts of the archimedean factor of `Sym^k h¹(E)`, with
  `Deligne.SymPow.mem_shifts_iff` its membership API and `Deligne.SymPow.shifts_zero` the
  identification of `Sym^0 h¹(E)` with `ℚ(0)`.
* `Deligne.SymPow.card_shifts`: there are `k + 1` of them, one per basis vector.
* `Deligne.SymPow.forall_mem_shifts_iff_of_odd`,
  `Deligne.SymPow.forall_mem_shifts_iff_of_two_mod_four`,
  `Deligne.SymPow.forall_mem_shifts_iff_of_four_dvd`: the archimedean factor is regular at an
  integer exactly when that integer meets a threshold, which differs in the three cases.
* `Deligne.SymPow.isCritical_iff_of_odd`, `Deligne.SymPow.isCritical_iff_of_two_mod_four`,
  `Deligne.SymPow.not_isCritical_of_four_dvd`, `Deligne.SymPow.isCritical_iff_of_eq_zero`: the
  critical set, in each of the four cases, for any package carrying the weight and the shifts.
-/

namespace Deligne.SymPow

/-- The `Γℝ`-shifts of the archimedean factor of `Sym^k h¹(E)`: the shifts `-p` and `-p + 1` of
`Γℂ(s - p)` for each `2 * p < k`, together with, for `k = 2m` even, one further shift from the
line `H^{m,m}` — the *even* member of `{-m, -m + 1}`, `F_∞` acting there as `+1` against
Deligne's `±(-1)^m` convention. -/
def shifts (k : ℕ) : Multiset ℤ :=
  ((Multiset.range ((k + 1) / 2)).bind fun p ↦ (-(p : ℤ)) ::ₘ {-(p : ℤ) + 1}) +
    if Even k then {-2 * ((k / 4 : ℕ) : ℤ)} else 0

/-- Membership in `shifts k`: a shift comes either from one of the `Γℂ(s - p)` with `2 * p < k`
or, for `k` even, from the middle `Γℝ`. -/
lemma mem_shifts_iff {k : ℕ} {a : ℤ} :
    a ∈ shifts k ↔ (∃ p : ℕ, 2 * p < k ∧ (a = -(p : ℤ) ∨ a = -(p : ℤ) + 1)) ∨
      (Even k ∧ a = -2 * ((k / 4 : ℕ) : ℤ)) := by
  have hr : ∀ p : ℕ, p < (k + 1) / 2 ↔ 2 * p < k := fun p ↦ by omega
  rw [shifts, Multiset.mem_add]
  simp only [Multiset.mem_bind, Multiset.mem_range, Multiset.mem_cons, Multiset.mem_singleton,
    hr]
  split_ifs with h <;> simp [h]

/-- `Sym^0 h¹(E)` is `ℚ(0)`, whose archimedean factor is that of `ζ`. -/
@[simp]
lemma shifts_zero : shifts 0 = ({0} : Multiset ℤ) := by simp [shifts]

/-- One `Γℝ` per basis vector of `Sym^k h¹(E)`, which has rank `k + 1`. -/
lemma card_shifts (k : ℕ) : Multiset.card (shifts k) = k + 1 := by
  rw [shifts, Multiset.card_add, Multiset.card_bind]
  simp only [Function.comp_apply, Multiset.card_cons, Multiset.card_singleton,
    Multiset.map_const', Multiset.sum_replicate, Multiset.card_range, smul_eq_mul]
  split_ifs with hk
  · simp only [Multiset.card_singleton]
    rw [Nat.even_iff] at hk
    omega
  · simp only [Multiset.card_zero]
    rw [Nat.not_even_iff_odd, Nat.odd_iff] at hk
    omega

/-- For `k = 2m + 1` the archimedean factor is regular at an integer `t` exactly when
`m + 1 ≤ t`. -/
lemma forall_mem_shifts_iff_of_odd {m : ℕ} {t : ℤ} :
    (∀ a ∈ shifts (2 * m + 1), Odd (t + a) ∨ 0 < t + a) ↔ (m : ℤ) + 1 ≤ t := by
  constructor
  · intro h
    -- the innermost `Γℂ(s - m)`, i.e. the consecutive pair of shifts `-m` and `-m + 1`
    have h₁ := h _ (mem_shifts_iff.mpr (.inl ⟨m, by omega, .inl rfl⟩))
    have h₂ := h _ (mem_shifts_iff.mpr (.inl ⟨m, by omega, .inr rfl⟩))
    simp only [Int.odd_iff] at h₁ h₂
    omega
  · intro ht a ha
    rcases mem_shifts_iff.mp ha with ⟨p, hp, hpa⟩ | ⟨hk, -⟩
    · rcases hpa with rfl | rfl <;> exact .inr (by omega)
    · rw [Nat.even_iff] at hk
      omega

/-- For `k = 2m` with `m` odd, i.e. `k ≡ 2 (mod 4)`, the archimedean factor is regular at an
integer `t` exactly when `m ≤ t`. -/
lemma forall_mem_shifts_iff_of_two_mod_four {m : ℕ} (hm : Odd m) {t : ℤ} :
    (∀ a ∈ shifts (2 * m), Odd (t + a) ∨ 0 < t + a) ↔ (m : ℤ) ≤ t := by
  obtain ⟨j, rfl⟩ := hm
  constructor
  · intro h
    have h₁ := h _ (mem_shifts_iff.mpr (.inl ⟨2 * j, by omega, .inl rfl⟩))
    have h₂ := h _ (mem_shifts_iff.mpr (.inl ⟨2 * j, by omega, .inr rfl⟩))
    simp only [Int.odd_iff] at h₁ h₂
    push_cast at h₁ h₂ ⊢
    omega
  · intro ht a ha
    push_cast at ht
    rcases mem_shifts_iff.mp ha with ⟨p, hp, rfl | rfl⟩ | ⟨-, rfl⟩ <;>
      exact .inr (by push_cast; omega)

/-- For `k = 2m` with `m` even and nonzero, i.e. `4 ∣ k` and `k ≥ 4`, the archimedean factor is
regular at an integer `t` exactly when `m + 1 ≤ t`. -/
lemma forall_mem_shifts_iff_of_four_dvd {m : ℕ} (hm : Even m) (hm0 : m ≠ 0) {t : ℤ} :
    (∀ a ∈ shifts (2 * m), Odd (t + a) ∨ 0 < t + a) ↔ (m : ℤ) + 1 ≤ t := by
  obtain ⟨j, rfl⟩ := hm
  constructor
  · intro h
    -- the middle shift `-m` is even, so at `t = m` it contributes `0`: that is what excludes
    -- `t = m` here and does not for `k ≡ 2 (mod 4)`
    have h₁ := h _ (mem_shifts_iff.mpr (.inr ⟨⟨j + j, by omega⟩, rfl⟩))
    have h₂ := h _ (mem_shifts_iff.mpr (.inl ⟨j + j - 1, by omega, .inl rfl⟩))
    simp only [Int.odd_iff] at h₁ h₂
    push_cast at h₁ h₂ ⊢
    omega
  · intro ht a ha
    push_cast at ht
    rcases mem_shifts_iff.mp ha with ⟨p, hp, rfl | rfl⟩ | ⟨-, rfl⟩ <;>
      exact .inr (by push_cast; omega)

variable {Ω : Type*} (F : Pkg Ω) {M : Ω} {m : ℕ}

/-- The critical set of `Sym^(2m+1) h¹(E)` is the single integer `m + 1`. -/
theorem isCritical_iff_of_odd (hw : F.weight = 2 * m + 1)
    (hs : F.gammaShifts M = shifts (2 * m + 1)) (n : ℤ) :
    F.IsCritical M n ↔ n = (m : ℤ) + 1 := by
  rw [Pkg.isCritical_iff, hs, hw, forall_mem_shifts_iff_of_odd, forall_mem_shifts_iff_of_odd]
  omega

/-- The critical set of `Sym^(2m) h¹(E)` for `m` odd is `{m, m + 1}`. -/
theorem isCritical_iff_of_two_mod_four (hm : Odd m) (hw : F.weight = 2 * m)
    (hs : F.gammaShifts M = shifts (2 * m)) (n : ℤ) :
    F.IsCritical M n ↔ n = (m : ℤ) ∨ n = (m : ℤ) + 1 := by
  rw [Pkg.isCritical_iff, hs, hw, forall_mem_shifts_iff_of_two_mod_four hm,
    forall_mem_shifts_iff_of_two_mod_four hm]
  omega

/-- `Sym^(2m) h¹(E)` for `m` even and nonzero has no critical integer. -/
theorem not_isCritical_of_four_dvd (hm : Even m) (hm0 : m ≠ 0) (hw : F.weight = 2 * m)
    (hs : F.gammaShifts M = shifts (2 * m)) (n : ℤ) : ¬ F.IsCritical M n := by
  rw [Pkg.isCritical_iff, hs, hw, forall_mem_shifts_iff_of_four_dvd hm hm0,
    forall_mem_shifts_iff_of_four_dvd hm hm0]
  omega

/-- The critical set of `Sym^0 h¹(E) = ℚ(0)` is that of the Riemann zeta function: the positive
even integers and the negative odd ones. -/
theorem isCritical_iff_of_eq_zero (hw : F.weight = 0) (hs : F.gammaShifts M = shifts 0)
    (n : ℤ) : F.IsCritical M n ↔ (Even n ∧ 0 < n) ∨ (Odd n ∧ n < 0) := by
  rw [Pkg.isCritical_iff, hs, hw, shifts_zero]
  simp only [Multiset.mem_singleton, forall_eq, add_zero, Int.odd_iff, Int.even_iff]
  omega

/-- `Sym^(2m+1) h¹(E)` has a critical integer, so Deligne's conjecture is not vacuous for it. -/
theorem hasCriticalInteger_of_odd (hw : F.weight = 2 * m + 1)
    (hs : F.gammaShifts M = shifts (2 * m + 1)) : F.HasCriticalInteger M :=
  ⟨(m : ℤ) + 1, (isCritical_iff_of_odd F hw hs _).mpr rfl⟩

/-- `Sym^(2m) h¹(E)` for `m` odd has a critical integer, so Deligne's conjecture is not vacuous
for it. -/
theorem hasCriticalInteger_of_two_mod_four (hm : Odd m) (hw : F.weight = 2 * m)
    (hs : F.gammaShifts M = shifts (2 * m)) : F.HasCriticalInteger M :=
  ⟨(m : ℤ), (isCritical_iff_of_two_mod_four F hm hw hs _).mpr (.inl rfl)⟩

/-- Deligne's conjecture holds vacuously for `Sym^(2m) h¹(E)` with `m` even and nonzero. -/
theorem conjecture_of_four_dvd (hm : Even m) (hm0 : m ≠ 0) (hw : F.weight = 2 * m)
    (hs : F.gammaShifts M = shifts (2 * m)) : F.Conjecture M :=
  Pkg.Conjecture.of_not_hasCriticalInteger fun ⟨n, hn⟩ ↦
    not_isCritical_of_four_dvd F hm hm0 hw hs n hn

end Deligne.SymPow
