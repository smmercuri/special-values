/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import SpecialValues.Deligne.GL1.LFunction
import SpecialValues.Deligne.GL1.Pkg
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.LSeries.Nonvanishing
import PadicLFunctions.Interpolation.GenBernoulliComplex

/-!
# Deligne's conjecture for GL(1)

`Deligne.GL1.conjecture` is Deligne's conjecture for the package `Deligne.GL1.pkg`: for every
primitive Dirichlet character `χ` modulo `N` and every critical integer `n`, the normalised value
`L(χ, n) / c⁺(M(χ)(n))` lies in `ℚ(χ)`, and every `σ ∈ Gal(ℂ/ℚ)` carries it to the corresponding
value of `χ ^ σ`.

The engine is the non-positive half: at a critical `n ≤ 0` the period is `1` and `L(χ, n)` is a
rational multiple of a generalised Bernoulli number, so the assertion is that `B_{k,χ}` lies in
`ℚ(χ)` and transports along the Galois action. The positive half is deduced from it through the
functional equation (`SpecialValues/Deligne/GL1/LFunction.lean`), which exchanges the two halves
of the critical set.

## Main results

* `Deligne.GL1.isArithmetic_of_nonpos`, `Deligne.GL1.isEquivariant_of_nonpos`: the conjecture at
  the non-positive integers.
* `Deligne.GL1.isArithmetic_of_pos`, `Deligne.GL1.isEquivariant_of_pos`: the conjecture at the
  positive integers.
* `Deligne.GL1.conjecture`: Deligne's conjecture for GL(1), assembled from
  `Deligne.GL1.isArithmetic_pkg` and `Deligne.GL1.isEquivariant_pkg`.
* `Deligne.GL1.normalizedValue_ne_zero`: the normalised critical values at positive integers are
  nonzero. `SpecialValues/Deligne/Pkg.lean` rules out the two degenerate *shapes* — no critical
  integers, and a vanishing period — but neither guard prevents an instance whose normalised
  values all happen to be `0`, which would satisfy the conjecture while asserting nothing. Together
  with `Deligne.GL1.hasCriticalInteger_pkg` this closes that for GL(1), uniformly in the conductor.
* `Deligne.GL1.normalizedValue_modOne_two`, `Deligne.GL1.normalizedValue_modOne_four`: numerical
  checks of the period normalisation against `ζ(2)` and `ζ(4)`.
-/

open Complex DirichletCharacter ZMod

open scoped Nat

namespace Deligne.GL1

variable {N : ℕ}

/-- The normalised value of the GL(1) package at a non-positive integer. -/
lemma normalizedValue_of_nonpos [NeZero N] (M : {χ : DirichletCharacter ℂ N // χ.IsPrimitive})
    {n : ℤ} (hn : n ≤ 0) :
    (pkg N).normalizedValue M n = DirichletCharacter.LFunction M.1 n := by
  change DirichletCharacter.LFunction M.1 n / period M.1 n = _
  rw [period_of_nonpos hn, div_one]

/-- The normalised value of the GL(1) package at `-k`, in terms of the generalised Bernoulli
number `B_{k+1,χ}`. -/
lemma normalizedValue_neg_natCast [NeZero N]
    (M : {χ : DirichletCharacter ℂ N // χ.IsPrimitive}) (k : ℕ) :
    (pkg N).normalizedValue M (-(k : ℤ))
      = -(M.1.genBernoulli (k + 1)) / (k + 1) := by
  rw [normalizedValue_of_nonpos M (by omega),
    show ((-(k : ℤ) : ℤ) : ℂ) = -(k : ℂ) by push_cast; ring, PadicLFunctions.LFunction_neg_nat]

/-- Algebraicity of the normalised critical values of `χ` at the non-positive integers. -/
theorem isArithmetic_of_nonpos [NeZero N] (M : {χ : DirichletCharacter ℂ N // χ.IsPrimitive})
    {n : ℤ} (hn : n ≤ 0) :
    (pkg N).normalizedValue M n ∈ (pkg N).valueField M := by
  obtain ⟨k, rfl⟩ := Int.exists_eq_neg_ofNat hn
  rw [valueField_pkg, normalizedValue_neg_natCast]
  exact div_mem (neg_mem (genBernoulli_mem_valueField _ _))
    (add_mem (natCast_mem _ _) (one_mem _))

/-- Equivariance of the normalised critical values of `χ` at the non-positive integers. -/
theorem isEquivariant_of_nonpos [NeZero N] (M : {χ : DirichletCharacter ℂ N // χ.IsPrimitive})
    (σ : Gal(ℂ/ℚ)) {n : ℤ} (hn : n ≤ 0) :
    σ ((pkg N).normalizedValue M n)
      = (pkg N).normalizedValue ((pkg N).galoisAction σ M) n := by
  obtain ⟨k, rfl⟩ := Int.exists_eq_neg_ofNat hn
  have hM : ((pkg N).galoisAction σ M).1 = galoisConj M.1 σ := rfl
  rw [normalizedValue_neg_natCast, normalizedValue_neg_natCast, hM, map_div₀, map_neg,
    genBernoulli_galoisConj]
  simp

/-- The normalised value of the GL(1) package at `k + 1`, in terms of the mirror value
`L(χ⁻¹, -k)`. -/
lemma normalizedValue_natCast_add_one [NeZero N]
    (M : {χ : DirichletCharacter ℂ N // χ.IsPrimitive}) {k : ℕ}
    (hc : IsCritical M.1 ((k : ℤ) + 1)) :
    (pkg N).normalizedValue M ((k : ℤ) + 1)
      = M.1 (-1) / (2 * (N : ℂ) ^ (k + 1) * (k ! : ℂ))
        * DirichletCharacter.LFunction M.1⁻¹ (-(k : ℂ)) := by
  change DirichletCharacter.LFunction M.1 (((k : ℤ) + 1 : ℤ) : ℂ)
    / period M.1 ((k : ℤ) + 1) = _
  rw [period_of_one_le (by omega),
    show ((((k : ℤ) + 1 : ℤ)) : ℂ) = (k : ℂ) + 1 by push_cast; ring,
    show ((k : ℤ) + 1) = ((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
    LFunction_natCast_add_one M.2 hc]
  exact mul_div_cancel_left₀ _ (mul_ne_zero M.2.gaussSum_ne_zero
    (pow_ne_zero _ (by simp [Real.pi_ne_zero, I_ne_zero])))

/-- Algebraicity of the normalised critical values of `χ` at the positive integers. -/
theorem isArithmetic_of_pos [NeZero N] (M : {χ : DirichletCharacter ℂ N // χ.IsPrimitive})
    {n : ℤ} (hn : 1 ≤ n) (hc : IsCritical M.1 n) :
    (pkg N).normalizedValue M n ∈ (pkg N).valueField M := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = (k : ℤ) + 1 := ⟨(n - 1).toNat, by omega⟩
  have hmirror : DirichletCharacter.LFunction M.1⁻¹ (-(k : ℂ)) ∈ valueField M.1 := by
    have h : DirichletCharacter.LFunction M.1⁻¹ (-(k : ℂ)) ∈ valueField M.1⁻¹ := by
      have h₀ := isArithmetic_of_nonpos ⟨M.1⁻¹, M.2.inv⟩ (n := -(k : ℤ)) (by omega)
      rw [valueField_pkg, normalizedValue_of_nonpos _ (by omega),
        show ((-(k : ℤ) : ℤ) : ℂ) = -(k : ℂ) by push_cast; ring] at h₀
      exact h₀
    rwa [valueField_inv] at h
  rw [valueField_pkg, normalizedValue_natCast_add_one M hc]
  exact mul_mem (div_mem (IntermediateField.subset_adjoin ℚ _ ⟨-1, rfl⟩)
    (mul_mem (mul_mem (ofNat_mem _ 2) (pow_mem (natCast_mem _ _) _)) (natCast_mem _ _)))
    hmirror

/-- Equivariance of the normalised critical values of `χ` at the positive integers. -/
theorem isEquivariant_of_pos [NeZero N] (M : {χ : DirichletCharacter ℂ N // χ.IsPrimitive})
    (σ : Gal(ℂ/ℚ)) {n : ℤ} (hn : 1 ≤ n) (hc : IsCritical M.1 n) :
    σ ((pkg N).normalizedValue M n)
      = (pkg N).normalizedValue ((pkg N).galoisAction σ M) n := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = (k : ℤ) + 1 := ⟨(n - 1).toNat, by omega⟩
  have hc' : IsCritical ((pkg N).galoisAction σ M).1 ((k : ℤ) + 1) := by
    rw [coe_galoisAction_pkg]
    exact (isCritical_galoisConj_iff M.1 σ _).mpr hc
  have hmirror : σ (DirichletCharacter.LFunction M.1⁻¹ (-(k : ℂ)))
      = DirichletCharacter.LFunction (galoisConj M.1 σ)⁻¹ (-(k : ℂ)) := by
    have h₀ := isEquivariant_of_nonpos ⟨M.1⁻¹, M.2.inv⟩ σ (n := -(k : ℤ)) (by omega)
    rw [normalizedValue_of_nonpos _ (by omega), normalizedValue_of_nonpos _ (by omega),
      show ((-(k : ℤ) : ℤ) : ℂ) = -(k : ℂ) by push_cast; ring] at h₀
    rw [MulChar.ringHomComp_inv]
    exact h₀
  have hscal : σ (2 * (N : ℂ) ^ (k + 1) * (k ! : ℂ)) = 2 * (N : ℂ) ^ (k + 1) * (k ! : ℂ) := by
    rw [map_mul, map_mul, map_ofNat, map_pow, map_natCast, map_natCast]
  rw [normalizedValue_natCast_add_one M hc, normalizedValue_natCast_add_one _ hc',
    coe_galoisAction_pkg, map_mul, map_div₀, hscal, hmirror, galoisConj_apply]

/-- Algebraicity for the GL(1) package: every normalised critical value of `χ` lies in `ℚ(χ)`. -/
theorem isArithmetic_pkg [NeZero N] (M : {χ : DirichletCharacter ℂ N // χ.IsPrimitive}) :
    (pkg N).IsArithmetic M := by
  intro n hn
  rw [isCritical_pkg_iff] at hn
  by_cases h : n ≤ 0
  · exact isArithmetic_of_nonpos M h
  · exact isArithmetic_of_pos M (by omega) hn

/-- Equivariance for the GL(1) package: every automorphism of `ℂ` carries a normalised critical
value of `χ` to the corresponding value of `χ ^ σ`. -/
theorem isEquivariant_pkg [NeZero N] (M : {χ : DirichletCharacter ℂ N // χ.IsPrimitive}) :
    (pkg N).IsEquivariant M := by
  intro σ n hn
  rw [isCritical_pkg_iff] at hn
  by_cases h : n ≤ 0
  · exact isEquivariant_of_nonpos M σ h
  · exact isEquivariant_of_pos M σ (by omega) hn

/-- **Deligne's conjecture for GL(1)**: for every primitive Dirichlet character `χ` modulo `N`
and every critical integer `n`, the normalised value `L(χ, n) / c(n, χ)` lies in `ℚ(χ)`, where
`c(n, χ) = 1` if `n ≤ 0` and `c(n, χ) = G(χ)(2πi)ⁿ` if `1 ≤ n`, and every automorphism of `ℂ`
carries it to the corresponding value of `χ ^ σ`. That there is a critical integer to speak of is
`Deligne.GL1.hasCriticalInteger_pkg`, a separate theorem. -/
theorem conjecture [NeZero N] {χ : DirichletCharacter ℂ N} (h : χ.IsPrimitive) :
    (pkg N).Conjecture ⟨χ, h⟩ :=
  ⟨isArithmetic_pkg ⟨χ, h⟩, isEquivariant_pkg ⟨χ, h⟩⟩

/-! ### Non-vanishing of the critical values -/

/-- The normalised critical values at the positive integers do not vanish. -/
theorem normalizedValue_ne_zero [NeZero N] (M : {χ : DirichletCharacter ℂ N // χ.IsPrimitive})
    {n : ℤ} (hn : 1 ≤ n) (hc : IsCritical M.1 n) :
    (pkg N).normalizedValue M n ≠ 0 := by
  refine div_ne_zero (DirichletCharacter.LFunction_ne_zero_of_one_le_re _ ?_ ?_)
    (period_ne_zero M.2 n)
  · -- mathlib excludes the trivial character at `s = 1`; at level one `1` is not critical
    rcases eq_or_ne N 1 with rfl | hN
    · refine Or.inr fun hs ↦ ?_
      have hn₁ : n = 1 := by exact_mod_cast hs
      have := (isCritical_one_iff n).mp (DirichletCharacter.level_one M.1 ▸ hc)
      omega
    · exact Or.inl fun h ↦ hN (by rw [← M.2, h, DirichletCharacter.conductor_one])
  · rw [Complex.intCast_re]
    exact_mod_cast hn

/-! ### Numerical checks of the period normalisation -/

/-- The normalised critical values of the level-one package, in terms of `riemannZeta`. -/
lemma normalizedValue_modOne (k : ℕ) (hk : 1 ≤ k) :
    (pkg 1).normalizedValue ⟨1, isPrimitive_one_level_one⟩ k
      = riemannZeta k / (2 * (Real.pi : ℂ) * I) ^ k := by
  change DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) ((k : ℤ) : ℂ)
    / period (1 : DirichletCharacter ℂ 1) (k : ℤ) = _
  rw [period_of_one_le (by exact_mod_cast hk), gaussSum_modOne,
    DirichletCharacter.LFunction_modOne_eq, zpow_natCast, one_mul, Int.cast_natCast]

/-- The normalised value at `n = 2` of the trivial character is `ζ(2) / (2πi) ^ 2 = -1/24`. -/
theorem normalizedValue_modOne_two :
    (pkg 1).normalizedValue ⟨1, isPrimitive_one_level_one⟩ 2 = -1 / 24 := by
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hI : ((2 : ℂ) * (Real.pi : ℂ) * I) ^ (2 : ℕ) = -(4 * (Real.pi : ℂ) ^ 2) := by
    rw [mul_pow, mul_pow, I_sq]
    ring
  rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, normalizedValue_modOne 2 one_le_two,
    show ((2 : ℕ) : ℂ) = 2 by norm_num, riemannZeta_two, hI]
  field_simp
  ring

/-- The normalised value at `n = 4` of the trivial character is `ζ(4) / (2πi) ^ 4 = 1/1440`. -/
theorem normalizedValue_modOne_four :
    (pkg 1).normalizedValue ⟨1, isPrimitive_one_level_one⟩ 4 = 1 / 1440 := by
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hI : ((2 : ℂ) * (Real.pi : ℂ) * I) ^ (4 : ℕ) = 16 * (Real.pi : ℂ) ^ 4 := by
    rw [mul_pow, mul_pow, I_pow_four]
    ring
  rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) from rfl, normalizedValue_modOne 4 (by norm_num),
    show ((4 : ℕ) : ℂ) = 4 by norm_num, riemannZeta_four, hI]
  field_simp
  ring

end Deligne.GL1
