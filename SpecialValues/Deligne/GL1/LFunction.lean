/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import SpecialValues.Deligne.GL1.Critical
import SpecialValues.Deligne.Gamma
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# GL(1): the functional equation at a positive critical integer

The positive half of the GL(1) case is deduced from the non-positive half through the functional
equation of `L(χ, ·)`. This file evaluates that functional equation at a positive critical integer
`k + 1`: the archimedean factors are computed by the reflection formulae of
`SpecialValues/Deligne/Gamma.lean`, and the root number and the sign they produce cancel.

## Main results

* `Deligne.GL1.gammaFactor_neg_natCast_ne_zero`: the Gamma factor of `χ` is regular at `-k` when
  `k + 1` is critical.
* `Deligne.GL1.rootNumber_mul_gammaFactor_quotient`: the archimedean part of the functional
  equation at `k + 1`.
* `Deligne.GL1.LFunction_natCast_add_one`: `L(χ, k + 1)` in terms of `L(χ⁻¹, -k)`, the Gauss sum
  and `(2πi) ^ (k + 1)`.
-/

open Complex DirichletCharacter ZMod

open scoped Nat

namespace Deligne.GL1

variable {N : ℕ}

/-- The gamma factor of `χ` does not vanish at `-k`, when `k + 1` is critical for `χ`. -/
lemma gammaFactor_neg_natCast_ne_zero {χ : DirichletCharacter ℂ N} {k : ℕ}
    (hc : IsCritical χ ((k : ℤ) + 1)) :
    DirichletCharacter.gammaFactor χ (-(k : ℂ)) ≠ 0 := by
  have hpar := (hc.resolve_right (by rintro ⟨h, -⟩; omega)).2
  rcases χ.even_or_odd with h | h
  · have hk : ((k : ℤ) + 1) % 2 = 0 := Int.even_iff.mp (hpar.mpr h)
    rw [h.gammaFactor_def, show (-(k : ℂ)) = ((-(k : ℤ) : ℤ) : ℂ) by push_cast; ring]
    exact Gammaℝ_intCast_ne_zero_of_odd (Int.odd_iff.mpr (by omega))
  · have hodd : ¬χ.Even := h.not_even
    have hk : ¬((k : ℤ) + 1) % 2 = 0 := fun hh ↦ hodd (hpar.mp (Int.even_iff.mpr hh))
    rw [h.gammaFactor_def, show (-(k : ℂ) + 1) = ((1 - (k : ℤ) : ℤ) : ℂ) by push_cast; ring]
    exact Gammaℝ_intCast_ne_zero_of_odd (Int.odd_iff.mpr (by omega))

/-- The archimedean part of the functional equation at a positive critical integer. -/
lemma rootNumber_mul_gammaFactor_quotient [NeZero N] {χ : DirichletCharacter ℂ N} {k : ℕ}
    (hc : IsCritical χ ((k : ℤ) + 1)) :
    rootNumber χ * (DirichletCharacter.gammaFactor χ (-(k : ℂ))
        / DirichletCharacter.gammaFactor χ ((k : ℂ) + 1))
      = gaussSum χ stdAddChar / (N : ℂ) ^ (1 / 2 : ℂ) *
          (χ (-1) * (2 * (Real.pi : ℂ) * I) ^ (k + 1) / (2 * (k ! : ℂ))) := by
  classical
  -- The root number and the quotient are combined into one statement because the factor
  -- `I ^ δ` inside `rootNumber` and the sign produced by the reflection formula cancel:
  -- separately, each carries a parity that the two together do not.
  have hpar := (hc.resolve_right (by rintro ⟨h, -⟩; omega)).2
  have hs : ∀ j : ℕ, ((k : ℂ) + 1) ≠ -(j : ℂ) := by
    intro j hj
    have : ((k : ℤ) + 1) = -(j : ℤ) := by exact_mod_cast hj
    omega
  have hsign : ∀ m : ℕ, ((-1 : ℂ) ^ m)⁻¹ = (-1) ^ m := fun m ↦ by rw [← inv_pow]; norm_num
  rcases χ.even_or_odd with h | h
  · -- `χ` is even, so `k` is odd
    have hk : k % 2 = 1 := by have := Int.even_iff.mp (hpar.mpr h); omega
    obtain ⟨r, rfl⟩ : ∃ r, k = 2 * r + 1 := ⟨k / 2, by omega⟩
    have hI : (I : ℂ) ^ (2 * r + 1 + 1) = (-1) ^ (r + 1) := by
      rw [show 2 * r + 1 + 1 = 2 * (r + 1) by ring, pow_mul, I_sq]
    unfold rootNumber
    rw [ite_eq_left h, pow_zero, div_one, h.gammaFactor_def, h.gammaFactor_def,
      show (-((2 * r + 1 : ℕ) : ℂ)) = 1 - (((2 * r + 1 : ℕ) : ℂ) + 1) by push_cast; ring,
      Gammaℝ_one_sub_div_Gammaℝ hs, mul_inv, inv_Gammaℂ_natCast_add_one,
      show (Real.pi : ℂ) * (((2 * r + 1 : ℕ) : ℂ) + 1) / 2
        = ((r + 1 : ℕ) : ℂ) * Real.pi by push_cast; ring,
      cos_natCast_mul_pi, hsign, show χ (-1) = 1 from h, mul_pow, mul_pow, hI]
    ring
  · -- `χ` is odd, so `k` is even
    have hodd : ¬χ.Even := h.not_even
    have hk : k % 2 = 0 := by
      have : ¬((k : ℤ) + 1) % 2 = 0 := fun hh ↦ hodd (hpar.mp (Int.even_iff.mpr hh))
      omega
    obtain ⟨r, rfl⟩ : ∃ r, k = 2 * r := ⟨k / 2, by omega⟩
    have hI : (I : ℂ) ^ (2 * r + 1) = (-1) ^ r * I := by rw [pow_succ, pow_mul, I_sq]
    unfold rootNumber
    rw [ite_eq_right hodd, pow_one, div_eq_mul_inv (gaussSum χ stdAddChar) I, inv_I,
      h.gammaFactor_def, h.gammaFactor_def,
      show (-((2 * r : ℕ) : ℂ) + 1) = 2 - (((2 * r : ℕ) : ℂ) + 1) by push_cast; ring,
      Gammaℝ_two_sub_div_Gammaℝ_add_one hs, mul_inv, inv_Gammaℂ_natCast_add_one,
      show (Real.pi : ℂ) * (((2 * r : ℕ) : ℂ) + 1) / 2 = (r : ℂ) * Real.pi + Real.pi / 2 by
        push_cast; ring,
      Complex.sin_add_pi_div_two, cos_natCast_mul_pi, hsign, show χ (-1) = -1 from h,
      mul_pow, mul_pow, hI]
    ring

/-- The functional equation of `L(χ, ·)` at a positive critical integer. -/
lemma LFunction_natCast_add_one [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    {k : ℕ} (hc : IsCritical χ ((k : ℤ) + 1)) :
    DirichletCharacter.LFunction χ ((k : ℂ) + 1)
      = gaussSum χ stdAddChar * (2 * (Real.pi : ℂ) * I) ^ (k + 1) *
        (χ (-1) / (2 * (N : ℂ) ^ (k + 1) * (k ! : ℂ)) *
          DirichletCharacter.LFunction χ⁻¹ (-(k : ℂ))) := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hg₁ : DirichletCharacter.gammaFactor χ ((k : ℂ) + 1) ≠ 0 :=
    gammaFactor_natCast_add_one_ne_zero χ k
  have hg₂ : DirichletCharacter.gammaFactor χ⁻¹ (-(k : ℂ)) ≠ 0 := by
    rw [gammaFactor_inv]
    exact gammaFactor_neg_natCast_ne_zero hc
  have hne : ((k : ℂ) + 1) ≠ 0 := fun hj ↦ by
    have : ((k : ℤ) + 1) = 0 := by exact_mod_cast hj
    omega
  have hzero : -(k : ℂ) ≠ 0 ∨ N ≠ 1 := by
    rcases eq_or_ne N 1 with rfl | hN₁
    · refine Or.inl fun hj ↦ ?_
      have hk : (k : ℤ) = 0 := by exact_mod_cast neg_eq_zero.mp hj
      have := (isCritical_one_iff ((k : ℤ) + 1)).mp (DirichletCharacter.level_one χ ▸ hc)
      omega
    · exact Or.inr hN₁
  have h₁ : DirichletCharacter.completedLFunction χ ((k : ℂ) + 1)
      = DirichletCharacter.LFunction χ ((k : ℂ) + 1)
        * DirichletCharacter.gammaFactor χ ((k : ℂ) + 1) := by
    rw [LFunction_eq_completed_div_gammaFactor χ _ (Or.inl hne), div_mul_cancel₀ _ hg₁]
  have h₂ : DirichletCharacter.completedLFunction χ⁻¹ (-(k : ℂ))
      = DirichletCharacter.LFunction χ⁻¹ (-(k : ℂ))
        * DirichletCharacter.gammaFactor χ⁻¹ (-(k : ℂ)) := by
    rw [LFunction_eq_completed_div_gammaFactor χ⁻¹ _ hzero, div_mul_cancel₀ _ hg₂]
  have hγ : DirichletCharacter.gammaFactor χ⁻¹ (-(k : ℂ))
      = DirichletCharacter.gammaFactor χ (-(k : ℂ))
          / DirichletCharacter.gammaFactor χ ((k : ℂ) + 1)
        * DirichletCharacter.gammaFactor χ ((k : ℂ) + 1) := by
    rw [div_mul_cancel₀ _ hg₁, gammaFactor_inv]
  have hNpow : (N : ℂ) ^ (-(k : ℂ) - 1 / 2) * ((N : ℂ) ^ (1 / 2 : ℂ))⁻¹
      = ((N : ℂ) ^ (k + 1))⁻¹ := by
    rw [← cpow_neg, ← cpow_add _ _ hN,
      show (-(k : ℂ) - 1 / 2 + -(1 / 2 : ℂ)) = -(((k + 1 : ℕ) : ℂ)) by push_cast; ring,
      cpow_neg, cpow_natCast]
  have hfe := hχ.completedLFunction_one_sub (-(k : ℂ))
  rw [show (1 : ℂ) - -(k : ℂ) = (k : ℂ) + 1 by ring, h₁, h₂, hγ] at hfe
  refine mul_right_cancel₀ hg₁ ?_
  rw [hfe]
  set Lmirror := DirichletCharacter.LFunction χ⁻¹ (-(k : ℂ))
  set γ := DirichletCharacter.gammaFactor χ ((k : ℂ) + 1)
  linear_combination ((N : ℂ) ^ (-(k : ℂ) - 1 / 2) * Lmirror * γ) *
      rootNumber_mul_gammaFactor_quotient hc +
    (gaussSum χ stdAddChar * χ (-1) * (2 * (Real.pi : ℂ) * I) ^ (k + 1) * Lmirror * γ /
      (2 * (k ! : ℂ))) * hNpow

end Deligne.GL1
