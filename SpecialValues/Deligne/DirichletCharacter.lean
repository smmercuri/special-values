/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.RingTheory.Algebraic.Integral

/-!
# Dirichlet characters under a ring homomorphism, and Gauss sums of primitive characters

Facts about Dirichlet characters that the GL(1) case of Deligne's conjecture needs and mathlib
does not record. None of them mentions Deligne's conjecture, and all belong upstream.

## Main results

* `DirichletCharacter.conductor_ringHomComp`: post-composition with an injective ring
  homomorphism leaves the conductor unchanged, so it preserves primitivity
  (`DirichletCharacter.IsPrimitive.ringHomComp`).
* `DirichletCharacter.IsPrimitive.gaussSum_ne_zero`: the Gauss sum of a primitive Dirichlet
  character against `ZMod.stdAddChar` is nonzero. Mathlib's `gaussSum_ne_zero_of_nontrivial`
  requires the source ring to be a field, so it is silent for composite moduli.
* `DirichletCharacter.gammaFactor_inv`: the archimedean Gamma factor is unchanged by inversion.
* `DirichletCharacter.isAlgebraic_apply`: the values of a Dirichlet character over `ℂ` are
  algebraic numbers.
-/

open Finset ZMod

namespace DirichletCharacter

section Parity

variable {S : Type*} {m : ℕ}

/-- The trivial Dirichlet character is even. -/
@[simp]
lemma even_one [CommRing S] : (1 : DirichletCharacter S m).Even :=
  MulChar.one_apply isUnit_one.neg

/-- A Dirichlet character and its inverse have the same parity. -/
lemma even_inv_iff [Field S] {χ : DirichletCharacter S m} : χ⁻¹.Even ↔ χ.Even := by
  simp [DirichletCharacter.Even, MulChar.inv_apply_eq_inv']

end Parity

section RingHomComp

variable {R R' : Type*} [CommRing R] [CommRing R'] {N : ℕ} [NeZero N]
  {f : R →+* R'} {χ : DirichletCharacter R N}

/-- Post-composition with an injective ring homomorphism does not change the set of levels a
Dirichlet character factors through. -/
lemma factorsThrough_ringHomComp_iff (hf : Function.Injective f) {d : ℕ} :
    FactorsThrough (χ.ringHomComp f) d ↔ FactorsThrough χ d := by
  have hker : (χ.ringHomComp f).toUnitHom.ker = χ.toUnitHom.ker := by
    ext u
    simp only [MonoidHom.mem_ker, ← Units.val_inj, Units.val_one, MulChar.coe_toUnitHom,
      MulChar.ringHomComp_apply]
    exact ⟨fun h ↦ hf (by rw [h, map_one]), fun h ↦ by rw [h, map_one]⟩
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩ <;>
    rw [factorsThrough_iff_ker_unitsMap h.dvd] <;>
    exact hker ▸ (factorsThrough_iff_ker_unitsMap h.dvd).mp h

/-- Post-composition with an injective ring homomorphism does not change the conductor. -/
lemma conductor_ringHomComp (hf : Function.Injective f) :
    conductor (χ.ringHomComp f) = conductor χ := by
  have h : conductorSet (χ.ringHomComp f) = conductorSet χ :=
    Set.ext fun _ ↦ factorsThrough_ringHomComp_iff hf
  simp [conductor, h]

/-- Post-composition with an injective ring homomorphism preserves primitivity. -/
lemma IsPrimitive.ringHomComp (hχ : χ.IsPrimitive) (hf : Function.Injective f) :
    IsPrimitive (χ.ringHomComp f) := by
  rwa [isPrimitive_def, conductor_ringHomComp hf]

end RingHomComp

section Primitive

variable {R : Type*} [CommMonoidWithZero R] {N : ℕ} {χ : DirichletCharacter R N}

/-- The inverse of a primitive Dirichlet character is primitive. -/
lemma IsPrimitive.inv (hχ : χ.IsPrimitive) : χ⁻¹.IsPrimitive := by
  rw [isPrimitive_def, conductor_inv]
  exact hχ

end Primitive

section GaussSum

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

/-- The Gauss sum of the Dirichlet character of modulus `1`. -/
lemma gaussSum_modOne (χ : DirichletCharacter ℂ 1) : gaussSum χ stdAddChar = 1 := by
  simp [gaussSum, -univ_unique, ← singleton_eq_univ (1 : ZMod 1),
    (show stdAddChar (1 : ZMod 1) = 1 from AddChar.map_zero_eq_one _)]

/-- The Gauss sums of a primitive Dirichlet character and of its inverse multiply to
`χ (-1) * N`. Compare `gaussSum_mul_gaussSum_eq_card`, which assumes the source is a field. -/
theorem IsPrimitive.gaussSum_mul_gaussSum_inv (hχ : χ.IsPrimitive) :
    gaussSum χ stdAddChar * gaussSum χ⁻¹ stdAddChar = χ (-1) * N := by
  -- The Fourier transform of `χ` is `χ⁻¹ ∘ (-·)` scaled by the Gauss sum, so transforming
  -- twice multiplies the two Gauss sums; Fourier inversion evaluates the same thing.
  have h₁ : (𝓕 (⇑χ)) = fun k ↦ (fun j ↦ (⇑χ⁻¹) (-j)) k * gaussSum χ stdAddChar :=
    funext hχ.fourierTransform_eq_inv_mul_gaussSum
  have h₂ : (𝓕 (𝓕 (⇑χ))) 1 = χ 1 * gaussSum χ⁻¹ stdAddChar * gaussSum χ stdAddChar := by
    simp [h₁, ZMod.dft_mul_const, ZMod.dft_comp_neg, hχ.inv.fourierTransform_eq_inv_mul_gaussSum]
  simp only [ZMod.dft_dft, MulChar.map_one, one_mul, smul_eq_mul] at h₂
  linear_combination -h₂

/-- The Gauss sum of a primitive Dirichlet character does not vanish. -/
lemma IsPrimitive.gaussSum_ne_zero (hχ : χ.IsPrimitive) : gaussSum χ stdAddChar ≠ 0 := fun h ↦ by
  have h := h ▸ hχ.gaussSum_mul_gaussSum_inv
  rw [zero_mul] at h
  exact mul_ne_zero (MulChar.apply_ne_zero_iff.mpr isUnit_one.neg)
    (Nat.cast_ne_zero.mpr (NeZero.ne N)) h.symm

end GaussSum

section GammaFactor

variable {N : ℕ}

/-- The archimedean Gamma factor of a Dirichlet character is unchanged by inversion. -/
lemma gammaFactor_inv (χ : DirichletCharacter ℂ N) (s : ℂ) :
    gammaFactor χ⁻¹ s = gammaFactor χ s := by
  classical
  simp only [gammaFactor]
  exact if_congr even_inv_iff rfl rfl

/-- The archimedean Gamma factor of a Dirichlet character does not vanish at a positive
integer. -/
lemma gammaFactor_natCast_add_one_ne_zero (χ : DirichletCharacter ℂ N) (k : ℕ) :
    gammaFactor χ ((k : ℂ) + 1) ≠ 0 := by
  rcases χ.even_or_odd with h | h <;>
    rw [h.gammaFactor_def] <;>
    exact Complex.Gammaℝ_ne_zero_of_re_pos
      (by simp only [Complex.add_re, Complex.natCast_re, Complex.one_re]; positivity)

end GammaFactor

section Values

variable {N : ℕ} [NeZero N]

/-- The values of a Dirichlet character over `ℂ` are algebraic. -/
lemma isAlgebraic_apply (χ : DirichletCharacter ℂ N) (a : ZMod N) : IsAlgebraic ℚ (χ a) := by
  rw [isAlgebraic_iff_isIntegral]
  -- a value is either `0`, at a non-unit, or a root of unity, since `χ ^ #(ZMod N)ˣ = 1`
  by_cases ha : IsUnit a
  · obtain ⟨u, rfl⟩ := ha
    refine IsIntegral.of_pow (n := Fintype.card (ZMod N)ˣ) Fintype.card_pos ?_
    rw [← MulChar.pow_apply_coe, χ.pow_card_eq_one, MulChar.one_apply_coe]
    exact isIntegral_one
  · exact χ.map_nonunit ha ▸ isIntegral_zero

end Values

end DirichletCharacter
