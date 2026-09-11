/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import SpecialValues.Deligne.DirichletCharacter
import Mathlib.FieldTheory.Galois.Notation

/-!
# GL(1): the Galois action on Dirichlet characters

`Gal(ℂ/ℚ)` acts on Dirichlet characters modulo `N` by post-composition, `χ ↦ σ ∘ χ`. This file
records that action, that it preserves parity and primitivity, and packages it as a group action
on the primitive characters, which is the form `Deligne.Pkg` asks for.

## Main definitions

* `Deligne.GL1.galoisConj`: the Galois conjugate `χ ^ σ = σ ∘ χ`.
* `Deligne.GL1.galoisAction`: the same, as an action of `Gal(ℂ/ℚ)` on the primitive characters.

## Main results

* `Deligne.GL1.even_galoisConj`, `Deligne.GL1.isPrimitive_galoisConj`: Galois conjugation
  preserves parity and primitivity.
-/

open Complex DirichletCharacter ZMod

namespace Deligne.GL1

variable {N : ℕ}

/-- The Galois conjugate `χ ^ σ = σ ∘ χ` of a Dirichlet character. -/
noncomputable abbrev galoisConj (χ : DirichletCharacter ℂ N) (σ : Gal(ℂ/ℚ)) :
    DirichletCharacter ℂ N :=
  χ.ringHomComp (σ : ℂ →+* ℂ)

@[simp]
lemma galoisConj_apply (χ : DirichletCharacter ℂ N) (σ : Gal(ℂ/ℚ)) (a : ZMod N) :
    galoisConj χ σ a = σ (χ a) := rfl

@[simp]
lemma coe_galoisConj (χ : DirichletCharacter ℂ N) (σ : Gal(ℂ/ℚ)) : ⇑(galoisConj χ σ) = σ ∘ χ :=
  rfl

/-- Galois conjugation preserves the parity of a Dirichlet character: `σ` fixes `1`, so
`χ ^ σ (-1) = 1` exactly when `χ (-1) = 1`. -/
@[simp]
lemma even_galoisConj (χ : DirichletCharacter ℂ N) (σ : Gal(ℂ/ℚ)) :
    (galoisConj χ σ).Even ↔ χ.Even := by
  simp only [DirichletCharacter.Even, galoisConj_apply]
  exact ⟨fun h ↦ σ.injective (by rw [h, map_one]), fun h ↦ by rw [h, map_one]⟩

lemma isPrimitive_galoisConj [NeZero N] (σ : Gal(ℂ/ℚ)) {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) : (galoisConj χ σ).IsPrimitive :=
  hχ.ringHomComp σ.injective

/-- Galois conjugation as an action of `Gal(ℂ/ℚ)` on the primitive Dirichlet characters modulo
`N`. -/
noncomputable def galoisAction [NeZero N] :
    Gal(ℂ/ℚ) →* Equiv.Perm {χ : DirichletCharacter ℂ N // χ.IsPrimitive} where
  toFun σ := {
      toFun χ := ⟨galoisConj χ.1 σ, isPrimitive_galoisConj σ χ.2⟩
      invFun χ := ⟨galoisConj χ.1 σ⁻¹, isPrimitive_galoisConj σ⁻¹ χ.2⟩
      left_inv χ := by ext; simp
      right_inv χ := by ext; simp
  }
  map_one' := by ext; simp
  map_mul' σ τ := by ext; simp

end Deligne.GL1
