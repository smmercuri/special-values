/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import SpecialValues.Deligne.GL1.Galois

/-!
# GL(1): the critical integers of a Dirichlet character

The critical integers of the Artin motive of `χ`, stated explicitly in terms of the parity of
`χ` and without reference to the framework: `n ≥ 1` with the parity of `χ`, or `n ≤ 0` with the
opposite parity. `Deligne.GL1.isCritical_pkg_iff` identifies this with the framework's computed
critical set, which is the characterisation obligation `SpecialValues/Deligne/Pkg.lean` imposes
on an instance.

## Main definitions

* `Deligne.GL1.IsCritical`: the critical integers of `χ`.

## Main results

* `Deligne.GL1.isCritical_galoisConj_iff`: criticality is invariant under Galois conjugation.
* `Deligne.GL1.exists_isCritical`: every character has a critical integer.
* `Deligne.GL1.isCritical_one_iff`: the critical set of the trivial character is that of `ζ`.
* `Deligne.GL1.exists_isCritical_and_isCritical_iff`: two characters share a critical integer
  exactly when they have the same parity.
* `Deligne.GL1.isCritical_one_sub_iff`: the functional equation exchanges the two halves of the
  critical set.
-/

open Complex DirichletCharacter ZMod

namespace Deligne.GL1

variable {N : ℕ}

/-- An integer is critical for `χ` when it is positive and has the parity of `χ`, or is
non-positive and has the opposite parity. -/
def IsCritical (χ : DirichletCharacter ℂ N) (n : ℤ) : Prop :=
  (1 ≤ n ∧ (Even n ↔ χ.Even)) ∨ (n ≤ 0 ∧ ¬(Even n ↔ χ.Even))

lemma isCritical_galoisConj_iff (χ : DirichletCharacter ℂ N) (σ : Gal(ℂ/ℚ)) (n : ℤ) :
    IsCritical (galoisConj χ σ) n ↔ IsCritical χ n := by
  simp only [IsCritical, even_galoisConj]

lemma exists_isCritical (χ : DirichletCharacter ℂ N) : ∃ n : ℤ, IsCritical χ n := by
  rcases χ.even_or_odd with h | h
  · exact ⟨2, Or.inl ⟨by norm_num, iff_of_true even_two h⟩⟩
  · exact ⟨1, Or.inl ⟨le_rfl, iff_of_false (by norm_num) h.not_even⟩⟩

/-- The critical set of the trivial character is the critical set of `ζ`: the even integers
`≥ 2` and the odd integers `≤ -1`. -/
lemma isCritical_one_iff (n : ℤ) :
    IsCritical (1 : DirichletCharacter ℂ N) n ↔ (2 ≤ n ∧ 2 ∣ n) ∨ (n ≤ -1 ∧ ¬2 ∣ n) := by
  simp only [IsCritical, DirichletCharacter.even_one, iff_true, Int.even_iff]
  omega

/-- Two Dirichlet characters have a common critical integer exactly when they have the same
parity. -/
lemma exists_isCritical_and_isCritical_iff {N₁ N₂ : ℕ} {χ₁ : DirichletCharacter ℂ N₁}
    {χ₂ : DirichletCharacter ℂ N₂} :
    (∃ n : ℤ, IsCritical χ₁ n ∧ IsCritical χ₂ n) ↔ (χ₁.Even ↔ χ₂.Even) := by
  constructor
  · rintro ⟨n, h₁, h₂⟩
    rcases χ₁.even_or_odd with he₁ | ho₁ <;> rcases χ₂.even_or_odd with he₂ | ho₂
    · exact iff_of_true he₁ he₂
    · simp only [IsCritical, iff_true_intro he₁, iff_false_intro ho₂.not_even, iff_true,
        iff_false, Int.even_iff] at h₁ h₂
      omega
    · simp only [IsCritical, iff_false_intro ho₁.not_even, iff_true_intro he₂, iff_true,
        iff_false, Int.even_iff] at h₁ h₂
      omega
    · exact iff_of_false ho₁.not_even ho₂.not_even
  · intro h
    rcases χ₁.even_or_odd with he₁ | ho₁
    · exact ⟨2, Or.inl ⟨by norm_num, iff_of_true even_two he₁⟩,
        Or.inl ⟨by norm_num, iff_of_true even_two (h.mp he₁)⟩⟩
    · have hne₁ : ¬χ₁.Even := ho₁.not_even
      have hne₂ : ¬χ₂.Even := fun hh ↦ hne₁ (h.mpr hh)
      exact ⟨1, Or.inl ⟨le_rfl, iff_of_false (by norm_num) hne₁⟩,
        Or.inl ⟨le_rfl, iff_of_false (by norm_num) hne₂⟩⟩

/-- The functional equation `s ↦ 1 - s` exchanges the two halves of the critical set. -/
lemma isCritical_one_sub_iff {χ : DirichletCharacter ℂ N} {n : ℤ} (hn : 1 ≤ n) :
    IsCritical χ n ↔ IsCritical χ⁻¹ (1 - n) := by
  have hE : _root_.Even (1 - n) ↔ ¬_root_.Even n := by
    simp only [Int.even_iff]
    omega
  simp only [IsCritical, DirichletCharacter.even_inv_iff, hE]
  constructor
  · rintro (⟨-, h⟩ | ⟨h, -⟩)
    · exact Or.inr ⟨by omega, by tauto⟩
    · exact absurd hn (by omega)
  · rintro (⟨h, -⟩ | ⟨-, h⟩)
    · exact absurd hn (by omega)
    · exact Or.inl ⟨hn, by tauto⟩

end Deligne.GL1
