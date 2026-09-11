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

end Deligne.GL1
