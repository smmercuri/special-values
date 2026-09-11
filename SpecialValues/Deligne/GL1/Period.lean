/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import SpecialValues.Deligne.DirichletCharacter

/-!
# GL(1): Deligne's period

Deligne's period `c⁺(M(χ)(n))` for the Artin motive of a primitive Dirichlet character `χ`: the
Gauss sum `τ(χ)` times `(2πi) ^ n` for `n ≥ 1`, and `1` for `n ≤ 0`. The branch is where `c⁺` and
`c⁻` exchange roles as `n` crosses the centre of the critical strip.

## Main definitions

* `Deligne.GL1.period`: the period.

## Main results

* `Deligne.GL1.period_ne_zero`: the period of a primitive character never vanishes, which is the
  requirement `Deligne.Pkg` places on a period; primitivity enters through the non-vanishing of
  the Gauss sum (`DirichletCharacter.IsPrimitive.gaussSum_ne_zero`).
-/

open Complex DirichletCharacter ZMod

namespace Deligne.GL1

variable {N : ℕ}

/-- Deligne's period `c⁺(M(χ)(n))`: the Gauss sum of `χ` times `(2πi) ^ n` for `n ≥ 1`, and `1`
for `n ≤ 0`. -/
noncomputable def period [NeZero N] (χ : DirichletCharacter ℂ N) (n : ℤ) : ℂ :=
  if 1 ≤ n then gaussSum χ stdAddChar * (2 * (Real.pi : ℂ) * I) ^ n else 1

lemma period_of_one_le [NeZero N] {χ : DirichletCharacter ℂ N} {n : ℤ} (hn : 1 ≤ n) :
    period χ n = gaussSum χ stdAddChar * (2 * (Real.pi : ℂ) * I) ^ n :=
  ite_eq_left hn

lemma period_of_nonpos [NeZero N] {χ : DirichletCharacter ℂ N} {n : ℤ} (hn : n ≤ 0) :
    period χ n = 1 :=
  ite_eq_right (by omega)

lemma period_ne_zero [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (n : ℤ) :
    period χ n ≠ 0 := by
  rw [period]
  split
  · exact mul_ne_zero hχ.gaussSum_ne_zero (zpow_ne_zero _ (by simp [Real.pi_ne_zero, I_ne_zero]))
  · exact one_ne_zero

end Deligne.GL1
