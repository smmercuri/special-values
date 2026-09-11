/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import SpecialValues.Deligne.GL1.Critical
import SpecialValues.Deligne.GL1.Period
import SpecialValues.Deligne.GL1.ValueField
import SpecialValues.Deligne.Pkg
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# GL(1): the Deligne package of primitive Dirichlet characters

This file assembles the data of the previous files — mathlib's `DirichletCharacter.LFunction`,
the value field `ℚ(χ)`, weight `0`, a single `Γℝ` shift `0` or `1` according to the parity of `χ`,
Deligne's period and `Deligne.GL1.galoisAction` — into a `Deligne.Pkg` on the primitive Dirichlet
characters modulo `N`, and discharges the obligations `SpecialValues/Deligne/Pkg.lean` imposes on
an instance: the framework's computed critical set is the explicit one of
`Deligne.GL1.IsCritical`, and every object has a critical integer.

## Main definitions

* `Deligne.GL1.pkg`: the Deligne package of primitive Dirichlet characters modulo `N`.

## Main results

* `Deligne.GL1.gammaFactor_pkg`: the framework's Gamma factor for the package is mathlib's own
  `DirichletCharacter.gammaFactor`, so the critical set is computed against an external object.
* `Deligne.GL1.isCritical_pkg_iff`: the framework's criticality predicate is
  `Deligne.GL1.IsCritical`.
* `Deligne.GL1.hasCriticalInteger_pkg`: every object has a critical integer.
-/

open Complex DirichletCharacter ZMod

namespace Deligne.GL1

variable {N : ℕ}

open scoped Classical in
/-- The Deligne package of primitive Dirichlet characters modulo `N`: mathlib's
`DirichletCharacter.LFunction`, the value field `ℚ(χ)`, weight `0`, a single `Γℝ` shift `0` or
`1` according to the parity of `χ`, the period `Deligne.GL1.period` and Galois conjugation. -/
noncomputable def pkg (N : ℕ) [NeZero N] :
    Pkg {χ : DirichletCharacter ℂ N // χ.IsPrimitive} where
  L χ := DirichletCharacter.LFunction χ.1
  valueField χ := valueField χ.1
  weight _ := 0
  gammaShifts χ := if χ.1.Even then {0} else {1}
  period χ n := period χ.1 n
  galoisAction := galoisAction
  weight_galoisAction _ _ := rfl
  gammaShifts_galoisAction σ χ := by simp [galoisAction]
  valueField_galoisAction σ χ := valueField_galoisConj σ χ.1
  valueField_isAlgebraic χ _ hx := isAlgebraic_of_mem_valueField χ.1 hx
  period_ne_zero' χ n _ _ := period_ne_zero χ.2 n

@[simp]
lemma coe_galoisAction_pkg [NeZero N] (σ : Gal(ℂ/ℚ))
    (M : {χ : DirichletCharacter ℂ N // χ.IsPrimitive}) :
    ((pkg N).galoisAction σ M).1 = galoisConj M.1 σ :=
  rfl

@[simp]
lemma L_pkg [NeZero N] (M : {χ : DirichletCharacter ℂ N // χ.IsPrimitive}) :
    (pkg N).L M = DirichletCharacter.LFunction M.1 :=
  rfl

/-- The value field of the GL(1) package is `ℚ(χ)`. -/
@[simp]
lemma valueField_pkg [NeZero N] (M : {χ : DirichletCharacter ℂ N // χ.IsPrimitive}) :
    (pkg N).valueField M = valueField M.1 :=
  rfl

/-- The framework's Gamma factor for the GL(1) package is mathlib's
`DirichletCharacter.gammaFactor`: the Artin motive of `χ` has Hodge type `(0, 0)`, so a single
`Γℝ`, shifted by `0` or `1` according to the parity of `χ`. -/
lemma gammaFactor_pkg [NeZero N]
    (M : {χ : DirichletCharacter ℂ N // χ.IsPrimitive}) (s : ℂ) :
    (pkg N).gammaFactor M s = DirichletCharacter.gammaFactor M.1 s := by
  rcases M.1.even_or_odd with h | h
  · simp [Pkg.gammaFactor, Complex.prodGammaℝ, pkg, h, h.gammaFactor_def]
  · simp [Pkg.gammaFactor, Complex.prodGammaℝ, pkg, h.not_even, h.gammaFactor_def]

/-- The GL(1) package has weight `0`, so the functional equation exchanges `n` and `1 - n`. -/
@[simp]
lemma weight_pkg [NeZero N] (M : {χ : DirichletCharacter ℂ N // χ.IsPrimitive}) :
    (pkg N).weight M = 0 := rfl

/-- The framework's criticality predicate, computed from the Gamma factor, is the explicit
condition of `Deligne.GL1.IsCritical`. -/
theorem isCritical_pkg_iff [NeZero N]
    (M : {χ : DirichletCharacter ℂ N // χ.IsPrimitive}) (n : ℤ) :
    (pkg N).IsCritical M n ↔ IsCritical M.1 n := by
  rw [Pkg.isCritical_iff, weight_pkg]
  rcases M.1.even_or_odd with h | h
  · simp only [IsCritical, iff_true_intro h, iff_true, show (pkg N).gammaShifts M = {0} by
      simp [pkg, h], Multiset.mem_singleton, forall_eq, Int.odd_iff, Int.even_iff]
    omega
  · simp only [IsCritical, iff_false_intro h.not_even, iff_false, show
      (pkg N).gammaShifts M = {1} by simp [pkg, h.not_even], Multiset.mem_singleton,
      forall_eq, Int.odd_iff, Int.even_iff]
    omega

/-- Every primitive character has a critical integer, which is the nondegeneracy obligation
`SpecialValues/Deligne/Pkg.lean` imposes on an instance. -/
theorem hasCriticalInteger_pkg [NeZero N]
    (M : {χ : DirichletCharacter ℂ N // χ.IsPrimitive}) :
    (pkg N).HasCriticalInteger M :=
  let ⟨n, hn⟩ := Deligne.GL1.exists_isCritical M.1
  ⟨n, (isCritical_pkg_iff M n).mpr hn⟩

end Deligne.GL1
