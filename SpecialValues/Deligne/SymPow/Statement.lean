/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import SpecialValues.Deligne.SymPow.Critical
import SpecialValues.Deligne.SymPow.LFunction
import SpecialValues.Deligne.SymPow.Period
import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Deligne's conjecture for the odd symmetric powers of an elliptic curve

`Deligne.SymPow.Conjecture` is the statement, for an elliptic curve `E` over `ℚ` given by a
`WeierstrassCurve ℚ` together with its Frobenius traces `a` and its bad primes `S`:
`Λ(m + 1)` divided by `Deligne.SymPow.criticalPeriod` is rational, where `Λ` is the `Sym^(2m+1)`
`L`-function of `E` and the period is built from the real and imaginary periods `Ω⁺`, `Ω⁻`
of `E`. It is the assembly of the
three previous files: the critical point `m + 1` is the whole critical set
(`Deligne.SymPow.isCritical_iff_of_odd`), `Λ` is pinned by `Deligne.SymPow.IsLFunction` and the
periods by `IsRealPeriod`, `IsImagPeriod`.

Nothing here is a degree of freedom, and the three inputs are unfree in three different ways.
`Ω⁺` and `Ω⁻` are *derived*: `PeriodPair.realPeriod` and `PeriodPair.imagPeriod` are functions of
the lattice, so the statement names them rather than quantifying over them, and
`Deligne.SymPow.conjecture_iff_forall_isPeriod` shows that choosing them costs nothing. The
lattice is *quantified over*, because recovering it from `(g₂, g₃)` is uniformisation, which
mathlib does not have — but the converse direction is constructible, and
`PeriodPair.uniformises_ofG₂G₃` uses it to witness that the hypothesis on the lattice is
satisfiable rather than merely assumed. `Λ` is quantified over and cannot be otherwise: no
`Sym^k` `L`-function exists in mathlib to name. See `blueprint/src/sympow.tex`
§`rem:sympow-relative-fails` for the failure mode this avoids and §`rem:sympow-residue` for what
remains assumed.

## From a Weierstrass model to a period pair

`PeriodPair.Uniformises` compares a lattice against a pair of rationals `(g₂, g₃)`, the
invariants of the model `y² = 4x³ - g₂x - g₃`, while mathlib's `WeierstrassCurve` carries
`a₁, …, a₆`. `WeierstrassCurve.g₂` and `WeierstrassCurve.g₃` are the translation, `c₄ / 12` and
`c₆ / 216`; `WeierstrassCurve.g₂_of_isShortNF` and
`WeierstrassCurve.g₃_of_isShortNF` check them against mathlib's short normal form
`WeierstrassCurve.IsShortNF`, `y² = x³ + a₄x + a₆`, and `WeierstrassCurve.variableChange_g₂`,
`WeierstrassCurve.variableChange_g₃` record that they scale as `u⁻⁴` and `u⁻⁶`, so a change of
model changes the lattice by the same scalar and the correspondence is consistent.

The other direction, `WeierstrassCurve.ofG₂G₃`, is the one that can be *built*: a period pair
has invariants `(g₂, g₃)`, and if they are rational then `y² = 4x³ - g₂x - g₃` is a curve over
`ℚ` that it uniformises (`PeriodPair.uniformises_ofG₂G₃`). Going the other way — from a curve to
its period lattice — is the uniformisation theorem, which mathlib does not have, and it is
carried as the hypothesis `hunif` of `Deligne.SymPow.conjecture_iff_framework`.

## The period at the critical point

`Deligne.SymPow.criticalPeriod` is Deligne's `c⁺(Sym^(2m+1) h¹(E)(m + 1))` up to `ℚˣ`, computed
in `blueprint/src/sympow.tex` §`cor:sympow-period-crit`. Its exponents are
`Deligne.SymPow.realExponent` and `Deligne.SymPow.imagExponent`, which sum to `(m + 1)^2`, the
rank of the eigenspace, and `Deligne.SymPow.twoPiIExponent`. That last one is the one exponent no
other check in the chapter constrains (§`rem:period-delta-check`), which is why it is named and
calibrated rather than written inline.

## Main results

* `WeierstrassCurve.g₂`, `WeierstrassCurve.g₃` and their calibration against the short model
  (`WeierstrassCurve.IsShortNF`) and against a change of model.
* `Deligne.SymPow.realExponent`, `Deligne.SymPow.imagExponent`,
  `Deligne.SymPow.realExponent_add_imagExponent`.
* `Deligne.SymPow.twoPiIExponent` and `Deligne.SymPow.twoPiIExponent_add_sq`, the calibration of
  the power of `2πi` against Deligne's `γ`.
* `Deligne.SymPow.criticalPeriod`, with `Deligne.SymPow.criticalPeriod_zero` recovering the
  classical `L^S(E, 1) / Ω⁺` at `m = 0` and
  `Deligne.SymPow.criticalPeriod_ne_zero_of_conj_mem` ruling out a division by zero.
* `WeierstrassCurve.ofG₂G₃` and `PeriodPair.uniformises_ofG₂G₃`: the curve a period pair with
  rational invariants uniformises.
* `Deligne.SymPow.Conjecture`, with `Deligne.SymPow.conjecture_iff_forall_isPeriod` showing that
  naming the two periods is no loss over quantifying over them.
* `Deligne.SymPow.pkg`: the Deligne package of `Sym^(2m+1) h¹(E)`, carrying `Λ`, the Hodge
  data, the value field `ℚ` and the period above.
* `Deligne.SymPow.conjecture_iff_framework`: the statement is the instance of
  `Deligne.Pkg.Conjecture` at any package carrying the same data. Uniformisation — that
  `(g₂, g₃)` determines the period pair — is an explicit hypothesis there, as it is throughout
  this chapter.
-/

open Complex ComplexConjugate

open scoped Real

/-! ### The invariants of a Weierstrass model -/

namespace WeierstrassCurve

variable (W : WeierstrassCurve ℚ)

/-- The invariant `g₂` of the model `y² = 4x³ - g₂x - g₃` of a Weierstrass curve over `ℚ`. -/
def g₂ : ℚ := W.c₄ / 12

/-- The invariant `g₃` of the model `y² = 4x³ - g₂x - g₃` of a Weierstrass curve over `ℚ`. -/
def g₃ : ℚ := W.c₆ / 216

variable {W}

theorem g₂_of_isShortNF [W.IsShortNF] : W.g₂ = -4 * W.a₄ := by
  rw [g₂, c₄_of_isShortNF]
  ring

theorem g₃_of_isShortNF [W.IsShortNF] : W.g₃ = -4 * W.a₆ := by
  rw [g₃, c₆_of_isShortNF]
  ring

/-- The Weierstrass model `y² = 4x³ - g₂x - g₃`, written in the `a₁, …, a₆` coordinates. -/
def ofG₂G₃ (g₂ g₃ : ℚ) : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := -g₂ / 4
  a₆ := -g₃ / 4

instance isShortNF_ofG₂G₃ (g₂ g₃ : ℚ) : (ofG₂G₃ g₂ g₃).IsShortNF := ⟨rfl, rfl, rfl⟩

@[simp]
theorem g₂_ofG₂G₃ (g₂ g₃ : ℚ) : (ofG₂G₃ g₂ g₃).g₂ = g₂ := by
  rw [g₂_of_isShortNF]
  change -4 * (-g₂ / 4) = g₂
  ring

@[simp]
theorem g₃_ofG₂G₃ (g₂ g₃ : ℚ) : (ofG₂G₃ g₂ g₃).g₃ = g₃ := by
  rw [g₃_of_isShortNF]
  change -4 * (-g₃ / 4) = g₃
  ring

variable (C : VariableChange ℚ) (W)

theorem variableChange_g₂ : (C • W).g₂ = C.u⁻¹ ^ 4 * W.g₂ := by
  simp only [g₂, variableChange_c₄, mul_div_assoc]

theorem variableChange_g₃ : (C • W).g₃ = C.u⁻¹ ^ 6 * W.g₃ := by
  simp only [g₃, variableChange_c₆, mul_div_assoc]

end WeierstrassCurve

/-- A period pair whose invariants are rational uniformises an actual Weierstrass curve over `ℚ`,
namely `WeierstrassCurve.ofG₂G₃` of those invariants. -/
theorem PeriodPair.uniformises_ofG₂G₃ {ℒ : PeriodPair} {g₂ g₃ : ℚ} (h : ℒ.Uniformises g₂ g₃) :
    ℒ.Uniformises (WeierstrassCurve.ofG₂G₃ g₂ g₃).g₂ (WeierstrassCurve.ofG₂G₃ g₂ g₃).g₃ := by
  rwa [WeierstrassCurve.g₂_ofG₂G₃, WeierstrassCurve.g₃_ofG₂G₃]

namespace Deligne.SymPow

/-! ### The period at the critical point -/

/-- The exponent `(m + 1)(m + 1 + (-1)^m) / 2` of `Ω⁺` in Deligne's period of
`Sym^(2m+1) h¹(E)(m + 1)`. -/
def realExponent (m : ℕ) : ℕ := if Even m then (m + 1) * (m + 2) / 2 else m * (m + 1) / 2

/-- The exponent `(m + 1)(m + 1 - (-1)^m) / 2` of `Ω⁻` in Deligne's period of
`Sym^(2m+1) h¹(E)(m + 1)`. -/
def imagExponent (m : ℕ) : ℕ := if Even m then m * (m + 1) / 2 else (m + 1) * (m + 2) / 2

@[simp]
theorem realExponent_zero : realExponent 0 = 1 := by norm_num [realExponent]

@[simp]
theorem imagExponent_zero : imagExponent 0 = 0 := by norm_num [imagExponent]

/-- The rank `(m + 1)^2` of the eigenspace whose determinant the period is. -/
theorem realExponent_add_imagExponent (m : ℕ) :
    realExponent m + imagExponent m = (m + 1) ^ 2 := by
  obtain ⟨t, ht⟩ := Nat.even_mul_succ_self m
  have hsucc : (m + 1) * (m + 2) = m * (m + 1) + 2 * (m + 1) := by ring
  have hsq : (m + 1) ^ 2 = m * (m + 1) + (m + 1) := by ring
  simp only [realExponent, imagExponent, hsucc, hsq, ht]
  split_ifs <;> omega

/-- The exponent `m(m+1)/2` of `2πi` in Deligne's period of `Sym^(2m+1) h¹(E)(m + 1)`. -/
def twoPiIExponent (m : ℕ) : ℕ := m * (m + 1) / 2

@[simp]
theorem twoPiIExponent_zero : twoPiIExponent 0 = 0 := rfl

/-- The halving in `twoPiIExponent` is exact. -/
theorem two_mul_twoPiIExponent (m : ℕ) : 2 * twoPiIExponent m = m * (m + 1) := by
  obtain ⟨t, ht⟩ := Nat.even_mul_succ_self m
  simp only [twoPiIExponent, ht]
  omega

/-- The exponent of `2πi` against Deligne's `γ = (m+1)(3m+2)/2`: the twist at `m + 1` contributes
`(m + 1)^2` and the comparison determinant contributes `γ`, and the period carries the
difference. -/
theorem twoPiIExponent_add_sq (m : ℕ) :
    twoPiIExponent m + (m + 1) ^ 2 = (m + 1) * (3 * m + 2) / 2 := by
  have h := two_mul_twoPiIExponent m
  have hγ : (m + 1) * (3 * m + 2) = 3 * (m * (m + 1)) + 2 * (m + 1) := by ring
  have hsq : (m + 1) ^ 2 = m * (m + 1) + (m + 1) := by ring
  rw [hγ, hsq, ← h]
  omega

/-- Deligne's period `c⁺(Sym^(2m+1) h¹(E)(m + 1))`, up to `ℚˣ`, in terms of the real and
imaginary periods of `E`. -/
noncomputable def criticalPeriod (m : ℕ) (Ωre Ωim : ℂ) : ℂ :=
  Ωre ^ realExponent m * Ωim ^ imagExponent m / (2 * π * I) ^ twoPiIExponent m

/-- A real period of `E`, at `m = 0`. -/
@[simp]
theorem criticalPeriod_zero (Ωre Ωim : ℂ) : criticalPeriod 0 Ωre Ωim = Ωre := by
  simp [criticalPeriod]

theorem criticalPeriod_ne_zero {m : ℕ} {Ωre Ωim : ℂ} (hre : Ωre ≠ 0) (him : Ωim ≠ 0) :
    criticalPeriod m Ωre Ωim ≠ 0 :=
  div_ne_zero (mul_ne_zero (pow_ne_zero _ hre) (pow_ne_zero _ him))
    (pow_ne_zero _ Complex.two_pi_I_ne_zero)

/-- The period built from any real and any imaginary period of a lattice stable under complex
conjugation is nonzero. -/
theorem criticalPeriod_ne_zero_of_isPeriod {ℒ : PeriodPair} {Ωre Ωim : ℂ} (m : ℕ)
    (hstab : ∀ z ∈ ℒ.lattice, conj z ∈ ℒ.lattice) (hΩre : IsRealPeriod ℒ.lattice Ωre)
    (hΩim : IsImagPeriod ℒ.lattice Ωim) : criticalPeriod m Ωre Ωim ≠ 0 :=
  criticalPeriod_ne_zero (hΩre.ne_zero hstab) (hΩim.ne_zero hstab)

/-- The period the statement divides by is nonzero, so the quotient is a genuine one. -/
theorem criticalPeriod_ne_zero_of_conj_mem {ℒ : PeriodPair} (m : ℕ)
    (hstab : ∀ z ∈ ℒ.lattice, conj z ∈ ℒ.lattice) :
    criticalPeriod m ℒ.realPeriod ℒ.imagPeriod ≠ 0 :=
  criticalPeriod_ne_zero_of_isPeriod m hstab ℒ.isRealPeriod_realPeriod ℒ.isImagPeriod_imagPeriod

/-! ### The statement -/

/-- The critical value of the `Sym^(2m+1)` `L`-function divided by Deligne's period. -/
noncomputable def normalizedLValue (m : ℕ) (Λ : ℂ → ℂ) (Ωre Ωim : ℂ) : ℂ :=
  Λ (m + 1) / criticalPeriod m Ωre Ωim

/-- Rationality of the normalised value does not see the sign by which two real, or two
imaginary, periods of the same lattice differ. -/
theorem normalizedLValue_mem_bot_congr {m : ℕ} {Λ : ℂ → ℂ} {Ωre Ωim Ωre' Ωim' : ℂ}
    (hre : Ωre' = Ωre ∨ Ωre' = -Ωre) (him : Ωim' = Ωim ∨ Ωim' = -Ωim) :
    normalizedLValue m Λ Ωre' Ωim' ∈ (⊥ : IntermediateField ℚ ℂ) ↔
      normalizedLValue m Λ Ωre Ωim ∈ (⊥ : IntermediateField ℚ ℂ) := by
  have hpow : ∀ (k : ℕ) {x y : ℂ}, (x = y ∨ x = -y) → x ^ k = y ^ k ∨ x ^ k = -y ^ k := by
    rintro k x y (rfl | rfl)
    · exact Or.inl rfl
    · exact (Nat.even_or_odd k).imp (fun h ↦ h.neg_pow y) fun h ↦ h.neg_pow y
  obtain ere | ere := hpow (realExponent m) hre <;>
    obtain eim | eim := hpow (imagExponent m) him <;>
    simp only [normalizedLValue, criticalPeriod, ere, eim, neg_mul, mul_neg, neg_neg, neg_div,
      div_neg, neg_mem_iff]

/-- The Deligne package of `Sym^(2m+1) h¹(E)`, for an `L`-function `Λ` and a period pair `ℒ`
whose lattice is stable under complex conjugation. The index type is `Unit`: this is one motive,
and `m`, `Λ`, `ℒ` are parameters of the package rather than objects of it. Away from the critical
integer `m + 1` the period is the junk value `1`; see the comment in the definition. -/
noncomputable def pkg (m : ℕ) (Λ : ℂ → ℂ) (ℒ : PeriodPair)
    (hstab : ∀ z ∈ ℒ.lattice, conj z ∈ ℒ.lattice) : Pkg Unit where
  L _ := Λ
  valueField _ := ⊥
  weight := 2 * m + 1
  gammaShifts _ := shifts (2 * m + 1)
  -- `1` is not a period of anything. It is invisible, because `Deligne.Pkg.IsArithmetic` and
  -- `Deligne.Pkg.IsEquivariant` quantify only over critical integers and `isCritical_pkg_iff`
  -- says the only one is `m + 1`; but it is unconstrained data of exactly the kind this
  -- development objects to elsewhere, and it is the symptom of `period` being a field
  -- rather than a computed quantity. See `blueprint/src/sympow.tex` §`rem:sympow-pkg-junk`.
  period _ n := if n = (m : ℤ) + 1 then criticalPeriod m ℒ.realPeriod ℒ.imagPeriod else 1
  galoisAction := 1
  gammaShifts_galoisAction _ _ := rfl
  valueField_galoisAction _ _ := (IntermediateField.map_bot _).symm
  valueField_isAlgebraic _ _ hx := IntermediateField.isAlgebraic_of_mem_bot hx
  period_ne_zero' _ n _ _ := by
    split_ifs
    · exact criticalPeriod_ne_zero_of_conj_mem m hstab
    · exact one_ne_zero

section Pkg

variable {m : ℕ} {Λ : ℂ → ℂ} {ℒ : PeriodPair} {hstab : ∀ z ∈ ℒ.lattice, conj z ∈ ℒ.lattice}

@[simp]
theorem L_pkg (M : Unit) : (pkg m Λ ℒ hstab).L M = Λ := rfl

@[simp]
theorem weight_pkg : (pkg m Λ ℒ hstab).weight = 2 * m + 1 := rfl

@[simp]
theorem gammaShifts_pkg (M : Unit) :
    (pkg m Λ ℒ hstab).gammaShifts M = shifts (2 * m + 1) := rfl

@[simp]
theorem valueField_pkg (M : Unit) : (pkg m Λ ℒ hstab).valueField M = ⊥ := rfl

@[simp]
theorem galoisAction_pkg (σ : Gal(ℂ/ℚ)) (M : Unit) :
    (pkg m Λ ℒ hstab).galoisAction σ M = M := Subsingleton.elim _ _

/-- The period of the package at its one critical integer. -/
theorem period_pkg_of_eq (M : Unit) :
    (pkg m Λ ℒ hstab).period M ((m : ℤ) + 1)
      = criticalPeriod m ℒ.realPeriod ℒ.imagPeriod := ite_eq_left rfl

/-- The framework's critical set for the package is the single integer `m + 1`. -/
theorem isCritical_pkg_iff (M : Unit) (n : ℤ) :
    (pkg m Λ ℒ hstab).IsCritical M n ↔ n = (m : ℤ) + 1 :=
  isCritical_iff_of_odd _ weight_pkg (gammaShifts_pkg M) n

/-- The nondegeneracy obligation `SpecialValues/Deligne/Pkg.lean` imposes on an instance. -/
theorem hasCriticalInteger_pkg (M : Unit) : (pkg m Λ ℒ hstab).HasCriticalInteger M :=
  hasCriticalInteger_of_odd _ weight_pkg (gammaShifts_pkg M)

/-- The framework's conjecture at the package is the rationality of the normalised value. -/
theorem conjecture_pkg_iff (M : Unit) :
    (pkg m Λ ℒ hstab).Conjecture M ↔
      normalizedLValue m Λ ℒ.realPeriod ℒ.imagPeriod ∈ (⊥ : IntermediateField ℚ ℂ) := by
  have hcast : ((((m : ℤ) + 1 : ℤ)) : ℂ) = (m : ℂ) + 1 := by push_cast; ring
  have hval : (pkg m Λ ℒ hstab).normalizedValue M ((m : ℤ) + 1)
      = normalizedLValue m Λ ℒ.realPeriod ℒ.imagPeriod := by
    rw [Pkg.normalizedValue, period_pkg_of_eq, L_pkg, hcast, normalizedLValue]
  have harith : (pkg m Λ ℒ hstab).IsArithmetic M ↔
      normalizedLValue m Λ ℒ.realPeriod ℒ.imagPeriod ∈ (⊥ : IntermediateField ℚ ℂ) := by
    refine ⟨fun h ↦ ?_, fun h n hn ↦ ?_⟩
    · rw [← hval, ← valueField_pkg M]
      exact h _ ((isCritical_pkg_iff M _).mpr rfl)
    · rw [(isCritical_pkg_iff M n).mp hn, hval, valueField_pkg]
      exact h
  exact ⟨fun h ↦ harith.mp h.1, fun h ↦ ⟨harith.mpr h,
    (harith.mpr h).isEquivariant_of_valueField_eq_bot (valueField_pkg M)
      fun σ ↦ galoisAction_pkg σ M⟩⟩

end Pkg

/-- Deligne's conjecture for `Sym^(2m+1) h¹(E)`, with `E` the elliptic curve `W` over `ℚ`, `a`
its Frobenius traces and `S` its bad primes: the framework's conjecture at
`Deligne.SymPow.pkg`. -/
def Conjecture (m : ℕ) (a : ℕ → ℤ) (S : Set ℕ) (W : WeierstrassCurve ℚ) : Prop :=
  ∀ (Λ : ℂ → ℂ) (ℒ : PeriodPair), IsLFunction (2 * m + 1) a S Λ → ℒ.Uniformises W.g₂ W.g₃ →
    ∀ hstab : ∀ z ∈ ℒ.lattice, conj z ∈ ℒ.lattice, (pkg m Λ ℒ hstab).Conjecture ()

/-- Choosing the two periods loses nothing: the statement at `PeriodPair.realPeriod` and
`PeriodPair.imagPeriod` holds exactly when it holds at every real and every imaginary period. -/
theorem conjecture_iff_forall_isPeriod {m : ℕ} {a : ℕ → ℤ} {S : Set ℕ} {W : WeierstrassCurve ℚ} :
    Conjecture m a S W ↔ ∀ (Λ : ℂ → ℂ) (ℒ : PeriodPair) (Ωre Ωim : ℂ),
      IsLFunction (2 * m + 1) a S Λ → ℒ.Uniformises W.g₂ W.g₃ →
      (∀ z ∈ ℒ.lattice, conj z ∈ ℒ.lattice) → IsRealPeriod ℒ.lattice Ωre →
      IsImagPeriod ℒ.lattice Ωim → normalizedLValue m Λ Ωre Ωim ∈ (⊥ : IntermediateField ℚ ℂ) := by
  refine ⟨fun h Λ ℒ Ωre Ωim hΛ hU hstab hΩre hΩim ↦ ?_, fun h Λ ℒ hΛ hU hstab ↦ ?_⟩
  · exact (normalizedLValue_mem_bot_congr hΩre.eq_or_eq_neg_realPeriod
      hΩim.eq_or_eq_neg_imagPeriod).mpr ((conjecture_pkg_iff ()).mp (h Λ ℒ hΛ hU hstab))
  · exact (conjecture_pkg_iff ()).mpr
      (h Λ ℒ _ _ hΛ hU hstab ℒ.isRealPeriod_realPeriod ℒ.isImagPeriod_imagPeriod)

/-- Deligne's conjecture for `Sym^(2m+1) h¹(E)` is the framework's conjecture at any package
whose `L`-function at `M` is `Λ`, whose weight, shifts, value field and period are those of
`Sym^(2m+1) h¹(E)`, and whose period pair is determined by `(g₂, g₃)`. -/
theorem conjecture_iff_framework {Ω : Type*} (F : Pkg Ω) {M : Ω} {m : ℕ} {a : ℕ → ℤ}
    {S : Set ℕ} {W : WeierstrassCurve ℚ} {Λ : ℂ → ℂ} {ℒ : PeriodPair}
    (hΛ : IsLFunction (2 * m + 1) a S Λ) (hU : ℒ.Uniformises W.g₂ W.g₃)
    (hstab : ∀ z ∈ ℒ.lattice, conj z ∈ ℒ.lattice)
    (hunif : ∀ ℒ' : PeriodPair, ℒ'.Uniformises W.g₂ W.g₃ → ℒ' = ℒ)
    (hw : F.weight = 2 * m + 1) (hs : F.gammaShifts M = shifts (2 * m + 1))
    (hE : F.valueField M = ⊥) (hgal : ∀ σ : Gal(ℂ/ℚ), F.galoisAction σ M = M) (hL : F.L M = Λ)
    (hc : F.period M ((m : ℤ) + 1) = criticalPeriod m ℒ.realPeriod ℒ.imagPeriod) :
    F.Conjecture M ↔ Conjecture m a S W := by
  have hcast : ((((m : ℤ) + 1 : ℤ)) : ℂ) = (m : ℂ) + 1 := by push_cast; ring
  have hval : F.normalizedValue M ((m : ℤ) + 1)
      = normalizedLValue m Λ ℒ.realPeriod ℒ.imagPeriod := by
    rw [Pkg.normalizedValue, hL, hc, hcast, normalizedLValue]
  have harith : F.IsArithmetic M ↔
      normalizedLValue m Λ ℒ.realPeriod ℒ.imagPeriod ∈ (⊥ : IntermediateField ℚ ℂ) := by
    refine ⟨fun h ↦ ?_, fun h n hn ↦ ?_⟩
    · rw [← hval, ← hE]
      exact h _ ((isCritical_iff_of_odd F hw hs _).mpr rfl)
    · rw [(isCritical_iff_of_odd F hw hs n).mp hn, hval, hE]
      exact h
  have hcon : F.Conjecture M ↔ F.IsArithmetic M :=
    ⟨And.left, fun h ↦ ⟨h, h.isEquivariant_of_valueField_eq_bot hE hgal⟩⟩
  rw [hcon, harith, conjecture_iff_forall_isPeriod]
  refine ⟨fun h Λ' ℒ' Ωre Ωim hΛ' hU' _ hΩre hΩim ↦ ?_,
    fun h ↦ h Λ ℒ _ _ hΛ hU hstab ℒ.isRealPeriod_realPeriod ℒ.isImagPeriod_imagPeriod⟩
  obtain rfl : Λ' = Λ := hΛ'.unique hΛ
  obtain rfl : ℒ' = ℒ := hunif ℒ' hU'
  exact (normalizedLValue_mem_bot_congr hΩre.eq_or_eq_neg_realPeriod
    hΩim.eq_or_eq_neg_imagPeriod).mpr h

end Deligne.SymPow
