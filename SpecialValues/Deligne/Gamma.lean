/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

/-!
# Deligne's archimedean Gamma factors at integer points

Facts about `Complex.Gammaℝ` and `Complex.Gammaℂ` that Deligne's conjecture needs and mathlib
does not record, together with `Complex.prodGammaℝ`, the product of shifted `Γℝ`'s that every
archimedean `L`-factor is. None of them mentions Deligne's conjecture, and all belong upstream.

## Main results

* `Complex.Gammaℝ_one_sub_div_Gammaℝ` and `Complex.Gammaℝ_two_sub_div_Gammaℝ_add_one`: the
  reflection formulae `Complex.inv_Gammaℝ_one_sub` and `Complex.inv_Gammaℝ_two_sub` as
  quotients. A functional equation compares `Λ(1 - s)` with `Λ(s)`, so it is the quotient of
  the two Gamma factors that occurs, not the inverse of either.
* `Complex.inv_Gammaℂ_natCast_add_one`: the value of `Gammaℂ` at a positive integer.
* `Complex.cos_natCast_mul_pi`: the complex counterpart of mathlib's `Real.cos_nat_mul_pi`.
* `Complex.Gammaℝ_intCast_eq_zero_iff`: mathlib's `Gammaℝ_eq_zero_iff` at integer arguments, with
  the existential eliminated. Since `Complex.Gamma` takes the value `0` at its poles, this says
  which integers are poles of `Gammaℝ`.
* `Complex.meromorphicOrderAt_Gammaℝ_add_nonpos` and
  `Complex.meromorphicOrderAt_Gammaℝ_add_neg_iff`: `Gammaℝ` has no zeros, so a shifted `Gammaℝ` is
  everywhere either regular or polar, and it is polar exactly where mathlib's junk value is `0`.
* `Complex.meromorphicOrderAt_Gammaℝ_add_intCast_nonneg_iff`: regularity at an integer, which is
  the form criticality is checked in.
* `Complex.prodGammaℝ`: the archimedean factor `∏ a, Γℝ(s + a)` attached to a multiset of integer
  shifts. Every archimedean `L`-factor has this shape, `Γℂ` included. It has no zeros of its own,
  so it is at every point either regular or polar
  (`Complex.meromorphicOrderAt_prodGammaℝ_nonpos`), and it is regular exactly when each of its
  factors is (`Complex.meromorphicOrderAt_prodGammaℝ_nonneg_iff`), which at an integer is
  arithmetic on the shifts (`Complex.meromorphicOrderAt_prodGammaℝ_intCast_nonneg_iff`).
-/

open Real
open scoped Nat

namespace Complex

/-- The cosine of an integer multiple of `π`. -/
lemma cos_natCast_mul_pi (m : ℕ) : cos ((m : ℂ) * (π : ℂ)) = (-1) ^ m := by
  rw [show ((m : ℂ) * (π : ℂ)) = ((m * π : ℝ) : ℂ) by push_cast; ring, ← ofReal_cos,
    Real.cos_nat_mul_pi]
  push_cast
  ring

/-- At an integer, `Gammaℝ` vanishes exactly at the non-positive even ones — which is where it has
a pole. -/
lemma Gammaℝ_intCast_eq_zero_iff {m : ℤ} : Gammaℝ (m : ℂ) = 0 ↔ m ≤ 0 ∧ Even m := by
  rw [Gammaℝ_eq_zero_iff, Int.even_iff]
  constructor
  · rintro ⟨j, hj⟩
    have hm : m = -(2 * (j : ℤ)) := by exact_mod_cast hj
    omega
  · rintro ⟨h₁, h₂⟩
    exact ⟨(-m / 2).toNat, by exact_mod_cast (by omega : m = -(2 * ((-m / 2).toNat : ℤ)))⟩

/-- `Gammaℝ` does not vanish at an odd integer. -/
lemma Gammaℝ_intCast_ne_zero_of_odd {m : ℤ} (hm : Odd m) : Gammaℝ (m : ℂ) ≠ 0 := by
  rw [Ne, Gammaℝ_intCast_eq_zero_iff]
  rintro ⟨-, h⟩
  rw [Int.even_iff] at h
  rw [Int.odd_iff] at hm
  omega

/-- The reflection formula for `Gammaℝ`, in quotient form. -/
lemma Gammaℝ_one_sub_div_Gammaℝ {s : ℂ} (hs : ∀ n : ℕ, s ≠ -n) :
    Gammaℝ (1 - s) / Gammaℝ s = (Gammaℂ s * cos (π * s / 2))⁻¹ := by
  have h₀ : Gammaℝ s ≠ 0 := by
    rw [Ne, Gammaℝ_eq_zero_iff]
    rintro ⟨n, hn⟩
    exact hs (2 * n) (by push_cast; linear_combination hn)
  have h : Gammaℝ (1 - s) = (Gammaℂ s * cos (π * s / 2))⁻¹ * Gammaℝ s := by
    rw [← inv_inv (Gammaℝ (1 - s)), inv_Gammaℝ_one_sub hs, mul_inv, inv_inv]
  rw [h, mul_div_assoc, div_self h₀, mul_one]

/-- The reflection formula for `Gammaℝ` shifted by one, in quotient form. -/
lemma Gammaℝ_two_sub_div_Gammaℝ_add_one {s : ℂ} (hs : ∀ n : ℕ, s ≠ -n) :
    Gammaℝ (2 - s) / Gammaℝ (s + 1) = (Gammaℂ s * sin (π * s / 2))⁻¹ := by
  have h₀ : Gammaℝ (s + 1) ≠ 0 := by
    rw [Ne, Gammaℝ_eq_zero_iff]
    rintro ⟨n, hn⟩
    exact hs (2 * n + 1) (by push_cast; linear_combination hn)
  have h : Gammaℝ (2 - s) = (Gammaℂ s * sin (π * s / 2))⁻¹ * Gammaℝ (s + 1) := by
    rw [← inv_inv (Gammaℝ (2 - s)), inv_Gammaℝ_two_sub hs, mul_inv, inv_inv]
  rw [h, mul_div_assoc, div_self h₀, mul_one]

/-- The value of `Gammaℂ` at a positive integer, as an inverse. -/
lemma inv_Gammaℂ_natCast_add_one (k : ℕ) :
    (Gammaℂ ((k : ℂ) + 1))⁻¹ = 2 ^ k * (π : ℂ) ^ (k + 1) / (k ! : ℂ) := by
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr pi_ne_zero
  have hk : ((k ! : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  rw [Gammaℂ_def, Gamma_nat_eq_factorial,
    show -((k : ℂ) + 1) = -(((k + 1 : ℕ) : ℂ)) by push_cast; ring, cpow_neg, cpow_natCast, mul_pow]
  field_simp
  ring

/-! ### `Gammaℝ` vanishes exactly where it has a pole -/

/-- `z ↦ (Gammaℝ (z + a))⁻¹` is entire. -/
lemma differentiable_inv_Gammaℝ_add (a : ℂ) :
    Differentiable ℂ fun z ↦ (Gammaℝ (z + a))⁻¹ :=
  differentiable_Gammaℝ_inv.comp (differentiable_id.add_const a)

lemma analyticOnNhd_inv_Gammaℝ_add (a : ℂ) :
    AnalyticOnNhd ℂ (fun z ↦ (Gammaℝ (z + a))⁻¹) Set.univ :=
  (differentiable_inv_Gammaℝ_add a).differentiableOn.analyticOnNhd isOpen_univ

lemma analyticAt_inv_Gammaℝ_add (a s : ℂ) :
    AnalyticAt ℂ (fun z ↦ (Gammaℝ (z + a))⁻¹) s :=
  analyticOnNhd_inv_Gammaℝ_add a s (Set.mem_univ s)

lemma inv_inv_Gammaℝ_add (a : ℂ) :
    (fun z ↦ Gammaℝ (z + a)) = (fun z ↦ (Gammaℝ (z + a))⁻¹)⁻¹ := by
  funext z
  simp

/-- A shifted `Gammaℝ` is meromorphic everywhere: it is the inverse of an entire function. -/
lemma meromorphicAt_Gammaℝ_add (a s : ℂ) : MeromorphicAt (fun z ↦ Gammaℝ (z + a)) s := by
  rw [inv_inv_Gammaℝ_add]
  exact (analyticAt_inv_Gammaℝ_add a s).meromorphicAt.inv

/-- `Gammaℝ⁻¹` is entire and takes the value `1` at `1`, so by the identity theorem it does not
vanish identically near any point and its analytic order there is finite. -/
lemma analyticOrderAt_inv_Gammaℝ_add_ne_top (a s : ℂ) :
    analyticOrderAt (fun z ↦ (Gammaℝ (z + a))⁻¹) s ≠ ⊤ := by
  intro h
  have hev : (fun z ↦ (Gammaℝ (z + a))⁻¹) =ᶠ[nhds s] 0 := by
    filter_upwards [analyticOrderAt_eq_top.mp h] with z hz using hz
  have hzero := (analyticOnNhd_inv_Gammaℝ_add a).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (Set.mem_univ s) hev
  have h₁ := hzero (Set.mem_univ (1 - a))
  simp only [Pi.zero_apply, show (1 - a) + a = 1 by ring, Gammaℝ_one, inv_one] at h₁
  exact one_ne_zero h₁

/-- The order of a shifted `Gammaℝ` at any point is `-n` for a natural number `n`, and `n = 0`
exactly when the value is nonzero. `Gammaℝ` is the inverse of an entire function, so it has no
zeros of its own: every point is either a regular point or a pole. -/
theorem meromorphicOrderAt_Gammaℝ_add_eq_neg (a s : ℂ) :
    ∃ n : ℕ, meromorphicOrderAt (fun z ↦ Gammaℝ (z + a)) s = ((-n : ℤ) : WithTop ℤ) ∧
      (Gammaℝ (s + a) = 0 ↔ n ≠ 0) := by
  have hg : AnalyticAt ℂ (fun z ↦ (Gammaℝ (z + a))⁻¹) s := analyticAt_inv_Gammaℝ_add a s
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (analyticOrderAt_inv_Gammaℝ_add_ne_top a s)
  refine ⟨n, ?_, ?_⟩
  · rw [inv_inv_Gammaℝ_add, meromorphicOrderAt_inv, hg.meromorphicOrderAt_eq, ← hn,
      ENat.map_natCast]
    simp
  · rw [← inv_eq_zero, ← hg.analyticOrderAt_ne_zero, ← hn]
    simp

/-- **The junk value is the pole.** `Gammaℝ (s + a) = 0` holds exactly when `z ↦ Gammaℝ (z + a)`
has a pole at `s`, in mathlib's own sense that its meromorphic order there is negative.

`Gammaℝ s = π ^ (-s / 2) * Γ (s / 2)` has no zeros — neither factor vanishes anywhere — so its
only zeros in mathlib are the junk values `Complex.Gamma` takes at its poles. Reading
"`γ s ≠ 0`" as "`γ` has no pole at `s`" is therefore a theorem about functions of this shape, not
a convention: for a general `f : ℂ → ℂ` a zero need not be a pole. -/
theorem meromorphicOrderAt_Gammaℝ_add_neg_iff {a s : ℂ} :
    meromorphicOrderAt (fun z ↦ Gammaℝ (z + a)) s < 0 ↔ Gammaℝ (s + a) = 0 := by
  obtain ⟨n, hord, hzero⟩ := meromorphicOrderAt_Gammaℝ_add_eq_neg a s
  rw [hord, hzero, show (0 : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) from rfl, WithTop.coe_lt_coe]
  omega

/-- A shifted `Gammaℝ` never has a zero, so its order is at most `0` everywhere. -/
lemma meromorphicOrderAt_Gammaℝ_add_nonpos (a s : ℂ) :
    meromorphicOrderAt (fun z ↦ Gammaℝ (z + a)) s ≤ 0 := by
  obtain ⟨n, hord, -⟩ := meromorphicOrderAt_Gammaℝ_add_eq_neg a s
  rw [hord, show (0 : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) from rfl, WithTop.coe_le_coe]
  omega

/-- At an integer, a shifted `Gammaℝ` is regular unless the shifted argument is a non-positive
even integer: those are its poles, and it has no other singularities. -/
theorem meromorphicOrderAt_Gammaℝ_add_intCast_nonneg_iff {a m : ℤ} :
    0 ≤ meromorphicOrderAt (fun z ↦ Gammaℝ (z + (a : ℂ))) (m : ℂ) ↔ Odd (m + a) ∨ 0 < m + a := by
  rw [← not_lt, meromorphicOrderAt_Gammaℝ_add_neg_iff,
    show ((m : ℂ) + (a : ℂ)) = (((m + a : ℤ)) : ℂ) by push_cast; ring,
    Gammaℝ_intCast_eq_zero_iff, Int.odd_iff, Int.even_iff]
  omega

/-! ### Products of shifted `Gammaℝ`'s -/

/-- The product of Deligne's archimedean Gamma factors with arguments shifted by the integers of a
multiset, possibly with repetition: `∏ a, Γℝ(s + a)`.

Every archimedean `L`-factor has this shape, `Γℂ` included:
`Complex.Gammaℝ_mul_Gammaℝ_add_one` splits `Γℂ(s - p)` into `Γℝ(s - p)` and `Γℝ(s - p + 1)`. -/
noncomputable def prodGammaℝ (shifts : Multiset ℤ) (s : ℂ) : ℂ :=
  (shifts.map fun a : ℤ ↦ Gammaℝ (s + a)).prod

@[simp]
lemma prodGammaℝ_zero : prodGammaℝ 0 = fun _ ↦ 1 := by
  funext; simp [prodGammaℝ]

lemma prodGammaℝ_cons (a : ℤ) (shifts : Multiset ℤ) :
    prodGammaℝ (a ::ₘ shifts) = (fun z ↦ Gammaℝ (z + a)) * prodGammaℝ shifts := by
  funext; simp [prodGammaℝ]

/-- For elements of `WithTop ℤ` that are at most `0`, a sum is non-negative exactly when both
summands are. -/
private lemma add_nonneg_iff_of_nonpos {x y : WithTop ℤ} (hx : x ≤ 0) (hy : y ≤ 0) :
    0 ≤ x + y ↔ 0 ≤ x ∧ 0 ≤ y := by
  refine ⟨fun h ↦ ?_, fun ⟨h₁, h₂⟩ ↦ by rw [le_antisymm hx h₁, le_antisymm hy h₂, add_zero]⟩
  refine ⟨?_, ?_⟩ <;> by_contra hlt <;> rw [not_le] at hlt
  · exact absurd (h.trans (add_le_add_right hy x |>.trans_eq (add_zero x))) hlt.not_ge
  · exact absurd (h.trans (add_le_add_left hx y |>.trans_eq (zero_add y))) hlt.not_ge

lemma meromorphicAt_prodGammaℝ (shifts : Multiset ℤ) (s : ℂ) :
    MeromorphicAt (prodGammaℝ shifts) s := by
  induction shifts using Multiset.induction with
  | empty => exact prodGammaℝ_zero ▸ analyticAt_const.meromorphicAt
  | cons a t ih => exact prodGammaℝ_cons a t ▸ (meromorphicAt_Gammaℝ_add _ s).mul ih

lemma meromorphicOrderAt_prodGammaℝ_zero (s : ℂ) : meromorphicOrderAt (prodGammaℝ 0) s = 0 := by
  rw [prodGammaℝ_zero, analyticAt_const.meromorphicOrderAt_eq,
    analyticAt_const.analyticOrderAt_eq_zero.mpr one_ne_zero]
  rfl

/-- `prodGammaℝ` has no zeros of its own, so at every point it is either regular or polar. -/
lemma meromorphicOrderAt_prodGammaℝ_nonpos (shifts : Multiset ℤ) (s : ℂ) :
    meromorphicOrderAt (prodGammaℝ shifts) s ≤ 0 := by
  induction shifts using Multiset.induction with
  | empty => exact (meromorphicOrderAt_prodGammaℝ_zero s).le
  | cons a t ih =>
    rw [prodGammaℝ_cons, meromorphicOrderAt_mul (meromorphicAt_Gammaℝ_add _ s)
      (meromorphicAt_prodGammaℝ t s)]
    exact add_nonpos (meromorphicOrderAt_Gammaℝ_add_nonpos _ s) ih

/-- `prodGammaℝ` is regular at `s` exactly when every one of its `Γℝ` factors is. -/
lemma meromorphicOrderAt_prodGammaℝ_nonneg_iff {shifts : Multiset ℤ} {s : ℂ} :
    0 ≤ meromorphicOrderAt (prodGammaℝ shifts) s ↔
      ∀ a ∈ shifts, 0 ≤ meromorphicOrderAt (fun z ↦ Gammaℝ (z + (a : ℂ))) s := by
  induction shifts using Multiset.induction with
  | empty => exact ⟨fun _ _ h ↦ absurd h (Multiset.notMem_zero _), fun _ ↦
      (meromorphicOrderAt_prodGammaℝ_zero s).ge⟩
  | cons a t ih =>
    rw [prodGammaℝ_cons, meromorphicOrderAt_mul (meromorphicAt_Gammaℝ_add _ s)
      (meromorphicAt_prodGammaℝ t s),
      add_nonneg_iff_of_nonpos (meromorphicOrderAt_Gammaℝ_add_nonpos _ s)
        (meromorphicOrderAt_prodGammaℝ_nonpos t s), ih]
    simp [Multiset.mem_cons, or_imp, forall_and]

/-- Regularity at an integer, in terms of the shifts: `Γℝ` has poles exactly at the non-positive
even integers. -/
lemma meromorphicOrderAt_prodGammaℝ_intCast_nonneg_iff {shifts : Multiset ℤ} {m : ℤ} :
    0 ≤ meromorphicOrderAt (prodGammaℝ shifts) (m : ℂ) ↔
      ∀ a ∈ shifts, Odd (m + a) ∨ 0 < m + a := by
  simp only [meromorphicOrderAt_prodGammaℝ_nonneg_iff,
    meromorphicOrderAt_Gammaℝ_add_intCast_nonneg_iff]

end Complex
