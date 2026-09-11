/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Determining the `L`-function of `Sym^k h¹(E)`

Deligne's conjecture for `Sym^k h¹(E)` is a statement about an `L`-function that mathlib
cannot construct: that `L(Sym^k E, s)` continues to a meromorphic function on `ℂ` is symmetric
power functoriality, a theorem of Newton–Thorne, and nothing anywhere near it is formalised.
This file supplies what keeps the eventual statement faithful rather than relative —
`Deligne.SymPow.IsLFunction`, a hypothesis on a function `Λ : ℂ → ℂ` saying that it *is* the
`Sym^k` `L`-function, together with `Deligne.SymPow.IsLFunction.unique`, which says that the
hypothesis pins `Λ` down completely. A hypothesis that determines its subject offers nothing to
choose, so it cannot be chosen to make the conclusion true; that is what separates this from
the failure mode of `blueprint/src/sympow.tex` §`rem:sympow-relative-fails`. Nothing here
asserts that such a `Λ` exists — but something does, so the hypothesis is not vacuous.

The `L`-function is pinned by its Euler factors. At a prime of good reduction, Frobenius acts
on the rank-two `h¹(E)` with eigenvalues `α, β` satisfying `α + β = a_p` and `α β = p`, so on
`Sym^k` it has eigenvalues `α^i β^(k - i)` for `0 ≤ i ≤ k` and the local factor is
`∏ i ∈ range (k + 1), (1 - α^i β^(k - i) T)`. Only `a_p` and `p` are given, never `α` and `β`
separately, so `Deligne.SymPow.eulerFactor` takes the sum and the product and chooses a root
pair; `Deligne.SymPow.eulerFactor_eq_of_roots` says the choice does not matter, because the two
admissible choices differ by a swap and the product is invariant under reindexing by `i ↦ k - i`.

## Why normal form appears in the definition

`MeromorphicAt f x` constrains `f` only on `𝓝[≠] x`, so the value of a meromorphic function
*at* a pole is unconstrained. Without a normalisation, uniqueness is therefore false rather
than merely hard: given any `Λ` meeting the Euler product condition and any `z₀` outside the
half-plane, `fun z ↦ if z = z₀ then Λ z + 1 else Λ z` meets it too, since multiplying by one
extra factor of `z - z₀` erases the difference. `MeromorphicNFOn` is mathlib's canonical
representative of a meromorphic function up to equality off a discrete set — analytic at `x`,
or a pole at `x` with value `0` — and `IsLFunction` asks for it. With that clause the
uniqueness is genuine equality of functions.

## Main results

* `quadraticRoots`, `quadraticRoots_add`, `quadraticRoots_mul`: over an algebraically closed
  field, a choice of pair with prescribed sum and product.
* `MeromorphicNFOn.eq_of_eventuallyEq`: the identity theorem for meromorphic functions on `ℂ`
  in normal form, the analogue of `AnalyticOnNhd.eq_of_eventuallyEq`.
* `Deligne.SymPow.eulerFactor` and `Deligne.SymPow.eulerFactor_eq_of_roots`: the local factor
  of `Sym^k` and its independence of the choice of Frobenius eigenvalues, with
  `Deligne.SymPow.eulerFactor_zero` and `Deligne.SymPow.eulerFactor_one` calibrating it against
  `ζ` and against the local polynomial of `E` itself.
* `Deligne.SymPow.IsLFunction` and `Deligne.SymPow.IsLFunction.unique`.
-/

open Filter Set

open scoped Topology

section QuadraticRoots

variable {K : Type*} [Field K] [IsAlgClosed K] (a q : K)

open Polynomial in
/-- Over an algebraically closed field, every pair `(a, q)` is the sum and the product of some
pair of elements. -/
theorem exists_quadraticRoots : ∃ x : K × K, x.1 + x.2 = a ∧ x.1 * x.2 = q := by
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root (C 1 * X ^ 2 + C (-a) * X + C q)
    (by rw [degree_quadratic (one_ne_zero : (1 : K) ≠ 0)]; norm_num)
  simp only [IsRoot, eval_add, eval_mul, eval_pow, eval_C, eval_X] at hα
  exact ⟨(α, a - α), by ring, by linear_combination -hα⟩

/-- A choice of pair of roots of `X ^ 2 - a * X + q`, that is, of elements with sum `a` and
product `q`. -/
noncomputable def quadraticRoots : K × K := (exists_quadraticRoots a q).choose

theorem quadraticRoots_add : (quadraticRoots a q).1 + (quadraticRoots a q).2 = a :=
  (exists_quadraticRoots a q).choose_spec.1

theorem quadraticRoots_mul : (quadraticRoots a q).1 * (quadraticRoots a q).2 = q :=
  (exists_quadraticRoots a q).choose_spec.2

end QuadraticRoots

/-- The identity theorem for meromorphic functions on `ℂ` in normal form: two of them that agree
near a point are equal. -/
theorem MeromorphicNFOn.eq_of_eventuallyEq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {f g : ℂ → E} (hf : MeromorphicNFOn f univ) (hg : MeromorphicNFOn g univ)
    {z₀ : ℂ} (hfg : f =ᶠ[𝓝 z₀] g) : f = g := by
  have hmf : MeromorphicOn f univ := hf.meromorphicOn
  have hmg : MeromorphicOn g univ := hg.meromorphicOn
  set V : Set ℂ := {z | AnalyticAt ℂ f z} ∩ {z | AnalyticAt ℂ g z}
  -- `V` is the complement of a countable set, so it meets every punctured neighbourhood ...
  have hVmem : ∀ z : ℂ, V ∈ 𝓝[≠] z := by
    intro z
    have h₁ := mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp
      hmf.analyticAt_mem_codiscreteWithin z (mem_univ z)
    have h₂ := mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp
      hmg.analyticAt_mem_codiscreteWithin z (mem_univ z)
    simp only [compl_univ, union_empty] at h₁ h₂
    exact inter_mem h₁ h₂
  -- ... and, `ℂ` having real rank two, is preconnected.
  have hVpre : IsPreconnected V := by
    have hc : ({z : ℂ | AnalyticAt ℂ f z}ᶜ ∪ {z : ℂ | AnalyticAt ℂ g z}ᶜ).Countable := by
      simpa using hmf.countable_compl_analyticAt_inter.union hmg.countable_compl_analyticAt_inter
    have hconn := hc.isConnected_compl_of_one_lt_rank (by simp [Complex.rank_real_complex])
    rw [compl_union, compl_compl, compl_compl] at hconn
    exact hconn.isPreconnected
  obtain ⟨U, hUsub, hUopen, hz₀U⟩ := mem_nhds_iff.mp hfg
  obtain ⟨w, hwV, hwU⟩ : (V ∩ U).Nonempty :=
    nonempty_of_mem (inter_mem (hVmem z₀) (mem_nhdsWithin_of_mem_nhds (hUopen.mem_nhds hz₀U)))
  have hfA : AnalyticOnNhd ℂ f V := fun _ hz ↦ hz.1
  have hgA : AnalyticOnNhd ℂ g V := fun _ hz ↦ hz.2
  have hEq : EqOn f g V := hfA.eqOn_of_preconnected_of_eventuallyEq hgA hVpre hwV
    (eventually_of_mem (hUopen.mem_nhds hwU) fun _ hz ↦ hUsub hz)
  funext x
  have hx : f =ᶠ[𝓝[≠] x] g := by filter_upwards [hVmem x] with z hz using hEq hz
  exact (((hf (mem_univ x)).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
    (hg (mem_univ x))).mp hx).eq_of_nhds

namespace Deligne.SymPow

section EulerFactor

variable (k : ℕ) (a q T : ℂ)

/-- The local Euler factor of `Sym^k` at a prime whose Frobenius has trace `a` and determinant
`q`, evaluated at `T`. -/
noncomputable def eulerFactor : ℂ :=
  ∏ i ∈ Finset.range (k + 1),
    (1 - (quadraticRoots a q).1 ^ i * (quadraticRoots a q).2 ^ (k - i) * T)

/-- `eulerFactor` computed from any pair of Frobenius eigenvalues with the given trace and
determinant. -/
theorem eulerFactor_eq_of_roots {α β : ℂ} (hadd : α + β = a) (hmul : α * β = q) :
    eulerFactor k a q T = ∏ i ∈ Finset.range (k + 1), (1 - α ^ i * β ^ (k - i) * T) := by
  -- swapping the two eigenvalues reindexes the product by `i ↦ k - i`
  have hswap : ∀ x y : ℂ, ∏ i ∈ Finset.range (k + 1), (1 - x ^ i * y ^ (k - i) * T)
      = ∏ i ∈ Finset.range (k + 1), (1 - y ^ i * x ^ (k - i) * T) := by
    intro x y
    rw [← Finset.prod_range_reflect]
    refine Finset.prod_congr rfl fun i hi ↦ ?_
    rw [Finset.mem_range] at hi
    have h₁ : k + 1 - 1 - i = k - i := by omega
    have h₂ : k - (k - i) = i := by omega
    rw [h₁, h₂]
    ring
  -- `α` is a root of `X ^ 2 - a * X + q`, which is `(X - α₀) (X - β₀)` for the chosen pair
  have hroot : (α - (quadraticRoots a q).1) * (α - (quadraticRoots a q).2) = 0 := by
    linear_combination (-α) * quadraticRoots_add a q + quadraticRoots_mul a q + α * hadd - hmul
  rcases mul_eq_zero.mp hroot with h | h
  · have hα : α = (quadraticRoots a q).1 := sub_eq_zero.mp h
    have hβ : β = (quadraticRoots a q).2 := by
      linear_combination hadd - quadraticRoots_add a q - hα
    rw [eulerFactor, hα, hβ]
  · have hα : α = (quadraticRoots a q).2 := sub_eq_zero.mp h
    have hβ : β = (quadraticRoots a q).1 := by
      linear_combination hadd - quadraticRoots_add a q - hα
    rw [eulerFactor, hα, hβ]
    exact hswap _ _

/-- `Sym^0 h¹(E)` is `ℚ(0)`, whose Euler factors are those of `ζ`. -/
@[simp]
theorem eulerFactor_zero : eulerFactor 0 a q T = 1 - T := by simp [eulerFactor]

/-- `Sym^1 h¹(E)` is `h¹(E)`, whose Euler factors are the local polynomial of `E`. -/
theorem eulerFactor_one : eulerFactor 1 a q T = 1 - a * T + q * T ^ 2 := by
  rw [eulerFactor_eq_of_roots 1 a q T (quadraticRoots_add a q) (quadraticRoots_mul a q),
    Finset.prod_range_succ, Finset.prod_range_one]
  simp only [pow_zero, pow_one, one_mul, Nat.sub_zero, Nat.sub_self]
  linear_combination (-T) * quadraticRoots_add a q + T ^ 2 * quadraticRoots_mul a q

end EulerFactor

/-- `Λ` is the `Sym^k` `L`-function of an elliptic curve with Frobenius traces `a` and bad
primes `S`. -/
structure IsLFunction (k : ℕ) (a : ℕ → ℤ) (S : Set ℕ) (Λ : ℂ → ℂ) : Prop where
  /-- `Λ` is meromorphic on `ℂ`, in the normal form that fixes its values at the poles. -/
  meromorphicNFOn : MeromorphicNFOn Λ univ
  /-- On the half-plane `1 + k / 2 < re s` the Euler product over the good primes converges
  to `Λ s`. -/
  hasProd : ∀ s : ℂ, 1 + (k : ℝ) / 2 < s.re →
    HasProd (fun p : {p : ℕ // p.Prime ∧ p ∉ S} ↦
      (eulerFactor k (a p : ℂ) ((p : ℕ) : ℂ) (((p : ℕ) : ℂ) ^ (-s)))⁻¹) (Λ s)

/-- The `Sym^k` `L`-function is determined by its Euler factors at the good primes. -/
theorem IsLFunction.unique {k : ℕ} {a : ℕ → ℤ} {S : Set ℕ} {Λ₁ Λ₂ : ℂ → ℂ}
    (h₁ : IsLFunction k a S Λ₁) (h₂ : IsLFunction k a S Λ₂) : Λ₁ = Λ₂ := by
  have hopen : IsOpen {s : ℂ | 1 + (k : ℝ) / 2 < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  -- any point of the half-plane will do; `2 + k` is one
  have hmem : (2 + (k : ℂ)) ∈ {s : ℂ | 1 + (k : ℝ) / 2 < s.re} := by
    simp only [Set.mem_ofPred_eq, Complex.add_re, Complex.re_ofNat, Complex.natCast_re]
    linarith [Nat.cast_nonneg (α := ℝ) k]
  refine h₁.meromorphicNFOn.eq_of_eventuallyEq h₂.meromorphicNFOn
    (z₀ := 2 + (k : ℂ)) (eventually_of_mem (hopen.mem_nhds hmem) fun s hs ↦ ?_)
  exact (h₁.hasProd s hs).unique (h₂.hasProd s hs)

end Deligne.SymPow
