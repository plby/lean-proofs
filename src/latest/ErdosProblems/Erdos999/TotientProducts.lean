/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib

/-!
# Totient-ratio products for two moduli with a common factor

This file isolates the Euler-product identity used after writing two moduli
as `g * a` and `g * b`, where `a` and `b` are coprime.  A prime of `g`
which already divides `a * b` supplies one extra Euler factor; a prime of
`g` which is new to `a * b` supplies two Euler factors.
-/

open scoped BigOperators

namespace Erdos999

noncomputable section

/-- The rational Euler factor attached to a prime. -/
private def eulerFactor (p : ℕ) : ℚ := 1 - (p : ℚ)⁻¹

/-- Euler's product formula, normalized by the argument. -/
private lemma totient_div_eq_prod_primeFactors (n : ℕ) (hn : 0 < n) :
    (Nat.totient n : ℚ) / n = ∏ p ∈ n.primeFactors, eulerFactor p := by
  rw [Nat.totient_eq_mul_prod_factors]
  change ((n : ℚ) * ∏ p ∈ n.primeFactors, eulerFactor p) / n = _
  field_simp

/-- The Euler factors of `g` split according to whether the prime already
divides `a * b`. -/
private lemma prod_g_split (g a b : ℕ) :
    (∏ p ∈ g.primeFactors.filter (fun p ↦ p ∣ a * b), eulerFactor p) *
        ∏ p ∈ g.primeFactors.filter (fun p ↦ ¬ p ∣ a * b), eulerFactor p =
      ∏ p ∈ g.primeFactors, eulerFactor p := by
  exact Finset.prod_filter_mul_prod_filter_not g.primeFactors
    (fun p ↦ p ∣ a * b) eulerFactor

/-- Adding the prime factors of `g` which are absent from `a * b` gives
exactly the Euler product of `g * (a * b)`. -/
private lemma prod_fresh_mul_prod_ab (g a b : ℕ)
    (hg : 0 < g) (ha : 0 < a) (hb : 0 < b) :
    (∏ p ∈ g.primeFactors.filter (fun p ↦ ¬ p ∣ a * b), eulerFactor p) *
        (∏ p ∈ (a * b).primeFactors, eulerFactor p) =
      ∏ p ∈ (g * (a * b)).primeFactors, eulerFactor p := by
  rw [Nat.primeFactors_mul hg.ne' (mul_pos ha hb).ne']
  have hfilter :
      g.primeFactors.filter (fun p ↦ ¬ p ∣ a * b) =
        g.primeFactors \ (a * b).primeFactors := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    constructor
    · rintro ⟨hpg, hp⟩
      exact ⟨hpg, fun hpab ↦ hp (Nat.dvd_of_mem_primeFactors hpab)⟩
    · rintro ⟨hpg, hp⟩
      refine ⟨hpg, fun hpdiv ↦ hp ?_⟩
      exact (Nat.prime_of_mem_primeFactors hpg).mem_primeFactors hpdiv
        (mul_pos ha hb).ne'
  rw [hfilter]
  have hdisj : Disjoint (g.primeFactors \ (a * b).primeFactors)
      (a * b).primeFactors := Finset.sdiff_disjoint
  calc
    _ = ∏ p ∈ (g.primeFactors \ (a * b).primeFactors) ∪
          (a * b).primeFactors, eulerFactor p :=
      (Finset.prod_union hdisj).symm
    _ = _ := by
      congr 1
      ext p
      simp

/-- The prime-factor products for `g*a` and `g*b` combine to the products
for `g` and `g*(a*b)` when `a` and `b` are coprime. -/
private lemma prod_ga_mul_prod_gb (g a b : ℕ)
    (hg : 0 < g) (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) :
    (∏ p ∈ (g * a).primeFactors, eulerFactor p) *
        (∏ p ∈ (g * b).primeFactors, eulerFactor p) =
      (∏ p ∈ g.primeFactors, eulerFactor p) *
        ∏ p ∈ (g * (a * b)).primeFactors, eulerFactor p := by
  rw [← Nat.prod_primeFactors_gcd_mul_prod_primeFactors_mul
    (g * a) (g * b) eulerFactor]
  rw [Nat.gcd_mul_left, hab.gcd_eq_one, mul_one]
  have hpf : ((g * a) * (g * b)).primeFactors =
      (g * (a * b)).primeFactors := by
    rw [Nat.primeFactors_mul (mul_pos hg ha).ne' (mul_pos hg hb).ne',
      Nat.primeFactors_mul hg.ne' ha.ne',
      Nat.primeFactors_mul hg.ne' hb.ne',
      Nat.primeFactors_mul hg.ne' (mul_pos ha hb).ne',
      Nat.primeFactors_mul ha.ne' hb.ne']
    ext p
    simp only [Finset.mem_union]
    aesop
  rw [hpf]

/-- Totient/product bridge for `q = g*a` and `r = g*b` with coprime
reduced parts.  The first product ranges over the primes of `g` already
present in `a*b`; `S` in the informal formula is the second filtered set. -/
theorem totient_product_bridge (g a b : ℕ)
    (hg : 0 < g) (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) :
    (∏ p ∈ g.primeFactors.filter (fun p ↦ p ∣ a * b),
        (1 - (p : ℚ)⁻¹)) *
      (∏ p ∈ g.primeFactors.filter (fun p ↦ ¬ p ∣ a * b),
        (1 - (p : ℚ)⁻¹) ^ 2) *
      ((Nat.totient (a * b) : ℚ) / (a * b)) =
      ((Nat.totient (g * a) : ℚ) / (g * a)) *
      ((Nat.totient (g * b) : ℚ) / (g * b)) := by
  rw [← Nat.cast_mul, ← Nat.cast_mul, ← Nat.cast_mul]
  rw [totient_div_eq_prod_primeFactors (a * b) (mul_pos ha hb),
    totient_div_eq_prod_primeFactors (g * a) (mul_pos hg ha),
    totient_div_eq_prod_primeFactors (g * b) (mul_pos hg hb)]
  change
    (∏ p ∈ g.primeFactors.filter (fun p ↦ p ∣ a * b), eulerFactor p) *
        (∏ p ∈ g.primeFactors.filter (fun p ↦ ¬ p ∣ a * b),
          eulerFactor p ^ 2) *
        (∏ p ∈ (a * b).primeFactors, eulerFactor p) =
      (∏ p ∈ (g * a).primeFactors, eulerFactor p) *
        ∏ p ∈ (g * b).primeFactors, eulerFactor p
  rw [Finset.prod_pow]
  have hsplit := prod_g_split g a b
  have hfresh := prod_fresh_mul_prod_ab g a b hg ha hb
  have hrhs := prod_ga_mul_prod_gb g a b hg ha hb hab
  calc
    _ =
        ((∏ p ∈ g.primeFactors.filter (fun p ↦ p ∣ a * b), eulerFactor p) *
          ∏ p ∈ g.primeFactors.filter (fun p ↦ ¬ p ∣ a * b),
            eulerFactor p) *
          ((∏ p ∈ g.primeFactors.filter (fun p ↦ ¬ p ∣ a * b),
            eulerFactor p) *
            ∏ p ∈ (a * b).primeFactors, eulerFactor p) := by ring
    _ = (∏ p ∈ g.primeFactors, eulerFactor p) *
          ∏ p ∈ (g * (a * b)).primeFactors, eulerFactor p := by
      rw [hsplit, hfresh]
    _ = _ := hrhs.symm

/-- Real-valued form of `totient_product_bridge`, used by the measure
estimate. -/
theorem totient_product_bridge_real (g a b : ℕ)
    (hg : 0 < g) (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) :
    (∏ p ∈ g.primeFactors.filter (fun p ↦ p ∣ a * b),
        (1 - (p : ℝ)⁻¹)) *
      (∏ p ∈ g.primeFactors.filter (fun p ↦ ¬ p ∣ a * b),
        (1 - (p : ℝ)⁻¹) ^ 2) *
      ((Nat.totient (a * b) : ℝ) / (a * b)) =
      ((Nat.totient (g * a) : ℝ) / (g * a)) *
      ((Nat.totient (g * b) : ℝ) / (g * b)) := by
  have h := congrArg (fun x : ℚ ↦ (x : ℝ))
    (totient_product_bridge g a b hg ha hb hab)
  norm_num at h ⊢
  exact h

end

end Erdos999
