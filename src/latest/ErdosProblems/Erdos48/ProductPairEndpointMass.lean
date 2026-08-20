/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.EndpointMass

/-!
# Endpoint mass on products of two varying primes

In the dyadic part of the Ford--Luca--Pomerance argument both the root prime
`q` and the auxiliary prime `r` vary.  Vaughan's mean theorem is indexed by
the product conductor `q * r`; this file supplies the finite reindexing step.
The only collision is interchange of the two prime factors, so every product
fiber has cardinality at most two.
-/

namespace Erdos48

open scoped BigOperators

open BoundedGaps.Maynard

noncomputable section

/-- Equality between two products of primes determines the ordered factors
up to interchange. -/
theorem prime_product_pair_eq_cases
    {a b q r : ℕ}
    (ha : a.Prime) (_hb : b.Prime) (hq : q.Prime) (hr : r.Prime)
    (h : a * b = q * r) :
    (a = q ∧ b = r) ∨ (a = r ∧ b = q) := by
  have haDvd : a ∣ q * r := by
    rw [← h]
    exact dvd_mul_right a b
  rcases ha.dvd_mul.mp haDvd with haq | har
  · have haq' : a = q :=
      (Nat.dvd_prime hq).mp haq |>.resolve_left ha.ne_one
    left
    refine ⟨haq', ?_⟩
    subst a
    exact Nat.eq_of_mul_eq_mul_left hq.pos h
  · have har' : a = r :=
      (Nat.dvd_prime hr).mp har |>.resolve_left ha.ne_one
    right
    refine ⟨har', ?_⟩
    subst a
    have h' : r * b = r * q := by
      calc
        r * b = q * r := h
        _ = r * q := Nat.mul_comm q r
    exact Nat.eq_of_mul_eq_mul_left hr.pos h'

/-- A fiber of multiplication on a product of two finite prime sets has at
most two elements. -/
theorem card_filter_primePairs_product_eq_le_two
    {Q R : Finset ℕ}
    (hQ : ∀ q ∈ Q, q.Prime) (hR : ∀ r ∈ R, r.Prime) (d : ℕ) :
    ((Q.product R).filter fun qr ↦ qr.1 * qr.2 = d).card ≤ 2 := by
  classical
  let F := (Q.product R).filter fun qr ↦ qr.1 * qr.2 = d
  by_cases hF : F = ∅
  · change F.card ≤ 2
    rw [hF]
    simp
  · obtain ⟨ab, hab⟩ := Finset.nonempty_iff_ne_empty.mpr hF
    obtain ⟨a, b⟩ := ab
    have habData : (a, b) ∈ Q.product R ∧ a * b = d := by
      simpa only [F, Finset.mem_filter] using hab
    have hsub : F ⊆ {(a, b), (b, a)} := by
      intro qr hqr
      obtain ⟨q, r⟩ := qr
      have hqrData : (q, r) ∈ Q.product R ∧ q * r = d := by
        simpa only [F, Finset.mem_filter] using hqr
      have hcases := prime_product_pair_eq_cases
        (hQ q (Finset.mem_product.mp hqrData.1).1)
        (hR r (Finset.mem_product.mp hqrData.1).2)
        (hQ a (Finset.mem_product.mp habData.1).1)
        (hR b (Finset.mem_product.mp habData.1).2)
        (hqrData.2.trans habData.2.symm)
      rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
    exact (Finset.card_le_card hsub).trans Finset.card_le_two

/-- Summing endpoint mass over two independently varying prime sets costs
at most the factor two coming from interchange of the prime factors. -/
theorem sum_primePair_primitiveEndpointMass_le_two_mul_sum
    {x M : ℕ} {Q R : Finset ℕ}
    (hQ : ∀ q ∈ Q, q.Prime) (hR : ∀ r ∈ R, r.Prime)
    (hupper : ∀ q ∈ Q, ∀ r ∈ R, q * r ≤ M) :
    (∑ qr ∈ Q.product R,
        primitiveEndpointMass x (qr.1 * qr.2)) ≤
      2 * ∑ d ∈ Finset.Icc 1 M, primitiveEndpointMass x d := by
  classical
  let g : ℕ × ℕ → ℕ := fun qr ↦ qr.1 * qr.2
  have hmap : ∀ qr ∈ Q.product R, g qr ∈ Finset.Icc 1 M := by
    intro qr hqr
    obtain ⟨q, r⟩ := qr
    have hqrData := Finset.mem_product.mp hqr
    rw [Finset.mem_Icc]
    refine ⟨?_, hupper q hqrData.1 r hqrData.2⟩
    exact Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero
        (hQ q hqrData.1).ne_zero (hR r hqrData.2).ne_zero)
  rw [← Finset.sum_fiberwise_of_maps_to hmap
    (fun qr ↦ primitiveEndpointMass x (g qr))]
  calc
    (∑ d ∈ Finset.Icc 1 M,
        ∑ qr ∈ Q.product R with g qr = d,
          primitiveEndpointMass x (g qr)) ≤
        ∑ d ∈ Finset.Icc 1 M,
          2 * primitiveEndpointMass x d := by
      apply Finset.sum_le_sum
      intro d hd
      calc
        (∑ qr ∈ Q.product R with g qr = d,
            primitiveEndpointMass x (g qr)) =
            ∑ _qr ∈ (Q.product R).filter (fun qr ↦ g qr = d),
              primitiveEndpointMass x d := by
          apply Finset.sum_congr rfl
          intro qr hqr
          rw [(Finset.mem_filter.mp hqr).2]
        _ = (((Q.product R).filter
              (fun qr ↦ g qr = d)).card : ℝ) *
              primitiveEndpointMass x d := by
          simp [nsmul_eq_mul]
        _ ≤ 2 * primitiveEndpointMass x d := by
          apply mul_le_mul_of_nonneg_right
          · exact_mod_cast card_filter_primePairs_product_eq_le_two hQ hR d
          · exact primitiveEndpointMass_nonneg x d
    _ = 2 * ∑ d ∈ Finset.Icc 1 M,
          primitiveEndpointMass x d := by
      rw [Finset.mul_sum]

/-- The two-variable prime-product endpoint mass is controlled explicitly by
the already formalized Vaughan mean theorem. -/
theorem sum_primePair_primitiveEndpointMass_le_two_mul_vaughan
    {x M : ℕ} {Q R : Finset ℕ}
    (hx : 4 ≤ x)
    (hM : (M : ℝ) ≤ Real.sqrt (x : ℝ))
    (hQ : ∀ q ∈ Q, q.Prime) (hR : ∀ r ∈ R, r.Prime)
    (hupper : ∀ q ∈ Q, ∀ r ∈ R, q * r ≤ M) :
    (∑ qr ∈ Q.product R,
        primitiveEndpointMass x (qr.1 * qr.2)) ≤
      2 * (vaughanPrimitiveMeanEquationOneOneConstant (Real.log 4 + 4) *
        vaughanPrimitiveMeanEquationOneOnePolynomial x M *
          vaughanPrimitiveMeanEquationOneOneLogPower x) := by
  exact (sum_primePair_primitiveEndpointMass_le_two_mul_sum hQ hR hupper).trans
    (mul_le_mul_of_nonneg_left
      (sum_primitiveEndpointMass_le_vaughan hx hM) (by positivity))

/-- Markov form: the number of bad ordered prime pairs is bounded by the
same Vaughan polynomial, with only the unavoidable factor two. -/
theorem badPrimePairs_card_mul_le_two_mul_vaughan
    {x M : ℕ} {Q R : Finset ℕ}
    (hx : 4 ≤ x)
    (hM : (M : ℝ) ≤ Real.sqrt (x : ℝ))
    (hQ : ∀ q ∈ Q, q.Prime) (hR : ∀ r ∈ R, r.Prime)
    (hupper : ∀ q ∈ Q, ∀ r ∈ R, q * r ≤ M) :
    ((((Q.product R).filter fun qr ↦
        (x : ℝ) / 10 <
          primitiveEndpointMass x (qr.1 * qr.2)).card : ℕ) : ℝ) *
          ((x : ℝ) / 10) ≤
      2 * (vaughanPrimitiveMeanEquationOneOneConstant (Real.log 4 + 4) *
        vaughanPrimitiveMeanEquationOneOnePolynomial x M *
          vaughanPrimitiveMeanEquationOneOneLogPower x) := by
  exact (card_filter_mul_le_sum_of_nonneg (Q.product R)
    (fun qr ↦ primitiveEndpointMass x (qr.1 * qr.2)) (by positivity)
    (fun qr _ ↦ primitiveEndpointMass_nonneg x (qr.1 * qr.2))).trans
      (sum_primePair_primitiveEndpointMass_le_two_mul_vaughan
        hx hM hQ hR hupper)

end

end Erdos48
