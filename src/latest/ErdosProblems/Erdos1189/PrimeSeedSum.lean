/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Reciprocal mass of the squarefree-product classes in a seed frame.
Informal source: Section 7 of Pickhardt and Omniscience Research Agent.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.SquarefreeReciprocals
import ErdosProblems.Erdos1189.Density
import Mathlib.NumberTheory.PrimeCounting

namespace Erdos1189

open Finset

lemma prime_divisor_small_product_le {p q d : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hd : 0 < d) (hdq : d < q) (hdiv : p ∣ q * d) : p ≤ q := by
  rcases hp.dvd_mul.mp hdiv with hpq | hpd
  · exact le_of_eq ((Nat.dvd_prime hq).mp hpq |>.resolve_left hp.ne_one)
  · exact (Nat.le_of_dvd hd hpd).trans hdq.le

lemma prime_small_product_injective {p q d e : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hd : 0 < d) (hdp : d < p) (he : 0 < e) (heq : e < q)
    (h : p * d = q * e) : p = q ∧ d = e := by
  have hpq : p ≤ q := prime_divisor_small_product_le hp hq he heq
    (h ▸ dvd_mul_right p d)
  have hqp : q ≤ p := prime_divisor_small_product_le hq hp hd hdp
    (h.symm ▸ dvd_mul_right q e)
  have hpeq := le_antisymm hpq hqp
  subst q
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left hp.pos h⟩

def primeSeedPairs (P : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (Nat.primesLE (P - 1)).sigma fun q => squarefreeUpto (q - 1)

lemma primeSeedPairs_injective (P : ℕ) :
    Set.InjOn (fun s : Σ _ : ℕ, ℕ => s.1 * s.2) (primeSeedPairs P) := by
  intro s hs t ht heq
  obtain ⟨hsq, hsd⟩ := mem_sigma.mp hs
  obtain ⟨htq, htd⟩ := mem_sigma.mp ht
  have hsdI := mem_Ioc.mp (mem_filter.mp hsd).1
  have htdI := mem_Ioc.mp (mem_filter.mp htd).1
  obtain ⟨h1, h2⟩ := prime_small_product_injective
    (Nat.prime_of_mem_primesLE hsq) (Nat.prime_of_mem_primesLE htq)
    hsdI.1 (by omega) htdI.1 (by omega) heq
  cases s
  cases t
  simp_all

lemma primeSeed_reciprocal_sum (P : ℕ) :
    (∑ s ∈ primeSeedPairs P, ((s.1 * s.2 : ℕ) : ℝ)⁻¹) =
      ∑ q ∈ Nat.primesLE (P - 1), (q : ℝ)⁻¹ *
        ∑ d ∈ squarefreeUpto (q - 1), (d : ℝ)⁻¹ := by
  rw [primeSeedPairs, sum_sigma]
  simp only [Nat.cast_mul, mul_inv, mul_sum]

theorem reciprocalSum_lower_of_squarefree_products {P : ℕ} {S : Finset ℕ}
    (hproducts : ∀ q : ℕ, q.Prime → q < P →
      ∀ d ∈ squarefreeUpto (q - 1), q * d ∈ S) :
    (1 / 4 : ℝ) * (∑ q ∈ Nat.primesLE (P - 1), Real.log q / q) ≤
      (reciprocalSum S : ℝ) := by
  by_cases hP : P = 0
  · subst P
    simp only [Nat.zero_sub, Nat.primesLE_zero, sum_empty, mul_zero]
    unfold reciprocalSum
    positivity
  have hsub : (primeSeedPairs P).image (fun s => s.1 * s.2) ⊆ S := by
    intro d hd
    obtain ⟨s, hs, rfl⟩ := mem_image.mp hd
    obtain ⟨hq, hd⟩ := mem_sigma.mp hs
    exact hproducts s.1 (Nat.prime_of_mem_primesLE hq)
      (by have := Nat.le_of_mem_primesLE hq; omega) s.2 hd
  have hsum : (∑ s ∈ primeSeedPairs P, ((s.1 * s.2 : ℕ) : ℝ)⁻¹) ≤
      (reciprocalSum S : ℝ) := by
    rw [← sum_image (f := fun d : ℕ => (d : ℝ)⁻¹) (primeSeedPairs_injective P)]
    simp only [reciprocalSum, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    exact sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
  rw [primeSeed_reciprocal_sum] at hsum
  apply le_trans _ hsum
  rw [mul_sum]
  apply sum_le_sum
  intro q hq
  have h := mul_le_mul_of_nonneg_left
    (squarefree_reciprocals_ge_quarter_log (Nat.prime_of_mem_primesLE hq).pos)
    (show (0 : ℝ) ≤ (q : ℝ)⁻¹ by positivity)
  simpa only [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h

end Erdos1189
