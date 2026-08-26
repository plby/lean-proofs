import ErdosProblems.Erdos380.ConductorMoments
import Mathlib.Data.Finset.NatDivisors

open scoped BigOperators Pointwise

namespace Erdos380

noncomputable section

/-- Sum of a nonnegative weight over the nontrivial divisors of a modulus. -/
def nontrivialDivisorSum (F : ℕ → ℝ) (q : ℕ) : ℝ :=
  ∑ d ∈ q.divisors, if d = 1 then 0 else F d

lemma divisorMeanMoment_eq (s : Finset ℕ) (k q : ℕ) :
    divisorMeanMoment s k q = nontrivialDivisorSum (primitiveMeanMoment s k) q := by
  unfold divisorMeanMoment nontrivialDivisorSum
  exact (Finset.sum_subtype (p := fun d => d ∈ q.divisors) q.divisors (by simp)
    (fun d => if d = 1 then 0 else primitiveMeanMoment s k d)).symm

lemma nontrivialDivisorSum_prime (F : ℕ → ℝ) {p : ℕ} (hp : p.Prime) :
    nontrivialDivisorSum F p = F p := by
  simp [nontrivialDivisorSum, hp.divisors, hp.ne_one, hp.ne_one.symm]

lemma nontrivialDivisorSum_prime_mul_le (F : ℕ → ℝ) (hF : ∀ n, 0 ≤ F n)
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    nontrivialDivisorSum F (p * q) ≤ F p + F q + F (p * q) := by
  let G : ℕ → ℝ := fun n => if n = 1 then 0 else F n
  have hG : ∀ n, 0 ≤ G n := fun n => by
    dsimp [G]
    split_ifs
    · exact le_rfl
    · exact hF n
  have hpq : p * q ≠ 1 := by nlinarith [hp.two_le, hq.two_le]
  unfold nontrivialDivisorSum
  rw [Nat.divisors_mul, Finset.mul_def]
  calc
    _ ≤ ∑ a ∈ p.divisors ×ˢ q.divisors, G (a.1 * a.2) :=
      Finset.sum_image_le_of_nonneg (fun n _ => hG n)
    _ = _ := by
      rw [Finset.sum_product, hp.divisors, hq.divisors]
      simp [G, hp.ne_one, hp.ne_one.symm, hq.ne_one, hq.ne_one.symm,
        add_comm, add_left_comm, add_assoc]

lemma sum_prime_tuple_weight_le {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime)
    (k : ℕ) (F : ℕ → ℝ) (hF : ∀ n, 0 ≤ F n) :
    (∑ f : Fin k → s, F (tupleProduct s k f)) ≤
      (k.factorial : ℝ) * ∑ n ∈ primeProductSupport s k, F n := by
  rw [sum_tupleProduct_eq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n _hn
  exact mul_le_mul_of_nonneg_right
    (by exact_mod_cast productMultiplicity_le_factorial hs k n) (hF n)

lemma sum_prime_pair_weight_eq (s : Finset ℕ) (F : ℕ → ℝ) :
    (∑ p ∈ s, ∑ q ∈ s, F (p * q)) =
      ∑ f : Fin 2 → s, F (tupleProduct s 2 f) := by
  classical
  calc
    _ = ∑ p : s, ∑ q : s, F (p.val * q.val) := by
      rw [Finset.sum_subtype (p := fun p => p ∈ s) s (by simp)
        (fun p => ∑ q ∈ s, F (p * q))]
      apply Finset.sum_congr rfl
      intro p _hp
      exact Finset.sum_subtype (p := fun q => q ∈ s) s (by simp)
        (fun q => F (p.val * q))
    _ = ∑ a : s × s, F (a.1.val * a.2.val) :=
      (Fintype.sum_prod_type (fun a : s × s => F (a.1.val * a.2.val))).symm
    _ = _ := by
      symm
      apply Fintype.sum_equiv (finTwoArrowEquiv s)
        (fun f : Fin 2 → s => F (tupleProduct s 2 f))
        (fun a : s × s => F (a.1.val * a.2.val))
      intro f
      simp [tupleProduct, Fin.prod_univ_two, finTwoArrowEquiv]

lemma sum_prime_pair_weight_le {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime)
    {P : ℕ} (hP : ∀ p ∈ s, p ≤ P) (F : ℕ → ℝ) (hF : ∀ n, 0 ≤ F n) :
    (∑ p ∈ s, ∑ q ∈ s, F (p * q)) ≤ 2 * ∑ n ∈ Finset.Ioc 0 (P ^ 2), F n := by
  rw [sum_prime_pair_weight_eq]
  have h := sum_prime_tuple_weight_le hs 2 F hF
  norm_num at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
  exact Finset.sum_le_sum_of_subset_of_nonneg (primeProductSupport_subset_Ioc hs hP)
    (fun n _ _ => hF n)

lemma reciprocal_totient_mul_le (p q : ℕ) :
    1 / ((p * q).totient : ℝ) ≤ (1 / (p.totient : ℝ)) * (1 / (q.totient : ℝ)) := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  have hpφ : 0 < (p.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hp)
  have hqφ : 0 < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hq)
  rw [div_mul_div_comm, one_mul]
  exact one_div_le_one_div_of_le (mul_pos hpφ hqφ)
    (by exact_mod_cast Nat.totient_super_multiplicative p q)

lemma prime_pair_divisor_weight_le {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime)
    (F : ℕ → ℝ) (hF : ∀ n, 0 ≤ F n) {W : ℝ} (hW0 : 0 ≤ W)
    (hW : ∀ p ∈ s, 1 / (p.totient : ℝ) ≤ W) {p q : ℕ} (hp : p ∈ s) (hq : q ∈ s) :
    nontrivialDivisorSum F (p * q) / ((p * q).totient : ℝ) ≤
      (F p / (p.totient : ℝ)) * (1 / (q.totient : ℝ)) +
        (1 / (p.totient : ℝ)) * (F q / (q.totient : ℝ)) + W ^ 2 * F (p * q) := by
  have hwp : 0 ≤ 1 / (p.totient : ℝ) := by positivity
  have hwq : 0 ≤ 1 / (q.totient : ℝ) := by positivity
  have hw : (1 / (p.totient : ℝ)) * (1 / (q.totient : ℝ)) ≤ W ^ 2 := by
    simpa [pow_two] using mul_le_mul (hW p hp) (hW q hq) hwq hW0
  calc
    _ = nontrivialDivisorSum F (p * q) * (1 / ((p * q).totient : ℝ)) := by ring
    _ ≤ (F p + F q + F (p * q)) *
        ((1 / (p.totient : ℝ)) * (1 / (q.totient : ℝ))) := by
      exact mul_le_mul (nontrivialDivisorSum_prime_mul_le F hF (hs p hp) (hs q hq))
        (reciprocal_totient_mul_le p q) (by positivity)
        (add_nonneg (add_nonneg (hF p) (hF q)) (hF (p * q)))
    _ ≤ _ := by
      have he := mul_le_mul_of_nonneg_right hw (hF (p * q))
      simp only [div_eq_mul_inv, one_mul] at he ⊢
      nlinarith

theorem sum_prime_pair_divisor_weight_le {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime)
    (F : ℕ → ℝ) (hF : ∀ n, 0 ≤ F n) {W : ℝ} (hW0 : 0 ≤ W)
    (hW : ∀ p ∈ s, 1 / (p.totient : ℝ) ≤ W) :
    (∑ p ∈ s, ∑ q ∈ s, nontrivialDivisorSum F (p * q) / ((p * q).totient : ℝ)) ≤
      2 * (∑ p ∈ s, F p / (p.totient : ℝ)) * (∑ q ∈ s, 1 / (q.totient : ℝ)) +
        W ^ 2 * (∑ p ∈ s, ∑ q ∈ s, F (p * q)) := by
  calc
    _ ≤ ∑ p ∈ s, ∑ q ∈ s,
        ((F p / (p.totient : ℝ)) * (1 / (q.totient : ℝ)) +
          (1 / (p.totient : ℝ)) * (F q / (q.totient : ℝ)) + W ^ 2 * F (p * q)) := by
      exact Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun q hq =>
        prime_pair_divisor_weight_le hs F hF hW0 hW hp hq
    _ = _ := by
      simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
      ring

theorem prime_and_pair_divisor_weight_le {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime)
    {P : ℕ} (hP : ∀ p ∈ s, p ≤ P) (F : ℕ → ℝ) (hF : ∀ n, 0 ≤ F n)
    {W : ℝ} (hW0 : 0 ≤ W) (hW : ∀ p ∈ s, 1 / (p.totient : ℝ) ≤ W) :
    (∑ p ∈ s, nontrivialDivisorSum F p / (p.totient : ℝ)) +
        (∑ p ∈ s, ∑ q ∈ s, nontrivialDivisorSum F (p * q) / ((p * q).totient : ℝ)) ≤
      (W * (1 + 2 * ∑ p ∈ s, 1 / (p.totient : ℝ)) + 2 * W ^ 2) *
        ∑ n ∈ Finset.Ioc 0 (P ^ 2), F n := by
  have hsP : s ⊆ Finset.Ioc 0 (P ^ 2) := by
    intro p hp
    have hple := hP p hp
    have hp2 := (hs p hp).two_le
    exact Finset.mem_Ioc.mpr ⟨by omega, by nlinarith⟩
  have hsingle : (∑ p ∈ s, F p / (p.totient : ℝ)) ≤
      W * ∑ n ∈ Finset.Ioc 0 (P ^ 2), F n := by
    calc
      _ ≤ ∑ p ∈ s, W * F p := by
        apply Finset.sum_le_sum
        intro p hp
        have h := mul_le_mul_of_nonneg_right (hW p hp) (hF p)
        simpa [div_eq_mul_inv, mul_comm] using h
      _ = W * ∑ p ∈ s, F p := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg hsP (fun n _ _ => hF n)) hW0
  have hpair := sum_prime_pair_divisor_weight_le hs F hF hW0 hW
  have hprod := sum_prime_pair_weight_le hs hP F hF
  have hsum : 0 ≤ ∑ p ∈ s, 1 / (p.totient : ℝ) := Finset.sum_nonneg fun _ _ => by positivity
  have heq : (∑ p ∈ s, nontrivialDivisorSum F p / (p.totient : ℝ)) =
      ∑ p ∈ s, F p / (p.totient : ℝ) := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [nontrivialDivisorSum_prime F (hs p hp)]
  rw [heq]
  have hsm := mul_le_mul_of_nonneg_right hsingle
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hsum)
  have hpm := mul_le_mul_of_nonneg_left hprod (sq_nonneg W)
  nlinarith

end

end Erdos380
