import ErdosProblems.Erdos587.HooleyHarmonicRecursion
import ErdosProblems.Erdos587.HooleySmoothEnvelope

/-!
# Products of moments on the restricted sets

One lower-order moment is bounded pointwise by its envelope and the
divisor cap. The other is then summed over the larger set appropriate to
its induction hypothesis.
-/

open scoped BigOperators

namespace Erdos587

lemma MeetsDeltaMoments.moment_le {E : ℕ → ℝ} {q n j : ℕ}
    (h : MeetsDeltaMoments E q n) (hn : n ≠ 0) (hj : 1 ≤ j) (hjq : j ≤ q) :
    deltaMoment n j ≤ E j * n.divisors.card := by
  have hc : (0 : ℝ) < n.divisors.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.mem_divisors.mpr ⟨one_dvd n, hn⟩⟩
  exact (div_le_iff₀ hc).mp (h j hj hjq)

theorem sum_restricted_moment_product_le (S : Finset ℕ) (E : ℕ → ℝ)
    (hS : ∀ n ∈ S, n ≠ 0) {U : ℝ} (hU : 0 ≤ U)
    (hdiv : ∀ n ∈ S, (n.divisors.card : ℝ) ≤ U)
    (q a b : ℕ) (hb : 1 ≤ b) (hbq : b ≤ q) (haq : a - 1 ≤ q) (hEb : 0 ≤ E b) :
    (∑ n ∈ deltaRestrictedSet S E q,
      (deltaMoment n a * deltaMoment n b) / ((n.divisors.card : ℝ) * n)) ≤
      (E b * U) * ∑ n ∈ deltaRestrictedSet S E (a - 1), harmonicDeltaMoment n a := by
  have hpoint (n : ℕ) (hn : n ∈ deltaRestrictedSet S E q) :
      (deltaMoment n a * deltaMoment n b) / ((n.divisors.card : ℝ) * n) ≤
        (E b * U) * harmonicDeltaMoment n a := by
    obtain ⟨hnS, hnE⟩ := mem_deltaRestrictedSet.mp hn
    have hMb : deltaMoment n b ≤ E b * U :=
      (hnE.moment_le (hS n hnS) hb hbq).trans
        (mul_le_mul_of_nonneg_left (hdiv n hnS) hEb)
    calc
      _ ≤ (deltaMoment n a * (E b * U)) / ((n.divisors.card : ℝ) * n) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hMb (deltaMoment_nonneg n a)) (by positivity)
      _ = _ := by
        unfold harmonicDeltaMoment
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
  calc
    _ ≤ ∑ n ∈ deltaRestrictedSet S E q, (E b * U) * harmonicDeltaMoment n a :=
      Finset.sum_le_sum hpoint
    _ = (E b * U) * ∑ n ∈ deltaRestrictedSet S E q, harmonicDeltaMoment n a :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum_of_subset_of_nonneg (deltaRestrictedSet_antitone S E haq)
        (fun n _ _ => harmonicDeltaMoment_nonneg n a)) (mul_nonneg hEb hU)

lemma half_order_reciprocal_sq_le {q b : ℕ} (hb : 1 ≤ b) (hbq : b ≤ q / 2) :
    (1 : ℝ) / (q - b : ℕ) ^ 2 ≤ 4 / (q : ℝ) ^ 2 := by
  have hq : 0 < q := by omega
  have ha : 0 < q - b := by omega
  have hqa : q ≤ 2 * (q - b) := by omega
  have hqaR : (q : ℝ) ≤ 2 * (q - b : ℕ) := by exact_mod_cast hqa
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have haR : (0 : ℝ) < (q - b : ℕ) := by exact_mod_cast ha
  rw [div_le_div_iff₀ (sq_pos_of_pos haR) (sq_pos_of_pos hqR)]
  nlinarith only [hqaR, hqR, haR]

/-- Close the algebraic part of the moment induction: after using the
lower-order averages, the envelope pays for the entire mixed-moment sum. -/
theorem sum_smoothed_restricted_products_le (S : Finset ℕ)
    (hS : ∀ n ∈ S, n ≠ 0) {B U K : ℝ} (hB : 0 ≤ B) (hU : 0 ≤ U) (hK : 0 ≤ K)
    (hdiv : ∀ n ∈ S, (n.divisors.card : ℝ) ≤ U) {q : ℕ} (hq : 3 ≤ q)
    (hIH : ∀ a : ℕ, 2 ≤ a → a ≤ q - 1 →
      (∑ n ∈ deltaRestrictedSet S (deltaSmoothMomentEnvelope B) (a - 1),
        harmonicDeltaMoment n a) ≤ K * deltaSmoothMomentEnvelope B a / (a : ℝ) ^ 2) :
    B * (∑ n ∈ deltaRestrictedSet S (deltaSmoothMomentEnvelope B) (q - 1),
      ∑ b ∈ Finset.Icc 1 (q / 2), 2 ^ b * (q.choose b : ℝ) *
        (deltaMoment n (q - b) * deltaMoment n b) / ((n.divisors.card : ℝ) * n)) ≤
      (4 * U * K / (q : ℝ) ^ 2) * deltaSmoothMomentEnvelope B q := by
  let E := deltaSmoothMomentEnvelope B
  let R := deltaRestrictedSet S E (q - 1)
  let c (b : ℕ) : ℝ := 2 ^ b * (q.choose b : ℝ)
  have hcoeff : 0 ≤ 4 * U * K / (q : ℝ) ^ 2 := by positivity
  have hraw :
      (∑ n ∈ R, ∑ b ∈ Finset.Icc 1 (q / 2),
        c b * (deltaMoment n (q - b) * deltaMoment n b) / ((n.divisors.card : ℝ) * n)) ≤
      (4 * U * K / (q : ℝ) ^ 2) *
        ∑ b ∈ Finset.Icc 1 (q / 2), c b * E b * E (q - b) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro b hb
    obtain ⟨hb, hbq⟩ := Finset.mem_Icc.mp hb
    have hEb : 0 ≤ E b := deltaSmoothMomentEnvelope_nonneg hB b
    have hEa : 0 ≤ E (q - b) := deltaSmoothMomentEnvelope_nonneg hB (q - b)
    have hc : 0 ≤ c b := by dsimp only [c]; positivity
    have hprod := sum_restricted_moment_product_le S E hS hU hdiv
      (q - 1) (q - b) b hb (by omega) (by omega) hEb
    have hIH' := hIH (q - b) (by omega) (by omega)
    calc
      _ = c b * ∑ n ∈ R,
          (deltaMoment n (q - b) * deltaMoment n b) / ((n.divisors.card : ℝ) * n) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n hn
        ring
      _ ≤ c b * ((E b * U) *
          ∑ n ∈ deltaRestrictedSet S E (q - b - 1), harmonicDeltaMoment n (q - b)) :=
        mul_le_mul_of_nonneg_left hprod hc
      _ ≤ c b * ((E b * U) * (K * E (q - b) / (q - b : ℕ) ^ 2)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hIH' (mul_nonneg hEb hU)) hc
      _ = (c b * E b * U * K * E (q - b)) * ((1 : ℝ) / (q - b : ℕ) ^ 2) := by ring
      _ ≤ (c b * E b * U * K * E (q - b)) * (4 / (q : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left (half_order_reciprocal_sq_le hb hbq)
          (by positivity)
      _ = _ := by ring
  calc
    _ ≤ B * ((4 * U * K / (q : ℝ) ^ 2) *
        ∑ b ∈ Finset.Icc 1 (q / 2), c b * E b * E (q - b)) :=
      mul_le_mul_of_nonneg_left hraw hB
    _ = (4 * U * K / (q : ℝ) ^ 2) *
        (B * ∑ b ∈ Finset.Icc 1 (q / 2), c b * E b * E (q - b)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (deltaSmoothMomentEnvelope_convolution hB (by omega : q ≠ 0)) hcoeff

end Erdos587
