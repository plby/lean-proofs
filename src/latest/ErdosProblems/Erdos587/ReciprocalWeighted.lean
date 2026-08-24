import ErdosProblems.Erdos587.ReciprocalWeyl

/-!
# Weighted reciprocal quadratic means

Summation by parts transfers the interval-uniform reciprocal mean to weights
with uniformly bounded discrete variation. The maximizing interval length may
depend on the denominator, which is essential for the weighted application.
-/

open scoped BigOperators ComplexConjugate

namespace Erdos587

/-- The discrete variation norm used in finite summation by parts. -/
noncomputable def finiteVariationNorm (w : ℕ → ℂ) (L : ℕ) : ℝ :=
  ‖w (L - 1)‖ + ∑ n ∈ Finset.range (L - 1), ‖w (n + 1) - w n‖

lemma finiteVariationNorm_nonneg (w : ℕ → ℂ) (L : ℕ) : 0 ≤ finiteVariationNorm w L := by
  unfold finiteVariationNorm
  positivity

lemma norm_weighted_sum_le_variation (g w : ℕ → ℂ) (L : ℕ) {B : ℝ}
    (_hB : 0 ≤ B) (hpartial : ∀ l ≤ L, ‖∑ n ∈ Finset.range l, g n‖ ≤ B) :
    ‖∑ n ∈ Finset.range L, w n * g n‖ ≤ finiteVariationNorm w L * B := by
  have hab := Finset.sum_range_by_parts w g L
  simp only [smul_eq_mul] at hab
  rw [hab]
  calc
    _ ≤ ‖w (L - 1) * ∑ n ∈ Finset.range L, g n‖ +
        ‖∑ n ∈ Finset.range (L - 1), (w (n + 1) - w n) *
          ∑ i ∈ Finset.range (n + 1), g i‖ := norm_sub_le _ _
    _ ≤ ‖w (L - 1)‖ * B +
        ∑ n ∈ Finset.range (L - 1), ‖w (n + 1) - w n‖ * B := by
      apply add_le_add
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hpartial L le_rfl) (norm_nonneg _)
      · apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro n hn
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hpartial (n + 1) (by
          have := Finset.mem_range.mp hn
          omega)) (norm_nonneg _)
    _ = finiteVariationNorm w L * B := by
      rw [finiteVariationNorm, add_mul, Finset.sum_mul]

/-- A mean bound uniform in all independently chosen partial-sum lengths
controls weighted means. No maximum is moved outside a sum. -/
lemma sum_norm_weighted_sq_le_of_partial_means {ι : Type*} (D : Finset ι) (K : ℕ)
    (g w : ι → ℕ → ℂ) (L : ι → ℕ) {V B : ℝ} (_hV : 0 ≤ V)
    (hL : ∀ r ∈ D, L r ≤ K)
    (hmean : ∀ l : ι → ℕ, (∀ r ∈ D, l r ≤ K) →
      (∑ r ∈ D, ‖∑ n ∈ Finset.range (l r), g r n‖ ^ 2) ≤ B)
    (hvar : ∀ r ∈ D, finiteVariationNorm (w r) (L r) ≤ V) :
    (∑ r ∈ D, ‖∑ n ∈ Finset.range (L r), w r n * g r n‖ ^ 2) ≤ V ^ 2 * B := by
  classical
  have hex (r : ι) : ∃ l ≤ K, ∀ n ≤ K,
      ‖∑ i ∈ Finset.range n, g r i‖ ≤ ‖∑ i ∈ Finset.range l, g r i‖ := by
    obtain ⟨l, hl, hmax⟩ := (Finset.range (K + 1)).exists_max_image
      (fun n => ‖∑ i ∈ Finset.range n, g r i‖) (by simp)
    refine ⟨l, by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hl, ?_⟩
    intro n hn
    exact hmax n (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hn)
  choose l hl hmax using hex
  have hbound (r : ι) (hr : r ∈ D) :
      ‖∑ n ∈ Finset.range (L r), w r n * g r n‖ ≤
        V * ‖∑ n ∈ Finset.range (l r), g r n‖ := by
    apply (norm_weighted_sum_le_variation (g r) (w r) (L r) (norm_nonneg _)
      (fun n hn => hmax r n (hn.trans (hL r hr)))).trans
    exact mul_le_mul_of_nonneg_right (hvar r hr) (norm_nonneg _)
  calc
    _ ≤ ∑ r ∈ D, (V * ‖∑ n ∈ Finset.range (l r), g r n‖) ^ 2 := by
      apply Finset.sum_le_sum
      intro r hr
      exact pow_le_pow_left₀ (norm_nonneg _) (hbound r hr) 2
    _ = V ^ 2 * ∑ r ∈ D, ‖∑ n ∈ Finset.range (l r), g r n‖ ^ 2 := by
      simp_rw [mul_pow]
      rw [Finset.mul_sum]
    _ ≤ V ^ 2 * B := mul_le_mul_of_nonneg_left (hmean l (fun r _ => hl r)) (sq_nonneg V)

/-- Weighted reciprocal mean, with arbitrary translated intervals, linear
terms, and denominator-dependent weights of variation at most `V`. -/
theorem exists_reciprocal_weighted_mean_bound (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ O : ℕ, 0 < O ∧
      ∀ (a v q c R K : ℕ), 0 < a → a ≤ 4 → 0 < c → c ≤ 8 → 3 ≤ K → K ≤ R →
        16 * K < q → q.Coprime v →
        64 * (q * R + v * K + 1) ≤ (R / K) ^ (4 ^ j) →
        ∀ (D : Finset ℕ) (inv : ℕ → ℤ),
          (∀ r ∈ D, 0 < r ∧ r ≤ 2 * R) →
          (∀ r ∈ D, ((c * r : ℕ) : ℤ) ∣ (q : ℤ) * inv r - 1) →
          ∀ (β : ℕ → ℝ) (s : ℕ → ℤ) (L : ℕ → ℕ), (∀ r ∈ D, L r ≤ K) →
          ∀ (w : ℕ → ℕ → ℂ) (V : ℝ), 0 ≤ V →
          (∀ r ∈ D, finiteVariationNorm (w r) (L r) ≤ V) →
          (∑ r ∈ D, ‖∑ z ∈ Finset.range (L r), w r z * phase
            (reciprocalQuadraticFrequency a v c inv r * ((s r : ℝ) + z) ^ 2 +
              β r * ((s r : ℝ) + z))‖ ^ 2) ≤
            V ^ 2 * (C * R * K * Real.log (35 * (R : ℝ)) ^ O) := by
  obtain ⟨C, hC, O, hO, hmean⟩ := exists_reciprocal_interval_mean_bound j
  refine ⟨C, hC, O, hO, ?_⟩
  intro a v q c R K ha ha4 hc hc8 hK hKR hq hcop hroot D inv hD hinv β s L hLK w V hV hw
  apply sum_norm_weighted_sq_le_of_partial_means D K _ w L hV hLK
  · intro l hl
    exact hmean a v q c R K ha ha4 hc hc8 hK hKR hq hcop hroot D inv hD hinv β s l hl
  · exact hw

lemma sum_norm_le_sqrt_card_mul_sum_sq {ι : Type*} (D : Finset ι) (f : ι → ℂ) :
    (∑ r ∈ D, ‖f r‖) ≤ Real.sqrt ((D.card : ℝ) * ∑ r ∈ D, ‖f r‖ ^ 2) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq D (fun _ => (1 : ℝ)) (fun r => ‖f r‖)
  apply (Real.le_sqrt (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
    (mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))).mpr
  simpa using hcs

lemma sum_norm_weighted_le_of_partial_means {ι : Type*} (D : Finset ι) (K : ℕ)
    (g w : ι → ℕ → ℂ) (L : ι → ℕ) {V B : ℝ} (hV : 0 ≤ V) (_hB : 0 ≤ B)
    (hL : ∀ r ∈ D, L r ≤ K)
    (hmean : ∀ l : ι → ℕ, (∀ r ∈ D, l r ≤ K) →
      (∑ r ∈ D, ‖∑ n ∈ Finset.range (l r), g r n‖ ^ 2) ≤ B)
    (hvar : ∀ r ∈ D, finiteVariationNorm (w r) (L r) ≤ V) :
    (∑ r ∈ D, ‖∑ n ∈ Finset.range (L r), w r n * g r n‖) ≤
      V * Real.sqrt ((D.card : ℝ) * B) := by
  have hs := sum_norm_weighted_sq_le_of_partial_means D K g w L hV hL hmean hvar
  apply (sum_norm_le_sqrt_card_mul_sum_sq D _).trans
  calc
    _ ≤ Real.sqrt ((D.card : ℝ) * (V ^ 2 * B)) :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _))
    _ = V * Real.sqrt ((D.card : ℝ) * B) := by
      rw [show (D.card : ℝ) * (V ^ 2 * B) = V ^ 2 * ((D.card : ℝ) * B) by ring,
        Real.sqrt_mul (sq_nonneg V), Real.sqrt_sq hV]

/-- Conjugating the weight changes a negative quadratic frequency into a
positive one without changing the absolute value or variation. -/
lemma finiteVariationNorm_conj (w : ℕ → ℂ) (L : ℕ) :
    finiteVariationNorm (fun n => conj (w n)) L = finiteVariationNorm w L := by
  simp only [finiteVariationNorm, ← map_sub, Complex.norm_conj]

lemma norm_weighted_neg_phase_sum (w : ℕ → ℂ) (f : ℕ → ℝ) (L : ℕ) :
    ‖∑ n ∈ Finset.range L, w n * phase (-f n)‖ =
      ‖∑ n ∈ Finset.range L, conj (w n) * phase (f n)‖ := by
  have hphase (x : ℝ) : conj (phase (-x)) = phase x := by
    change conj (Real.fourierChar (-x) : ℂ) = (Real.fourierChar x : ℂ)
    rw [← Circle.coe_inv_eq_conj, ← AddChar.map_neg_eq_inv, neg_neg]
  rw [← Complex.norm_conj]
  simp only [map_sum, map_mul, hphase]

end Erdos587
