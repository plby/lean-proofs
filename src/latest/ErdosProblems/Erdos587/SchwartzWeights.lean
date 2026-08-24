import ErdosProblems.Erdos587.ReciprocalWeighted
import ErdosProblems.Erdos587.Fresnel

/-!
# Uniform variation of sampled Fresnel profiles

Fixed-length blocks suffice: the reciprocal mean is uniform in the starting
point. Uniform rapid decay then makes the sum of the block variation bounds
convergent, without an expanding dual-frequency cutoff.
-/

open scoped BigOperators SchwartzMap FourierTransform

namespace Erdos587

lemma finiteVariationNorm_sample_le (f : ℝ → ℂ) {x δ C₀ C₁ : ℝ} (L : ℕ)
    (hδ : 0 ≤ δ) (hC₁ : 0 ≤ C₁)
    (hf : ∀ y ∈ Set.Icc x (x + δ * L), DifferentiableAt ℝ f y)
    (hzero : ∀ y ∈ Set.Icc x (x + δ * L), ‖f y‖ ≤ C₀)
    (hone : ∀ y ∈ Set.Icc x (x + δ * L), ‖deriv f y‖ ≤ C₁) :
    finiteVariationNorm (fun n => f (x + δ * n)) L ≤ C₀ + L * δ * C₁ := by
  have hmem (n : ℕ) (hn : n ≤ L) : x + δ * n ∈ Set.Icc x (x + δ * L) := by
    constructor
    · have : 0 ≤ δ * (n : ℝ) := mul_nonneg hδ (Nat.cast_nonneg _)
      linarith
    · exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (by exact_mod_cast hn) hδ)
  have hstep (n : ℕ) (hn : n ∈ Finset.range (L - 1)) :
      ‖f (x + δ * (n + 1)) - f (x + δ * n)‖ ≤ C₁ * δ := by
    have hnL : n + 1 ≤ L := by have := Finset.mem_range.mp hn; omega
    have h := Convex.norm_image_sub_le_of_norm_deriv_le hf hone
      (convex_Icc x (x + δ * L)) (hmem n (by omega)) (hmem (n + 1) hnL)
    have heq : x + δ * ((n + 1 : ℕ) : ℝ) - (x + δ * n) = δ := by push_cast; ring
    rw [heq, Real.norm_eq_abs, abs_of_nonneg hδ] at h
    simpa only [Nat.cast_add, Nat.cast_one] using h
  unfold finiteVariationNorm
  calc
    _ ≤ C₀ + ∑ n ∈ Finset.range (L - 1), C₁ * δ := by
      apply add_le_add (hzero _ (hmem (L - 1) (by omega)))
      apply Finset.sum_le_sum
      intro n hn
      simpa only [Nat.cast_add, Nat.cast_one] using hstep n hn
    _ = C₀ + ((L - 1 : ℕ) : ℝ) * (C₁ * δ) := by simp
    _ ≤ C₀ + (L : ℝ) * (C₁ * δ) := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le L 1)
        (mul_nonneg hC₁ hδ))
    _ = C₀ + L * δ * C₁ := by ring

lemma fresnelProfile_differentiable (f : 𝓢(ℝ, ℂ)) (A : ℝ) :
    Differentiable ℝ (fresnelProfile f A) := by
  have heq : fresnelProfile f A =
      (𝓕⁻ (quadraticChirpMul (-1 / (4 * A)) (𝓕 f)) : 𝓢(ℝ, ℂ)) := by
    funext x
    exact fresnelProfile_eq_inverse_fourier f A x
  rw [heq]
  exact SchwartzMap.differentiable _

/-- The spatial scale of each block is bounded above and below. Therefore
its integer block label is bounded by a constant times every spatial argument
in that block. -/
lemma block_label_le_spatial_weight {t u δ : ℝ} {K : ℕ}
    (ht : 1 / 2 ≤ t) (hu : |u| ≤ 1) (_hδ : 0 ≤ δ) (hKδ : δ * K ≤ 2)
    (j : ℤ) {x : ℝ} (hx : x ∈ Set.Icc (t * j + u) (t * j + u + δ * K)) :
    1 + |(j : ℝ)| ≤ 8 * (1 + |x|) := by
  have hoff : |x - t * j| ≤ 3 := by
    rw [abs_le]
    have hulo := (abs_le.mp hu).1
    have huhi := (abs_le.mp hu).2
    constructor <;> linarith [hx.1, hx.2]
  have htpos : 0 ≤ t := by linarith
  have hmul : t * |(j : ℝ)| ≤ |x| + 3 := by
    calc
      t * |(j : ℝ)| = |t * j| := by rw [abs_mul, abs_of_nonneg htpos]
      _ ≤ |x| + |x - t * j| := by
        have h := abs_add_le x (-(x - t * j))
        rw [abs_neg, show x + -(x - t * j) = t * j by ring] at h
        exact h
      _ ≤ |x| + 3 := add_le_add le_rfl hoff
  nlinarith [abs_nonneg (j : ℝ), abs_nonneg x]

lemma le_block_decay_of_spatial_bound (p : ℕ) (j : ℤ) {x y C : ℝ}
    (hy : 0 ≤ y) (hlabel : 1 + |(j : ℝ)| ≤ 8 * (1 + |x|))
    (hbound : (1 + |x|) ^ p * y ≤ C) :
    y ≤ 8 ^ p * C / (1 + |(j : ℝ)|) ^ p := by
  have hpos : 0 < (1 + |(j : ℝ)|) ^ p := by positivity
  apply (le_div_iff₀ hpos).mpr
  calc
    y * (1 + |(j : ℝ)|) ^ p ≤ y * (8 * (1 + |x|)) ^ p :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hlabel p) hy
    _ = 8 ^ p * ((1 + |x|) ^ p * y) := by rw [mul_pow]; ring
    _ ≤ 8 ^ p * C := mul_le_mul_of_nonneg_left hbound (by positivity)

/-- Spatial decay of a function and its first derivative gives a summable
variation envelope for fixed-length sampled blocks. -/
lemma sample_block_variation_le_of_decay (f : ℝ → ℂ) (p : ℕ) (hf : Differentiable ℝ f)
    (M₀ M₁ : ℝ) (hM₁ : 0 ≤ M₁)
    (hb₀ : ∀ y, (1 + |y|) ^ p * ‖f y‖ ≤ M₀)
    (hb₁ : ∀ y, (1 + |y|) ^ p * ‖deriv f y‖ ≤ M₁)
    (t u δ : ℝ) (K : ℕ) (j : ℤ)
    (ht : 1 / 2 ≤ t) (hu : |u| ≤ 1) (hδ : 0 ≤ δ) (hKδ : δ * K ≤ 2) :
    finiteVariationNorm (fun n => f (t * j + u + δ * n)) K ≤
      (8 ^ p * (M₀ + 2 * M₁)) / (1 + |(j : ℝ)|) ^ p := by
  let Z := (1 + |(j : ℝ)|) ^ p
  have hZ : 0 < Z := by dsimp [Z]; positivity
  have hbzero : ∀ y ∈ Set.Icc (t * j + u) (t * j + u + δ * K),
      ‖f y‖ ≤ 8 ^ p * M₀ / Z := by
    intro y hy
    apply le_block_decay_of_spatial_bound p j (norm_nonneg _)
      (block_label_le_spatial_weight ht hu hδ hKδ j hy)
    exact hb₀ y
  have hbone : ∀ y ∈ Set.Icc (t * j + u) (t * j + u + δ * K),
      ‖deriv f y‖ ≤ 8 ^ p * M₁ / Z := by
    intro y hy
    apply le_block_decay_of_spatial_bound p j (norm_nonneg _)
      (block_label_le_spatial_weight ht hu hδ hKδ j hy)
    exact hb₁ y
  have hC₁ : 0 ≤ 8 ^ p * M₁ / Z := by positivity
  apply (finiteVariationNorm_sample_le _ K hδ hC₁
    (fun y _ => hf y) hbzero hbone).trans
  calc
    _ ≤ 8 ^ p * M₀ / Z + 2 * (8 ^ p * M₁ / Z) := by
      apply add_le_add le_rfl
      apply mul_le_mul_of_nonneg_right _ hC₁
      simpa only [mul_comm] using hKδ
    _ = (8 ^ p * (M₀ + 2 * M₁)) / (1 + |(j : ℝ)|) ^ p := by dsimp [Z]; ring

/-- Every fixed-length sampled block has a rapidly decaying variation bound,
uniform in the oscillation parameter `A >= 1` and all allowed sampling scales. -/
theorem exists_uniform_fresnel_block_variation_bound (f : 𝓢(ℝ, ℂ)) (p : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (A t u δ : ℝ) (K : ℕ) (j : ℤ),
      1 ≤ A → 1 / 2 ≤ t → |u| ≤ 1 → 0 ≤ δ → δ * K ≤ 2 →
      finiteVariationNorm (fun n => fresnelProfile f A (t * j + u + δ * n)) K ≤
        C / (1 + |(j : ℝ)|) ^ p := by
  obtain ⟨M₀, hM₀, hb₀⟩ := exists_uniform_fresnelProfile_derivative_bound f p 0
  obtain ⟨M₁, hM₁, hb₁⟩ := exists_uniform_fresnelProfile_derivative_bound f p 1
  refine ⟨8 ^ p * (M₀ + 2 * M₁), by positivity, ?_⟩
  intro A t u δ K j hA ht hu hδ hKδ
  apply sample_block_variation_le_of_decay _ p (fresnelProfile_differentiable f A)
    M₀ M₁ hM₁ _ _ t u δ K j ht hu hδ hKδ
  · intro y
    simpa only [iteratedDeriv_zero] using hb₀ A hA y
  · intro y
    simpa only [iteratedDeriv_one] using hb₁ A hA y

lemma summable_block_decay : Summable (fun j : ℤ => 1 / (1 + |(j : ℝ)|) ^ 2) := by
  have hnat : Summable (fun n : ℕ => 1 / (1 + (n : ℝ)) ^ 2) := by
    have h := (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)).comp_injective
      (fun a b h => Nat.add_right_cancel h : Function.Injective (fun n : ℕ => n + 1))
    change Summable (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ)) ^ 2) at h
    simpa only [Nat.cast_add, Nat.cast_one, add_comm] using h
  apply Summable.of_nat_of_neg
  · simpa only [Int.cast_natCast, Nat.abs_cast] using hnat
  · simpa only [Int.cast_neg, abs_neg, Int.cast_natCast, Nat.abs_cast] using hnat

end Erdos587
