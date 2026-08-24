import ErdosProblems.Erdos587.ReciprocalSeries

/-!
# Full Fresnel-weighted reciprocal series

The uniformly Schwartz Fresnel profiles have summable block variation. This
transfers a mean for translated quadratic intervals to the complete series.
-/

open scoped BigOperators SchwartzMap FourierTransform

namespace Erdos587

lemma summable_fresnelProfile_affine (f : 𝓢(ℝ, ℂ)) (A u : ℝ) {δ : ℝ} (hδ : δ ≠ 0) :
    Summable (fun n : ℤ => fresnelProfile f A (u + δ * n)) := by
  let g : 𝓢(ℝ, ℂ) := 𝓕⁻ (quadraticChirpMul (-1 / (4 * A)) (𝓕 f))
  have h := summable_schwartz_int (dilateSchwartz (g.compSubConstCLM ℂ (-u)) δ hδ)
  apply h.congr
  intro n
  rw [dilateSchwartz_apply, SchwartzMap.compSubConstCLM_apply,
    fresnelProfile_eq_inverse_fourier]
  dsimp [g]
  congr 1
  ring

lemma summable_fresnelProfile_affine_phase (f : 𝓢(ℝ, ℂ)) (A u : ℝ)
    {δ : ℝ} (hδ : δ ≠ 0) (ψ : ℤ → ℝ) :
    Summable (fun n : ℤ => fresnelProfile f A (u + δ * n) * phase (ψ n)) := by
  apply Summable.of_norm
  simpa only [norm_mul, norm_phase, mul_one] using
    (summable_fresnelProfile_affine f A u hδ).norm

/-- The analytic weight transfer is uniform in the independently varying
profile parameters and sampling scales. -/
theorem exists_fresnel_series_mean_constant (f : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ι : Type*} (D : Finset ι) (K : ℕ), 0 < K →
      ∀ (θ β : ι → ℝ) (B : ℝ), 0 ≤ B →
      (∀ (s : ι → ℤ) (l : ι → ℕ), (∀ r ∈ D, l r ≤ K) →
        (∑ r ∈ D, ‖∑ n ∈ Finset.range (l r),
          phase (θ r * ((s r : ℝ) + n) ^ 2 + β r * ((s r : ℝ) + n))‖ ^ 2) ≤ B) →
      ∀ (A u δ : ι → ℝ), (∀ r ∈ D, 1 ≤ A r) → (∀ r ∈ D, |u r| ≤ 1) →
        (∀ r ∈ D, 0 < δ r) → (∀ r ∈ D, 1 / 2 ≤ δ r * K ∧ δ r * K ≤ 2) →
        (∑ r ∈ D, ‖∑' n : ℤ, fresnelProfile f (A r) (u r + δ r * n) *
          phase (θ r * (n : ℝ) ^ 2 + β r * n)‖) ≤ C * Real.sqrt ((D.card : ℝ) * B) := by
  obtain ⟨C, hC, hvar⟩ := exists_uniform_fresnel_block_variation_bound f 2
  refine ⟨C * ∑' j : ℤ, 1 / (1 + |(j : ℝ)|) ^ 2, mul_nonneg hC
    (tsum_nonneg (fun j => by positivity)), ?_⟩
  intro ι D K hK θ β B hB hmean A u δ hA hu hδ hscale
  have hwvar (r : ι) (hr : r ∈ D) (j : ℤ) :
      finiteVariationNorm (fun n => fresnelProfile f (A r)
        (u r + δ r * (((K : ℤ) * j + n : ℤ) : ℝ))) K ≤
          C / (1 + |(j : ℝ)|) ^ 2 := by
    have h := hvar (A r) (δ r * K) (u r) (δ r) K j (hA r hr)
      (hscale r hr).1 (hu r hr) (hδ r hr).le (hscale r hr).2
    convert h using 1
    congr 1
    funext n
    congr 1
    push_cast
    ring
  have h := sum_norm_weighted_series_le_of_block_variation D K hK θ β
    (fun r n => fresnelProfile f (A r) (u r + δ r * n)) hC hB hmean hwvar
    (fun r hr => summable_fresnelProfile_affine_phase f (A r) (u r) (hδ r hr).ne' _)
  convert h using 1
  ring

lemma norm_negative_quadratic_interval (θ β : ℝ) (s : ℤ) (L : ℕ) :
    ‖∑ n ∈ Finset.range L, phase (-θ * ((s : ℝ) + n) ^ 2 + β * ((s : ℝ) + n))‖ =
      ‖∑ n ∈ Finset.range L, phase (θ * ((s : ℝ) + n) ^ 2 + (-β) * ((s : ℝ) + n))‖ := by
  have heq (n : ℕ) : -θ * ((s : ℝ) + n) ^ 2 + β * ((s : ℝ) + n) =
      -(θ * ((s : ℝ) + n) ^ 2 + (-β) * ((s : ℝ) + n)) := by ring
  simp_rw [heq]
  simpa only [one_mul, map_one] using norm_weighted_neg_phase_sum (fun _ => 1)
    (fun n => θ * ((s : ℝ) + n) ^ 2 + (-β) * ((s : ℝ) + n)) L

/-- Absorbing Cauchy--Schwarz into the usual `R * sqrt K` scale costs only
one harmless enlargement of the constant and no additional log exponent. -/
lemma sqrt_card_reciprocal_mean_le {d R K : ℕ} {C F : ℝ} (hC : 0 ≤ C) (hF : 1 ≤ F)
    (hd : d ≤ 2 * R) :
    Real.sqrt ((d : ℝ) * (C * R * K * F)) ≤
      (C + 1) * R * Real.sqrt K * F := by
  have hF0 : 0 ≤ F := by linarith
  have hdR : (d : ℝ) ≤ 2 * R := by exact_mod_cast hd
  have hconstant : 2 * C ≤ (C + 1) ^ 2 := by nlinarith [sq_nonneg C]
  have hFpow : F ≤ F ^ 2 := by nlinarith
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  rw [Real.sq_sqrt (by positivity)]
  calc
    (d : ℝ) * (C * R * K * F) ≤ (2 * R) * (C * R * K * F) :=
      mul_le_mul_of_nonneg_right hdR (by positivity)
    _ = (2 * C) * ((R : ℝ) ^ 2 * K * F) := by ring
    _ ≤ (C + 1) ^ 2 * ((R : ℝ) ^ 2 * K * F) :=
      mul_le_mul_of_nonneg_right hconstant (by positivity)
    _ ≤ (C + 1) ^ 2 * ((R : ℝ) ^ 2 * K * F ^ 2) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hFpow (by positivity))
        (sq_nonneg _)
    _ = ((C + 1) * R * Real.sqrt K * F) ^ 2 := by
      rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg K)]
      ring

/-- The complete reciprocal series has the expected `R * sqrt K` mean.
The negative frequency is the sign produced by Gauss--Fresnel reciprocity. -/
theorem exists_reciprocal_fresnel_series_bound (j : ℕ) (f : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 < C ∧ ∃ O : ℕ, 0 < O ∧
      ∀ (a v q c R K : ℕ), 0 < a → a ≤ 4 → 0 < c → c ≤ 8 → 3 ≤ K → K ≤ R →
        16 * K < q → q.Coprime v →
        64 * (q * R + v * K + 1) ≤ (R / K) ^ (4 ^ j) →
        ∀ (D : Finset ℕ) (inv : ℕ → ℤ),
          (∀ r ∈ D, 0 < r ∧ r ≤ 2 * R) →
          (∀ r ∈ D, ((c * r : ℕ) : ℤ) ∣ (q : ℤ) * inv r - 1) →
          ∀ (β A u δ : ℕ → ℝ), (∀ r ∈ D, 1 ≤ A r) → (∀ r ∈ D, |u r| ≤ 1) →
            (∀ r ∈ D, 0 < δ r) → (∀ r ∈ D, 1 / 2 ≤ δ r * K ∧ δ r * K ≤ 2) →
            (∑ r ∈ D, ‖∑' n : ℤ, fresnelProfile f (A r) (u r + δ r * n) *
              phase (-reciprocalQuadraticFrequency a v c inv r * (n : ℝ) ^ 2 + β r * n)‖) ≤
                C * R * Real.sqrt K * Real.log (35 * (R : ℝ)) ^ O := by
  obtain ⟨C₀, hC₀, hseries⟩ := exists_fresnel_series_mean_constant f
  obtain ⟨C₁, hC₁, O, hO, hmean⟩ := exists_reciprocal_interval_mean_bound j
  refine ⟨C₀ * (C₁ + 1) + 1, by positivity, O, hO, ?_⟩
  intro a v q c R K ha ha4 hc hc8 hK hKR hq hcop hroot D inv hD hinv β A u δ hA hu hδ hscale
  let F := Real.log (35 * (R : ℝ)) ^ O
  have hlog : 1 ≤ Real.log (35 * (R : ℝ)) := by
    apply (one_le_log_nat_of_three_le hK).trans
    apply Real.log_le_log (by exact_mod_cast (by omega : 0 < K))
    have hKR' : (K : ℝ) ≤ R := by exact_mod_cast hKR
    have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg _
    linarith
  have hF : 1 ≤ F := one_le_pow₀ hlog
  have hB : 0 ≤ C₁ * R * K * F := by positivity
  have hnegmean (s : ℕ → ℤ) (l : ℕ → ℕ) (hl : ∀ r ∈ D, l r ≤ K) :
      (∑ r ∈ D, ‖∑ n ∈ Finset.range (l r), phase
        (-reciprocalQuadraticFrequency a v c inv r * ((s r : ℝ) + n) ^ 2 +
          β r * ((s r : ℝ) + n))‖ ^ 2) ≤ C₁ * R * K * F := by
    simp_rw [norm_negative_quadratic_interval]
    exact hmean a v q c R K ha ha4 hc hc8 hK hKR hq hcop hroot D inv hD hinv
      (fun r => -β r) s l hl
  have h := hseries D K (by omega) (fun r => -reciprocalQuadraticFrequency a v c inv r)
    β (C₁ * R * K * F) hB hnegmean A u δ hA hu hδ hscale
  have hcard : D.card ≤ 2 * R := by
    have hsub : D ⊆ Finset.Icc 1 (2 * R) := by
      intro r hr
      exact Finset.mem_Icc.mpr ⟨hD r hr |>.1, hD r hr |>.2⟩
    have hh := Finset.card_le_card hsub
    simpa using hh
  apply h.trans
  calc
    C₀ * Real.sqrt ((D.card : ℝ) * (C₁ * R * K * F)) ≤
        C₀ * ((C₁ + 1) * R * Real.sqrt K * F) :=
      mul_le_mul_of_nonneg_left (sqrt_card_reciprocal_mean_le hC₁.le hF hcard) hC₀
    _ = (C₀ * (C₁ + 1)) * R * Real.sqrt K * F := by ring
    _ ≤ (C₀ * (C₁ + 1) + 1) * R * Real.sqrt K * F := by
      gcongr
      linarith

end Erdos587
