import ErdosProblems.Erdos587.HooleyCenteredMean
import ErdosProblems.Erdos587.HooleyCauchy
import ErdosProblems.Erdos587.LowFrequency

/-!
# Low nearby frequencies with the exact integral mean

The smooth centered mean already retains the integral zero mode, so no
quadrature error is needed when the weights are scaled directly by `L`.
-/

open scoped BigOperators SchwartzMap FourierTransform

namespace Erdos587

lemma delta_integral_centered_chirp_eq (f : 𝓢(ℝ, ℂ)) (q : ℕ) (a : ℤ) (A : ℝ)
    {L : ℝ} (hL : 0 < L) :
    integralCenteredChirpSeries f q a A L⁻¹ =
      deltaSmoothCenteredQuadratic (quadraticChirpMul A f) L q a := by
  let g := quadraticChirpMul A f
  let w := dilateSchwartz g L⁻¹ (inv_ne_zero hL.ne')
  have hzero : (∫ x : ℝ, w x) = (L : ℂ) * 𝓕 g 0 := by
    rw [← fourier_zero_eq_integral]
    change 𝓕 w 0 = _
    rw [delta_fourier_dilate_inverse g hL, mul_zero]
  rw [deltaSmoothCenteredQuadratic, delta_smooth_sum_eq_quadratic_weight _ hL]
  change (∑' n : ℤ, quadraticResiduePhase q a n * w n) -
      (completeQuadraticGaussSum q a 0 / q) * (∫ x : ℝ, w x) = _
  rw [hzero]
  dsimp only [deltaSmoothQuadraticMean, g, w]
  ring

lemma delta_nearby_remainder_eq_centered (f : 𝓢(ℝ, ℂ)) (q r v : ℕ) (b : ℤ)
    {L : ℝ} (hL : 0 < L) :
    nearbyQuadraticRemainder f q r v b L =
      deltaSmoothCenteredQuadratic
        (quadraticChirpMul (((r : ℝ) / (q * v)) * L ^ 2) f) L q ((r : ℤ) * b) := by
  rw [nearbyQuadraticRemainder_eq_integral_centered f q r v b hL,
    delta_integral_centered_chirp_eq f q _ _ hL]

theorem exists_delta_nearby_low_frequency_mean (f : 𝓢(ℝ, ℂ))
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ a q v M X : ℕ, a.Coprime q → 0 < q → 1 ≤ M →
      ∀ L : ℝ, 1 ≤ L → 2 * M * L ≤ X → (q : ℝ) * (X : ℝ) ^ κ ≤ M * L →
      (∀ m ∈ Finset.Icc 1 M, ((m : ℝ) / (q * v)) * L ^ 2 ≤ 1) →
      (∑ m ∈ Finset.Icc 1 M, ‖nearbyQuadraticRemainder f q m v (a : ℤ) L‖) ≤
        C * M * Real.sqrt L * (max 1 (Real.log (Real.log (X : ℝ)))) ^ (7 / 2 : ℝ) := by
  let W := Set.image2 quadraticChirpMul {t : ℝ | |t| ≤ 1} ({f} : Set 𝓢(ℝ, ℂ))
  have hW : Bornology.IsVonNBounded ℝ W :=
    delta_bounded_chirps (Bornology.isVonNBounded_singleton (𝕜 := ℝ) f)
  obtain ⟨C, hC, hmean⟩ := exists_delta_smooth_centered_mean hW hκ
  refine ⟨C + 1, by positivity, ?_⟩
  intro a q v M X haq hq hM L hL hsize hsep hA
  have hLpos : 0 < L := by linarith
  let g (m : ℕ) := quadraticChirpMul (((m : ℝ) / (q * v)) * L ^ 2) f
  have hg (m : ℕ) (hm : m ∈ Finset.Icc 1 M) : g m ∈ W := by
    refine ⟨((m : ℝ) / (q * v)) * L ^ 2, ?_, f, Set.mem_singleton f, rfl⟩
    change |((m : ℝ) / (q * v)) * L ^ 2| ≤ 1
    rw [abs_of_nonneg (by positivity)]
    exact hA m hm
  have h := hmean a M q X hM hq haq.symm L hL hsize hsep g hg
  have heq (m : ℕ) : nearbyQuadraticRemainder f q m v (a : ℤ) L =
      deltaSmoothCenteredQuadratic (g m) L q (a * m) := by
    rw [delta_nearby_remainder_eq_centered f q m v (a : ℤ) hLpos]
    congr 1
    ring
  simp_rw [← heq] at h
  apply delta_sum_norm_le_of_seventh_power (Finset.Icc 1 M)
    (fun m => nearbyQuadraticRemainder f q m v (a : ℤ) L) hC.le (Nat.cast_nonneg M)
    hLpos.le (by positivity) _ h
  simp only [Nat.card_Icc, Nat.add_sub_cancel]
  linarith [Nat.cast_nonneg (α := ℝ) M]

end Erdos587
