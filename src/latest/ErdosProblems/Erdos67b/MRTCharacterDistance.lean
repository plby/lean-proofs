import ErdosProblems.Erdos67b.MRTLogPowerShortIntervals
import ErdosProblems.Erdos67b.MRCofactorTwistDistance

/-! # Character twists at an explicitly controlled lower ambient scale -/

open scoped BigOperators ComplexConjugate

namespace Erdos67b

noncomputable section

def mrtCharacterUntwist (f : ℕ → ℂ) {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ :=
  f n * conj (χ n)

theorem mrtCharacterUntwist_isMultiplicative {f : ℕ → ℂ}
    (hmul : IsMultiplicativeOnPositiveNat f) {q : ℕ} (χ : DirichletCharacter ℂ q) :
    IsMultiplicativeOnPositiveNat (mrtCharacterUntwist f χ) := by
  constructor
  · simp [mrtCharacterUntwist, hmul.1]
  intro m n hm hn hcoprime
  simp only [mrtCharacterUntwist, Nat.cast_mul, map_mul]
  rw [hmul.2 m n hm hn hcoprime]
  ring

theorem norm_mrtCharacterUntwist_le {f : ℕ → ℂ}
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1) {q : ℕ} (χ : DirichletCharacter ℂ q)
    {n : ℕ} (hn : 0 < n) : ‖mrtCharacterUntwist f χ n‖ ≤ 1 := by
  rw [mrtCharacterUntwist, norm_mul, Complex.norm_conj]
  calc
    _ ≤ 1 * 1 := mul_le_mul (hbound n hn) (χ.norm_le_one n) (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

theorem pretentiousDistSq_mrtCharacterUntwist (f : ℕ → ℂ) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (t : ℝ) (X : ℕ) :
    pretentiousDistSq (mrtCharacterUntwist f χ) (archimedeanTwist t) X =
      pretentiousDistSqToTwist f χ t X := by
  simp only [pretentiousDistSqToTwist, pretentiousDistSq, pretentiousTerm,
    mrtCharacterUntwist, dirichletArchimedeanTwist, map_mul, mul_assoc]

def mrtLogScaleDistanceLoss (R : ℝ) : ℝ :=
  2 * Real.log R + 4 * PrimeEstimates.mertensBound

theorem mrtLogScaleDistanceLoss_nonneg {R : ℝ} (hR : 1 ≤ R) :
    0 ≤ mrtLogScaleDistanceLoss R := by
  have hlog := Real.log_nonneg hR
  have hM := PrimeEstimates.mertensBound_nonneg
  unfold mrtLogScaleDistanceLoss
  positivity

theorem mrtPretentiousDistSq_tail_le_logScaleLoss {f g : ℕ → ℂ} {Y X : ℕ}
    {R : ℝ} (hR : 1 ≤ R) (hY : 2 ≤ Y) (hYX : Y ≤ X)
    (hlog : Real.log (X : ℝ) ≤ R * Real.log (Y : ℝ))
    (hf : ∀ p, p.Prime → ‖f p‖ ≤ 1) (hg : ∀ p, p.Prime → ‖g p‖ ≤ 1) :
    pretentiousDistSq f g X - pretentiousDistSq f g Y ≤ mrtLogScaleDistanceLoss R := by
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  have hLY : 0 < Real.log (Y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Y by omega))
  have hLX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hloglog := Real.log_le_log hLX hlog
  rw [Real.log_mul hRpos.ne' hLY.ne'] at hloglog
  have hmass := PrimeEstimates.reciprocalPrimeInterval_le_log_log_sub_add hY hYX
  calc
    _ ≤ ∑ p ∈ primesBetween Y X, 2 / (p : ℝ) :=
      pretentiousDistSq_tail_le_primeHarmonic hYX hf hg
    _ = 2 * PrimeEstimates.reciprocalPrimeInterval Y X := by
      unfold PrimeEstimates.reciprocalPrimeInterval PrimeEstimates.primesInInterval primesBetween
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ ≤ 2 * (Real.log (Real.log (X : ℝ)) - Real.log (Real.log (Y : ℝ)) +
        2 * PrimeEstimates.mertensBound) := mul_le_mul_of_nonneg_left hmass (by norm_num)
    _ ≤ mrtLogScaleDistanceLoss R := by
      unfold mrtLogScaleDistanceLoss
      linarith only [hloglog]

theorem mrtArchimedeanNonpretentious_character_lower_scale
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1) {A M X Y q : ℕ}
    {R : ℝ} (hR : 1 ≤ R) (hA : 1 ≤ A)
    (hMA : (M : ℝ) + mrtLogScaleDistanceLoss R ≤ A)
    (hY : 2 ≤ Y) (hYX : Y ≤ X) (hlog : Real.log (X : ℝ) ≤ R * Real.log (Y : ℝ))
    (hq : 0 < q) (hqA : q ≤ A) (χ : DirichletCharacter ℂ q)
    (hnonpret : MRTNonpretentious f A X) :
    MRArchimedeanNonpretentious (mrtCharacterUntwist f χ) M Y := by
  intro t ht
  rw [pretentiousDistSq_mrtCharacterUntwist]
  have hwindow : |t| ≤ (A : ℝ) * X := by
    calc
      _ ≤ (Y : ℝ) := ht
      _ ≤ (X : ℝ) := by exact_mod_cast hYX
      _ ≤ _ := le_mul_of_one_le_left (Nat.cast_nonneg X) (by exact_mod_cast hA)
  have hlarge := hnonpret q hq hqA χ t hwindow
  have htail := mrtPretentiousDistSq_tail_le_logScaleLoss hR hY hYX hlog
    (fun p hp ↦ hbound p hp.pos)
    (fun p hp ↦ norm_dirichletArchimedeanTwist_le_one χ t hp.pos)
  change pretentiousDistSqToTwist f χ t X - pretentiousDistSqToTwist f χ t Y ≤
    mrtLogScaleDistanceLoss R at htail
  linarith only [hlarge, htail, hMA]

theorem mrtExists_logPower_character_short_firstMoment {rho R : ℝ}
    (hrho : 0 < rho) (hR : 1 ≤ R) :
    ∃ H₀ : ℕ, 10 ≤ H₀ ∧ ∀ H : ℕ, H₀ ≤ H →
      2 ≤ mrtLogPowerWindow (Real.log (H : ℝ)) ∧
      mrtLogPowerLower (Real.log (H : ℝ)) / mrtLogPowerUpper (Real.log (H : ℝ)) ≤ rho ∧
      ∃ K A₀ Y₀ : ℕ, 0 < K ∧ 0 < A₀ ∧ H ≤ Y₀ ∧
        ∀ {A X Y : ℕ}, A₀ ≤ A → Y₀ ≤ Y → Y ≤ X →
          Real.log (X : ℝ) ≤ R * Real.log (Y : ℝ) →
        ∀ {f : ℕ → ℂ}, IsMultiplicativeOnPositiveNat f →
          (∀ n, 0 < n → ‖f n‖ ≤ 1) → MRTNonpretentious f A X →
        ∀ {q : ℕ}, 0 < q → q ≤ A → ∀ χ : DirichletCharacter ℂ q,
        ∀ {h Z : ℕ},
          (H : ℝ) / mrtLogPowerWindow (Real.log (H : ℝ)) ^ 3 ≤ h → h ≤ H → 2 * Y ≤ Z →
          (∑ n ∈ Finset.Ioc Y (2 * Y),
            ‖typicalModulatedShortSum
              (mrScheduledBlocks (mrtLogPowerLower (Real.log (H : ℝ)))
                (mrtLogPowerUpper (Real.log (H : ℝ))) K) Z
                (mrtCharacterUntwist f χ) n h 0‖) ≤
              (h : ℝ) * Y / mrtLogPowerWindow (Real.log (H : ℝ)) ^ 3 := by
  obtain ⟨H₀, hH₀, hmain⟩ := mrtExists_logPower_typical_short_firstMoment hrho
  refine ⟨H₀, hH₀, ?_⟩
  intro H hH
  obtain ⟨hW, hratio, K, M₀, Y₀, hK, _, hY₀, hfirst⟩ := hmain H hH
  let A₀ := max 1 ⌈(M₀ : ℝ) + mrtLogScaleDistanceLoss R⌉₊
  have hA₀ : 0 < A₀ := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  refine ⟨hW, hratio, K, A₀, Y₀, hK, hA₀, hY₀, ?_⟩
  intro A X Y hA hY hYX hlog f hmul hbound hnonpret q hq hqA χ h Z hlength hhH hZ
  have hAone : 1 ≤ A := hA₀.trans_le hA
  have hMA : (M₀ : ℝ) + mrtLogScaleDistanceLoss R ≤ A :=
    Nat.le_of_ceil_le ((le_max_right _ _).trans hA)
  have hYtwo : 2 ≤ Y := by omega
  have hcharNP := mrtArchimedeanNonpretentious_character_lower_scale hbound hR hAone
    hMA hYtwo hYX hlog hq hqA χ hnonpret
  exact hfirst (le_refl M₀) hY (mrtCharacterUntwist_isMultiplicative hmul χ)
    (fun n hn ↦ norm_mrtCharacterUntwist_le hbound χ hn) hcharNP hlength hhH hZ

end

end Erdos67b
