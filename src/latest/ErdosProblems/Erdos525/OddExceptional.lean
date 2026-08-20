import ErdosProblems.Erdos525.OddRegular
import ErdosProblems.Erdos525.Exceptional

open scoped BigOperators ENNReal NNReal Topology Real ComplexConjugate

namespace Erdos525

open Classical Filter Finset Set MeasureTheory

namespace Odd

/-!  Uniform small phase-space boxes for the odd coefficient interval. -/

theorem eventually_scaled_oneBlockProductProbability_le
    (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    ∀ᶠ n : ℕ in atTop, ∀ t : ℝ,
      IsSmooth n (rigiditySmoothScale n) t →
      IsSpread n (rigiditySmoothScale n) (fun _ : Fin 1 ↦ t) →
      (localMeshSize n : ℝ) *
          uniformProbability (fun e : SignVector (2 * n + 1) ↦
            normalizedPhaseEuclideanWalk n e (fun _ : Fin 1 ↦ t) ∈
              oneBlockProductRegion (A / n) B) ≤
        256 * Real.pi ^ 2 * A ^ 2 * B ^ 2 := by
  have hnr : Tendsto (fun n : ℕ ↦ (n : ℝ) * phaseBoundaryRadius n)
      atTop (𝓝 0) := scaled_phaseBoundaryRadius_tendsto_zero
  have hr : Tendsto phaseBoundaryRadius atTop (𝓝 0) :=
    phaseBoundaryRadius_tendsto_zero
  have htail : Tendsto (phaseBoundaryGaussianTail 1) atTop (𝓝 0) := by
    have hscaled := scaled_phaseBoundaryGaussianTail_tendsto_zero 1
    refine squeeze_zero'
      (f := phaseBoundaryGaussianTail 1)
      (g := fun n : ℕ ↦ (localMeshSize n : ℝ) *
        phaseBoundaryGaussianTail 1 n)
      (Eventually.of_forall fun n ↦ by
        unfold phaseBoundaryGaussianTail
        positivity)
      ?_ (by simpa only [pow_one] using hscaled)
    exact Eventually.of_forall fun n ↦ by
      have hone : (1 : ℝ) ≤ localMeshSize n := by
        exact_mod_cast localMeshSize_pos n
      have hnonneg : 0 ≤ phaseBoundaryGaussianTail 1 n := by
        unfold phaseBoundaryGaussianTail
        positivity
      nlinarith
  filter_upwards [Nat.eventually_pos,
      hnr.eventually (Iio_mem_nhds hA),
      hr.eventually (Iio_mem_nhds hB),
      htail.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
      eventually_uniform_phaseSmoothedDensity (m := 1) (by omega)
        (show (0 : ℝ) < 1 by norm_num)]
    with n hn hnrN hrN htailN hdensity
  intro t hsmooth hspread
  let r : ℝ := phaseBoundaryRadius n
  let s := oneBlockProductRegion (A / n) B
  let expanded := oneBlockProductRegion (A / n + r) (B + r)
  let p := uniformProbability (fun e : SignVector (2 * n + 1) ↦
    normalizedPhaseEuclideanWalk n e (fun _ : Fin 1 ↦ t) ∈ s)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hprefix0 : 0 < prefixScale n := prefixScale_pos n
  have hprefix1 : prefixScale n ≤ 1 := prefixScale_le_one n
  have hboundary0 : 0 ≤ phaseBoundaryRadius n := phaseBoundaryRadius_nonneg n
  have hr0 : 0 ≤ r := hboundary0
  have hrLe : r ≤ phaseBoundaryRadius n := le_rfl
  have hposExpand : 0 ≤ A / n + r := by positivity
  have hvelExpand : 0 ≤ B + r := by positivity
  have hfinite : volume expanded ≠ ⊤ :=
    volume_oneBlockProductRegion_ne_top _ _
  have hdensityBound : ∀ y : PhaseEuclidean 1,
      phaseSmoothedDensity n (fun _ : Fin 1 ↦ t)
          (prefixScale n * localCLTSmoothingScaleTest n) y ≤ 4 := by
    intro y
    have hclose := hdensity (fun _ : Fin 1 ↦ t) y
      (fun _ ↦ hsmooth) hspread
    rw [abs_lt] at hclose
    linarith [phaseLimitingDensity_one_le_three y]
  have hInt :
      (∫ y in expanded,
          phaseSmoothedDensity n (fun _ : Fin 1 ↦ t)
            (prefixScale n * localCLTSmoothingScaleTest n) y) ≤
        4 * volume.real expanded := by
    have hsigma : 0 < prefixScale n * localCLTSmoothingScaleTest n :=
      mul_pos hprefix0 (by
        unfold localCLTSmoothingScaleTest
        exact rigidityPower_pos hn _)
    calc
      (∫ y in expanded,
          phaseSmoothedDensity n (fun _ : Fin 1 ↦ t)
            (prefixScale n * localCLTSmoothingScaleTest n) y) ≤
          ∫ _y : PhaseEuclidean 1 in expanded, (4 : ℝ) := by
        apply integral_mono_ae
        · exact (integrable_phaseSmoothedDensity 1 n (fun _ : Fin 1 ↦ t)
            (prefixScale n * localCLTSmoothingScaleTest n) hsigma).integrableOn
        · exact integrableOn_const hfinite
        · filter_upwards [] with y
          exact hdensityBound y
      _ = 4 * volume.real expanded := by
        rw [setIntegral_const]
        simp
        ring
  have hsigma : 0 < prefixScale n * localCLTSmoothingScaleTest n :=
    mul_pos hprefix0 (by
      unfold localCLTSmoothingScaleTest
      exact rigidityPower_pos hn _)
  have hsandwich := uniformProbability_mul_gaussianLower_le_integral_thickening
    n (fun _ : Fin 1 ↦ t)
      (prefixScale n * localCLTSmoothingScaleTest n) r hsigma hr0 s
  have hthick : Metric.thickening r s ⊆ expanded := by
    exact thickening_oneBlockProductRegion_subset _ _ _
  have hmono :
      (∫ y in Metric.thickening r s,
          phaseSmoothedDensity n (fun _ : Fin 1 ↦ t)
            (prefixScale n * localCLTSmoothingScaleTest n) y) ≤
        ∫ y in expanded,
          phaseSmoothedDensity n (fun _ : Fin 1 ↦ t)
            (prefixScale n * localCLTSmoothingScaleTest n) y := by
    exact setIntegral_mono_set
      (integrable_phaseSmoothedDensity 1 n (fun _ : Fin 1 ↦ t)
        (prefixScale n * localCLTSmoothingScaleTest n) hsigma).integrableOn
      (Eventually.of_forall fun y ↦ phaseSmoothedDensity_nonneg 1 n
        (fun _ : Fin 1 ↦ t)
          (prefixScale n * localCLTSmoothingScaleTest n) y)
      (Eventually.of_forall hthick)
  have htailEq :
      2 ^ (2 * 1) * Real.exp (-(r ^ 2 /
          (4 * (prefixScale n * localCLTSmoothingScaleTest n) ^ 2))) =
        phaseBoundaryGaussianTail 1 n := by
    unfold phaseBoundaryGaussianTail
    dsimp [r]
  have hraw : p * (1 / 2) ≤ 4 * volume.real expanded := by
    have hp : 0 ≤ p := uniformProbability_nonneg _
    have hfactor : (1 / 2 : ℝ) < 1 - phaseBoundaryGaussianTail 1 n := by
      linarith
    have hmul := mul_le_mul_of_nonneg_left hfactor.le hp
    calc
      p * (1 / 2) ≤ p * (1 - phaseBoundaryGaussianTail 1 n) := hmul
      _ = p * (1 - 2 ^ (2 * 1) * Real.exp (-(r ^ 2 /
          (4 * (prefixScale n * localCLTSmoothingScaleTest n) ^ 2)))) := by
        rw [htailEq]
      _ ≤ (∫ y in Metric.thickening r s,
          phaseSmoothedDensity n (fun _ : Fin 1 ↦ t)
            (prefixScale n * localCLTSmoothingScaleTest n) y) := by
        simpa only [p, s] using hsandwich
      _ ≤ ∫ y in expanded,
          phaseSmoothedDensity n (fun _ : Fin 1 ↦ t)
            (prefixScale n * localCLTSmoothingScaleTest n) y := hmono
      _ ≤ 4 * volume.real expanded := hInt
  have hpvol : p ≤ 8 * volume.real expanded := by linarith
  have hposRadius : A / n + r < 2 * (A / n) := by
    have hscaled : (n : ℝ) * r < A :=
      (mul_le_mul_of_nonneg_left hrLe hnR.le).trans_lt hnrN
    have hrlt : r < A / n :=
      (lt_div_iff₀ hnR).2 (by simpa [mul_comm] using hscaled)
    linarith
  have hvelRadius : B + r < 2 * B := by
    have : r < B := hrLe.trans_lt hrN
    linarith
  have hmesh : (localMeshSize n : ℝ) ≤ 2 * n ^ 2 := by
    unfold localMeshSize
    push_cast
    nlinarith [show (1 : ℝ) ≤ n by exact_mod_cast hn]
  have hvolEq : volume.real expanded =
      (Real.pi * (A / n + r) ^ 2) *
        (Real.pi * (B + r) ^ 2) := by
    exact volumeReal_oneBlockProductRegion _ _ hposExpand hvelExpand
  have hvolBound : (localMeshSize n : ℝ) * volume.real expanded ≤
      32 * Real.pi ^ 2 * A ^ 2 * B ^ 2 := by
    rw [hvolEq]
    have hposSq := (sq_le_sq₀ hposExpand
      (mul_nonneg (by norm_num) (div_nonneg hA.le hnR.le))).2 hposRadius.le
    have hvelSq := (sq_le_sq₀ hvelExpand
      (mul_nonneg (by norm_num) hB.le)).2 hvelRadius.le
    calc
      (localMeshSize n : ℝ) *
          ((Real.pi * (A / n + r) ^ 2) *
            (Real.pi * (B + r) ^ 2)) ≤
        (2 * n ^ 2) *
          ((Real.pi * (2 * (A / n)) ^ 2) *
            (Real.pi * (2 * B) ^ 2)) := by gcongr
      _ = 32 * Real.pi ^ 2 * A ^ 2 * B ^ 2 := by
        field_simp [hnR.ne']
        ring
  calc
    (localMeshSize n : ℝ) * p ≤
        (localMeshSize n : ℝ) * (8 * volume.real expanded) := by gcongr
    _ ≤ 8 * (32 * Real.pi ^ 2 * A ^ 2 * B ^ 2) := by
      nlinarith [hvolBound]
    _ = 256 * Real.pi ^ 2 * A ^ 2 * B ^ 2 := by ring

def HasLowVelocitySmallMinimum
    (n : ℕ) (u L : ℝ) (e : SignVector (2 * n + 1)) : Prop :=
  ∃ t ∈ Set.Icc (0 : ℝ) (Real.pi * n),
    ‖eval n e t‖ = oddCenteredMin n e ∧
    oddCenteredMin n e ≤ u / n ∧
    IsSmooth n (4 * rigiditySmoothScale n) t ∧
    ‖velocity n e t‖ < L

def HasBoundedLowVelocityMeshWitness
    (n : ℕ) (u L : ℝ) (e : SignVector (2 * n + 1)) : Prop :=
  ∃ a : Fin (localMeshSize n),
    IsSmooth n (rigiditySmoothScale n) (localMeshPoint n a) ∧
    IsSpread n (rigiditySmoothScale n)
      (fun _ : Fin 1 ↦ localMeshPoint n a) ∧
    normalizedPhaseEuclideanWalk n e
        (fun _ : Fin 1 ↦ localMeshPoint n a) ∈
      oneBlockProductRegion ((u + 1 + 2 * Real.pi * L) / n) (2 * L)

lemma oneBlockProductRegion_of_eval_velocity
    (n : ℕ) (e : SignVector (2 * n + 1)) (t A B : ℝ)
    (hpos : ‖eval n e t‖ ≤ A) (hvel : ‖velocity n e t‖ ≤ B) :
    normalizedPhaseEuclideanWalk n e (fun _ : Fin 1 ↦ t) ∈
      oneBlockProductRegion A B := by
  constructor <;>
    simpa only [phaseToBlocks_normalizedPhaseEuclideanWalk] using ‹_›

lemma lowVelocitySmallMinimum_has_bounded_mesh_site
    (n : ℕ) (hn : 0 < n) (u L : ℝ)
    (hwidth : 2 * localMeshHalfWidth n <
      Real.pi * (2 * rigiditySmoothScale n))
    (hheight : minimumTransferHeight n 0 < 1)
    (hvelocityError : minimumVelocityTransferError n < L / 2)
    (e : SignVector (2 * n + 1))
    (hlow : HasLowVelocitySmallMinimum n u L e) :
    HasBoundedLowVelocityMeshWitness n u L e := by
  rcases hlow with ⟨t, ht, hvalue, hsmall, htSmooth, htVelocity⟩
  have htSmoothTwo : IsSmooth n (2 * rigiditySmoothScale n) t := by
    intro p hp1 hpBound
    have hscale : 0 ≤ rigiditySmoothScale n := rigidityPower_nonneg n _
    have hpBound' : p ≤ Nat.floor (4 * rigiditySmoothScale n) + 1 :=
      hpBound.trans (Nat.add_le_add_right
        (Nat.floor_mono (by linarith)) 1)
    have hstrong := htSmooth p hp1 hpBound'
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    exact (div_le_div_of_nonneg_right (by linarith) hnR.le).trans_lt hstrong
  rcases exists_halfLocalMeshSite_within_halfWidth n hn
      (2 * rigiditySmoothScale n) t hwidth htSmoothTwo ht with
    ⟨a, haHalf, haNear⟩
  have hhalf0 : 0 ≤ localMeshHalfWidth n := by
    unfold localMeshHalfWidth
    positivity
  have hC0 : 0 ≤ globalAccelerationBound n := globalAccelerationBound_nonneg n
  have herror0 : 0 ≤ minimumVelocityTransferError n :=
    mul_nonneg hC0 hhalf0
  have hL : 0 < L := by linarith
  have hnearest : IsSmooth n (rigiditySmoothScale n)
      (localMeshPoint n a) := by
    have hKtop : 1 ≤ rigiditySmoothScale n := by
      unfold rigiditySmoothScale rigiditySmoothExponent rigidityPower
      exact Real.one_le_rpow
        (by exact_mod_cast (Nat.succ_le_iff.mpr hn) : (1 : ℝ) ≤ n)
        (by norm_num)
    have hM : (2 : ℝ) * n ≤ localMeshSize n := by
      unfold localMeshSize
      push_cast
      nlinarith [sq_nonneg ((n : ℝ) - 1)]
    have hhalfPi : 2 * localMeshHalfWidth n ≤ Real.pi := by
      unfold localMeshHalfWidth
      rw [show 2 * (Real.pi * (n : ℝ) / (localMeshSize n : ℝ)) =
        (2 * Real.pi * n) / (localMeshSize n : ℝ) by ring]
      rw [div_le_iff₀ (by exact_mod_cast localMeshSize_pos n :
        (0 : ℝ) < localMeshSize n)]
      nlinarith [Real.pi_pos]
    exact htSmoothTwo.of_near hn hKtop hhalf0 hhalfPi haNear
  have hspread := singleton_spread_of_near_four_smooth n hn t ht htSmooth
    a haHalf haNear hwidth
  have hvelDiff := abs_norm_velocity_sub_le_of_near n e t a haNear
  have hvelSite : ‖velocity n e (localMeshPoint n a)‖ ≤ 2 * L := by
    rw [abs_le] at hvelDiff
    linarith [hvelDiff.1]
  have htVelBound : ‖velocity n e t‖ ≤ 2 * L := by linarith
  have htaylor := norm_eval_sub_linear_le n e t (localMeshPoint n a)
  have hdiff : |localMeshPoint n a - t| ≤ localMeshHalfWidth n := by
    simpa [abs_sub_comm] using haNear
  have hTaylorBound :
      ‖eval n e (localMeshPoint n a) -
          (eval n e t + ((localMeshPoint n a - t : ℝ) : ℂ) *
            velocity n e t)‖ ≤
        globalAccelerationBound n * localMeshHalfWidth n ^ 2 := by
    exact htaylor.trans (mul_le_mul_of_nonneg_left
      (by
        have hs := pow_le_pow_left₀ (abs_nonneg _) hdiff 2
        simpa only [sq_abs] using hs) hC0)
  have hposSite : ‖eval n e (localMeshPoint n a)‖ ≤
      (u + 1 + 2 * Real.pi * L) / n := by
    have htri : ‖eval n e (localMeshPoint n a)‖ ≤
        ‖eval n e (localMeshPoint n a) -
          (eval n e t + ((localMeshPoint n a - t : ℝ) : ℂ) *
            velocity n e t)‖ +
        ‖eval n e t‖ + |localMeshPoint n a - t| * ‖velocity n e t‖ := by
      calc
        _ ≤ ‖eval n e (localMeshPoint n a) -
              (eval n e t + ((localMeshPoint n a - t : ℝ) : ℂ) *
                velocity n e t)‖ +
            ‖eval n e t + ((localMeshPoint n a - t : ℝ) : ℂ) *
              velocity n e t‖ := by
          have h := norm_add_le
            (eval n e (localMeshPoint n a) -
              (eval n e t + ((localMeshPoint n a - t : ℝ) : ℂ) *
                velocity n e t))
            (eval n e t + ((localMeshPoint n a - t : ℝ) : ℂ) *
              velocity n e t)
          simpa only [sub_add_cancel] using h
        _ ≤ _ := add_le_add (le_refl _) (norm_add_le _ _)
        _ = _ := by
          simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          ring
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hvalueBound : ‖eval n e t‖ ≤ u / n := by
      simpa [hvalue] using hsmall
    have hheightScaled : (n : ℝ) * globalAccelerationBound n *
        localMeshHalfWidth n ^ 2 < 1 := by
      simpa [minimumTransferHeight] using hheight
    have hmesh := n_mul_localMeshHalfWidth_le_pi n
    have hproduct : |localMeshPoint n a - t| * ‖velocity n e t‖ ≤
        localMeshHalfWidth n * (2 * L) :=
      mul_le_mul hdiff htVelBound (norm_nonneg _) hhalf0
    have hbase : ‖eval n e (localMeshPoint n a)‖ ≤
        globalAccelerationBound n * localMeshHalfWidth n ^ 2 +
          u / n + localMeshHalfWidth n * (2 * L) :=
      htri.trans (add_le_add (add_le_add hTaylorBound hvalueBound) hproduct)
    apply (le_div_iff₀ hnR).2
    calc
      ‖eval n e (localMeshPoint n a)‖ * n ≤
          (globalAccelerationBound n * localMeshHalfWidth n ^ 2 +
            u / n + localMeshHalfWidth n * (2 * L)) * n :=
        mul_le_mul_of_nonneg_right hbase hnR.le
      _ ≤ u + 1 + 2 * Real.pi * L := by
        have hlin : (n : ℝ) * localMeshHalfWidth n * (2 * L) ≤
            Real.pi * (2 * L) :=
          mul_le_mul_of_nonneg_right hmesh (mul_nonneg (by norm_num) hL.le)
        have hlt :
            (globalAccelerationBound n * localMeshHalfWidth n ^ 2 +
              u / n + localMeshHalfWidth n * (2 * L)) * n <
              u + 1 + 2 * Real.pi * L := by
          field_simp [hnR.ne']
          nlinarith
        exact hlt.le
  exact ⟨a, hnearest, hspread,
    oneBlockProductRegion_of_eval_velocity n e (localMeshPoint n a)
      ((u + 1 + 2 * Real.pi * L) / n) (2 * L) hposSite hvelSite⟩

theorem eventually_lowVelocitySmallMinimum_probability_le
    (u L : ℝ) (hu : 0 ≤ u) (hL : 0 < L) :
    ∀ᶠ n : ℕ in atTop,
      uniformProbability (HasLowVelocitySmallMinimum n u L) ≤
        256 * Real.pi ^ 2 * (u + 1 + 2 * Real.pi * L) ^ 2 *
          (2 * L) ^ 2 := by
  let A := u + 1 + 2 * Real.pi * L
  let B := 2 * L
  have hA : 0 < A := by dsimp [A]; nlinarith [Real.pi_pos]
  have hB : 0 < B := by dsimp [B]; linarith
  have hheight : ∀ᶠ n : ℕ in atTop, minimumTransferHeight n 0 < 1 :=
    (minimumTransferHeight_tendsto 0).eventually
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hvelocity : ∀ᶠ n : ℕ in atTop,
      minimumVelocityTransferError n < L / 2 :=
    minimumVelocityTransferError_tendsto_zero.eventually
      (Iio_mem_nhds (half_pos hL))
  have hbox := eventually_scaled_oneBlockProductProbability_le A B hA hB
  filter_upwards [Nat.eventually_pos,
      eventually_two_halfWidth_lt_pi_mul_rigiditySmoothScale,
      hheight, hvelocity, hbox]
    with n hn hwidth hheightN hvelocityN hboxN
  let P : Fin (localMeshSize n) → SignVector (2 * n + 1) → Prop :=
    fun a e ↦
      IsSmooth n (rigiditySmoothScale n) (localMeshPoint n a) ∧
      IsSpread n (rigiditySmoothScale n)
        (fun _ : Fin 1 ↦ localMeshPoint n a) ∧
      normalizedPhaseEuclideanWalk n e
          (fun _ : Fin 1 ↦ localMeshPoint n a) ∈
        oneBlockProductRegion (A / n) B
  have hmeshPos : (0 : ℝ) < localMeshSize n := by
    exact_mod_cast localMeshSize_pos n
  have hsite : ∀ a : Fin (localMeshSize n),
      uniformProbability (P a) ≤
        (256 * Real.pi ^ 2 * A ^ 2 * B ^ 2) / localMeshSize n := by
    intro a
    by_cases hsmooth : IsSmooth n (rigiditySmoothScale n)
        (localMeshPoint n a)
    · by_cases hspread : IsSpread n (rigiditySmoothScale n)
          (fun _ : Fin 1 ↦ localMeshPoint n a)
      · apply (le_div_iff₀ hmeshPos).2
        have hmono : uniformProbability (P a) ≤
            uniformProbability (fun e : SignVector (2 * n + 1) ↦
              normalizedPhaseEuclideanWalk n e
                  (fun _ : Fin 1 ↦ localMeshPoint n a) ∈
                oneBlockProductRegion (A / n) B) := by
          apply uniformProbability_mono
          intro e he
          exact he.2.2
        calc
          uniformProbability (P a) * (localMeshSize n : ℝ) ≤
              (localMeshSize n : ℝ) *
                uniformProbability (fun e : SignVector (2 * n + 1) ↦
                  normalizedPhaseEuclideanWalk n e
                    (fun _ : Fin 1 ↦ localMeshPoint n a) ∈
                      oneBlockProductRegion (A / n) B) := by
            rw [mul_comm]
            exact mul_le_mul_of_nonneg_left hmono hmeshPos.le
          _ ≤ 256 * Real.pi ^ 2 * A ^ 2 * B ^ 2 :=
            hboxN (localMeshPoint n a) hsmooth hspread
      · have hempty : ∀ e : SignVector (2 * n + 1), ¬P a e := by
          intro e he
          exact hspread he.2.1
        rw [show uniformProbability (P a) = 0 by
          unfold uniformProbability; simp [Finset.filter_eq_empty_iff, hempty]]
        positivity
    · have hempty : ∀ e : SignVector (2 * n + 1), ¬P a e := by
        intro e he
        exact hsmooth he.1
      rw [show uniformProbability (P a) = 0 by
        unfold uniformProbability; simp [Finset.filter_eq_empty_iff, hempty]]
      positivity
  have hwitness : uniformProbability
      (HasBoundedLowVelocityMeshWitness n u L) ≤
      256 * Real.pi ^ 2 * A ^ 2 * B ^ 2 := by
    have hexists : uniformProbability (fun e : SignVector (2 * n + 1) ↦
        ∃ a, P a e) ≤ ∑ a, uniformProbability (P a) :=
      uniformProbability_exists_le_sum P
    calc
      uniformProbability (HasBoundedLowVelocityMeshWitness n u L) =
          uniformProbability (fun e : SignVector (2 * n + 1) ↦
            ∃ a, P a e) := by
        apply congrArg uniformProbability
        funext e
        apply propext
        simp only [HasBoundedLowVelocityMeshWitness, P, A, B]
      _ ≤ ∑ a, uniformProbability (P a) := hexists
      _ ≤ ∑ _a : Fin (localMeshSize n),
          (256 * Real.pi ^ 2 * A ^ 2 * B ^ 2) / localMeshSize n := by
        exact Finset.sum_le_sum fun a _ha ↦ hsite a
      _ = 256 * Real.pi ^ 2 * A ^ 2 * B ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        simp only [nsmul_eq_mul]
        field_simp [hmeshPos.ne']
  calc
    uniformProbability (HasLowVelocitySmallMinimum n u L) ≤
        uniformProbability (HasBoundedLowVelocityMeshWitness n u L) := by
      apply uniformProbability_mono
      intro e he
      exact lowVelocitySmallMinimum_has_bounded_mesh_site
        n hn u L hwidth hheightN hvelocityN e he
    _ ≤ 256 * Real.pi ^ 2 * A ^ 2 * B ^ 2 := hwitness
    _ = _ := rfl

end Odd

end Erdos525
