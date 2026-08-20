import ErdosProblems.Erdos525.GlobalTransfer

open scoped BigOperators ENNReal NNReal Topology Real ComplexConjugate
open MeasureTheory Filter Set

namespace Erdos525

/-!  Bounded phase-space boxes used to remove the small-velocity cutoff. -/

def oneBlockProductRegion (positionRadius velocityRadius : ℝ) :
    Set (PhaseEuclidean 1) :=
  {y | ‖(phaseToBlocks y 0).1‖ ≤ positionRadius ∧
    ‖(phaseToBlocks y 0).2‖ ≤ velocityRadius}

lemma oneBlockProductRegion_eq_preimage_pi
    (positionRadius velocityRadius : ℝ) :
    oneBlockProductRegion positionRadius velocityRadius =
      phaseToBlocks ⁻¹' Set.univ.pi (fun _ : Fin 1 ↦
        Metric.closedBall (0 : ℂ) positionRadius ×ˢ
          Metric.closedBall (0 : ℂ) velocityRadius) := by
  ext y
  simp only [oneBlockProductRegion, Set.mem_setOf_eq, Set.mem_preimage,
    Set.mem_pi, Set.mem_univ, forall_const, Set.mem_prod,
    Metric.mem_closedBall, dist_zero_right]
  constructor
  · intro h r
    simpa only [Fin.eq_zero r] using h
  · intro h
    exact h 0

lemma measurableSet_oneBlockProductRegion
    (positionRadius velocityRadius : ℝ) :
    MeasurableSet (oneBlockProductRegion positionRadius velocityRadius) := by
  rw [oneBlockProductRegion_eq_preimage_pi]
  exact (MeasurableSet.univ_pi fun _ ↦
    Metric.isClosed_closedBall.measurableSet.prod
      Metric.isClosed_closedBall.measurableSet).preimage
    (measurePreserving_phaseToBlocks (m := 1) (by omega)).measurable

lemma volumeReal_oneBlockProductRegion
    (positionRadius velocityRadius : ℝ)
    (hposition : 0 ≤ positionRadius) (hvelocity : 0 ≤ velocityRadius) :
    volume.real (oneBlockProductRegion positionRadius velocityRadius) =
      (Real.pi * positionRadius ^ 2) *
        (Real.pi * velocityRadius ^ 2) := by
  let S : Set (Fin 1 → (ℂ × ℂ)) := Set.univ.pi (fun _ : Fin 1 ↦
    Metric.closedBall (0 : ℂ) positionRadius ×ˢ
      Metric.closedBall (0 : ℂ) velocityRadius)
  have hS : MeasurableSet S := MeasurableSet.univ_pi fun _ ↦
    Metric.isClosed_closedBall.measurableSet.prod
      Metric.isClosed_closedBall.measurableSet
  have hpre := (measurePreserving_phaseToBlocks (m := 1) (by omega)).measure_preimage
    hS.nullMeasurableSet
  rw [oneBlockProductRegion_eq_preimage_pi]
  change volume.real (phaseToBlocks ⁻¹' S) = _
  rw [measureReal_def, hpre, volume_pi_pi, Fin.prod_univ_one,
    MeasureTheory.Measure.volume_eq_prod, Measure.prod_prod]
  rw [InnerProductSpace.volume_closedBall_of_dim_even
      (E := ℂ) (k := 1) (by simp),
    InnerProductSpace.volume_closedBall_of_dim_even
      (E := ℂ) (k := 1) (by simp)]
  simp only [Complex.finrank_real_complex, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal hposition,
    ENNReal.toReal_ofReal hvelocity, pow_two, Nat.factorial_one,
    Nat.cast_one, div_one]
  simp only [pow_one]
  rw [ENNReal.toReal_ofReal Real.pi_pos.le]
  ring

lemma volume_oneBlockProductRegion_ne_top
    (positionRadius velocityRadius : ℝ) :
    volume (oneBlockProductRegion positionRadius velocityRadius) ≠ ⊤ := by
  have hcompact : IsCompact
      (Metric.closedBall (0 : ℂ) positionRadius ×ˢ
        Metric.closedBall (0 : ℂ) velocityRadius) :=
    (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  let S : Set (Fin 1 → (ℂ × ℂ)) := Set.univ.pi (fun _ : Fin 1 ↦
    Metric.closedBall (0 : ℂ) positionRadius ×ˢ
      Metric.closedBall (0 : ℂ) velocityRadius)
  have hS : MeasurableSet S := MeasurableSet.univ_pi fun _ ↦
    Metric.isClosed_closedBall.measurableSet.prod
      Metric.isClosed_closedBall.measurableSet
  have hpre := (measurePreserving_phaseToBlocks (m := 1) (by omega)).measure_preimage
    hS.nullMeasurableSet
  rw [oneBlockProductRegion_eq_preimage_pi]
  change volume (phaseToBlocks ⁻¹' S) ≠ ⊤
  rw [hpre, volume_pi_pi, Fin.prod_univ_one]
  exact hcompact.measure_lt_top.ne

lemma thickening_oneBlockProductRegion_subset
    (positionRadius velocityRadius boundaryRadius : ℝ) :
    Metric.thickening boundaryRadius
        (oneBlockProductRegion positionRadius velocityRadius) ⊆
      oneBlockProductRegion (positionRadius + boundaryRadius)
        (velocityRadius + boundaryRadius) := by
  intro y hy
  rw [Metric.mem_thickening_iff] at hy
  rcases hy with ⟨x, hx, hxy⟩
  constructor
  · calc
      ‖(phaseToBlocks y 0).1‖ ≤
          ‖(phaseToBlocks x 0).1‖ +
            ‖(phaseToBlocks y 0).1 - (phaseToBlocks x 0).1‖ := by
        have := norm_add_le
          ((phaseToBlocks x 0).1)
          ((phaseToBlocks y 0).1 - (phaseToBlocks x 0).1)
        simpa [add_sub_cancel_left, add_comm] using this
      _ ≤ positionRadius + boundaryRadius := by
        gcongr
        · exact hx.1
        · exact (norm_phaseToBlocks_fst_sub_le y x 0).trans hxy.le
  · calc
      ‖(phaseToBlocks y 0).2‖ ≤
          ‖(phaseToBlocks x 0).2‖ +
            ‖(phaseToBlocks y 0).2 - (phaseToBlocks x 0).2‖ := by
        have := norm_add_le
          ((phaseToBlocks x 0).2)
          ((phaseToBlocks y 0).2 - (phaseToBlocks x 0).2)
        simpa [add_sub_cancel_left, add_comm] using this
      _ ≤ velocityRadius + boundaryRadius := by
        gcongr
        · exact hx.2
        · exact (norm_phaseToBlocks_snd_sub_le y x 0).trans hxy.le

lemma phaseLimitingDensity_one_le_three (y : PhaseEuclidean 1) :
    phaseLimitingDensity y ≤ 3 := by
  unfold phaseLimitingDensity
  rw [Fin.prod_univ_one]
  have hexp : Real.exp
      (-(y (0, 0) ^ 2 + y (0, 1) ^ 2) -
        3 * (y (0, 2) ^ 2 + y (0, 3) ^ 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith [sq_nonneg (y (0, 0)), sq_nonneg (y (0, 1)),
      sq_nonneg (y (0, 2)), sq_nonneg (y (0, 3))]
  have hcoeff : 0 ≤ 3 / Real.pi ^ 2 := by positivity
  calc
    (3 / Real.pi ^ 2) * Real.exp
        (-(y (0, 0) ^ 2 + y (0, 1) ^ 2) -
          3 * (y (0, 2) ^ 2 + y (0, 3) ^ 2)) ≤
        (3 / Real.pi ^ 2) * 1 :=
      mul_le_mul_of_nonneg_left hexp hcoeff
    _ ≤ 3 := by
      have hpi : 1 ≤ Real.pi ^ 2 := by
        nlinarith [Real.pi_gt_three]
      rw [mul_one]
      exact (div_le_iff₀ (sq_pos_of_pos Real.pi_pos)).2 (by nlinarith)

theorem eventually_scaled_oneBlockProductProbability_le
    (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    ∀ᶠ n : ℕ in atTop, ∀ t : ℝ,
      IsSmooth n (rigiditySmoothScale n) t →
      IsSpread n (rigiditySmoothScale n) (fun _ : Fin 1 ↦ t) →
      (localMeshSize n : ℝ) *
          uniformProbability (fun e : SignVector (2 * n) ↦
            normalizedPhaseEuclideanWalk n e (fun _ : Fin 1 ↦ t) ∈
              oneBlockProductRegion (A / n) B) ≤
        256 * Real.pi ^ 2 * A ^ 2 * B ^ 2 := by
  have hnr : Tendsto (fun n : ℕ ↦ (n : ℝ) * phaseBoundaryRadius n)
      atTop (nhds 0) := scaled_phaseBoundaryRadius_tendsto_zero
  have hr : Tendsto phaseBoundaryRadius atTop (nhds 0) :=
    phaseBoundaryRadius_tendsto_zero
  have htail : Tendsto (phaseBoundaryGaussianTail 1) atTop (nhds 0) := by
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
  let s := oneBlockProductRegion (A / n) B
  let expanded := oneBlockProductRegion
    (A / n + phaseBoundaryRadius n) (B + phaseBoundaryRadius n)
  let p := uniformProbability (fun e : SignVector (2 * n) ↦
    normalizedPhaseEuclideanWalk n e (fun _ : Fin 1 ↦ t) ∈ s)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hboundary0 : 0 ≤ phaseBoundaryRadius n := phaseBoundaryRadius_nonneg n
  have hposExpand : 0 ≤ A / n + phaseBoundaryRadius n := by positivity
  have hvelExpand : 0 ≤ B + phaseBoundaryRadius n := by positivity
  have hfinite : volume expanded ≠ ⊤ :=
    volume_oneBlockProductRegion_ne_top _ _
  have hdensityBound : ∀ y : PhaseEuclidean 1,
      phaseSmoothedDensity n (fun _ : Fin 1 ↦ t)
          (localCLTSmoothingScaleTest n) y ≤ 4 := by
    intro y
    have hclose := hdensity (fun _ : Fin 1 ↦ t) y
      (fun _ ↦ hsmooth) hspread
    rw [abs_lt] at hclose
    linarith [phaseLimitingDensity_one_le_three y]
  have hInt :
      (∫ y in expanded,
          phaseSmoothedDensity n (fun _ : Fin 1 ↦ t)
            (localCLTSmoothingScaleTest n) y) ≤
        4 * volume.real expanded := by
    have hsigma : 0 < localCLTSmoothingScaleTest n := by
      unfold localCLTSmoothingScaleTest
      exact rigidityPower_pos hn _
    calc
      (∫ y in expanded,
          phaseSmoothedDensity n (fun _ : Fin 1 ↦ t)
            (localCLTSmoothingScaleTest n) y) ≤
          ∫ _y : PhaseEuclidean 1 in expanded, (4 : ℝ) := by
        apply integral_mono_ae
        · exact (integrable_phaseSmoothedDensity 1 n (fun _ : Fin 1 ↦ t)
            (localCLTSmoothingScaleTest n) hsigma).integrableOn
        · exact integrableOn_const hfinite
        · filter_upwards [] with y
          exact hdensityBound y
      _ = 4 * volume.real expanded := by
        rw [setIntegral_const]
        simp
        ring
  have hsandwich := uniformProbability_mul_gaussianLower_le_integral_thickening
    n (fun _ : Fin 1 ↦ t) (localCLTSmoothingScaleTest n)
      (phaseBoundaryRadius n)
      (by unfold localCLTSmoothingScaleTest; exact rigidityPower_pos hn _)
      hboundary0 s
  have hthick : Metric.thickening (phaseBoundaryRadius n) s ⊆ expanded := by
    exact thickening_oneBlockProductRegion_subset _ _ _
  have hmono :
      (∫ y in Metric.thickening (phaseBoundaryRadius n) s,
          phaseSmoothedDensity n (fun _ : Fin 1 ↦ t)
            (localCLTSmoothingScaleTest n) y) ≤
        ∫ y in expanded,
          phaseSmoothedDensity n (fun _ : Fin 1 ↦ t)
            (localCLTSmoothingScaleTest n) y := by
    exact setIntegral_mono_set
      (integrable_phaseSmoothedDensity 1 n (fun _ : Fin 1 ↦ t)
        (localCLTSmoothingScaleTest n)
        (by unfold localCLTSmoothingScaleTest; exact rigidityPower_pos hn _)).integrableOn
      (Eventually.of_forall fun y ↦ phaseSmoothedDensity_nonneg 1 n
        (fun _ : Fin 1 ↦ t) (localCLTSmoothingScaleTest n) y)
      (Eventually.of_forall hthick)
  have htailEq : phaseBoundaryGaussianTail 1 n =
      2 ^ (2 * 1) * Real.exp (-(phaseBoundaryRadius n ^ 2 /
        (4 * localCLTSmoothingScaleTest n ^ 2))) := rfl
  have hraw : p * (1 / 2) ≤ 4 * volume.real expanded := by
    have hp : 0 ≤ p := uniformProbability_nonneg _
    have hfactor : (1 / 2 : ℝ) < 1 - phaseBoundaryGaussianTail 1 n := by
      linarith
    have hmul := mul_le_mul_of_nonneg_left hfactor.le hp
    calc
      p * (1 / 2) ≤ p * (1 - phaseBoundaryGaussianTail 1 n) := hmul
      _ ≤ (∫ y in Metric.thickening (phaseBoundaryRadius n) s,
          phaseSmoothedDensity n (fun _ : Fin 1 ↦ t)
            (localCLTSmoothingScaleTest n) y) := by
        simpa only [p, s, phaseBoundaryGaussianTail, one_mul] using hsandwich
      _ ≤ ∫ y in expanded,
          phaseSmoothedDensity n (fun _ : Fin 1 ↦ t)
            (localCLTSmoothingScaleTest n) y := hmono
      _ ≤ 4 * volume.real expanded := hInt
  have hpvol : p ≤ 8 * volume.real expanded := by linarith
  have hposRadius : A / n + phaseBoundaryRadius n < 2 * (A / n) := by
    have hscaled : (n : ℝ) * phaseBoundaryRadius n < A := hnrN
    have hrlt : phaseBoundaryRadius n < A / n :=
      (lt_div_iff₀ hnR).2 (by simpa [mul_comm] using hscaled)
    linarith
  have hvelRadius : B + phaseBoundaryRadius n < 2 * B := by linarith
  have hmesh : (localMeshSize n : ℝ) ≤ 2 * n ^ 2 := by
    unfold localMeshSize
    push_cast
    nlinarith [show (1 : ℝ) ≤ n by exact_mod_cast hn]
  have hvolEq : volume.real expanded =
      (Real.pi * (A / n + phaseBoundaryRadius n) ^ 2) *
        (Real.pi * (B + phaseBoundaryRadius n) ^ 2) := by
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
          ((Real.pi * (A / n + phaseBoundaryRadius n) ^ 2) *
            (Real.pi * (B + phaseBoundaryRadius n) ^ 2)) ≤
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

lemma localMeshPoint_nonneg_of_mem_half
    (n : ℕ) (a : Fin (localMeshSize n))
    (ha : a ∈ halfLocalMeshSites n) :
    0 ≤ localMeshPoint n a := by
  rw [halfLocalMeshSites] at ha
  rcases Finset.mem_image.mp ha with ⟨b, _hb, rfl⟩
  exact halfLocalMeshPoint_nonneg n b

lemma singleton_spread_of_near_four_smooth
    (n : ℕ) (hn : 0 < n) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi * n))
    (htSmooth : IsSmooth n (4 * rigiditySmoothScale n) t)
    (a : Fin (localMeshSize n)) (haHalf : a ∈ halfLocalMeshSites n)
    (haNear : |t - localMeshPoint n a| ≤ localMeshHalfWidth n)
    (hwidth : 2 * localMeshHalfWidth n <
      Real.pi * (2 * rigiditySmoothScale n)) :
    IsSpread n (rigiditySmoothScale n)
      (fun _ : Fin 1 ↦ localMeshPoint n a) := by
  let K := rigiditySmoothScale n
  let x := localMeshPoint n a
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hK0 : 0 ≤ K := by
    dsimp [K, rigiditySmoothScale]
    exact rigidityPower_nonneg n _
  have hsep := htSmooth.halfPeriod_endpoint_separation hn ht
  have hx0 : 0 ≤ x := localMeshPoint_nonneg_of_mem_half n a haHalf
  have hxlt : x < Real.pi * n := (localMeshPoint_mem_Ico n hn a).2
  have hnearLower : t - localMeshHalfWidth n ≤ x := by
    rw [abs_le] at haNear
    dsimp [x]
    linarith [haNear.2]
  have hh : localMeshHalfWidth n < Real.pi * K := by
    dsimp [K] at hwidth ⊢
    linarith
  have hxLower : 2 * Real.pi * K < x := by
    have htLower : 4 * Real.pi * K < t := by
      dsimp [K] at hsep ⊢
      nlinarith [Real.pi_pos]
    linarith [Real.pi_pos]
  constructor
  · intro _hm r
    have hr : r = 0 := Subsingleton.elim _ _
    subst r
    have hratio0 : 0 ≤ x / (2 * Real.pi * n) := by positivity
    have hratioHalf : x / (2 * Real.pi * n) ≤ 1 / 2 := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi * n)).2
      nlinarith
    rw [distanceToInteger_eq_self_of_nonneg_le_half hratio0 hratioHalf]
    apply (lt_of_lt_of_le ?_ le_rfl).le
    have hden : 0 < 2 * Real.pi * (n : ℝ) := by positivity
    change K / n < x / (2 * Real.pi * n)
    calc
      K / n = (2 * Real.pi * K) / (2 * Real.pi * n) := by
        field_simp [hnR.ne', Real.pi_ne_zero]
      _ < x / (2 * Real.pi * n) :=
        (div_lt_div_iff_of_pos_right hden).2 hxLower
  · intro r s hrs
    exact (hrs (Subsingleton.elim r s)).elim

lemma oneBlockProductRegion_of_eval_velocity
    (n : ℕ) (e : SignVector (2 * n)) (t A B : ℝ)
    (hpos : ‖rescaledCenteredEval n e t‖ ≤ A)
    (hvel : ‖rescaledCenteredVelocity n e t‖ ≤ B) :
    normalizedPhaseEuclideanWalk n e (fun _ : Fin 1 ↦ t) ∈
      oneBlockProductRegion A B := by
  constructor
  · simpa only [phaseToBlocks_normalizedPhaseEuclideanWalk] using hpos
  · simpa only [phaseToBlocks_normalizedPhaseEuclideanWalk] using hvel

lemma lowVelocitySmallMinimum_good_has_bounded_mesh_site
    (n : ℕ) (hn : 0 < n) (u L : ℝ)
    (hwidth : 2 * localMeshHalfWidth n <
      Real.pi * (2 * rigiditySmoothScale n))
    (hheight : minimumTransferHeight n 0 < 1)
    (hvelocityError : minimumVelocityTransferError n < L / 2)
    (e : SignVector (2 * n))
    (hlow : HasLowVelocitySmallMinimum n u L e)
    (hacc : ¬HasHighMeshAcceleration n e) :
    ∃ a ∈ halfLocalMeshSites n,
      IsSmooth n (rigiditySmoothScale n) (localMeshPoint n a) ∧
      IsSpread n (rigiditySmoothScale n)
        (fun _ : Fin 1 ↦ localMeshPoint n a) ∧
      normalizedPhaseEuclideanWalk n e
          (fun _ : Fin 1 ↦ localMeshPoint n a) ∈
        oneBlockProductRegion ((u + 1 + 2 * Real.pi * L) / n) (2 * L) := by
  rcases hlow with ⟨t, ht, hvalue, hsmall, htSmooth, htVelocity⟩
  have htSmoothTwo : IsSmooth n (2 * rigiditySmoothScale n) t := by
    intro p hp1 hpBound
    have hscale : 0 ≤ rigiditySmoothScale n := by
      unfold rigiditySmoothScale
      exact rigidityPower_nonneg n _
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
  have hC0 : 0 ≤ globalAccelerationBound n := by
    unfold globalAccelerationBound accelerationCutoff
    exact add_nonneg (rigidityPower_nonneg n _)
      (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hhalf0)
  have herror0 : 0 ≤ minimumVelocityTransferError n := by
    exact mul_nonneg hC0 hhalf0
  have hL : 0 < L := by linarith
  have hnearest : IsSmooth n (rigiditySmoothScale n) (localMeshPoint n a) := by
    -- The caller supplies `hwidth`; the pointwise smoothness transfer uses
    -- only the same elementary perturbation estimate.
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
  have hxIco := localMeshPoint_mem_Ico n hn a
  have hx : localMeshPoint n a ∈
      Set.Icc (-(Real.pi * n)) (Real.pi * n) := ⟨hxIco.1, hxIco.2.le⟩
  have htFull : t ∈ Set.Icc (-(Real.pi * n)) (Real.pi * n) := by
    have hpin : 0 < Real.pi * (n : ℝ) := by positivity
    exact ⟨(neg_nonpos.mpr hpin.le).trans ht.1, ht.2⟩
  have hvelDiff := abs_norm_rescaledCenteredVelocity_sub_le_of_near
    n hn e hacc t ht a haNear
  have hvelSite : ‖rescaledCenteredVelocity n e (localMeshPoint n a)‖ ≤
      2 * L := by
    rw [abs_le] at hvelDiff
    linarith [hvelDiff.1]
  have htVelBound : ‖rescaledCenteredVelocity n e t‖ ≤ 2 * L := by
    linarith
  have htaylor := norm_rescaledCenteredEval_sub_linear_le_of_not_high
    n hn e hacc t (localMeshPoint n a) htFull hx
  have hdiff : |localMeshPoint n a - t| ≤ localMeshHalfWidth n := by
    simpa [abs_sub_comm] using haNear
  have hTaylorBound :
      ‖rescaledCenteredEval n e (localMeshPoint n a) -
          (rescaledCenteredEval n e t +
            ((localMeshPoint n a - t : ℝ) : ℂ) *
              rescaledCenteredVelocity n e t)‖ ≤
        globalAccelerationBound n * localMeshHalfWidth n ^ 2 := by
    exact htaylor.trans (mul_le_mul_of_nonneg_left
      (by
        have hs := pow_le_pow_left₀ (abs_nonneg _) hdiff 2
        simpa only [sq_abs] using hs) hC0)
  have hposSite : ‖rescaledCenteredEval n e (localMeshPoint n a)‖ ≤
      (u + 1 + 2 * Real.pi * L) / n := by
    have htri : ‖rescaledCenteredEval n e (localMeshPoint n a)‖ ≤
        ‖rescaledCenteredEval n e (localMeshPoint n a) -
          (rescaledCenteredEval n e t +
            ((localMeshPoint n a - t : ℝ) : ℂ) *
              rescaledCenteredVelocity n e t)‖ +
        ‖rescaledCenteredEval n e t‖ +
        |localMeshPoint n a - t| *
          ‖rescaledCenteredVelocity n e t‖ := by
      calc
        _ ≤ ‖rescaledCenteredEval n e (localMeshPoint n a) -
              (rescaledCenteredEval n e t +
                ((localMeshPoint n a - t : ℝ) : ℂ) *
                  rescaledCenteredVelocity n e t)‖ +
            ‖rescaledCenteredEval n e t +
              ((localMeshPoint n a - t : ℝ) : ℂ) *
                rescaledCenteredVelocity n e t‖ := by
          have := norm_add_le
            (rescaledCenteredEval n e (localMeshPoint n a) -
              (rescaledCenteredEval n e t +
                ((localMeshPoint n a - t : ℝ) : ℂ) *
                  rescaledCenteredVelocity n e t))
            (rescaledCenteredEval n e t +
              ((localMeshPoint n a - t : ℝ) : ℂ) *
                rescaledCenteredVelocity n e t)
          simpa only [sub_add_cancel] using this
        _ ≤ ‖rescaledCenteredEval n e (localMeshPoint n a) -
              (rescaledCenteredEval n e t +
                ((localMeshPoint n a - t : ℝ) : ℂ) *
                  rescaledCenteredVelocity n e t)‖ +
            (‖rescaledCenteredEval n e t‖ +
              ‖((localMeshPoint n a - t : ℝ) : ℂ) *
                rescaledCenteredVelocity n e t‖) := by
          exact add_le_add (le_refl _) (norm_add_le _ _)
        _ = _ := by
          simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          ring
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hvalueBound : ‖rescaledCenteredEval n e t‖ ≤ u / n := by
      simpa [hvalue] using hsmall
    have hheightScaled : (n : ℝ) * globalAccelerationBound n *
        localMeshHalfWidth n ^ 2 < 1 := by
      simpa [minimumTransferHeight] using hheight
    have hmesh := n_mul_localMeshHalfWidth_le_pi n
    have hproduct : |localMeshPoint n a - t| *
        ‖rescaledCenteredVelocity n e t‖ ≤
        localMeshHalfWidth n * (2 * L) :=
      mul_le_mul hdiff htVelBound (norm_nonneg _) hhalf0
    have hbase : ‖rescaledCenteredEval n e (localMeshPoint n a)‖ ≤
        globalAccelerationBound n * localMeshHalfWidth n ^ 2 +
          u / n + localMeshHalfWidth n * (2 * L) :=
      htri.trans (add_le_add (add_le_add hTaylorBound hvalueBound) hproduct)
    apply (le_div_iff₀ hnR).2
    exact (calc
      ‖rescaledCenteredEval n e (localMeshPoint n a)‖ * n ≤
          (globalAccelerationBound n * localMeshHalfWidth n ^ 2 +
            u / n + localMeshHalfWidth n * (2 * L)) * n :=
        mul_le_mul_of_nonneg_right hbase hnR.le
      _ < u + 1 + 2 * Real.pi * L := by
        have hlin : (n : ℝ) * localMeshHalfWidth n * (2 * L) ≤
            Real.pi * (2 * L) :=
          mul_le_mul_of_nonneg_right hmesh (mul_nonneg (by norm_num) hL.le)
        field_simp [hnR.ne']
        nlinarith).le
  exact ⟨a, haHalf, hnearest, hspread,
    oneBlockProductRegion_of_eval_velocity n e (localMeshPoint n a)
      ((u + 1 + 2 * Real.pi * L) / n) (2 * L) hposSite hvelSite⟩

def HasBoundedLowVelocityMeshWitness
    (n : ℕ) (u L : ℝ) (e : SignVector (2 * n)) : Prop :=
  ∃ a : Fin (localMeshSize n),
    IsSmooth n (rigiditySmoothScale n) (localMeshPoint n a) ∧
    IsSpread n (rigiditySmoothScale n)
      (fun _ : Fin 1 ↦ localMeshPoint n a) ∧
    normalizedPhaseEuclideanWalk n e
        (fun _ : Fin 1 ↦ localMeshPoint n a) ∈
      oneBlockProductRegion ((u + 1 + 2 * Real.pi * L) / n) (2 * L)

lemma lowVelocitySmallMinimum_subset_meshWitness_or_highAcceleration
    (n : ℕ) (hn : 0 < n) (u L : ℝ)
    (hwidth : 2 * localMeshHalfWidth n <
      Real.pi * (2 * rigiditySmoothScale n))
    (hheight : minimumTransferHeight n 0 < 1)
    (hvelocityError : minimumVelocityTransferError n < L / 2)
    (e : SignVector (2 * n))
    (hlow : HasLowVelocitySmallMinimum n u L e) :
    HasBoundedLowVelocityMeshWitness n u L e ∨
      HasHighMeshAcceleration n e := by
  by_cases hacc : HasHighMeshAcceleration n e
  · exact Or.inr hacc
  · left
    rcases lowVelocitySmallMinimum_good_has_bounded_mesh_site n hn u L
        hwidth hheight hvelocityError e hlow hacc with
      ⟨a, _haHalf, haSmooth, haSpread, haRegion⟩
    exact ⟨a, haSmooth, haSpread, haRegion⟩

theorem eventually_lowVelocitySmallMinimum_probability_le
    (u L : ℝ) (hu : 0 ≤ u) (hL : 0 < L) :
    ∀ᶠ n : ℕ in atTop,
      uniformProbability (HasLowVelocitySmallMinimum n u L) ≤
        256 * Real.pi ^ 2 * (u + 1 + 2 * Real.pi * L) ^ 2 *
            (2 * L) ^ 2 +
          uniformProbability (HasHighMeshAcceleration n) := by
  let A := u + 1 + 2 * Real.pi * L
  let B := 2 * L
  have hA : 0 < A := by
    dsimp [A]
    nlinarith [Real.pi_pos]
  have hB : 0 < B := by
    dsimp [B]
    linarith
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
  let P : Fin (localMeshSize n) → SignVector (2 * n) → Prop :=
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
    by_cases hsmooth :
        IsSmooth n (rigiditySmoothScale n) (localMeshPoint n a)
    · by_cases hspread : IsSpread n (rigiditySmoothScale n)
          (fun _ : Fin 1 ↦ localMeshPoint n a)
      · apply (le_div_iff₀ hmeshPos).2
        have hmono : uniformProbability (P a) ≤
            uniformProbability (fun e : SignVector (2 * n) ↦
              normalizedPhaseEuclideanWalk n e
                  (fun _ : Fin 1 ↦ localMeshPoint n a) ∈
                oneBlockProductRegion (A / n) B) := by
          apply uniformProbability_mono
          intro e he
          exact he.2.2
        calc
          uniformProbability (P a) * (localMeshSize n : ℝ) ≤
              (localMeshSize n : ℝ) *
                uniformProbability (fun e : SignVector (2 * n) ↦
                  normalizedPhaseEuclideanWalk n e
                      (fun _ : Fin 1 ↦ localMeshPoint n a) ∈
                    oneBlockProductRegion (A / n) B) := by
            rw [mul_comm]
            exact mul_le_mul_of_nonneg_left hmono hmeshPos.le
          _ ≤ 256 * Real.pi ^ 2 * A ^ 2 * B ^ 2 :=
            hboxN (localMeshPoint n a) hsmooth hspread
      · have hempty : ∀ e : SignVector (2 * n), ¬P a e := by
          intro e he
          exact hspread he.2.1
        have hzero : uniformProbability (P a) = 0 := by
          unfold uniformProbability
          simp [Finset.filter_eq_empty_iff, hempty]
        rw [hzero]
        positivity
    · have hempty : ∀ e : SignVector (2 * n), ¬P a e := by
        intro e he
        exact hsmooth he.1
      have hzero : uniformProbability (P a) = 0 := by
        unfold uniformProbability
        simp [Finset.filter_eq_empty_iff, hempty]
      rw [hzero]
      positivity
  have hwitness : uniformProbability
      (HasBoundedLowVelocityMeshWitness n u L) ≤
      256 * Real.pi ^ 2 * A ^ 2 * B ^ 2 := by
    have hexists : uniformProbability (fun e : SignVector (2 * n) ↦
        ∃ a, P a e) ≤ ∑ a, uniformProbability (P a) :=
      uniformProbability_exists_le_sum P
    calc
      uniformProbability (HasBoundedLowVelocityMeshWitness n u L) =
          uniformProbability (fun e : SignVector (2 * n) ↦ ∃ a, P a e) := by
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
        uniformProbability (fun e : SignVector (2 * n) ↦
          HasBoundedLowVelocityMeshWitness n u L e ∨
            HasHighMeshAcceleration n e) := by
      apply uniformProbability_mono
      exact lowVelocitySmallMinimum_subset_meshWitness_or_highAcceleration
        n hn u L hwidth hheightN hvelocityN
    _ ≤ uniformProbability (HasBoundedLowVelocityMeshWitness n u L) +
          uniformProbability (HasHighMeshAcceleration n) :=
      uniformProbability_or_le_add _ _
    _ ≤ 256 * Real.pi ^ 2 * A ^ 2 * B ^ 2 +
          uniformProbability (HasHighMeshAcceleration n) := by gcongr
    _ = 256 * Real.pi ^ 2 * (u + 1 + 2 * Real.pi * L) ^ 2 *
            (2 * L) ^ 2 +
          uniformProbability (HasHighMeshAcceleration n) := by
      rfl

def HasHighMeshVelocity (n : ℕ) (T : ℝ)
    (e : SignVector (2 * n)) : Prop :=
  ∃ a : Fin (localMeshSize n),
    T ≤ ‖rescaledCenteredVelocity n e (localMeshPoint n a)‖

lemma normalized_phaseStep_variance_le_one
    (n : ℕ) (points : Fin m → ℝ) (r : Fin m) (c : Fin 4) :
    ∑ j : Fin (2 * n + 1),
        (phaseStep n points j r c / Real.sqrt (2 * n + 1 : ℝ)) ^ 2 ≤ 1 := by
  have hcount : (0 : ℝ) < 2 * n + 1 := by positivity
  have hsqrtSq : Real.sqrt (2 * n + 1 : ℝ) ^ 2 = 2 * n + 1 :=
    Real.sq_sqrt hcount.le
  simp_rw [div_pow, hsqrtSq]
  rw [← Finset.sum_div]
  rw [div_le_one hcount]
  exact phaseStep_variance_le_count n points r c

lemma uniformProbability_rescaledCenteredVelocity_norm_ge
    (n : ℕ) (t T : ℝ) (hT : 0 < T) :
    uniformProbability (fun e : SignVector (2 * n) ↦
        T ≤ ‖rescaledCenteredVelocity n e t‖) ≤
      4 * Real.exp (-(T / 2) ^ 2 / 2) := by
  let points : Fin 1 → ℝ := fun _ ↦ t
  let aRe : Fin (2 * n + 1) → ℝ := fun j ↦
    phaseStep n points j 0 2 / Real.sqrt (2 * n + 1 : ℝ)
  let aIm : Fin (2 * n + 1) → ℝ := fun j ↦
    phaseStep n points j 0 3 / Real.sqrt (2 * n + 1 : ℝ)
  have hre := rademacherLinear_abs_tail_of_sum_sq_le_one
    (2 * n + 1) aRe (T / 2) (half_pos hT)
      (normalized_phaseStep_variance_le_one n points 0 2)
  have him := rademacherLinear_abs_tail_of_sum_sq_le_one
    (2 * n + 1) aIm (T / 2) (half_pos hT)
      (normalized_phaseStep_variance_le_one n points 0 3)
  have hreEq : ∀ e : SignVector (2 * n),
      ∑ j, aRe j * sign (e j) =
        (rescaledCenteredVelocity n e t).re := by
    intro e
    rw [← phaseWalk_velocity_re n e points 0]
    simp only [aRe, points, phaseWalk]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  have himEq : ∀ e : SignVector (2 * n),
      ∑ j, aIm j * sign (e j) =
        (rescaledCenteredVelocity n e t).im := by
    intro e
    rw [← phaseWalk_velocity_im n e points 0]
    simp only [aIm, points, phaseWalk]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  calc
    uniformProbability (fun e : SignVector (2 * n) ↦
        T ≤ ‖rescaledCenteredVelocity n e t‖) ≤
        uniformProbability (fun e : SignVector (2 * n) ↦
          T / 2 ≤ |(rescaledCenteredVelocity n e t).re| ∨
          T / 2 ≤ |(rescaledCenteredVelocity n e t).im|) := by
      apply uniformProbability_mono
      intro e he
      by_contra hboth
      push Not at hboth
      have hnorm := Complex.norm_le_abs_re_add_abs_im
        (rescaledCenteredVelocity n e t)
      linarith
    _ ≤ uniformProbability (fun e : SignVector (2 * n) ↦
          T / 2 ≤ |(rescaledCenteredVelocity n e t).re|) +
        uniformProbability (fun e : SignVector (2 * n) ↦
          T / 2 ≤ |(rescaledCenteredVelocity n e t).im|) :=
      uniformProbability_or_le_add _ _
    _ ≤ 2 * Real.exp (-(T / 2) ^ 2 / 2) +
        2 * Real.exp (-(T / 2) ^ 2 / 2) := by
      apply add_le_add
      · simpa only [hreEq] using hre
      · simpa only [himEq] using him
    _ = 4 * Real.exp (-(T / 2) ^ 2 / 2) := by ring

lemma uniformProbability_highMeshVelocity_le
    (n : ℕ) (T : ℝ) (hT : 0 < T) :
    uniformProbability (HasHighMeshVelocity n T) ≤
      (localMeshSize n : ℝ) *
        (4 * Real.exp (-(T / 2) ^ 2 / 2)) := by
  calc
    uniformProbability (HasHighMeshVelocity n T) ≤
        ∑ a : Fin (localMeshSize n),
          uniformProbability (fun e : SignVector (2 * n) ↦
            T ≤ ‖rescaledCenteredVelocity n e (localMeshPoint n a)‖) := by
      exact uniformProbability_exists_le_sum _
    _ ≤ ∑ _a : Fin (localMeshSize n),
        4 * Real.exp (-(T / 2) ^ 2 / 2) := by
      exact Finset.sum_le_sum fun a _ha ↦
        uniformProbability_rescaledCenteredVelocity_norm_ge n
          (localMeshPoint n a) T hT
    _ = (localMeshSize n : ℝ) *
        (4 * Real.exp (-(T / 2) ^ 2 / 2)) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      simp only [nsmul_eq_mul]

theorem uniformProbability_highMeshVelocity_at_accelerationCutoff_tendsto_zero :
    Tendsto (fun n : ℕ ↦
      uniformProbability (HasHighMeshVelocity n (accelerationCutoff n)))
      atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun n ↦ uniformProbability_nonneg _)
  · filter_upwards [Nat.eventually_pos] with n hn
    exact uniformProbability_highMeshVelocity_le n (accelerationCutoff n)
      (by unfold accelerationCutoff; exact rigidityPower_pos hn _)
  · exact highMeshAcceleration_upper_tendsto_zero

end Erdos525
