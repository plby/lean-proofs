import ErdosProblems.Erdos525.OddHighVelocity

open scoped BigOperators ENNReal NNReal Topology Real ComplexConjugate
open MeasureTheory Filter Set

namespace Erdos525

open Classical Finset

namespace Odd

def HasHighVelocitySmallMinimum
    (n : ℕ) (u V : ℝ) (e : SignVector (2 * n + 1)) : Prop :=
  ∃ t ∈ Set.Icc (0 : ℝ) (Real.pi * n),
    ‖eval n e t‖ = oddCenteredMin n e ∧
    oddCenteredMin n e ≤ u / n ∧
    IsSmooth n (4 * rigiditySmoothScale n) t ∧
    V < ‖velocity n e t‖

def HasHighVelocityMeshWitness
    (n : ℕ) (u V : ℝ) (e : SignVector (2 * n + 1)) : Prop :=
  ∃ a : Fin (localMeshSize n),
    a ∈ halfLocalMeshSites n ∧
    IsSmooth n (rigiditySmoothScale n) (localMeshPoint n a) ∧
    IsSpread n (rigiditySmoothScale n)
      (fun _ : Fin 1 ↦ localMeshPoint n a) ∧
    IsFactoredTruncatedLocalRepresentative n 2 (u + 1)
      (V / 2) (2 * growingVelocityCutoff n) e a

lemma factoredTruncatedLocalProbability_eq_phase_one
    (n : ℕ) (hn : 0 < n)
    (widthFactor u velocityLower velocityUpper : ℝ)
    (hvelLower : 0 < velocityLower)
    (a : Fin (localMeshSize n)) :
    uniformProbability (fun e : SignVector (2 * n + 1) ↦
        IsFactoredTruncatedLocalRepresentative n widthFactor u
          velocityLower velocityUpper e a) =
      factoredTruncatedPhaseProbability 1 n
        (fun _ : Fin 1 ↦ localMeshPoint n a)
        widthFactor u velocityLower velocityUpper := by
  unfold factoredTruncatedPhaseProbability
  apply congrArg uniformProbability
  funext e
  apply propext
  rw [truncatedPhaseRegion]
  change IsFactoredTruncatedLocalRepresentative n widthFactor u
      velocityLower velocityUpper e a ↔
    phaseToBlocks (normalizedPhaseEuclideanWalk n e
      (fun _ : Fin 1 ↦ localMeshPoint n a)) ∈
      Set.univ.pi (fun _ : Fin 1 ↦
        truncatedBlockSet n u (widthFactor * localMeshHalfWidth n)
          velocityLower velocityUpper)
  constructor
  · intro ha r _hr
    have hr0 : r = 0 := Subsingleton.elim _ _
    subst r
    rw [truncatedBlockSet,
      mem_truncatedBlockRegion_iff n u
        (widthFactor * localMeshHalfWidth n)
        velocityLower velocityUpper hvelLower]
    rw [phaseToBlocks_normalizedPhaseEuclideanWalk]
    rw [← phasePosition_normalizedPhaseWalk n e
      (fun _ : Fin 1 ↦ localMeshPoint n a) 0,
      ← phaseVelocity_normalizedPhaseWalk n e
        (fun _ : Fin 1 ↦ localMeshPoint n a) 0]
    rw [isTruncatedBlockRepresentative_iff_phase
      (m := 1) n hn u (widthFactor * localMeshHalfWidth n)
        velocityLower velocityUpper]
    rw [isPhaseRepresentative_normalized_iff]
    rw [phaseVelocity_normalizedPhaseWalk]
    exact ⟨⟨ha.1, ha.2.1, ha.2.2.1⟩, ha.2.2.2.1, ha.2.2.2.2⟩
  · intro h
    have hr := h (0 : Fin 1) (Set.mem_univ _)
    rw [truncatedBlockSet,
      mem_truncatedBlockRegion_iff n u
        (widthFactor * localMeshHalfWidth n)
        velocityLower velocityUpper hvelLower] at hr
    rw [phaseToBlocks_normalizedPhaseEuclideanWalk] at hr
    rw [← phasePosition_normalizedPhaseWalk n e
      (fun _ : Fin 1 ↦ localMeshPoint n a) 0,
      ← phaseVelocity_normalizedPhaseWalk n e
        (fun _ : Fin 1 ↦ localMeshPoint n a) 0] at hr
    rw [isTruncatedBlockRepresentative_iff_phase
      (m := 1) n hn u (widthFactor * localMeshHalfWidth n)
        velocityLower velocityUpper] at hr
    rw [isPhaseRepresentative_normalized_iff,
      phaseVelocity_normalizedPhaseWalk] at hr
    exact ⟨hr.1.1, hr.1.2.1, hr.1.2.2, hr.2.1, hr.2.2⟩

theorem eventually_highVelocitySmallMinimum_subset_witness_or_highMesh
    (u V : ℝ) (hV : 0 < V) :
    ∀ᶠ n : ℕ in atTop, ∀ e : SignVector (2 * n + 1),
      HasHighVelocitySmallMinimum n u V e →
        HasHighVelocityMeshWitness n u V e ∨
        HasHighMeshVelocity n (growingVelocityCutoff n) e := by
  have hwidthDynamic : ∀ᶠ n : ℕ in atTop,
      minimumTransferWidthFactor n u (V / 2)
          (2 * growingVelocityCutoff n) < 2 :=
    (highVelocity_fixedLower_minimumTransferWidthFactor_tendsto_one u V hV).eventually
      (Iio_mem_nhds (by norm_num))
  have hheightDynamic : ∀ᶠ n : ℕ in atTop,
      minimumTransferHeight n u < u + 1 :=
    (minimumTransferHeight_tendsto u).eventually
      (Iio_mem_nhds (by linarith))
  have hvelocityError : ∀ᶠ n : ℕ in atTop,
      2 * minimumVelocityTransferError n < V := by
    have hleft := minimumVelocityTransferError_tendsto_zero.const_mul 2
    have hleft' : Tendsto (fun n : ℕ ↦
        2 * minimumVelocityTransferError n) atTop (𝓝 0) := by
      simpa using hleft
    exact hleft'.eventually (Iio_mem_nhds hV)
  filter_upwards [Nat.eventually_pos,
      eventually_two_halfWidth_lt_pi_mul_rigiditySmoothScale,
      eventually_nearest_halfLocalMeshSite_smooth,
      hwidthDynamic, hheightDynamic, hvelocityError]
    with n hn hcell hnearest hwidthN hheightN hvelocityN
  intro e hhigh
  by_cases hmesh : HasHighMeshVelocity n (growingVelocityCutoff n) e
  · exact Or.inr hmesh
  left
  rcases hhigh with ⟨t, ht, hvalue, hsmall, htSmooth, htVelocity⟩
  have htSmoothTwo : IsSmooth n (2 * rigiditySmoothScale n) t := by
    intro p hp1 hpFloor
    have hscale : 0 ≤ rigiditySmoothScale n := by
      unfold rigiditySmoothScale
      exact rigidityPower_nonneg n _
    have hpBound : p ≤ Nat.floor (4 * rigiditySmoothScale n) + 1 :=
      hpFloor.trans (Nat.add_le_add_right
        (Nat.floor_mono (by linarith)) 1)
    have hstrong := htSmooth p hp1 hpBound
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    exact (div_le_div_of_nonneg_right (by linarith) hnR.le).trans_lt hstrong
  rcases exists_halfLocalMeshSite_within_halfWidth n hn
      (2 * rigiditySmoothScale n) t hcell htSmoothTwo ht with
    ⟨a, haHalf, haNear⟩
  have haSmooth := hnearest t htSmoothTwo a haNear
  have haSpread := singleton_spread_of_near_four_smooth
    n hn t ht htSmooth a haHalf haNear hcell
  have hvelDiff := abs_norm_velocity_sub_le_of_near n e t a haNear
  rw [abs_le] at hvelDiff
  have hsiteNotHigh : ¬ growingVelocityCutoff n ≤
      ‖velocity n e (localMeshPoint n a)‖ := by
    intro ha
    exact hmesh ⟨a, ha⟩
  have haLower : V / 2 ≤
      ‖velocity n e (localMeshPoint n a)‖ := by
    have hsiteLower :
        ‖velocity n e t‖ - minimumVelocityTransferError n ≤
          ‖velocity n e (localMeshPoint n a)‖ := by
      linarith [hvelDiff.1]
    have hstrict : V / 2 <
        ‖velocity n e t‖ - minimumVelocityTransferError n := by
      linarith
    exact hstrict.le.trans hsiteLower
  have haUpper :
      ‖velocity n e (localMeshPoint n a)‖ ≤
        2 * growingVelocityCutoff n := by
    have hsite := lt_of_not_ge hsiteNotHigh
    have hcut0 := growingVelocityCutoff_nonneg n
    linarith
  have hortho : (eval n e t * conj (velocity n e t)).re = 0 := by
    have hlocal : IsLocalMin (energy n e) t := by
      change ∀ᶠ s in 𝓝 t, energy n e t ≤ energy n e s
      exact Eventually.of_forall fun s ↦ by
        have hle := oddCenteredMin_le_eval n hn e s
        have hnonneg : 0 ≤ oddCenteredMin n e := by
          rw [← hvalue]
          exact norm_nonneg _
        unfold energy
        rw [hvalue]
        exact pow_le_pow_left₀ hnonneg hle 2
    have hzero : deriv (energy n e) t = 0 := hlocal.deriv_eq_zero
    have hderiv := (hasDerivAt_energy n e t).deriv
    rw [hzero] at hderiv
    linarith
  have hrep := isFactoredTruncatedLocalRepresentative_of_minimizer
    n hn e u (V / 2) (2 * growingVelocityCutoff n) t
      (by simpa [hvalue] using hsmall) hortho a haNear
      (half_pos hV) haLower haUpper
  refine ⟨a, haHalf, haSmooth, haSpread, ?_⟩
  refine ⟨hrep.1, ?_, ?_, hrep.2.2.2.1, hrep.2.2.2.2⟩
  · exact hrep.2.1.trans (mul_le_mul_of_nonneg_right hwidthN.le
      (by unfold localMeshHalfWidth; positivity))
  · exact hrep.2.2.1.trans hheightN.le

theorem eventually_highVelocityMeshWitness_probability_le
    (u V : ℝ) (hu : 0 ≤ u) (hV : 0 < V) :
    ∀ᶠ n : ℕ in atTop,
      uniformProbability (HasHighVelocityMeshWitness n u V) ≤
        (72 / Real.pi) * (u + 2) * blockVelocityTailMass (V / 4) +
          648 * Real.pi ^ 2 * (u + 2) * growingVelocityCutoff n ^ 3 *
            quantitativePhaseDensityError n := by
  filter_upwards [Nat.eventually_pos,
      eventually_uniform_scaled_highVelocityPhaseProbability_upper u V hu hV]
    with n hn hphase
  let B : ℝ :=
    (72 / Real.pi) * (u + 2) * blockVelocityTailMass (V / 4) +
      648 * Real.pi ^ 2 * (u + 2) * growingVelocityCutoff n ^ 3 *
        quantitativePhaseDensityError n
  have hB : 0 ≤ B := by
    have htail0 := blockVelocityTailMass_nonneg (V / 4)
    have herr0 := quantitativePhaseDensityError_nonneg n
    have hcut0 := growingVelocityCutoff_nonneg n
    dsimp [B]
    positivity
  let P : Fin (localMeshSize n) → SignVector (2 * n + 1) → Prop := fun a e ↦
    a ∈ halfLocalMeshSites n ∧
    IsSmooth n (rigiditySmoothScale n) (localMeshPoint n a) ∧
    IsSpread n (rigiditySmoothScale n)
      (fun _ : Fin 1 ↦ localMeshPoint n a) ∧
    IsFactoredTruncatedLocalRepresentative n 2 (u + 1)
      (V / 2) (2 * growingVelocityCutoff n) e a
  have hmeshPos : (0 : ℝ) < localMeshSize n := by
    exact_mod_cast localMeshSize_pos n
  have hsite : ∀ a : Fin (localMeshSize n),
      uniformProbability (P a) ≤ B / localMeshSize n := by
    intro a
    by_cases haHalf : a ∈ halfLocalMeshSites n
    · by_cases hsmooth :
        IsSmooth n (rigiditySmoothScale n) (localMeshPoint n a)
      · by_cases hspread : IsSpread n (rigiditySmoothScale n)
          (fun _ : Fin 1 ↦ localMeshPoint n a)
        · apply (le_div_iff₀ hmeshPos).2
          have hmono : uniformProbability (P a) ≤
              uniformProbability (fun e : SignVector (2 * n + 1) ↦
                IsFactoredTruncatedLocalRepresentative n 2 (u + 1)
                  (V / 2) (2 * growingVelocityCutoff n) e a) := by
            apply uniformProbability_mono
            intro e he
            exact he.2.2.2
          have heq := factoredTruncatedLocalProbability_eq_phase_one
            n hn 2 (u + 1) (V / 2) (2 * growingVelocityCutoff n)
              (half_pos hV) a
          have hrep : (localMeshSize n : ℝ) *
              uniformProbability (fun e : SignVector (2 * n + 1) ↦
                IsFactoredTruncatedLocalRepresentative n 2 (u + 1)
                  (V / 2) (2 * growingVelocityCutoff n) e a) ≤ B := by
            rw [heq]
            simpa only [factoredTruncatedPhaseProbability, B] using
              hphase (localMeshPoint n a) hsmooth hspread
          calc
            uniformProbability (P a) * (localMeshSize n : ℝ) ≤
                (localMeshSize n : ℝ) *
                  uniformProbability (fun e : SignVector (2 * n + 1) ↦
                    IsFactoredTruncatedLocalRepresentative n 2 (u + 1)
                      (V / 2) (2 * growingVelocityCutoff n) e a) := by
              rw [mul_comm]
              exact mul_le_mul_of_nonneg_left hmono hmeshPos.le
            _ ≤ B := hrep
        · have hempty : ∀ e : SignVector (2 * n + 1), ¬P a e := by
            intro e he
            exact hspread he.2.2.1
          have hzero : uniformProbability (P a) = 0 := by
            unfold uniformProbability
            simp [Finset.filter_eq_empty_iff, hempty]
          rw [hzero]
          exact div_nonneg hB hmeshPos.le
      · have hempty : ∀ e : SignVector (2 * n + 1), ¬P a e := by
          intro e he
          exact hsmooth he.2.1
        have hzero : uniformProbability (P a) = 0 := by
          unfold uniformProbability
          simp [Finset.filter_eq_empty_iff, hempty]
        rw [hzero]
        exact div_nonneg hB hmeshPos.le
    · have hempty : ∀ e : SignVector (2 * n + 1), ¬P a e := by
        intro e he
        exact haHalf he.1
      have hzero : uniformProbability (P a) = 0 := by
        unfold uniformProbability
        simp [Finset.filter_eq_empty_iff, hempty]
      rw [hzero]
      exact div_nonneg hB hmeshPos.le
  have hexists : uniformProbability (fun e : SignVector (2 * n + 1) ↦
      ∃ a, P a e) ≤ ∑ a, uniformProbability (P a) :=
    uniformProbability_exists_le_sum P
  calc
    uniformProbability (HasHighVelocityMeshWitness n u V) =
        uniformProbability (fun e : SignVector (2 * n + 1) ↦ ∃ a, P a e) := by
      apply congrArg uniformProbability
      funext e
      apply propext
      simp only [HasHighVelocityMeshWitness, P]
    _ ≤ ∑ a, uniformProbability (P a) := hexists
    _ ≤ ∑ _a : Fin (localMeshSize n), B / localMeshSize n := by
      exact Finset.sum_le_sum fun a _ha ↦ hsite a
    _ = B := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      simp only [nsmul_eq_mul]
      field_simp [hmeshPos.ne']
    _ = _ := rfl

theorem eventually_highVelocitySmallMinimum_probability_le
    (u V : ℝ) (hu : 0 ≤ u) (hV : 0 < V) :
    ∀ᶠ n : ℕ in atTop,
      uniformProbability (HasHighVelocitySmallMinimum n u V) ≤
        (72 / Real.pi) * (u + 2) * blockVelocityTailMass (V / 4) +
          648 * Real.pi ^ 2 * (u + 2) * growingVelocityCutoff n ^ 3 *
            quantitativePhaseDensityError n +
          uniformProbability
            (HasHighMeshVelocity n (growingVelocityCutoff n)) := by
  filter_upwards [eventually_highVelocitySmallMinimum_subset_witness_or_highMesh
      u V hV,
    eventually_highVelocityMeshWitness_probability_le u V hu hV]
    with n hsubset hwitness
  let A : SignVector (2 * n + 1) → Prop := HasHighVelocityMeshWitness n u V
  let C : SignVector (2 * n + 1) → Prop :=
    HasHighMeshVelocity n (growingVelocityCutoff n)
  calc
    uniformProbability (HasHighVelocitySmallMinimum n u V) ≤
        uniformProbability (fun e ↦ A e ∨ C e) := by
      apply uniformProbability_mono
      intro e he
      simpa only [A, C] using hsubset e he
    _ ≤ uniformProbability A + uniformProbability C :=
      uniformProbability_or_le_add _ _
    _ ≤ ((72 / Real.pi) * (u + 2) * blockVelocityTailMass (V / 4) +
          648 * Real.pi ^ 2 * (u + 2) * growingVelocityCutoff n ^ 3 *
            quantitativePhaseDensityError n) + uniformProbability C := by gcongr
    _ = _ := by
      simp only [A, C]

theorem highVelocitySmallMinimum_eventually_lt
    (u V b : ℝ) (hu : 0 ≤ u) (hV : 0 < V)
    (hb : (72 / Real.pi) * (u + 2) *
      blockVelocityTailMass (V / 4) < b) :
    ∀ᶠ n : ℕ in atTop,
      uniformProbability (HasHighVelocitySmallMinimum n u V) < b := by
  let C := (72 / Real.pi) * (u + 2) * blockVelocityTailMass (V / 4)
  let E : ℕ → ℝ := fun n ↦
    648 * Real.pi ^ 2 * (u + 2) * growingVelocityCutoff n ^ 3 *
      quantitativePhaseDensityError n
  have hE : Tendsto E atTop (𝓝 0) := by
    have h := growingVelocityCutoff_cube_mul_quantitativePhaseDensityError_tendsto_zero.const_mul
      (648 * Real.pi ^ 2 * (u + 2))
    convert h using 1 <;> simp [E] <;> ring
  have hrem := hE.add uniformProbability_highMeshVelocity_growing_tendsto_zero
  have hrem' : Tendsto (fun n : ℕ ↦
      E n + uniformProbability (HasHighMeshVelocity n (growingVelocityCutoff n)))
      atTop (𝓝 0) := by simpa using hrem
  have hsmall := hrem'.eventually
    (Iio_mem_nhds (show (0 : ℝ) < b - C by dsimp [C]; linarith))
  filter_upwards [eventually_highVelocitySmallMinimum_probability_le u V hu hV,
      hsmall] with n hupper hsmallN
  dsimp [C, E] at hsmallN
  exact hupper.trans_lt (by linarith)

theorem highVelocitySmallMinimum_vanishes_after_cutoff
    (u eps : ℝ) (hu : 0 ≤ u) (heps : 0 < eps) :
    ∃ V : ℝ, 0 < V ∧ ∀ᶠ n : ℕ in atTop,
      uniformProbability (HasHighVelocitySmallMinimum n u V) < eps := by
  let c : ℝ := (72 / Real.pi) * (u + 2)
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have htarget : 0 < eps / c := div_pos heps hc
  have htail := blockVelocityTailMass_tendsto_zero.eventually
    (Iio_mem_nhds htarget)
  rcases (htail.and (eventually_gt_atTop (0 : ℝ))).exists with ⟨L, hLtail, hL⟩
  refine ⟨4 * L, by positivity, ?_⟩
  apply highVelocitySmallMinimum_eventually_lt u (4 * L) eps hu (by positivity)
  have hcTail : c * blockVelocityTailMass L < eps := by
    simpa [mul_comm] using (lt_div_iff₀ hc).mp hLtail
  simpa [c] using hcTail

end Odd

end Erdos525
