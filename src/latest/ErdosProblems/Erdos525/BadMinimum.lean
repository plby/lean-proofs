import ErdosProblems.Erdos525.BadProbability

open scoped BigOperators Topology ComplexConjugate RealInnerProductSpace

namespace Erdos525

open Classical Filter Finset Set MeasureTheory

lemma eventually_endpointShellUpper_48_gt_eleven :
    ∀ᶠ n : ℕ in atTop, 11 < endpointShellUpper n 48 := by
  have h := (tendsto_rigidityPower_atTop
    (show (0 : ℝ) < 1 / 128 by norm_num)).eventually (eventually_gt_atTop 11)
  filter_upwards [h] with n hn
  norm_num [endpointShellUpper] at hn ⊢
  exact hn

lemma eventually_badArcCoarseWidth_lt_one :
    ∀ᶠ n : ℕ in atTop, badArcCoarseWidth n < 1 := by
  have h := (tendsto_rigidityPower_neg_zero
    (show (0 : ℝ) < 1 / 4 by norm_num)).eventually
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [h] with n hn
  change rigidityPower n (-1 / 4) < 1
  rw [show (-1 / 4 : ℝ) = -(1 / 4) by norm_num]
  exact hn

lemma eventually_badArcSmallMinimum_subset_coverExceptions (u : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ e : SignVector (2 * n),
      HasBadArcSmallMinimum n u e →
        HasLeftEndpointCoverWitness n u e ∨
          HasRightEndpointCoverWitness n u e ∨
          HasInteriorCoverWitness n u e ∨
          HasHighMeshAcceleration n e ∨
          HasHighMeshVelocity n (growingVelocityCutoff n) e := by
  filter_upwards [Nat.eventually_pos,
      eventually_small_value_away_from_endpoints u,
      eventually_global_velocity_le_two_growing,
      eventually_endpointShellUpper_48_gt_eleven,
      eventually_badArcCoarseWidth_lt_one] with
      n hn hawayN hglobalN hshell hwidth e hbad
  by_cases hacc : HasHighMeshAcceleration n e
  · exact Or.inr (Or.inr (Or.inr (Or.inl hacc)))
  by_cases hmesh : HasHighMeshVelocity n (growingVelocityCutoff n) e
  · exact Or.inr (Or.inr (Or.inr (Or.inr hmesh)))
  rcases hbad with ⟨t, ht, hvalue, hsmall, hnonsmooth⟩
  have hsmallEval : ‖rescaledCenteredEval n e t‖ ≤ u / n := by
    rw [hvalue]
    exact hsmall
  have haway := hawayN e hacc t ht hsmallEval
  have hglobal := hglobalN e hacc hmesh
  have htop : t < Real.pi * n := by
    have hrpos : 0 < endpointExclusionRadius n := by
      unfold endpointExclusionRadius
      exact rigidityPower_pos hn _
    linarith [haway.2]
  by_cases hleft : t ≤ 11
  · rcases exists_endpointCover_point hn haway.1.le (hleft.trans_lt hshell) with
      ⟨ℓ, hℓ, b, hb, hqt, hdist, hql⟩
    have hq0 : 0 ≤ endpointShellPoint n ℓ b :=
      (endpointShellLower_pos hn ℓ).le.trans hql
    have hqIcc : endpointShellPoint n ℓ b ∈ Set.Icc (0 : ℝ) 11 :=
      ⟨hq0, hqt.trans hleft⟩
    have htransfer := small_value_transfers_to_left_cover_point
      hn e hacc hmesh hglobal u t (endpointShellPoint n ℓ b)
      (endpointShellStep n ℓ) ht hq0 hqt htop hdist
      (endpointShellStep_pos hn ℓ).le hsmallEval
    exact Or.inl ⟨⟨ℓ, hℓ⟩, ⟨b, hb⟩, hqIcc, by
      simpa [endpointCoverDelta] using htransfer⟩
  have hleftFar : 11 < t := lt_of_not_ge hleft
  let d : ℝ := Real.pi * n - t
  by_cases hright : d ≤ 11
  · rcases exists_endpointCover_point hn haway.2.le (hright.trans_lt hshell) with
      ⟨ℓ, hℓ, b, hb, hqd, hdist, hql⟩
    let qd : ℝ := endpointShellPoint n ℓ b
    let q : ℝ := Real.pi * n - qd
    have hqd0 : 0 ≤ qd := (endpointShellLower_pos hn ℓ).le.trans hql
    have hqdIcc : qd ∈ Set.Icc (0 : ℝ) 11 :=
      ⟨hqd0, hqd.trans hright⟩
    have htq : t ≤ q := by
      dsimp [q, qd, d] at *
      linarith
    have hqtop : q < Real.pi * n := by
      have hqdpos : 0 < qd := (endpointShellLower_pos hn ℓ).trans_le hql
      dsimp [q]
      linarith
    have hqdist : q - t < endpointShellStep n ℓ := by
      dsimp [q, qd, d] at *
      linarith
    have htransfer := small_value_transfers_to_right_cover_point
      hn e hacc hmesh hglobal u t q (endpointShellStep n ℓ) ht htq hqtop
      hqdist (endpointShellStep_pos hn ℓ).le hsmallEval
    exact Or.inr (Or.inl ⟨⟨ℓ, hℓ⟩, ⟨b, hb⟩, hqdIcc, by
      simpa [q, qd, endpointCoverDelta] using htransfer⟩)
  have hrightFar : 11 < d := lt_of_not_ge hright
  rcases nonsmooth_has_nearby_interiorArcPoint hn ht hnonsmooth with
    ⟨q, hqmem, hqt, hdist⟩
  have hqLower : 10 ≤ q := by
    have hdistOne : t - q < 1 := hdist.trans hwidth
    linarith
  have hqUpper : q ≤ Real.pi * n - 10 := by
    dsimp [d] at hrightFar
    linarith
  have hqIcc : q ∈ Set.Icc (10 : ℝ) (Real.pi * n - 10) :=
    ⟨hqLower, hqUpper⟩
  have htransfer := small_value_transfers_to_left_cover_point
    hn e hacc hmesh hglobal u t q (badArcCoarseWidth n) ht
    (by linarith : 0 ≤ q) hqt htop hdist (badArcCoarseWidth_pos hn).le
    hsmallEval
  exact Or.inr (Or.inr (Or.inl ⟨⟨q, hqmem⟩, hqIcc, by
    simpa [interiorCoverDelta] using htransfer⟩))

theorem eventually_uniformProbability_badArcSmallMinimum_le_coverExceptions
    (u : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      uniformProbability (HasBadArcSmallMinimum n u) ≤
        uniformProbability (HasLeftEndpointCoverWitness n u) +
          uniformProbability (HasRightEndpointCoverWitness n u) +
          uniformProbability (HasInteriorCoverWitness n u) +
          uniformProbability (HasHighMeshAcceleration n) +
          uniformProbability
            (HasHighMeshVelocity n (growingVelocityCutoff n)) := by
  filter_upwards [eventually_badArcSmallMinimum_subset_coverExceptions u] with
      n hsubset
  let A : SignVector (2 * n) → Prop := HasLeftEndpointCoverWitness n u
  let B : SignVector (2 * n) → Prop := HasRightEndpointCoverWitness n u
  let C : SignVector (2 * n) → Prop := HasInteriorCoverWitness n u
  let D : SignVector (2 * n) → Prop := HasHighMeshAcceleration n
  let E : SignVector (2 * n) → Prop :=
    HasHighMeshVelocity n (growingVelocityCutoff n)
  have hmono : uniformProbability (HasBadArcSmallMinimum n u) ≤
      uniformProbability (fun e ↦ A e ∨ B e ∨ C e ∨ D e ∨ E e) := by
    apply uniformProbability_mono
    intro e he
    simpa only [A, B, C, D, E] using hsubset e he
  calc
    uniformProbability (HasBadArcSmallMinimum n u) ≤
        uniformProbability (fun e ↦ A e ∨ B e ∨ C e ∨ D e ∨ E e) := hmono
    _ ≤ uniformProbability A +
        uniformProbability (fun e ↦ B e ∨ C e ∨ D e ∨ E e) :=
      uniformProbability_or_le_add _ _
    _ ≤ uniformProbability A + (uniformProbability B +
        uniformProbability (fun e ↦ C e ∨ D e ∨ E e)) := by
      gcongr
      exact uniformProbability_or_le_add _ _
    _ ≤ uniformProbability A + (uniformProbability B +
        (uniformProbability C + uniformProbability (fun e ↦ D e ∨ E e))) := by
      gcongr
      exact uniformProbability_or_le_add _ _
    _ ≤ uniformProbability A + (uniformProbability B +
        (uniformProbability C + (uniformProbability D + uniformProbability E))) := by
      gcongr
      exact uniformProbability_or_le_add _ _
    _ = uniformProbability (HasLeftEndpointCoverWitness n u) +
          uniformProbability (HasRightEndpointCoverWitness n u) +
          uniformProbability (HasInteriorCoverWitness n u) +
          uniformProbability (HasHighMeshAcceleration n) +
          uniformProbability
            (HasHighMeshVelocity n (growingVelocityCutoff n)) := by
      simp only [A, B, C, D, E]
      ring

theorem uniformProbability_badArcSmallMinimum_tendsto_zero
    (u : ℝ) (hu : 0 < u) :
    Tendsto (fun n : ℕ ↦ uniformProbability (HasBadArcSmallMinimum n u))
      atTop (𝓝 0) := by
  have hsum := (((uniformProbability_leftEndpointCoverWitness_tendsto_zero u hu).add
      (uniformProbability_rightEndpointCoverWitness_tendsto_zero u hu)).add
      (uniformProbability_interiorCoverWitness_tendsto_zero u hu)).add
      uniformProbability_highMeshAcceleration_tendsto_zero |>.add
      uniformProbability_highMeshVelocity_growing_tendsto_zero
  have hsum' : Tendsto (fun n : ℕ ↦
      uniformProbability (HasLeftEndpointCoverWitness n u) +
        uniformProbability (HasRightEndpointCoverWitness n u) +
        uniformProbability (HasInteriorCoverWitness n u) +
        uniformProbability (HasHighMeshAcceleration n) +
        uniformProbability (HasHighMeshVelocity n (growingVelocityCutoff n)))
      atTop (𝓝 0) := by simpa using hsum
  apply squeeze_zero' (Eventually.of_forall fun n ↦ uniformProbability_nonneg _)
  · exact eventually_uniformProbability_badArcSmallMinimum_le_coverExceptions u
  · exact hsum'

end Erdos525
