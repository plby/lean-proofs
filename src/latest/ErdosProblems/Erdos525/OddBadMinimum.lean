import ErdosProblems.Erdos525.OddEndpoint

open scoped BigOperators Topology ComplexConjugate RealInnerProductSpace

namespace Erdos525

open Classical Filter Finset Set MeasureTheory

namespace Odd

def HasBadArcSmallMinimum (n : ℕ) (u : ℝ)
    (e : SignVector (2 * n + 1)) : Prop :=
  ∃ t ∈ Set.Icc (0 : ℝ) (Real.pi * n),
    ‖eval n e t‖ = oddCenteredMin n e ∧
    oddCenteredMin n e ≤ u / n ∧
    ¬IsSmooth n (4 * rigiditySmoothScale n) t

lemma eventually_global_velocity_le_two_growing :
    ∀ᶠ n : ℕ in atTop, ∀ e : SignVector (2 * n + 1),
      ¬HasHighMeshVelocity n (growingVelocityCutoff n) e →
      ∀ t ∈ Set.Ico (-(Real.pi * n)) (Real.pi * n),
        ‖velocity n e t‖ ≤ 2 * growingVelocityCutoff n := by
  have herr : ∀ᶠ n : ℕ in atTop,
      2 * globalAccelerationBound n * localMeshHalfWidth n < 1 := by
    have h := globalAccelerationBound_mul_halfWidth_tendsto_zero.const_mul 2
    have h' : Tendsto (fun n : ℕ ↦
        2 * globalAccelerationBound n * localMeshHalfWidth n)
        atTop (𝓝 0) := by
      convert h using 1 <;> ring
    exact h'.eventually (Iio_mem_nhds (by norm_num))
  have hcut : ∀ᶠ n : ℕ in atTop, 1 < growingVelocityCutoff n :=
    growingVelocityCutoff_tendsto_atTop.eventually (eventually_gt_atTop 1)
  filter_upwards [Nat.eventually_pos, herr, hcut] with n hn herrN hcutN
  intro e hvel t ht
  rcases exists_localMeshPoint_within_step n hn t ht with
    ⟨a, hdiff0, hdiff⟩
  have ha : ‖velocity n e (localMeshPoint n a)‖ < growingVelocityCutoff n := by
    exact lt_of_not_ge fun hge ↦ hvel ⟨a, hge⟩
  have hsub := norm_velocity_sub_le n e (localMeshPoint n a) t
  have hsub' : ‖velocity n e t - velocity n e (localMeshPoint n a)‖ < 1 := by
    calc
      _ ≤ globalAccelerationBound n * |t - localMeshPoint n a| := hsub
      _ < globalAccelerationBound n * (2 * localMeshHalfWidth n) := by
        rw [abs_of_nonneg hdiff0]
        exact mul_lt_mul_of_pos_left hdiff
          ((globalAccelerationBound_nonneg n).lt_of_ne' (by
            intro hzero
            have hroot : 0 < Real.sqrt (2 * n + 1 : ℝ) := by positivity
            unfold globalAccelerationBound at hzero
            nlinarith [extraAccelerationBound_nonneg n]))
      _ = 2 * globalAccelerationBound n * localMeshHalfWidth n := by ring
      _ < 1 := herrN
  have htri : ‖velocity n e t‖ ≤
      ‖velocity n e (localMeshPoint n a)‖ +
        ‖velocity n e t - velocity n e (localMeshPoint n a)‖ := by
    have hid : velocity n e t = velocity n e (localMeshPoint n a) +
        (velocity n e t - velocity n e (localMeshPoint n a)) := by abel
    calc
      ‖velocity n e t‖ = ‖velocity n e (localMeshPoint n a) +
          (velocity n e t - velocity n e (localMeshPoint n a))‖ :=
        congrArg norm hid
      _ ≤ _ := norm_add_le _ _
  exact (calc
    ‖velocity n e t‖ ≤ _ := htri
    _ < growingVelocityCutoff n + 1 := add_lt_add ha hsub'
    _ < 2 * growingVelocityCutoff n := by linarith).le

lemma norm_eval_sub_le_of_global_velocity
    (n : ℕ) (e : SignVector (2 * n + 1)) (T x y : ℝ)
    (hxy : x ≤ y)
    (hvel : ∀ s ∈ Set.Icc x y, ‖velocity n e s‖ ≤ T) :
    ‖eval n e y - eval n e x‖ ≤ T * (y - x) := by
  exact norm_image_sub_le_of_norm_deriv_le_segment'
    (fun s _hs ↦ (hasDerivAt_eval n e s).hasDerivWithinAt)
    (fun s hs ↦ hvel s ⟨hs.1, hs.2.le⟩)
    y (Set.right_mem_Icc.mpr hxy)

lemma small_value_transfers_to_left_cover_point
    {n : ℕ} (hn : 0 < n) (e : SignVector (2 * n + 1))
    (hglobal : ∀ s ∈ Set.Ico (-(Real.pi * n)) (Real.pi * n),
      ‖velocity n e s‖ ≤ 2 * growingVelocityCutoff n)
    (u t q step : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi * n))
    (hq0 : 0 ≤ q) (hqt : q ≤ t) (htop : t < Real.pi * n)
    (hdist : t - q < step) (hstep : 0 ≤ step)
    (hsmall : ‖eval n e t‖ ≤ u / n) :
    ‖eval n e q‖ ≤ u / n + 2 * growingVelocityCutoff n * step := by
  have hsegment : ∀ s ∈ Set.Icc q t,
      s ∈ Set.Ico (-(Real.pi * n)) (Real.pi * n) := by
    intro s hs
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hp : 0 < Real.pi * (n : ℝ) := mul_pos Real.pi_pos hnR
    exact ⟨(le_of_lt (neg_lt_zero.mpr hp)).trans (hq0.trans hs.1),
      hs.2.trans_lt htop⟩
  have hdiff := norm_eval_sub_le_of_global_velocity
    n e (2 * growingVelocityCutoff n) q t hqt
      (fun s hs ↦ hglobal s (hsegment s hs))
  have htri : ‖eval n e q‖ ≤ ‖eval n e t‖ + ‖eval n e t - eval n e q‖ := by
    have hid : eval n e q = eval n e t - (eval n e t - eval n e q) := by abel
    calc
      ‖eval n e q‖ = ‖eval n e t - (eval n e t - eval n e q)‖ := congrArg norm hid
      _ ≤ _ := norm_sub_le _ _
  have hT : 0 ≤ 2 * growingVelocityCutoff n :=
    mul_nonneg (by norm_num) (growingVelocityCutoff_nonneg n)
  calc
    ‖eval n e q‖ ≤ _ := htri
    _ ≤ u / n + (2 * growingVelocityCutoff n) * (t - q) :=
      add_le_add hsmall hdiff
    _ ≤ u / n + 2 * growingVelocityCutoff n * step := by
      simpa using add_le_add_left
        (mul_le_mul_of_nonneg_left hdist.le hT) (u / n)

lemma small_value_transfers_to_right_cover_point
    {n : ℕ} (hn : 0 < n) (e : SignVector (2 * n + 1))
    (hglobal : ∀ s ∈ Set.Ico (-(Real.pi * n)) (Real.pi * n),
      ‖velocity n e s‖ ≤ 2 * growingVelocityCutoff n)
    (u t q step : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (Real.pi * n))
    (htq : t ≤ q) (hqtop : q < Real.pi * n)
    (hdist : q - t < step) (hstep : 0 ≤ step)
    (hsmall : ‖eval n e t‖ ≤ u / n) :
    ‖eval n e q‖ ≤ u / n + 2 * growingVelocityCutoff n * step := by
  have hsegment : ∀ s ∈ Set.Icc t q,
      s ∈ Set.Ico (-(Real.pi * n)) (Real.pi * n) := by
    intro s hs
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hp : 0 < Real.pi * (n : ℝ) := mul_pos Real.pi_pos hnR
    exact ⟨(le_of_lt (neg_lt_zero.mpr hp)).trans (ht.1.trans hs.1),
      hs.2.trans_lt hqtop⟩
  have hdiff := norm_eval_sub_le_of_global_velocity
    n e (2 * growingVelocityCutoff n) t q htq
      (fun s hs ↦ hglobal s (hsegment s hs))
  have htri : ‖eval n e q‖ ≤ ‖eval n e t‖ + ‖eval n e q - eval n e t‖ := by
    have hid : eval n e q = eval n e t + (eval n e q - eval n e t) := by abel
    calc
      ‖eval n e q‖ = ‖eval n e t + (eval n e q - eval n e t)‖ := congrArg norm hid
      _ ≤ _ := norm_add_le _ _
  have hT : 0 ≤ 2 * growingVelocityCutoff n :=
    mul_nonneg (by norm_num) (growingVelocityCutoff_nonneg n)
  calc
    ‖eval n e q‖ ≤ _ := htri
    _ ≤ u / n + (2 * growingVelocityCutoff n) * (q - t) :=
      add_le_add hsmall hdiff
    _ ≤ u / n + 2 * growingVelocityCutoff n * step := by
      simpa using add_le_add_left
        (mul_le_mul_of_nonneg_left hdist.le hT) (u / n)

lemma eventually_badArcSmallMinimum_subset_coverExceptions (u : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ e : SignVector (2 * n + 1),
      HasBadArcSmallMinimum n u e →
        HasLeftEndpointCoverWitness n u e ∨
          HasRightEndpointCoverWitness n u e ∨
          HasInteriorCoverWitness n u e ∨
          HasHighPrefixFineMeshAcceleration 0 n e ∨
          HasEndpointZero n e ∨
          HasHighMeshVelocity n (growingVelocityCutoff n) e := by
  filter_upwards [Nat.eventually_pos,
      eventually_small_value_away_from_endpoints u,
      eventually_global_velocity_le_two_growing,
      Erdos525.eventually_endpointShellUpper_48_gt_eleven,
      Erdos525.eventually_badArcCoarseWidth_lt_one] with
      n hn hawayN hglobalN hshell hwidth e hbad
  by_cases hacc : HasHighPrefixFineMeshAcceleration 0 n e
  · exact Or.inr (Or.inr (Or.inr (Or.inl hacc)))
  by_cases hendpoint : HasEndpointZero n e
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hendpoint))))
  by_cases hmesh : HasHighMeshVelocity n (growingVelocityCutoff n) e
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hmesh))))
  rcases hbad with ⟨t, ht, hvalue, hsmall, hnonsmooth⟩
  have hsmallEval : ‖eval n e t‖ ≤ u / n := by
    rw [hvalue]
    exact hsmall
  have haway := hawayN e hacc hendpoint t ht hsmallEval
  have hglobal := hglobalN e hmesh
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
      hn e hglobal u t (endpointShellPoint n ℓ b)
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
    have hqdIcc : qd ∈ Set.Icc (0 : ℝ) 11 := ⟨hqd0, hqd.trans hright⟩
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
      hn e hglobal u t q (endpointShellStep n ℓ) ht htq hqtop
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
    hn e hglobal u t q (badArcCoarseWidth n) ht
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
          uniformProbability (HasHighPrefixFineMeshAcceleration 0 n) +
          uniformProbability (HasEndpointZero n) +
          uniformProbability (HasHighMeshVelocity n (growingVelocityCutoff n)) := by
  filter_upwards [eventually_badArcSmallMinimum_subset_coverExceptions u] with
      n hsubset
  let A : SignVector (2 * n + 1) → Prop := HasLeftEndpointCoverWitness n u
  let B : SignVector (2 * n + 1) → Prop := HasRightEndpointCoverWitness n u
  let C : SignVector (2 * n + 1) → Prop := HasInteriorCoverWitness n u
  let D : SignVector (2 * n + 1) → Prop := HasHighPrefixFineMeshAcceleration 0 n
  let E : SignVector (2 * n + 1) → Prop := HasEndpointZero n
  let F : SignVector (2 * n + 1) → Prop :=
    HasHighMeshVelocity n (growingVelocityCutoff n)
  have hmono : uniformProbability (HasBadArcSmallMinimum n u) ≤
      uniformProbability (fun e ↦ A e ∨ B e ∨ C e ∨ D e ∨ E e ∨ F e) := by
    apply uniformProbability_mono
    intro e he
    simpa only [A, B, C, D, E, F] using hsubset e he
  calc
    uniformProbability (HasBadArcSmallMinimum n u) ≤
        uniformProbability (fun e ↦ A e ∨ B e ∨ C e ∨ D e ∨ E e ∨ F e) := hmono
    _ ≤ uniformProbability A +
        uniformProbability (fun e ↦ B e ∨ C e ∨ D e ∨ E e ∨ F e) :=
      uniformProbability_or_le_add _ _
    _ ≤ uniformProbability A + (uniformProbability B +
        uniformProbability (fun e ↦ C e ∨ D e ∨ E e ∨ F e)) := by
      gcongr
      exact uniformProbability_or_le_add _ _
    _ ≤ uniformProbability A + (uniformProbability B +
        (uniformProbability C +
          uniformProbability (fun e ↦ D e ∨ E e ∨ F e))) := by
      gcongr
      exact uniformProbability_or_le_add _ _
    _ ≤ uniformProbability A + (uniformProbability B +
        (uniformProbability C + (uniformProbability D +
          uniformProbability (fun e ↦ E e ∨ F e)))) := by
      gcongr
      exact uniformProbability_or_le_add _ _
    _ ≤ uniformProbability A + (uniformProbability B +
        (uniformProbability C + (uniformProbability D +
          (uniformProbability E + uniformProbability F)))) := by
      gcongr
      exact uniformProbability_or_le_add _ _
    _ = _ := by
      simp only [A, B, C, D, E, F]
      ring

lemma uniformProbability_highPrefixFineMeshAcceleration_tendsto_zero :
    Tendsto (fun n : ℕ ↦
      uniformProbability (HasHighPrefixFineMeshAcceleration 0 n))
      atTop (𝓝 0) := by
  simpa using localMeshSize_pow_mul_highPrefixFineMeshAcceleration_tendsto_zero 0 0

theorem uniformProbability_badArcSmallMinimum_tendsto_zero
    (u : ℝ) (hu : 0 < u) :
    Tendsto (fun n : ℕ ↦ uniformProbability (HasBadArcSmallMinimum n u))
      atTop (𝓝 0) := by
  have hsum := (((((uniformProbability_leftEndpointCoverWitness_tendsto_zero u hu).add
      (uniformProbability_rightEndpointCoverWitness_tendsto_zero u hu)).add
      (uniformProbability_interiorCoverWitness_tendsto_zero u hu)).add
      uniformProbability_highPrefixFineMeshAcceleration_tendsto_zero).add
      uniformProbability_hasEndpointZero_tendsto_zero).add
      uniformProbability_highMeshVelocity_growing_tendsto_zero
  have hsum' : Tendsto (fun n : ℕ ↦
      uniformProbability (HasLeftEndpointCoverWitness n u) +
        uniformProbability (HasRightEndpointCoverWitness n u) +
        uniformProbability (HasInteriorCoverWitness n u) +
        uniformProbability (HasHighPrefixFineMeshAcceleration 0 n) +
        uniformProbability (HasEndpointZero n) +
        uniformProbability (HasHighMeshVelocity n (growingVelocityCutoff n)))
      atTop (𝓝 0) := by simpa using hsum
  apply squeeze_zero' (Eventually.of_forall fun n ↦ uniformProbability_nonneg _)
  · exact eventually_uniformProbability_badArcSmallMinimum_le_coverExceptions u
  · exact hsum'

end Odd

end Erdos525
