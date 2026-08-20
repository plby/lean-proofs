import ErdosProblems.Erdos525.Transfer

open scoped BigOperators ENNReal NNReal Topology Real
open MeasureTheory Filter Set

namespace Erdos525

lemma joint_factoredTruncatedLocalRepresentatives_positionBall
    (n : ℕ) (hn : 0 < n)
    (widthFactor u velocityLower velocityUpper : ℝ)
    (hfactor : 0 ≤ widthFactor) (hu : 0 ≤ u)
    (hvelocityLower : 0 < velocityLower)
    (hvelocityUpper : 0 ≤ velocityUpper)
    (e : SignVector (2 * n))
    (s : Finset (Fin (localMeshSize n)))
    (hrep : ∀ a ∈ s,
      IsFactoredTruncatedLocalRepresentative n widthFactor u
        velocityLower velocityUpper e a) :
    ‖normalizedPositionEuclideanWalk n e (localSitesPoints s)‖ ≤
      positionRepresentativeRadius s.card n u
        (widthFactor * velocityUpper) := by
  let R : ℝ := widthFactor * localMeshHalfWidth n * velocityUpper + u / n
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hR : 0 ≤ R := by
    dsimp [R]
    exact add_nonneg
      (mul_nonneg (mul_nonneg hfactor (by
        unfold localMeshHalfWidth
        positivity)) hvelocityUpper)
      (div_nonneg hu hnreal.le)
  have hregion := (joint_factoredTruncatedLocalRepresentatives_iff_region
    n hn widthFactor u velocityLower velocityUpper hvelocityLower e s).1 hrep
  have hcoord : ∀ r : Fin s.card,
      ‖rescaledCenteredEval n e (localSitesPoints s r)‖ ≤ R := by
    intro r
    have hr := hregion r (Set.mem_univ r)
    change phaseToBlocks
        (normalizedPhaseEuclideanWalk n e (localSitesPoints s)) r ∈
      truncatedBlockRegion n u (widthFactor * localMeshHalfWidth n)
        velocityLower velocityUpper at hr
    have hcompact := truncatedBlockRegion_subset_compactProduct n hn u
      (widthFactor * localMeshHalfWidth n) velocityLower velocityUpper hu
      (mul_nonneg hfactor (by unfold localMeshHalfWidth; positivity))
      hvelocityLower hr
    have hfirst := hcompact.1
    rw [phaseToBlocks_normalizedPhaseEuclideanWalk] at hfirst
    simpa [Metric.mem_closedBall, dist_zero_right, R, mul_assoc] using hfirst
  have hsquares : ∑ r : Fin s.card,
      ‖rescaledCenteredEval n e (localSitesPoints s r)‖ ^ 2 ≤
      s.card * R ^ 2 := by
    calc
      _ ≤ ∑ _r : Fin s.card, R ^ 2 := by
        apply Finset.sum_le_sum
        intro r _hr
        exact (sq_le_sq₀ (norm_nonneg _) hR).2 (hcoord r)
      _ = s.card * R ^ 2 := by simp
  have hnormsq :
      ‖normalizedPositionEuclideanWalk n e (localSitesPoints s)‖ ^ 2 ≤
        (Real.sqrt s.card * R) ^ 2 := by
    rw [norm_normalizedPositionEuclideanWalk_sq]
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    simpa [R] using hsquares
  have hnorm := (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) hR)).1 hnormsq
  simpa [positionRepresentativeRadius, R, mul_assoc, mul_left_comm,
    mul_comm] using hnorm

theorem eventually_scaled_halfWeakNonspread_factored_site_probability_le_power
    (k : ℕ) (hk : 0 < k)
    (widthFactor u velocityLower velocityUpper : ℝ)
    (hfactor : 0 ≤ widthFactor) (hu : 0 ≤ u)
    (hvelocityLower : 0 < velocityLower)
    (hvelocityUpper : 0 ≤ velocityUpper) :
    ∀ᶠ n : ℕ in atTop,
      ∀ s ∈ halfWeakNonspreadLocalSiteSets n k,
        (localMeshSize n : ℝ) ^ k *
          uniformProbability (fun e : SignVector (2 * n) ↦
            ∀ a ∈ s,
              IsFactoredTruncatedLocalRepresentative n widthFactor u
                velocityLower velocityUpper e a) ≤
        rigidityPower n (1 / 20) := by
  classical
  have hfactorUpper : 0 ≤ widthFactor * velocityUpper :=
    mul_nonneg hfactor hvelocityUpper
  filter_upwards [Nat.eventually_pos,
      eventually_scaled_positionBall_probability_le_power
        hk u (widthFactor * velocityUpper) hu hfactorUpper]
    with n hn hball
  intro s hs
  have hweak := Finset.mem_filter.mp hs
  have hnonspread := Finset.mem_filter.mp hweak.1
  have hpowerset := Finset.mem_powersetCard.mp hnonspread.1
  have hcard : s.card = k := hpowerset.2
  have hsmooth : ∀ r : Fin s.card,
      IsSmooth n (rigiditySmoothScale n) (localSitesPoints s r) := by
    intro r
    exact (Finset.mem_filter.mp
      (hpowerset.1 (localSite_mem s r))).2
  have hprobMono :
      uniformProbability (fun e : SignVector (2 * n) ↦
          ∀ a ∈ s,
            IsFactoredTruncatedLocalRepresentative n widthFactor u
              velocityLower velocityUpper e a) ≤
        uniformProbability (fun e : SignVector (2 * n) ↦
          ‖normalizedPositionEuclideanWalk n e (localSitesPoints s)‖ ≤
            positionRepresentativeRadius s.card n u
              (widthFactor * velocityUpper)) := by
    apply uniformProbability_mono
    intro e he
    exact joint_factoredTruncatedLocalRepresentatives_positionBall n hn
      widthFactor u velocityLower velocityUpper hfactor hu hvelocityLower
        hvelocityUpper e s he
  subst k
  calc
    (localMeshSize n : ℝ) ^ s.card *
        uniformProbability (fun e : SignVector (2 * n) ↦
          ∀ a ∈ s,
            IsFactoredTruncatedLocalRepresentative n widthFactor u
              velocityLower velocityUpper e a) ≤
      (localMeshSize n : ℝ) ^ s.card *
        uniformProbability (fun e : SignVector (2 * n) ↦
          ‖normalizedPositionEuclideanWalk n e (localSitesPoints s)‖ ≤
            positionRepresentativeRadius s.card n u
              (widthFactor * velocityUpper)) :=
      mul_le_mul_of_nonneg_left hprobMono (by positivity)
    _ ≤ rigidityPower n (1 / 20) :=
      hball (localSitesPoints s) hsmooth hweak.2

noncomputable def halfWeakNonspreadFactoredChooseContribution
    (n k : ℕ) (widthFactor u velocityLower velocityUpper : ℝ) : ℝ :=
  ∑ s ∈ halfWeakNonspreadLocalSiteSets n k,
    uniformProbability (fun e : SignVector (2 * n) ↦
      ∀ a ∈ s,
        IsFactoredTruncatedLocalRepresentative n widthFactor u
          velocityLower velocityUpper e a)

theorem halfWeakNonspreadFactoredChooseContribution_tendsto_zero
    (k : ℕ) (hk : 0 < k)
    (widthFactor u velocityLower velocityUpper : ℝ)
    (hfactor : 0 ≤ widthFactor) (hu : 0 ≤ u)
    (hvelocityLower : 0 < velocityLower)
    (hvelocityUpper : 0 ≤ velocityUpper) :
    Tendsto (fun n : ℕ ↦
      halfWeakNonspreadFactoredChooseContribution n k widthFactor u
        velocityLower velocityUpper) atTop (𝓝 0) := by
  have hupper : ∀ᶠ n : ℕ in atTop,
      halfWeakNonspreadFactoredChooseContribution n k widthFactor u
          velocityLower velocityUpper ≤
        rigidityPower n (1 / 20) *
          (((badLocalSiteSets n k).card : ℝ) /
            (localMeshSize n : ℝ) ^ k) := by
    filter_upwards [
      eventually_scaled_halfWeakNonspread_factored_site_probability_le_power
        k hk widthFactor u velocityLower velocityUpper hfactor hu
          hvelocityLower hvelocityUpper] with n hsite
    let q : ℝ := (localMeshSize n : ℝ) ^ k
    have hq : 0 < q := by
      dsimp [q]
      exact pow_pos (by exact_mod_cast localMeshSize_pos n) k
    have hterm : ∀ s ∈ halfWeakNonspreadLocalSiteSets n k,
        uniformProbability (fun e : SignVector (2 * n) ↦
          ∀ a ∈ s,
            IsFactoredTruncatedLocalRepresentative n widthFactor u
              velocityLower velocityUpper e a) ≤
          rigidityPower n (1 / 20) / q := by
      intro s hs
      exact (le_div_iff₀ hq).2 (by simpa [q, mul_comm] using hsite s hs)
    calc
      halfWeakNonspreadFactoredChooseContribution n k widthFactor u
          velocityLower velocityUpper ≤
        ∑ _s ∈ halfWeakNonspreadLocalSiteSets n k,
          rigidityPower n (1 / 20) / q := by
        unfold halfWeakNonspreadFactoredChooseContribution
        exact Finset.sum_le_sum fun s hs ↦ hterm s hs
      _ = ((halfWeakNonspreadLocalSiteSets n k).card : ℝ) *
          (rigidityPower n (1 / 20) / q) := by simp
      _ ≤ ((badLocalSiteSets n k).card : ℝ) *
          (rigidityPower n (1 / 20) / q) := by
        have hcard : ((halfWeakNonspreadLocalSiteSets n k).card : ℝ) ≤
            (badLocalSiteSets n k).card := by
          exact_mod_cast Finset.card_le_card
            (halfWeakNonspread_subset_badLocalSiteSets n k)
        exact mul_le_mul_of_nonneg_right hcard
          (div_nonneg (rigidityPower_nonneg n _) hq.le)
      _ = rigidityPower n (1 / 20) *
          (((badLocalSiteSets n k).card : ℝ) /
            (localMeshSize n : ℝ) ^ k) := by
        dsimp only [q]
        ring
  apply squeeze_zero'
    (Eventually.of_forall fun n ↦ by
      unfold halfWeakNonspreadFactoredChooseContribution
      exact Finset.sum_nonneg fun s _ ↦ uniformProbability_nonneg _)
    hupper
  exact weighted_badLocalSiteSets_ratio_tendsto_zero k hk

noncomputable def halfVeryCloseFactoredChooseContribution
    (n k : ℕ) (widthFactor u velocityLower velocityUpper : ℝ) : ℝ :=
  ∑ s ∈ halfVeryCloseLocalSiteSets n k,
    uniformProbability (fun e : SignVector (2 * n) ↦
      ∀ a ∈ s,
        IsFactoredTruncatedLocalRepresentative n widthFactor u
          velocityLower velocityUpper e a)

theorem halfVeryCloseFactoredChooseContribution_one_tendsto_zero
    (widthFactor u velocityLower velocityUpper : ℝ) :
    Tendsto (fun n : ℕ ↦
      halfVeryCloseFactoredChooseContribution n 1 widthFactor u
        velocityLower velocityUpper) atTop (𝓝 0) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_halfVeryCloseLocalSiteSets_one_eq_empty]
    with n hn
  rw [halfVeryCloseFactoredChooseContribution, hn]
  simp

noncomputable def halfNonspreadFactoredChooseContribution
    (n k : ℕ) (widthFactor u velocityLower velocityUpper : ℝ) : ℝ :=
  ∑ s ∈ halfNonspreadLocalSiteSets n k,
    uniformProbability (fun e : SignVector (2 * n) ↦
      ∀ a ∈ s,
        IsFactoredTruncatedLocalRepresentative n widthFactor u
          velocityLower velocityUpper e a)

lemma halfNonspreadFactoredChooseContribution_eq_weak_add_veryClose
    (n k : ℕ) (widthFactor u velocityLower velocityUpper : ℝ) :
    halfNonspreadFactoredChooseContribution n k widthFactor u
        velocityLower velocityUpper =
      halfWeakNonspreadFactoredChooseContribution n k widthFactor u
          velocityLower velocityUpper +
        halfVeryCloseFactoredChooseContribution n k widthFactor u
          velocityLower velocityUpper := by
  rw [halfNonspreadFactoredChooseContribution,
    halfNonspread_eq_weak_union_veryClose,
    Finset.sum_union (halfWeakNonspread_disjoint_veryClose n k)]
  rfl

theorem halfNonspreadFactoredChooseContribution_one_tendsto_zero
    (widthFactor u velocityLower velocityUpper : ℝ)
    (hfactor : 0 ≤ widthFactor) (hu : 0 ≤ u)
    (hvelocityLower : 0 < velocityLower)
    (hvelocityUpper : 0 ≤ velocityUpper) :
    Tendsto (fun n : ℕ ↦
      halfNonspreadFactoredChooseContribution n 1 widthFactor u
        velocityLower velocityUpper) atTop (𝓝 0) := by
  have hweak := halfWeakNonspreadFactoredChooseContribution_tendsto_zero
    1 (by omega) widthFactor u velocityLower velocityUpper hfactor hu
      hvelocityLower hvelocityUpper
  have hclose := halfVeryCloseFactoredChooseContribution_one_tendsto_zero
    widthFactor u velocityLower velocityUpper
  have hsum := hweak.add hclose
  have hsum' : Tendsto (fun n : ℕ ↦
      halfWeakNonspreadFactoredChooseContribution n 1 widthFactor u
          velocityLower velocityUpper +
        halfVeryCloseFactoredChooseContribution n 1 widthFactor u
          velocityLower velocityUpper) atTop (𝓝 0) := by
    simpa using hsum
  apply hsum'.congr'
  exact Eventually.of_forall fun n ↦
    (halfNonspreadFactoredChooseContribution_eq_weak_add_veryClose
      n 1 widthFactor u velocityLower velocityUpper).symm

noncomputable def halfGoodOuterDefectContribution
    (n : ℕ) (widthFactor u velocityLower velocityUpper : ℝ) : ℝ :=
  ∑ s ∈ halfGoodLocalSiteSets n 1,
    uniformProbability (fun e : SignVector (2 * n) ↦
      (∀ a ∈ s,
        IsFactoredTruncatedLocalRepresentative n widthFactor u
          velocityLower velocityUpper e a) ∧
      ¬(∀ a ∈ s,
        IsTruncatedLocalRepresentative n u velocityLower velocityUpper e a))

lemma halfGoodOuterDefectContribution_eq_sub
    (n : ℕ) (widthFactor u velocityLower velocityUpper : ℝ)
    (hfactor : 1 ≤ widthFactor) :
    halfGoodOuterDefectContribution n widthFactor u velocityLower velocityUpper =
      halfGoodFactoredTruncatedChooseContribution n 1 widthFactor u
          velocityLower velocityUpper -
        halfGoodTruncatedChooseContribution n 1 u velocityLower velocityUpper := by
  classical
  unfold halfGoodOuterDefectContribution
  unfold halfGoodFactoredTruncatedChooseContribution
  unfold halfGoodTruncatedChooseContribution
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s _hs
  let P : SignVector (2 * n) → Prop := fun e ↦
    ∀ a ∈ s,
      IsFactoredTruncatedLocalRepresentative n widthFactor u
        velocityLower velocityUpper e a
  let Q : SignVector (2 * n) → Prop := fun e ↦
    ∀ a ∈ s,
      IsTruncatedLocalRepresentative n u velocityLower velocityUpper e a
  have hQP : ∀ e, Q e → P e := by
    intro e he a ha
    exact isFactoredTruncatedLocalRepresentative_mono n 1 widthFactor u
      velocityLower velocityUpper hfactor e a
      ((isFactoredTruncatedLocalRepresentative_one_iff
        n u velocityLower velocityUpper e a).2 (he a ha))
  exact uniformProbability_and_not_eq_sub P Q hQP

theorem halfGoodOuterDefectContribution_tendsto
    (widthFactor u velocityLower velocityUpper : ℝ)
    (hfactor : 1 ≤ widthFactor) (hu : 0 < u)
    (hvelLower : 0 < velocityLower) (hvelUpper : 0 < velocityUpper) :
    Tendsto (fun n : ℕ ↦
      halfGoodOuterDefectContribution n widthFactor u
        velocityLower velocityUpper) atTop
      (𝓝 ((widthFactor - 1) * ((6 * u / Real.pi) *
        blockVelocityMass velocityLower velocityUpper))) := by
  have hwide := halfGoodFactoredTruncatedChooseContribution_tendsto
    1 (by omega) widthFactor u velocityLower velocityUpper
      (lt_of_lt_of_le (by norm_num) hfactor) hu hvelLower hvelUpper
  have hfull := halfGoodTruncatedChooseContribution_tendsto
    1 (by omega) u velocityLower velocityUpper hu hvelLower hvelUpper
  have hsub := (hwide.sub hfull).congr'
    (Eventually.of_forall fun n ↦
      (halfGoodOuterDefectContribution_eq_sub n widthFactor u
        velocityLower velocityUpper hfactor).symm)
  convert hsub using 1 <;> simp <;> ring

def HalfHasFactoredRepresentative
    (n : ℕ) (widthFactor u velocityLower velocityUpper : ℝ)
    (e : SignVector (2 * n)) : Prop :=
  ∃ a ∈ halfSmoothLocalMeshSites n,
    IsFactoredTruncatedLocalRepresentative n widthFactor u
      velocityLower velocityUpper e a

def HalfHasTruncatedRepresentative
    (n : ℕ) (u velocityLower velocityUpper : ℝ)
    (e : SignVector (2 * n)) : Prop :=
  ∃ a ∈ halfSmoothLocalMeshSites n,
    IsTruncatedLocalRepresentative n u velocityLower velocityUpper e a

lemma halfHasTruncatedRepresentative_iff_count_ne_zero
    (n : ℕ) (u velocityLower velocityUpper : ℝ)
    (e : SignVector (2 * n)) :
    HalfHasTruncatedRepresentative n u velocityLower velocityUpper e ↔
      halfTruncatedLocalMinimumCount n u velocityLower velocityUpper e ≠ 0 := by
  classical
  simp [HalfHasTruncatedRepresentative, halfTruncatedLocalMinimumCount]

lemma uniformProbability_halfHasFactored_and_not_truncated_le
    (n : ℕ) (widthFactor u velocityLower velocityUpper : ℝ) :
    uniformProbability (fun e : SignVector (2 * n) ↦
      HalfHasFactoredRepresentative n widthFactor u velocityLower velocityUpper e ∧
      ¬HalfHasTruncatedRepresentative n u velocityLower velocityUpper e) ≤
      halfGoodOuterDefectContribution n widthFactor u
          velocityLower velocityUpper +
        halfNonspreadFactoredChooseContribution n 1 widthFactor u
          velocityLower velocityUpper := by
  classical
  let GoodEvent : SignVector (2 * n) → Prop := fun e ↦
    ∃ s ∈ halfGoodLocalSiteSets n 1,
      (∀ a ∈ s,
        IsFactoredTruncatedLocalRepresentative n widthFactor u
          velocityLower velocityUpper e a) ∧
      ¬(∀ a ∈ s,
        IsTruncatedLocalRepresentative n u velocityLower velocityUpper e a)
  let BadEvent : SignVector (2 * n) → Prop := fun e ↦
    ∃ s ∈ halfNonspreadLocalSiteSets n 1,
      ∀ a ∈ s,
        IsFactoredTruncatedLocalRepresentative n widthFactor u
          velocityLower velocityUpper e a
  have hevent : ∀ e : SignVector (2 * n),
      HalfHasFactoredRepresentative n widthFactor u velocityLower velocityUpper e ∧
        ¬HalfHasTruncatedRepresentative n u velocityLower velocityUpper e →
      GoodEvent e ∨ BadEvent e := by
    intro e he
    rcases he.1 with ⟨a, haSmooth, haWide⟩
    have hsingleton : {a} ∈ (halfSmoothLocalMeshSites n).powersetCard 1 := by
      rw [Finset.mem_powersetCard]
      simp [haSmooth]
    rw [halfSmoothPowerset_eq_good_union_nonspread] at hsingleton
    rcases Finset.mem_union.mp hsingleton with hgood | hbad
    · left
      refine ⟨{a}, hgood, ?_, ?_⟩
      · simpa using haWide
      · intro hall
        exact he.2 ⟨a, haSmooth, by simpa using hall a (by simp)⟩
    · right
      refine ⟨{a}, hbad, ?_⟩
      simpa using haWide
  calc
    uniformProbability (fun e : SignVector (2 * n) ↦
        HalfHasFactoredRepresentative n widthFactor u velocityLower velocityUpper e ∧
        ¬HalfHasTruncatedRepresentative n u velocityLower velocityUpper e) ≤
      uniformProbability (fun e ↦ GoodEvent e ∨ BadEvent e) :=
        uniformProbability_mono hevent
    _ ≤ uniformProbability GoodEvent + uniformProbability BadEvent :=
      uniformProbability_or_le_add _ _
    _ ≤ halfGoodOuterDefectContribution n widthFactor u
          velocityLower velocityUpper +
        halfNonspreadFactoredChooseContribution n 1 widthFactor u
          velocityLower velocityUpper := by
      apply add_le_add
      · calc
          uniformProbability GoodEvent ≤
              ∑ s ∈ halfGoodLocalSiteSets n 1,
                uniformProbability (fun e : SignVector (2 * n) ↦
                  (∀ a ∈ s,
                    IsFactoredTruncatedLocalRepresentative n widthFactor u
                      velocityLower velocityUpper e a) ∧
                  ¬(∀ a ∈ s,
                    IsTruncatedLocalRepresentative n u velocityLower velocityUpper e a)) := by
            unfold GoodEvent
            let P := fun s (e : SignVector (2 * n)) ↦
              s ∈ halfGoodLocalSiteSets n 1 ∧
              ((∀ a ∈ s,
                  IsFactoredTruncatedLocalRepresentative n widthFactor u
                    velocityLower velocityUpper e a) ∧
                ¬(∀ a ∈ s,
                  IsTruncatedLocalRepresentative n u velocityLower velocityUpper e a))
            calc
              uniformProbability (fun e : SignVector (2 * n) ↦ ∃ s, P s e) ≤
                  ∑ s, uniformProbability (P s) :=
                uniformProbability_exists_le_sum P
              _ = ∑ s ∈ halfGoodLocalSiteSets n 1,
                  uniformProbability (fun e : SignVector (2 * n) ↦
                    (∀ a ∈ s,
                      IsFactoredTruncatedLocalRepresentative n widthFactor u
                        velocityLower velocityUpper e a) ∧
                    ¬(∀ a ∈ s,
                      IsTruncatedLocalRepresentative n u velocityLower velocityUpper e a)) := by
                classical
                rw [← Finset.sum_subset (Finset.subset_univ
                  (halfGoodLocalSiteSets n 1))]
                · apply Finset.sum_congr rfl
                  intro s hs
                  apply congrArg uniformProbability
                  funext e
                  simp [P, hs]
                · intro s _hs hnot
                  simp [P, hnot, uniformProbability]
          _ = halfGoodOuterDefectContribution n widthFactor u
                velocityLower velocityUpper := by
            rfl
      · calc
          uniformProbability BadEvent ≤
              ∑ s ∈ halfNonspreadLocalSiteSets n 1,
                uniformProbability (fun e : SignVector (2 * n) ↦
                  ∀ a ∈ s,
                    IsFactoredTruncatedLocalRepresentative n widthFactor u
                      velocityLower velocityUpper e a) := by
            unfold BadEvent
            let P := fun s (e : SignVector (2 * n)) ↦
              s ∈ halfNonspreadLocalSiteSets n 1 ∧
                ∀ a ∈ s,
                  IsFactoredTruncatedLocalRepresentative n widthFactor u
                    velocityLower velocityUpper e a
            calc
              uniformProbability (fun e : SignVector (2 * n) ↦ ∃ s, P s e) ≤
                  ∑ s, uniformProbability (P s) :=
                uniformProbability_exists_le_sum P
              _ = ∑ s ∈ halfNonspreadLocalSiteSets n 1,
                  uniformProbability (fun e : SignVector (2 * n) ↦
                    ∀ a ∈ s,
                      IsFactoredTruncatedLocalRepresentative n widthFactor u
                        velocityLower velocityUpper e a) := by
                classical
                rw [← Finset.sum_subset (Finset.subset_univ
                  (halfNonspreadLocalSiteSets n 1))]
                · apply Finset.sum_congr rfl
                  intro s hs
                  apply congrArg uniformProbability
                  funext e
                  simp [P, hs]
                · intro s _hs hnot
                  simp [P, hnot, uniformProbability]
          _ = halfNonspreadFactoredChooseContribution n 1 widthFactor u
                velocityLower velocityUpper := by
            rfl

theorem eventually_uniformProbability_halfHasFactored_and_not_truncated_lt
    (widthFactor u velocityLower velocityUpper : ℝ)
    (hfactor : 1 ≤ widthFactor) (hu : 0 < u)
    (hvelLower : 0 < velocityLower) (hvelUpper : 0 < velocityUpper)
    {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ n : ℕ in atTop,
      uniformProbability (fun e : SignVector (2 * n) ↦
        HalfHasFactoredRepresentative n widthFactor u
            velocityLower velocityUpper e ∧
          ¬HalfHasTruncatedRepresentative n u
            velocityLower velocityUpper e) <
        (widthFactor - 1) * ((6 * u / Real.pi) *
          blockVelocityMass velocityLower velocityUpper) + eps := by
  have hgood := halfGoodOuterDefectContribution_tendsto
    widthFactor u velocityLower velocityUpper hfactor hu hvelLower hvelUpper
  have hbad := halfNonspreadFactoredChooseContribution_one_tendsto_zero
    widthFactor u velocityLower velocityUpper
      (show 0 ≤ widthFactor by linarith) hu.le hvelLower hvelUpper.le
  have hsum : Tendsto (fun n : ℕ ↦
      halfGoodOuterDefectContribution n widthFactor u
          velocityLower velocityUpper +
        halfNonspreadFactoredChooseContribution n 1 widthFactor u
          velocityLower velocityUpper) atTop
      (𝓝 ((widthFactor - 1) * ((6 * u / Real.pi) *
        blockVelocityMass velocityLower velocityUpper))) := by
    simpa using hgood.add hbad
  have hevent := hsum.eventually (Iio_mem_nhds
    (lt_add_of_pos_right
      ((widthFactor - 1) * ((6 * u / Real.pi) *
        blockVelocityMass velocityLower velocityUpper)) heps))
  filter_upwards [hevent] with n hn
  exact (uniformProbability_halfHasFactored_and_not_truncated_le n
    widthFactor u velocityLower velocityUpper).trans_lt hn

end Erdos525
