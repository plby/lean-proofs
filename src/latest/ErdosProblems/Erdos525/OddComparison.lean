import ErdosProblems.Erdos525.OddBadMinimum

open scoped BigOperators ENNReal NNReal Topology Real
open MeasureTheory Filter Set

namespace Erdos525

open Classical Finset

namespace Odd

lemma isFactoredTruncatedLocalRepresentative_mono
    (n : ℕ) (widthFactor₁ widthFactor₂ u velocityLower velocityUpper : ℝ)
    (hfactor : widthFactor₁ ≤ widthFactor₂)
    (e : SignVector (2 * n + 1)) (a : Fin (localMeshSize n))
    (hrep : IsFactoredTruncatedLocalRepresentative n widthFactor₁ u
      velocityLower velocityUpper e a) :
    IsFactoredTruncatedLocalRepresentative n widthFactor₂ u
      velocityLower velocityUpper e a := by
  rcases hrep with ⟨hvel, hoff, hheight, hlower, hupper⟩
  refine ⟨hvel, hoff.trans ?_, hheight, hlower, hupper⟩
  exact mul_le_mul_of_nonneg_right hfactor (by
    unfold localMeshHalfWidth
    positivity)

theorem halfVeryCloseFactoredChooseContribution_one_tendsto_zero
    (widthFactor u velocityLower velocityUpper : ℝ) :
    Tendsto (fun n : ℕ ↦
      halfVeryCloseFactoredChooseContribution n 1 widthFactor u
        velocityLower velocityUpper) atTop (𝓝 0) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_halfVeryCloseLocalSiteSets_one_eq_empty] with n hn
  rw [halfVeryCloseFactoredChooseContribution, hn]
  simp

theorem halfNonspreadFactoredChooseContribution_one_tendsto_zero_wide
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
  have hsum' := hsum.congr' (Eventually.of_forall fun n ↦
    (halfNonspreadFactoredChooseContribution_eq_weak_add_veryClose
      n 1 widthFactor u velocityLower velocityUpper).symm)
  simpa only [zero_add] using hsum'

noncomputable def halfGoodOuterDefectContribution
    (n : ℕ) (wideFactor narrowFactor u velocityLower velocityUpper : ℝ) : ℝ :=
  ∑ s ∈ halfGoodLocalSiteSets n 1,
    uniformProbability (fun e : SignVector (2 * n + 1) ↦
      (∀ a ∈ s,
        IsFactoredTruncatedLocalRepresentative n wideFactor u
          velocityLower velocityUpper e a) ∧
      ¬(∀ a ∈ s,
        IsFactoredTruncatedLocalRepresentative n narrowFactor u
          velocityLower velocityUpper e a))

lemma halfGoodOuterDefectContribution_eq_sub
    (n : ℕ) (wideFactor narrowFactor u velocityLower velocityUpper : ℝ)
    (hfactor : narrowFactor ≤ wideFactor) :
    halfGoodOuterDefectContribution n wideFactor narrowFactor u
        velocityLower velocityUpper =
      halfGoodFactoredTruncatedChooseContribution n 1 wideFactor u
          velocityLower velocityUpper -
        halfGoodFactoredTruncatedChooseContribution n 1 narrowFactor u
          velocityLower velocityUpper := by
  classical
  unfold halfGoodOuterDefectContribution
  unfold halfGoodFactoredTruncatedChooseContribution
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s _hs
  let P : SignVector (2 * n + 1) → Prop := fun e ↦
    ∀ a ∈ s, IsFactoredTruncatedLocalRepresentative n wideFactor u
      velocityLower velocityUpper e a
  let Q : SignVector (2 * n + 1) → Prop := fun e ↦
    ∀ a ∈ s, IsFactoredTruncatedLocalRepresentative n narrowFactor u
      velocityLower velocityUpper e a
  have hQP : ∀ e, Q e → P e := by
    intro e he a ha
    exact isFactoredTruncatedLocalRepresentative_mono n narrowFactor wideFactor u
      velocityLower velocityUpper hfactor e a (he a ha)
  exact uniformProbability_and_not_eq_sub P Q hQP

theorem halfGoodOuterDefectContribution_tendsto
    (wideFactor narrowFactor u velocityLower velocityUpper : ℝ)
    (hwide : 0 < wideFactor) (hnarrow : 0 < narrowFactor)
    (hfactor : narrowFactor ≤ wideFactor) (hu : 0 < u)
    (hvelLower : 0 < velocityLower) (hvelUpper : 0 < velocityUpper) :
    Tendsto (fun n : ℕ ↦
      halfGoodOuterDefectContribution n wideFactor narrowFactor u
        velocityLower velocityUpper) atTop
      (𝓝 ((wideFactor - narrowFactor) * ((6 * u / Real.pi) *
        blockVelocityMass velocityLower velocityUpper))) := by
  have hwideLimit := halfGoodFactoredTruncatedChooseContribution_tendsto
    1 (by omega) wideFactor u velocityLower velocityUpper
      hwide hu hvelLower hvelUpper
  have hnarrowLimit := halfGoodFactoredTruncatedChooseContribution_tendsto
    1 (by omega) narrowFactor u velocityLower velocityUpper
      hnarrow hu hvelLower hvelUpper
  have hsub := (hwideLimit.sub hnarrowLimit).congr'
    (Eventually.of_forall fun n ↦
      (halfGoodOuterDefectContribution_eq_sub n wideFactor narrowFactor u
        velocityLower velocityUpper hfactor).symm)
  convert hsub using 1 <;> simp <;> ring

def HalfHasFactoredRepresentative
    (n : ℕ) (widthFactor u velocityLower velocityUpper : ℝ)
    (e : SignVector (2 * n + 1)) : Prop :=
  ∃ a ∈ halfSmoothLocalMeshSites n,
    IsFactoredTruncatedLocalRepresentative n widthFactor u
      velocityLower velocityUpper e a

lemma halfHasFactoredRepresentative_iff_count_ne_zero
    (n : ℕ) (widthFactor u velocityLower velocityUpper : ℝ)
    (e : SignVector (2 * n + 1)) :
    HalfHasFactoredRepresentative n widthFactor u velocityLower velocityUpper e ↔
      halfFactoredTruncatedLocalMinimumCount n widthFactor u
        velocityLower velocityUpper e ≠ 0 := by
  classical
  simp [HalfHasFactoredRepresentative, halfFactoredTruncatedLocalMinimumCount]

lemma uniformProbability_halfHasWide_and_not_narrow_le
    (n : ℕ) (wideFactor narrowFactor u velocityLower velocityUpper : ℝ) :
    uniformProbability (fun e : SignVector (2 * n + 1) ↦
      HalfHasFactoredRepresentative n wideFactor u velocityLower velocityUpper e ∧
      ¬HalfHasFactoredRepresentative n narrowFactor u velocityLower velocityUpper e) ≤
      halfGoodOuterDefectContribution n wideFactor narrowFactor u
          velocityLower velocityUpper +
        halfNonspreadFactoredChooseContribution n 1 wideFactor u
          velocityLower velocityUpper := by
  classical
  let GoodEvent : SignVector (2 * n + 1) → Prop := fun e ↦
    ∃ s ∈ halfGoodLocalSiteSets n 1,
      (∀ a ∈ s, IsFactoredTruncatedLocalRepresentative n wideFactor u
        velocityLower velocityUpper e a) ∧
      ¬(∀ a ∈ s, IsFactoredTruncatedLocalRepresentative n narrowFactor u
        velocityLower velocityUpper e a)
  let BadEvent : SignVector (2 * n + 1) → Prop := fun e ↦
    ∃ s ∈ halfNonspreadLocalSiteSets n 1,
      ∀ a ∈ s, IsFactoredTruncatedLocalRepresentative n wideFactor u
        velocityLower velocityUpper e a
  have hevent : ∀ e : SignVector (2 * n + 1),
      HalfHasFactoredRepresentative n wideFactor u velocityLower velocityUpper e ∧
        ¬HalfHasFactoredRepresentative n narrowFactor u velocityLower velocityUpper e →
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
    uniformProbability (fun e : SignVector (2 * n + 1) ↦
        HalfHasFactoredRepresentative n wideFactor u velocityLower velocityUpper e ∧
        ¬HalfHasFactoredRepresentative n narrowFactor u velocityLower velocityUpper e) ≤
      uniformProbability (fun e ↦ GoodEvent e ∨ BadEvent e) :=
        uniformProbability_mono hevent
    _ ≤ uniformProbability GoodEvent + uniformProbability BadEvent :=
      uniformProbability_or_le_add _ _
    _ ≤ halfGoodOuterDefectContribution n wideFactor narrowFactor u
          velocityLower velocityUpper +
        halfNonspreadFactoredChooseContribution n 1 wideFactor u
          velocityLower velocityUpper := by
      apply add_le_add
      · calc
          uniformProbability GoodEvent ≤
              ∑ s ∈ halfGoodLocalSiteSets n 1,
                uniformProbability (fun e : SignVector (2 * n + 1) ↦
                  (∀ a ∈ s, IsFactoredTruncatedLocalRepresentative n wideFactor u
                    velocityLower velocityUpper e a) ∧
                  ¬(∀ a ∈ s, IsFactoredTruncatedLocalRepresentative n narrowFactor u
                    velocityLower velocityUpper e a)) := by
            unfold GoodEvent
            let P := fun s (e : SignVector (2 * n + 1)) ↦
              s ∈ halfGoodLocalSiteSets n 1 ∧
              ((∀ a ∈ s, IsFactoredTruncatedLocalRepresentative n wideFactor u
                  velocityLower velocityUpper e a) ∧
                ¬(∀ a ∈ s, IsFactoredTruncatedLocalRepresentative n narrowFactor u
                  velocityLower velocityUpper e a))
            calc
              uniformProbability (fun e : SignVector (2 * n + 1) ↦ ∃ s, P s e) ≤
                  ∑ s, uniformProbability (P s) := uniformProbability_exists_le_sum P
              _ = ∑ s ∈ halfGoodLocalSiteSets n 1,
                  uniformProbability (fun e : SignVector (2 * n + 1) ↦
                    (∀ a ∈ s, IsFactoredTruncatedLocalRepresentative n wideFactor u
                      velocityLower velocityUpper e a) ∧
                    ¬(∀ a ∈ s, IsFactoredTruncatedLocalRepresentative n narrowFactor u
                      velocityLower velocityUpper e a)) := by
                rw [← Finset.sum_subset (Finset.subset_univ
                  (halfGoodLocalSiteSets n 1))]
                · apply Finset.sum_congr rfl
                  intro s hs
                  apply congrArg uniformProbability
                  funext e
                  simp [P, hs]
                · intro s _hs hnot
                  simp [P, hnot, uniformProbability]
          _ = halfGoodOuterDefectContribution n wideFactor narrowFactor u
                velocityLower velocityUpper := rfl
      · calc
          uniformProbability BadEvent ≤
              ∑ s ∈ halfNonspreadLocalSiteSets n 1,
                uniformProbability (fun e : SignVector (2 * n + 1) ↦
                  ∀ a ∈ s, IsFactoredTruncatedLocalRepresentative n wideFactor u
                    velocityLower velocityUpper e a) := by
            unfold BadEvent
            let P := fun s (e : SignVector (2 * n + 1)) ↦
              s ∈ halfNonspreadLocalSiteSets n 1 ∧
                ∀ a ∈ s, IsFactoredTruncatedLocalRepresentative n wideFactor u
                  velocityLower velocityUpper e a
            calc
              uniformProbability (fun e : SignVector (2 * n + 1) ↦ ∃ s, P s e) ≤
                  ∑ s, uniformProbability (P s) := uniformProbability_exists_le_sum P
              _ = ∑ s ∈ halfNonspreadLocalSiteSets n 1,
                  uniformProbability (fun e : SignVector (2 * n + 1) ↦
                    ∀ a ∈ s, IsFactoredTruncatedLocalRepresentative n wideFactor u
                      velocityLower velocityUpper e a) := by
                rw [← Finset.sum_subset (Finset.subset_univ
                  (halfNonspreadLocalSiteSets n 1))]
                · apply Finset.sum_congr rfl
                  intro s hs
                  apply congrArg uniformProbability
                  funext e
                  simp [P, hs]
                · intro s _hs hnot
                  simp [P, hnot, uniformProbability]
          _ = halfNonspreadFactoredChooseContribution n 1 wideFactor u
                velocityLower velocityUpper := rfl

theorem eventually_uniformProbability_halfHasWide_and_not_narrow_lt
    (wideFactor narrowFactor u velocityLower velocityUpper : ℝ)
    (hwide : 0 < wideFactor) (hnarrow : 0 < narrowFactor)
    (hfactor : narrowFactor ≤ wideFactor) (hu : 0 < u)
    (hvelLower : 0 < velocityLower) (hvelUpper : 0 < velocityUpper)
    {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ n : ℕ in atTop,
      uniformProbability (fun e : SignVector (2 * n + 1) ↦
        HalfHasFactoredRepresentative n wideFactor u velocityLower velocityUpper e ∧
          ¬HalfHasFactoredRepresentative n narrowFactor u velocityLower velocityUpper e) <
        (wideFactor - narrowFactor) * ((6 * u / Real.pi) *
          blockVelocityMass velocityLower velocityUpper) + eps := by
  have hgood := halfGoodOuterDefectContribution_tendsto
    wideFactor narrowFactor u velocityLower velocityUpper hwide hnarrow hfactor
      hu hvelLower hvelUpper
  have hbad := halfNonspreadFactoredChooseContribution_one_tendsto_zero_wide
    wideFactor u velocityLower velocityUpper hwide.le hu.le hvelLower hvelUpper.le
  have hsum := hgood.add hbad
  have hsum' : Tendsto (fun n : ℕ ↦
      halfGoodOuterDefectContribution n wideFactor narrowFactor u
          velocityLower velocityUpper +
        halfNonspreadFactoredChooseContribution n 1 wideFactor u
          velocityLower velocityUpper) atTop
      (𝓝 ((wideFactor - narrowFactor) * ((6 * u / Real.pi) *
        blockVelocityMass velocityLower velocityUpper))) := by
    simpa using hsum
  have hevent := hsum'.eventually (Iio_mem_nhds
    (lt_add_of_pos_right
      ((wideFactor - narrowFactor) * ((6 * u / Real.pi) *
        blockVelocityMass velocityLower velocityUpper)) heps))
  filter_upwards [hevent] with n hn
  exact (uniformProbability_halfHasWide_and_not_narrow_le n wideFactor
    narrowFactor u velocityLower velocityUpper).trans_lt hn

end Odd

end Erdos525
