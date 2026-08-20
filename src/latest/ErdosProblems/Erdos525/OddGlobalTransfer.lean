import ErdosProblems.Erdos525.OddComparison

open scoped BigOperators Topology ComplexConjugate RealInnerProductSpace

namespace Erdos525

open Classical Filter Finset Set MeasureTheory

namespace Odd

lemma isFactoredTruncatedLocalRepresentative_mono_height
    (n : ℕ) (widthFactor u₁ u₂ velocityLower velocityUpper : ℝ)
    (hu : u₁ ≤ u₂) (e : SignVector (2 * n + 1))
    (a : Fin (localMeshSize n))
    (hrep : IsFactoredTruncatedLocalRepresentative n widthFactor u₁
      velocityLower velocityUpper e a) :
    IsFactoredTruncatedLocalRepresentative n widthFactor u₂
      velocityLower velocityUpper e a := by
  exact ⟨hrep.1, hrep.2.1, hrep.2.2.1.trans hu,
    hrep.2.2.2.1, hrep.2.2.2.2⟩

def HasRegularSmallMinimum
    (n : ℕ) (u velocityLower velocityUpper : ℝ)
    (e : SignVector (2 * n + 1)) : Prop :=
  ∃ t ∈ Set.Icc (0 : ℝ) (Real.pi * n),
    ‖eval n e t‖ = oddCenteredMin n e ∧
    oddCenteredMin n e ≤ u / n ∧
    (eval n e t * conj (velocity n e t)).re = 0 ∧
    IsSmooth n (4 * rigiditySmoothScale n) t ∧
    2 * velocityLower ≤ ‖velocity n e t‖ ∧
    ‖velocity n e t‖ ≤ velocityUpper / 2

def HasIrregularSmallMinimum
    (n : ℕ) (u velocityLower velocityUpper : ℝ)
    (e : SignVector (2 * n + 1)) : Prop :=
  oddCenteredMin n e ≤ u / n ∧
    ¬HasRegularSmallMinimum n u velocityLower velocityUpper e

theorem eventually_regularSmallMinimum_has_fixed_factored_representative
    (u v widthFactor velocityLower velocityUpper : ℝ)
    (huv : u < v) (hwidthFactor : 1 < widthFactor)
    (hvelocityLower : 0 < velocityLower)
    (hvelocityUpper : 0 < velocityUpper) :
    ∀ᶠ n : ℕ in atTop, ∀ e : SignVector (2 * n + 1),
      HasRegularSmallMinimum n u velocityLower velocityUpper e →
      HalfHasFactoredRepresentative n widthFactor v
        velocityLower velocityUpper e := by
  have hwidthDynamic : ∀ᶠ n : ℕ in atTop,
      minimumTransferWidthFactor n u velocityLower velocityUpper < widthFactor :=
    (minimumTransferWidthFactor_tendsto_one u velocityLower velocityUpper
      hvelocityLower.ne').eventually (Iio_mem_nhds hwidthFactor)
  have hheightDynamic : ∀ᶠ n : ℕ in atTop,
      minimumTransferHeight n u < v :=
    (minimumTransferHeight_tendsto u).eventually (Iio_mem_nhds huv)
  have herrorLower : ∀ᶠ n : ℕ in atTop,
      minimumVelocityTransferError n < velocityLower :=
    minimumVelocityTransferError_tendsto_zero.eventually
      (Iio_mem_nhds hvelocityLower)
  have herrorUpper : ∀ᶠ n : ℕ in atTop,
      minimumVelocityTransferError n < velocityUpper / 2 :=
    minimumVelocityTransferError_tendsto_zero.eventually
      (Iio_mem_nhds (half_pos hvelocityUpper))
  filter_upwards [Nat.eventually_pos,
      eventually_two_halfWidth_lt_pi_mul_rigiditySmoothScale,
      eventually_nearest_halfLocalMeshSite_smooth,
      hwidthDynamic, hheightDynamic, herrorLower, herrorUpper]
    with n hn hcell hsmooth hwidthN hheightN herrLower herrUpper
  intro e hregular
  rcases hregular with
    ⟨t, ht, hvalue, hsmall, hortho, htSmooth, htLower, htUpper⟩
  have htSmoothTwo : IsSmooth n (2 * rigiditySmoothScale n) t := by
    intro p hp1 hpFloor
    have hscale : 0 ≤ rigiditySmoothScale n := rigidityPower_nonneg n _
    have hpBound : p ≤ Nat.floor (4 * rigiditySmoothScale n) + 1 :=
      hpFloor.trans (Nat.add_le_add_right
        (Nat.floor_mono (by linarith)) 1)
    have hstrong := htSmooth p hp1 hpBound
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    exact (div_le_div_of_nonneg_right (by linarith) hnR.le).trans_lt hstrong
  rcases exists_smooth_factoredTruncatedLocalRepresentative_of_minimizer
      n hn e u velocityLower velocityUpper t hcell
      (hsmooth t htSmoothTwo) htSmoothTwo ht
      (by simpa [hvalue] using hsmall) hortho hvelocityLower
      (by linarith) (by linarith) with ⟨a, ha, hrep⟩
  refine ⟨a, ha, ?_⟩
  apply isFactoredTruncatedLocalRepresentative_mono_height n widthFactor
    (minimumTransferHeight n u) v velocityLower velocityUpper hheightN.le e a
  exact isFactoredTruncatedLocalRepresentative_mono n
    (minimumTransferWidthFactor n u velocityLower velocityUpper) widthFactor
      (minimumTransferHeight n u) velocityLower velocityUpper hwidthN.le e a hrep

lemma halfFactoredVoid_subset_tail_or_irregular_or_outerDefect
    (n : ℕ) (u v wideFactor narrowFactor velocityLower velocityUpper : ℝ)
    (htransfer : ∀ e : SignVector (2 * n + 1),
      HasRegularSmallMinimum n u velocityLower velocityUpper e →
      HalfHasFactoredRepresentative n wideFactor v
        velocityLower velocityUpper e)
    (e : SignVector (2 * n + 1))
    (hvoid : halfFactoredTruncatedLocalMinimumCount n narrowFactor v
      velocityLower velocityUpper e = 0) :
    u / n < oddCenteredMin n e ∨
      HasIrregularSmallMinimum n u velocityLower velocityUpper e ∨
      (HalfHasFactoredRepresentative n wideFactor v
          velocityLower velocityUpper e ∧
        ¬HalfHasFactoredRepresentative n narrowFactor v
          velocityLower velocityUpper e) := by
  by_cases htail : u / n < oddCenteredMin n e
  · exact Or.inl htail
  right
  have hsmall : oddCenteredMin n e ≤ u / n := le_of_not_gt htail
  by_cases hregular : HasRegularSmallMinimum n u velocityLower velocityUpper e
  · right
    refine ⟨htransfer e hregular, ?_⟩
    rw [halfHasFactoredRepresentative_iff_count_ne_zero]
    exact not_ne_iff.mpr hvoid
  · left
    exact ⟨hsmall, hregular⟩

theorem eventually_halfFactoredVoidProbability_le_tail_add_exceptions
    (u v wideFactor narrowFactor velocityLower velocityUpper : ℝ)
    (huv : u < v) (hwide : 1 < wideFactor)
    (hvelocityLower : 0 < velocityLower)
    (hvelocityUpper : 0 < velocityUpper) :
    ∀ᶠ n : ℕ in atTop,
      uniformProbability (fun e : SignVector (2 * n + 1) ↦
        halfFactoredTruncatedLocalMinimumCount n narrowFactor v
          velocityLower velocityUpper e = 0) ≤
        tail n u +
          uniformProbability (HasIrregularSmallMinimum n u
            velocityLower velocityUpper) +
          uniformProbability (fun e : SignVector (2 * n + 1) ↦
            HalfHasFactoredRepresentative n wideFactor v
                velocityLower velocityUpper e ∧
              ¬HalfHasFactoredRepresentative n narrowFactor v
                velocityLower velocityUpper e) := by
  filter_upwards [eventually_regularSmallMinimum_has_fixed_factored_representative
      u v wideFactor velocityLower velocityUpper huv hwide
        hvelocityLower hvelocityUpper] with n htransfer
  calc
    uniformProbability (fun e : SignVector (2 * n + 1) ↦
        halfFactoredTruncatedLocalMinimumCount n narrowFactor v
          velocityLower velocityUpper e = 0) ≤
      uniformProbability (fun e : SignVector (2 * n + 1) ↦
        u / n < oddCenteredMin n e ∨
          HasIrregularSmallMinimum n u velocityLower velocityUpper e ∨
          (HalfHasFactoredRepresentative n wideFactor v
              velocityLower velocityUpper e ∧
            ¬HalfHasFactoredRepresentative n narrowFactor v
              velocityLower velocityUpper e)) := by
        apply uniformProbability_mono
        exact halfFactoredVoid_subset_tail_or_irregular_or_outerDefect
          n u v wideFactor narrowFactor velocityLower velocityUpper htransfer
    _ ≤ uniformProbability (fun e : SignVector (2 * n + 1) ↦
          u / n < oddCenteredMin n e) +
        uniformProbability (fun e : SignVector (2 * n + 1) ↦
          HasIrregularSmallMinimum n u velocityLower velocityUpper e ∨
          (HalfHasFactoredRepresentative n wideFactor v
              velocityLower velocityUpper e ∧
            ¬HalfHasFactoredRepresentative n narrowFactor v
              velocityLower velocityUpper e)) :=
      uniformProbability_or_le_add _ _
    _ ≤ tail n u + uniformProbability (HasIrregularSmallMinimum n u
          velocityLower velocityUpper) +
        uniformProbability (fun e : SignVector (2 * n + 1) ↦
          HalfHasFactoredRepresentative n wideFactor v
              velocityLower velocityUpper e ∧
            ¬HalfHasFactoredRepresentative n narrowFactor v
              velocityLower velocityUpper e) := by
      unfold tail
      linarith [uniformProbability_or_le_add
        (fun e : SignVector (2 * n + 1) ↦
          HasIrregularSmallMinimum n u velocityLower velocityUpper e)
        (fun e : SignVector (2 * n + 1) ↦
          HalfHasFactoredRepresentative n wideFactor v
              velocityLower velocityUpper e ∧
            ¬HalfHasFactoredRepresentative n narrowFactor v
              velocityLower velocityUpper e)]

lemma irregularSmallMinimum_subset_elementaryExceptions
    (n : ℕ) (hn : 0 < n) (u velocityLower velocityUpper : ℝ)
    (e : SignVector (2 * n + 1))
    (hirregular : HasIrregularSmallMinimum n u
      velocityLower velocityUpper e) :
    HasBadArcSmallMinimum n u e ∨
      HasLowVelocitySmallMinimum n u (2 * velocityLower) e ∨
      HasHighVelocitySmallMinimum n u (velocityUpper / 2) e := by
  rcases exists_halfPeriod_oddCenteredMin_orthogonal n hn e with
    ⟨t, ht, hvalue, hortho⟩
  have hsmall := hirregular.1
  by_cases hsmooth : IsSmooth n (4 * rigiditySmoothScale n) t
  · by_cases hlow : 2 * velocityLower ≤ ‖velocity n e t‖
    · by_cases hupp : ‖velocity n e t‖ ≤ velocityUpper / 2
      · exfalso
        apply hirregular.2
        exact ⟨t, ht, hvalue, hsmall, hortho, hsmooth, hlow, hupp⟩
      · exact Or.inr (Or.inr ⟨t, ht, hvalue, hsmall, hsmooth,
          lt_of_not_ge hupp⟩)
    · exact Or.inr (Or.inl ⟨t, ht, hvalue, hsmall, hsmooth,
        lt_of_not_ge hlow⟩)
  · exact Or.inl ⟨t, ht, hvalue, hsmall, hsmooth⟩

theorem eventually_irregularSmallMinimum_probability_le_elementaryExceptions
    (u velocityLower velocityUpper : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      uniformProbability (HasIrregularSmallMinimum n u
          velocityLower velocityUpper) ≤
        uniformProbability (HasBadArcSmallMinimum n u) +
          uniformProbability (HasLowVelocitySmallMinimum n u
            (2 * velocityLower)) +
          uniformProbability (HasHighVelocitySmallMinimum n u
            (velocityUpper / 2)) := by
  filter_upwards [Nat.eventually_pos] with n hn
  let A : SignVector (2 * n + 1) → Prop := HasBadArcSmallMinimum n u
  let B : SignVector (2 * n + 1) → Prop :=
    HasLowVelocitySmallMinimum n u (2 * velocityLower)
  let C : SignVector (2 * n + 1) → Prop :=
    HasHighVelocitySmallMinimum n u (velocityUpper / 2)
  have hmono : uniformProbability (HasIrregularSmallMinimum n u
      velocityLower velocityUpper) ≤
      uniformProbability (fun e ↦ A e ∨ B e ∨ C e) := by
    apply uniformProbability_mono
    intro e he
    simpa only [A, B, C] using
      irregularSmallMinimum_subset_elementaryExceptions n hn u
        velocityLower velocityUpper e he
  calc
    uniformProbability (HasIrregularSmallMinimum n u
        velocityLower velocityUpper) ≤
      uniformProbability (fun e ↦ A e ∨ B e ∨ C e) := hmono
    _ ≤ uniformProbability A + uniformProbability (fun e ↦ B e ∨ C e) :=
      uniformProbability_or_le_add _ _
    _ ≤ uniformProbability A +
        (uniformProbability B + uniformProbability C) := by
      gcongr
      exact uniformProbability_or_le_add _ _
    _ = _ := by simp only [A, B, C]; ring

end Odd

end Erdos525
