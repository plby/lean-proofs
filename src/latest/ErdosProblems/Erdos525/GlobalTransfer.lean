import ErdosProblems.Erdos525.Comparison

open scoped BigOperators ENNReal NNReal Topology Real ComplexConjugate
open MeasureTheory Filter Set

namespace Erdos525

lemma isLocalRepresentative_of_isTruncatedLocalRepresentative
    {n : ℕ} {u velocityLower velocityUpper : ℝ}
    {e : SignVector (2 * n)} {a : Fin (localMeshSize n)}
    (h : IsTruncatedLocalRepresentative n u velocityLower velocityUpper e a) :
    IsLocalRepresentative n u e a := h.1

theorem eventually_centeredTail_le_halfTruncatedVoid
    (u v velocityLower velocityUpper : ℝ) (hvu : v < u) :
    ∀ᶠ n : ℕ in atTop,
      centeredTail n u ≤
        uniformProbability (fun e : SignVector (2 * n) ↦
          halfTruncatedLocalMinimumCount n v velocityLower velocityUpper e = 0) := by
  have herr : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) * localMeshTaylorError n < u - v :=
    scaled_localMeshTaylorError_tendsto_zero.eventually
      (Iio_mem_nhds (sub_pos.mpr hvu))
  filter_upwards [Nat.eventually_pos, herr] with n hn herrn
  unfold centeredTail
  apply uniformProbability_mono
  intro e htail
  by_contra hcount
  have hhas : HalfHasTruncatedRepresentative n v velocityLower velocityUpper e :=
    (halfHasTruncatedRepresentative_iff_count_ne_zero n v velocityLower
      velocityUpper e).2 hcount
  rcases hhas with ⟨a, _ha, hrep⟩
  have hmin := (isLocalRepresentative_of_isTruncatedLocalRepresentative hrep).centeredMin_le hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hscaled : v / n + localMeshTaylorError n < u / n := by
    apply (lt_div_iff₀ hnR).2
    calc
      (v / n + localMeshTaylorError n) * n =
          v + n * localMeshTaylorError n := by
        field_simp [hnR.ne']
      _ < u := by linarith
  exact (not_lt_of_ge hmin) (htail.trans' hscaled)

theorem centeredTail_limsup_le_cutoffIntensity
    (u velocityLower velocityUpper : ℝ)
    (hu : 0 < u) (hvelLower : 0 < velocityLower)
    (hvelUpper : 0 < velocityUpper) {b : ℝ}
    (hb : Real.exp (-((6 * u / Real.pi) *
      blockVelocityMass velocityLower velocityUpper)) < b) :
    ∀ᶠ n : ℕ in atTop, centeredTail n u < b := by
  let vSeq : ℕ → ℝ := fun k ↦ u - 1 / (k + 1 : ℝ)
  have hone : Tendsto (fun k : ℕ ↦ (1 : ℝ) / (k + 1 : ℝ))
      atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hvSeq : Tendsto vSeq atTop (𝓝 u) := by
    simpa [vSeq] using tendsto_const_nhds.sub hone
  have hlinear : Tendsto (fun k : ℕ ↦
      -((6 * vSeq k / Real.pi) *
        blockVelocityMass velocityLower velocityUpper)) atTop
      (𝓝 (-((6 * u / Real.pi) *
        blockVelocityMass velocityLower velocityUpper))) := by
    exact (((tendsto_const_nhds.mul hvSeq).div_const Real.pi).mul_const
      (blockVelocityMass velocityLower velocityUpper)).neg
  have hexp : Tendsto (fun k : ℕ ↦
      Real.exp (-((6 * vSeq k / Real.pi) *
        blockVelocityMass velocityLower velocityUpper))) atTop
      (𝓝 (Real.exp (-((6 * u / Real.pi) *
        blockVelocityMass velocityLower velocityUpper)))) := by
    exact Real.continuous_exp.continuousAt.tendsto.comp hlinear
  have hsmall : ∀ᶠ k : ℕ in atTop,
      Real.exp (-((6 * vSeq k / Real.pi) *
        blockVelocityMass velocityLower velocityUpper)) < b :=
    hexp.eventually (Iio_mem_nhds hb)
  have hpos : ∀ᶠ k : ℕ in atTop, 0 < vSeq k :=
    hvSeq.eventually (Ioi_mem_nhds hu)
  rcases (hsmall.and hpos).exists with ⟨k, hsmallk, hposk⟩
  have hvu : vSeq k < u := by
    dsimp [vSeq]
    have : (0 : ℝ) < 1 / (k + 1 : ℝ) := by positivity
    linarith
  have htailLe := eventually_centeredTail_le_halfTruncatedVoid
    u (vSeq k) velocityLower velocityUpper hvu
  have hvoid := uniformProbability_halfTruncatedLocalMinimumCount_eq_zero_tendsto
    (vSeq k) velocityLower velocityUpper hposk hvelLower hvelUpper
  have hvoidLt : ∀ᶠ n : ℕ in atTop,
      uniformProbability (fun e : SignVector (2 * n) ↦
        halfTruncatedLocalMinimumCount n (vSeq k) velocityLower
          velocityUpper e = 0) < b :=
    hvoid.eventually (Iio_mem_nhds hsmallk)
  filter_upwards [htailLe, hvoidLt] with n hle hlt
  exact hle.trans_lt hlt

lemma halfScaledExhaustedBlockMass_tendsto (u : ℝ) :
    Tendsto (fun k : ℕ ↦
      (6 * u / Real.pi) *
        blockVelocityMass (1 / (k + 1 : ℝ)) (k + 1 : ℝ))
      atTop (𝓝 (2 * rate * u)) := by
  have h := (scaled_exhaustedBlockMass_tendsto u).const_mul (1 / 2 : ℝ)
  convert h using 1 <;> ring

theorem centeredTail_limsup_le
    (u : ℝ) (hu : 0 < u) {b : ℝ}
    (hb : Real.exp (-2 * rate * u) < b) :
    ∀ᶠ n : ℕ in atTop, centeredTail n u < b := by
  have hmass := halfScaledExhaustedBlockMass_tendsto u
  have hexp : Tendsto (fun k : ℕ ↦
      Real.exp (-((6 * u / Real.pi) *
        blockVelocityMass (1 / (k + 1 : ℝ)) (k + 1 : ℝ))))
      atTop (𝓝 (Real.exp (-2 * rate * u))) :=
    Real.continuous_exp.continuousAt.tendsto.comp (by
      convert hmass.neg using 1 <;> ring)
  have hlt : ∀ᶠ k : ℕ in atTop,
      Real.exp (-((6 * u / Real.pi) *
        blockVelocityMass (1 / (k + 1 : ℝ)) (k + 1 : ℝ))) < b :=
    hexp.eventually (Iio_mem_nhds hb)
  rcases hlt.exists with ⟨k, hk⟩
  exact centeredTail_limsup_le_cutoffIntensity u
    (1 / (k + 1 : ℝ)) (k + 1 : ℝ) hu (by positivity) (by positivity) hk

lemma isFactoredTruncatedLocalRepresentative_mono_height
    (n : ℕ) (widthFactor u₁ u₂ velocityLower velocityUpper : ℝ)
    (hu : u₁ ≤ u₂) (e : SignVector (2 * n))
    (a : Fin (localMeshSize n))
    (hrep : IsFactoredTruncatedLocalRepresentative n widthFactor u₁
      velocityLower velocityUpper e a) :
    IsFactoredTruncatedLocalRepresentative n widthFactor u₂
      velocityLower velocityUpper e a := by
  exact ⟨hrep.1, hrep.2.1, hrep.2.2.1.trans hu,
    hrep.2.2.2.1, hrep.2.2.2.2⟩

def HasRegularSmallMinimum
    (n : ℕ) (u velocityLower velocityUpper : ℝ)
    (e : SignVector (2 * n)) : Prop :=
  ∃ t ∈ Set.Icc (0 : ℝ) (Real.pi * n),
    ‖rescaledCenteredEval n e t‖ = centeredMin n e ∧
    centeredMin n e ≤ u / n ∧
    (rescaledCenteredEval n e t *
      conj (rescaledCenteredVelocity n e t)).re = 0 ∧
    IsSmooth n (4 * rigiditySmoothScale n) t ∧
    velocityLower + minimumVelocityTransferError n ≤
      ‖rescaledCenteredVelocity n e t‖ ∧
    ‖rescaledCenteredVelocity n e t‖ ≤
      velocityUpper - minimumVelocityTransferError n ∧
    ¬HasHighMeshAcceleration n e

def HasIrregularSmallMinimum
    (n : ℕ) (u velocityLower velocityUpper : ℝ)
    (e : SignVector (2 * n)) : Prop :=
  centeredMin n e ≤ u / n ∧
    ¬HasRegularSmallMinimum n u velocityLower velocityUpper e

lemma regularSmallMinimum_has_factored_representative
    (n : ℕ) (hn : 0 < n) (u velocityLower velocityUpper : ℝ)
    (hwidth : 2 * localMeshHalfWidth n <
      Real.pi * (2 * rigiditySmoothScale n))
    (hnearestSmooth : ∀ t : ℝ,
      IsSmooth n (2 * rigiditySmoothScale n) t →
      ∀ a : Fin (localMeshSize n),
        |t - localMeshPoint n a| ≤ localMeshHalfWidth n →
        IsSmooth n (rigiditySmoothScale n) (localMeshPoint n a))
    (hvelocityLower : 0 < velocityLower)
    (e : SignVector (2 * n))
    (hregular : HasRegularSmallMinimum n u velocityLower velocityUpper e) :
    HalfHasFactoredRepresentative n
      (minimumTransferWidthFactor n u velocityLower velocityUpper)
      (minimumTransferHeight n u) velocityLower velocityUpper e := by
  rcases hregular with
    ⟨t, ht, hvalue, hsmall, hortho, htSmooth, htLower, htUpper, hacc⟩
  have htSmoothTwo : IsSmooth n (2 * rigiditySmoothScale n) t := by
    intro p hp1 hpFloor
    have hpBound : p ≤ Nat.floor (4 * rigiditySmoothScale n) + 1 := by
      have hscale : 0 ≤ rigiditySmoothScale n := by
        unfold rigiditySmoothScale
        exact rigidityPower_nonneg n _
      exact hpFloor.trans (Nat.add_le_add_right
        (Nat.floor_mono (by linarith)) 1)
    have hstrong := htSmooth p hp1 hpBound
    have hscale : 0 ≤ rigiditySmoothScale n := by
      unfold rigiditySmoothScale
      exact rigidityPower_nonneg n _
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    exact (div_le_div_of_nonneg_right (by linarith) hnR.le).trans_lt hstrong
  apply exists_smooth_factoredTruncatedLocalRepresentative_of_minimizer
    n hn e hacc u velocityLower velocityUpper t hwidth
      (hnearestSmooth t htSmoothTwo) htSmoothTwo ht
  · simpa [hvalue] using hsmall
  · exact hortho
  · exact hvelocityLower
  · exact htLower
  · exact htUpper

theorem eventually_regularSmallMinimum_has_fixed_factored_representative
    (u v widthFactor velocityLower velocityUpper : ℝ)
    (huv : u < v) (hwidthFactor : 1 < widthFactor)
    (hvelocityLower : 0 < velocityLower) :
    ∀ᶠ n : ℕ in atTop, ∀ e : SignVector (2 * n),
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
  filter_upwards [Nat.eventually_pos,
      eventually_two_halfWidth_lt_pi_mul_rigiditySmoothScale,
      eventually_nearest_halfLocalMeshSite_smooth,
      hwidthDynamic, hheightDynamic]
    with n hn hcell hsmooth hwidthN hheightN
  intro e hregular
  rcases regularSmallMinimum_has_factored_representative n hn u
      velocityLower velocityUpper hcell hsmooth hvelocityLower e hregular with
    ⟨a, ha, hrep⟩
  refine ⟨a, ha, ?_⟩
  apply isFactoredTruncatedLocalRepresentative_mono_height n widthFactor
    (minimumTransferHeight n u) v velocityLower velocityUpper hheightN.le e a
  exact isFactoredTruncatedLocalRepresentative_mono n
    (minimumTransferWidthFactor n u velocityLower velocityUpper) widthFactor
      (minimumTransferHeight n u) velocityLower velocityUpper hwidthN.le e a hrep

lemma halfTruncatedVoid_subset_tail_or_irregular_or_outerDefect
    (n : ℕ) (u v widthFactor velocityLower velocityUpper : ℝ)
    (htransfer : ∀ e : SignVector (2 * n),
      HasRegularSmallMinimum n u velocityLower velocityUpper e →
      HalfHasFactoredRepresentative n widthFactor v
        velocityLower velocityUpper e)
    (e : SignVector (2 * n))
    (hvoid : halfTruncatedLocalMinimumCount n v velocityLower velocityUpper e = 0) :
    u / n < centeredMin n e ∨
      HasIrregularSmallMinimum n u velocityLower velocityUpper e ∨
      (HalfHasFactoredRepresentative n widthFactor v
          velocityLower velocityUpper e ∧
        ¬HalfHasTruncatedRepresentative n v velocityLower velocityUpper e) := by
  by_cases htail : u / n < centeredMin n e
  · exact Or.inl htail
  right
  have hsmall : centeredMin n e ≤ u / n := le_of_not_gt htail
  by_cases hregular : HasRegularSmallMinimum n u velocityLower velocityUpper e
  · right
    refine ⟨htransfer e hregular, ?_⟩
    rw [halfHasTruncatedRepresentative_iff_count_ne_zero]
    exact not_ne_iff.mpr hvoid
  · left
    exact ⟨hsmall, hregular⟩

theorem eventually_halfTruncatedVoidProbability_le_tail_add_exceptions
    (u v widthFactor velocityLower velocityUpper : ℝ)
    (huv : u < v) (hwidthFactor : 1 < widthFactor)
    (hvelocityLower : 0 < velocityLower) :
    ∀ᶠ n : ℕ in atTop,
      uniformProbability (fun e : SignVector (2 * n) ↦
          halfTruncatedLocalMinimumCount n v velocityLower velocityUpper e = 0) ≤
        centeredTail n u +
          uniformProbability (HasIrregularSmallMinimum n u
            velocityLower velocityUpper) +
          uniformProbability (fun e : SignVector (2 * n) ↦
            HalfHasFactoredRepresentative n widthFactor v
                velocityLower velocityUpper e ∧
              ¬HalfHasTruncatedRepresentative n v
                velocityLower velocityUpper e) := by
  filter_upwards [
    eventually_regularSmallMinimum_has_fixed_factored_representative
      u v widthFactor velocityLower velocityUpper huv hwidthFactor
        hvelocityLower] with n htransfer
  calc
    uniformProbability (fun e : SignVector (2 * n) ↦
        halfTruncatedLocalMinimumCount n v velocityLower velocityUpper e = 0) ≤
      uniformProbability (fun e : SignVector (2 * n) ↦
        u / n < centeredMin n e ∨
          HasIrregularSmallMinimum n u velocityLower velocityUpper e ∨
          (HalfHasFactoredRepresentative n widthFactor v
              velocityLower velocityUpper e ∧
            ¬HalfHasTruncatedRepresentative n v
              velocityLower velocityUpper e)) := by
        apply uniformProbability_mono
        exact halfTruncatedVoid_subset_tail_or_irregular_or_outerDefect
          n u v widthFactor velocityLower velocityUpper htransfer
    _ ≤ uniformProbability (fun e : SignVector (2 * n) ↦
          u / n < centeredMin n e) +
        uniformProbability (fun e : SignVector (2 * n) ↦
          HasIrregularSmallMinimum n u velocityLower velocityUpper e ∨
          (HalfHasFactoredRepresentative n widthFactor v
              velocityLower velocityUpper e ∧
            ¬HalfHasTruncatedRepresentative n v
              velocityLower velocityUpper e)) :=
      uniformProbability_or_le_add _ _
    _ ≤ centeredTail n u +
          uniformProbability (HasIrregularSmallMinimum n u
            velocityLower velocityUpper) +
          uniformProbability (fun e : SignVector (2 * n) ↦
            HalfHasFactoredRepresentative n widthFactor v
                velocityLower velocityUpper e ∧
              ¬HalfHasTruncatedRepresentative n v
                velocityLower velocityUpper e) := by
      unfold centeredTail
      linarith [uniformProbability_or_le_add
        (fun e : SignVector (2 * n) ↦
          HasIrregularSmallMinimum n u velocityLower velocityUpper e)
        (fun e : SignVector (2 * n) ↦
          HalfHasFactoredRepresentative n widthFactor v
              velocityLower velocityUpper e ∧
            ¬HalfHasTruncatedRepresentative n v
              velocityLower velocityUpper e)]

def HasBadArcSmallMinimum (n : ℕ) (u : ℝ)
    (e : SignVector (2 * n)) : Prop :=
  ∃ t ∈ Set.Icc (0 : ℝ) (Real.pi * n),
    ‖rescaledCenteredEval n e t‖ = centeredMin n e ∧
    centeredMin n e ≤ u / n ∧
    ¬IsSmooth n (4 * rigiditySmoothScale n) t

def HasLowVelocitySmallMinimum
    (n : ℕ) (u velocityLower : ℝ) (e : SignVector (2 * n)) : Prop :=
  ∃ t ∈ Set.Icc (0 : ℝ) (Real.pi * n),
    ‖rescaledCenteredEval n e t‖ = centeredMin n e ∧
    centeredMin n e ≤ u / n ∧
    IsSmooth n (4 * rigiditySmoothScale n) t ∧
    ‖rescaledCenteredVelocity n e t‖ <
      velocityLower + minimumVelocityTransferError n

def HasHighVelocitySmallMinimum
    (n : ℕ) (u velocityUpper : ℝ) (e : SignVector (2 * n)) : Prop :=
  ∃ t ∈ Set.Icc (0 : ℝ) (Real.pi * n),
    ‖rescaledCenteredEval n e t‖ = centeredMin n e ∧
    centeredMin n e ≤ u / n ∧
    IsSmooth n (4 * rigiditySmoothScale n) t ∧
    velocityUpper - minimumVelocityTransferError n <
      ‖rescaledCenteredVelocity n e t‖

lemma irregularSmallMinimum_subset_elementaryExceptions
    (n : ℕ) (hn : 0 < n) (u velocityLower velocityUpper : ℝ)
    (e : SignVector (2 * n))
    (hirregular : HasIrregularSmallMinimum n u
      velocityLower velocityUpper e) :
    HasBadArcSmallMinimum n u e ∨
      HasLowVelocitySmallMinimum n u velocityLower e ∨
      HasHighVelocitySmallMinimum n u velocityUpper e ∨
      HasHighMeshAcceleration n e := by
  rcases exists_halfPeriod_centeredMin_orthogonal n hn e with
    ⟨t, ht, hvalue, hortho⟩
  have hsmall := hirregular.1
  by_cases hsmooth : IsSmooth n (4 * rigiditySmoothScale n) t
  · by_cases hlow : velocityLower + minimumVelocityTransferError n ≤
        ‖rescaledCenteredVelocity n e t‖
    · by_cases hupp : ‖rescaledCenteredVelocity n e t‖ ≤
          velocityUpper - minimumVelocityTransferError n
      · by_cases hacc : HasHighMeshAcceleration n e
        · exact Or.inr (Or.inr (Or.inr hacc))
        · exfalso
          apply hirregular.2
          exact ⟨t, ht, hvalue, hsmall, hortho, hsmooth, hlow, hupp, hacc⟩
      · exact Or.inr (Or.inr (Or.inl ⟨t, ht, hvalue, hsmall, hsmooth,
          lt_of_not_ge hupp⟩))
    · exact Or.inr (Or.inl ⟨t, ht, hvalue, hsmall, hsmooth,
        lt_of_not_ge hlow⟩)
  · exact Or.inl ⟨t, ht, hvalue, hsmall, hsmooth⟩

theorem eventually_irregularSmallMinimum_probability_le_elementaryExceptions
    (u velocityLower velocityUpper : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      uniformProbability (HasIrregularSmallMinimum n u
          velocityLower velocityUpper) ≤
        uniformProbability (HasBadArcSmallMinimum n u) +
          uniformProbability (HasLowVelocitySmallMinimum n u velocityLower) +
          uniformProbability (HasHighVelocitySmallMinimum n u velocityUpper) +
          uniformProbability (HasHighMeshAcceleration n) := by
  filter_upwards [Nat.eventually_pos] with n hn
  let A : SignVector (2 * n) → Prop := HasBadArcSmallMinimum n u
  let B : SignVector (2 * n) → Prop :=
    HasLowVelocitySmallMinimum n u velocityLower
  let C : SignVector (2 * n) → Prop :=
    HasHighVelocitySmallMinimum n u velocityUpper
  let D : SignVector (2 * n) → Prop := HasHighMeshAcceleration n
  have hmono : uniformProbability (HasIrregularSmallMinimum n u
      velocityLower velocityUpper) ≤
      uniformProbability (fun e ↦ A e ∨ B e ∨ C e ∨ D e) := by
    apply uniformProbability_mono
    intro e he
    simpa only [A, B, C, D] using
      irregularSmallMinimum_subset_elementaryExceptions n hn u
        velocityLower velocityUpper e he
  have hA := uniformProbability_or_le_add A
    (fun e ↦ B e ∨ C e ∨ D e)
  have hB := uniformProbability_or_le_add B (fun e ↦ C e ∨ D e)
  have hC := uniformProbability_or_le_add C D
  calc
    uniformProbability (HasIrregularSmallMinimum n u
        velocityLower velocityUpper) ≤
      uniformProbability (fun e ↦ A e ∨ B e ∨ C e ∨ D e) := hmono
    _ ≤ uniformProbability A +
        uniformProbability (fun e ↦ B e ∨ C e ∨ D e) := hA
    _ ≤ uniformProbability A +
        (uniformProbability B +
          uniformProbability (fun e ↦ C e ∨ D e)) :=
      add_le_add_right hB (uniformProbability A)
    _ ≤ uniformProbability A +
        (uniformProbability B +
          (uniformProbability C + uniformProbability D)) :=
      add_le_add_right
        (add_le_add_right hC (uniformProbability B)) (uniformProbability A)
    _ = uniformProbability (HasBadArcSmallMinimum n u) +
          uniformProbability (HasLowVelocitySmallMinimum n u velocityLower) +
          uniformProbability (HasHighVelocitySmallMinimum n u velocityUpper) +
          uniformProbability (HasHighMeshAcceleration n) := by
      simp only [A, B, C, D]
      ring

end Erdos525
