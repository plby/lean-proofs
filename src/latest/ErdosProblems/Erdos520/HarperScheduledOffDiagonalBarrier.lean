import ErdosProblems.Erdos520.HarperScheduledOffDiagonalCDF
import ErdosProblems.Erdos520.HarperScheduledGaussianSlicing

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal

namespace Erdos
namespace Problem520

noncomputable section

/-!
# Off-diagonal reverse-log barrier probability

The generic varying-Gaussian walk theorem only needs a positive lower
variance bound and the coarse upper bound `sqrt variance ≤ 1`.  Thus the
off-diagonal window `[1/4,1/2]` gives the same numerical constant `64` as
the diagonal specialization.  Composing this with the fixed-`exp 2`
finite-slicing theorem yields the reverse-log barrier endpoint required by
the restricted first-moment argument.
-/

/-- Finite-vector form of the generic varying-Gaussian walk estimate. -/
theorem gaussianVarianceWalk_probability_le_fin_of_lower_of_sqrt_le
    (lo : ℝ≥0) (hlo : lo ≠ 0) (n : ℕ) (hn : 0 < n)
    (variance : Fin n → ℝ≥0) {x : ℝ} (hx : 0 ≤ x)
    (hlower : ∀ i, lo ≤ variance i)
    (hupper : ∀ i, Real.sqrt (variance i : ℝ) ≤ 1) :
    (Measure.pi (fun i : Fin n ↦ gaussianReal 0 (variance i))).real
        (gaussianWalkSurvivalSet n x) ≤
      (32 / Real.sqrt (lo : ℝ)) * (x + 2) /
        Real.sqrt (n : ℝ) := by
  let vs : List ℝ≥0 := List.ofFn variance
  have hne : vs ≠ [] := by
    intro hnil
    have : vs.length = 0 := by simp [hnil]
    simp only [vs, List.length_ofFn] at this
    omega
  have hlower' : ∀ v ∈ vs, lo ≤ v := by
    exact (List.forall_mem_ofFn_iff).2 hlower
  have hupper' : ∀ v ∈ vs, Real.sqrt (v : ℝ) ≤ 1 := by
    exact (List.forall_mem_ofFn_iff).2 hupper
  have h := gaussianVarianceWalkSurvivalProbability_le
    lo hlo vs hne hx hlower' hupper'
  rw [gaussianVarianceWalkSurvivalProbability_eq_measureReal vs hx] at h
  have hvlen : vs.length = n := by simp [vs]
  let e : Fin vs.length ≃ Fin n := finCongr hvlen
  let E : (Fin vs.length → ℝ) ≃ᵐ (Fin n → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ : Fin n ↦ ℝ) e
  have hcoord (i : Fin vs.length) : vs.get i = variance (e i) := by
    dsimp only [vs, e]
    rw [List.get_ofFn]
    congr 1
  have hsource : gaussianVarianceWalkMeasure vs =
      Measure.pi (fun i : Fin vs.length ↦
        gaussianReal 0 (variance (e i))) := by
    unfold gaussianVarianceWalkMeasure
    congr 1
    funext i
    rw [hcoord]
  have hmp := measurePreserving_piCongrLeft
    (μ := fun i : Fin n ↦ gaussianReal 0 (variance i)) e
  have hE (omega : Fin vs.length → ℝ) :
      E omega = fun j ↦ omega (e.symm j) := by
    funext j
    obtain ⟨i, rfl⟩ := e.surjective j
    change (MeasurableEquiv.piCongrLeft (fun _ : Fin n ↦ ℝ) e)
      omega (e i) = omega i
    exact MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ : Fin n ↦ ℝ) e omega i
  have hpre : E ⁻¹' gaussianWalkSurvivalSet n x =
      gaussianWalkSurvivalSet vs.length x := by
    ext omega
    simp only [Set.mem_preimage, gaussianWalkSurvivalSet, mem_setOf_eq]
    rw [hE]
    exact gaussianWalkSurvives_reindex_finCongr hvlen x omega
  have htransport :
      (Measure.pi (fun i : Fin n ↦ gaussianReal 0 (variance i))).real
          (gaussianWalkSurvivalSet n x) =
        (gaussianVarianceWalkMeasure vs).real
          (gaussianWalkSurvivalSet vs.length x) := by
    rw [← hmp.map_eq]
    rw [map_measureReal_apply E.measurable
      (measurableSet_gaussianWalkSurvivalSet n hx)]
    rw [hpre, hsource]
  rw [htransport]
  simpa only [vs, List.length_ofFn] using! h

/-- Varying centered Gaussians with variances in `[1/4,1/2]` satisfy the
same `64 (x+2) / sqrt n` ballot estimate used on the diagonal. -/
theorem gaussianVarianceWalk_quarter_half_probability_le_fin
    (n : ℕ) (hn : 0 < n) (variance : Fin n → ℝ≥0)
    {x : ℝ} (hx : 0 ≤ x)
    (hlower : ∀ i, (1 / 4 : ℝ≥0) ≤ variance i)
    (hupper : ∀ i, variance i ≤ (1 / 2 : ℝ≥0)) :
    (Measure.pi (fun i : Fin n ↦ gaussianReal 0 (variance i))).real
        (gaussianWalkSurvivalSet n x) ≤
      64 * (x + 2) / Real.sqrt (n : ℝ) := by
  have hsqrtUpper : ∀ i, Real.sqrt (variance i : ℝ) ≤ 1 := by
    intro i
    apply (Real.sqrt_le_iff).2
    constructor
    · norm_num
    · have hv : (variance i : ℝ) ≤ (1 / 2 : ℝ) := by
        exact_mod_cast hupper i
      have : (variance i : ℝ) ≤ 1 := hv.trans (by norm_num)
      simpa using! this
  have hmain := gaussianVarianceWalk_probability_le_fin_of_lower_of_sqrt_le
    (1 / 4 : ℝ≥0) (by norm_num) n hn variance hx hlower hsqrtUpper
  have hsqrtlo : (1 / 2 : ℝ) ≤
      Real.sqrt (((1 / 4 : ℝ≥0) : ℝ)) := by
    rw [show (((1 / 4 : ℝ≥0) : ℝ)) = (1 / 4 : ℝ) by
      norm_num [NNReal.coe_div]]
    have hs0 := Real.sqrt_nonneg (1 / 4 : ℝ)
    have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 4)
    nlinarith
  have hsqrtpos : 0 < Real.sqrt (((1 / 4 : ℝ≥0) : ℝ)) := by
    apply Real.sqrt_pos.2
    norm_num [NNReal.coe_div]
  have hconst :
      32 / Real.sqrt (((1 / 4 : ℝ≥0) : ℝ)) ≤ 64 := by
    apply (div_le_iff₀ hsqrtpos).2
    nlinarith
  have ha : 0 ≤ x + 2 := by linarith
  have hden : 0 < Real.sqrt (n : ℝ) := by
    exact Real.sqrt_pos.2 (by exact_mod_cast hn)
  exact hmain.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hconst ha) hden.le)

/-- The variance vector of consecutive scheduled blocks evaluated at a
possibly different nearby height in every coordinate. -/
noncomputable def harperScheduledOffDiagonalGaussianVariance
    (y start n : ℕ) (t : ℝ) (u : Fin n → ℝ) (i : Fin n) : ℝ≥0 :=
  harperLinearBlockVarianceNNReal y
    (harperScheduledPrimeBlock y (start + (i : ℕ))) t (u i)

noncomputable def harperScheduledOffDiagonalGaussianProductMeasure
    (y start n : ℕ) (t : ℝ) (u : Fin n → ℝ) :
    Measure (Fin n → ℝ) :=
  Measure.pi fun i ↦ gaussianReal 0
    (harperScheduledOffDiagonalGaussianVariance y start n t u i)

instance harperScheduledOffDiagonalGaussianProductMeasure_isProbabilityMeasure
    (y start n : ℕ) (t : ℝ) (u : Fin n → ℝ) :
    IsProbabilityMeasure
      (harperScheduledOffDiagonalGaussianProductMeasure y start n t u) := by
  unfold harperScheduledOffDiagonalGaussianProductMeasure
  infer_instance

/-- The coordinatewise scale-displacement condition puts the complete
off-diagonal Gaussian variance vector in `[1/4,1/2]`. -/
theorem exists_eventually_harperScheduledOffDiagonalGaussianVariance_quarter_half
    (M : ℕ) :
    ∃ J : ℕ, ∀ start : ℕ, J ≤ start → ∀ n y : ℕ,
      harperBlockEndpoint (start + n) ≤ y →
        ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M → ∀ u : Fin n → ℝ,
          (∀ i : Fin n,
            |u i - t| *
                Real.log (harperBlockEndpoint
                  (start + (i : ℕ) + 1) : ℝ) ≤ (1 / 64 : ℝ)) →
            ∀ i : Fin n,
              (1 / 4 : ℝ≥0) ≤
                  harperScheduledOffDiagonalGaussianVariance
                    y start n t u i ∧
                harperScheduledOffDiagonalGaussianVariance
                    y start n t u i ≤ (1 / 2 : ℝ≥0) := by
  obtain ⟨J, hJ⟩ :=
    exists_eventually_harperScheduledOffDiagonalVariance_quarter_half M
  refine ⟨J, ?_⟩
  intro start hstart n y hy t htLower htUpper u hscale i
  have hindex : J ≤ start + (i : ℕ) := by omega
  have hendpoint :
      harperBlockEndpoint (start + (i : ℕ) + 1) ≤ y := by
    exact (monotone_harperBlockEndpoint (by omega)).trans hy
  have hv := hJ (start + (i : ℕ)) hindex y hendpoint
    t htLower htUpper (u i) (hscale i)
  constructor
  · exact_mod_cast hv.1.le
  · exact_mod_cast hv.2.le

/-- Ballot estimate for the scheduled off-diagonal Gaussian product. -/
theorem exists_eventually_harperScheduledOffDiagonalGaussianWalk_probability_le
    (M : ℕ) :
    ∃ J : ℕ, ∀ start : ℕ, J ≤ start → ∀ n : ℕ, 0 < n → ∀ y : ℕ,
      harperBlockEndpoint (start + n) ≤ y →
        ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M → ∀ u : Fin n → ℝ,
          (∀ i : Fin n,
            |u i - t| *
                Real.log (harperBlockEndpoint
                  (start + (i : ℕ) + 1) : ℝ) ≤ (1 / 64 : ℝ)) →
            ∀ x : ℝ, 0 ≤ x →
              (harperScheduledOffDiagonalGaussianProductMeasure
                y start n t u).real (gaussianWalkSurvivalSet n x) ≤
                64 * (x + 2) / Real.sqrt (n : ℝ) := by
  obtain ⟨J, hJ⟩ :=
    exists_eventually_harperScheduledOffDiagonalGaussianVariance_quarter_half M
  refine ⟨J, ?_⟩
  intro start hstart n hn y hy t htLower htUpper u hscale x hx
  have hvar := hJ start hstart n y hy t htLower htUpper u hscale
  have h := gaussianVarianceWalk_quarter_half_probability_le_fin
    n hn (harperScheduledOffDiagonalGaussianVariance y start n t u) hx
    (fun i ↦ (hvar i).1) (fun i ↦ (hvar i).2)
  simpa only [harperScheduledOffDiagonalGaussianProductMeasure] using! h

/-- The expanded normalized reverse-log barrier has probability
`64 (x+4) / sqrt n` under the off-diagonal Gaussian product.  The logarithmic
shape is nonpositive and the cumulative slicing width costs only `2`. -/
theorem exists_eventually_harperScheduledOffDiagonalGaussianWalk_expandedReverseLogBarrier_probability_le
    (M : ℕ) :
    ∃ J : ℕ, ∀ start : ℕ, J ≤ start → ∀ n : ℕ, 0 < n → ∀ y : ℕ,
      harperBlockEndpoint (start + n) ≤ y →
        ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M → ∀ u : Fin n → ℝ,
          (∀ i : Fin n,
            |u i - t| *
                Real.log (harperBlockEndpoint
                  (start + (i : ℕ) + 1) : ℝ) ≤ (1 / 64 : ℝ)) →
            ∀ x c : ℝ, 0 ≤ x → 0 ≤ c → ∀ lower : Fin n → ℝ,
              (harperScheduledOffDiagonalGaussianProductMeasure
                y start n t u).real
                  (harperExpandedPartialSumBarrierSet lower
                    (harperNormalizedReverseLogBarrier n x c)
                    (harperScheduledRelativeCellWidth start n)) ≤
                64 * (x + 4) / Real.sqrt (n : ℝ) := by
  obtain ⟨J, hJ⟩ :=
    exists_eventually_harperScheduledOffDiagonalGaussianWalk_probability_le M
  refine ⟨J, ?_⟩
  intro start hstart n hn y hy t htLower htUpper u hscale
    x c hx hc lower
  have hbarrier : ∀ k : Fin n,
      harperNormalizedReverseLogBarrier n x c k +
          harperCumulativeCellWidth
            (harperScheduledRelativeCellWidth start n) k ≤ x + 2 := by
    intro k
    have hreverse := harperNormalizedReverseLogBarrier_le n x hc k
    have hwidth := harperCumulativeScheduledRelativeCellWidth_le_two start n k
    linarith
  have hsubset :
      harperExpandedPartialSumBarrierSet lower
          (harperNormalizedReverseLogBarrier n x c)
          (harperScheduledRelativeCellWidth start n) ⊆
        gaussianWalkSurvivalSet n (x + 2) :=
    harperExpandedPartialSumBarrierSet_subset_gaussianWalkSurvivalSet
      (lower := lower) hbarrier
  have hwalk := hJ start hstart n hn y hy t htLower htUpper u hscale
    (x + 2) (by linarith)
  calc
    (harperScheduledOffDiagonalGaussianProductMeasure
        y start n t u).real
          (harperExpandedPartialSumBarrierSet lower
            (harperNormalizedReverseLogBarrier n x c)
            (harperScheduledRelativeCellWidth start n)) ≤
        (harperScheduledOffDiagonalGaussianProductMeasure
          y start n t u).real (gaussianWalkSurvivalSet n (x + 2)) :=
      measureReal_mono hsubset
    _ ≤ 64 * (x + 2 + 2) / Real.sqrt (n : ℝ) := hwalk
    _ = 64 * (x + 4) / Real.sqrt (n : ℝ) := by ring

/-- Exact off-diagonal tilted-event endpoint: after restricting to the
moderate coordinate box, the centered Harper block path stays below the
normalized reverse-log barrier with probability
`exp 2 * 64 (x+4) / sqrt n`. -/
theorem exists_eventually_harperScheduledOffDiagonalModerateBoxReverseLogBarrier_probability_le
    (M : ℕ) :
    ∃ J : ℕ, ∀ start : ℕ, J ≤ start → ∀ n : ℕ, 0 < n → ∀ y : ℕ,
      harperBlockEndpoint (start + n) ≤ y →
        ∀ t : ℝ, 1 ≤ |t| → |t| ≤ M → ∀ u : Fin n → ℝ,
          (∀ i : Fin n,
            |u i - t| *
                Real.log (harperBlockEndpoint
                  (start + (i : ℕ) + 1) : ℝ) ≤ (1 / 64 : ℝ)) →
            ∀ x c : ℝ, 0 ≤ x → 0 ≤ c → ∀ lower : Fin n → ℝ,
              (Measure.pi (fun i : Fin n ↦
                harperCenteredLinearBlockLaw y
                  (harperScheduledPrimeBlock y
                    (start + (i : ℕ))) t (u i))).real
                  (harperPartialSumBarrierSet lower
                      (harperNormalizedReverseLogBarrier n x c) ∩
                    harperCoordinateBox
                      (harperScheduledModerateRadius start n)) ≤
                Real.exp 2 *
                  (64 * (x + 4) / Real.sqrt (n : ℝ)) := by
  obtain ⟨Jslice, hJslice⟩ :=
    exists_eventually_harperScheduledOffDiagonalModerateBoxBarrierProbability_le_exp_two_mul_gaussian M
  obtain ⟨Jwalk, hJwalk⟩ :=
    exists_eventually_harperScheduledOffDiagonalGaussianWalk_expandedReverseLogBarrier_probability_le M
  refine ⟨max Jslice Jwalk, ?_⟩
  intro start hstart n hn y hy t htLower htUpper u hscale
    x c hx hc lower
  have hstartSlice : Jslice ≤ start :=
    (le_max_left Jslice Jwalk).trans hstart
  have hstartWalk : Jwalk ≤ start :=
    (le_max_right Jslice Jwalk).trans hstart
  have hslice := hJslice start hstartSlice n y hy t htLower htUpper
    u hscale lower (harperNormalizedReverseLogBarrier n x c)
  have hwalk := hJwalk start hstartWalk n hn y hy t htLower htUpper
    u hscale x c hx hc lower
  have hgaussian :
      (Measure.pi (fun i : Fin n ↦
        harperGaussianBlockLaw y
          (harperScheduledPrimeBlock y
            (start + (i : ℕ))) t (u i))).real
          (harperExpandedPartialSumBarrierSet lower
            (harperNormalizedReverseLogBarrier n x c)
            (harperScheduledRelativeCellWidth start n)) ≤
        64 * (x + 4) / Real.sqrt (n : ℝ) := by
    simpa only [harperScheduledOffDiagonalGaussianProductMeasure,
      harperScheduledOffDiagonalGaussianVariance,
      harperGaussianBlockLaw] using! hwalk
  exact hslice.trans
    (mul_le_mul_of_nonneg_left hgaussian (by positivity))

end
end Problem520
end Erdos
