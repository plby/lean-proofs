import Wikipedia.HopfProblem.DegreeCollapseQuadraticGermDerivative
import Wikipedia.HopfProblem.DegreeCollapseSurvivingMorseGerms

/-!
# The native Morse index is independent of the signed chart

The actual chart transition fixes the origin and has bijective derivative.
Its exact quadratic identity passes to that derivative by a line limit.
Sylvester's law of inertia then equates the original negative dimensions.
This also preserves the index of every surviving critical function germ.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ} {p : M}

theorem signed_morse_chart_quadratic_equivalent
    (c d : SignedMorseChart (E := E) f p) :
    (QuadraticMap.weightedSumSquares ℝ c.weights).Equivalent
      (QuadraticMap.weightedSumSquares ℝ d.weights) := by
  let Z := Fin (Module.finrank ℝ E) → ℝ
  let Q : QuadraticForm ℝ Z := QuadraticMap.weightedSumSquares ℝ c.weights
  let R : QuadraticForm ℝ Z := QuadraticMap.weightedSumSquares ℝ d.weights
  have hQ (z : Z) : Q z = ∑ i, c.weights i * (z i) ^ 2 := by
    simpa only [smul_eq_mul, pow_two] using
      (QuadraticMap.weightedSumSquares_apply (R := ℝ) c.weights z)
  have hR (z : Z) : R z = ∑ i, d.weights i * (z i) ^ 2 := by
    simpa only [smul_eq_mul, pow_two] using
      (QuadraticMap.weightedSumSquares_apply (R := ℝ) d.weights z)
  have hRcont : Continuous R := by
    change Continuous (fun z : Z => R z)
    simp_rw [hR]
    fun_prop
  let P := c.chart.symm.trans d.chart
  have hc0 : c.chart.symm (0 : Z) = p := by
    rw [← c.center]
    exact c.chart.left_inv' c.mem_source
  have h0 : (0 : Z) ∈ P.source := by
    refine ⟨?_, ?_⟩
    · rw [← c.center]
      exact c.chart.map_source' c.mem_source
    · change c.chart.symm (0 : Z) ∈ d.chart.source
      rw [hc0]
      exact d.mem_source
  have hP0 : P (0 : Z) = 0 := by
    change d.chart (c.chart.symm (0 : Z)) = 0
    rw [hc0, d.center]
  have hdiff := (P.mdifferentiableAt (by simp) h0).differentiableAt
  have hbij : Bijective (fderiv ℝ P (0 : Z)) := by
    have hh := PartialChart.bijective_mfderiv P h0
    rw [mfderiv_eq_fderiv] at hh
    exact hh
  have hquad : (fun z => R (P z)) =ᶠ[𝓝 (0 : Z)] Q := by
    filter_upwards [P.open_source.mem_nhds h0] with z hz
    have hzs : z ∈ c.chart.target ∧ c.chart.symm z ∈ d.chart.source := hz
    rw [hR, hQ]
    change (∑ i, d.weights i * (d.chart (c.chart.symm z) i) ^ 2) =
      ∑ i, c.weights i * (z i) ^ 2
    linarith [c.inverse_equation z hzs.1, d.equation (c.chart.symm z) hzs.2]
  exact equivalent_quadratic_germs_of_bijective_derivative Q R hRcont
    hdiff.hasFDerivAt hP0 hbij hquad

open Classical in
theorem signed_morse_chart_negative_card_eq (c d : SignedMorseChart (E := E) f p) :
    Fintype.card {i // c.weights i = -1} = Fintype.card {i // d.weights i = -1} := by
  have hs := (signed_morse_chart_quadratic_equivalent c d).sigNeg_eq
  rw [QuadraticForm.sigNeg_weightedSumSquares, QuadraticForm.sigNeg_weightedSumSquares] at hs
  have hc : {i | c.weights i < 0} = {i | c.weights i = -1} := by
    ext i
    rcases c.signs i with h | h <;> norm_num [h]
  have hd : {i | d.weights i < 0} = {i | d.weights i = -1} := by
    ext i
    rcases d.signs i with h | h <;> norm_num [h]
  rw [hc, hd] at hs
  calc
    Fintype.card {i // c.weights i = -1} = {i | c.weights i = -1}.ncard :=
      Set.fintypeCard_eq_ncard _
    _ = {i | d.weights i = -1}.ncard := hs
    _ = Fintype.card {i // d.weights i = -1} := (Set.fintypeCard_eq_ncard _).symm

open Classical in
theorem signed_morse_chart_negative_finrank_eq (c d : SignedMorseChart (E := E) f p) :
    Module.finrank ℝ c.NegativeCoordinates = Module.finrank ℝ d.NegativeCoordinates := by
  simpa only [SignedMorseChart.NegativeCoordinates, MorseHandle.NegativeSpace,
    finrank_euclideanSpace] using signed_morse_chart_negative_card_eq c d

open Classical in
theorem signed_morse_chart_positive_finrank_eq (c d : SignedMorseChart (E := E) f p) :
    Module.finrank ℝ c.PositiveCoordinates = Module.finrank ℝ d.PositiveCoordinates := by
  have hn := signed_morse_chart_negative_finrank_eq c d
  have hc := c.finrank_negative_add_positive
  have hd := d.finrank_negative_add_positive
  omega

open Classical in
theorem signed_morse_chart_negative_finrank_eq_of_germ
    (c : SignedMorseChart (E := E) f p) (d : SignedMorseChart (E := E) g p)
    (hgerm : g =ᶠ[𝓝 p] f) :
    Module.finrank ℝ c.NegativeCoordinates = Module.finrank ℝ d.NegativeCoordinates := by
  obtain ⟨c', hw, -, -, -⟩ := exists_signed_morse_chart_of_germ c hgerm
  have heq := signed_morse_chart_negative_card_eq c' d
  rw [hw] at heq
  simpa only [SignedMorseChart.NegativeCoordinates, MorseHandle.NegativeSpace,
    finrank_euclideanSpace] using heq

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
