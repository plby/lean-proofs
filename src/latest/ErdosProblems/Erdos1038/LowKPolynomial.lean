import ErdosProblems.Erdos1038.NormalizedResidualBridge

/-!
# The elementary residual estimate at polynomial level

This file sums the disjoint main and residual components of an
endpoint-normalized, component-atomized polynomial.  It upgrades the
configuration-level low-`k` radius estimate to a strict lower bound of `2`
for the polynomial's entire strict unit sublevel set.
-/

open scoped BigOperators ENNReal Real
open MeasureTheory Set Polynomial

namespace Erdos1038

noncomputable section

def normalizedSelectedRoot {f : Polynomial ℝ}
    (h : EndpointNormalizationHypotheses f) :
    Option (NormalizedResidualIndex h) → ℝ
  | none => -1
  | some i => i

def normalizedSelectedComponent {f : Polynomial ℝ}
    (h : EndpointNormalizationHypotheses f)
    (o : Option (NormalizedResidualIndex h)) : Set ℝ :=
  sublevelComponent h.normalizedPolynomial (normalizedSelectedRoot h o)

/-- Exact real width of the endpoint component after normalization. -/
def normalizedMainComponentWidth {f : Polynomial ℝ}
    (h : EndpointNormalizationHypotheses f) : ℝ :=
  h.normalizedRightBoundary -
    sInf (sublevelComponent h.normalizedPolynomial (-1))

namespace EndpointNormalizationHypotheses

variable {f : Polynomial ℝ} (h : EndpointNormalizationHypotheses f)

lemma normalizedSelectedRoot_mem_roots
    (o : Option (NormalizedResidualIndex h)) :
    normalizedSelectedRoot h o ∈ h.normalizedPolynomial.roots := by
  cases o with
  | none =>
      simpa [normalizedSelectedRoot] using! h.neg_one_mem_normalized_roots
  | some i =>
      exact (mem_endpointResidualRoots.mp
        (Multiset.mem_toFinset.mp i.property)).1

lemma normalizedSelectedRoot_injective :
    Function.Injective (normalizedSelectedRoot h) := by
  intro i j hij
  cases i with
  | none =>
      cases j with
      | none => rfl
      | some j =>
          have hjne : (j : ℝ) ≠ -1 :=
            (mem_endpointResidualRoots.mp
              (Multiset.mem_toFinset.mp j.property)).2
          exact False.elim (hjne (by simpa [normalizedSelectedRoot] using! hij.symm))
  | some i =>
      cases j with
      | none =>
          have hine : (i : ℝ) ≠ -1 :=
            (mem_endpointResidualRoots.mp
              (Multiset.mem_toFinset.mp i.property)).2
          exact False.elim (hine (by simpa [normalizedSelectedRoot] using! hij))
      | some j =>
          congr 1
          apply Subtype.ext
          simpa [normalizedSelectedRoot] using! hij

lemma normalizedSelectedComponents_pairwiseDisjoint :
    Pairwise (fun i j ↦ Disjoint (normalizedSelectedComponent h i)
      (normalizedSelectedComponent h j)) := by
  intro i j hij
  apply Set.disjoint_left.2
  intro x hxi hxj
  apply hij
  apply h.normalizedSelectedRoot_injective
  apply h.normalized_componentAtomized
    (h.normalizedSelectedRoot_mem_roots i)
    (h.normalizedSelectedRoot_mem_roots j)
  exact (connectedComponentIn_eq hxi).trans
    (connectedComponentIn_eq hxj).symm

lemma normalized_mainWindow_subset_component
    (hres : endpointResidualRoots h.normalizedPolynomial ≠ 0) :
    Ioo (-Real.sqrt 2) 0 ⊆ normalizedSelectedComponent h none := by
  have hk := h.one_le_normalizedEndpointResidualRatio hres
  have hwindow := endpointWindow_subset_residualNegativeWithPoles
    (h.normalizedResidualConfiguration hres) hk
  have hinterval : Ioo (-Real.sqrt 2) 0 ⊆
      sublevelSet h.normalizedPolynomial := by
    intro y hy
    have hyshift : y + 1 ∈ Ioo (1 - Real.sqrt 2) 1 := by
      constructor <;> linarith [hy.1, hy.2]
    have hyres := hwindow hyshift
    rw [← h.shifted_sublevelSet_eq_residualNegativeWithPoles hres] at hyres
    simpa using! hyres
  have hsqrt : 1 < Real.sqrt 2 := by
    have hsquare : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hsqrtnonneg := Real.sqrt_nonneg 2
    nlinarith
  have hminus : (-1 : ℝ) ∈ Ioo (-Real.sqrt 2) 0 := by
    constructor <;> linarith
  change Ioo (-Real.sqrt 2) 0 ⊆
    connectedComponentIn (sublevelSet h.normalizedPolynomial) (-1)
  exact isPreconnected_Ioo.subset_connectedComponentIn hminus hinterval

lemma ofReal_sqrt_two_le_normalized_main_component_volume
    (hres : endpointResidualRoots h.normalizedPolynomial ≠ 0) :
    ENNReal.ofReal (Real.sqrt 2) ≤
      volume (normalizedSelectedComponent h none) := by
  have hmono : volume (Ioo (-Real.sqrt 2) 0) ≤
      volume (normalizedSelectedComponent h none) :=
    measure_mono (h.normalized_mainWindow_subset_component hres)
  rw [Real.volume_Ioo] at hmono
  simpa using! hmono

lemma normalizedMainComponentWidth_pos :
    0 < normalizedMainComponentWidth h := by
  have hmem : (-1 : ℝ) ∈
      sublevelComponent h.normalizedPolynomial (-1) :=
    mem_connectedComponentIn
      (root_mem_sublevelSet h.neg_one_mem_normalized_roots)
  rw [h.normalized_endpoint_component_eq_Ioo] at hmem
  unfold normalizedMainComponentWidth
  linarith [hmem.1, hmem.2]

/-- Haar/Lebesgue volume of the main component is exactly its endpoint
width, with no coarse window estimate. -/
lemma volume_normalized_main_component_eq_ofReal_width :
    volume (normalizedSelectedComponent h none) =
      ENNReal.ofReal (normalizedMainComponentWidth h) := by
  unfold normalizedSelectedComponent normalizedSelectedRoot
  rw [h.normalized_endpoint_component_eq_Ioo, Real.volume_Ioo]
  rfl

lemma sum_normalizedSelectedComponent_volume_le :
    ∑ o : Option (NormalizedResidualIndex h),
        volume (normalizedSelectedComponent h o) ≤
      sublevelVolume h.normalizedPolynomial := by
  have hmeas : ∀ o : Option (NormalizedResidualIndex h),
      NullMeasurableSet (normalizedSelectedComponent h o) volume := by
    intro o
    exact ((isOpen_sublevelSet h.normalizedPolynomial).connectedComponentIn
      |>.measurableSet).nullMeasurableSet
  have hdisj : Pairwise (fun i j ↦ AEDisjoint volume
      (normalizedSelectedComponent h i) (normalizedSelectedComponent h j)) := by
    intro i j hij
    exact (h.normalizedSelectedComponents_pairwiseDisjoint hij).aedisjoint
  have hsum := tsum_meas_le_meas_iUnion_of_disjoint₀
    volume hmeas hdisj
  rw [tsum_fintype] at hsum
  have hunion : (⋃ o, normalizedSelectedComponent h o) ⊆
      sublevelSet h.normalizedPolynomial := by
    apply iUnion_subset
    intro o
    exact connectedComponentIn_subset _ _
  exact hsum.trans (measure_mono hunion)

theorem ofReal_sqrt_two_add_twice_radiusSum_le_sublevelVolume
    (hres : endpointResidualRoots h.normalizedPolynomial ≠ 0) :
    ENNReal.ofReal (Real.sqrt 2 +
        2 * residualRadiusSum (h.normalizedResidualConfiguration hres)
          (normalizedEndpointResidualRatio h)) ≤
      sublevelVolume f := by
  let C := h.normalizedResidualConfiguration hres
  let k := normalizedEndpointResidualRatio h
  have hmain := h.ofReal_sqrt_two_le_normalized_main_component_volume hres
  have hresidual : ∀ i : NormalizedResidualIndex h,
      ENNReal.ofReal (2 * residualRadius C k i) ≤
        volume (normalizedSelectedComponent h (some i)) := by
    intro i
    simpa [C, k, normalizedSelectedComponent, normalizedSelectedRoot] using!
      h.ofReal_two_mul_residualRadius_le_normalized_component_volume hres i
  have hsumcomponents := h.sum_normalizedSelectedComponent_volume_le
  rw [Fintype.sum_option] at hsumcomponents
  have hpieces : ENNReal.ofReal (Real.sqrt 2) +
      ∑ i : NormalizedResidualIndex h,
        ENNReal.ofReal (2 * residualRadius C k i) ≤
      sublevelVolume h.normalizedPolynomial := by
    exact (add_le_add hmain (Finset.sum_le_sum fun i _ ↦ hresidual i)).trans
      hsumcomponents
  have hsqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hradius : ∀ i : NormalizedResidualIndex h,
      0 ≤ 2 * residualRadius C k i :=
    fun i ↦ (mul_pos (by norm_num) (residualRadius_pos C k i)).le
  have hrewrite :
      ENNReal.ofReal (Real.sqrt 2 + 2 * residualRadiusSum C k) =
        ENNReal.ofReal (Real.sqrt 2) +
          ∑ i : NormalizedResidualIndex h,
            ENNReal.ofReal (2 * residualRadius C k i) := by
    have hrsum : 0 ≤ 2 * residualRadiusSum C k := by
      unfold residualRadiusSum
      exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ ↦
        (residualRadius_pos C k i).le)
    rw [ENNReal.ofReal_add hsqrt hrsum]
    congr 1
    rw [residualRadiusSum, Finset.mul_sum,
      ENNReal.ofReal_sum_of_nonneg]
    exact fun i _ ↦ hradius i
  rw [hrewrite]
  exact hpieces.trans_eq h.normalized_sublevelVolume

/-- Exact high-ratio geometric bridge: the real main width plus twice all
local residual radii is bounded by the polynomial's full sublevel volume. -/
theorem ofReal_mainWidth_add_twice_radiusSum_le_sublevelVolume
    (hres : endpointResidualRoots h.normalizedPolynomial ≠ 0) :
    ENNReal.ofReal (normalizedMainComponentWidth h +
        2 * residualRadiusSum (h.normalizedResidualConfiguration hres)
          (normalizedEndpointResidualRatio h)) ≤
      sublevelVolume f := by
  let C := h.normalizedResidualConfiguration hres
  let k := normalizedEndpointResidualRatio h
  have hmain : ENNReal.ofReal (normalizedMainComponentWidth h) =
      volume (normalizedSelectedComponent h none) :=
    h.volume_normalized_main_component_eq_ofReal_width.symm
  have hresidual : ∀ i : NormalizedResidualIndex h,
      ENNReal.ofReal (2 * residualRadius C k i) ≤
        volume (normalizedSelectedComponent h (some i)) := by
    intro i
    simpa [C, k, normalizedSelectedComponent, normalizedSelectedRoot] using!
      h.ofReal_two_mul_residualRadius_le_normalized_component_volume hres i
  have hsumcomponents := h.sum_normalizedSelectedComponent_volume_le
  rw [Fintype.sum_option] at hsumcomponents
  have hpieces : ENNReal.ofReal (normalizedMainComponentWidth h) +
      ∑ i : NormalizedResidualIndex h,
        ENNReal.ofReal (2 * residualRadius C k i) ≤
      sublevelVolume h.normalizedPolynomial := by
    rw [hmain]
    exact (add_le_add le_rfl (Finset.sum_le_sum fun i _ ↦ hresidual i)).trans
      hsumcomponents
  have hwidth : 0 ≤ normalizedMainComponentWidth h :=
    h.normalizedMainComponentWidth_pos.le
  have hradius : ∀ i : NormalizedResidualIndex h,
      0 ≤ 2 * residualRadius C k i :=
    fun i ↦ (mul_pos (by norm_num) (residualRadius_pos C k i)).le
  have hrewrite :
      ENNReal.ofReal (normalizedMainComponentWidth h +
          2 * residualRadiusSum C k) =
        ENNReal.ofReal (normalizedMainComponentWidth h) +
          ∑ i : NormalizedResidualIndex h,
            ENNReal.ofReal (2 * residualRadius C k i) := by
    have hrsum : 0 ≤ 2 * residualRadiusSum C k := by
      unfold residualRadiusSum
      exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ ↦
        (residualRadius_pos C k i).le)
    rw [ENNReal.ofReal_add hwidth hrsum]
    congr 1
    rw [residualRadiusSum, Finset.mul_sum,
      ENNReal.ofReal_sum_of_nonneg]
    exact fun i _ ↦ hradius i
  rw [hrewrite]
  exact hpieces.trans_eq h.normalized_sublevelVolume

/-- Any strict real lower bound for the exact residual functional gives the
corresponding strict lower bound for the original polynomial. -/
theorem ofReal_lt_sublevelVolume_of_lt_mainWidth_add_twice_radiusSum
    (hres : endpointResidualRoots h.normalizedPolynomial ≠ 0)
    {ell : ℝ} (hell0 : 0 ≤ ell)
    (hstrict : ell < normalizedMainComponentWidth h +
      2 * residualRadiusSum (h.normalizedResidualConfiguration hres)
        (normalizedEndpointResidualRatio h)) :
    ENNReal.ofReal ell < sublevelVolume f := by
  have hofReal : ENNReal.ofReal ell <
      ENNReal.ofReal (normalizedMainComponentWidth h +
        2 * residualRadiusSum (h.normalizedResidualConfiguration hres)
          (normalizedEndpointResidualRatio h)) :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hell0).2 hstrict
  exact hofReal.trans_le
    (h.ofReal_mainWidth_add_twice_radiusSum_le_sublevelVolume hres)

theorem ofReal_two_lt_sublevelVolume_of_lowK
    (hres : endpointResidualRoots h.normalizedPolynomial ≠ 0)
    (hk : normalizedEndpointResidualRatio h ≤ 29 / 20) :
    ENNReal.ofReal 2 < sublevelVolume f := by
  let C := h.normalizedResidualConfiguration hres
  let k := normalizedEndpointResidualRatio h
  have hreal := h.two_lt_sqrt_two_add_twice_normalizedResidualRadiusSum
    hres hk
  have hofReal : ENNReal.ofReal 2 <
      ENNReal.ofReal (Real.sqrt 2 + 2 * residualRadiusSum C k) := by
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg
      (by norm_num : (0 : ℝ) ≤ 2)).2 hreal
  exact hofReal.trans_le
    (h.ofReal_sqrt_two_add_twice_radiusSum_le_sublevelVolume hres)

end EndpointNormalizationHypotheses

end

end Erdos1038
