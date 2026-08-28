import Wikipedia.HopfProblem.HolomorphicMeromorphicPolarSurfaceReducedRepresentatives
import Wikipedia.HopfProblem.HolomorphicMeromorphicPolarSurfaceReducedCharts
import Wikipedia.HopfProblem.HolomorphicMeromorphicPolarReducedTransport

/-!
# Isolated common zeros in the original manifold topology

Representative-independent isolation of the two-variable analytic germs
pulls back through an actual centered chart. The proof retains the chart
source neighborhood, where zero centered coordinates force the original
point to equal the chart center.
-/

open Set Filter Topology TopologicalSpace
open scoped Manifold ContDiff
open Wikipedia.HopfProblem.CuspNormalization.Germs

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic.PolarSurfaceReduced

variable {E H : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
  (M : Type) [TopologicalSpace M] [ChartedSpace H M]

/-- Every pair of genuine local holomorphic representatives has no nearby
common zero except possibly the specified original manifold point. -/
def NativeIsolatedCommonZero (x : M) (a b : HolomorphicStalk I M x) : Prop :=
  ∀ (U : Opens M) (hx : x ∈ U) (A B : HolomorphicFunctionSheaf.Section I M U),
    (HolomorphicFunctionSheaf.presheaf I M).germ U x hx A = a →
    (HolomorphicFunctionSheaf.presheaf I M).germ U x hx B = b →
    ∀ᶠ y in 𝓝 x,
      HolomorphicFunctionSheaf.extendManifoldSection I U A y = 0 →
      HolomorphicFunctionSheaf.extendManifoldSection I U B y = 0 → y = x

/-- On the true chart source the centered representative evaluates to the
original section extension. -/
theorem surfaceSectionRepresentative_centeredChart
    (e : (ℂ × ℂ) ≃L[ℂ] E) (x : M) (U : Opens M)
    (A : HolomorphicFunctionSheaf.Section I M U) {y : M}
    (hy : y ∈ (extChartAt I x).source) :
    surfaceSectionRepresentative I e x U A (centeredChart I e x y) =
      HolomorphicFunctionSheaf.extendManifoldSection I U A y := by
  change HolomorphicFunctionSheaf.extendManifoldSection I U A
    (centeredChartInverse I e x (centeredChart I e x y)) = _
  rw [centeredChartInverse_left I e x hy]

variable [I.Boundaryless] [IsManifold I ω M]

/-- Isolation for the actual centered analytic germs gives isolation of
arbitrary native local representatives in the original manifold topology. -/
theorem nativeIsolatedCommonZero_of_surfaceStalkEquiv
    (e : (ℂ × ℂ) ≃L[ℂ] E) (x : M) {a b : HolomorphicStalk I M x}
    (h : PolarReduced.IsolatedCommonZero
      (PolarStalk.surfaceStalkEquiv I M e x a)
      (PolarStalk.surfaceStalkEquiv I M e x b)) :
    NativeIsolatedCommonZero I M x a b := by
  intro U hx A B hA hB
  have hAgerm :
      ofAnalytic (surfaceSectionRepresentative I e x U A)
          (surfaceSectionRepresentative_analyticAt I e x U hx A) =
        PolarStalk.surfaceStalkEquiv I M e x a := by
    rw [← surfaceStalkEquiv_germ I e x U hx A, hA]
  have hBgerm :
      ofAnalytic (surfaceSectionRepresentative I e x U B)
          (surfaceSectionRepresentative_analyticAt I e x U hx B) =
        PolarStalk.surfaceStalkEquiv I M e x b := by
    rw [← surfaceStalkEquiv_germ I e x U hx B, hB]
  have hlocal := h
    (surfaceSectionRepresentative I e x U A) (surfaceSectionRepresentative I e x U B)
    (surfaceSectionRepresentative_analyticAt I e x U hx A)
    (surfaceSectionRepresentative_analyticAt I e x U hx B) hAgerm hBgerm
  filter_upwards [(centeredChart_tendsto I e x).eventually hlocal,
    extChartAt_source_mem_nhds (I := I) x] with y hy hychart
  intro hAy hBy
  have hzero : centeredChart I e x y = 0 := hy
    (by simpa only [surfaceSectionRepresentative_centeredChart I M e x U A hychart]
      using hAy)
    (by simpa only [surfaceSectionRepresentative_centeredChart I M e x U B hychart]
      using hBy)
  exact (centeredChart_eq_zero_iff I e x hychart).mp hzero

end Wikipedia.HopfProblem.HolomorphicMeromorphic.PolarSurfaceReduced
