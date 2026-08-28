import Wikipedia.HopfProblem.DegreeCollapseNativeInclusionHomology
import Wikipedia.HopfProblem.DegreeCollapseIndexFourSectionClass

/-!
# The actual index-four relation for literal sublevel inclusions

The original core-cell homotopy equivalence carries the native exact
sequence to the literal ambient inclusion. On third homology its kernel
is exactly the span of the original index-four attaching class, and the
same inclusion map is surjective. No chosen attachment homeomorphism is
silently identified with the literal inclusion.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open SingularMayerVietoris PeriodTorusHigherHomology

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.native_index_four_inclusion_relation
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p : criticalPoints E f) (hp : nativeMorseIndex E f p = 4) :
    let I := singularHomologyMap (sublevelMap f
      ((S.toSurgeryWindows.lower_lt_value p).trans (S.toSurgeryWindows.value_lt_upper p)).le) 3
    Surjective I ∧ LinearMap.ker I = Submodule.span ℤ
      {IndexFour.indexFourAttachingClass (S.data p)
        ((nativeMorseIndex_eq_chart (S.data p).chart).symm.trans hp)} := by
  let d := S.data p
  have hindex : Module.finrank ℝ d.chart.NegativeCoordinates = 4 :=
    (nativeMorseIndex_eq_chart d.chart).symm.trans hp
  let _ : Subsingleton (SingularHomology (sphere (0 : d.chart.NegativeCoordinates) 1) 2) :=
    d.attachingHomology_subsingleton_of_index 2 (by decide) (by omega) (by omega)
  have hsurj : Surjective ((d.coreCellPresentation hf.continuous).oldHomologyMap 3) := by
    intro a
    have ha : a ∈ LinearMap.ker ((d.coreCellPresentation hf.continuous).cellConnectingMap 2) :=
      Subsingleton.elim _ _
    rw [← (d.coreCellPresentation hf.continuous).cell_exact_at_ambient 2] at ha
    exact ha
  obtain ⟨A, hA⟩ := S.exists_core_inclusion_homology_comparison hf p 3
  constructor
  · intro a
    obtain ⟨x, hx⟩ := hsurj (A.symm a)
    refine ⟨(d.cellOldHomologyEquiv hf.continuous 3).symm x, ?_⟩
    have hh := hA ((d.cellOldHomologyEquiv hf.continuous 3).symm x)
    rw [LinearEquiv.apply_symm_apply, hx, LinearEquiv.apply_symm_apply] at hh
    exact hh.symm
  · rw [← S.native_sublevel_inclusion_exact hf p 3 (by decide),
      IndexFour.coreBoundary_three_range d hindex]

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
