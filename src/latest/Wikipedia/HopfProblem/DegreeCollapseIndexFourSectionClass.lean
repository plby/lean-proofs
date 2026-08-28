import Wikipedia.HopfProblem.DegreeCollapseIndexFourRelation
import Wikipedia.HopfProblem.DegreeCollapseSectionAttachingClass
import Wikipedia.SmoothSixDPoincare.MorseBandHomology

/-!
# Exact native three-sphere section classes for the index-four relations

The original standard parametrization sends the primitive S3 class to
the generator defining the native index-four relation. Exact downward
flow transport therefore compares the actual common-cut class with that
same attaching class through the literal sublevel inclusion, with no
undetermined sign. Homotopies retain this common-cut class as well.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open SphereHomology SingularMayerVietoris PeriodTorusHigherHomology

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}

theorem IndexFour.boundary_generator (d : MorseSurgeryData E f p)
    [hindex : Fact (Module.finrank ℝ d.chart.NegativeCoordinates = 3 + 1)] :
    (IndexFour.indexFourBoundaryEquiv d hindex.out).symm 1 =
      singularHomologyMap
        (SphereCoordinates.standardParametrization
          d.chart.NegativeCoordinates 3).toHomeomorph.toHomotopyEquiv.toFun 3
            (unitSphereTopClass 2) := rfl

theorem IndexFour.attachingClass_parametrized (d : MorseSurgeryData E f p)
    [hindex : Fact (Module.finrank ℝ d.chart.NegativeCoordinates = 3 + 1)] :
    IndexFour.indexFourAttachingClass d hindex.out =
      singularHomologyMap
        (d.coreBoundaryMap.comp (SphereCoordinates.standardParametrization
          d.chart.NegativeCoordinates 3).toHomeomorph.toHomotopyEquiv.toFun) 3
            (unitSphereTopClass 2) := by
  rw [singularHomologyMap_comp]
  rfl

def nativeIndexFourAttachingSphere [IsManifold 𝓘(ℝ, E) ∞ M] (A : AdaptedSurgeryWindows E f)
    (q : criticalPoints E f) (hq : nativeMorseIndex E f q = 4) :
    C(Hemisphere.Sphere 3, (A.data q).LowerLevel) := by
  let _ : Fact (Module.finrank ℝ (A.data q).chart.NegativeCoordinates = 3 + 1) :=
    ⟨(nativeMorseIndex_eq_chart (A.data q).chart).symm.trans hq⟩
  exact (A.data q).surgery.attachingSphere.comp
    ((SphereCoordinates.standardParametrization
      (A.data q).chart.NegativeCoordinates 3).toHomeomorph :
      C(Hemisphere.Sphere 3, sphere (0 : (A.data q).chart.NegativeCoordinates) 1))

def threeSectionClass {a : ℝ} (γ : C(Hemisphere.Sphere 3, {y : M // f y = a})) :
    SingularHomology {y : M // f y ≤ a} 3 :=
  singularHomologyMap ((levelSublevelMap f le_rfl).comp γ) 3 (unitSphereTopClass 2)

theorem threeSectionClass_homotopic {a : ℝ}
    {γ δ : C(Hemisphere.Sphere 3, {y : M // f y = a})} (h : γ.Homotopic δ) :
    threeSectionClass γ = threeSectionClass δ := by
  have hmaps := homotopic_homologyMap h 3
  simp only [threeSectionClass, singularHomologyMap_comp, LinearMap.comp_apply]
  rw [hmaps]

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]

theorem AdaptedSurgeryWindows.native_index_four_attaching_class_of_flow_section
    (A : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (q : criticalPoints E f) (hq : nativeMorseIndex E f q = 4)
    {a : ℝ} (ha : ∀ y, f y = a → y ∉ criticalPoints E f)
    (hab : a < A.toSurgeryWindows.lower q)
    (γ : C(Hemisphere.Sphere 3, {y : M // f y = a}))
    (horbit : ∀ x, ∃ t : ℝ,
      A.flow t (nativeIndexFourAttachingSphere A q hq x).val = (γ x).val) :
    singularHomologyMap (sublevelMap f hab.le) 3 (threeSectionClass γ) =
      IndexFour.indexFourAttachingClass (A.data q)
        ((nativeMorseIndex_eq_chart (A.data q).chart).symm.trans hq) := by
  let _ : Fact (Module.finrank ℝ (A.data q).chart.NegativeCoordinates = 3 + 1) :=
    ⟨(nativeMorseIndex_eq_chart (A.data q).chart).symm.trans hq⟩
  have hh := A.level_transport_homotopic_in_sublevel hf hab ha
    (nativeIndexFourAttachingSphere A q hq) γ horbit
  have hm := homotopic_homologyMap hh 3
  have hparam : singularHomologyMap
      ((levelSublevelMap f (le_refl (A.toSurgeryWindows.lower q))).comp
        (nativeIndexFourAttachingSphere A q hq)) 3 (unitSphereTopClass 2) =
      IndexFour.indexFourAttachingClass (A.data q)
        ((nativeMorseIndex_eq_chart (A.data q).chart).symm.trans hq) :=
    (IndexFour.attachingClass_parametrized (A.data q)).symm
  rw [← hparam, hm]
  rw [threeSectionClass, ← LinearMap.comp_apply, ← singularHomologyMap_comp]
  rfl

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
