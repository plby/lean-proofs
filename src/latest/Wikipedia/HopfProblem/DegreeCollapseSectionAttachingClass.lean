import Wikipedia.HopfProblem.DegreeCollapseAttachingSectionHomotopy
import Wikipedia.SmoothSixDPoincare.MorseIndexThreeTransportClass

/-!
# The canonical common-cut class maps to the original native attaching class

The maps between sublevels here are the literal ambient inclusions. The
constructed signed-time homotopy retains the original sphere parameter,
so the class equality has coefficient exactly one, with no sign choice.
-/

noncomputable section

open Set Function Filter Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open SingularMayerVietoris PeriodTorusHigherHomology SphereHomology

local notation "S₂" => Hemisphere.Sphere 2

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

def sublevelMap (f : M → ℝ) {a b : ℝ} (hab : a ≤ b) :
    C({y : M // f y ≤ a}, {y : M // f y ≤ b}) :=
  ⟨fun y => ⟨y.val, y.property.trans hab⟩, continuous_subtype_val.subtype_mk _⟩

def middleSectionClass {a : ℝ} (γ : C(S₂, {y : M // f y = a})) :
    SingularHomology {y : M // f y ≤ a} 2 :=
  singularHomologyMap ((levelSublevelMap f le_rfl).comp γ) 2 (unitSphereTopClass 1)

theorem AdaptedSurgeryWindows.native_attaching_class_of_flow_section
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p : criticalPoints E f) (hp : nativeMorseIndex E f p = 3)
    {a : ℝ} (ha : ∀ y, f y = a → y ∉ criticalPoints E f)
    (hab : a < S.toSurgeryWindows.lower p) (γ : C(S₂, {y : M // f y = a}))
    (horbit : ∀ x, ∃ t : ℝ,
      S.flow t (nativeIndexThreeAttachingSphere S p hp x).val = (γ x).val) :
    singularHomologyMap (sublevelMap f hab.le) 2 (middleSectionClass γ) =
      (S.data p).indexThreeAttachingClass
        ((nativeMorseIndex_eq_chart (S.data p).chart).symm.trans hp) := by
  let _ : Fact (Module.finrank ℝ (S.data p).chart.NegativeCoordinates = 2 + 1) :=
    ⟨(nativeMorseIndex_eq_chart (S.data p).chart).symm.trans hp⟩
  have hh := S.level_transport_homotopic_in_sublevel hf hab ha
    (nativeIndexThreeAttachingSphere S p hp) γ horbit
  have hm := homotopic_homologyMap hh 2
  have hparam : singularHomologyMap
      ((levelSublevelMap f (le_refl (S.toSurgeryWindows.lower p))).comp
        (nativeIndexThreeAttachingSphere S p hp)) 2 (unitSphereTopClass 1) =
      (S.data p).indexThreeAttachingClass
        ((nativeMorseIndex_eq_chart (S.data p).chart).symm.trans hp) :=
    (S.data p).indexThreeAttachingClass_parametrized.symm
  rw [← hparam, hm]
  rw [middleSectionClass, ← LinearMap.comp_apply, ← singularHomologyMap_comp]
  rfl

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
