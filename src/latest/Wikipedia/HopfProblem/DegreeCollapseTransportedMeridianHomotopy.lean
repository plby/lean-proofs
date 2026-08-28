import Wikipedia.HopfProblem.DegreeCollapseBeltComplementLowerTransport
import Wikipedia.HopfProblem.DegreeCollapseSmoothBeltMeridian

/-!
# The common-flow complement map sends the native meridian to the attaching class

The exact explicit flow passage and uniqueness of the lower-level point
identify the constructed complement map on the whole meridian sphere.
The proved native meridian homotopy then gives the original attaching
sphere with its full parametrization.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

def nativeUpperMeridianInComplement (S : AdaptedSurgeryWindows E f) (p : criticalPoints E f)
    (v : sphere (0 : (S.data p).chart.PositiveCoordinates) 1)
    (s : unitInterval) (hs : 0 < (s : ℝ)) :
    C(sphere (0 : (S.data p).chart.NegativeCoordinates) 1,
      ((range (S.data p).surgery.beltSphere)ᶜ : Set (S.data p).UpperLevel)) where
  toFun u := ⟨nativeUpperMeridian S p v s u, nativeUpperMeridian_avoids_belt S p v s hs u⟩
  continuous_toFun := (nativeUpperMeridian S p v s).continuous.subtype_mk _

theorem lower_transport_upperMeridian_eq (S : AdaptedSurgeryWindows E f)
    (p : criticalPoints E f)
    (D : C(((range (S.data p).surgery.beltSphere)ᶜ : Set (S.data p).UpperLevel),
      (S.data p).LowerLevel))
    (hD : ∀ x (y : (S.data p).LowerLevel) (t : ℝ),
      S.flow t x.val.val = y.val → D x = y)
    (v : sphere (0 : (S.data p).chart.PositiveCoordinates) 1)
    (s : unitInterval) (hs : 0 < (s : ℝ)) :
    D.comp (nativeUpperMeridianInComplement S p v s hs) = nativeLowerMeridian S p v s := by
  apply ContinuousMap.ext
  intro u
  exact hD (nativeUpperMeridianInComplement S p v s hs u)
    (nativeLowerMeridian S p v s u) (BeltPassage.time s)
    (nativeUpperMeridian_flow S p v s hs u)

theorem AdaptedSurgeryWindows.exists_lower_transport_with_meridians
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p : criticalPoints E f)
    (u : sphere (0 : (S.data p).chart.NegativeCoordinates) 1)
    (v : sphere (0 : (S.data p).chart.PositiveCoordinates) 1) :
    ∃ D : C(((range (S.data p).surgery.beltSphere)ᶜ : Set (S.data p).UpperLevel),
        (S.data p).LowerLevel),
      (∀ x, ∃ t : ℝ, S.flow t x.val.val = (D x).val) ∧
      (∀ x (y : (S.data p).LowerLevel) (t : ℝ), S.flow t x.val.val = y.val → D x = y) ∧
      ∀ (w : sphere (0 : (S.data p).chart.PositiveCoordinates) 1)
        (s : unitInterval) (hs : 0 < (s : ℝ)),
        (D.comp (nativeUpperMeridianInComplement S p w s hs)).Homotopic
          (S.data p).surgery.attachingSphere := by
  obtain ⟨D, horbit, hunique⟩ := S.exists_belt_complement_lower_transport hf p u v
  refine ⟨D, horbit, hunique, ?_⟩
  intro w s hs
  rw [lower_transport_upperMeridian_eq S p D hunique w s hs]
  exact nativeLowerMeridian_homotopic_attaching S p w s

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
