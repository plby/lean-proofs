import Wikipedia.NoExoticSixSphere.SphereCapComparisonScaleHomotopy
import Wikipedia.NoExoticSixSphere.SphereResolutionPinchComparison
import Wikipedia.NoExoticSixSphere.SpherePinchHomotopy

/-!
# The actual comparison pinch is independent of positive cap scale up to homotopy

Both input homotopies fix the common value at the collapsed pole. The
southern reflection is retained throughout. Their pinch is a homotopy
relative to the actual equator of the original source sphere.
-/

noncomputable section

open Set Function Topology

namespace NoExoticSixSphere.SphereSumNeck

open GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] (F G : C(Sphere 3, M))
  {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)

def northPinchScaleHomotopy :
    (northPinchInput F ε hε.ne').HomotopyRel (northPinchInput F δ hδ.ne')
      {antipode pinchPole} :=
  (capComparisonScaleHomotopy hε hδ).compContinuousMap F

def southPinchScaleHomotopy :
    (southPinchInput G ε hε.ne').HomotopyRel (southPinchInput G δ hδ.ne')
      {antipode pinchPole} := by
  let H := capComparisonScaleHomotopy hε hδ
  refine {
    toFun := fun p ↦ G (H (p.1, tailReflection p.2))
    continuous_toFun := G.continuous.comp (H.continuous.comp
      (continuous_fst.prodMk (contMDiff_tailReflection.continuous.comp continuous_snd)))
    map_zero_left := fun x ↦ congrArg G (H.toHomotopy.map_zero_left (tailReflection x))
    map_one_left := fun x ↦ congrArg G (H.toHomotopy.map_one_left (tailReflection x))
    prop' := ?_ }
  intro t x hx
  rcases mem_singleton_iff.mp hx with rfl
  change G (H (t, tailReflection (antipode pinchPole))) =
    G (capComparisonMap ε hε.ne' (tailReflection (antipode pinchPole)))
  rw [tailReflection_base]
  exact congrArg G (H.eq_fst t (mem_singleton _))

def comparisonPinchScaleHomotopy (hzero : F (sourceChart 0) = G (sourceChart 0)) :
    (comparisonPinch F G ε hε.ne' hzero).HomotopyRel
      (comparisonPinch F G δ hδ.ne' hzero) (equator pinchPole) :=
  SphereFold.pinchHomotopyRel pinchPole
    (northPinchInput F ε hε.ne') (southPinchInput G ε hε.ne')
    (northPinchInput F δ hδ.ne') (southPinchInput G δ hδ.ne')
    (pinchInput_base F G ε hε.ne' hzero) (pinchInput_base F G δ hδ.ne' hzero)
    (northPinchScaleHomotopy F hε hδ) (southPinchScaleHomotopy G hε hδ)

theorem comparisonPinch_scale_homotopic (hzero : F (sourceChart 0) = G (sourceChart 0)) :
    (comparisonPinch F G ε hε.ne' hzero).Homotopic
      (comparisonPinch F G δ hδ.ne' hzero) :=
  ⟨(comparisonPinchScaleHomotopy F G hε hδ hzero).toHomotopy⟩

end NoExoticSixSphere.SphereSumNeck
