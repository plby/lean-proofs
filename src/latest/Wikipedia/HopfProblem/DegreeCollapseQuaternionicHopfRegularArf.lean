import Wikipedia.HopfProblem.DegreeCollapseQuaternionicHopfFiberArf
import Wikipedia.HopfProblem.DegreeCollapseGeometricArfAgreement
import Wikipedia.NoExoticSixSphere.GeometricArfNormalCoordinates
import Wikipedia.NoExoticSixSphere.RegularSphereFiberEmbedding

/-!
# Arf one in the original regular-sphere-fiber interface

The general regular-fiber obstruction uses head normal coordinates; the
explicit Hopf calculation uses tail coordinates. A fixed invertible change
relates them on the same original equation frame and Euclidean inclusion.
Its proved geometric invariance transfers the computed Arf value exactly.
-/

noncomputable section

open scoped Manifold ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.QuaternionicHopfRegularArf

open NoExoticSixSphere QuaternionicHopf QuaternionicHopfProductDiffeomorph
open QuaternionicHopfFramedFiber QuaternionicHopfFiberQuadratic

local instance : ChartedSpace (V 6) Fiber := fiberAtlas
local instance : IsManifold (𝓡 6) ∞ Fiber := fiber_isManifold
attribute [local instance] fiber_compact fiber_simplyConnected fiber_piTwo

theorem regularEmbedding_eq :
    RegularSphereFiber.embedding smoothMap smoothMap_contMDiff
      QuaternionicHopfProductFiber.point smoothMap_regular 6 (by decide) = embedding := rfl

def regularFrame (a : Sphere 16) :
    SmoothRangeFrame (𝓡 6) embedding.normalProjection embedding.NormalModel :=
  RegularSphereFiber.frame smoothMap smoothMap_contMDiff
    QuaternionicHopfProductFiber.point smoothMap_regular 6 (by decide) a

def normalChange : embedding.NormalModel ≃L[ℝ] embedding.NormalModel :=
  normalCoordinates.trans (RegularSphereFiber.normalCoordinates 6 (show 16 = 10 + 6 by decide)).symm

theorem regularFrame_ambient (a : Sphere 16) (x : Fiber) :
    (regularFrame a).ambient x = ((equationFrame a).ambient x).comp
      (RegularSphereFiber.normalCoordinates 6
        (show 16 = 10 + 6 by decide)).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro v
  rfl

theorem framing_ambient_recoordinate (a : Sphere 16) (x : Fiber) :
    (framing a).ambient x =
      ((regularFrame a).ambient x).comp normalChange.toContinuousLinearMap := by
  rw [framing_ambient, regularFrame_ambient]
  apply ContinuousLinearMap.ext
  intro v
  let Q := RegularSphereFiber.normalCoordinates 6 (show 16 = 10 + 6 by decide)
  change ((equationFrame a).ambient x) (normalCoordinates v) =
    ((equationFrame a).ambient x) (Q (Q.symm (normalCoordinates v)))
  rw [ContinuousLinearEquiv.apply_symm_apply]

variable (a : Sphere 16) (r : EuclideanEmbedding.TubularRetraction embedding) (x : Fiber)

theorem invariant_regularFrame_one :
    GeometricArf.invariant embedding (regularFrame a) r x = 1 := by
  have he := GeometricArf.invariant_eq_of_normal_coordinates embedding
    (regularFrame a) (framing a) r r x x normalChange (framing_ambient_recoordinate a)
  rw [← SurgeryDetector.actualGeometricArf_eq_invariant] at he
  exact he.trans (QuaternionicHopfFiberArf.actualGeometricArf_one a r x)

theorem originalRegularFiberArf_one :
    GeometricArf.invariant
      (RegularSphereFiber.embedding smoothMap smoothMap_contMDiff
        QuaternionicHopfProductFiber.point smoothMap_regular 6 (by decide))
      (RegularSphereFiber.frame smoothMap smoothMap_contMDiff
        QuaternionicHopfProductFiber.point smoothMap_regular 6 (by decide) a) r x = 1 :=
  invariant_regularFrame_one a r x

end Wikipedia.HopfProblem.DegreeCollapse.QuaternionicHopfRegularArf
