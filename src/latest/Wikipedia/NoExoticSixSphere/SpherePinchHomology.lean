import Wikipedia.NoExoticSixSphere.SphereHemisphereCollapse
import Wikipedia.NoExoticSixSphere.SphereThreeAntipodalHomotopy
import Wikipedia.NoExoticSixSphere.SphereHemisphereExchange
import Wikipedia.NoExoticSixSphere.SphereCapPinchCoordinates
import Wikipedia.HopfProblem.CuspCentralHomologyAttachingCrossNull

/-!
# The original geometric sphere pinch adds actual singular homology maps

The two hemisphere collapses are genuinely homotopic to the identity on
the three-sphere. Closed-hemisphere exchange splits the pinch into those
two collapsed inputs and a constant map. Homotopy invariance and vanishing
of the constant map in positive degree give the actual homology sum.
-/

noncomputable section

namespace NoExoticSixSphere.SphereFold

open SphereSumNeck
open Wikipedia.HopfProblem.SingularMayerVietoris
open Wikipedia.HopfProblem.PeriodTorusHigherHomology
open Wikipedia.HopfProblem.CuspCentralHomology

def southCollapseHomotopy (v : Sphere 3) :
    (ContinuousMap.id (Sphere 3)).Homotopy (southCollapse v) := by
  have hs : southCollapse v = (northCollapse v).comp SphereThreeAntipodal.map := by
    apply ContinuousMap.ext
    exact southCollapse_eq_north_antipode v
  rw [hs]
  exact SphereThreeAntipodal.homotopy.trans
    ((northCollapseHomotopy v).compContinuousMap SphereThreeAntipodal.map)

variable {Y : Type} [TopologicalSpace Y]

theorem homologyMap_comp_northCollapse (f : C(Sphere 3, Y)) (v : Sphere 3) (n : ℕ) :
    singularHomologyMap (f.comp (northCollapse v)) n = singularHomologyMap f n := by
  rw [singularHomologyMap_comp, ← homotopy_homologyMap (northCollapseHomotopy v) n,
    singularHomologyMap_id, LinearMap.comp_id]

theorem homologyMap_comp_southCollapse (g : C(Sphere 3, Y)) (v : Sphere 3) (n : ℕ) :
    singularHomologyMap (g.comp (southCollapse v)) n = singularHomologyMap g n := by
  rw [singularHomologyMap_comp, ← homotopy_homologyMap (southCollapseHomotopy v) n,
    singularHomologyMap_id, LinearMap.comp_id]

theorem homologyMap_pinch (f g : C(Sphere 3, Y))
    (hbase : f (antipode pinchPole) = g (antipode pinchPole)) (n : ℕ) (hn : n ≠ 0) :
    singularHomologyMap (pinch pinchPole f g hbase) n =
      singularHomologyMap f n + singularHomologyMap g n := by
  let N := f.comp (northCollapse pinchPole)
  let S := g.comp (southCollapse pinchPole)
  let c := ContinuousMap.const (Sphere 3) (f (antipode pinchPole))
  have hN₀ : ∀ x : Sphere 3, 0 ≤ x.val 0 → pinch pinchPole f g hbase x = N x := by
    intro x hx
    have hh : 0 ≤ height pinchPole x := by rwa [pinchPole_height]
    change pinch pinchPole f g hbase x = f (northCollapse pinchPole x)
    rw [pinch_north _ _ _ _ x hh, northCollapse_north _ _ hh]
  have hN₁ : ∀ x : Sphere 3, 0 ≤ x.val 0 → S x = c x := by
    intro x hx
    have hh : 0 ≤ height pinchPole x := by rwa [pinchPole_height]
    change g (southCollapse pinchPole x) = f (antipode pinchPole)
    rw [southCollapse_north _ _ hh]
    exact hbase.symm
  have hS₀ : ∀ x : Sphere 3, x.val 0 ≤ 0 → pinch pinchPole f g hbase x = S x := by
    intro x hx
    have hh : height pinchPole x ≤ 0 := by rwa [pinchPole_height]
    change pinch pinchPole f g hbase x = g (southCollapse pinchPole x)
    rw [pinch_south _ _ _ _ x hh, southCollapse_south _ _ hh]
  have hS₁ : ∀ x : Sphere 3, x.val 0 ≤ 0 → N x = c x := by
    intro x hx
    have hh : height pinchPole x ≤ 0 := by rwa [pinchPole_height]
    change f (northCollapse pinchPole x) = f (antipode pinchPole)
    rw [northCollapse_south _ _ hh]
  have h := HemisphereExchange.homologyMap_exchange (pinch pinchPole f g hbase)
    N S c hN₀ hN₁ hS₀ hS₁ n
  change singularHomologyMap (pinch pinchPole f g hbase) n +
    singularHomologyMap (ContinuousMap.const (Sphere 3) (f (antipode pinchPole))) n =
      singularHomologyMap (f.comp (northCollapse pinchPole)) n +
        singularHomologyMap (g.comp (southCollapse pinchPole)) n at h
  simpa only [singularHomologyMap_const_eq_zero _ _ n hn, add_zero,
    homologyMap_comp_northCollapse, homologyMap_comp_southCollapse] using h

end NoExoticSixSphere.SphereFold
