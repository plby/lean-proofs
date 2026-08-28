import Wikipedia.HopfProblem.DegreeCollapseProductSphereFiber
import Wikipedia.HopfProblem.DegreeCollapseQuaternionicHopfSouthNormal

/-!
# The actual polynomial Hopf smash square has a specified S3 × S3 fiber

Use the south value of the original polynomial, the zero slice of its
ORIGINAL product suspension, and the ORIGINAL sphere pairing. The whole
fiber of the actual map (E nu) smash (E nu) is homeomorphic to S3 × S3,
with its precise ambient inclusion retained. This is the map defining
QuaternionicHopf.suspendedSmashClass, not a new stable representative.
Global smoothing, regularity of this product fiber and its induced
normal-framing comparison are separate remaining obligations.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.QuaternionicHopfProductFiber

open NoExoticSixSphere QuaternionicHopf

def suspendedPoint : Sphere 5 := ProductSphereFiber.slice 4 QuaternionicHopfSouthFiber.point

theorem suspendedPoint_ne_pole : suspendedPoint ≠ spherePole 5 := by
  intro h
  exact QuaternionicHopfSouthFiber.point_ne_pole
    ((ProductSphereFiber.slice_eq_pole_iff 4 QuaternionicHopfSouthFiber.point).mp h)

def suspendedFiberHomeomorph :
    Sphere 3 ≃ₜ SmashFiberProduct.Fiber suspendedMap suspendedPoint :=
  QuaternionicHopfSouthFiber.fiberHomeomorph.trans
    (ProductSphereFiber.fiberHomeomorph basedMap QuaternionicHopfSouthFiber.point
      QuaternionicHopfSouthFiber.point_ne_pole)

theorem suspendedFiberHomeomorph_val (q : Sphere 3) :
    (suspendedFiberHomeomorph q).val =
      ProductSphereFiber.slice 7 (QuaternionicHopfSouthFiber.fiberPoint q) := rfl

def point : Sphere 10 := SmashFiberProduct.point suspendedPoint

theorem point_ne_pole : point ≠ spherePole 10 :=
  SmashFiberProduct.point_ne_pole suspendedPoint suspendedPoint_ne_pole

def fiberHomeomorph :
    Sphere 3 × Sphere 3 ≃ₜ
      {x : Sphere 16 // SphereSmash.squareMap suspendedMap x = point} :=
  (suspendedFiberHomeomorph.prodCongr suspendedFiberHomeomorph).trans
    (SmashFiberProduct.fiberHomeomorph suspendedMap suspendedPoint suspendedPoint_ne_pole)

theorem fiberHomeomorph_val (p : Sphere 3 × Sphere 3) :
    (fiberHomeomorph p).val = JamesSphere.pairing 8
      (ProductSphereFiber.slice 7 (QuaternionicHopfSouthFiber.fiberPoint p.1),
        ProductSphereFiber.slice 7 (QuaternionicHopfSouthFiber.fiberPoint p.2)) := rfl

theorem square_fiber_range (x : Sphere 16) :
    SphereSmash.squareMap suspendedMap x = point ↔
      ∃ p : Sphere 3 × Sphere 3, JamesSphere.pairing 8
        (ProductSphereFiber.slice 7 (QuaternionicHopfSouthFiber.fiberPoint p.1),
          ProductSphereFiber.slice 7 (QuaternionicHopfSouthFiber.fiberPoint p.2)) = x := by
  constructor
  · intro hx
    obtain ⟨p, hp⟩ := fiberHomeomorph.surjective ⟨x, hx⟩
    exact ⟨p, (fiberHomeomorph_val p).symm.trans (congrArg Subtype.val hp)⟩
  · rintro ⟨p, rfl⟩
    rw [← fiberHomeomorph_val]
    exact (fiberHomeomorph p).property

end Wikipedia.HopfProblem.DegreeCollapse.QuaternionicHopfProductFiber

