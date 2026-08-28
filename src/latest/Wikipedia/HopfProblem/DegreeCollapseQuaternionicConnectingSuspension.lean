import Wikipedia.HopfProblem.DegreeCollapseSphereLiftFamily
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSequence

/-!
# The original symplectic connecting map under suspended precomposition

Joint descent of an actual lift supplies a continuous family on time
times the sphere. Pulling it back along a based sphere map gives a lift
of the original product suspension. Its terminal face is exactly
precomposition of the original clutching sphere map.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.DegreeCollapse.QuaternionicConnectingSuspension

open NoExoticSixSphere SmoothCube CubicalSphereSuspension
open Wikipedia.HomotopyGroupsOfSpheres QuaternionicFibration

variable {n : ℕ} (hn : 0 < n) {p : BasedMap (n + 1) BaseSphere north}
  (L : CubeLift (toGenLoop p))

def boundarySphere : BasedMap n northSubgroup 1 := (basedEquiv hn).symm L.endpoint

theorem boundarySphere_point (z : NoExoticSixSphere.Sphere n) :
    ((boundarySphere hn L).val z).val =
      SphereLiftFamily.descend L.map L.boundary hn (1, z) :=
  (SphereLiftFamily.descend_final L.map L.boundary hn inclusion L.endpoint
    (fun _ ↦ rfl) z).symm

theorem boundarySphere_class :
    sphereClass (boundarySphere hn L) = connecting n (sphereClass p) := by
  have he : toGenLoop (boundarySphere hn L) = L.endpoint :=
    (basedEquiv hn).apply_symm_apply L.endpoint
  exact (congrArg Quotient.mk' he).trans (connecting_eq_endpoint (toGenLoop p) L).symm

def precompose {k : ℕ} (g : SphereComposition.Based k n) :
    CubeLift (toGenLoop (SphereLiftFamily.compose p (productBasedMap g))) where
  map := SphereLiftFamily.precompose L.map L.boundary hn g
  initial := SphereLiftFamily.precompose_initial L.map L.boundary hn g L.initial
  project := SphereLiftFamily.precompose_project L.map L.boundary hn g projection p.val L.project
  boundary := SphereLiftFamily.precompose_boundary L.map L.boundary hn g

theorem precompose_endpoint {k : ℕ} (g : SphereComposition.Based k n) :
    (precompose hn L g).endpoint =
      toGenLoop (SphereLiftFamily.compose (boundarySphere hn L) g) := by
  apply GenLoop.ext
  intro u
  apply Subtype.ext
  change SphereLiftFamily.descend L.map L.boundary hn (1, g.val (quotient k u)) =
    ((boundarySphere hn L).val (g.val (quotient k u))).val
  exact (boundarySphere_point hn L _).symm

theorem connecting_suspended_precomposition {k : ℕ} (g : SphereComposition.Based k n) :
    connecting k (sphereClass (SphereLiftFamily.compose p (productBasedMap g))) =
      sphereClass (SphereLiftFamily.compose (boundarySphere hn L) g) :=
  (connecting_eq_endpoint
    (toGenLoop (SphereLiftFamily.compose p (productBasedMap g))) (precompose hn L g)).trans
      (congrArg Quotient.mk' (precompose_endpoint hn L g))

theorem connecting_suspension_map {k : ℕ} [NeZero k]
    (c : π_ k (NoExoticSixSphere.Sphere n) (spherePole n)) :
    connecting k (HigherHomotopy.map (N := Fin (k + 1)) p.val p.property (hom k n c)) =
      HigherHomotopy.map (N := Fin k) (boundarySphere hn L).val
        (boundarySphere hn L).property c := by
  obtain ⟨g, rfl⟩ := sphereClass_surjective (Nat.pos_of_neZero k) c
  rw [hom_sphereClass, ← SphereLiftFamily.sphereClass_compose,
    ← SphereLiftFamily.sphereClass_compose]
  exact connecting_suspended_precomposition hn L g

end Wikipedia.HopfProblem.DegreeCollapse.QuaternionicConnectingSuspension

