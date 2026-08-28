import Wikipedia.NoExoticSixSphere.LowCollaredStateClopenRestriction
import Wikipedia.NoExoticSixSphere.CircleCylinderLowCollaredState

/-!
# The actual circle component as a native framed collared state

Select a genuine connected component of the compact circle double.
Its collar boundary consists exactly of the original endpoint points
lying in that component. The literal fold proves path connectedness of
its positive half whenever the chosen point has nonnegative time.
The full endpoint disjoint union is not assumed connected.
-/

noncomputable section

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace NoExoticSixSphere.CircleCylinder

open GLOrthonormalization Wikipedia.HopfProblem.DegreeCollapse

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)

def componentOpen (k : ℕ) (hd : m = n + k) (p : Fiber d) : Opens (Fiber d) :=
  ⟨connectedComponent p, (isClopen_component d k hd p).isOpen⟩

theorem componentOpen_closed (k : ℕ) (hd : m = n + k) (p : Fiber d) :
    IsClosed (componentOpen d k hd p : Set (Fiber d)) :=
  (isClopen_component d k hd p).isClosed

def componentEndpoints (k : ℕ) (hd : m = n + k) (p : Fiber d) : Opens (Endpoints d) :=
  (timeCollar d).clopenBoundary (componentOpen d k hd p)

theorem mem_componentEndpoints (k : ℕ) (hd : m = n + k) (p : Fiber d) (q : Endpoints d) :
    q ∈ componentEndpoints d k hd p ↔ endpointsMap d q ∈ connectedComponent p := by
  change ((timeCollar d).zeroPoint q).val ∈ connectedComponent p ↔ _
  rw [timeCollar_zeroPoint]

def componentState (hd : m = n + 6) (a : Sphere 1 × Sphere m) (p : Fiber d) :
    LowCollaredSevenState (componentEndpoints d 6 hd p) :=
  (lowCollaredState d hd a).restrictClopen (componentOpen d 6 hd p) (componentOpen_closed d 6 hd p)

theorem componentState_pathConnected (hd : m = n + 6) (a : Sphere 1 × Sphere m) (p : Fiber d) :
    PathConnectedSpace (componentState d hd a p).Space :=
  isPathConnected_iff_pathConnectedSpace.mp (isPathConnected_component d 6 hd p)

def componentStatePositiveHomeomorph (hd : m = n + 6) (a : Sphere 1 × Sphere m) (p : Fiber d) :
    (componentState d hd a p).PositiveHalf ≃ₜ ComponentPositiveHalf d p where
  toFun q := ⟨q.val.val, q.val.property, q.property⟩
  invFun q := ⟨⟨q.val, q.property.1⟩, q.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    have h₁ : Continuous (Subtype.val : (componentState d hd a p).PositiveHalf →
        componentOpen d 6 hd p) := continuous_subtype_val
    have h₂ : Continuous (Subtype.val : componentOpen d 6 hd p → Fiber d) := continuous_subtype_val
    exact (h₂.comp h₁).subtype_mk _
  continuous_invFun := by
    have hv : Continuous (Subtype.val : ComponentPositiveHalf d p → Fiber d) :=
      continuous_subtype_val
    have hr : Continuous (fun q : ComponentPositiveHalf d p ↦
        (⟨q.val, q.property.1⟩ : componentOpen d 6 hd p)) := hv.subtype_mk _
    exact hr.subtype_mk _

theorem componentState_positiveHalf_pathConnected (hd : m = n + 6)
    (a : Sphere 1 × Sphere m) (p : Fiber d) (hp : 0 ≤ time d p) :
    PathConnectedSpace (componentState d hd a p).PositiveHalf := by
  let := pathConnectedSpace_componentPositiveHalf d 6 hd p hp
  exact (componentStatePositiveHomeomorph d hd a p).symm.surjective.pathConnectedSpace
    (componentStatePositiveHomeomorph d hd a p).symm.continuous

end NoExoticSixSphere.CircleCylinder
