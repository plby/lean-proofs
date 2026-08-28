import Wikipedia.NoExoticSixSphere.FatWedgeCofibration
import Wikipedia.NoExoticSixSphere.ProductHomotopyConnectivity

/-!
# Connectivity of the actual Cartesian powers and fat wedges

A point in a nonempty fat wedge has a basepoint coordinate. Paths to
the constant array can keep that coordinate fixed throughout, so the
entire path remains in the original fat wedge. Cartesian powers of a
simply connected space are simply connected by the actual product maps.
-/

noncomputable section

namespace NoExoticSixSphere.FatWedge

variable {X : Type*} [TopologicalSpace X]

theorem power_simplyConnected [SimplyConnectedSpace X] (k : ℕ) :
    SimplyConnectedSpace (Fin k → X) := by
  induction k with
  | zero => infer_instance
  | succ k ih =>
      let := ih
      let : SimplyConnectedSpace (X × (Fin k → X)) := HigherHomotopy.simplyConnected_product
      exact (split (X := X) k).toHomotopyEquiv.simplyConnectedSpace

variable (b : X)

def constantArray (k : ℕ) : space b (k + 1) := ⟨fun _ ↦ b, ⟨0, rfl⟩⟩

theorem joined_constant [PathConnectedSpace X] (k : ℕ) (v : space b (k + 1)) :
    Joined v (constantArray b k) := by
  classical
  obtain ⟨i, hi⟩ := v.property
  let p (j : Fin (k + 1)) : Path (v.val j) b :=
    if h : j = i then (Path.refl b).cast ((congrArg v.val h).trans hi) rfl
    else PathConnectedSpace.somePath (v.val j) b
  have hp (t : unitInterval) : (Path.pi p) t ∈ space b (k + 1) := by
    refine ⟨i, ?_⟩
    change p i t = b
    simp only [p, dif_pos rfl, Path.cast_coe, Path.refl_apply]
  exact ⟨{ toFun := fun t ↦ ⟨(Path.pi p) t, hp t⟩
           continuous_toFun := (Path.pi p).continuous.subtype_mk _
           source' := Subtype.ext (Path.pi p).source
           target' := Subtype.ext (Path.pi p).target }⟩

theorem pathConnectedSpace [PathConnectedSpace X] (k : ℕ) :
    PathConnectedSpace (space b (k + 1)) where
  nonempty := ⟨constantArray b k⟩
  joined v w := (joined_constant b k v).trans (joined_constant b k w).symm

end NoExoticSixSphere.FatWedge
