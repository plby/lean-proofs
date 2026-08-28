import Wikipedia.NoExoticSixSphere.JamesFiltration
import Mathlib.Topology.Connected.PathConnected

/-!
# Path connectedness of the actual James space

Each finite word can be connected to the empty word by a path in its
Cartesian-power presentation. This works for any path-connected pointed
space, without assuming a CW structure or a loop-space equivalence.
-/

namespace NoExoticSixSphere.James

variable {X : Type*} [TopologicalSpace X] [PathConnectedSpace X] (x₀ : X)

theorem joined_one (w : Space X x₀) : Joined (1 : Space X x₀) w := by
  obtain ⟨⟨n, v⟩, rfl⟩ := presentation_surjective x₀ w
  have h := (PathConnectedSpace.joined (fun _ : Fin n ↦ x₀) v).map
    (continuous_word_array x₀ n)
  simpa only [List.ofFn_const, word_replicate_basepoint, presentation] using h

instance : PathConnectedSpace (Space X x₀) where
  nonempty := ⟨1⟩
  joined v w := (joined_one x₀ v).symm.trans (joined_one x₀ w)

end NoExoticSixSphere.James
