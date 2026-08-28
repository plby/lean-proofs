import Wikipedia.NoExoticSixSphere.SphereDoublePointParity
import Wikipedia.NoExoticSixSphere.FreeInvolutionCardinality

/-!
# The actual unordered double points of a sphere map

These are the sheet-swap orbits of distinct source pairs with equal image.
For a self-transverse immersion this is a finite set. Its cardinality is
exactly half the ordered count. Its mod-two cardinality is a separate
geometric quantity and is not claimed to vanish or be homotopy invariant.
-/

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereSelfIntersections

open GLOrthonormalization InvolutionQuotient

variable {M : Type*} (f : Sphere 3 → M)

abbrev Unordered := Orbit (swap f) (swap_involutive f)

def unorderedProj : pairs f → Unordered f := proj (swap f) (swap_involutive f)

theorem unorderedProj_eq_iff (p q : pairs f) :
    unorderedProj f p = unorderedProj f q ↔ p = q ∨ swap f p = q :=
  proj_eq_iff (swap f) (swap_involutive f) p q

def unorderedParity : ZMod 2 := Nat.card (Unordered f)

theorem finite_unordered (hfin : (pairs f).Finite) : Finite (Unordered f) := by
  let := hfin.to_subtype
  infer_instance

theorem ordered_ncard_eq_twice_unordered (hfin : (pairs f).Finite) :
    (pairs f).ncard = 2 * Nat.card (Unordered f) := by
  let := hfin.to_subtype
  exact card_eq_twice_orbits (swap f) (swap_involutive f) (swap_ne f)

theorem unorderedParity_eq_half_ordered (hfin : (pairs f).Finite) :
    unorderedParity f = (((pairs f).ncard / 2 : ℕ) : ZMod 2) := by
  rw [ordered_ncard_eq_twice_unordered f hfin]
  simp [unorderedParity]

theorem unorderedParity_zero_of_injective (hi : Injective f) : unorderedParity f = 0 := by
  have hp : IsEmpty (pairs f) := ⟨fun p ↦ p.property.1 (hi p.property.2)⟩
  let := hp
  have hu : IsEmpty (Unordered f) := inferInstance
  let := hu
  simp [unorderedParity]

variable [TopologicalSpace M] [T2Space M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M]

theorem finite_unordered_of_selfTransverse
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
    (hi : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s))
    (ht : ∀ x y, x ≠ y → f x = f y → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) f x).coprod (mfderiv (𝓡 3) (𝓡 6) f y))) :
    Finite (Unordered f) := finite_unordered f (finite_pairs hf ht hi)

end NoExoticSixSphere.SphereSelfIntersections
