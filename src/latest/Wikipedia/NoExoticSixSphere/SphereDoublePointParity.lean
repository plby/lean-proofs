import Wikipedia.NoExoticSixSphere.SelfTransverseSphereDoublePoints
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.ZMod.Basic

/-!
# The ordered off-diagonal double-point count is even

Swapping the two distinct source points is a fixed-point-free involution.
The finite sum of ones modulo two therefore cancels in pairs. This is the
ordered double-point count, not yet a comparison with the intersection
number of a sphere and a perturbed copy of it.
-/

noncomputable section

open Function
open scoped BigOperators Manifold ContDiff

namespace NoExoticSixSphere.SphereSelfIntersections

open GLOrthonormalization

theorem ncard_cast_eq_zero {M : Type*} (f : Sphere 3 → M) (hfin : (pairs f).Finite) :
    ((pairs f).ncard : ZMod 2) = 0 := by
  classical
  let := hfin.fintype
  have hsum : (∑ _p : pairs f, (1 : ZMod 2)) = 0 :=
    Finset.sum_ninvolution (s := Finset.univ) (f := fun _ : pairs f ↦ (1 : ZMod 2))
      (swap f) (fun _ ↦ by decide) (fun p _ ↦ swap_ne f p)
      (fun _ ↦ Finset.mem_univ _) (swap_involutive f)
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    Set.fintypeCard_eq_ncard] using hsum

theorem even_ncard {M : Type*} (f : Sphere 3 → M) (hfin : (pairs f).Finite) :
    Even (pairs f).ncard := ZMod.natCast_eq_zero_iff_even.mp (ncard_cast_eq_zero f hfin)

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (Vector 6) M] [IsManifold (𝓡 6) ∞ M]

theorem even_ncard_of_selfTransverse {f : Sphere 3 → M}
    (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
    (hi : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s))
    (ht : ∀ x y, x ≠ y → f x = f y → Surjective
      ((mfderiv (𝓡 3) (𝓡 6) f x).coprod (mfderiv (𝓡 3) (𝓡 6) f y))) :
    Even (pairs f).ncard := even_ncard f (finite_pairs hf ht hi)

end NoExoticSixSphere.SphereSelfIntersections
