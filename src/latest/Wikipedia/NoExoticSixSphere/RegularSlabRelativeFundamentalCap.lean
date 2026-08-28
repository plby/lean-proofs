import Wikipedia.NoExoticSixSphere.RegularSlabRelativeFundamentalClass
import Wikipedia.NoExoticSixSphere.RegularSlabBoundaryDuality

/-!
# The slab duality map is cap with its actual relative fundamental class

Naturality for the original identity and interior inclusion identifies
the constructed duality map with the genuine relative cap product.
This proves cap-by-fundamental-class bijectivity. No compatibility with
the boundary connecting map is built into the definition or assumed.
-/

noncomputable section

open Set Module
open scoped Manifold ContDiff

namespace NoExoticSixSphere.RegularCollaredCylinder

open CylinderFiberSlab RelativeModTwoCochains
open Wikipedia.HopfProblem.SphereHomologyCoefficients

variable {B H M C H' N : Type}
  [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
  [TopologicalSpace H] {I : ModelWithCorners ℝ B H} [I.Boundaryless]
  [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M]
  [NormedAddCommGroup C] [NormedSpace ℝ C] [FiniteDimensional ℝ C]
  [TopologicalSpace H'] {J : ModelWithCorners ℝ C H'} [J.Boundaryless]
  [TopologicalSpace N] [T2Space N] [ChartedSpace H' N] [IsManifold J ∞ N]
  {z : N} {s t : ℝ} (d : RegularCollaredCylinder (M := M) I J z s t)
  (n : ℕ) (hd : finrank ℝ (ℝ × B) = finrank ℝ C + (n + 3))
  (a b : ℝ) (hsa : s < a) (hab : a ≤ b) (hbt : b < t)
  (hL : Icc s a ⊆ d.leftTimes) (hR : Icc b t ⊆ d.rightTimes)

theorem interiorCapMap_boundaryCompactSupportMap (p q : ℕ) (h : p + q = n + 3)
    (c : Cohomology (BoundaryPush.ends d.map z s t) p) :
    d.interiorCapMap n hd p q h (d.boundaryCompactSupportMap a b hsa hab hbt hL hR p c) =
      modHomologyMap 2 (InteriorPush.inclusion d.map z s t) q
        (RelativeModTwoCap.capProductInDegree
          (d.compactCore a b hsa hbt : Set (interiorDomain d.map z s t))ᶜ h
          (d.boundaryCoreEquiv a b hsa hab hbt hL hR p c)
          (d.coreFundamentalClass n hd a b hsa hbt)) := rfl

theorem cap_relativeFundamentalClassOnCore (p q : ℕ) (h : p + q = n + 3)
    (c : Cohomology (BoundaryPush.ends d.map z s t) p) :
    RelativeModTwoCap.capProductInDegree (BoundaryPush.ends d.map z s t) h c
        (d.relativeFundamentalClassOnCore n hd a b hsa hab hbt hL hR) =
      d.interiorCapMap n hd p q h
        (d.boundaryCompactSupportMap a b hsa hab hbt hL hR p c) := by
  obtain ⟨v, rfl⟩ := (d.collarToBoundaryEquiv a b hsa hab hbt hL hR p).surjective c
  have h₁ := RelativeModTwoCap.capProductInDegree_naturality
    (ContinuousMap.id (slab d.map z s t))
    (BoundaryPush.ends_subset_domain d.map z s t a b hsa hbt) h v
    (d.relativeFundamentalClassOnCore n hd a b hsa hab hbt hL hR)
  rw [modHomologyMap_id, LinearMap.id_apply] at h₁
  change RelativeModTwoCap.capProductInDegree (BoundaryPush.ends d.map z s t) h
    (d.collarToBoundaryEquiv a b hsa hab hbt hL hR p v)
    (d.relativeFundamentalClassOnCore n hd a b hsa hab hbt hL hR) =
      RelativeModTwoCap.capProductInDegree
        (BoundaryPush.domain d.map z s t a b : Set (slab d.map z s t)) h v
        (d.boundaryToCollarModEquiv a b hsa hab hbt hL hR 2 (by decide) (n + 3)
          (d.relativeFundamentalClassOnCore n hd a b hsa hab hbt hL hR)) at h₁
  rw [d.relativeFundamentalClassOnCore_collar] at h₁
  have h₂ := RelativeModTwoCap.capProductInDegree_naturality
    (InteriorPush.inclusion d.map z s t) (d.coreComplement_mapsTo_collar a b hsa hbt)
    h v (d.coreFundamentalClass n hd a b hsa hbt)
  rw [d.interiorCapMap_boundaryCompactSupportMap, d.boundaryCoreEquiv_collar]
  exact h₁.trans h₂.symm

omit [FiniteDimensional ℝ B] [I.Boundaryless] [T2Space M] [IsManifold I ∞ M]
  [FiniteDimensional ℝ C] [J.Boundaryless] [IsManifold J ∞ N] in
theorem boundaryCompactSupportCanonical_eq_map (p : ℕ) :
    (d.boundaryCompactSupportCanonical p).toLinearMap =
      d.boundaryCompactSupportMap a b hsa hab hbt hL hR p := by
  unfold boundaryCompactSupportCanonical
  exact d.boundaryCompactSupportMap_independent _ _ _ _ _ _ _ a b hsa hab hbt hL hR p

theorem cap_relativeFundamentalClass (p q : ℕ) (h : p + q = n + 3)
    (c : Cohomology (BoundaryPush.ends d.map z s t) p) :
    RelativeModTwoCap.capProductInDegree (BoundaryPush.ends d.map z s t) h c
        (d.relativeFundamentalClass n hd) = d.boundaryDualityMap n hd p q h c := by
  obtain ⟨a, b, hsa, hab, hbt, hL, hR⟩ := d.exists_inner_times
  rw [d.relativeFundamentalClass_eq_onCore n hd a b hsa hab hbt hL hR,
    d.cap_relativeFundamentalClassOnCore]
  unfold boundaryDualityMap
  rw [d.boundaryCompactSupportCanonical_eq_map a b hsa hab hbt hL hR]
  rfl

theorem cap_relativeFundamentalClass_bijective (p q : ℕ) (h : p + q = n + 3) :
    Function.Bijective (fun c : Cohomology (BoundaryPush.ends d.map z s t) p ↦
      RelativeModTwoCap.capProductInDegree (BoundaryPush.ends d.map z s t) h c
        (d.relativeFundamentalClass n hd)) := by
  have he : (fun c : Cohomology (BoundaryPush.ends d.map z s t) p ↦
      RelativeModTwoCap.capProductInDegree (BoundaryPush.ends d.map z s t) h c
        (d.relativeFundamentalClass n hd)) = d.boundaryDualityMap n hd p q h :=
    funext (d.cap_relativeFundamentalClass n hd p q h)
  rw [he]
  exact d.boundaryDualityMap_bijective n hd p q h

end NoExoticSixSphere.RegularCollaredCylinder
