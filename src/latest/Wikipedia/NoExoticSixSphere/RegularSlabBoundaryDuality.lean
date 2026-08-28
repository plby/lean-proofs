import Wikipedia.NoExoticSixSphere.RegularSlabCompactSupportComparison
import Wikipedia.NoExoticSixSphere.RegularSlabInteriorCapDuality
import Wikipedia.NoExoticSixSphere.FramedSlabData

/-!
# Relative duality for the original regular collared filling slabs

The boundary-relative comparison, actual interior cap map, and original
interior inclusion give a bijection from relative cohomology to absolute
homology in complementary degrees. For the constructed framed filling
slabs the source subspace is identified with the actual boundary of the
retained manifold atlas. Compatibility with the boundary connecting map
and the geometric intersection pairing is not asserted here.
-/

noncomputable section

open Function Module
open scoped Manifold ContDiff

namespace NoExoticSixSphere.RegularCollaredCylinder

open CylinderFiberSlab
open Wikipedia.HopfProblem.SphereHomologyCoefficients

section General

variable {B H M C H' N : Type}
  [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
  [TopologicalSpace H] {I : ModelWithCorners ℝ B H} [I.Boundaryless]
  [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M]
  [NormedAddCommGroup C] [NormedSpace ℝ C] [FiniteDimensional ℝ C]
  [TopologicalSpace H'] {J : ModelWithCorners ℝ C H'} [J.Boundaryless]
  [TopologicalSpace N] [T2Space N] [ChartedSpace H' N] [IsManifold J ∞ N]
  {z : N} {s t : ℝ} (d : RegularCollaredCylinder (M := M) I J z s t)
  (n : ℕ) (hd : finrank ℝ (ℝ × B) = finrank ℝ C + (n + 3))

def boundaryDualityMap (p q : ℕ) (h : p + q = n + 3) :
    RelativeModTwoCochains.Cohomology (BoundaryPush.ends d.map z s t) p →ₗ[ℤ]
      ModHomology 2 (slab d.map z s t) q :=
  (d.interiorCapMap n hd p q h).comp (d.boundaryCompactSupportCanonical p).toLinearMap

theorem boundaryDualityMap_bijective (p q : ℕ) (h : p + q = n + 3) :
    Bijective (d.boundaryDualityMap n hd p q h) :=
  (d.interiorCapMap_bijective n hd p q h).comp (d.boundaryCompactSupportCanonical p).bijective

def boundaryDualityEquiv (p q : ℕ) (h : p + q = n + 3) :
    RelativeModTwoCochains.Cohomology (BoundaryPush.ends d.map z s t) p ≃ₗ[ℤ]
      ModHomology 2 (slab d.map z s t) q :=
  LinearEquiv.ofBijective (d.boundaryDualityMap n hd p q h)
    (d.boundaryDualityMap_bijective n hd p q h)

theorem boundaryDualityEquiv_toLinearMap (p q : ℕ) (h : p + q = n + 3) :
    (d.boundaryDualityEquiv n hd p q h).toLinearMap = d.boundaryDualityMap n hd p q h := rfl

end General

namespace FramedSlabData

variable {m n : ℕ} {z : Sphere n} {s t : ℝ}
  {d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) z s t}
  {k : ℕ} {hd : m = n + k} {a : Sphere m} (A : d.FramedSlabData k hd a)

def nativeBoundary : Set (slab d.map z s t) :=
  letI := A.atlas
  {p | ((𝓡∂ 1).prod (𝓡 k)).IsBoundaryPoint p}

theorem nativeBoundary_eq_ends : A.nativeBoundary = BoundaryPush.ends d.map z s t := by
  let := A.atlas
  ext p
  exact A.boundary_iff p

def nativeBoundaryDualityEquiv (r : ℕ) (hk : k = r + 2) (p q : ℕ) (hpq : p + q = r + 3) :
    RelativeModTwoCochains.Cohomology A.nativeBoundary p ≃ₗ[ℤ]
      ModHomology 2 (slab d.map z s t) q := by
  rw [A.nativeBoundary_eq_ends]
  apply d.boundaryDualityEquiv r _ p q hpq
  simp only [finrank_prod, finrank_self, finrank_euclideanSpace_fin]
  omega

end FramedSlabData

end NoExoticSixSphere.RegularCollaredCylinder
