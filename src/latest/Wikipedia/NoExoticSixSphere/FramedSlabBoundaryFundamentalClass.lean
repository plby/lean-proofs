import Wikipedia.NoExoticSixSphere.RegularSlabBoundaryFundamentalClass

/-!
# Fundamental classes and cap compatibility for the retained boundary atlas

The boundary is the actual manifold boundary predicate in `A.atlas`,
and its fundamental class is constructed using the original
`A.boundaryAtlas`. The original homology connecting map sends the
slab's relative class to this class. The cap square and its kernel
criterion therefore concern the retained boundary, not a replacement.
-/

noncomputable section

open Module Set
open scoped Manifold ContDiff
open Wikipedia.HopfProblem SphereHomologyCoefficients SingularMayerVietoris

namespace NoExoticSixSphere.RegularCollaredCylinder.FramedSlabData

open CylinderFiberSlab
open ModTwoCapProduct (Coefficient)

variable {m n : ℕ} {z : Sphere n} {s t : ℝ}
  {d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) z s t}
  {k : ℕ} {hd : m = n + k} {a : Sphere m} (A : d.FramedSlabData k hd a)

theorem nativeBoundaryCompactSpace : CompactSpace A.nativeBoundary := by
  let := CylinderFiberSlab.compactSpace d.map z s t
  have hc : IsCompact A.nativeBoundary := by
    rw [A.nativeBoundary_eq_ends]
    exact (BoundaryPush.isClosed_ends d.map z s t).isCompact
  exact isCompact_iff_compactSpace.mp hc

def nativeRelativeFundamentalClass (r : ℕ) (hk : k = r + 3) :
    RelativeCoefficients.ModHomology 2 A.nativeBoundary (r + 4) :=
  d.relativeFundamentalClassOnBoundary (r + 1) (by
    simp only [finrank_prod, finrank_self, finrank_euclideanSpace_fin]
    omega) A.nativeBoundary A.nativeBoundary_eq_ends

def nativeBoundaryFundamentalClass (r : ℕ) (hk : k = r + 3) :
    ModHomology 2 A.nativeBoundary (r + 3) :=
  letI := A.atlas
  letI : ChartedSpace (EuclideanSpace ℝ (Fin k)) A.nativeBoundary := A.boundaryAtlas
  letI := A.nativeBoundaryCompactSpace
  letI : Fact (finrank ℝ (EuclideanSpace ℝ (Fin k)) = (r + 2) + 1) :=
    ⟨by simpa only [finrank_euclideanSpace_fin] using hk⟩
  ManifoldFundamentalClass.fundamentalClass (E := EuclideanSpace ℝ (Fin k)) r A.nativeBoundary

theorem connecting_nativeRelativeFundamentalClass (r : ℕ) (hk : k = r + 3) :
    RelativeCoefficients.connecting Coefficient A.nativeBoundary (r + 3)
        (A.nativeRelativeFundamentalClass r hk) = A.nativeBoundaryFundamentalClass r hk := by
  let := A.atlas
  let : ChartedSpace (EuclideanSpace ℝ (Fin k)) A.nativeBoundary := A.boundaryAtlas
  let := A.nativeBoundaryCompactSpace
  let : Fact (finrank ℝ (EuclideanSpace ℝ (Fin k)) = (r + 2) + 1) :=
    ⟨by simpa only [finrank_euclideanSpace_fin] using hk⟩
  exact d.connecting_relativeFundamentalClassOnBoundary (E := EuclideanSpace ℝ (Fin k)) r
    (by
      simp only [finrank_prod, finrank_self, finrank_euclideanSpace_fin]
      omega) A.nativeBoundary A.nativeBoundary_eq_ends

theorem nativeRelativeCap_bijective (r : ℕ) (hk : k = r + 3)
    (p q : ℕ) (h : p + q = r + 4) :
    Function.Bijective (fun b : RelativeModTwoCochains.Cohomology A.nativeBoundary p ↦
      RelativeModTwoCap.capProductInDegree A.nativeBoundary h b
        (A.nativeRelativeFundamentalClass r hk)) :=
  d.cap_relativeFundamentalClassOnBoundary_bijective (r + 1) (by
    simp only [finrank_prod, finrank_self, finrank_euclideanSpace_fin]
    omega) A.nativeBoundary A.nativeBoundary_eq_ends p q h

theorem nativeConnectingCap (r : ℕ) (hk : k = r + 3)
    (p q : ℕ) (h : p + q = r + 3) (b : ModTwoCapProduct.Cohomology A.nativeBoundary p) :
    RelativeModTwoCap.capProductInDegree A.nativeBoundary
        (p := p + 1) (q := q) (n := r + 4) (by omega)
        (RelativeModTwoCochains.connecting A.nativeBoundary p b)
        (A.nativeRelativeFundamentalClass r hk) =
      modHomologyMap 2 (subtypeInclusion A.nativeBoundary) q
        (ModTwoCapProduct.capProductInDegree A.nativeBoundary h b
          (A.nativeBoundaryFundamentalClass r hk)) := by
  have he := RelativeModTwoCap.pair_connecting_capInDegree A.nativeBoundary h b
    (A.nativeRelativeFundamentalClass r hk)
  rw [A.connecting_nativeRelativeFundamentalClass] at he
  exact he

theorem nativeBoundaryCap_kernel (r : ℕ) (hk : k = r + 3)
    (p q : ℕ) (h : p + q = r + 3) (b : ModTwoCapProduct.Cohomology A.nativeBoundary p) :
    modHomologyMap 2 (subtypeInclusion A.nativeBoundary) q
        (ModTwoCapProduct.capProductInDegree A.nativeBoundary h b
          (A.nativeBoundaryFundamentalClass r hk)) = 0 ↔
      ∃ c : ModTwoCapProduct.Cohomology (slab d.map z s t) p,
        ModTwoCapProduct.cohomologyPullback (subtypeInclusion A.nativeBoundary) p c = b := by
  have he := RelativeModTwoCap.pair_connecting_cap_kernel A.nativeBoundary h b
    (A.nativeRelativeFundamentalClass r hk)
    (A.nativeRelativeCap_bijective r hk (p + 1) q (by omega)).injective
  rw [A.connecting_nativeRelativeFundamentalClass] at he
  exact he

end NoExoticSixSphere.RegularCollaredCylinder.FramedSlabData
