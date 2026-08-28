import Wikipedia.NoExoticSixSphere.FramedSlabBoundaryFundamentalClass
import Wikipedia.NoExoticSixSphere.MiddleCapKernelOrthogonality
import Wikipedia.NoExoticSixSphere.GeometricCapPairingComparison

/-!
# Self-orthogonality of the actual boundary inclusion kernel

The retained six-dimensional boundary atlas supplies its original cap
pairing. The proved boundary cap kernel criterion and actual evaluation
naturality give self-orthogonality when the boundary and filling are
actually two-connected. Constructing a framing-preserving surgery to
produce such a filling is not assumed to have been done here.
-/

noncomputable section

open Module
open scoped Manifold ContDiff Topology
open Wikipedia.HopfProblem SphereHomologyCoefficients SingularMayerVietoris

namespace NoExoticSixSphere.RegularCollaredCylinder.FramedSlabData

open CylinderFiberSlab GLOrthonormalization

attribute [local instance] modHomologyModule

variable {m n : ℕ} {z : Sphere n} {s t : ℝ}
  {d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) z s t}
  {hd : m = n + 6} {a : Sphere m} (A : d.FramedSlabData 6 hd a)
  [SimplyConnectedSpace A.nativeBoundary] (b₀ : A.nativeBoundary)
  [Subsingleton (π_ 2 A.nativeBoundary b₀)]
  [SimplyConnectedSpace (slab d.map z s t)] (w₀ : slab d.map z s t)
  [hW₂ : Subsingleton (π_ 2 (slab d.map z s t) w₀)]

include w₀ hW₂

theorem nativeBoundaryKernel_selfOrthogonal (b : ModHomology 2 A.nativeBoundary 3) :
    letI := A.atlas
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 6)) A.nativeBoundary := A.boundaryAtlas
    letI := A.nativeBoundaryCompactSpace
    letI : Fact (finrank ℝ (EuclideanSpace ℝ (Fin 6)) = (3 + 2) + 1) :=
      ⟨finrank_euclideanSpace_fin⟩
    (∀ c : ModHomology 2 A.nativeBoundary 3,
      modHomologyMap 2 (subtypeInclusion A.nativeBoundary) 3 c = 0 →
        MiddleCapEvaluation.pairing (E := EuclideanSpace ℝ (Fin 6)) b₀ c b = 0) ↔
      modHomologyMap 2 (subtypeInclusion A.nativeBoundary) 3 b = 0 := by
  let := A.atlas
  let : ChartedSpace (EuclideanSpace ℝ (Fin 6)) A.nativeBoundary := A.boundaryAtlas
  let := A.nativeBoundaryCompactSpace
  let : Fact (finrank ℝ (EuclideanSpace ℝ (Fin 6)) = (3 + 2) + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  apply MiddleCapEvaluation.kernel_selfOrthogonal (E := EuclideanSpace ℝ (Fin 6))
    b₀ w₀ (subtypeInclusion A.nativeBoundary)
  intro c
  exact A.nativeBoundaryCap_kernel 3 rfl 3 3 rfl c

theorem nativeBoundaryGeometricKernel_selfOrthogonal (b : ModHomology 2 A.nativeBoundary 3) :
    letI := A.atlas
    letI : ChartedSpace (Vector 6) A.nativeBoundary := A.boundaryAtlas
    letI : IsManifold (𝓡 6) ∞ A.nativeBoundary := A.boundaryManifold
    letI := A.nativeBoundaryCompactSpace
    ∀ (e : EuclideanEmbedding 6 A.nativeBoundary)
      (_f : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)
      (r : EuclideanEmbedding.TubularRetraction e),
      (∀ c : ModHomology 2 A.nativeBoundary 3,
        modHomologyMap 2 (subtypeInclusion A.nativeBoundary) 3 c = 0 →
          EuclideanEmbedding.modTwoHomologyIntersection e r b₀ c b = 0) ↔
        modHomologyMap 2 (subtypeInclusion A.nativeBoundary) 3 b = 0 := by
  let := A.atlas
  let : ChartedSpace (Vector 6) A.nativeBoundary := A.boundaryAtlas
  let : IsManifold (𝓡 6) ∞ A.nativeBoundary := A.boundaryManifold
  let := A.nativeBoundaryCompactSpace
  intro e f r
  simp_rw [← EuclideanEmbedding.cap_pairing_eq_geometric e f r b₀]
  exact A.nativeBoundaryKernel_selfOrthogonal b₀ w₀ b

theorem nativeBoundaryQuadraticKernel_selfOrthogonal (b : ModHomology 2 A.nativeBoundary 3) :
    letI := A.atlas
    letI : ChartedSpace (Vector 6) A.nativeBoundary := A.boundaryAtlas
    letI : IsManifold (𝓡 6) ∞ A.nativeBoundary := A.boundaryManifold
    letI := A.nativeBoundaryCompactSpace
    ∀ (e : EuclideanEmbedding 6 A.nativeBoundary)
      (f : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)
      (r : EuclideanEmbedding.TubularRetraction e),
      (∀ c : ModHomology 2 A.nativeBoundary 3,
        modHomologyMap 2 (subtypeInclusion A.nativeBoundary) 3 c = 0 →
          (EuclideanEmbedding.modTwoHomologyQuadraticForm e f r b₀).polarBilin c b = 0) ↔
        modHomologyMap 2 (subtypeInclusion A.nativeBoundary) 3 b = 0 := by
  let := A.atlas
  let : ChartedSpace (Vector 6) A.nativeBoundary := A.boundaryAtlas
  let : IsManifold (𝓡 6) ∞ A.nativeBoundary := A.boundaryManifold
  let := A.nativeBoundaryCompactSpace
  intro e f r
  have hpol := EuclideanEmbedding.modTwoHomologyQuadraticForm_polar e f r b₀
  have hkernel := A.nativeBoundaryGeometricKernel_selfOrthogonal b₀ w₀ b e f r
  constructor
  · intro hb
    apply hkernel.mp
    intro c hc
    exact (LinearMap.congr_fun (LinearMap.congr_fun hpol c) b).symm.trans (hb c hc)
  · intro hb c hc
    exact (LinearMap.congr_fun (LinearMap.congr_fun hpol c) b).trans (hkernel.mpr hb c hc)

end NoExoticSixSphere.RegularCollaredCylinder.FramedSlabData
