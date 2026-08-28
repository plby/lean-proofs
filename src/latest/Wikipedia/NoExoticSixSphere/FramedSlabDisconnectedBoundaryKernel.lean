import Wikipedia.NoExoticSixSphere.FramedSlabBoundaryFundamentalClass
import Wikipedia.NoExoticSixSphere.ZeroSecondHomologyCapKernel
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleDisjoint

/-!
# The actual two-ended boundary kernel is self-orthogonal

The two endpoint fibers are separately two-connected; their disjoint
union is not declared connected. The retained boundary diffeomorphism
and the actual disjoint-union homology equivalence prove second homology
vanishing for the original native boundary. The original global cap and
evaluation pairing then identify the full boundary inclusion kernel
with its right annihilator, including classes involving both endpoints.

This is the actual cap pairing. Its comparison with the sum of the
original endpoint quadratic forms is still required for an Arf argument.
-/

noncomputable section

open Module
open scoped Manifold ContDiff Topology
open Wikipedia.HopfProblem SphereHomologyCoefficients SingularMayerVietoris

namespace NoExoticSixSphere.RegularCollaredCylinder.FramedSlabData

open CylinderFiberSlab PeriodTorusHigherHomology

local notation "V" => EuclideanSpace ℝ (Fin 6)

attribute [local instance] modHomologyModule

variable {m n : ℕ} {z : Sphere n} {s t : ℝ}
  {d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) z s t}
  {hd : m = n + 6} {a : Sphere m} (A : d.FramedSlabData 6 hd a)
  [SimplyConnectedSpace {x : Sphere m // d.leftMap x = z}]
  [SimplyConnectedSpace {x : Sphere m // d.rightMap x = z}]
  (l₀ : {x : Sphere m // d.leftMap x = z}) (r₀ : {x : Sphere m // d.rightMap x = z})
  [hL₂ : Subsingleton (π_ 2 {x : Sphere m // d.leftMap x = z} l₀)]
  [hR₂ : Subsingleton (π_ 2 {x : Sphere m // d.rightMap x = z} r₀)]

include l₀ r₀ hL₂ hR₂ in
theorem nativeBoundary_secondHomology_subsingleton :
    Subsingleton (SingularHomology A.nativeBoundary 2) := by
  let := A.atlas
  let : ChartedSpace V
      {p : slab d.map z s t // ((𝓡∂ 1).prod (𝓡 6)).IsBoundaryPoint p} := A.boundaryAtlas
  let := regularFiberAtlas d.leftMap d.smooth_left z d.regular_left 6 (by simpa using hd)
  let := regularFiberAtlas d.rightMap d.smooth_right z d.regular_right 6 (by simpa using hd)
  let : Subsingleton (SingularHomology {x : Sphere m // d.leftMap x = z} 2) :=
    TwoConnectedCoefficients.secondHomology_subsingleton l₀
  let : Subsingleton (SingularHomology {x : Sphere m // d.rightMap x = z} 2) :=
    TwoConnectedCoefficients.secondHomology_subsingleton r₀
  let : Subsingleton (SingularHomology
      ({x : Sphere m // d.leftMap x = z} ⊕ {x : Sphere m // d.rightMap x = z}) 2) :=
    (sumHomologyEquiv _ _ 2).injective.subsingleton
  exact (homeomorphHomologyEquiv A.boundaryDiffeomorph.toHomeomorph 2).surjective.subsingleton

def disconnectedBoundaryPairing :
    ModHomology 2 A.nativeBoundary 3 →ₗ[ZMod 2]
      ModHomology 2 A.nativeBoundary 3 →ₗ[ZMod 2] ZMod 2 := by
  let := A.atlas
  let : ChartedSpace (V) A.nativeBoundary := A.boundaryAtlas
  let := A.nativeBoundaryCompactSpace
  let : Fact (finrank ℝ (V) = (3 + 2) + 1) := ⟨finrank_euclideanSpace_fin⟩
  let := A.nativeBoundary_secondHomology_subsingleton l₀ r₀
  exact ZeroSecondHomologyCap.pairing (E := V) A.nativeBoundary

theorem disconnectedBoundaryPairing_nondegenerate :
    (A.disconnectedBoundaryPairing l₀ r₀).Nondegenerate := by
  let := A.atlas
  let : ChartedSpace (V) A.nativeBoundary := A.boundaryAtlas
  let := A.nativeBoundaryCompactSpace
  let : Fact (finrank ℝ (V) = (3 + 2) + 1) := ⟨finrank_euclideanSpace_fin⟩
  let := A.nativeBoundary_secondHomology_subsingleton l₀ r₀
  exact ZeroSecondHomologyCap.pairing_nondegenerate (E := V) A.nativeBoundary

theorem disconnectedBoundaryPairing_cap_reduction
    (b : ModTwoCapProduct.Cohomology A.nativeBoundary 3)
    (c : SingularHomology A.nativeBoundary 3) :
    letI := A.atlas
    letI : ChartedSpace (V) A.nativeBoundary := A.boundaryAtlas
    letI := A.nativeBoundaryCompactSpace
    letI : Fact (finrank ℝ (V) = (3 + 2) + 1) := ⟨finrank_euclideanSpace_fin⟩
    A.disconnectedBoundaryPairing l₀ r₀
        (ManifoldCapMap.dualityMap (E := V) 3 A.nativeBoundary 3 3 rfl b)
        (reductionHomologyMap 2 A.nativeBoundary 3 c) =
      SingularModTwoEvaluation.evaluation A.nativeBoundary 3 b c := by
  let := A.atlas
  let : ChartedSpace (V) A.nativeBoundary := A.boundaryAtlas
  let := A.nativeBoundaryCompactSpace
  let : Fact (finrank ℝ (V) = (3 + 2) + 1) := ⟨finrank_euclideanSpace_fin⟩
  let := A.nativeBoundary_secondHomology_subsingleton l₀ r₀
  exact ZeroSecondHomologyCap.pairing_cap_reduction (E := V) A.nativeBoundary b c

variable [SimplyConnectedSpace (slab d.map z s t)] (w₀ : slab d.map z s t)
  [hW₂ : Subsingleton (π_ 2 (slab d.map z s t) w₀)]

include w₀ hW₂ in
theorem disconnectedBoundaryKernel_selfOrthogonal (b : ModHomology 2 A.nativeBoundary 3) :
    (∀ c : ModHomology 2 A.nativeBoundary 3,
      modHomologyMap 2 (subtypeInclusion A.nativeBoundary) 3 c = 0 →
        A.disconnectedBoundaryPairing l₀ r₀ c b = 0) ↔
      modHomologyMap 2 (subtypeInclusion A.nativeBoundary) 3 b = 0 := by
  let := A.atlas
  let : ChartedSpace (V) A.nativeBoundary := A.boundaryAtlas
  let := A.nativeBoundaryCompactSpace
  let : Fact (finrank ℝ (V) = (3 + 2) + 1) := ⟨finrank_euclideanSpace_fin⟩
  let := A.nativeBoundary_secondHomology_subsingleton l₀ r₀
  let := TwoConnectedCoefficients.secondHomology_subsingleton w₀
  apply ZeroSecondHomologyCap.kernel_selfOrthogonal (E := V)
    (subtypeInclusion A.nativeBoundary)
  intro c
  exact A.nativeBoundaryCap_kernel 3 rfl 3 3 rfl c

include w₀ hW₂ in
theorem disconnectedBoundaryKernel_pairing_zero (b c : ModHomology 2 A.nativeBoundary 3)
    (hb : modHomologyMap 2 (subtypeInclusion A.nativeBoundary) 3 b = 0)
    (hc : modHomologyMap 2 (subtypeInclusion A.nativeBoundary) 3 c = 0) :
    A.disconnectedBoundaryPairing l₀ r₀ b c = 0 :=
  (A.disconnectedBoundaryKernel_selfOrthogonal l₀ r₀ w₀ c).mpr hc b hb

end NoExoticSixSphere.RegularCollaredCylinder.FramedSlabData
