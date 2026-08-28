import Wikipedia.NoExoticSixSphere.RelativeBoundaryLocalNonvanishing
import Wikipedia.NoExoticSixSphere.TimeCollarConnectingCap
import Wikipedia.NoExoticSixSphere.TimeCollarFundamentalLocalization
import Wikipedia.NoExoticSixSphere.TimeCollarBoundaryLocalHomology

/-!
# The collared half's connecting class is the genuine boundary class

Nonzero interior localization, density, and vanishing of local homology at
boundary points give nonzero local values of the connecting class. Local
mod-two uniqueness identifies it with the fundamental class of the supplied
six-dimensional boundary atlas. No boundary connectedness is assumed.
-/

noncomputable section

open Set Function ContinuousMap
open scoped Manifold ContDiff

namespace NoExoticSixSphere.TimeCollarDuality

open GLOrthonormalization
open Wikipedia.HopfProblem.DegreeCollapse Wikipedia.HopfProblem.DegreeCollapse.TimeCollar
open Wikipedia.HopfProblem.SphereHomologyCoefficients
open Wikipedia.HopfProblem.SingularMayerVietoris
open ModTwoCapProduct (Coefficient)

variable {M B : Type} [TopologicalSpace M] [TopologicalSpace B]
  {t : M → ℝ} (C : TimeCollar t B)

theorem not_mem_boundary_iff_interior (p : NonnegativeHalf t) :
    p ∉ boundary t ↔ p ∈ interiorDomain C :=
  ⟨fun hp ↦ lt_of_le_of_ne p.property (Ne.symm hp), fun hp ↦ ne_of_gt hp⟩

include C in
theorem isClosed_boundary : IsClosed (boundary t) :=
  isClosed_eq (C.continuous_time.comp continuous_subtype_val) continuous_const

include C in
theorem boundaryCompactSpace [CompactSpace M] : CompactSpace (boundary t) := by
  let : CompactSpace (NonnegativeHalf t) :=
    (isClosed_le continuous_const C.continuous_time).isClosedEmbedding_subtypeVal.compactSpace
  exact (isClosed_boundary C).isClosedEmbedding_subtypeVal.compactSpace

variable [ChartedSpace (Vector 7) M] [IsManifold (𝓡 7) ∞ M] [T2Space M] [CompactSpace M]

theorem boundaryConnectingClass_local_ne_zero (x : boundary t) :
    homologyLinearMap (RelativeCoefficients.projection Coefficient
        ({x}ᶜ : Set (boundary t))) 6 (boundaryConnectingClass C) ≠ 0 := by
  apply RelativeCoefficients.connecting_localize_ne_zero Coefficient
    (boundary t) 6 (relativeFundamentalClass C) x
  · exact boundaryLocalModHomology_subsingleton C x 2 (by decide) 7
  · intro O hO hxO
    obtain ⟨y, hyO, hy⟩ := exists_interior_mem_open C O hO x.val hxO
    exact ⟨y, hyO, (not_mem_boundary_iff_interior C y).mpr hy⟩
  · intro y hy
    exact relativeFundamentalClass_local_ne_zero C
      ⟨y.val, (not_mem_boundary_iff_interior C y).mp hy⟩

variable [ChartedSpace (Vector 6) (boundary t)] [CompactSpace (boundary t)]

local instance : Fact (Module.finrank ℝ (Vector 6) = (3 + 2) + 1) := ⟨by simp⟩

theorem boundaryConnectingClass_eq_fundamentalClass :
    boundaryConnectingClass C =
      ManifoldFundamentalClass.fundamentalClass (E := Vector 6) 3 (boundary t) := by
  apply ManifoldFundamentalClass.fundamentalClass_unique (E := Vector 6) 3
  intro x
  apply ModTwoLocalClass.eq_manifoldClass_of_ne_zero (E := Vector 6) 3 x
  exact boundaryConnectingClass_local_ne_zero C x

theorem boundaryDualityMap_connecting_fundamental (p q : ℕ) (h : p + q = 6)
    (a : ModTwoCapProduct.Cohomology (boundary t) p) :
    boundaryDualityMap C (p + 1) q (by omega)
        (RelativeModTwoCochains.connecting (boundary t) p a) =
      modHomologyMap 2 (subtypeInclusion (boundary t)) q
        (ModTwoCapProduct.capProductInDegree (boundary t) h a
          (ManifoldFundamentalClass.fundamentalClass (E := Vector 6) 3 (boundary t))) := by
  rw [← boundaryConnectingClass_eq_fundamentalClass C]
  exact boundaryDualityMap_connecting C p q h a

include C in
theorem boundaryCap_kernel (p q : ℕ) (h : p + q = 6)
    (a : ModTwoCapProduct.Cohomology (boundary t) p) :
    modHomologyMap 2 (subtypeInclusion (boundary t)) q
        (ModTwoCapProduct.capProductInDegree (boundary t) h a
          (ManifoldFundamentalClass.fundamentalClass (E := Vector 6) 3 (boundary t))) = 0 ↔
      ∃ b : ModTwoCapProduct.Cohomology (NonnegativeHalf t) p,
        ModTwoCapProduct.cohomologyPullback (subtypeInclusion (boundary t)) p b = a := by
  rw [← boundaryConnectingClass_eq_fundamentalClass C]
  exact boundaryConnectingCap_kernel C p q h a

end NoExoticSixSphere.TimeCollarDuality
