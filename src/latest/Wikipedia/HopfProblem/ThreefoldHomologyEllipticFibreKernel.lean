import Wikipedia.HopfProblem.ThreefoldHomologyEllipticFibre
import Wikipedia.HopfProblem.ThreefoldHomologyEllipticFibreKernelConjugacy

/-!
# The actual elliptic cap map and Wang boundary jointly detect classes

The fibre map into the original small cap has exactly the kernel of the
actual Wang fibre inclusion.  This follows from the proved central
finite-cover kernel and its genuine real-period conjugacy.  Exactness of
the native Wang sequence then says that a boundary class killed both by
the cap inclusion and the Wang boundary is zero.  The same statement is
transported back to the literal overlap in the original threefold.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.EllipticFibre

open SingularMayerVietoris PeriodTorusHigherHomology MappingTorusHomology
open Wikipedia.HopfProblem.Elliptic
open ThreefoldOverlapMappingTorus Elliptic.HigherHomology EllipticFilling

/-- The actual fibre-to-cap kernel is exactly the image of the actual
forward Wang difference, with no supplied matrix or kernel hypothesis. -/
theorem fibreToFilling_ker_eq_wangDifference_range (j : Elliptic.Kind) (n : ℕ) :
    LinearMap.ker (singularHomologyMap (fibreToFilling (some j)) n) =
      LinearMap.range (wangDifference (monodromy (some j)) n) := by
  ext a
  change singularHomologyMap (fibreToFilling (some j)) n a = 0 ↔ _
  rw [fibreToFilling_homology_eq_zero_iff]
  change centralPeriodHomologyEquiv j n a ∈ LinearMap.ker
    (singularHomologyMap
      (periodCover j (specialLocalData j).centralPeriod j.twist
        (Elliptic.mainTwist_admissible j)) n) ↔ _
  rw [periodCover_ker_eq_deckDifference_range]
  exact periodHomologyEquiv_mem_deckDifference_range_iff
    j (specialLocalData j).centralPeriod n a

/-- A real fibre class dies in the actual cap exactly when it already
dies under the genuine mapping-torus fibre inclusion. -/
theorem fibreToFilling_eq_zero_iff_fibreHomologyMap_eq_zero (j : Elliptic.Kind) (n : ℕ)
    (a : SingularHomology RealTorus₄ n) :
    singularHomologyMap (fibreToFilling (some j)) n a = 0 ↔
      fibreHomologyMap (monodromy (some j)) n a = 0 := by
  change a ∈ LinearMap.ker (singularHomologyMap (fibreToFilling (some j)) n) ↔
    a ∈ LinearMap.ker (fibreHomologyMap (monodromy (some j)) n)
  rw [fibreToFilling_ker_eq_wangDifference_range, wang_exact_at_fibre]

/-- The actual cap map and actual Wang boundary detect every positive-degree
class of the original elliptic boundary mapping torus. -/
theorem boundaryFilling_wang_eq_zero (j : Elliptic.Kind) (n : ℕ)
    (a : SingularHomology (Boundary (some j)) (n + 1))
    (hcap : boundaryFillingHomologyMap (some j) (n + 1) a = 0)
    (hwang : wangBoundary (monodromy (some j)) n a = 0) : a = 0 := by
  have ha : a ∈ LinearMap.range (fibreHomologyMap (monodromy (some j)) (n + 1)) := by
    rw [wang_exact_at_mappingTorus]
    exact hwang
  obtain ⟨b, rfl⟩ := ha
  have hf := LinearMap.congr_fun (boundaryFillingHomologyMap_fibre (some j) (n + 1)) b
  change boundaryFillingHomologyMap (some j) (n + 1)
    (fibreHomologyMap (monodromy (some j)) (n + 1) b) =
      singularHomologyMap (fibreToFilling (some j)) (n + 1) b at hf
  exact (fibreToFilling_eq_zero_iff_fibreHomologyMap_eq_zero j (n + 1) b).mp
    (hf.symm.trans hcap)

/-- Joint injectivity retains the two literal native homology maps. -/
theorem boundaryFilling_wang_injective (j : Elliptic.Kind) (n : ℕ) :
    Function.Injective (fun a : SingularHomology (Boundary (some j)) (n + 1) =>
      (boundaryFillingHomologyMap (some j) (n + 1) a,
        wangBoundary (monodromy (some j)) n a)) := by
  intro a b h
  have hc : boundaryFillingHomologyMap (some j) (n + 1) a =
      boundaryFillingHomologyMap (some j) (n + 1) b := congrArg Prod.fst h
  have hw : wangBoundary (monodromy (some j)) n a =
      wangBoundary (monodromy (some j)) n b := congrArg Prod.snd h
  apply sub_eq_zero.mp
  apply boundaryFilling_wang_eq_zero j n
  · rw [map_sub, hc, sub_self]
  · rw [map_sub, hw, sub_self]

/-- The degree-four joint detection used by the original attachment sequence. -/
theorem boundaryFilling_four_wang_three_injective (j : Elliptic.Kind) :
    Function.Injective (fun a : SingularHomology (Boundary (some j)) 4 =>
      (boundaryFillingHomologyMap (some j) 4 a,
        wangBoundary (monodromy (some j)) 3 a)) :=
  boundaryFilling_wang_injective j 3

/-- Joint detection on the literal original intersection, using its actual
inclusion into the cap and its actual deformation to the boundary model. -/
theorem overlapFilling_wang_eq_zero (j : Elliptic.Kind) (n : ℕ)
    (a : SingularHomology (RegularOverlap (some j)) (n + 1))
    (hcap : singularHomologyMap (overlapToFilling (some j)) (n + 1) a = 0)
    (hwang : wangBoundary (monodromy (some j)) n
      (overlapHomologyEquiv (some j) (n + 1) a) = 0) : a = 0 := by
  apply (overlapHomologyEquiv (some j) (n + 1)).injective
  rw [map_zero]
  apply boundaryFilling_wang_eq_zero j n
  · have hf := LinearMap.congr_fun
      (boundaryFillingHomologyMap_retraction (some j) (n + 1)) a
    change boundaryFillingHomologyMap (some j) (n + 1)
        (overlapHomologyEquiv (some j) (n + 1) a) =
      singularHomologyMap (overlapToFilling (some j)) (n + 1) a at hf
    exact hf.trans hcap
  · exact hwang

/-- The literal original cap inclusion and transported actual Wang map
are jointly injective on every positive-degree overlap homology group. -/
theorem overlapFilling_wang_injective (j : Elliptic.Kind) (n : ℕ) :
    Function.Injective (fun a : SingularHomology (RegularOverlap (some j)) (n + 1) =>
      (singularHomologyMap (overlapToFilling (some j)) (n + 1) a,
        wangBoundary (monodromy (some j)) n
          (overlapHomologyEquiv (some j) (n + 1) a))) := by
  intro a b h
  have hc : singularHomologyMap (overlapToFilling (some j)) (n + 1) a =
      singularHomologyMap (overlapToFilling (some j)) (n + 1) b := congrArg Prod.fst h
  have hw : wangBoundary (monodromy (some j)) n
      (overlapHomologyEquiv (some j) (n + 1) a) =
        wangBoundary (monodromy (some j)) n
          (overlapHomologyEquiv (some j) (n + 1) b) := congrArg Prod.snd h
  apply sub_eq_zero.mp
  apply overlapFilling_wang_eq_zero j n
  · rw [map_sub, hc, sub_self]
  · rw [map_sub, map_sub, hw, sub_self]

/-- In particular the actual fourth-degree elliptic overlap class is detected. -/
theorem overlapFilling_four_wang_three_injective (j : Elliptic.Kind) :
    Function.Injective (fun a : SingularHomology (RegularOverlap (some j)) 4 =>
      (singularHomologyMap (overlapToFilling (some j)) 4 a,
        wangBoundary (monodromy (some j)) 3
          (overlapHomologyEquiv (some j) 4 a))) :=
  overlapFilling_wang_injective j 3

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.EllipticFibre
