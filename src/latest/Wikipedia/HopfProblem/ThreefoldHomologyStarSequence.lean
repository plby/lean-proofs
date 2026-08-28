import Wikipedia.HopfProblem.ThreefoldHomologyStarComparison
import Wikipedia.HopfProblem.ThreefoldHomologyGluingAlgebra

/-!
# The actual one-shot Mayer–Vietoris sequence of the threefold

The genuine cover consists of the full regular patch and the disjoint
union of all three full filling patches.  The following exact sequence
has the actual global singular homology as its ambient term, the product
of the original overlap homologies on the left, and the original regular
family and filling homologies in the middle.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology

open SingularMayerVietoris

local notation "U" => (liftedPatch none : Set Space)
local notation "V" => (starFillings : Set Space)

/-- The actual singular connecting map before the disjoint-union coordinates. -/
def rawStarConnectingHomomorphism (n : ℕ) :
    SingularHomology Space (n + 1) →ₗ[ℤ] SingularHomology starOverlap n :=
  connectingHomomorphism U V (liftedPatch none).isOpen starFillings.isOpen star_cover n

/-- The genuine connecting homomorphism, with each of the three original
full overlap homology groups retained as its own component. -/
def starConnectingHomomorphism (n : ℕ) :
    SingularHomology Space (n + 1) →ₗ[ℤ] StarOverlapHomology n :=
  (starOverlapHomologyEquiv n).toLinearMap.comp (rawStarConnectingHomomorphism n)

@[simp] theorem starConnectingHomomorphism_apply (n : ℕ)
    (a : SingularHomology Space (n + 1)) :
    starConnectingHomomorphism n a =
      starOverlapHomologyEquiv n (rawStarConnectingHomomorphism n a) := rfl

/-- Exactness at the product of the genuine regular and filling homologies. -/
theorem star_exact_at_pair (n : ℕ) :
    Function.Exact (starLeftHomologyMap n) (starRightHomologyMap n) := by
  have hraw : Function.Exact (leftHomologyMap U V n) (rightHomologyMap U V n) :=
    LinearMap.exact_iff.mpr
      (exact_at_pair U V (liftedPatch none).isOpen starFillings.isOpen star_cover n).symm
  apply exact_of_linearEquiv_squares _ _ _ _ (starOverlapHomologyEquiv n)
    (starPairHomologyEquiv n) (LinearEquiv.refl ℤ _)
    (starLeftHomologyMap_comparison n) _ hraw
  simpa only [LinearEquiv.refl_toLinearMap, LinearMap.id_comp] using
    starRightHomologyMap_comparison n

/-- Exactness at the three actual full overlap homology groups. -/
theorem star_exact_at_intersection (n : ℕ) :
    Function.Exact (starConnectingHomomorphism n) (starLeftHomologyMap n) := by
  have hraw : Function.Exact (rawStarConnectingHomomorphism n)
      (leftHomologyMap U V n) :=
    LinearMap.exact_iff.mpr
      (exact_at_intersection U V (liftedPatch none).isOpen
        starFillings.isOpen star_cover n).symm
  apply exact_of_linearEquiv_squares _ _ _ _ (LinearEquiv.refl ℤ _)
    (starOverlapHomologyEquiv n) (starPairHomologyEquiv n)
    _ (starLeftHomologyMap_comparison n) hraw
  simp only [LinearEquiv.refl_toLinearMap, LinearMap.comp_id,
    starConnectingHomomorphism]

/-- Exactness at each positive-degree homology group of the constructed threefold. -/
theorem star_exact_at_ambient (n : ℕ) :
    Function.Exact (starRightHomologyMap (n + 1)) (starConnectingHomomorphism n) := by
  have hraw : Function.Exact (rightHomologyMap U V (n + 1))
      (rawStarConnectingHomomorphism n) :=
    LinearMap.exact_iff.mpr
      (exact_at_ambient U V (liftedPatch none).isOpen starFillings.isOpen star_cover n).symm
  apply exact_of_linearEquiv_squares _ _ _ _ (starPairHomologyEquiv (n + 1))
    (LinearEquiv.refl ℤ _) (starOverlapHomologyEquiv n) _ _ hraw
  · simpa only [LinearEquiv.refl_toLinearMap, LinearMap.id_comp] using
      starRightHomologyMap_comparison (n + 1)
  · simp only [LinearEquiv.refl_toLinearMap, LinearMap.comp_id,
      starConnectingHomomorphism]

/-- The actual degree-zero endpoint of the star sequence is onto. -/
theorem starRightHomologyMap_zero_surjective : Function.Surjective (starRightHomologyMap 0) := by
  apply surjective_of_linearEquiv_square (rightHomologyMap U V 0) _
    (starPairHomologyEquiv 0) (LinearEquiv.refl ℤ _)
  · simpa only [LinearEquiv.refl_toLinearMap, LinearMap.id_comp] using
      starRightHomologyMap_comparison 0
  · exact rightHomologyMap_zero_surjective U V (liftedPatch none).isOpen
      starFillings.isOpen star_cover

/-- All three exactness statements for the actual star cover, in every degree. -/
theorem star_mayerVietoris_exact (n : ℕ) :
    Function.Exact (starConnectingHomomorphism n) (starLeftHomologyMap n) ∧
      Function.Exact (starLeftHomologyMap n) (starRightHomologyMap n) ∧
      Function.Exact (starRightHomologyMap (n + 1)) (starConnectingHomomorphism n) :=
  ⟨star_exact_at_intersection n, star_exact_at_pair n, star_exact_at_ambient n⟩

theorem starConnectingHomomorphism_comp_left (n : ℕ) :
    (starLeftHomologyMap n).comp (starConnectingHomomorphism n) = 0 := by
  apply LinearMap.ext
  intro a
  exact (star_exact_at_intersection n).apply_apply_eq_zero a

theorem starRightHomologyMap_comp_connecting (n : ℕ) :
    (starConnectingHomomorphism n).comp (starRightHomologyMap (n + 1)) = 0 := by
  apply LinearMap.ext
  intro a
  exact (star_exact_at_ambient n).apply_apply_eq_zero a

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology
