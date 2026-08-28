import Wikipedia.NoExoticSixSphere.CollaredSlabBoundaryRetraction
import Wikipedia.NoExoticSixSphere.SlabInterior
import Wikipedia.NoExoticSixSphere.RelativeModTwoHomologyComparison
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleHomotopy

/-!
# Relative cohomology of the actual boundary and collar

The identity map from the boundary pair to the collar pair induces an
isomorphism on relative cohomology, by the constructed collar retraction.
Excision then identifies it with the actual interior pair. All maps are
the original pair pullbacks, not merely abstract isomorphisms of groups.
-/

noncomputable section

open Set CategoryTheory
open Wikipedia.HopfProblem SingularMayerVietoris PeriodTorusHigherHomology

namespace NoExoticSixSphere.CylinderFiberSlab.BoundaryPush

variable {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
  (F : C(ℝ × M, N)) (z : N) (s t a b : ℝ)
  (hsa : s < a) (hab : a ≤ b) (hbt : b < t)
  (hleft : ∀ r ∈ Icc s a, ∀ x, F (r, x) = F (s, x))
  (hright : ∀ r ∈ Icc b t, ∀ x, F (r, x) = F (t, x))

def boundaryPullbackMap : RelativeModTwoCochains.complex (domain F z s t a b : Set (slab F z s t)) ⟶
    RelativeModTwoCochains.complex (ends F z s t) :=
  RelativeModTwoCochains.pullbackMap (ContinuousMap.id (slab F z s t))
    (ends_subset_domain F z s t a b hsa hbt)

include hab hleft hright in
theorem boundaryPullbackMap_quasiIso :
    QuasiIso (boundaryPullbackMap F z s t a b hsa hbt) := by
  apply RelativeModTwoCochains.pullbackMap_quasiIso_of_absolute
  · intro q
    rw [singularHomologyMap_id]
    exact Function.bijective_id
  · intro q
    exact (homotopyEquivHomologyEquiv
      (homotopyEquiv F z s t a b hsa hab hbt hleft hright) q).bijective

def collarRelativeEquiv (p : ℕ) :
    RelativeModTwoCochains.Cohomology (domain F z s t a b : Set (slab F z s t)) p ≃ₗ[ℤ]
      RelativeModTwoCochains.Cohomology (ends F z s t) p := by
  let := boundaryPullbackMap_quasiIso F z s t a b hsa hab hbt hleft hright
  exact (isoOfQuasiIsoAt (boundaryPullbackMap F z s t a b hsa hbt) p).toLinearEquiv

theorem collarRelativeEquiv_toLinearMap (p : ℕ) :
    (collarRelativeEquiv F z s t a b hsa hab hbt hleft hright p).toLinearMap =
      RelativeModTwoCochains.cohomologyPullback (ContinuousMap.id (slab F z s t))
        (ends_subset_domain F z s t a b hsa hbt) p := rfl

include hsa hbt in
theorem interior_collar_cover :
    (interiorDomain F z s t : Set (slab F z s t)) ∪
      (domain F z s t a b : Set (slab F z s t)) = univ := by
  apply eq_univ_of_forall
  intro p
  rcases eq_endpoints_or_mem_Ioo_of_mem_Icc p.property with hs | ht | hi
  · exact Or.inr (Or.inl (hs.trans_lt hsa))
  · exact Or.inr (Or.inr (hbt.trans_eq ht.symm))
  · exact Or.inl hi

def interiorExcisionEquiv (p : ℕ) :
    RelativeModTwoCochains.Cohomology (domain F z s t a b : Set (slab F z s t)) p ≃ₗ[ℤ]
      RelativeModTwoCochains.Cohomology (RelativeSingularHomology.overlapIn
        (interiorDomain F z s t : Set (slab F z s t))
        (domain F z s t a b : Set (slab F z s t))) p :=
  RelativeModTwoCochains.excisionEquiv (interiorDomain F z s t : Set (slab F z s t))
    (domain F z s t a b : Set (slab F z s t)) (interiorDomain F z s t).isOpen
    (domain F z s t a b).isOpen
    (interior_collar_cover F z s t a b hsa hbt) p

def boundaryToInteriorRelativeEquiv (p : ℕ) :
    RelativeModTwoCochains.Cohomology (ends F z s t) p ≃ₗ[ℤ]
      RelativeModTwoCochains.Cohomology (RelativeSingularHomology.overlapIn
        (interiorDomain F z s t : Set (slab F z s t))
        (domain F z s t a b : Set (slab F z s t))) p :=
  (collarRelativeEquiv F z s t a b hsa hab hbt hleft hright p).symm.trans
    (interiorExcisionEquiv F z s t a b hsa hbt p)

theorem boundaryToInteriorRelativeEquiv_collar (p : ℕ)
    (c : RelativeModTwoCochains.Cohomology (domain F z s t a b : Set (slab F z s t)) p) :
    boundaryToInteriorRelativeEquiv F z s t a b hsa hab hbt hleft hright p
      (collarRelativeEquiv F z s t a b hsa hab hbt hleft hright p c) =
        interiorExcisionEquiv F z s t a b hsa hbt p c := by
  change interiorExcisionEquiv F z s t a b hsa hbt p
    ((collarRelativeEquiv F z s t a b hsa hab hbt hleft hright p).symm
      (collarRelativeEquiv F z s t a b hsa hab hbt hleft hright p c)) = _
  rw [LinearEquiv.symm_apply_apply]

end NoExoticSixSphere.CylinderFiberSlab.BoundaryPush
