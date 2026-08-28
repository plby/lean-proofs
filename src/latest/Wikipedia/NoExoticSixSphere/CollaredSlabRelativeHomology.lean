import Wikipedia.NoExoticSixSphere.CollaredSlabRelativeCohomology
import Wikipedia.NoExoticSixSphere.RelativeModExcision

/-!
# Homology comparison for the original boundary and its collar

The actual identity map of pairs is an integral quasi-isomorphism by the
constructed boundary retraction. The coefficient sequence transfers this
to the original finite-cyclic relative complexes, without a flatness
assumption on the coefficient module.
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

include hab hleft hright in
theorem boundaryPairMap_quasiIso : QuasiIso
    (RelativeSingularHomology.mapChain (ContinuousMap.id (slab F z s t))
      (ends_subset_domain F z s t a b hsa hbt)) := by
  apply RelativeSingularHomology.mapChain_quasiIso_of_absolute
  · intro q
    rw [singularHomologyMap_id]
    exact Function.bijective_id
  · intro q
    exact (homotopyEquivHomologyEquiv
      (homotopyEquiv F z s t a b hsa hab hbt hleft hright) q).bijective

include hab hleft hright in
theorem boundaryModPairMap_quasiIso (p : ℕ) (hp : p ≠ 0) : QuasiIso
    (RelativeCoefficients.mapChain (ModuleCat.of ℤ (ZMod p))
      (ContinuousMap.id (slab F z s t)) (ends_subset_domain F z s t a b hsa hbt)) :=
  RelativeCoefficients.mapChain_mod_quasiIso_of_integral p hp _ _
    (boundaryPairMap_quasiIso F z s t a b hsa hab hbt hleft hright)

def boundaryToCollarModHomologyEquiv (p : ℕ) (hp : p ≠ 0) (q : ℕ) :
    RelativeCoefficients.ModHomology p (ends F z s t) q ≃ₗ[ℤ]
      RelativeCoefficients.ModHomology p (domain F z s t a b : Set (slab F z s t)) q := by
  let := boundaryModPairMap_quasiIso F z s t a b hsa hab hbt hleft hright p hp
  exact (isoOfQuasiIsoAt (RelativeCoefficients.mapChain (ModuleCat.of ℤ (ZMod p))
    (ContinuousMap.id (slab F z s t)) (ends_subset_domain F z s t a b hsa hbt)) q).toLinearEquiv

theorem boundaryToCollarModHomologyEquiv_toLinearMap (p : ℕ) (hp : p ≠ 0) (q : ℕ) :
    (boundaryToCollarModHomologyEquiv F z s t a b hsa hab hbt hleft hright p hp q).toLinearMap =
      RelativeCoefficients.modMap p (ContinuousMap.id (slab F z s t))
        (ends_subset_domain F z s t a b hsa hbt) q := rfl

end NoExoticSixSphere.CylinderFiberSlab.BoundaryPush
