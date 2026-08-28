import Wikipedia.NoExoticSixSphere.RegularSlabCompactCores
import Wikipedia.NoExoticSixSphere.CollaredSlabRelativeCohomology
import Wikipedia.NoExoticSixSphere.SupportedModTwoCohomology

/-!
# Actual boundary-relative cohomology computed on each compact inner slab

The excised collar in the interior is exactly the complement of the
constructed compact core. The actual inclusion pullback is therefore
a cohomology equivalence. Composing with the proved boundary-collar
comparison identifies the original boundary-relative group with the
original supported cohomology at this actual core.
-/

noncomputable section

open Set Topology TopologicalSpace CategoryTheory
open scoped Manifold ContDiff

namespace NoExoticSixSphere.RegularCollaredCylinder

open CylinderFiberSlab

variable {B H M C H' N : Type}
  [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H]
  {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup C] [NormedSpace ℝ C] [TopologicalSpace H']
  {J : ModelWithCorners ℝ C H'} [TopologicalSpace N] [ChartedSpace H' N]
  {z : N} {s t : ℝ} (d : RegularCollaredCylinder (M := M) I J z s t)
  [CompactSpace M] [T2Space N]
  (a b : ℝ) (hsa : s < a) (hab : a ≤ b) (hbt : b < t)
  (hL : Icc s a ⊆ d.leftTimes) (hR : Icc b t ⊆ d.rightTimes)

theorem collarInInterior_eq_compl_core :
    RelativeSingularHomology.overlapIn (interiorDomain d.map z s t : Set (slab d.map z s t))
      (BoundaryPush.domain d.map z s t a b : Set (slab d.map z s t)) =
      (d.compactCore a b hsa hbt : Set (interiorDomain d.map z s t))ᶜ := by
  ext p
  change (d.interiorTime p < a ∨ b < d.interiorTime p) ↔ p ∉ d.compactCore a b hsa hbt
  rw [d.mem_compactCore_iff]
  simp only [mem_Icc, not_and_or, not_le]

theorem coreComplement_mapsTo_collar : Set.MapsTo
    (InteriorPush.inclusion d.map z s t)
    (d.compactCore a b hsa hbt : Set (interiorDomain d.map z s t))ᶜ
    (BoundaryPush.domain d.map z s t a b : Set (slab d.map z s t)) := by
  intro p hp
  change p ∈ RelativeSingularHomology.overlapIn
    (interiorDomain d.map z s t : Set (slab d.map z s t))
    (BoundaryPush.domain d.map z s t a b : Set (slab d.map z s t))
  rw [d.collarInInterior_eq_compl_core a b hsa hbt]
  exact hp

def corePullbackMap :
    RelativeModTwoCochains.complex (BoundaryPush.domain d.map z s t a b : Set (slab d.map z s t)) ⟶
      SupportedModTwoCohomology.complex
        (d.compactCore a b hsa hbt : Set (interiorDomain d.map z s t)) :=
  RelativeModTwoCochains.pullbackMap (InteriorPush.inclusion d.map z s t)
    (d.coreComplement_mapsTo_collar a b hsa hbt)

theorem corePullbackMap_quasiIso : QuasiIso (d.corePullbackMap a b hsa hbt) := by
  have h := RelativeModTwoCochains.excisionPullbackMap_quasiIso
    (interiorDomain d.map z s t : Set (slab d.map z s t))
    (BoundaryPush.domain d.map z s t a b : Set (slab d.map z s t))
    (interiorDomain d.map z s t).isOpen (BoundaryPush.domain d.map z s t a b).isOpen
    (BoundaryPush.interior_collar_cover d.map z s t a b hsa hbt)
  unfold RelativeModTwoCochains.excisionPullbackMap at h
  have transport (V : Set (interiorDomain d.map z s t))
      (he : RelativeSingularHomology.overlapIn
        (interiorDomain d.map z s t : Set (slab d.map z s t))
        (BoundaryPush.domain d.map z s t a b : Set (slab d.map z s t)) = V)
      (hf : Set.MapsTo (InteriorPush.inclusion d.map z s t) V
        (BoundaryPush.domain d.map z s t a b : Set (slab d.map z s t))) :
      QuasiIso (RelativeModTwoCochains.pullbackMap (InteriorPush.inclusion d.map z s t) hf) := by
    subst V
    exact h
  exact transport _ (d.collarInInterior_eq_compl_core a b hsa hbt)
    (d.coreComplement_mapsTo_collar a b hsa hbt)

def coreExcisionEquiv (p : ℕ) :
    RelativeModTwoCochains.Cohomology
      (BoundaryPush.domain d.map z s t a b : Set (slab d.map z s t)) p ≃ₗ[ℤ]
      SupportedModTwoCohomology.Cohomology
        (d.compactCore a b hsa hbt : Set (interiorDomain d.map z s t)) p := by
  let := d.corePullbackMap_quasiIso a b hsa hbt
  exact (isoOfQuasiIsoAt (d.corePullbackMap a b hsa hbt) p).toLinearEquiv

theorem coreExcisionEquiv_toLinearMap (p : ℕ) :
    (d.coreExcisionEquiv a b hsa hbt p).toLinearMap =
      RelativeModTwoCochains.cohomologyPullback (InteriorPush.inclusion d.map z s t)
        (d.coreComplement_mapsTo_collar a b hsa hbt) p := rfl

def collarToBoundaryEquiv (p : ℕ) :
    RelativeModTwoCochains.Cohomology
      (BoundaryPush.domain d.map z s t a b : Set (slab d.map z s t)) p ≃ₗ[ℤ]
      RelativeModTwoCochains.Cohomology (BoundaryPush.ends d.map z s t) p :=
  BoundaryPush.collarRelativeEquiv d.map z s t a b hsa hab hbt
    (fun r hr x ↦ (d.left_eq r (hL hr) x).trans (d.left_eq s d.left_mem x).symm)
    (fun r hr x ↦ (d.right_eq r (hR hr) x).trans (d.right_eq t d.right_mem x).symm) p

omit [CompactSpace M] [T2Space N] in
theorem collarToBoundaryEquiv_toLinearMap (p : ℕ) :
    (d.collarToBoundaryEquiv a b hsa hab hbt hL hR p).toLinearMap =
      RelativeModTwoCochains.cohomologyPullback (ContinuousMap.id (slab d.map z s t))
        (BoundaryPush.ends_subset_domain d.map z s t a b hsa hbt) p := rfl

def boundaryCoreEquiv (p : ℕ) :
    RelativeModTwoCochains.Cohomology (BoundaryPush.ends d.map z s t) p ≃ₗ[ℤ]
      SupportedModTwoCohomology.Cohomology
        (d.compactCore a b hsa hbt : Set (interiorDomain d.map z s t)) p :=
  (d.collarToBoundaryEquiv a b hsa hab hbt hL hR p).symm.trans
    (d.coreExcisionEquiv a b hsa hbt p)

theorem boundaryCoreEquiv_collar (p : ℕ)
    (c : RelativeModTwoCochains.Cohomology
      (BoundaryPush.domain d.map z s t a b : Set (slab d.map z s t)) p) :
    d.boundaryCoreEquiv a b hsa hab hbt hL hR p
      (d.collarToBoundaryEquiv a b hsa hab hbt hL hR p c) =
        d.coreExcisionEquiv a b hsa hbt p c := by
  change d.coreExcisionEquiv a b hsa hbt p
    ((d.collarToBoundaryEquiv a b hsa hab hbt hL hR p).symm
      (d.collarToBoundaryEquiv a b hsa hab hbt hL hR p c)) = _
  rw [LinearEquiv.symm_apply_apply]

end NoExoticSixSphere.RegularCollaredCylinder
