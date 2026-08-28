import Wikipedia.NoExoticSixSphere.CollaredSlabRelativeHomology
import Wikipedia.NoExoticSixSphere.RegularSlabCoreCohomology

/-!
# Actual relative homology computed on an inner slab

The maps are the original inclusion from the interior pair and the
original identity from the boundary pair to the collar pair. Their
homology equivalences allow transport of genuine supported fundamental
classes to the original boundary-relative group.
-/

noncomputable section

open Set CategoryTheory
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

def coreModPairMap (p : ℕ) :
    RelativeCoefficients.complex (ModuleCat.of ℤ (ZMod p))
        (d.compactCore a b hsa hbt : Set (interiorDomain d.map z s t))ᶜ ⟶
      RelativeCoefficients.complex (ModuleCat.of ℤ (ZMod p))
        (BoundaryPush.domain d.map z s t a b : Set (slab d.map z s t)) :=
  RelativeCoefficients.mapChain (ModuleCat.of ℤ (ZMod p))
    (InteriorPush.inclusion d.map z s t) (d.coreComplement_mapsTo_collar a b hsa hbt)

theorem coreModPairMap_quasiIso (p : ℕ) (hp : p ≠ 0) :
    QuasiIso (d.coreModPairMap a b hsa hbt p) := by
  have h := RelativeCoefficients.modExcisionChainMap_quasiIso p hp
    (interiorDomain d.map z s t : Set (slab d.map z s t))
    (BoundaryPush.domain d.map z s t a b : Set (slab d.map z s t))
    (interiorDomain d.map z s t).isOpen (BoundaryPush.domain d.map z s t a b).isOpen
    (BoundaryPush.interior_collar_cover d.map z s t a b hsa hbt)
  unfold RelativeCoefficients.modExcisionChainMap at h
  have transport (V : Set (interiorDomain d.map z s t))
      (he : RelativeSingularHomology.overlapIn
        (interiorDomain d.map z s t : Set (slab d.map z s t))
        (BoundaryPush.domain d.map z s t a b : Set (slab d.map z s t)) = V)
      (hf : Set.MapsTo (InteriorPush.inclusion d.map z s t) V
        (BoundaryPush.domain d.map z s t a b : Set (slab d.map z s t))) :
      QuasiIso (RelativeCoefficients.mapChain (ModuleCat.of ℤ (ZMod p))
        (InteriorPush.inclusion d.map z s t) hf) := by
    subst V
    exact h
  exact transport _ (d.collarInInterior_eq_compl_core a b hsa hbt)
    (d.coreComplement_mapsTo_collar a b hsa hbt)

def coreModHomologyEquiv (p : ℕ) (hp : p ≠ 0) (q : ℕ) :
    RelativeCoefficients.ModHomology p
        (d.compactCore a b hsa hbt : Set (interiorDomain d.map z s t))ᶜ q ≃ₗ[ℤ]
      RelativeCoefficients.ModHomology p
        (BoundaryPush.domain d.map z s t a b : Set (slab d.map z s t)) q := by
  let := d.coreModPairMap_quasiIso a b hsa hbt p hp
  exact (isoOfQuasiIsoAt (d.coreModPairMap a b hsa hbt p) q).toLinearEquiv

theorem coreModHomologyEquiv_toLinearMap (p : ℕ) (hp : p ≠ 0) (q : ℕ) :
    (d.coreModHomologyEquiv a b hsa hbt p hp q).toLinearMap =
      RelativeCoefficients.modMap p (InteriorPush.inclusion d.map z s t)
        (d.coreComplement_mapsTo_collar a b hsa hbt) q := rfl

def boundaryToCollarModEquiv (p : ℕ) (hp : p ≠ 0) (q : ℕ) :
    RelativeCoefficients.ModHomology p (BoundaryPush.ends d.map z s t) q ≃ₗ[ℤ]
      RelativeCoefficients.ModHomology p
        (BoundaryPush.domain d.map z s t a b : Set (slab d.map z s t)) q :=
  BoundaryPush.boundaryToCollarModHomologyEquiv d.map z s t a b hsa hab hbt
    (fun r hr x ↦ (d.left_eq r (hL hr) x).trans (d.left_eq s d.left_mem x).symm)
    (fun r hr x ↦ (d.right_eq r (hR hr) x).trans (d.right_eq t d.right_mem x).symm) p hp q

omit [CompactSpace M] [T2Space N] in
theorem boundaryToCollarModEquiv_toLinearMap (p : ℕ) (hp : p ≠ 0) (q : ℕ) :
    (d.boundaryToCollarModEquiv a b hsa hab hbt hL hR p hp q).toLinearMap =
      RelativeCoefficients.modMap p (ContinuousMap.id (slab d.map z s t))
        (BoundaryPush.ends_subset_domain d.map z s t a b hsa hbt) q := rfl

def coreToBoundaryModEquiv (p : ℕ) (hp : p ≠ 0) (q : ℕ) :
    RelativeCoefficients.ModHomology p
        (d.compactCore a b hsa hbt : Set (interiorDomain d.map z s t))ᶜ q ≃ₗ[ℤ]
      RelativeCoefficients.ModHomology p (BoundaryPush.ends d.map z s t) q :=
  (d.coreModHomologyEquiv a b hsa hbt p hp q).trans
    (d.boundaryToCollarModEquiv a b hsa hab hbt hL hR p hp q).symm

theorem coreToBoundaryModEquiv_collar (p : ℕ) (hp : p ≠ 0) (q : ℕ)
    (c : RelativeCoefficients.ModHomology p
      (d.compactCore a b hsa hbt : Set (interiorDomain d.map z s t))ᶜ q) :
    d.boundaryToCollarModEquiv a b hsa hab hbt hL hR p hp q
        (d.coreToBoundaryModEquiv a b hsa hab hbt hL hR p hp q c) =
      d.coreModHomologyEquiv a b hsa hbt p hp q c := by
  exact LinearEquiv.apply_symm_apply _ _

end NoExoticSixSphere.RegularCollaredCylinder
