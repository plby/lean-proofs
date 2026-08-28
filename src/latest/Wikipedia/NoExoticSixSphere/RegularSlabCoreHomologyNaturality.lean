import Wikipedia.NoExoticSixSphere.RegularSlabCoreHomology
import Wikipedia.NoExoticSixSphere.RegularSlabCoreNaturality
import Wikipedia.NoExoticSixSphere.SupportedRelativeHomology

/-!
# Support restriction preserves the original boundary-relative homology comparison

The two inclusion squares commute already on the actual relative chain
complexes. Thus transporting a class from an inner slab to the boundary
pair commutes with restricting its support to any smaller inner slab.
-/

noncomputable section

open Set CategoryTheory
open Wikipedia.HopfProblem.SingularMayerVietoris
open scoped Manifold ContDiff

namespace NoExoticSixSphere.RegularCollaredCylinder

open CylinderFiberSlab RelativeCoefficients

variable {B H M C H' N : Type}
  [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H]
  {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup C] [NormedSpace ℝ C] [TopologicalSpace H']
  {J : ModelWithCorners ℝ C H'} [TopologicalSpace N] [ChartedSpace H' N]
  {z : N} {s t : ℝ} (d : RegularCollaredCylinder (M := M) I J z s t)
  [CompactSpace M] [T2Space N]
  (a b : ℝ) (hsa : s < a) (hab : a ≤ b) (hbt : b < t)
  (hL : Icc s a ⊆ d.leftTimes) (hR : Icc b t ⊆ d.rightTimes)
  (a' b' : ℝ) (hsa' : s < a') (hab' : a' ≤ b') (hbt' : b' < t)
  (hL' : Icc s a' ⊆ d.leftTimes) (hR' : Icc b' t ⊆ d.rightTimes)
  (haa : a' ≤ a) (hbb : b ≤ b')

def collarModHomologyMap (p q : ℕ) :
    ModHomology p (BoundaryPush.domain d.map z s t a' b' : Set (slab d.map z s t)) q →ₗ[ℤ]
      ModHomology p (BoundaryPush.domain d.map z s t a b : Set (slab d.map z s t)) q :=
  modMap p (ContinuousMap.id (slab d.map z s t)) (d.collar_antitone a b a' b' haa hbb) q

omit [CompactSpace M] [T2Space N] in
theorem boundaryToCollarModEquiv_natural (p : ℕ) (hp : p ≠ 0) (q : ℕ)
    (c : ModHomology p (BoundaryPush.ends d.map z s t) q) :
    d.collarModHomologyMap a b a' b' haa hbb p q
        (d.boundaryToCollarModEquiv a' b' hsa' hab' hbt' hL' hR' p hp q c) =
      d.boundaryToCollarModEquiv a b hsa hab hbt hL hR p hp q c := by
  have h := mapChain_comp (ModuleCat.of ℤ (ZMod p))
    (ContinuousMap.id (slab d.map z s t))
    (BoundaryPush.ends_subset_domain d.map z s t a' b' hsa' hbt')
    (ContinuousMap.id (slab d.map z s t)) (d.collar_antitone a b a' b' haa hbb)
  simp only [ContinuousMap.id_comp] at h
  have he := congrArg (fun k ↦ homologyLinearMap k q) h
  simp only [homologyLinearMap_comp] at he
  exact (LinearMap.congr_fun he c).symm

theorem coreModHomologyEquiv_natural (p : ℕ) (hp : p ≠ 0) (q : ℕ)
    (c : ModHomology p
      (d.compactCore a' b' hsa' hbt' : Set (interiorDomain d.map z s t))ᶜ q) :
    d.collarModHomologyMap a b a' b' haa hbb p q
        (d.coreModHomologyEquiv a' b' hsa' hbt' p hp q c) =
      d.coreModHomologyEquiv a b hsa hbt p hp q
        (SupportedRelativeHomology.restrict (ModuleCat.of ℤ (ZMod p))
          (d.compactCore_mono a b hsa hbt a' b' hsa' hbt' haa hbb) q c) := by
  let hK := d.compactCore_mono a b hsa hbt a' b' hsa' hbt' haa hbb
  have h₁ := mapChain_comp (ModuleCat.of ℤ (ZMod p))
    (InteriorPush.inclusion d.map z s t) (d.coreComplement_mapsTo_collar a' b' hsa' hbt')
    (ContinuousMap.id (slab d.map z s t)) (d.collar_antitone a b a' b' haa hbb)
  have h₂ := mapChain_comp (ModuleCat.of ℤ (ZMod p))
    (ContinuousMap.id (interiorDomain d.map z s t))
    (show Set.MapsTo (ContinuousMap.id (interiorDomain d.map z s t))
      (d.compactCore a' b' hsa' hbt' : Set (interiorDomain d.map z s t))ᶜ
      (d.compactCore a b hsa hbt : Set (interiorDomain d.map z s t))ᶜ from
      fun _ hx hy ↦ hx (hK hy))
    (InteriorPush.inclusion d.map z s t) (d.coreComplement_mapsTo_collar a b hsa hbt)
  simp only [ContinuousMap.id_comp] at h₁
  simp only [ContinuousMap.comp_id] at h₂
  have he := congrArg (fun k ↦ homologyLinearMap k q) (h₁.symm.trans h₂)
  simp only [homologyLinearMap_comp] at he
  exact LinearMap.congr_fun he c

theorem coreToBoundaryModEquiv_natural (p : ℕ) (hp : p ≠ 0) (q : ℕ)
    (c : ModHomology p
      (d.compactCore a' b' hsa' hbt' : Set (interiorDomain d.map z s t))ᶜ q) :
    d.coreToBoundaryModEquiv a' b' hsa' hab' hbt' hL' hR' p hp q c =
      d.coreToBoundaryModEquiv a b hsa hab hbt hL hR p hp q
        (SupportedRelativeHomology.restrict (ModuleCat.of ℤ (ZMod p))
          (d.compactCore_mono a b hsa hbt a' b' hsa' hbt' haa hbb) q c) := by
  apply (d.boundaryToCollarModEquiv a b hsa hab hbt hL hR p hp q).injective
  rw [← d.boundaryToCollarModEquiv_natural a b hsa hab hbt hL hR
    a' b' hsa' hab' hbt' hL' hR' haa hbb p hp q]
  rw [d.coreToBoundaryModEquiv_collar, d.coreModHomologyEquiv_natural
    a b hsa hbt a' b' hsa' hbt' haa hbb p hp q]
  exact (d.coreToBoundaryModEquiv_collar a b hsa hab hbt hL hR p hp q _).symm

end NoExoticSixSphere.RegularCollaredCylinder
