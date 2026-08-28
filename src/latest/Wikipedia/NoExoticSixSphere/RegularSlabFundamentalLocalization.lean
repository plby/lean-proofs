import Wikipedia.NoExoticSixSphere.RegularSlabRelativeFundamentalClass

/-!
# Localization of the slab's relative fundamental class

At every actual interior point, the original identity map from the
boundary pair to the punctured-point pair sends the relative class to
the original nonzero interior local class, followed by the genuine
open-neighborhood inclusion. This is a statement about the original
maps of pairs, not a normalization imposed on a replacement group.
-/

noncomputable section

open Set Module CategoryTheory
open scoped Manifold ContDiff
open Wikipedia.HopfProblem SingularMayerVietoris

namespace NoExoticSixSphere.CylinderFiberSlab.BoundaryPush

variable {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
  (F : C(ℝ × M, N)) (z : N) (s t : ℝ)

theorem ends_avoid_interior (x : interiorDomain F z s t) :
    Set.MapsTo (ContinuousMap.id (slab F z s t)) (ends F z s t)
      ({x.val}ᶜ : Set (slab F z s t)) := by
  intro y hy
  change y ≠ x.val
  intro he
  subst y
  change x.val.val.val.1 = s ∨ x.val.val.val.1 = t at hy
  have hx : s < x.val.val.val.1 ∧ x.val.val.val.1 < t := x.property
  exact hy.elim (ne_of_gt hx.1) (ne_of_lt hx.2)

end NoExoticSixSphere.CylinderFiberSlab.BoundaryPush

namespace NoExoticSixSphere.RegularCollaredCylinder

open CylinderFiberSlab
open ModTwoCapProduct (Coefficient)

variable {B H M C H' N : Type}
  [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
  [TopologicalSpace H] {I : ModelWithCorners ℝ B H} [I.Boundaryless]
  [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M]
  [NormedAddCommGroup C] [NormedSpace ℝ C] [FiniteDimensional ℝ C]
  [TopologicalSpace H'] {J : ModelWithCorners ℝ C H'} [J.Boundaryless]
  [TopologicalSpace N] [T2Space N] [ChartedSpace H' N] [IsManifold J ∞ N]
  {z : N} {s t : ℝ} (d : RegularCollaredCylinder (M := M) I J z s t)
  (n : ℕ) (hd : finrank ℝ (ℝ × B) = finrank ℝ C + (n + 3))

def interiorLocalClass (x : interiorDomain d.map z s t) :
    RelativeCoefficients.ModHomology 2 ({x}ᶜ : Set (interiorDomain d.map z s t)) (n + 3) :=
  letI := d.interiorEuclideanAtlas n hd
  letI : Fact (finrank ℝ (EuclideanSpace ℝ (Fin (n + 3))) = (n + 2) + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  ModTwoLocalClass.manifoldClass (E := EuclideanSpace ℝ (Fin (n + 3))) n x

omit [CompactSpace M] [T2Space N] in
theorem interiorLocalClass_ne_zero (x : interiorDomain d.map z s t) :
    d.interiorLocalClass n hd x ≠ 0 := by
  let := d.interiorEuclideanAtlas n hd
  let : Fact (finrank ℝ (EuclideanSpace ℝ (Fin (n + 3))) = (n + 2) + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  exact ModTwoLocalClass.manifoldClass_ne_zero (E := EuclideanSpace ℝ (Fin (n + 3))) n x

variable (a b : ℝ) (hsa : s < a) (hab : a ≤ b) (hbt : b < t)
  (hL : Icc s a ⊆ d.leftTimes) (hR : Icc b t ⊆ d.rightTimes)

theorem coreFundamentalClass_evaluate (x : interiorDomain d.map z s t)
    (hx : x ∈ d.compactCore a b hsa hbt) :
    SupportedRelativeHomology.evaluate Coefficient
        (d.compactCore a b hsa hbt : Set (interiorDomain d.map z s t)) x hx (n + 3)
        (d.coreFundamentalClass n hd a b hsa hbt) = d.interiorLocalClass n hd x := by
  let := d.interiorEuclideanAtlas n hd
  let : Fact (finrank ℝ (EuclideanSpace ℝ (Fin (n + 3))) = (n + 2) + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  exact CompactSupportedFundamentalClass.isFundamentalOn
    (E := EuclideanSpace ℝ (Fin (n + 3))) n
    (d.compactCore a b hsa hbt : Set (interiorDomain d.map z s t))
    (d.compactCore a b hsa hbt).isCompact x hx

include hab hL hR in
theorem relativeFundamentalClass_local_onCore (x : interiorDomain d.map z s t)
    (hx : x ∈ d.compactCore a b hsa hbt) :
    RelativeCoefficients.modMap 2 (ContinuousMap.id (slab d.map z s t))
        (BoundaryPush.ends_avoid_interior d.map z s t x) (n + 3)
        (d.relativeFundamentalClass n hd) =
      RelativeCoefficients.modNeighborhoodMap 2
        (interiorDomain d.map z s t : Set (slab d.map z s t)) x (n + 3)
        (d.interiorLocalClass n hd x) := by
  have hV : Set.MapsTo (ContinuousMap.id (slab d.map z s t))
      (BoundaryPush.domain d.map z s t a b : Set (slab d.map z s t))
      ({x.val}ᶜ : Set (slab d.map z s t)) := by
    intro y hy
    change y ≠ x.val
    intro he
    subst y
    have hx' : x ∈ RelativeSingularHomology.overlapIn
        (interiorDomain d.map z s t : Set (slab d.map z s t))
        (BoundaryPush.domain d.map z s t a b : Set (slab d.map z s t)) := hy
    rw [d.collarInInterior_eq_compl_core a b hsa hbt] at hx'
    exact hx' hx
  let hK : Set.MapsTo (ContinuousMap.id (interiorDomain d.map z s t))
      (d.compactCore a b hsa hbt : Set (interiorDomain d.map z s t))ᶜ
      ({x}ᶜ : Set (interiorDomain d.map z s t)) := by
    intro y hy he
    have hxy : y = x := Set.mem_singleton_iff.mp he
    exact hy (hxy.symm ▸ hx)
  have h₁ := RelativeCoefficients.mapChain_comp Coefficient
    (ContinuousMap.id (slab d.map z s t))
    (BoundaryPush.ends_subset_domain d.map z s t a b hsa hbt)
    (ContinuousMap.id (slab d.map z s t)) hV
  simp only [ContinuousMap.id_comp] at h₁
  have he₁ := congrArg (fun k ↦ homologyLinearMap k (n + 3)) h₁
  simp only [homologyLinearMap_comp] at he₁
  have h₂ := RelativeCoefficients.mapChain_comp Coefficient
    (InteriorPush.inclusion d.map z s t) (d.coreComplement_mapsTo_collar a b hsa hbt)
    (ContinuousMap.id (slab d.map z s t)) hV
  have h₃ := RelativeCoefficients.mapChain_comp Coefficient
    (ContinuousMap.id (interiorDomain d.map z s t)) hK
    (subtypeInclusion (interiorDomain d.map z s t : Set (slab d.map z s t)))
    (RelativeSingularHomology.inclusion_mapsTo_puncture
      (interiorDomain d.map z s t : Set (slab d.map z s t)) x)
  simp only [ContinuousMap.id_comp] at h₂
  simp only [ContinuousMap.comp_id] at h₃
  have he₂ := congrArg (fun k ↦ homologyLinearMap k (n + 3)) (h₂.symm.trans h₃)
  simp only [homologyLinearMap_comp] at he₂
  have hF : d.boundaryToCollarModEquiv a b hsa hab hbt hL hR 2 (by decide) (n + 3)
      (d.relativeFundamentalClass n hd) =
        d.coreModHomologyEquiv a b hsa hbt 2 (by decide) (n + 3)
          (d.coreFundamentalClass n hd a b hsa hbt) := by
    rw [d.relativeFundamentalClass_eq_onCore n hd a b hsa hab hbt hL hR]
    exact d.relativeFundamentalClassOnCore_collar n hd a b hsa hab hbt hL hR
  apply (LinearMap.congr_fun he₁ (d.relativeFundamentalClass n hd)).trans
  apply (congrArg (RelativeCoefficients.modMap 2 (ContinuousMap.id (slab d.map z s t))
    hV (n + 3)) hF).trans
  apply (LinearMap.congr_fun he₂ (d.coreFundamentalClass n hd a b hsa hbt)).trans
  exact congrArg (RelativeCoefficients.modNeighborhoodMap 2
    (interiorDomain d.map z s t : Set (slab d.map z s t)) x (n + 3))
    (d.coreFundamentalClass_evaluate n hd a b hsa hbt x hx)

theorem relativeFundamentalClass_local (x : interiorDomain d.map z s t) :
    RelativeCoefficients.modMap 2 (ContinuousMap.id (slab d.map z s t))
        (BoundaryPush.ends_avoid_interior d.map z s t x) (n + 3)
        (d.relativeFundamentalClass n hd) =
      RelativeCoefficients.modNeighborhoodMap 2
        (interiorDomain d.map z s t : Set (slab d.map z s t)) x (n + 3)
        (d.interiorLocalClass n hd x) := by
  let K : TopologicalSpace.Compacts (interiorDomain d.map z s t) :=
    ⟨{x}, isCompact_singleton⟩
  obtain ⟨a, b, hsa, hbt, hab, hL, hR, hK⟩ := d.compactCore_cofinal K
  exact d.relativeFundamentalClass_local_onCore n hd a b hsa hab hbt hL hR x
    (hK (Set.mem_singleton x))

theorem relativeFundamentalClass_local_ne_zero (x : interiorDomain d.map z s t) :
    RelativeCoefficients.modMap 2 (ContinuousMap.id (slab d.map z s t))
        (BoundaryPush.ends_avoid_interior d.map z s t x) (n + 3)
        (d.relativeFundamentalClass n hd) ≠ 0 := by
  rw [d.relativeFundamentalClass_local]
  intro hz
  apply d.interiorLocalClass_ne_zero n hd x
  apply (RelativeCoefficients.modNeighborhoodEquiv 2 (by decide)
    (interiorDomain d.map z s t : Set (slab d.map z s t))
    (interiorDomain d.map z s t).isOpen x (n + 3)).injective
  exact hz.trans (map_zero _).symm

end NoExoticSixSphere.RegularCollaredCylinder
