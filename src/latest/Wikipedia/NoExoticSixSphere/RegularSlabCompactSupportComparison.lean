import Wikipedia.NoExoticSixSphere.RegularSlabCoreNaturality
import Wikipedia.NoExoticSixSphere.CompactSupportCofinalComponent

/-!
# Boundary-relative cohomology equals actual interior compact-support cohomology

The original map from each collar-controlled compact core to the
compact-support direct limit is bijective: every support fits in a
larger such core and all core transitions are the proved isomorphisms.
The boundary comparison is independent of the chosen core by the
original transition formulas. No compact-support group is assigned an
expected value in place of its actual direct limit.
-/

noncomputable section

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace NoExoticSixSphere.RegularCollaredCylinder

open CylinderFiberSlab RelativeModTwoCochains

variable {B H M C H' N : Type}
  [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H]
  {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup C] [NormedSpace ℝ C] [TopologicalSpace H']
  {J : ModelWithCorners ℝ C H'} [TopologicalSpace N] [ChartedSpace H' N]
  {z : N} {s t : ℝ} (d : RegularCollaredCylinder (M := M) I J z s t)
  [CompactSpace M] [T2Space N]
  (a b : ℝ) (hsa : s < a) (hab : a ≤ b) (hbt : b < t)
  (hL : Icc s a ⊆ d.leftTimes) (hR : Icc b t ⊆ d.rightTimes)

include hab hL hR in
theorem compactCore_of_bijective (p : ℕ) : Function.Bijective
    (CompactSupportCohomology.of (interiorDomain d.map z s t) p (d.compactCore a b hsa hbt)) := by
  apply CompactSupportCohomology.of_bijective_of_cofinal
  intro K
  obtain ⟨c, e, hsc, het, hce, hLc, hRe, hK⟩ := d.compactCore_cofinal K
  let c' := min c a
  let e' := max e b
  have hsc' : s < c' := lt_min hsc hsa
  have he't : e' < t := max_lt het hbt
  have hce' : c' ≤ e' := (min_le_left _ _).trans (hce.trans (le_max_left _ _))
  have hLc' : Icc s c' ⊆ d.leftTimes :=
    (Icc_subset_Icc le_rfl (min_le_left _ _)).trans hLc
  have hRe' : Icc e' t ⊆ d.rightTimes :=
    (Icc_subset_Icc (le_max_left _ _) le_rfl).trans hRe
  let h₀ := d.compactCore_mono a b hsa hbt c' e' hsc' he't (min_le_right _ _) (le_max_right _ _)
  have hK' : K ≤ d.compactCore c' e' hsc' he't :=
    hK.trans (d.compactCore_mono c e hsc het c' e' hsc' he't
      (min_le_left _ _) (le_max_left _ _))
  refine ⟨d.compactCore c' e' hsc' he't, h₀, hK', ?_⟩
  exact d.compactCore_extend_bijective a b hsa hab hbt hL hR
    c' e' hsc' hce' he't hLc' hRe' (min_le_right _ _) (le_max_right _ _) p

def boundaryCompactSupportMap (p : ℕ) :
    Cohomology (BoundaryPush.ends d.map z s t) p →ₗ[ℤ]
      CompactSupportCohomology.Cohomology (interiorDomain d.map z s t) p :=
  (CompactSupportCohomology.of (interiorDomain d.map z s t) p
    (d.compactCore a b hsa hbt)).comp (d.boundaryCoreEquiv a b hsa hab hbt hL hR p).toLinearMap

theorem boundaryCompactSupportMap_bijective (p : ℕ) :
    Function.Bijective (d.boundaryCompactSupportMap a b hsa hab hbt hL hR p) :=
  (d.compactCore_of_bijective a b hsa hab hbt hL hR p).comp
    (d.boundaryCoreEquiv a b hsa hab hbt hL hR p).bijective

def boundaryCompactSupportEquiv (p : ℕ) :
    Cohomology (BoundaryPush.ends d.map z s t) p ≃ₗ[ℤ]
      CompactSupportCohomology.Cohomology (interiorDomain d.map z s t) p :=
  LinearEquiv.ofBijective (d.boundaryCompactSupportMap a b hsa hab hbt hL hR p)
    (d.boundaryCompactSupportMap_bijective a b hsa hab hbt hL hR p)

theorem boundaryCompactSupportEquiv_toLinearMap (p : ℕ) :
    (d.boundaryCompactSupportEquiv a b hsa hab hbt hL hR p).toLinearMap =
      d.boundaryCompactSupportMap a b hsa hab hbt hL hR p := rfl

variable (a' b' : ℝ) (hsa' : s < a') (hab' : a' ≤ b') (hbt' : b' < t)
  (hL' : Icc s a' ⊆ d.leftTimes) (hR' : Icc b' t ⊆ d.rightTimes)

theorem boundaryCompactSupportMap_mono (haa : a' ≤ a) (hbb : b ≤ b') (p : ℕ) :
    d.boundaryCompactSupportMap a' b' hsa' hab' hbt' hL' hR' p =
      d.boundaryCompactSupportMap a b hsa hab hbt hL hR p := by
  apply LinearMap.ext
  intro c
  change CompactSupportCohomology.of (interiorDomain d.map z s t) p
    (d.compactCore a' b' hsa' hbt') (d.boundaryCoreEquiv a' b' hsa' hab' hbt' hL' hR' p c) = _
  rw [d.boundaryCoreEquiv_natural a b hsa hab hbt hL hR
    a' b' hsa' hab' hbt' hL' hR' haa hbb p c]
  exact CompactSupportCohomology.of_transition (interiorDomain d.map z s t) p
    (d.compactCore_mono a b hsa hbt a' b' hsa' hbt' haa hbb) _

theorem boundaryCompactSupportMap_independent (p : ℕ) :
    d.boundaryCompactSupportMap a b hsa hab hbt hL hR p =
      d.boundaryCompactSupportMap a' b' hsa' hab' hbt' hL' hR' p := by
  let c := min a a'
  let e := max b b'
  have hsc : s < c := lt_min hsa hsa'
  have het : e < t := max_lt hbt hbt'
  have hce : c ≤ e := (min_le_left _ _).trans (hab.trans (le_max_left _ _))
  have hLc : Icc s c ⊆ d.leftTimes :=
    (Icc_subset_Icc le_rfl (min_le_left _ _)).trans hL
  have hRe : Icc e t ⊆ d.rightTimes :=
    (Icc_subset_Icc (le_max_left _ _) le_rfl).trans hR
  exact (d.boundaryCompactSupportMap_mono a b hsa hab hbt hL hR
    c e hsc hce het hLc hRe (min_le_left _ _) (le_max_left _ _) p).symm.trans
    (d.boundaryCompactSupportMap_mono a' b' hsa' hab' hbt' hL' hR'
      c e hsc hce het hLc hRe (min_le_right _ _) (le_max_right _ _) p)

def boundaryCompactSupportCanonical (p : ℕ) :
    Cohomology (BoundaryPush.ends d.map z s t) p ≃ₗ[ℤ]
      CompactSupportCohomology.Cohomology (interiorDomain d.map z s t) p :=
  let l := d.exists_inner_times.choose
  let u := d.exists_inner_times.choose_spec.choose
  let h := d.exists_inner_times.choose_spec.choose_spec
  d.boundaryCompactSupportEquiv l u h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2 p

end NoExoticSixSphere.RegularCollaredCylinder
