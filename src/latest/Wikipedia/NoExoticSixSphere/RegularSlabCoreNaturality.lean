import Wikipedia.NoExoticSixSphere.RegularSlabCoreCohomology
import Wikipedia.NoExoticSixSphere.RelativeModTwoPullbackFunctor

/-!
# Growing the actual compact cores preserves the boundary comparison

The original pair-pullback squares show that the core equivalences
commute with actual extension of support. Consequently every nested
pair of collar-controlled cores has a bijective support transition.
-/

noncomputable section

open Set
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
  (a' b' : ℝ) (hsa' : s < a') (hab' : a' ≤ b') (hbt' : b' < t)
  (hL' : Icc s a' ⊆ d.leftTimes) (hR' : Icc b' t ⊆ d.rightTimes)
  (haa : a' ≤ a) (hbb : b ≤ b')

include haa hbb in
omit [CompactSpace M] [T2Space N] in
theorem collar_antitone :
    (BoundaryPush.domain d.map z s t a' b' : Set (slab d.map z s t)) ⊆
      BoundaryPush.domain d.map z s t a b := by
  intro p hp
  rcases hp with hl | hr
  · exact Or.inl (hl.trans_le haa)
  · exact Or.inr (hbb.trans_lt hr)

include haa hbb in
theorem compactCore_mono :
    d.compactCore a b hsa hbt ≤ d.compactCore a' b' hsa' hbt' := by
  intro p hp
  apply (d.mem_compactCore_iff a' b' hsa' hbt' p).mpr
  have h := (d.mem_compactCore_iff a b hsa hbt p).mp hp
  exact ⟨haa.trans h.1, h.2.trans hbb⟩

def collarRestriction (p : ℕ) :
    Cohomology (BoundaryPush.domain d.map z s t a b : Set (slab d.map z s t)) p →ₗ[ℤ]
      Cohomology (BoundaryPush.domain d.map z s t a' b' : Set (slab d.map z s t)) p :=
  cohomologyPullback (ContinuousMap.id (slab d.map z s t))
    (d.collar_antitone a b a' b' haa hbb) p

omit [CompactSpace M] [T2Space N] in
theorem collarToBoundaryEquiv_natural (p : ℕ)
    (c : Cohomology (BoundaryPush.domain d.map z s t a b : Set (slab d.map z s t)) p) :
    d.collarToBoundaryEquiv a' b' hsa' hab' hbt' hL' hR' p
      (d.collarRestriction a b a' b' haa hbb p c) =
        d.collarToBoundaryEquiv a b hsa hab hbt hL hR p c := by
  have h := cohomologyPullback_comp (ContinuousMap.id (slab d.map z s t))
    (BoundaryPush.ends_subset_domain d.map z s t a' b' hsa' hbt')
    (ContinuousMap.id (slab d.map z s t)) (d.collar_antitone a b a' b' haa hbb) p
  simp only [ContinuousMap.id_comp] at h
  exact (LinearMap.congr_fun h c).symm

theorem coreExcisionEquiv_natural (p : ℕ)
    (c : Cohomology (BoundaryPush.domain d.map z s t a b : Set (slab d.map z s t)) p) :
    d.coreExcisionEquiv a' b' hsa' hbt' p (d.collarRestriction a b a' b' haa hbb p c) =
      SupportedModTwoCohomology.extend
        (d.compactCore_mono a b hsa hbt a' b' hsa' hbt' haa hbb) p
        (d.coreExcisionEquiv a b hsa hbt p c) := by
  let hK := d.compactCore_mono a b hsa hbt a' b' hsa' hbt' haa hbb
  have h₁ := cohomologyPullback_comp (InteriorPush.inclusion d.map z s t)
    (d.coreComplement_mapsTo_collar a' b' hsa' hbt')
    (ContinuousMap.id (slab d.map z s t)) (d.collar_antitone a b a' b' haa hbb) p
  have h₂ := cohomologyPullback_comp (ContinuousMap.id (interiorDomain d.map z s t))
    (show Set.MapsTo (ContinuousMap.id (interiorDomain d.map z s t))
      (d.compactCore a' b' hsa' hbt' : Set (interiorDomain d.map z s t))ᶜ
      (d.compactCore a b hsa hbt : Set (interiorDomain d.map z s t))ᶜ from
      fun _ hx hy ↦ hx (hK hy))
    (InteriorPush.inclusion d.map z s t) (d.coreComplement_mapsTo_collar a b hsa hbt) p
  simp only [ContinuousMap.id_comp] at h₁
  simp only [ContinuousMap.comp_id] at h₂
  exact LinearMap.congr_fun (h₁.symm.trans h₂) c

theorem boundaryCoreEquiv_natural (p : ℕ) (c : Cohomology (BoundaryPush.ends d.map z s t) p) :
    d.boundaryCoreEquiv a' b' hsa' hab' hbt' hL' hR' p c =
      SupportedModTwoCohomology.extend
        (d.compactCore_mono a b hsa hbt a' b' hsa' hbt' haa hbb) p
        (d.boundaryCoreEquiv a b hsa hab hbt hL hR p c) := by
  obtain ⟨v, rfl⟩ := (d.collarToBoundaryEquiv a b hsa hab hbt hL hR p).surjective c
  calc
    d.boundaryCoreEquiv a' b' hsa' hab' hbt' hL' hR' p
        (d.collarToBoundaryEquiv a b hsa hab hbt hL hR p v) =
        d.boundaryCoreEquiv a' b' hsa' hab' hbt' hL' hR' p
          (d.collarToBoundaryEquiv a' b' hsa' hab' hbt' hL' hR' p
            (d.collarRestriction a b a' b' haa hbb p v)) :=
      congrArg (d.boundaryCoreEquiv a' b' hsa' hab' hbt' hL' hR' p)
        (d.collarToBoundaryEquiv_natural a b hsa hab hbt hL hR
          a' b' hsa' hab' hbt' hL' hR' haa hbb p v).symm
    _ = d.coreExcisionEquiv a' b' hsa' hbt' p
        (d.collarRestriction a b a' b' haa hbb p v) :=
      d.boundaryCoreEquiv_collar a' b' hsa' hab' hbt' hL' hR' p _
    _ = SupportedModTwoCohomology.extend
        (d.compactCore_mono a b hsa hbt a' b' hsa' hbt' haa hbb) p
        (d.coreExcisionEquiv a b hsa hbt p v) :=
      d.coreExcisionEquiv_natural a b hsa hbt a' b' hsa' hbt' haa hbb p v
    _ = _ := congrArg (SupportedModTwoCohomology.extend
      (d.compactCore_mono a b hsa hbt a' b' hsa' hbt' haa hbb) p)
      (d.boundaryCoreEquiv_collar a b hsa hab hbt hL hR p v).symm

include hab hL hR hab' hL' hR' in
theorem compactCore_extend_bijective (p : ℕ) :
    Function.Bijective (SupportedModTwoCohomology.extend
      (d.compactCore_mono a b hsa hbt a' b' hsa' hbt' haa hbb) p) := by
  let E := d.boundaryCoreEquiv a b hsa hab hbt hL hR p
  let G := d.boundaryCoreEquiv a' b' hsa' hab' hbt' hL' hR' p
  let f := SupportedModTwoCohomology.extend
    (d.compactCore_mono a b hsa hbt a' b' hsa' hbt' haa hbb) p
  have he : f.comp E.toLinearMap = G.toLinearMap := by
    apply LinearMap.ext
    intro c
    exact (d.boundaryCoreEquiv_natural a b hsa hab hbt hL hR
      a' b' hsa' hab' hbt' hL' hR' haa hbb p c).symm
  have hb : Function.Bijective (f.comp E.toLinearMap) := by
    rw [he]
    exact G.bijective
  exact (Function.Bijective.of_comp_iff f E.bijective).mp hb

end NoExoticSixSphere.RegularCollaredCylinder
