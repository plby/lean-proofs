import Wikipedia.NoExoticSixSphere.TimeCollarCoreCohomology

/-!
# Actual core transitions retain the boundary-relative comparison

The original pair-pullback squares commute with restriction of the collar
and extension of support. Thus enlarging the actual compact core gives a
bijective support transition, with no choice of abstract replacement maps.
-/

noncomputable section

open Set Function ContinuousMap

namespace NoExoticSixSphere.TimeCollarDuality

open Wikipedia.HopfProblem.DegreeCollapse Wikipedia.HopfProblem.DegreeCollapse.TimeCollar
open RelativeModTwoCochains

variable {M B : Type} [TopologicalSpace M] [TopologicalSpace B]
  {t : M → ℝ} (C : TimeCollar t B) [CompactSpace M]
  (δ : ℝ) (hδ : 0 < δ) (hδw : δ ≤ C.width)
  (ε : ℝ) (hε : 0 < ε) (hεw : ε ≤ C.width) (hεδ : ε ≤ δ)

include hεδ in
theorem collar_antitone : (collarRegion C ε : Set (NonnegativeHalf t)) ⊆ collarRegion C δ :=
  fun _ hp ↦ hp.trans_le hεδ

def collarRestriction (p : ℕ) :
    Cohomology (collarRegion C δ : Set (NonnegativeHalf t)) p →ₗ[ℤ]
      Cohomology (collarRegion C ε : Set (NonnegativeHalf t)) p :=
  cohomologyPullback (ContinuousMap.id (NonnegativeHalf t)) (collar_antitone C δ ε hεδ) p

theorem collarRelativeEquiv_natural (p : ℕ)
    (c : Cohomology (collarRegion C δ : Set (NonnegativeHalf t)) p) :
    collarRelativeEquiv C ε hε hεw p (collarRestriction C δ ε hεδ p c) =
      collarRelativeEquiv C δ hδ hδw p c := by
  have h := cohomologyPullback_comp (ContinuousMap.id (NonnegativeHalf t))
    (boundary_subset_collar C ε hε) (ContinuousMap.id (NonnegativeHalf t))
    (collar_antitone C δ ε hεδ) p
  simp only [ContinuousMap.id_comp] at h
  exact (LinearMap.congr_fun h c).symm

theorem coreExcisionEquiv_natural (p : ℕ)
    (c : Cohomology (collarRegion C δ : Set (NonnegativeHalf t)) p) :
    coreExcisionEquiv C ε hε p (collarRestriction C δ ε hεδ p c) =
      SupportedModTwoCohomology.extend (compactCore_mono C δ ε hδ hε hεδ) p
        (coreExcisionEquiv C δ hδ p c) := by
  let hK := compactCore_mono C δ ε hδ hε hεδ
  have h₁ := cohomologyPullback_comp C.interiorToHalf (coreComplement_mapsTo_collar C ε hε)
    (ContinuousMap.id (NonnegativeHalf t)) (collar_antitone C δ ε hεδ) p
  have h₂ := cohomologyPullback_comp (ContinuousMap.id C.positiveInterior)
    (show MapsTo (ContinuousMap.id C.positiveInterior)
      (compactCore C ε hε : Set C.positiveInterior)ᶜ
      (compactCore C δ hδ : Set C.positiveInterior)ᶜ from fun _ hx hy ↦ hx (hK hy))
    C.interiorToHalf (coreComplement_mapsTo_collar C δ hδ) p
  simp only [ContinuousMap.id_comp] at h₁
  simp only [ContinuousMap.comp_id] at h₂
  calc
    coreExcisionEquiv C ε hε p (collarRestriction C δ ε hεδ p c) =
        cohomologyPullback C.interiorToHalf (coreComplement_mapsTo_collar C ε hε) p
          (collarRestriction C δ ε hεδ p c) :=
      LinearMap.congr_fun (coreExcisionEquiv_toLinearMap C ε hε p) _
    _ = SupportedModTwoCohomology.extend hK p
        (cohomologyPullback C.interiorToHalf (coreComplement_mapsTo_collar C δ hδ) p c) :=
      LinearMap.congr_fun (h₁.symm.trans h₂) c
    _ = SupportedModTwoCohomology.extend hK p (coreExcisionEquiv C δ hδ p c) :=
      congrArg (SupportedModTwoCohomology.extend hK p)
        (LinearMap.congr_fun (coreExcisionEquiv_toLinearMap C δ hδ p) c).symm

theorem boundaryCoreEquiv_natural (p : ℕ) (c : Cohomology (boundary t) p) :
    boundaryCoreEquiv C ε hε hεw p c =
      SupportedModTwoCohomology.extend (compactCore_mono C δ ε hδ hε hεδ) p
        (boundaryCoreEquiv C δ hδ hδw p c) := by
  obtain ⟨v, rfl⟩ := (collarRelativeEquiv C δ hδ hδw p).surjective c
  calc
    boundaryCoreEquiv C ε hε hεw p (collarRelativeEquiv C δ hδ hδw p v) =
        boundaryCoreEquiv C ε hε hεw p
          (collarRelativeEquiv C ε hε hεw p (collarRestriction C δ ε hεδ p v)) :=
      congrArg (boundaryCoreEquiv C ε hε hεw p)
        (collarRelativeEquiv_natural C δ hδ hδw ε hε hεw hεδ p v).symm
    _ = coreExcisionEquiv C ε hε p (collarRestriction C δ ε hεδ p v) :=
      boundaryCoreEquiv_collar C ε hε hεw p _
    _ = SupportedModTwoCohomology.extend (compactCore_mono C δ ε hδ hε hεδ) p
        (coreExcisionEquiv C δ hδ p v) :=
      coreExcisionEquiv_natural C δ hδ ε hε hεδ p v
    _ = _ := congrArg (SupportedModTwoCohomology.extend (compactCore_mono C δ ε hδ hε hεδ) p)
      (boundaryCoreEquiv_collar C δ hδ hδw p v).symm

include hδw hεw in
theorem compactCore_extend_bijective (p : ℕ) :
    Bijective (SupportedModTwoCohomology.extend (compactCore_mono C δ ε hδ hε hεδ) p) := by
  let E := boundaryCoreEquiv C δ hδ hδw p
  let G := boundaryCoreEquiv C ε hε hεw p
  let f := SupportedModTwoCohomology.extend (compactCore_mono C δ ε hδ hε hεδ) p
  have he : f.comp E.toLinearMap = G.toLinearMap := by
    apply LinearMap.ext
    intro c
    exact (boundaryCoreEquiv_natural C δ hδ hδw ε hε hεw hεδ p c).symm
  have hb : Bijective (f.comp E.toLinearMap) := by
    rw [he]
    exact G.bijective
  exact (Function.Bijective.of_comp_iff f E.bijective).mp hb

end NoExoticSixSphere.TimeCollarDuality
