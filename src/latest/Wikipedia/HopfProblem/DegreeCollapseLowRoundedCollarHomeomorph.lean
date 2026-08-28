import Wikipedia.HopfProblem.DegreeCollapseLowRoundedCylinderCoordinates

/-!

# A genuine open collar piece of the rounded attachment

The actual relatively open collar subset is homeomorphic to the regular
superlevel domain in the original sphere–transverse–height coordinates.
The homeomorphism retains the ambient sheet map exactly. All points added
by rounding lie in this open piece.
-/

noncomputable section

open Function Set Metric Topology TopologicalSpace
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.RoundedTrace

open NoExoticSixSphere GLOrthonormalization Stiefel

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel}
  {f : NoExoticSixSphere.Sphere d → M}
  (A : FramedAttachingProduct e a f)

def collarParameters : Set ((NoExoticSixSphere.Sphere d × Vector (7 - d)) × ℝ) :=
  {p | p.1.2 ∈ ball (0 : Vector (7 - d)) A.radius ∧
    p.2 ∈ Ioo (-collarHeight A) (collarHeight A) ∧
    0 ≤ GeneralRoundedHandleCorner.level (bump A) (UnroundedTrace.handleRadius A) (p.1.2, p.2)}

theorem collarParameters_subset_source : collarParameters A ⊆ A.tubeHeightCoordinates.source :=
  fun p hp ↦ (A.mem_tubeHeightCoordinates_source p).mpr hp.1

theorem collarParameter_time (p : collarParameters A) : ‖p.val.2‖ ≤ collarHeight A := by
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨p.property.2.1.1.le, p.property.2.1.2.le⟩

theorem collarParameter_mem (p : collarParameters A) : A.collarSheet p.val ∈ ambientSet A :=
  (sheet_mem_iff A p.val.1.1 p.property.1 (collarParameter_time A p)).mpr p.property.2.2

def collarMap : C(collarParameters A, ambientSet A) :=
  ⟨fun p ↦ ⟨A.collarSheet p.val, collarParameter_mem A p⟩,
    (A.contMDiffOn_collarSheet.continuousOn.mono
      (collarParameters_subset_source A)).domRestrict.subtype_mk _⟩

theorem isEmbedding_collarMap : IsEmbedding (collarMap A) := by
  have he := A.isEmbedding_collarSheet.comp
    (IsEmbedding.inclusion (collarParameters_subset_source A))
  exact he.codRestrict (ambientSet A) (collarParameter_mem A)

theorem collarMap_mem_part (p : collarParameters A) : collarMap A p ∈ collarPart A := by
  have hi : collarMap A p ∈ cylinderPart A :=
    sheet_band_avoids_inner A p.val.1.1 p.property.1 (collarParameter_time A p)
  apply (mem_collarPart_iff A _).mpr
  refine ⟨hi, ?_⟩
  have hc : cylinderCoordinates A ⟨collarMap A p, hi⟩ = (A.tube p.val.1, p.val.2) :=
    cylinderCoordinates_of_eq A _ _ rfl
  rw [hc]
  exact ⟨A.tubeCoordinates.map_source ⟨mem_univ _, p.property.1⟩, p.property.2.1⟩

theorem range_collarMap : range (collarMap A) = (collarPart A : Set (ambientSet A)) := by
  ext y
  constructor
  · rintro ⟨p, rfl⟩
    exact collarMap_mem_part A p
  · intro hy
    obtain ⟨hi, hz⟩ := (mem_collarPart_iff A y).mp hy
    let z := cylinderCoordinates A ⟨y, hi⟩
    have hz' : z.1 ∈ A.tubeCoordinates.target ∧
        z.2 ∈ Ioo (-collarHeight A) (collarHeight A) := hz
    let q : (NoExoticSixSphere.Sphere d × Vector (7 - d)) × ℝ := (A.tubeCoordinates.symm z.1, z.2)
    have hqs := A.tubeCoordinates.map_target hz'.1
    have hv : q.1.2 ∈ ball (0 : Vector (7 - d)) A.radius := hqs.2
    have hr : A.tube (A.tubeCoordinates.symm z.1) = z.1 :=
      A.tubeCoordinates.right_inv hz'.1
    have he : A.collarSheet q = y.val := by
      change LowHeightCylinder.heightCylinder d e
        (A.tube (A.tubeCoordinates.symm z.1), z.2) = y.val
      rw [hr]
      exact cylinderCoordinates_ambient A ⟨y, hi⟩
    have ht : ‖q.2‖ ≤ collarHeight A := by
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨hz'.2.1.le, hz'.2.2.le⟩
    have hmem : A.collarSheet q ∈ ambientSet A := he.symm ▸ y.property
    have hL := (sheet_mem_iff A q.1.1 hv ht).mp hmem
    exact ⟨⟨q, hv, hz'.2, hL⟩, Subtype.ext he⟩

def collarHomeomorph : collarParameters A ≃ₜ collarPart A :=
  (isEmbedding_collarMap A).toHomeomorph.trans (Homeomorph.setCongr (range_collarMap A))

theorem collarHomeomorph_ambient (p : collarParameters A) :
    (collarHomeomorph A p).val.val = A.collarSheet p.val := rfl

theorem collarHomeomorph_symm_ambient (p : collarPart A) :
    A.collarSheet ((collarHomeomorph A).symm p).val = p.val.val := by
  have h := collarHomeomorph_ambient A ((collarHomeomorph A).symm p)
  rw [(collarHomeomorph A).apply_symm_apply] at h
  exact h.symm

theorem addedImage_mem_part (y : ambientSet A)
    (hy : y.val ∈ A.collarSheet '' addedParameters A) : y ∈ collarPart A := by
  obtain ⟨p, hp, he⟩ := hy
  have hv : p.1.2 ∈ ball (0 : Vector (7 - d)) A.radius :=
    (closedBall_subset_ball (outerRadius_lt A)) hp.1
  have ht : p.2 ∈ Ioo (-collarHeight A) (collarHeight A) := by
    constructor
    · linarith [hp.2.1.1, twice_outer_lt_height A]
    · linarith [hp.2.1.2, collarHeight_pos A]
  change y ∈ (collarPart A : Set (ambientSet A))
  rw [← range_collarMap A]
  exact ⟨⟨p, hv, ht, hp.2.2⟩, Subtype.ext he⟩

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.RoundedTrace
