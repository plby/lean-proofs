import StackExchange.Puzzling139335.CentralRotation.CoordinateCutPairs
import StackExchange.Puzzling139335.CentralRotation.LocalReversal
import StackExchange.Puzzling139335.CentralRotation.FirstOverlap.CurveOpen
import StackExchange.Puzzling139335.CentralRotation.GapIdentity

/-!
# Locating the cut images on the actual outer arcs

The reversed-lift rigidity theorem excludes overlap of the cut with its
inverse image under a direct non-half-turn congruence.  Relative openness
of Jordan subarcs then excludes endpoint contacts with the open cut and
places both image arcs on the corresponding outer arcs.
-/

open Set Schoenflies

namespace Puzzling139335.CentralRotation

theorem symm_not_halfTurn (g : Plane ≃ᵃⁱ[ℝ] Plane)
    (hnot : ∀ z, g ≠ AffineIsometryEquiv.pointReflection ℝ z) :
    ∀ z, g.symm ≠ AffineIsometryEquiv.pointReflection ℝ z := by
  intro z hz
  apply hnot z
  simpa only [AffineIsometryEquiv.symm_symm, AffineIsometryEquiv.pointReflection_symm] using
    congrArg (fun e : Plane ≃ᵃⁱ[ℝ] Plane => e.symm) hz

namespace BoundaryLifts

variable {M Γ N : Set Plane} {d : BoundaryCoordinates M Γ N}
variable {g h : Plane ≃ᵃⁱ[ℝ] Plane} (L : BoundaryLifts d g h)

include L

/-- The initial two image arcs really lie on the outer boundary arcs; this
conclusion is not part of the coordinate or lift definitions. -/
theorem cut_images_subset_outer (a : Circle) (b : ℂ)
    (hg : ∀ x, PlaneIsometries.complexEquiv (g x) =
      (a : ℂ) * PlaneIsometries.complexEquiv x + b)
    (hnot : ∀ z, g ≠ AffineIsometryEquiv.pointReflection ℝ z) :
    g.symm '' Γ ⊆ M ∧ g '' Γ ⊆ N := by
  let p := circleParam d.leftParam (1 / 2)
  let q := circleParam d.leftParam 1
  have hIleft : g.symm '' Γ ⊆ range d.leftParam := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨t, ht, rfl⟩ := d.leftCutImage.symm.subset hx
    rw [L.inverse_cut_agrees ht]
    exact mem_range_self (L.G.symm (1 - t) : AddCircle (1 : ℝ))
  have hJright : g '' Γ ⊆ range d.rightParam := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨t, ht, rfl⟩ := d.leftCutImage.symm.subset hx
    rw [← L.left_to_right]
    exact mem_range_self (L.G t : AddCircle (1 : ℝ))
  have hinvform (x : Plane) : PlaneIsometries.complexEquiv (g.symm x) =
      ((a⁻¹ : Circle) : ℂ) * PlaneIsometries.complexEquiv x - (a : ℂ)⁻¹ * b := by
    simpa only [Circle.coe_inv] using RotationAlgebra.direct_form_symm g a b hg x
  have hlocal := disjoint_of_decreasing_lift_of_not_halfTurn
    d.leftContinuous d.leftInjective (a := (1 / 2 : ℝ)) (b := 1)
    (by norm_num) (by norm_num) g.symm a⁻¹ (-((a : ℂ)⁻¹ * b))
    (fun x => by simpa only [sub_eq_add_neg] using hinvform x)
    (by simpa only [d.leftCutImage] using hIleft)
    L.inverse_cut_lift_continuous.continuousOn
    (L.inverse_cut_lift_antitone.strictAntiOn _)
    (fun t ht => L.inverse_cut_agrees ht) (symm_not_halfTurn g hnot)
  have hlocal' : Disjoint (Γ \ {p, q}) (g.symm '' (Γ \ {p, q})) := by
    simpa only [circleParam_image_Ioo d.leftInjective (by norm_num : (1 / 2 : ℝ) < 1)
      (by norm_num : (1 : ℝ) < 1 / 2 + 1), d.leftCutImage] using hlocal
  have hIopen : Disjoint ((g.symm '' Γ) \ {g.symm p, g.symm q}) (Γ \ {p, q}) := by
    simpa only [image_sdiff g.symm.injective, image_pair] using hlocal'.symm
  have hI := FirstOverlap.subset_complement_of_disjoint_arc_interiors_of_isJordanCurve
    (isJordanCurve_range_circle d.leftContinuous d.leftInjective)
    (d.leftCutPair.fst.image_homeomorph g.symm.toHomeomorph)
    d.leftCutPair.fst hIleft d.leftCutPair.fst_subset d.leftCutPair.union_eq.symm
    d.leftCutPair.snd.left_mem d.leftCutPair.snd.right_mem hIopen
  have hcancel : g '' (g.symm '' (Γ \ {p, q})) = Γ \ {p, q} := by
    apply Subset.antisymm
    · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      simpa only [g.apply_symm_apply] using hx
    · intro x hx
      exact ⟨g.symm x, ⟨x, hx, rfl⟩, g.apply_symm_apply x⟩
  have hJdis : Disjoint (g '' (Γ \ {p, q})) (Γ \ {p, q}) := by
    simpa only [hcancel] using (disjoint_image_iff g.injective).2 hlocal'
  have hJopen : Disjoint ((g '' Γ) \ {g p, g q}) (Γ \ {p, q}) := by
    simpa only [image_sdiff g.injective, image_pair] using hJdis
  have hJ := FirstOverlap.subset_complement_of_disjoint_arc_interiors_of_isJordanCurve
    (isJordanCurve_range_circle d.rightContinuous d.rightInjective)
    (d.rightCutPair.fst.image_homeomorph g.toHomeomorph)
    d.rightCutPair.fst hJright d.rightCutPair.fst_subset d.rightCutPair.union_eq.symm
    d.rightCutPair.snd.left_mem d.rightCutPair.snd.right_mem hJopen
  exact ⟨hI, hJ⟩

end BoundaryLifts

namespace BoundaryCoordinates

variable {M Γ N : Set Plane} (d : BoundaryCoordinates M Γ N)

/-- Before entering the image cut gap, the inverse congruence lies on the
left outer arc.  This follows from the actual boundary set identity. -/
theorem preimage_outer_gap_subset (g : Plane ≃ᵃⁱ[ℝ] Plane)
    (hboundary : g '' (M ∪ Γ) = N ∪ Γ) :
    g.symm '' (N \ g '' (Γ \
      {circleParam d.leftParam (1 / 2), circleParam d.leftParam 1})) ⊆ M := by
  have hgap := GapIdentity.image_outer_gap g.toHomeomorph
    d.leftCutPair.inter_eq d.rightCutPair.inter_eq hboundary
  change g '' (M \ g.symm '' (Γ \
    {circleParam d.leftParam (1 / 2), circleParam d.leftParam 1})) =
      N \ g '' (Γ \ {circleParam d.leftParam (1 / 2), circleParam d.leftParam 1}) at hgap
  rintro _ ⟨y, hy, rfl⟩
  rw [← hgap] at hy
  obtain ⟨x, hx, hxy⟩ := hy
  rw [← hxy, g.symm_apply_apply]
  exact hx.1

end BoundaryCoordinates

end Puzzling139335.CentralRotation
