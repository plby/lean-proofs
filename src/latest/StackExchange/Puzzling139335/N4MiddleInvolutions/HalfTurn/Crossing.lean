import StackExchange.Puzzling139335.SegmentCrossing
import StackExchange.Puzzling139335.JordanTransport

/-!
# Crossing an actual base with a half-turned actual arm

The full unit base and half-unit left arm are required to belong to the
Jordan region itself. Coordinate support puts these segments on its actual
frontier. Their transverse crossing after a half-turn then forces interior
overlap; no convex-hull chord is substituted for either segment.
-/

open Set

namespace Puzzling139335.N4MiddleInvolutions.HalfTurn

noncomputable section

private theorem segment_frontier_of_nonneg_coordinate {P : Set Plane} {A B : Plane}
    (i : Fin 2) (hsupport : ∀ p ∈ P, 0 ≤ p i)
    (hseg : segment ℝ A B ⊆ P) (hA : A i = 0) (hB : B i = 0) :
    segment ℝ A B ⊆ frontier P := by
  let f : Plane →L[ℝ] ℝ := -EuclideanSpace.proj i
  have hf : Function.Surjective f := by
    intro t
    refine ⟨(!₂[-t, -t] : Plane), ?_⟩
    change -(!₂[-t, -t] : Plane) i = t
    fin_cases i <;> simp
  refine SegmentCrossing.segment_subset_frontier_of_linear_support f hf
    (c := 0) ?_ hseg ?_ ?_
  · intro p hp
    change -p i ≤ 0
    exact neg_nonpos.mpr (hsupport p hp)
  · change -A i = 0
    rw [hA, neg_zero]
  · change -B i = 0
    rw [hB, neg_zero]

/-- In the stated intrinsic coordinate range, the actual base crosses the
half-turned actual left arm in the relative interior of both segments. -/
theorem not_disjoint_of_base_and_left_arm {P : Set Plane} {q : Plane}
    (hP : IsJordanRegion P)
    (hbox : P ⊆ {p : Plane | p 0 ∈ Icc (0 : ℝ) 1 ∧ p 1 ∈ Icc (0 : ℝ) (1 / 2)})
    (hbase : segment ℝ (!₂[0, 0] : Plane) (!₂[1, 0] : Plane) ⊆ P)
    (harm : segment ℝ (!₂[0, 0] : Plane) (!₂[0, (1 / 2 : ℝ)] : Plane) ⊆ P)
    (hu : q 0 ∈ Ioo (0 : ℝ) (1 / 2)) (hv : q 1 ∈ Ioo (0 : ℝ) (1 / 4)) :
    ¬ Disjoint (interior P)
      (interior (AffineIsometryEquiv.pointReflection ℝ q '' P)) := by
  let A : Plane := !₂[0, 0]
  let B : Plane := !₂[1, 0]
  let M : Plane := !₂[0, (1 / 2 : ℝ)]
  let e : Plane ≃ᵃⁱ[ℝ] Plane := AffineIsometryEquiv.pointReflection ℝ q
  have hQ : IsJordanRegion (e '' P) := hP.image_homeomorph e.toHomeomorph
  have hbaseFrontier : segment ℝ A B ⊆ frontier P :=
    segment_frontier_of_nonneg_coordinate 1 (fun p hp => (hbox hp).2.1)
      hbase rfl rfl
  have harmFrontier : segment ℝ A M ⊆ frontier P :=
    segment_frontier_of_nonneg_coordinate 0 (fun p hp => (hbox hp).1.1)
      harm rfl rfl
  have hsegmentImage : e '' segment ℝ A M = segment ℝ (e A) (e M) :=
    image_segment ℝ e.toAffineEquiv.toAffineMap A M
  have hfrontierImage : e '' frontier P = frontier (e '' P) :=
    e.toHomeomorph.image_frontier P
  have harmImageFrontier : segment ℝ (e A) (e M) ⊆ frontier (e '' P) := by
    rw [← hsegmentImage, ← hfrontierImage]
    exact image_mono harmFrontier
  have hdet : SegmentCrossing.det (B - A) (e M - e A) = -(1 / 2 : ℝ) := by
    simp [SegmentCrossing.det, A, B, M, e, AffineIsometryEquiv.pointReflection_apply,
      vsub_eq_sub, vadd_eq_add]
  have hdetNe : SegmentCrossing.det (B - A) (e M - e A) ≠ 0 := by
    rw [hdet]
    norm_num
  have ht : 2 * q 0 ∈ Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [hu.1, hu.2]
  have hs : 4 * q 1 ∈ Ioo (0 : ℝ) 1 := by
    constructor <;> linarith [hv.1, hv.2]
  have hpoint : SegmentCrossing.point A B (2 * q 0) =
      SegmentCrossing.point (e A) (e M) (4 * q 1) := by
    ext i
    fin_cases i <;>
      simp [SegmentCrossing.point, A, B, M, e, AffineIsometryEquiv.pointReflection_apply,
        vsub_eq_sub, vadd_eq_add] <;> ring
  exact SegmentCrossing.not_disjoint_interiors_of_point_eq hP hQ
    hbaseFrontier harmImageFrontier hdetNe ht hs hpoint

/-- Once the vertical coordinate is strictly below a quarter, disjointness
forces a positive intrinsic horizontal coordinate to be at least a half. -/
theorem half_le_first_coordinate_of_disjoint {P : Set Plane} {q : Plane}
    (hP : IsJordanRegion P)
    (hbox : P ⊆ {p : Plane | p 0 ∈ Icc (0 : ℝ) 1 ∧ p 1 ∈ Icc (0 : ℝ) (1 / 2)})
    (hbase : segment ℝ (!₂[0, 0] : Plane) (!₂[1, 0] : Plane) ⊆ P)
    (harm : segment ℝ (!₂[0, 0] : Plane) (!₂[0, (1 / 2 : ℝ)] : Plane) ⊆ P)
    (hu : 0 < q 0) (hv : q 1 ∈ Ioo (0 : ℝ) (1 / 4))
    (hdis : Disjoint (interior P)
      (interior (AffineIsometryEquiv.pointReflection ℝ q '' P))) :
    1 / 2 ≤ q 0 := by
  by_contra hlt
  exact not_disjoint_of_base_and_left_arm hP hbox hbase harm
    ⟨hu, not_le.mp hlt⟩ hv hdis

end

end Puzzling139335.N4MiddleInvolutions.HalfTurn
