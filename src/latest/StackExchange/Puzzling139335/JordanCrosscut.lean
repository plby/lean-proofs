import StackExchange.Puzzling139335.ArcStraightening
import StackExchange.Puzzling139335.JordanTransport

/-!
# Crosscuts with arbitrary Jordan arcs

The existing crosscut theorem assumes that the cutting arc is polygonal.  A
homeomorphism straightens that arc; transporting the result back removes this
restriction without adding an assumption.
-/

open Set Schoenflies

namespace Puzzling139335

/-- A simple crosscut of a Jordan domain, with no rectifiability assumption. -/
structure JordanCrosscut (C P : Set Plane) (p q : Plane) : Prop where
  curve : IsJordanCurve C
  arc : IsArcBetween P p q
  left_mem : p ∈ C
  right_mem : q ∈ C
  sdiff_subset : P \ {p, q} ⊆ inside C

namespace JordanCrosscut

variable {C P A B : Set Plane} {p q : Plane}

theorem inter_eq (h : JordanCrosscut C P p q) : P ∩ C = {p, q} := by
  apply Subset.antisymm
  · intro x hx
    by_contra hxpair
    exact (h.sdiff_subset ⟨hx.1, hxpair⟩).1 hx.2
  · exact pair_subset ⟨h.arc.left_mem, h.left_mem⟩ ⟨h.arc.right_mem, h.right_mem⟩

theorem inter_arc_eq (h : JordanCrosscut C P p q) (hc : IsCutPair C p q A B) :
    P ∩ A = {p, q} := by
  apply Subset.antisymm
  · intro x hx
    exact h.inter_eq ▸ ⟨hx.1, hc.fst_subset hx.2⟩
  · exact pair_subset ⟨h.arc.left_mem, hc.fst.left_mem⟩
      ⟨h.arc.right_mem, hc.fst.right_mem⟩

theorem isJordanCurve_union (h : JordanCrosscut C P p q) (hc : IsCutPair C p q A B) :
    IsJordanCurve (A ∪ P) := by
  apply Schoenflies.isJordanCurve_union hc.fst h.arc
  intro x hxA hxP
  have hx := h.inter_arc_eq hc ▸ (show x ∈ P ∩ A from ⟨hxP, hxA⟩)
  simpa only [mem_insert_iff, mem_singleton_iff] using hx

theorem image_of_polygonal (h : JordanCrosscut C P p q) (e : Plane ≃ₜ Plane)
    (hp : IsPolygonal (e '' P)) :
    IsCrosscut (e '' C) (e '' P) (e p) (e q) := by
  refine ⟨h.curve.image_homeomorph e, h.arc.image_homeomorph e, hp,
    mem_image_of_mem e h.left_mem, mem_image_of_mem e h.right_mem, ?_⟩
  have himage := image_mono h.sdiff_subset (f := (e : Plane → Plane))
  rw [image_sdiff e.injective, image_pair, homeomorph_image_inside] at himage
  exact himage

/-- The cutting arc can be made polygonal while preserving the whole configuration. -/
theorem exists_polygonal_image (h : JordanCrosscut C P p q) (hc : IsCutPair C p q A B) :
    ∃ e : Plane ≃ₜ Plane, IsCrosscut (e '' C) (e '' P) (e p) (e q) := by
  have hpair : IsCutPair (P ∪ A) p q P A :=
    ⟨h.arc, hc.fst, rfl, h.inter_arc_eq hc⟩
  obtain ⟨e, _, hpoly, _⟩ := cutPair_exists_polygonal_homeomorph hpair
  exact ⟨e, h.image_of_polygonal e hpoly⟩

/-- An arbitrary crosscut divides the open Jordan domain into its two named sides. -/
theorem inside_diff_eq (h : JordanCrosscut C P p q) (hc : IsCutPair C p q A B) :
    inside C \ P = inside (A ∪ P) ∪ inside (B ∪ P) := by
  obtain ⟨e, he⟩ := h.exists_polygonal_image hc
  have hcross := (crosscut_theorem he (hc.image_homeomorph e)).1
  apply e.injective.image_injective
  rw [image_sdiff e.injective, homeomorph_image_inside, image_union,
    homeomorph_image_inside, homeomorph_image_inside, image_union, image_union]
  exact hcross

theorem disjoint_sides (h : JordanCrosscut C P p q) (hc : IsCutPair C p q A B) :
    Disjoint (inside (A ∪ P)) (inside (B ∪ P)) := by
  obtain ⟨e, he⟩ := h.exists_polygonal_image hc
  have hcross := (crosscut_theorem he (hc.image_homeomorph e)).2.1
  apply Set.disjoint_left.mpr
  intro x hxA hxB
  apply Set.disjoint_left.mp hcross
  · rw [← image_union, ← homeomorph_image_inside]
    exact mem_image_of_mem e hxA
  · rw [← image_union, ← homeomorph_image_inside]
    exact mem_image_of_mem e hxB

theorem closure_side_inter (h : JordanCrosscut C P p q) (hc : IsCutPair C p q A B) :
    closure (inside (A ∪ P)) ∩ C = A := by
  obtain ⟨e, he⟩ := h.exists_polygonal_image hc
  have hcross := he.closure_side_inter (fun _ h => jordan_curve_theorem h)
    (hc.image_homeomorph e)
  apply e.injective.image_injective
  rw [image_inter e.injective, e.image_closure, homeomorph_image_inside, image_union]
  exact hcross

theorem side_subset (h : JordanCrosscut C P p q) (hc : IsCutPair C p q A B) :
    inside (A ∪ P) ⊆ inside C \ P := by
  rw [h.inside_diff_eq hc]
  exact subset_union_left

theorem side_isComponent (h : JordanCrosscut C P p q) (hc : IsCutPair C p q A B)
    {x : Plane} (hx : x ∈ inside (A ∪ P)) :
    connectedComponentIn (inside C \ P) x = inside (A ∪ P) := by
  obtain ⟨e, he⟩ := h.exists_polygonal_image hc
  have hcomponent := he.side_isComponent (fun _ h => jordan_curve_theorem h)
    (hc.image_homeomorph e)
  apply e.injective.image_injective
  rw [e.image_connectedComponentIn (h.side_subset hc hx),
    image_sdiff e.injective, homeomorph_image_inside, homeomorph_image_inside, image_union]
  apply hcomponent
  rw [← image_union, ← homeomorph_image_inside]
  exact mem_image_of_mem e hx

theorem side_nonempty (h : JordanCrosscut C P p q) (hc : IsCutPair C p q A B) :
    (inside (A ∪ P)).Nonempty :=
  (jordan_curve_theorem (h.isJordanCurve_union hc)).isConnected_inside.nonempty

theorem side_isJordanRegion (h : JordanCrosscut C P p q) (hc : IsCutPair C p q A B) :
    IsJordanRegion (closure (inside (A ∪ P))) :=
  ⟨A ∪ P, h.isJordanCurve_union hc, rfl⟩

/-- The two closed sides fill the closed original domain. -/
theorem closure_inside_eq_union (h : JordanCrosscut C P p q) (hc : IsCutPair C p q A B) :
    closure (inside C) = closure (inside (A ∪ P)) ∪ closure (inside (B ∪ P)) := by
  have hC := jordan_curve_theorem h.curve
  have hA := jordan_curve_theorem (h.isJordanCurve_union hc)
  have hB := jordan_curve_theorem (h.isJordanCurve_union hc.symm)
  rw [(IsRegionOf.inside C).closure_eq hC,
    (IsRegionOf.inside (A ∪ P)).closure_eq hA,
    (IsRegionOf.inside (B ∪ P)).closure_eq hB]
  ext x
  constructor
  · rintro (hx | hx)
    · by_cases hxP : x ∈ P
      · exact Or.inl (Or.inr (Or.inr hxP))
      · have hm : x ∈ inside (A ∪ P) ∪ inside (B ∪ P) := h.inside_diff_eq hc ▸ ⟨hx, hxP⟩
        exact hm.elim (fun hx => Or.inl (Or.inl hx)) (fun hx => Or.inr (Or.inl hx))
    · rw [← hc.union_eq] at hx
      exact hx.elim (fun hx => Or.inl (Or.inr (Or.inl hx)))
        (fun hx => Or.inr (Or.inr (Or.inl hx)))
  · rintro ((hx | (hx | hx)) | (hx | (hx | hx)))
    · exact Or.inl (h.side_subset hc hx).1
    · exact Or.inr (hc.fst_subset hx)
    · by_cases hpq : x ∈ ({p, q} : Set Plane)
      · exact Or.inr (by rcases hpq with rfl | rfl; exacts [h.left_mem, h.right_mem])
      · exact Or.inl (h.sdiff_subset ⟨hx, hpq⟩)
    · exact Or.inl (h.side_subset hc.symm hx).1
    · exact Or.inr (hc.snd_subset hx)
    · by_cases hpq : x ∈ ({p, q} : Set Plane)
      · exact Or.inr (by rcases hpq with rfl | rfl; exacts [h.left_mem, h.right_mem])
      · exact Or.inl (h.sdiff_subset ⟨hx, hpq⟩)

/-- The two closed sides meet exactly along the crosscut. -/
theorem closure_sides_inter (h : JordanCrosscut C P p q) (hc : IsCutPair C p q A B) :
    closure (inside (A ∪ P)) ∩ closure (inside (B ∪ P)) = P := by
  have hA := jordan_curve_theorem (h.isJordanCurve_union hc)
  have hB := jordan_curve_theorem (h.isJordanCurve_union hc.symm)
  rw [(IsRegionOf.inside (A ∪ P)).closure_eq hA,
    (IsRegionOf.inside (B ∪ P)).closure_eq hB]
  apply Subset.antisymm
  · intro x hx
    rcases hx with ⟨hxA | hxA | hxP, hxB | hxB | hxP⟩
    · exact False.elim (Set.disjoint_left.mp (h.disjoint_sides hc) hxA hxB)
    · exact False.elim ((h.side_subset hc hxA).1.1 (hc.snd_subset hxB))
    · exact hxP
    · exact False.elim ((h.side_subset hc.symm hxB).1.1 (hc.fst_subset hxA))
    · have hxpair : x ∈ ({p, q} : Set Plane) := hc.inter_eq ▸ ⟨hxA, hxB⟩
      rcases hxpair with rfl | rfl
      exacts [h.arc.left_mem, h.arc.right_mem]
    · exact hxP
    · exact hxP
    · exact hxP
    · exact hxP
  · intro x hx
    exact ⟨Or.inr (Or.inr hx), Or.inr (Or.inr hx)⟩

/-- A connected set approaching opposite boundary arcs must meet the crosscut. -/
theorem inter_nonempty_of_alternating {Q : Set Plane} {r s : Plane}
    (h : JordanCrosscut C P p q) (hc : IsCutPair C p q A B)
    (hQ : IsPreconnected Q) (hsub : Q ⊆ inside C)
    (hr : r ∈ closure Q) (hs : s ∈ closure Q)
    (hrA : r ∈ A) (hrB : r ∉ B) (hsB : s ∈ B) (hsA : s ∉ A) :
    (Q ∩ P).Nonempty := by
  by_contra hnone
  have hsub' : Q ⊆ inside C \ P := by
    intro x hx
    exact ⟨hsub hx, fun hxP => hnone ⟨x, hx, hxP⟩⟩
  have hcover : Q ⊆ inside (A ∪ P) ∪ inside (B ∪ P) := h.inside_diff_eq hc ▸ hsub'
  have hopenA := (jordan_curve_theorem (h.isJordanCurve_union hc)).isOpen_inside
  have hopenB := (jordan_curve_theorem (h.isJordanCurve_union hc.symm)).isOpen_inside
  rcases hQ.subset_or_subset hopenA hopenB (h.disjoint_sides hc) hcover with hQA | hQB
  · have hm : s ∈ closure (inside (A ∪ P)) ∩ C := ⟨closure_mono hQA hs, hc.snd_subset hsB⟩
    rw [h.closure_side_inter hc] at hm
    exact hsA hm
  · have hm : r ∈ closure (inside (B ∪ P)) ∩ C := ⟨closure_mono hQB hr, hc.fst_subset hrA⟩
    rw [h.closure_side_inter hc.symm] at hm
    exact hrB hm

/-- Two crosscut arcs with alternating endpoints intersect. -/
theorem arc_inter_nonempty_of_alternating {Q : Set Plane} {r s : Plane}
    (h : JordanCrosscut C P p q) (hc : IsCutPair C p q A B)
    (hQ : IsArcBetween Q r s) (hsub : Q \ {r, s} ⊆ inside C)
    (hrA : r ∈ A) (hrB : r ∉ B) (hsB : s ∈ B) (hsA : s ∉ A) :
    ((Q \ {r, s}) ∩ P).Nonempty :=
  h.inter_nonempty_of_alternating hc hQ.isPreconnected_diff hsub
    hQ.left_mem_closure_diff hQ.right_mem_closure_diff hrA hrB hsB hsA

end JordanCrosscut

end Puzzling139335
