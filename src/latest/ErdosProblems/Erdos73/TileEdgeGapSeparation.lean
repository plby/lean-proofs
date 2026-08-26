import ErdosProblems.Erdos73.TileEdgeGaps

/-! Normalized gap regions are disjoint for distinct pattern edges, and meet arms at ports. -/

namespace Erdos73.BrickTileArray
noncomputable section
open scoped Classical
open SimpleGraph Finset

variable {c r C R : ℕ} (A : BrickTileArray c r C R)

theorem edgeGap_inter_code {u v s t : ElementaryWallVertex c r}
    (huv : (elementaryWall c r).Adj u v) (hst : (elementaryWall c r).Adj s t)
    {x : ElementaryWallVertex C R} (hx : x ∈ A.edgeGap u v) (hx' : x ∈ A.edgeGap s t) :
    brickEdgeCode u v = brickEdgeCode s t := by
  have hu := brickAdj_coordinates huv
  have hs := brickAdj_coordinates hst
  by_cases hr : u.val.1 = v.val.1
  · have hrv := congrArg Fin.val hr
    have hj : (min u.val.2 v.val.2).val + 1 = (max u.val.2 v.val.2).val := by
      simp only [fin_min_val, fin_max_val]
      omega
    rw [edgeGap, if_pos hr] at hx
    by_cases hsrow : s.val.1 = t.val.1
    · have hsv := congrArg Fin.val hsrow
      have ht : (min s.val.2 t.val.2).val + 1 = (max s.val.2 t.val.2).val := by
        simp only [fin_min_val, fin_max_val]
        omega
      rw [edgeGap, if_pos hsrow] at hx'
      obtain ⟨hi, hj', _⟩ := A.horizontalGap_inter_indices hj ht hx hx'
      have hi' := congrArg Fin.val hi
      have hj'' := congrArg Fin.val hj'
      simp only [fin_min_val] at hj''
      dsimp only [brickEdgeCode]
      rw [if_pos hrv, if_pos hsv, hi', hj'']
    · rw [edgeGap, if_neg hsrow] at hx'
      exact (Finset.disjoint_left.mp (A.horizontalGap_disjoint_verticalGap
        u.val.1 (min s.val.1 t.val.1) (max s.val.1 t.val.1)
        (min u.val.2 v.val.2) (max u.val.2 v.val.2) s.val.2 hj) hx hx').elim
  · have hrv : u.val.1.val ≠ v.val.1.val := fun he => hr (Fin.ext he)
    have hi : (min u.val.1 v.val.1).val + 1 = (max u.val.1 v.val.1).val := by
      simp only [fin_min_val, fin_max_val]
      omega
    rw [edgeGap, if_neg hr] at hx
    by_cases hsrow : s.val.1 = t.val.1
    · have hsv := congrArg Fin.val hsrow
      have ht : (min s.val.2 t.val.2).val + 1 = (max s.val.2 t.val.2).val := by
        simp only [fin_min_val, fin_max_val]
        omega
      rw [edgeGap, if_pos hsrow] at hx'
      exact (Finset.disjoint_left.mp (A.horizontalGap_disjoint_verticalGap
        s.val.1 (min u.val.1 v.val.1) (max u.val.1 v.val.1)
        (min s.val.2 t.val.2) (max s.val.2 t.val.2) u.val.2 ht) hx' hx).elim
    · have hsv : s.val.1.val ≠ t.val.1.val := fun he => hsrow (Fin.ext he)
      have ht : (min s.val.1 t.val.1).val + 1 = (max s.val.1 t.val.1).val := by
        simp only [fin_min_val, fin_max_val]
        omega
      rw [edgeGap, if_neg hsrow] at hx'
      obtain ⟨hi', _, hj⟩ := A.verticalGap_inter_indices hi ht hx hx'
      have hi'' := congrArg Fin.val hi'
      have hj' := congrArg Fin.val hj
      simp only [fin_min_val] at hi''
      dsimp only [brickEdgeCode]
      rw [if_neg hrv, if_neg hsv, hi'', hj']

theorem edgeGap_disjoint {e f : OrientedEdge (elementaryWall c r)} (hef : e ≠ f) :
    Disjoint (A.edgeGap e.lo e.hi) (A.edgeGap f.lo f.hi) := by
  apply Finset.disjoint_left.mpr
  intro x hx hx'
  exact hef (brickEdgeCode_injective (A.edgeGap_inter_code e.adj f.adj hx hx'))

theorem horizontal_edgeGap_arm_endpoint {u v : ElementaryWallVertex c r}
    (hrow : u.val.1 = v.val.1) (hcol : u.val.2.val + 1 = v.val.2.val)
    (w : ElementaryWallVertex c r) (a : Fin 3) {x : ElementaryWallVertex C R}
    (hx : x ∈ A.edgeGap u v) (hwa : x ∈ (A.arm w a).vertexSet) :
    ((w = u ∧ a = brickWallPort u.val v.val) ∨
      (w = v ∧ a = brickWallPort v.val u.val)) ∧ x = (A.arm w a).target := by
  rw [A.edgeGap_eq_horizontal hrow hcol] at hx
  obtain ⟨hr, hh⟩ := A.horizontalGap_arm_endpoint hcol w a hx hwa
  have hp := brickWallPort_horizontal_forward hrow hcol
  rcases hh with ⟨hc, ha, he⟩ | ⟨hc, ha, he⟩
  · exact ⟨Or.inl ⟨Subtype.ext (Prod.ext hr hc), ha.trans hp.1.symm⟩, by simpa only [ha] using he⟩
  · exact ⟨Or.inr ⟨Subtype.ext (Prod.ext (hr.trans hrow) hc), ha.trans hp.2.symm⟩,
      by simpa only [ha] using he⟩

theorem vertical_edgeGap_arm_endpoint {u v : ElementaryWallVertex c r}
    (hrow : u.val.1.val + 1 = v.val.1.val) (hcol : u.val.2 = v.val.2)
    (hpar : (u.val.2.val + u.val.1.val) % 2 = 1)
    (w : ElementaryWallVertex c r) (a : Fin 3) {x : ElementaryWallVertex C R}
    (hx : x ∈ A.edgeGap u v) (hwa : x ∈ (A.arm w a).vertexSet) :
    ((w = u ∧ a = brickWallPort u.val v.val) ∨
      (w = v ∧ a = brickWallPort v.val u.val)) ∧ x = (A.arm w a).target := by
  rw [A.edgeGap_eq_vertical hrow] at hx
  obtain ⟨hc, hr, ha, he⟩ := A.verticalGap_arm_endpoint hrow hpar w a hx hwa
  have hn : u.val.1 ≠ v.val.1 := by intro he; have hh := congrArg Fin.val he; omega
  have hp := brickWallPort_vertical hn
  have hp' := brickWallPort_vertical (Ne.symm hn)
  refine ⟨?_, by simpa only [ha] using he⟩
  rcases hr with hr | hr
  · exact Or.inl ⟨Subtype.ext (Prod.ext hr hc), ha.trans hp.symm⟩
  · exact Or.inr ⟨Subtype.ext (Prod.ext hr (hc.trans hcol)), ha.trans hp'.symm⟩

theorem edgeGap_arm_endpoint {u v : ElementaryWallVertex c r}
    (huv : (elementaryWall c r).Adj u v) (w : ElementaryWallVertex c r) (a : Fin 3)
    {x : ElementaryWallVertex C R} (hx : x ∈ A.edgeGap u v)
    (hwa : x ∈ (A.arm w a).vertexSet) :
    ((w = u ∧ a = brickWallPort u.val v.val) ∨
      (w = v ∧ a = brickWallPort v.val u.val)) ∧ x = (A.arm w a).target := by
  have hsym := A.edgeGap_symm huv
  change (rawBrickWall c r).Adj u.val v.val at huv
  rcases huv with ⟨hr, hc⟩ | ⟨hc, hr⟩
  · rcases pathGraph_adj.mp hc with hcol | hcol
    · exact A.horizontal_edgeGap_arm_endpoint hr hcol w a hx hwa
    · rw [hsym] at hx
      obtain ⟨hh, he⟩ := A.horizontal_edgeGap_arm_endpoint hr.symm hcol w a hx hwa
      exact ⟨hh.symm, he⟩
  · rcases hr with ⟨hrow, hpar⟩ | ⟨hrow, hpar⟩
    · exact A.vertical_edgeGap_arm_endpoint hrow hc hpar w a hx hwa
    · rw [hsym] at hx
      obtain ⟨hh, he⟩ := A.vertical_edgeGap_arm_endpoint hrow hc.symm hpar w a hx hwa
      exact ⟨hh.symm, he⟩

end
end Erdos73.BrickTileArray
