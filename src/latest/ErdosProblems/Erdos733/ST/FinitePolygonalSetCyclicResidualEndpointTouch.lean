import ErdosProblems.Erdos733.ST.SimpleClosedPolygonalCurve
import Mathlib.Tactic

open Classical
noncomputable section

-- [TABLET NODE: FinitePolygonalSetCyclicResidualEndpointTouch]
lemma FinitePolygonalSetCyclicResidualEndpointTouch
    (J : SimpleClosedPolygonalCurve)
    {PieceIndex : Type}
    (pieceArc : PieceIndex → {γ : PolygonalArc // γ ∈ J.edgeArcs})
    (pieceSegmentIndex :
      (i : PieceIndex) → {n : ℕ // n + 1 < (pieceArc i).1.vertices.length})
    (pieceSource pieceTarget : PieceIndex → EuclideanSpace ℝ (Fin 2))
    (pieceSourceParam pieceTargetParam : PieceIndex → Set.Icc (0 : ℝ) 1)
    (hparam_lt : ∀ i, pieceSourceParam i < pieceTargetParam i)
    (pieceSource_eq :
      ∀ i,
        pieceSource i =
          AffineMap.lineMap
            ((pieceArc i).1.vertices[(pieceSegmentIndex i).1]'
              (Nat.lt_of_succ_lt (pieceSegmentIndex i).2))
            ((pieceArc i).1.vertices[(pieceSegmentIndex i).1 + 1]'
              (pieceSegmentIndex i).2)
            (pieceSourceParam i).1)
    (pieceTarget_eq :
      ∀ i,
        pieceTarget i =
          AffineMap.lineMap
            ((pieceArc i).1.vertices[(pieceSegmentIndex i).1]'
              (Nat.lt_of_succ_lt (pieceSegmentIndex i).2))
            ((pieceArc i).1.vertices[(pieceSegmentIndex i).1 + 1]'
              (pieceSegmentIndex i).2)
            (pieceTargetParam i).1)
    (pieceCarrier : PieceIndex → Set (EuclideanSpace ℝ (Fin 2)))
    (pieceCarrier_eq :
      ∀ i, pieceCarrier i = segment ℝ (pieceSource i) (pieceTarget i))
    (i j : PieceIndex)
    (hnot_same_elementary :
      ¬ (pieceArc i = pieceArc j ∧
        (pieceSegmentIndex i).1 = (pieceSegmentIndex j).1))
    (hnot_same_separated :
      ¬ (pieceArc i = pieceArc j ∧
        ((pieceSegmentIndex i).1 + 1 < (pieceSegmentIndex j).1 ∨
          (pieceSegmentIndex j).1 + 1 < (pieceSegmentIndex i).1)))
    (hnot_nonadjacent :
      ¬ (pieceArc j ≠ pieceArc i ∧
        pieceArc j ≠ J.successor (pieceArc i) ∧
        J.successor (pieceArc j) ≠ pieceArc i))
    (x : EuclideanSpace ℝ (Fin 2))
    (hxi : x ∈ pieceCarrier i) (hxj : x ∈ pieceCarrier j) :
    (x = pieceTarget i ∧ x = pieceSource j) ∨
      (x = pieceTarget j ∧ x = pieceSource i) := by
-- BODY
  classical
  have hpiece_subset_parent :
      ∀ q : PieceIndex,
        pieceCarrier q ⊆
          segment ℝ
            ((pieceArc q).1.vertices[(pieceSegmentIndex q).1]'
              (Nat.lt_of_succ_lt (pieceSegmentIndex q).2))
            ((pieceArc q).1.vertices[(pieceSegmentIndex q).1 + 1]'
              (pieceSegmentIndex q).2) := by
    intro q y hy
    rw [pieceCarrier_eq q] at hy
    have hs :
        pieceSource q ∈
          segment ℝ
            ((pieceArc q).1.vertices[(pieceSegmentIndex q).1]'
              (Nat.lt_of_succ_lt (pieceSegmentIndex q).2))
            ((pieceArc q).1.vertices[(pieceSegmentIndex q).1 + 1]'
              (pieceSegmentIndex q).2) := by
      rw [pieceSource_eq q, segment_eq_image_lineMap]
      exact ⟨(pieceSourceParam q).1, (pieceSourceParam q).2, rfl⟩
    have ht :
        pieceTarget q ∈
          segment ℝ
            ((pieceArc q).1.vertices[(pieceSegmentIndex q).1]'
              (Nat.lt_of_succ_lt (pieceSegmentIndex q).2))
            ((pieceArc q).1.vertices[(pieceSegmentIndex q).1 + 1]'
              (pieceSegmentIndex q).2) := by
      rw [pieceTarget_eq q, segment_eq_image_lineMap]
      exact ⟨(pieceTargetParam q).1, (pieceTargetParam q).2, rfl⟩
    exact (convex_segment _ _).segment_subset hs ht hy
  have hpiece_subset_arc :
      ∀ q : PieceIndex, pieceCarrier q ⊆ (pieceArc q).1.carrier := by
    intro q y hy
    rw [(pieceArc q).1.carrier_eq]
    exact ⟨(pieceSegmentIndex q).1, (pieceSegmentIndex q).2,
      hpiece_subset_parent q hy⟩
  have hparent_param_of_mem :
      ∀ (q : PieceIndex) {y : EuclideanSpace ℝ (Fin 2)},
        y ∈ pieceCarrier q →
          ∃ t : ℝ,
            (pieceSourceParam q).1 ≤ t ∧
              t ≤ (pieceTargetParam q).1 ∧
              y =
                AffineMap.lineMap
                  ((pieceArc q).1.vertices[(pieceSegmentIndex q).1]'
                    (Nat.lt_of_succ_lt (pieceSegmentIndex q).2))
                  ((pieceArc q).1.vertices[(pieceSegmentIndex q).1 + 1]'
                    (pieceSegmentIndex q).2)
                  t := by
    intro q y hy
    let A : EuclideanSpace ℝ (Fin 2) :=
      (pieceArc q).1.vertices[(pieceSegmentIndex q).1]'
        (Nat.lt_of_succ_lt (pieceSegmentIndex q).2)
    let B : EuclideanSpace ℝ (Fin 2) :=
      (pieceArc q).1.vertices[(pieceSegmentIndex q).1 + 1]'
        (pieceSegmentIndex q).2
    have hlt : (pieceSourceParam q).1 < (pieceTargetParam q).1 :=
      hparam_lt q
    have hyseg :
        y ∈ segment ℝ
            (AffineMap.lineMap A B (pieceSourceParam q).1)
            (AffineMap.lineMap A B (pieceTargetParam q).1) := by
      simpa [A, B, pieceCarrier_eq, pieceSource_eq, pieceTarget_eq] using hy
    have hseg_image :
        segment ℝ
            (AffineMap.lineMap A B (pieceSourceParam q).1)
            (AffineMap.lineMap A B (pieceTargetParam q).1) =
          (AffineMap.lineMap A B) '' Set.Icc
            (pieceSourceParam q).1 (pieceTargetParam q).1 := by
      rw [← image_segment ℝ (AffineMap.lineMap A B)
        (pieceSourceParam q).1 (pieceTargetParam q).1,
        segment_eq_Icc hlt.le]
    rw [hseg_image] at hyseg
    rcases hyseg with ⟨t, ht, hty⟩
    exact ⟨t, ht.1, ht.2, hty.symm⟩
  have htarget_of_right_endpoint :
      ∀ (q : PieceIndex) {y : EuclideanSpace ℝ (Fin 2)},
        y ∈ pieceCarrier q →
        y =
          (pieceArc q).1.vertices[(pieceSegmentIndex q).1 + 1]'
            (pieceSegmentIndex q).2 →
        y = pieceTarget q := by
    intro q y hy hy_right
    let A : EuclideanSpace ℝ (Fin 2) :=
      (pieceArc q).1.vertices[(pieceSegmentIndex q).1]'
        (Nat.lt_of_succ_lt (pieceSegmentIndex q).2)
    let B : EuclideanSpace ℝ (Fin 2) :=
      (pieceArc q).1.vertices[(pieceSegmentIndex q).1 + 1]'
        (pieceSegmentIndex q).2
    have hAB : A ≠ B := by
      intro hEq
      have hidx : (pieceSegmentIndex q).1 = (pieceSegmentIndex q).1 + 1 := by
        exact ((pieceArc q).1.simple_vertices.getElem_inj_iff).mp hEq
      omega
    rcases hparent_param_of_mem q hy with ⟨t, _hsrc_le, ht_le, hyt⟩
    have ht_eq_one : t = 1 := by
      apply AffineMap.lineMap_injective (k := ℝ) hAB
      calc
        AffineMap.lineMap A B t = y := hyt.symm
        _ = B := by simpa [B] using hy_right
        _ = AffineMap.lineMap A B (1 : ℝ) := by simp [A, B]
    have htarget_param : (pieceTargetParam q).1 = 1 := by
      have htarget_le_one : (pieceTargetParam q).1 ≤ 1 :=
        (pieceTargetParam q).2.2
      have hone_le_target : (1 : ℝ) ≤ (pieceTargetParam q).1 := by
        simpa [ht_eq_one] using ht_le
      exact le_antisymm htarget_le_one hone_le_target
    have htarget_right : pieceTarget q = B := by
      rw [pieceTarget_eq q, htarget_param]
      simp [A, B]
    exact hy_right.trans (by simpa [B] using htarget_right.symm)
  have hsource_of_left_endpoint :
      ∀ (q : PieceIndex) {y : EuclideanSpace ℝ (Fin 2)},
        y ∈ pieceCarrier q →
        y =
          (pieceArc q).1.vertices[(pieceSegmentIndex q).1]'
            (Nat.lt_of_succ_lt (pieceSegmentIndex q).2) →
        y = pieceSource q := by
    intro q y hy hy_left
    let A : EuclideanSpace ℝ (Fin 2) :=
      (pieceArc q).1.vertices[(pieceSegmentIndex q).1]'
        (Nat.lt_of_succ_lt (pieceSegmentIndex q).2)
    let B : EuclideanSpace ℝ (Fin 2) :=
      (pieceArc q).1.vertices[(pieceSegmentIndex q).1 + 1]'
        (pieceSegmentIndex q).2
    have hAB : A ≠ B := by
      intro hEq
      have hidx : (pieceSegmentIndex q).1 = (pieceSegmentIndex q).1 + 1 := by
        exact ((pieceArc q).1.simple_vertices.getElem_inj_iff).mp hEq
      omega
    rcases hparent_param_of_mem q hy with ⟨t, hsrc_le, _ht_le, hyt⟩
    have ht_eq_zero : t = 0 := by
      apply AffineMap.lineMap_injective (k := ℝ) hAB
      calc
        AffineMap.lineMap A B t = y := hyt.symm
        _ = A := by simpa [A] using hy_left
        _ = AffineMap.lineMap A B (0 : ℝ) := by simp [A, B]
    have hsource_param : (pieceSourceParam q).1 = 0 := by
      have hsource_nonneg : (0 : ℝ) ≤ (pieceSourceParam q).1 :=
        (pieceSourceParam q).2.1
      have hsource_le_zero : (pieceSourceParam q).1 ≤ 0 := by
        simpa [ht_eq_zero] using hsrc_le
      exact le_antisymm hsource_le_zero hsource_nonneg
    have hsource_left : pieceSource q = A := by
      rw [pieceSource_eq q, hsource_param]
      simp [A, B]
    exact hy_left.trans (by simpa [A] using hsource_left.symm)
  have htarget_of_arc_target :
      ∀ (q : PieceIndex) {y : EuclideanSpace ℝ (Fin 2)},
        y ∈ pieceCarrier q → y = (pieceArc q).1.target → y = pieceTarget q := by
    intro q y hy hy_target
    let γ : PolygonalArc := (pieceArc q).1
    let m : ℕ := (pieceSegmentIndex q).1
    have hm : m + 1 < γ.vertices.length := by
      simpa [γ, m] using (pieceSegmentIndex q).2
    by_cases hlast : m + 2 = γ.vertices.length
    · have hvertex_target :
          γ.vertices[m + 1]'hm = γ.target := by
        have hlast_some :
            γ.vertices.getLast? = some (γ.vertices[m + 1]'hm) := by
          rw [List.getLast?_eq_getElem?]
          have hidx : γ.vertices.length - 1 = m + 1 := by omega
          simp [hidx]
        exact Option.some.inj (by rw [← hlast_some, γ.target_eq_last])
      exact
        htarget_of_right_endpoint q hy
          (by simpa [γ, m, hvertex_target] using hy_target)
    · let r : ℕ := γ.vertices.length - 2
      have hr : r + 1 < γ.vertices.length := by
        have hlen : 2 ≤ γ.vertices.length := γ.length_ge_two
        dsimp [r]
        omega
      have hr_last : r + 1 = γ.vertices.length - 1 := by
        have hlen : 2 ≤ γ.vertices.length := γ.length_ge_two
        dsimp [r]
        omega
      have hm_lt_r : m < r := by
        have hle : m + 2 ≤ γ.vertices.length := by omega
        dsimp [r]
        omega
      have hy_parent :
          y ∈ segment ℝ
              (γ.vertices[m]'(Nat.lt_of_succ_lt hm))
              (γ.vertices[m + 1]'hm) := by
        simpa [γ, m] using hpiece_subset_parent q hy
      have htarget_parent :
          γ.target ∈ segment ℝ
              (γ.vertices[m]'(Nat.lt_of_succ_lt hm))
              (γ.vertices[m + 1]'hm) := by
        simpa [hy_target] using hy_parent
      have htarget_vertex_last :
          γ.target = γ.vertices[r + 1]'hr := by
        have hlast_some :
            γ.vertices.getLast? = some (γ.vertices[r + 1]'hr) := by
          rw [List.getLast?_eq_getElem?]
          simp [hr_last]
        exact (Option.some.inj (by rw [← hlast_some, γ.target_eq_last])).symm
      have htarget_last :
          γ.target ∈ segment ℝ
              (γ.vertices[r]'(Nat.lt_of_succ_lt hr))
              (γ.vertices[r + 1]'hr) := by
        rw [htarget_vertex_last]
        exact right_mem_segment ℝ _ _
      have htarget_inter :
          γ.target ∈
            segment ℝ
                (γ.vertices[m]'(Nat.lt_of_succ_lt hm))
                (γ.vertices[m + 1]'hm) ∩
              segment ℝ
                (γ.vertices[r]'(Nat.lt_of_succ_lt hr))
                (γ.vertices[r + 1]'hr) :=
        ⟨htarget_parent, htarget_last⟩
      have hinter := γ.segment_intersections hm hr hm_lt_r
      by_cases hadj : r = m + 1
      · have htarget_prev :
            γ.target = γ.vertices[r]'(Nat.lt_of_succ_lt hr) := by
          rw [hinter] at htarget_inter
          simpa [hadj] using htarget_inter
        have hidx : r = r + 1 := by
          exact γ.simple_vertices.getElem_inj_iff.mp
            (htarget_prev.symm.trans htarget_vertex_last)
        omega
      · have : γ.target ∈ (∅ : Set (EuclideanSpace ℝ (Fin 2))) := by
          rw [hinter] at htarget_inter
          simpa [hadj] using htarget_inter
        exact False.elim this
  have hsource_of_arc_source :
      ∀ (q : PieceIndex) {y : EuclideanSpace ℝ (Fin 2)},
        y ∈ pieceCarrier q → y = (pieceArc q).1.source → y = pieceSource q := by
    intro q y hy hy_source
    let γ : PolygonalArc := (pieceArc q).1
    let m : ℕ := (pieceSegmentIndex q).1
    have hm : m + 1 < γ.vertices.length := by
      simpa [γ, m] using (pieceSegmentIndex q).2
    by_cases hfirst : m = 0
    · have hvertex_source :
          γ.vertices[m]'(Nat.lt_of_succ_lt hm) = γ.source := by
        have hpos : 0 < γ.vertices.length := by
          have hlen := γ.length_ge_two
          omega
        have hhead_some :
            γ.vertices.head? = some (γ.vertices[0]'hpos) := by
          rw [List.head?_eq_getElem?]
          simp [hpos]
        have h0 : γ.vertices[0]'hpos = γ.source :=
          Option.some.inj (by rw [← hhead_some, γ.source_eq_head])
        simpa [hfirst] using h0
      exact
        hsource_of_left_endpoint q hy
          (by simpa [γ, m, hvertex_source] using hy_source)
    · have hzero_seg : 0 + 1 < γ.vertices.length := by
        have hlen := γ.length_ge_two
        omega
      have hzero_lt_m : 0 < m := by omega
      have hy_parent :
          y ∈ segment ℝ
              (γ.vertices[m]'(Nat.lt_of_succ_lt hm))
              (γ.vertices[m + 1]'hm) := by
        simpa [γ, m] using hpiece_subset_parent q hy
      have hsource_parent :
          γ.source ∈ segment ℝ
              (γ.vertices[m]'(Nat.lt_of_succ_lt hm))
              (γ.vertices[m + 1]'hm) := by
        simpa [hy_source] using hy_parent
      have hsource_vertex_zero :
          γ.source = γ.vertices[0]'(Nat.lt_of_succ_lt hzero_seg) := by
        have hhead_some :
            γ.vertices.head? =
              some (γ.vertices[0]'(Nat.lt_of_succ_lt hzero_seg)) := by
          rw [List.head?_eq_getElem?]
          simp
        exact (Option.some.inj (by rw [← hhead_some, γ.source_eq_head])).symm
      have hsource_zero :
          γ.source ∈ segment ℝ
              (γ.vertices[0]'(Nat.lt_of_succ_lt hzero_seg))
              (γ.vertices[0 + 1]'hzero_seg) := by
        rw [hsource_vertex_zero]
        exact left_mem_segment ℝ _ _
      have hsource_inter :
          γ.source ∈
            segment ℝ
                (γ.vertices[0]'(Nat.lt_of_succ_lt hzero_seg))
                (γ.vertices[0 + 1]'hzero_seg) ∩
              segment ℝ
                (γ.vertices[m]'(Nat.lt_of_succ_lt hm))
                (γ.vertices[m + 1]'hm) :=
        ⟨hsource_zero, hsource_parent⟩
      have hinter := γ.segment_intersections hzero_seg hm hzero_lt_m
      by_cases hadj : m = 0 + 1
      · have hsource_next :
            γ.source = γ.vertices[m]'(Nat.lt_of_succ_lt hm) := by
          rw [hinter] at hsource_inter
          simpa [hadj] using hsource_inter
        have hidx : 0 = m := by
          exact γ.simple_vertices.getElem_inj_iff.mp
            (hsource_vertex_zero.symm.trans hsource_next)
        omega
      · have : γ.source ∈ (∅ : Set (EuclideanSpace ℝ (Fin 2))) := by
          rw [hinter] at hsource_inter
          simpa [hadj] using hsource_inter
        exact False.elim this
  by_cases hsame_arc : pieceArc i = pieceArc j
  · let γ : PolygonalArc := (pieceArc i).1
    let a : ℕ := (pieceSegmentIndex i).1
    let b : ℕ := (pieceSegmentIndex j).1
    have hi : a + 1 < γ.vertices.length := by
      simpa [γ, a] using (pieceSegmentIndex i).2
    have hj : b + 1 < γ.vertices.length := by
      simpa [γ, b, hsame_arc] using (pieceSegmentIndex j).2
    have hab_ne : a ≠ b := by
      intro hab
      exact hnot_same_elementary ⟨hsame_arc, by simpa [a, b] using hab⟩
    have hnot_gap : ¬ (a + 1 < b ∨ b + 1 < a) := by
      intro hgap
      exact hnot_same_separated ⟨hsame_arc, by simpa [a, b] using hgap⟩
    have hadj : a + 1 = b ∨ b + 1 = a := by
      omega
    rcases hadj with hab | hba
    · have hxi_parent :
          x ∈ segment ℝ
              (γ.vertices[a]'(Nat.lt_of_succ_lt hi))
              (γ.vertices[a + 1]'hi) := by
        simpa [γ, a] using hpiece_subset_parent i hxi
      have hxj_parent :
          x ∈ segment ℝ
              (γ.vertices[b]'(Nat.lt_of_succ_lt hj))
              (γ.vertices[b + 1]'hj) := by
        simpa [γ, b, hsame_arc] using hpiece_subset_parent j hxj
      have hx_inter :
          x ∈ segment ℝ
              (γ.vertices[a]'(Nat.lt_of_succ_lt hi))
              (γ.vertices[a + 1]'hi) ∩
            segment ℝ
              (γ.vertices[b]'(Nat.lt_of_succ_lt hj))
              (γ.vertices[b + 1]'hj) :=
        ⟨hxi_parent, hxj_parent⟩
      have hinter := γ.segment_intersections hi hj (by omega)
      have hx_vertex : x = γ.vertices[b]'(Nat.lt_of_succ_lt hj) := by
        rw [hinter] at hx_inter
        simpa [hab] using hx_inter
      have hx_right_i :
          x =
            (pieceArc i).1.vertices[(pieceSegmentIndex i).1 + 1]'
              (pieceSegmentIndex i).2 := by
        simpa [γ, a, hab] using hx_vertex
      have hx_left_j :
          x =
            (pieceArc j).1.vertices[(pieceSegmentIndex j).1]'
              (Nat.lt_of_succ_lt (pieceSegmentIndex j).2) := by
        simpa [γ, b, hsame_arc] using hx_vertex
      exact Or.inl
        ⟨htarget_of_right_endpoint i hxi hx_right_i,
          hsource_of_left_endpoint j hxj hx_left_j⟩
    · have hxj_parent :
          x ∈ segment ℝ
              (γ.vertices[b]'(Nat.lt_of_succ_lt hj))
              (γ.vertices[b + 1]'hj) := by
        simpa [γ, b, hsame_arc] using hpiece_subset_parent j hxj
      have hxi_parent :
          x ∈ segment ℝ
              (γ.vertices[a]'(Nat.lt_of_succ_lt hi))
              (γ.vertices[a + 1]'hi) := by
        simpa [γ, a] using hpiece_subset_parent i hxi
      have hx_inter :
          x ∈ segment ℝ
              (γ.vertices[b]'(Nat.lt_of_succ_lt hj))
              (γ.vertices[b + 1]'hj) ∩
            segment ℝ
              (γ.vertices[a]'(Nat.lt_of_succ_lt hi))
              (γ.vertices[a + 1]'hi) :=
        ⟨hxj_parent, hxi_parent⟩
      have hinter := γ.segment_intersections hj hi (by omega)
      have hx_vertex : x = γ.vertices[a]'(Nat.lt_of_succ_lt hi) := by
        rw [hinter] at hx_inter
        simpa [hba] using hx_inter
      have hx_right_j :
          x =
            (pieceArc j).1.vertices[(pieceSegmentIndex j).1 + 1]'
              (pieceSegmentIndex j).2 := by
        simpa [γ, b, hsame_arc, hba] using hx_vertex
      have hx_left_i :
          x =
            (pieceArc i).1.vertices[(pieceSegmentIndex i).1]'
              (Nat.lt_of_succ_lt (pieceSegmentIndex i).2) := by
        simpa [γ, a] using hx_vertex
      exact Or.inr
        ⟨htarget_of_right_endpoint j hxj hx_right_j,
          hsource_of_left_endpoint i hxi hx_left_i⟩
  · have hji_ne : pieceArc j ≠ pieceArc i := by
      intro hji
      exact hsame_arc hji.symm
    have hadj_arc :
        pieceArc j = J.successor (pieceArc i) ∨
          J.successor (pieceArc j) = pieceArc i := by
      by_cases hforward : pieceArc j = J.successor (pieceArc i)
      · exact Or.inl hforward
      · by_cases hback : J.successor (pieceArc j) = pieceArc i
        · exact Or.inr hback
        · exact False.elim (hnot_nonadjacent ⟨hji_ne, hforward, hback⟩)
    rcases hadj_arc with hforward | hback
    · have hxi_arc : x ∈ (pieceArc i).1.carrier :=
        hpiece_subset_arc i hxi
      have hxj_arc : x ∈ (J.successor (pieceArc i)).1.carrier := by
        simpa [hforward] using hpiece_subset_arc j hxj
      have hx_inter :
          x ∈ (pieceArc i).1.carrier ∩
              (J.successor (pieceArc i)).1.carrier :=
        ⟨hxi_arc, hxj_arc⟩
      have hinter := J.adjacent_intersection (pieceArc i)
      have hx_target_i_arc : x = (pieceArc i).1.target := by
        rw [hinter] at hx_inter
        simpa using hx_inter
      have hx_source_j_arc : x = (pieceArc j).1.source := by
        calc
          x = (pieceArc i).1.target := hx_target_i_arc
          _ = (J.successor (pieceArc i)).1.source :=
            J.adjacent_endpoint (pieceArc i)
          _ = (pieceArc j).1.source := by rw [← hforward]
      exact Or.inl
        ⟨htarget_of_arc_target i hxi hx_target_i_arc,
          hsource_of_arc_source j hxj hx_source_j_arc⟩
    · have hxj_arc : x ∈ (pieceArc j).1.carrier :=
        hpiece_subset_arc j hxj
      have hxi_arc : x ∈ (J.successor (pieceArc j)).1.carrier := by
        simpa [hback] using hpiece_subset_arc i hxi
      have hx_inter :
          x ∈ (pieceArc j).1.carrier ∩
              (J.successor (pieceArc j)).1.carrier :=
        ⟨hxj_arc, hxi_arc⟩
      have hinter := J.adjacent_intersection (pieceArc j)
      have hx_target_j_arc : x = (pieceArc j).1.target := by
        rw [hinter] at hx_inter
        simpa using hx_inter
      have hx_source_i_arc : x = (pieceArc i).1.source := by
        calc
          x = (pieceArc j).1.target := hx_target_j_arc
          _ = (J.successor (pieceArc j)).1.source :=
            J.adjacent_endpoint (pieceArc j)
          _ = (pieceArc i).1.source := by rw [hback]
      exact Or.inr
        ⟨htarget_of_arc_target j hxj hx_target_j_arc,
          hsource_of_arc_source i hxi hx_source_i_arc⟩
