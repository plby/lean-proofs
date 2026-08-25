import Util.IncidenceGeometry.FinitePolygonalSetElementaryComplex
import Util.IncidenceGeometry.FiniteElementarySegmentCutParameterList
import Util.IncidenceGeometry.FiniteSortedRealCutListCoversUnitInterval
import Util.IncidenceGeometry.CollinearAdjacentSubsegmentsMeetAtEndpoint

open Classical
noncomputable section


lemma FinitePolygonalSetElementaryComplexExists (K : FinitePolygonalSet) :
    Nonempty (FinitePolygonalSetElementaryComplex K) := by
  classical
  let Raw := {s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) // s ∈ K.segments}
  let cutList : Raw → List ℝ := fun s =>
    Classical.choose
      (FiniteElementarySegmentCutParameterList s.1.1 s.1.2
        (K.segment_nondegenerate s.1 s.2) K.points)
  have cutSpec :
      ∀ s : Raw,
        (cutList s).Nodup ∧
          (cutList s).SortedLT ∧
            (∀ t : ℝ, t ∈ cutList s ↔
              t = 0 ∨ t = 1 ∨
                (0 ≤ t ∧ t ≤ 1 ∧
                  AffineMap.lineMap s.1.1 s.1.2 t ∈ K.points)) ∧
              (0 : ℝ) ∈ cutList s ∧
                (1 : ℝ) ∈ cutList s ∧
                  (∀ t : ℝ, t ∈ cutList s → 0 ≤ t ∧ t ≤ 1) ∧
                    (∀ n (hn : n + 1 < (cutList s).length),
                      (cutList s)[n] < (cutList s)[n + 1]) ∧
                      (∀ n (hn : n + 1 < (cutList s).length) t,
                        0 ≤ t → t ≤ 1 →
                          AffineMap.lineMap s.1.1 s.1.2 t ∈ K.points →
                            ¬ ((cutList s)[n] < t ∧ t < (cutList s)[n + 1])) := by
    intro s
    simpa [cutList] using
      Classical.choose_spec
        (FiniteElementarySegmentCutParameterList s.1.1 s.1.2
          (K.segment_nondegenerate s.1 s.2) K.points)
  have cut_nodup : ∀ s : Raw, (cutList s).Nodup := fun s => (cutSpec s).1
  have cut_sorted : ∀ s : Raw, (cutList s).SortedLT := fun s => (cutSpec s).2.1
  have cut_mem :
      ∀ s : Raw, ∀ t : ℝ, t ∈ cutList s ↔
        t = 0 ∨ t = 1 ∨
          (0 ≤ t ∧ t ≤ 1 ∧ AffineMap.lineMap s.1.1 s.1.2 t ∈ K.points) :=
    fun s => (cutSpec s).2.2.1
  have cut_zero : ∀ s : Raw, (0 : ℝ) ∈ cutList s :=
    fun s => (cutSpec s).2.2.2.1
  have cut_one : ∀ s : Raw, (1 : ℝ) ∈ cutList s :=
    fun s => (cutSpec s).2.2.2.2.1
  have cut_bounds : ∀ s : Raw, ∀ t : ℝ, t ∈ cutList s → 0 ≤ t ∧ t ≤ 1 :=
    fun s => (cutSpec s).2.2.2.2.2.1
  have cut_lt :
      ∀ s : Raw, ∀ n (hn : n + 1 < (cutList s).length),
        (cutList s)[n] < (cutList s)[n + 1] :=
    fun s => (cutSpec s).2.2.2.2.2.2.1
  have cut_no_between :
      ∀ s : Raw, ∀ n (hn : n + 1 < (cutList s).length) t,
        0 ≤ t → t ≤ 1 →
          AffineMap.lineMap s.1.1 s.1.2 t ∈ K.points →
            ¬ ((cutList s)[n] < t ∧ t < (cutList s)[n + 1]) :=
    fun s => (cutSpec s).2.2.2.2.2.2.2
  have open_subsegment_parameters :
      ∀ (A B : EuclideanSpace ℝ (Fin 2)) {u v : ℝ}, u < v →
        ∀ {x : EuclideanSpace ℝ (Fin 2)},
          x ∈ openSegment ℝ (AffineMap.lineMap A B u) (AffineMap.lineMap A B v) →
            ∃ t : ℝ, u < t ∧ t < v ∧ x = AffineMap.lineMap A B t := by
    intro A B u v huv x hx
    rw [openSegment_eq_image_lineMap] at hx
    rcases hx with ⟨θ, hθ, rfl⟩
    refine ⟨(1 - θ) * u + θ * v, ?_, ?_, ?_⟩
    · nlinarith [hθ.1, hθ.2, huv]
    · nlinarith [hθ.1, hθ.2, huv]
    · ext i
      simp [AffineMap.lineMap_apply_module]
      ring
  let IsCutEdge :
      Raw → EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) → Prop :=
    fun s e =>
      ∃ k, ∃ hk : k + 1 < (cutList s).length,
        e.1 =
            AffineMap.lineMap s.1.1 s.1.2
              ((cutList s)[k]'(Nat.lt_of_succ_lt hk)) ∧
          e.2 =
            AffineMap.lineMap s.1.1 s.1.2
              ((cutList s)[k + 1]'hk)
  let EdgeGood : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) → Prop :=
    fun e => e.1 ≠ e.2 ∧ ∃ s : Raw, IsCutEdge s e
  let edges : Finset (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) :=
    (K.points.product K.points).filter EdgeGood
  have cut_endpoint_mem :
      ∀ (s : Raw) (k : ℕ) (hk : k < (cutList s).length),
        AffineMap.lineMap s.1.1 s.1.2 ((cutList s)[k]'hk) ∈ K.points := by
    intro s k hk
    have hmemL : (cutList s)[k]'hk ∈ cutList s :=
      List.getElem_mem (l := cutList s) (n := k) hk
    rcases (cut_mem s ((cutList s)[k]'hk)).1 hmemL with h0 | h1 | hmid
    · rw [h0, AffineMap.lineMap_apply_zero]
      exact (K.segment_endpoints_listed s.1 s.2).1
    · rw [h1, AffineMap.lineMap_apply_one]
      exact (K.segment_endpoints_listed s.1 s.2).2
    · exact hmid.2.2
  have cut_edge_nondegenerate :
      ∀ (s : Raw) (k : ℕ) (hk : k + 1 < (cutList s).length),
        AffineMap.lineMap s.1.1 s.1.2
              ((cutList s)[k]'(Nat.lt_of_succ_lt hk)) ≠
          AffineMap.lineMap s.1.1 s.1.2 ((cutList s)[k + 1]'hk) := by
    intro s k hk heq
    have hparam_eq :
        (cutList s)[k]'(Nat.lt_of_succ_lt hk) = (cutList s)[k + 1]'hk :=
      (AffineMap.lineMap_injective ℝ (K.segment_nondegenerate s.1 s.2)) heq
    have hlt := cut_lt s k hk
    exact (ne_of_lt hlt) hparam_eq
  have cut_edge_segment_subset :
      ∀ (s : Raw) (e : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))
        (k : ℕ) (hk : k + 1 < (cutList s).length),
        e.1 =
            AffineMap.lineMap s.1.1 s.1.2
              ((cutList s)[k]'(Nat.lt_of_succ_lt hk)) →
        e.2 =
            AffineMap.lineMap s.1.1 s.1.2
              ((cutList s)[k + 1]'hk) →
        segment ℝ e.1 e.2 ⊆ segment ℝ s.1.1 s.1.2 := by
    intro s e k hk hsrc htgt
    have hleft_bounds :
        0 ≤ (cutList s)[k]'(Nat.lt_of_succ_lt hk) ∧
          (cutList s)[k]'(Nat.lt_of_succ_lt hk) ≤ 1 :=
      cut_bounds s ((cutList s)[k]'(Nat.lt_of_succ_lt hk))
        (List.getElem_mem (l := cutList s) (n := k) (Nat.lt_of_succ_lt hk))
    have hright_bounds :
        0 ≤ (cutList s)[k + 1]'hk ∧ (cutList s)[k + 1]'hk ≤ 1 :=
      cut_bounds s ((cutList s)[k + 1]'hk)
        (List.getElem_mem (l := cutList s) (n := k + 1) hk)
    have hleft_raw : e.1 ∈ segment ℝ s.1.1 s.1.2 := by
      rw [hsrc, segment_eq_image_lineMap]
      exact ⟨(cutList s)[k]'(Nat.lt_of_succ_lt hk), hleft_bounds, rfl⟩
    have hright_raw : e.2 ∈ segment ℝ s.1.1 s.1.2 := by
      rw [htgt, segment_eq_image_lineMap]
      exact ⟨(cutList s)[k + 1]'hk, hright_bounds, rfl⟩
    exact (convex_segment s.1.1 s.1.2).segment_subset hleft_raw hright_raw
  have edge_cut_witness :
      ∀ {e : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)},
        e ∈ edges →
          ∃ s : Raw, ∃ k, ∃ hk : k + 1 < (cutList s).length,
            e.1 =
                AffineMap.lineMap s.1.1 s.1.2
                  ((cutList s)[k]'(Nat.lt_of_succ_lt hk)) ∧
              e.2 =
                AffineMap.lineMap s.1.1 s.1.2
                  ((cutList s)[k + 1]'hk) := by
    intro e he
    rcases (Finset.mem_filter.mp he).2.2 with ⟨s, k, hk, hsrc, htgt⟩
    exact ⟨s, k, hk, hsrc, htgt⟩
  have edge_subset_raw_aux :
      ∀ e : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
        e ∈ edges →
          ∃ s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
            s ∈ K.segments ∧ segment ℝ e.1 e.2 ⊆ segment ℝ s.1 s.2 := by
    intro e he
    rcases edge_cut_witness he with ⟨s, k, hk, hsrc, htgt⟩
    exact ⟨s.1, s.2, cut_edge_segment_subset s e k hk hsrc htgt⟩
  have no_vertex_aux :
      ∀ e : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
        e ∈ edges →
          ∀ v : EuclideanSpace ℝ (Fin 2),
            v ∈ K.points → v ∉ openSegment ℝ e.1 e.2 := by
    intro e he v hv hvin
    rcases edge_cut_witness he with ⟨s, k, hk, hsrc, htgt⟩
    have hgap := cut_lt s k hk
    rcases
      open_subsegment_parameters s.1.1 s.1.2 hgap
        (x := v) (by simpa [hsrc, htgt] using hvin) with
      ⟨t, ht_left, ht_right, hv_eq⟩
    have hleft_bounds :
        0 ≤ (cutList s)[k]'(Nat.lt_of_succ_lt hk) ∧
          (cutList s)[k]'(Nat.lt_of_succ_lt hk) ≤ 1 :=
      cut_bounds s ((cutList s)[k]'(Nat.lt_of_succ_lt hk))
        (List.getElem_mem (l := cutList s) (n := k) (Nat.lt_of_succ_lt hk))
    have hright_bounds :
        0 ≤ (cutList s)[k + 1]'hk ∧ (cutList s)[k + 1]'hk ≤ 1 :=
      cut_bounds s ((cutList s)[k + 1]'hk)
        (List.getElem_mem (l := cutList s) (n := k + 1) hk)
    have ht0 : 0 ≤ t := by nlinarith
    have ht1 : t ≤ 1 := by nlinarith
    have htK : AffineMap.lineMap s.1.1 s.1.2 t ∈ K.points := by
      simpa [hv_eq] using hv
    exact cut_no_between s k hk t ht0 ht1 htK ⟨ht_left, ht_right⟩
  have cut_edge_mem_edges :
      ∀ (s : Raw) (k : ℕ) (hk : k + 1 < (cutList s).length),
        (AffineMap.lineMap s.1.1 s.1.2
            ((cutList s)[k]'(Nat.lt_of_succ_lt hk)),
          AffineMap.lineMap s.1.1 s.1.2
            ((cutList s)[k + 1]'hk)) ∈ edges := by
    intro s k hk
    change
      (AffineMap.lineMap s.1.1 s.1.2
            ((cutList s)[k]'(Nat.lt_of_succ_lt hk)),
          AffineMap.lineMap s.1.1 s.1.2
            ((cutList s)[k + 1]'hk)) ∈
        (K.points.product K.points).filter EdgeGood
    rw [Finset.mem_filter]
    constructor
    · exact Finset.mem_product.mpr
        ⟨cut_endpoint_mem s k (Nat.lt_of_succ_lt hk),
        cut_endpoint_mem s (k + 1) hk⟩
    · constructor
      · exact cut_edge_nondegenerate s k hk
      · exact ⟨s, k, hk, rfl, rfl⟩
  have raw_segment_covered :
      ∀ s : Raw, segment ℝ s.1.1 s.1.2 ⊆
        ⋃ e : {e // e ∈ edges}, segment ℝ e.1.1 e.1.2 := by
    intro s x hx
    rw [segment_eq_image_lineMap] at hx
    rcases hx with ⟨t, htIcc, rfl⟩
    rcases
      FiniteSortedRealCutListCoversUnitInterval (cutList s) (cut_sorted s)
        (cut_zero s) (cut_one s) (cut_bounds s) t htIcc with
      ⟨k, hk, htseg⟩
    let e : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) :=
      (AffineMap.lineMap s.1.1 s.1.2
          ((cutList s)[k]'(Nat.lt_of_succ_lt hk)),
        AffineMap.lineMap s.1.1 s.1.2
          ((cutList s)[k + 1]'hk))
    have he : e ∈ edges := cut_edge_mem_edges s k hk
    have hxedge : AffineMap.lineMap s.1.1 s.1.2 t ∈ segment ℝ e.1 e.2 := by
      change
        AffineMap.lineMap s.1.1 s.1.2 t ∈
          segment ℝ
            (AffineMap.lineMap s.1.1 s.1.2
              ((cutList s)[k]'(Nat.lt_of_succ_lt hk)))
            (AffineMap.lineMap s.1.1 s.1.2
              ((cutList s)[k + 1]'hk))
      rw [← image_segment ℝ (AffineMap.lineMap s.1.1 s.1.2)
        ((cutList s)[k]'(Nat.lt_of_succ_lt hk)) ((cutList s)[k + 1]'hk)]
      exact ⟨t, htseg, rfl⟩
    exact Set.mem_iUnion.mpr ⟨⟨e, he⟩, hxedge⟩
  refine ⟨{
    vertices := K.points
    edges := edges
    vertices_eq_points := rfl
    edge_source_mem := ?_
    edge_target_mem := ?_
    edge_nondegenerate := ?_
    edge_consecutive_cut := ?_
    edge_subset_raw := edge_subset_raw_aux
    no_vertex_in_edge_interior := no_vertex_aux
    edge_open_interiors_disjoint := ?_
    carrier_eq := ?_
  }⟩
  · intro e he
    exact (Finset.mem_product.mp (Finset.mem_filter.mp he).1).1
  · intro e he
    exact (Finset.mem_product.mp (Finset.mem_filter.mp he).1).2
  · intro e he
    exact (Finset.mem_filter.mp he).2.1
  · intro e he
    rcases edge_cut_witness he with ⟨s, k, hk, hsrc, htgt⟩
    exact
      ⟨s.1, s.2, cutList s, cut_nodup s, cut_sorted s, cut_mem s,
        cut_zero s, cut_one s, cut_bounds s, cut_lt s, cut_no_between s,
        k, hk, hsrc, htgt⟩
  · intro e f he hf hef
    rw [Set.disjoint_left]
    intro x hxe hxf
    rcases edge_cut_witness he with ⟨s, k, hk, hsrc, htgt⟩
    rcases edge_cut_witness hf with ⟨t, l, hl, hfsrc, hftgt⟩
    by_cases hraw : s.1 = t.1
    · have hst : s = t := Subtype.ext hraw
      subst t
      have hgap_e := cut_lt s k hk
      have hgap_f := cut_lt s l hl
      rcases
        open_subsegment_parameters s.1.1 s.1.2 hgap_e
          (x := x) (by simpa [hsrc, htgt] using hxe) with
        ⟨u, huk, huk_next, hx_u⟩
      rcases
        open_subsegment_parameters s.1.1 s.1.2 hgap_f
          (x := x) (by simpa [hfsrc, hftgt] using hxf) with
        ⟨v, hvl, hvl_next, hx_v⟩
      have huv : u = v := by
        apply AffineMap.lineMap_injective ℝ (K.segment_nondegenerate s.1 s.2)
        rw [← hx_u, ← hx_v]
      subst v
      have hnot_kl : ¬ k < l := by
        intro hkl
        have hle : (cutList s)[k + 1]'hk ≤
            (cutList s)[l]'(Nat.lt_of_succ_lt hl) := by
          have hk1_le_l : k + 1 ≤ l := by omega
          by_cases heq : k + 1 = l
          · subst l
            rfl
          · have hlt_index :
                (⟨k + 1, hk⟩ : Fin (cutList s).length) <
                  ⟨l, Nat.lt_of_succ_lt hl⟩ := by
              exact Fin.mk_lt_mk.mpr (by omega)
            exact ((cut_sorted s) hlt_index).le
        nlinarith
      have hnot_lk : ¬ l < k := by
        intro hlk
        have hle : (cutList s)[l + 1]'hl ≤
            (cutList s)[k]'(Nat.lt_of_succ_lt hk) := by
          have hl1_le_k : l + 1 ≤ k := by omega
          by_cases heq : l + 1 = k
          · subst k
            rfl
          · have hlt_index :
                (⟨l + 1, hl⟩ : Fin (cutList s).length) <
                  ⟨k, Nat.lt_of_succ_lt hk⟩ := by
              exact Fin.mk_lt_mk.mpr (by omega)
            exact ((cut_sorted s) hlt_index).le
        nlinarith
      have hkl : k = l := by omega
      subst l
      exact hef (Prod.ext (by rw [hsrc, hfsrc]) (by rw [htgt, hftgt]))
    · have hx_raw_s : x ∈ segment ℝ s.1.1 s.1.2 :=
        cut_edge_segment_subset s e k hk hsrc htgt
          (openSegment_subset_segment ℝ e.1 e.2 hxe)
      have hx_raw_t : x ∈ segment ℝ t.1.1 t.1.2 :=
        cut_edge_segment_subset t f l hl hfsrc hftgt
          (openSegment_subset_segment ℝ f.1 f.2 hxf)
      have hx_point : x ∈ K.points :=
        K.segment_intersections_listed s.1 t.1 s.2 t.2 hraw x hx_raw_s hx_raw_t
      exact no_vertex_aux e he x hx_point hxe
  · rw [K.carrier_eq]
    ext x
    constructor
    · intro hx
      rcases hx with hxpt | hxseg
      · exact Or.inl hxpt
      · rcases Set.mem_iUnion.mp hxseg with ⟨s, hxs⟩
        exact Or.inr (raw_segment_covered s hxs)
    · intro hx
      rcases hx with hxpt | hxedge
      · exact Or.inl hxpt
      · rcases Set.mem_iUnion.mp hxedge with ⟨e, hxe⟩
        rcases edge_subset_raw_aux e.1 e.2 with ⟨s, hs, hsub⟩
        exact Or.inr (Set.mem_iUnion.mpr ⟨⟨s, hs⟩, hsub hxe⟩)
