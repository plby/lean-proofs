import ErdosProblems.Erdos733.ST.JordanLocalSideData
import ErdosProblems.Erdos733.ST.ComplementComponent
import ErdosProblems.Erdos733.ST.SimpleClosedPolygonalCurveComplementOpen

open Classical
noncomputable section

-- [TABLET NODE: JordanComponentFrontiers]
lemma JordanComponentFrontiers
    (J : SimpleClosedPolygonalCurve) (S : JordanLocalSideData J)
    (inside outside : Set (EuclideanSpace ℝ (Fin 2))) :
    ComplementComponent J.carrier inside →
      ComplementComponent J.carrier outside →
        inside ≠ outside →
          ((S.leftRegion ⊆ inside ∧ S.rightRegion ⊆ outside) ∨
            (S.leftRegion ⊆ outside ∧ S.rightRegion ⊆ inside)) →
            (∀ p : EuclideanSpace ℝ (Fin 2),
              p ∈ J.carrierᶜ → p ∈ inside ∨ p ∈ outside) →
              frontier inside = J.carrier ∧ frontier outside = J.carrier := by
-- BODY
  rintro ⟨hinside_ne, hinside_sub, hinside_conn, hinside_max⟩
    ⟨houtside_ne, houtside_sub, houtside_conn, houtside_max⟩
    hne horient hcover
  have hdisjoint : Disjoint inside outside := by
    rw [Set.disjoint_left]
    intro x hxinside hxoutside
    have hinter : (inside ∩ outside).Nonempty := ⟨x, hxinside, hxoutside⟩
    have hunion_ne : (inside ∪ outside).Nonempty :=
      hinside_ne.mono Set.subset_union_left
    have hunion_sub : inside ∪ outside ⊆ J.carrierᶜ :=
      Set.union_subset hinside_sub houtside_sub
    have hunion_conn : IsConnected (inside ∪ outside) :=
      IsConnected.union hinter hinside_conn houtside_conn
    have hunion_inside : inside ∪ outside ⊆ inside :=
      hinside_max (inside ∪ outside) hunion_ne hunion_sub hunion_conn Set.subset_union_left
    have hunion_outside : inside ∪ outside ⊆ outside :=
      houtside_max (inside ∪ outside) hunion_ne hunion_sub hunion_conn Set.subset_union_right
    apply hne
    apply Set.Subset.antisymm
    · intro y hy
      exact hunion_outside (Set.mem_union_left outside hy)
    · intro y hy
      exact hunion_inside (Set.mem_union_right inside hy)
  have hcarrier_closures :
      J.carrier ⊆ closure inside ∧ J.carrier ⊆ closure outside := by
    rcases horient with hleft_right | hright_left
    · constructor
      · intro x hx
        exact closure_mono hleft_right.1 (S.carrier_subset_left_closure hx)
      · intro x hx
        exact closure_mono hleft_right.2 (S.carrier_subset_right_closure hx)
    · constructor
      · intro x hx
        exact closure_mono hright_left.2 (S.carrier_subset_right_closure hx)
      · intro x hx
        exact closure_mono hright_left.1 (S.carrier_subset_left_closure hx)
  have hcarrier_frontiers : ∀ x ∈ J.carrier,
      x ∈ frontier inside ∧ x ∈ frontier outside := by
    intro x hx
    rw [frontier_eq_closure_inter_closure, frontier_eq_closure_inter_closure]
    constructor
    · exact
        ⟨hcarrier_closures.1 hx,
          subset_closure (fun hxinside => hinside_sub hxinside hx)⟩
    · exact
        ⟨hcarrier_closures.2 hx,
          subset_closure (fun hxoutside => houtside_sub hxoutside hx)⟩
  have hoff_frontiers : ∀ p ∈ J.carrierᶜ,
      p ∉ frontier inside ∧ p ∉ frontier outside := by
    intro p hp
    rcases Metric.isOpen_iff.mp (SimpleClosedPolygonalCurveComplementOpen J) p hp with
      ⟨ε, hε, hball_compl⟩
    have hpball : p ∈ Metric.ball p ε := Metric.mem_ball_self hε
    rcases hcover p hp with hpinside | hpoutside
    · have hinter : (inside ∩ Metric.ball p ε).Nonempty :=
        ⟨p, hpinside, hpball⟩
      have hunion_ne : (inside ∪ Metric.ball p ε).Nonempty :=
        hinside_ne.mono Set.subset_union_left
      have hunion_sub : inside ∪ Metric.ball p ε ⊆ J.carrierᶜ :=
        Set.union_subset hinside_sub hball_compl
      have hunion_conn : IsConnected (inside ∪ Metric.ball p ε) :=
        IsConnected.union hinter hinside_conn
          ⟨⟨p, hpball⟩, (convex_ball p ε).isPreconnected⟩
      have hball_inside : Metric.ball p ε ⊆ inside := by
        intro y hy
        exact hinside_max (inside ∪ Metric.ball p ε) hunion_ne hunion_sub hunion_conn
          Set.subset_union_left (Set.mem_union_right inside hy)
      have hp_inside_interior : p ∈ interior inside :=
        interior_maximal hball_inside Metric.isOpen_ball hpball
      have hball_outside_compl : Metric.ball p ε ⊆ outsideᶜ := by
        intro y hy hyo
        exact Set.disjoint_left.mp hdisjoint (hball_inside hy) hyo
      have hp_outside_compl_interior : p ∈ interior outsideᶜ :=
        interior_maximal hball_outside_compl Metric.isOpen_ball hpball
      constructor
      · rw [frontier_eq_inter_compl_interior]
        intro hpf
        exact hpf.1 hp_inside_interior
      · rw [frontier_eq_inter_compl_interior]
        intro hpf
        exact hpf.2 hp_outside_compl_interior
    · have hinter : (outside ∩ Metric.ball p ε).Nonempty :=
        ⟨p, hpoutside, hpball⟩
      have hunion_ne : (outside ∪ Metric.ball p ε).Nonempty :=
        houtside_ne.mono Set.subset_union_left
      have hunion_sub : outside ∪ Metric.ball p ε ⊆ J.carrierᶜ :=
        Set.union_subset houtside_sub hball_compl
      have hunion_conn : IsConnected (outside ∪ Metric.ball p ε) :=
        IsConnected.union hinter houtside_conn
          ⟨⟨p, hpball⟩, (convex_ball p ε).isPreconnected⟩
      have hball_outside : Metric.ball p ε ⊆ outside := by
        intro y hy
        exact houtside_max (outside ∪ Metric.ball p ε) hunion_ne hunion_sub hunion_conn
          Set.subset_union_left (Set.mem_union_right outside hy)
      have hp_outside_interior : p ∈ interior outside :=
        interior_maximal hball_outside Metric.isOpen_ball hpball
      have hball_inside_compl : Metric.ball p ε ⊆ insideᶜ := by
        intro y hy hyi
        exact Set.disjoint_left.mp hdisjoint hyi (hball_outside hy)
      have hp_inside_compl_interior : p ∈ interior insideᶜ :=
        interior_maximal hball_inside_compl Metric.isOpen_ball hpball
      constructor
      · rw [frontier_eq_inter_compl_interior]
        intro hpf
        exact hpf.2 hp_inside_compl_interior
      · rw [frontier_eq_inter_compl_interior]
        intro hpf
        exact hpf.1 hp_outside_interior
  constructor
  · ext x
    constructor
    · intro hx
      by_contra hxcarrier
      exact (hoff_frontiers x hxcarrier).1 hx
    · intro hx
      exact (hcarrier_frontiers x hx).1
  · ext x
    constructor
    · intro hx
      by_contra hxcarrier
      exact (hoff_frontiers x hxcarrier).2 hx
    · intro hx
      exact (hcarrier_frontiers x hx).2
