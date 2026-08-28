import ErdosProblems.Erdos577.EdgeChanges
import ErdosProblems.Erdos577.QuadSets
import ErdosProblems.Erdos577.LocalFactors

/-! The almost-complete seven-vertex cores used in Wang's preliminary lemmas. -/

namespace Erdos577

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableEq V] in
lemma edgeCount_clique {s : Finset V} (hs : G.IsClique s) :
    edgeCount G s = s.card.choose 2 := by
  classical
  calc
    edgeCount G s = Nat.card (G.induce (s : Set V)).edgeSet := by
      rw [edgeCount, Nat.card_eq_fintype_card, SimpleGraph.edgeFinset_card]
    _ = Nat.card (⊤ : SimpleGraph (s : Set V)).edgeSet :=
      congrArg (fun H : SimpleGraph (s : Set V) ↦ Nat.card H.edgeSet) (G.induce_eq_top.mpr hs)
    _ = s.card.choose 2 := by
      rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card,
        SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
      change (Fintype.card s).choose 2 = s.card.choose 2
      rw [Fintype.card_coe]

/-- A graph whose edge count is at most one below complete becomes complete
after adding one missing edge, unless it was already complete. -/
lemma eq_top_or_add_edge_eq_top [Fintype V]
    (hgap : (⊤ : SimpleGraph V).edgeFinset.card ≤ G.edgeFinset.card + 1) :
    G = ⊤ ∨ ∃ u v : V, u ≠ v ∧ ¬G.Adj u v ∧ G ⊔ SimpleGraph.edge u v = ⊤ := by
  classical
  by_cases hG : G = ⊤
  · exact Or.inl hG
  · obtain ⟨u, v, huv, hnot⟩ := exists_nonedge hG
    refine Or.inr ⟨u, v, huv, hnot, ?_⟩
    by_contra hJ
    have h₁ := card_lt_card ((SimpleGraph.edgeFinset_ssubset_edgeFinset).mpr
      (G.lt_sup_edge u v huv hnot))
    have hlt : G ⊔ SimpleGraph.edge u v < ⊤ := lt_top_iff_ne_top.mpr hJ
    have h₂ := card_lt_card ((SimpleGraph.edgeFinset_ssubset_edgeFinset).mpr hlt)
    omega

lemma dense_triangle_clique_edges {t q : Finset V}
    (ht : G.IsNClique 3 t) (hq : G.IsNClique 4 q) (hd : Disjoint t q)
    (hc : 11 ≤ contacts G t q) : 20 ≤ edgeCount G (t ∪ q) ∧ (t ∪ q).card = 7 := by
  constructor
  · rw [edgeCount_union G hd, edgeCount_clique ht.isClique, edgeCount_clique hq.isClique,
      ht.card_eq, hq.card_eq]
    norm_num only [Nat.choose]
    omega
  · rw [card_union_of_disjoint hd, ht.card_eq, hq.card_eq]

omit [DecidableRel G.Adj] in
lemma QuadOn.of_clique {s : Finset V} (hs : s.card = 4) (hc : G.IsClique s) : QuadOn G s := by
  classical
  apply QuadOn.of_degreeIn hs
  intro v hv
  rw [degreeIn_clique G hc hv, hs]
  decide

omit [DecidableRel G.Adj] in
lemma clique_erase_of_add_edge {s : Finset V} {a b : V}
    (h : (G ⊔ SimpleGraph.edge a b).IsClique s) : G.IsClique (s.erase a) := by
  simpa only [coe_erase] using h.sdiff_of_sup_edge

omit [DecidableEq V] [DecidableRel G.Adj] in
lemma adj_of_add_edge_of_avoids_endpoints {a b x y : V}
    (h : (G ⊔ SimpleGraph.edge a b).Adj x y) (hxa : x ≠ a) (hxb : x ≠ b) : G.Adj x y := by
  rcases (SimpleGraph.sup_adj _ _ _ _).mp h with h | h
  · exact h
  · rcases ((SimpleGraph.edge_adj _ _ _ _).mp h).1 with h | h
    · exact False.elim (hxa h.1)
    · exact False.elim (hxb h.1)

omit [DecidableRel G.Adj] in
lemma clique_sdiff_of_add_edge {s t : Finset V} {a b : V}
    (h : (G ⊔ SimpleGraph.edge a b).IsClique s) (ha : a ∈ t) :
    G.IsClique (s \ t : Finset V) := by
  have hsub : s \ t ⊆ s.erase a := by
    rw [← sdiff_singleton_eq_erase]
    exact sdiff_subset_sdiff subset_rfl (singleton_subset_iff.mpr ha)
  exact SimpleGraph.IsClique.subset (coe_subset.mpr hsub) (clique_erase_of_add_edge h)

omit [DecidableRel G.Adj] in
/-- A common neighbor can be chosen to remove an endpoint of the only
possible missing edge. A five-vertex pool also covers the source's second construction. -/
lemma near_clique_path {s pool : Finset V} {a b p q : V}
    (h : (G ⊔ SimpleGraph.edge a b).IsClique s) (hpool : pool ⊆ s)
    (hsize : 5 ≤ pool.card) (ha : a ∈ pool) (hab : a ≠ b) (hp : p ∈ pool) (hq : q ∈ pool) :
    ∃ r ∈ pool, r ≠ p ∧ r ≠ q ∧ G.Adj p r ∧ G.Adj r q ∧
      G.IsClique (s \ {p, q, r} : Finset V) := by
  have hswap : (G ⊔ SimpleGraph.edge b a).IsClique s := by
    simpa only [SimpleGraph.edge_comm a b] using h
  by_cases hend : a ∈ ({p, q} : Finset V) ∨ b ∈ ({p, q} : Finset V)
  · have hlt : ({p, q, a, b} : Finset V).card < pool.card :=
      lt_of_le_of_lt card_le_four (by omega)
    obtain ⟨r, hr, havoid⟩ := exists_mem_notMem_of_card_lt_card hlt
    simp only [mem_insert, mem_singleton, not_or] at havoid
    have erp := adj_of_add_edge_of_avoids_endpoints
      (h (hpool hr) (hpool hp) havoid.1) havoid.2.2.1 havoid.2.2.2
    have erq := adj_of_add_edge_of_avoids_endpoints
      (h (hpool hr) (hpool hq) havoid.2.1) havoid.2.2.1 havoid.2.2.2
    refine ⟨r, hr, havoid.1, havoid.2.1, erp.symm, erq, ?_⟩
    rcases hend with hend | hend
    · apply clique_sdiff_of_add_edge (t := {p, q, r}) h
      simp only [mem_insert, mem_singleton] at hend ⊢
      tauto
    · apply clique_sdiff_of_add_edge (t := {p, q, r}) hswap
      simp only [mem_insert, mem_singleton] at hend ⊢
      tauto
  · simp only [mem_insert, mem_singleton, not_or] at hend
    have hbcl := clique_erase_of_add_edge hswap
    have hpa : p ≠ a := Ne.symm hend.1.1
    have haq : a ≠ q := hend.1.2
    have ep := hbcl (mem_erase.mpr ⟨Ne.symm hend.2.1, hpool hp⟩)
      (mem_erase.mpr ⟨hab, hpool ha⟩) hpa
    have eq := hbcl (mem_erase.mpr ⟨hab, hpool ha⟩)
      (mem_erase.mpr ⟨Ne.symm hend.2.2, hpool hq⟩) haq
    exact ⟨a, ha, hend.1.1, haq, ep, eq,
      clique_sdiff_of_add_edge (t := {p, q, a}) h (by simp)⟩

/-- A vertex with two neighbors in a seven-vertex near clique gives two
disjoint quadrilaterals; the second one is a complete four-set. -/
lemma local_factor_of_near_clique {s : Finset V} {a b z : V} (hs : s.card = 7)
    (h : (G ⊔ SimpleGraph.edge a b).IsClique s) (ha : a ∈ s) (hab : a ≠ b)
    (hz : z ∉ s) (hd : 2 ≤ degreeIn G z s) : LocalFactor G (insert z s) := by
  have hn : 1 < (s.filter (G.Adj z)).card := hd
  obtain ⟨p, hp, q, hq, hpq⟩ := one_lt_card.mp hn
  obtain ⟨hps, ezp⟩ := mem_filter.mp hp
  obtain ⟨hqs, ezq⟩ := mem_filter.mp hq
  obtain ⟨r, hr, hrp, hrq, epr, erq, hcl⟩ :=
    near_clique_path h subset_rfl (by omega) ha hab hps hqs
  have hzr : z ≠ r := fun he ↦ hz (he.symm ▸ hr)
  have hquad : QuadOn G {z, p, r, q} := QuadOn.of_vertices hzr hpq ezp epr erq ezq.symm
  have hsub : ({z, p, r, q} : Finset V) ⊆ insert z s := by
    simp [insert_subset_iff, hps, hqs, hr]
  have hsub' : ({p, q, r} : Finset V) ⊆ s := by
    simp [insert_subset_iff, hps, hqs, hr]
  have hc3 : ({p, q, r} : Finset V).card = 3 := by
    simp [hpq, Ne.symm hrp, Ne.symm hrq]
  have hc : (s \ {p, q, r}).card = 4 := by
    rw [card_sdiff_of_subset hsub', hs, hc3]
  have he : insert z s \ {z, p, r, q} = s \ {p, q, r} := by
    ext v
    by_cases hv : v = z
    · subst v
      simp [hz]
    · simp only [mem_sdiff, mem_insert, mem_singleton, hv, false_or]
      tauto
  refine ⟨{z, p, r, q}, hsub, hquad, ?_⟩
  rw [he]
  exact QuadOn.of_clique hc hcl

omit [DecidableEq V] in
lemma clique_or_one_missing_edge {s : Finset V} (hs : s.card = 7)
    (he : 20 ≤ edgeCount G s) :
    G.IsClique s ∨ ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ¬G.Adj a b ∧
      (G ⊔ SimpleGraph.edge a b).IsClique s := by
  classical
  have hsize : Fintype.card (s : Set V) = 7 := by
    change Fintype.card s = 7
    rw [Fintype.card_coe, hs]
  have hgap : (⊤ : SimpleGraph (s : Set V)).edgeFinset.card ≤
      (G.induce (s : Set V)).edgeFinset.card + 1 := by
    rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two, hsize]
    change 21 ≤ edgeCount G s + 1
    omega
  rcases eq_top_or_add_edge_eq_top (G := G.induce (s : Set V)) hgap with htop | hmissing
  · exact Or.inl (G.induce_eq_top.mp htop)
  · obtain ⟨a, b, hab, hn, htop⟩ := hmissing
    have habV : (a : V) ≠ (b : V) := fun he ↦ hab (Subtype.ext he)
    refine Or.inr ⟨a, a.property, b, b.property, habV, hn, ?_⟩
    intro x hx y hy hxy
    have hxy' : (⟨x, hx⟩ : (s : Set V)) ≠ ⟨y, hy⟩ :=
      fun he ↦ hxy (congrArg Subtype.val he)
    have hadj : (G.induce (s : Set V) ⊔ SimpleGraph.edge a b).Adj ⟨x, hx⟩ ⟨y, hy⟩ := by
      rw [htop]
      exact (SimpleGraph.top_adj _ _).mpr hxy'
    apply (SimpleGraph.sup_adj _ _ _ _).mpr
    rcases (SimpleGraph.sup_adj _ _ _ _).mp hadj with hadj | hadj
    · exact Or.inl hadj
    · right
      refine (SimpleGraph.edge_adj _ _ _ _).mpr ⟨?_, hxy⟩
      rcases ((SimpleGraph.edge_adj _ _ _ _).mp hadj).1 with ⟨he₁, he₂⟩ | ⟨he₁, he₂⟩
      · exact Or.inl ⟨congrArg Subtype.val he₁, congrArg Subtype.val he₂⟩
      · exact Or.inr ⟨congrArg Subtype.val he₁, congrArg Subtype.val he₂⟩

lemma local_factor_of_seven_dense {s : Finset V} {z : V} (hs : s.card = 7)
    (he : 20 ≤ edgeCount G s) (hz : z ∉ s) (hd : 2 ≤ degreeIn G z s) :
    LocalFactor G (insert z s) := by
  rcases clique_or_one_missing_edge hs he with hcl | hmissing
  · obtain ⟨a, ha, b, _, hab⟩ := one_lt_card.mp (by omega : 1 < s.card)
    exact local_factor_of_near_clique hs
      (SimpleGraph.IsClique.mono (le_sup_left : G ≤ G ⊔ SimpleGraph.edge a b) hcl) ha hab hz hd
  · obtain ⟨a, ha, b, _, hab, _, hcl⟩ := hmissing
    exact local_factor_of_near_clique hs hcl ha hab hz hd

/-- Wang 3.1(1): a dense triangle--clique core plus two outside contacts
has a factor by quadrilaterals of exactly four vertices. -/
theorem dense_triangle_clique_factor {t q : Finset V} {z : V}
    (ht : G.IsNClique 3 t) (hq : G.IsNClique 4 q) (hd : Disjoint t q)
    (hc : 11 ≤ contacts G t q) (hz : z ∉ t ∪ q) (hz2 : 2 ≤ degreeIn G z (t ∪ q)) :
    LocalFactor G (insert z (t ∪ q)) := by
  obtain ⟨he, hs⟩ := dense_triangle_clique_edges ht hq hd hc
  exact local_factor_of_seven_dense hs he hz hz2

lemma dense_join_clique_or_cross_gap {t q : Finset V}
    (ht : G.IsNClique 3 t) (hq : G.IsNClique 4 q) (hd : Disjoint t q)
    (hc : 11 ≤ contacts G t q) :
    G.IsClique (t ∪ q : Finset V) ∨ ∃ a ∈ t, ∃ b ∈ q, a ≠ b ∧ ¬G.Adj a b ∧
      (G ⊔ SimpleGraph.edge a b).IsClique (t ∪ q : Finset V) := by
  obtain ⟨he, hs⟩ := dense_triangle_clique_edges ht hq hd hc
  rcases clique_or_one_missing_edge hs he with hcl | hmissing
  · exact Or.inl hcl
  · obtain ⟨a, ha, b, hb, hab, hn, hcl⟩ := hmissing
    rcases mem_union.mp ha with ha | ha <;> rcases mem_union.mp hb with hb | hb
    · exact False.elim (hn (ht.isClique ha hb hab))
    · exact Or.inr ⟨a, ha, b, hb, hab, hn, hcl⟩
    · refine Or.inr ⟨b, hb, a, ha, hab.symm, fun h ↦ hn h.symm, ?_⟩
      simpa only [SimpleGraph.edge_comm a b] using hcl
    · exact False.elim (hn (hq.isClique ha hb hab))

omit [DecidableRel G.Adj] in
lemma near_clique_triangle {s pool : Finset V} {a b u v : V}
    (h : (G ⊔ SimpleGraph.edge a b).IsClique s) (hpool : pool ⊆ s)
    (hsize : 5 ≤ pool.card) (ha : a ∈ pool) (hab : a ≠ b)
    (hu : u ∈ pool) (hv : v ∈ pool) (huv : G.Adj u v) :
    ∃ c ⊆ pool, G.IsNClique 3 c ∧ u ∈ c ∧ v ∈ c ∧ G.IsClique (s \ c : Finset V) := by
  obtain ⟨r, hr, _, _, eur, erv, hcl⟩ := near_clique_path h hpool hsize ha hab hu hv
  refine ⟨{u, v, r}, ?_, SimpleGraph.is3Clique_triple_iff.mpr ⟨huv, eur, erv.symm⟩,
    by simp, by simp, hcl⟩
  simp [insert_subset_iff, hu, hv, hr]

omit [DecidableRel G.Adj] in
lemma near_clique_triangle_through_endpoint {s z : Finset V} {a b : V}
    (h : (G ⊔ SimpleGraph.edge a b).IsClique s) (hz : z ⊆ s)
    (hsize : 4 ≤ z.card) (ha : a ∈ z) (hab : a ≠ b) :
    ∃ c ⊆ z, G.IsNClique 3 c ∧ G.IsClique (s \ c : Finset V) := by
  have hbound : z.card ≤ (z \ {a, b}).card + ({a, b} : Finset V).card :=
    card_le_card_sdiff_add_card
  have hp : ({a, b} : Finset V).card ≤ 2 := card_le_two
  obtain ⟨u, hu, v, hv, huv⟩ := one_lt_card.mp (by omega : 1 < (z \ {a, b}).card)
  obtain ⟨huz, hun⟩ := mem_sdiff.mp hu
  obtain ⟨hvz, hvn⟩ := mem_sdiff.mp hv
  simp only [mem_insert, mem_singleton, not_or] at hun hvn
  have hswap : (G ⊔ SimpleGraph.edge b a).IsClique s := by
    simpa only [SimpleGraph.edge_comm a b] using h
  have hsub : ({a, u, v} : Finset V) ⊆ s.erase b := by
    simp only [insert_subset_iff, singleton_subset_iff]
    exact ⟨mem_erase.mpr ⟨hab, hz ha⟩, mem_erase.mpr ⟨hun.2, hz huz⟩,
      mem_erase.mpr ⟨hvn.2, hz hvz⟩⟩
  have hcl : G.IsClique ({a, u, v} : Finset V) :=
    SimpleGraph.IsClique.subset (coe_subset.mpr hsub) (clique_erase_of_add_edge hswap)
  have hc3 : ({a, u, v} : Finset V).card = 3 := by
    simp [Ne.symm hun.1, Ne.symm hvn.1, huv]
  refine ⟨{a, u, v}, ?_, ⟨hcl, hc3⟩, clique_sdiff_of_add_edge (t := {a, u, v}) h (by simp)⟩
  simp [insert_subset_iff, ha, huz, hvz]

/-- Wang 3.1(2): retain any specified edge in the five-vertex pool while
leaving a complete four-vertex complement in the seven-vertex core. -/
theorem dense_triangle_edge_extension {t q : Finset V} {x₁ x₂ u v : V}
    (ht : G.IsNClique 3 t) (hq : G.IsNClique 4 q) (hd : Disjoint t q)
    (hc : 11 ≤ contacts G t q) (h₁ : x₁ ∈ t) (h₂ : x₂ ∈ t) (h12 : x₁ ≠ x₂)
    (hu : u ∈ (t ∪ q) \ {x₁, x₂}) (hv : v ∈ (t ∪ q) \ {x₁, x₂}) (huv : G.Adj u v) :
    ∃ c ⊆ (t ∪ q) \ {x₁, x₂}, G.IsNClique 3 c ∧ u ∈ c ∧ v ∈ c ∧
      G.IsClique ((t ∪ q) \ c : Finset V) := by
  let pool : Finset V := (t ∪ q) \ {x₁, x₂}
  have hsub : ({x₁, x₂} : Finset V) ⊆ t ∪ q := by simp [insert_subset_iff, h₁, h₂]
  have hsize : pool.card = 5 := by
    dsimp only [pool]
    rw [card_sdiff_of_subset hsub, card_union_of_disjoint hd, ht.card_eq, hq.card_eq]
    simp [h12]
  have hpool : pool ⊆ t ∪ q := sdiff_subset
  have hqpool : q ⊆ pool := by
    intro z hz
    refine mem_sdiff.mpr ⟨mem_union_right _ hz, ?_⟩
    intro hzpair
    rcases mem_insert.mp hzpair with rfl | hzpair
    · exact (disjoint_left.mp hd) h₁ hz
    · have he : z = x₂ := mem_singleton.mp hzpair
      subst z
      exact (disjoint_left.mp hd) h₂ hz
  rcases dense_join_clique_or_cross_gap ht hq hd hc with hcl | hmissing
  · obtain ⟨a, ha, b, _, hab⟩ := one_lt_card.mp (by omega : 1 < pool.card)
    exact near_clique_triangle
      (SimpleGraph.IsClique.mono (le_sup_left : G ≤ G ⊔ SimpleGraph.edge a b) hcl)
      hpool hsize.ge ha hab hu hv huv
  · obtain ⟨a, _, b, hb, hab, _, hcl⟩ := hmissing
    have hswap : (G ⊔ SimpleGraph.edge b a).IsClique (t ∪ q : Finset V) := by
      simpa only [SimpleGraph.edge_comm a b] using hcl
    exact near_clique_triangle hswap hpool hsize.ge (hqpool hb) hab.symm hu hv huv

/-- Wang 3.1(4): if two triangle rows are full, every four-set in the
remaining five vertices contains a triangle with a complete complement. -/
theorem dense_triangle_four_subset {t q z : Finset V} {x₁ x₂ : V}
    (ht : G.IsNClique 3 t) (hq : G.IsNClique 4 q) (hd : Disjoint t q)
    (hc : 11 ≤ contacts G t q) (h₁ : x₁ ∈ t) (h₂ : x₂ ∈ t) (h12 : x₁ ≠ x₂)
    (hfull₁ : ∀ w ∈ q, G.Adj x₁ w) (hfull₂ : ∀ w ∈ q, G.Adj x₂ w)
    (hz : z ⊆ (t ∪ q) \ {x₁, x₂}) (hz4 : z.card = 4) :
    ∃ c ⊆ z, G.IsNClique 3 c ∧ G.IsClique ((t ∪ q) \ c : Finset V) := by
  let pool : Finset V := (t ∪ q) \ {x₁, x₂}
  have hsub : ({x₁, x₂} : Finset V) ⊆ t ∪ q := by simp [insert_subset_iff, h₁, h₂]
  have hsize : pool.card = 5 := by
    dsimp only [pool]
    rw [card_sdiff_of_subset hsub, card_union_of_disjoint hd, ht.card_eq, hq.card_eq]
    simp [h12]
  have hzcore : z ⊆ t ∪ q := hz.trans sdiff_subset
  rcases dense_join_clique_or_cross_gap ht hq hd hc with hcl | hmissing
  · obtain ⟨c, hcz, hc3⟩ := exists_subset_card_eq (by omega : 3 ≤ z.card)
    exact ⟨c, hcz, ⟨SimpleGraph.IsClique.subset (coe_subset.mpr (hcz.trans hzcore)) hcl, hc3⟩,
      SimpleGraph.IsClique.subset (coe_subset.mpr (sdiff_subset : (t ∪ q) \ c ⊆ t ∪ q)) hcl⟩
  · obtain ⟨a, ha, b, hb, hab, hn, hcl⟩ := hmissing
    have ha1 : a ≠ x₁ := by
      intro he
      subst a
      exact hn (hfull₁ b hb)
    have ha2 : a ≠ x₂ := by
      intro he
      subst a
      exact hn (hfull₂ b hb)
    have hap : a ∈ pool := mem_sdiff.mpr ⟨mem_union_left _ ha, by simp [ha1, ha2]⟩
    have hbp : b ∈ pool := by
      refine mem_sdiff.mpr ⟨mem_union_right _ hb, ?_⟩
      intro hbp
      rcases mem_insert.mp hbp with rfl | hbp
      · exact (disjoint_left.mp hd) h₁ hb
      · have he : b = x₂ := mem_singleton.mp hbp
        subst b
        exact (disjoint_left.mp hd) h₂ hb
    have hpairs : ({a, b} : Finset V) ⊆ pool := by simp [insert_subset_iff, hap, hbp]
    have hend : a ∈ z ∨ b ∈ z := by
      by_contra hh
      have haz : a ∉ z := fun h ↦ hh (Or.inl h)
      have hbz : b ∉ z := fun h ↦ hh (Or.inr h)
      have hsmall : z ⊆ pool \ {a, b} := by
        intro v hv
        refine mem_sdiff.mpr ⟨hz hv, ?_⟩
        intro hp
        rcases mem_insert.mp hp with rfl | hp
        · exact haz hv
        · have he : v = b := mem_singleton.mp hp
          subst v
          exact hbz hv
      have hle := card_le_card hsmall
      rw [hz4, card_sdiff_of_subset hpairs, hsize] at hle
      simp [hab] at hle
    rcases hend with haz | hbz
    · exact near_clique_triangle_through_endpoint hcl hzcore hz4.ge haz hab
    · have hswap : (G ⊔ SimpleGraph.edge b a).IsClique (t ∪ q : Finset V) := by
        simpa only [SimpleGraph.edge_comm a b] using hcl
      exact near_clique_triangle_through_endpoint hswap hzcore hz4.ge hbz hab.symm

/-- Wang 3.1(3): label the four-clique relative to any specified vertex
of the triangle. The two complete sets use the other two triangle vertices. -/
theorem dense_triangle_clique_label {t q : Finset V} {x : V}
    (ht : G.IsNClique 3 t) (hq : G.IsNClique 4 q) (hd : Disjoint t q)
    (hc : 11 ≤ contacts G t q) (hx : x ∈ t) :
    ∃ b₁ b₂ b₃ b₄, q = {b₁, b₂, b₃, b₄} ∧
      G.Adj x b₁ ∧ G.Adj x b₂ ∧ G.Adj x b₃ ∧
      G.IsClique (t.erase x ∪ {b₄, b₂} : Finset V) ∧
      G.IsClique (t.erase x ∪ {b₄, b₃} : Finset V) := by
  have hcompletion : ∃ a ∈ t, ∃ b ∈ q, a ≠ b ∧
      (G ⊔ SimpleGraph.edge a b).IsClique (t ∪ q : Finset V) := by
    rcases dense_join_clique_or_cross_gap ht hq hd hc with hcl | hmissing
    · obtain ⟨b, hb⟩ := card_pos.mp (by rw [hq.card_eq]; decide : 0 < q.card)
      refine ⟨x, hx, b, hb, ?_, SimpleGraph.IsClique.mono le_sup_left hcl⟩
      intro he
      exact (disjoint_left.mp hd) hx (he.symm ▸ hb)
    · obtain ⟨a, ha, b, hb, hab, _, hcl⟩ := hmissing
      exact ⟨a, ha, b, hb, hab, hcl⟩
  obtain ⟨a, ha, b, hb, _, hcl⟩ := hcompletion
  have hc3 : (q.erase b).card = 3 := by rw [card_erase_of_mem hb, hq.card_eq]
  obtain ⟨u, v, w, _, _, _, henum⟩ := card_eq_three.mp hc3
  have hu : u ∈ q.erase b := by rw [henum]; simp
  have hv : v ∈ q.erase b := by rw [henum]; simp
  have hw : w ∈ q.erase b := by rw [henum]; simp
  have hqenum : q = {b, u, v, w} := by
    rw [← insert_erase hb, henum]
  have hxb : x ≠ b := fun he ↦ (disjoint_left.mp hd) hx (he.symm ▸ hb)
  have hswap : (G ⊔ SimpleGraph.edge b a).IsClique (t ∪ q : Finset V) := by
    simpa only [SimpleGraph.edge_comm a b] using hcl
  have hwithoutb := clique_erase_of_add_edge hswap
  have htwithoutb : t ⊆ (t ∪ q).erase b := by
    intro z hz
    exact mem_erase.mpr ⟨fun he ↦ (disjoint_left.mp hd) hz (he.symm ▸ hb),
      mem_union_left _ hz⟩
  have hqwithoutb : q.erase b ⊆ (t ∪ q).erase b := erase_subset_erase _ subset_union_right
  have e (y : V) (hy : y ∈ q.erase b) : G.Adj x y :=
    hwithoutb (htwithoutb hx) (hqwithoutb hy)
      (fun he ↦ (disjoint_left.mp hd) hx (he.symm ▸ (mem_erase.mp hy).2))
  have hqwithoutx : q ⊆ (t ∪ q).erase x := by
    intro z hz
    exact mem_erase.mpr ⟨fun he ↦ (disjoint_left.mp hd) hx (he ▸ hz),
      mem_union_right _ hz⟩
  by_cases hax : a = x
  · subst a
    refine ⟨u, v, w, b, ?_, e u hu, e v hv, e w hw, ?_, ?_⟩
    · rw [hqenum]
      ext z
      simp only [mem_insert, mem_singleton]
      tauto
    · apply SimpleGraph.IsClique.subset _ (clique_erase_of_add_edge hcl)
      apply coe_subset.mpr
      apply union_subset
      · exact erase_subset_erase _ subset_union_left
      · exact (by simp [insert_subset_iff, hb, (mem_erase.mp hv).2] :
          ({b, v} : Finset V) ⊆ q).trans hqwithoutx
    · apply SimpleGraph.IsClique.subset _ (clique_erase_of_add_edge hcl)
      apply coe_subset.mpr
      apply union_subset
      · exact erase_subset_erase _ subset_union_left
      · exact (by simp [insert_subset_iff, hb, (mem_erase.mp hw).2] :
          ({b, w} : Finset V) ⊆ q).trans hqwithoutx
  · have exb := adj_of_add_edge_of_avoids_endpoints
      (hcl (mem_union_left _ hx) (mem_union_right _ hb) hxb) (Ne.symm hax) hxb
    refine ⟨b, u, v, w, hqenum, exb, e u hu, e v hv, ?_, ?_⟩
    · apply SimpleGraph.IsClique.subset _ hwithoutb
      apply coe_subset.mpr
      apply union_subset ((erase_subset x t).trans htwithoutb)
      exact (by simp [insert_subset_iff, hu, hw] : ({w, u} : Finset V) ⊆ q.erase b).trans
        hqwithoutb
    · apply SimpleGraph.IsClique.subset _ hwithoutb
      apply coe_subset.mpr
      apply union_subset ((erase_subset x t).trans htwithoutb)
      exact (by simp [insert_subset_iff, hv, hw] : ({w, v} : Finset V) ⊆ q.erase b).trans
        hqwithoutb

end Erdos577
