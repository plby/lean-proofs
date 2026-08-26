import ErdosProblems.Erdos19.Core

/-!
# Pair completion of a linear hypergraph

Missing pairs can be added as two-element edges without losing linearity.
This is the exact completion used by the asymptotic proof.
-/

namespace Erdos19.SetHypergraph

universe u
variable {X : Type u}

/-- Restrict a proper coloring to a subhypergraph. -/
def EdgeColoring.restrict {H J : SetHypergraph X} {K : Type*}
    (c : J.EdgeColoring K) (hHJ : H ⊆ J) : H.EdgeColoring K where
  color e := c ⟨e.1, hHJ e.2⟩
  valid := by
    intro e f hef hinter hsame
    apply c.valid (e := ⟨e.1, hHJ e.2⟩) (f := ⟨f.1, hHJ f.2⟩)
      (fun h ↦ hef (Subtype.ext (congrArg (fun z : J ↦ z.1) h))) hinter
    exact hsame

lemma EdgeColorable.of_subset {H J : SetHypergraph X} {k : ℕ}
    (hcolor : J.EdgeColorable k) (hHJ : H ⊆ J) : H.EdgeColorable k := by
  obtain ⟨c⟩ := hcolor
  exact ⟨c.restrict hHJ⟩

/-- Every pair of distinct vertices is contained in some hyperedge. -/
def IsPairComplete (H : SetHypergraph X) : Prop :=
  ∀ x y : X, x ≠ y → ∃ e ∈ H, x ∈ e ∧ y ∈ e

/-- Add precisely the two-element sets not contained in an existing edge. -/
def pairCompletion (H : SetHypergraph X) : SetHypergraph X :=
  H ∪ {e | e.ncard = 2 ∧ ∀ f ∈ H, ¬e ⊆ f}

lemma subset_pairCompletion (H : SetHypergraph X) : H ⊆ H.pairCompletion :=
  Set.subset_union_left

lemma pair_inter_subsingleton_or_subset [Fintype X] {e f : Set X}
    (he : e.ncard = 2) : (e ∩ f).Subsingleton ∨ e ⊆ f := by
  by_cases hi : (e ∩ f).Subsingleton
  · exact Or.inl hi
  · right
    have hcard : e.ncard ≤ (e ∩ f).ncard := by
      have hnot : ¬(e ∩ f).ncard ≤ 1 := by
        intro h
        exact hi (Set.ncard_le_one_iff_subsingleton.mp h)
      omega
    have heq : e ∩ f = e := Set.eq_of_subset_of_ncard_le Set.inter_subset_left hcard
    rw [← heq]
    exact Set.inter_subset_right

lemma pairCompletion_isLinear [Fintype X] {H : SetHypergraph X}
    (hH : H.IsLinear) : H.pairCompletion.IsLinear := by
  intro e he f hf hef
  rcases he with he | he <;> rcases hf with hf | hf
  · exact hH he hf hef
  · rcases pair_inter_subsingleton_or_subset (f := e) hf.1 with hsub | hsub
    · simpa only [Set.inter_comm] using hsub
    · exact (hf.2 e he hsub).elim
  · rcases pair_inter_subsingleton_or_subset (f := f) he.1 with hsub | hsub
    · exact hsub
    · exact (he.2 f hf hsub).elim
  · rcases pair_inter_subsingleton_or_subset (f := f) he.1 with hsub | hsub
    · exact hsub
    · exact (hef (Set.eq_of_subset_of_ncard_le hsub (by rw [hf.1, he.1]))).elim

lemma pairCompletion_isPairComplete (H : SetHypergraph X) :
    H.pairCompletion.IsPairComplete := by
  classical
  intro x y hxy
  by_cases hcovered : ∃ e ∈ H, x ∈ e ∧ y ∈ e
  · obtain ⟨e, he, hx, hy⟩ := hcovered
    exact ⟨e, Or.inl he, hx, hy⟩
  · refine ⟨{x, y}, Or.inr ⟨Set.ncard_pair hxy, ?_⟩, by simp, by simp⟩
    intro f hf hsub
    exact hcovered ⟨f, hf, hsub (by simp), hsub (by simp)⟩

lemma pairCompletion_min_size {H : SetHypergraph X}
    (hsize : ∀ e ∈ H, 2 ≤ e.ncard) :
    ∀ e ∈ H.pairCompletion, 2 ≤ e.ncard := by
  intro e he
  rcases he with he | he
  · exact hsize e he
  · exact he.1.ge

/-- In a pair-complete linear hypergraph, the off-vertex incidence budget is
an equality, rather than just the general inequality in `Core`. -/
lemma sum_incident_ncard_sub_one_eq [Fintype X] (H : SetHypergraph X)
    (hlinear : H.IsLinear) (hcomplete : H.IsPairComplete) (x : X) :
    (∑ e : H.incidentEdges x, (e.1.1.ncard - 1)) = Fintype.card X - 1 := by
  classical
  let Fiber (e : H.incidentEdges x) := (e.1.1 \ {x} : Set X)
  let code (p : Σ e : H.incidentEdges x, Fiber e) : (Set.univ \ {x} : Set X) :=
    ⟨p.2.1, Set.mem_univ _, p.2.2.2⟩
  have hinj : Function.Injective code := by
    intro p q hpq
    have hpoint : p.2.1 = q.2.1 := congrArg Subtype.val hpq
    have hedge : p.1.1 = q.1.1 := by
      apply Subtype.ext
      by_contra hne
      have hsub := hlinear p.1.1.2 q.1.1.2 hne
      have hxmem : x ∈ p.1.1.1 ∩ q.1.1.1 := ⟨p.1.2, q.1.2⟩
      have hymem : p.2.1 ∈ p.1.1.1 ∩ q.1.1.1 := by
        exact ⟨p.2.2.1, hpoint ▸ q.2.2.1⟩
      exact p.2.2.2 (hsub hymem hxmem)
    have hindex : p.1 = q.1 := Subtype.ext hedge
    apply Sigma.ext hindex
    exact (Subtype.heq_iff_coe_eq (fun z ↦ by rw [hindex])).2 hpoint
  have hsurj : Function.Surjective code := by
    intro y
    have hyx : y.1 ≠ x := y.2.2
    obtain ⟨e, he, hx, hy⟩ := hcomplete x y.1 hyx.symm
    refine ⟨⟨⟨⟨e, he⟩, hx⟩, ⟨y.1, hy, hyx⟩⟩, ?_⟩
    exact Subtype.ext rfl
  have hcard := Fintype.card_congr (Equiv.ofBijective code ⟨hinj, hsurj⟩)
  have hdiff (e : H.incidentEdges x) :
      (e.1.1 \ {x}).ncard = e.1.1.ncard - 1 := by
    have hx : x ∈ e.1.1 := e.2
    rw [Set.ncard_sdiff (Set.singleton_subset_iff.mpr hx), Set.ncard_singleton]
  calc
    (∑ e : H.incidentEdges x, (e.1.1.ncard - 1)) =
        ∑ e : H.incidentEdges x, Fintype.card (Fiber e) := by
          apply Finset.sum_congr rfl
          intro e _
          rw [Set.fintypeCard_eq_ncard, hdiff]
    _ = Fintype.card (Σ e : H.incidentEdges x, Fiber e) := by
      rw [Fintype.card_sigma]
    _ = Fintype.card (Set.univ \ {x} : Set X) := hcard
    _ = (Set.univ \ {x} : Set X).ncard := Set.fintypeCard_eq_ncard _
    _ = Fintype.card X - 1 := by
      rw [Set.ncard_sdiff (show ({x} : Set X) ⊆ Set.univ by simp)]
      simp

/-- The graph consisting of the two-element hyperedges. -/
def twoGraph (H : SetHypergraph X) : SimpleGraph X where
  Adj x y := x ≠ y ∧ ({x, y} : Set X) ∈ H
  symm := ⟨by
    intro x y h
    exact ⟨h.1.symm, by simpa only [Set.pair_comm] using h.2⟩⟩
  loopless := ⟨by
    intro x h
    exact h.1 rfl⟩

@[simp]
lemma twoGraph_adj (H : SetHypergraph X) (x y : X) :
    H.twoGraph.Adj x y ↔ x ≠ y ∧ ({x, y} : Set X) ∈ H := Iff.rfl

lemma eq_pair_of_ncard_eq_two [Fintype X] {e : Set X} {x y : X}
    (he : e.ncard = 2) (hxy : x ≠ y) (hx : x ∈ e) (hy : y ∈ e) :
    e = {x, y} := by
  have hsub : ({x, y} : Set X) ⊆ e := by
    intro z hz
    rcases hz with (rfl | rfl)
    · exact hx
    · exact hy
  exact (Set.eq_of_subset_of_ncard_le hsub (by rw [he, Set.ncard_pair hxy])).symm

lemma incidentEdges_ncard_le_card_pred [Fintype X] (H : SetHypergraph X)
    (hlinear : H.IsLinear) (hsize : ∀ e : H, 2 ≤ e.1.ncard) (x : X) :
    (H.incidentEdges x).ncard ≤ Fintype.card X - 1 := by
  simpa using H.incidentEdges_ncard_mul_sub_one_le hlinear x 2
    (fun e _ ↦ hsize e)

/-- Excess rank above two, summed over all edges at a vertex. -/
noncomputable def incidentExcess [Fintype X] (H : SetHypergraph X) (x : X) : ℕ :=
  ∑ e : H.incidentEdges x, (e.1.1.ncard - 2)

/-- The exact degree/excess identity underlying all completion degree counts. -/
lemma incident_degree_add_excess [Fintype X] (H : SetHypergraph X)
    (hlinear : H.IsLinear) (hcomplete : H.IsPairComplete)
    (hsize : ∀ e : H, 2 ≤ e.1.ncard) (x : X) :
    (H.incidentEdges x).ncard + H.incidentExcess x = Fintype.card X - 1 := by
  classical
  calc
    (H.incidentEdges x).ncard + H.incidentExcess x =
        (∑ _e : H.incidentEdges x, 1) +
          ∑ e : H.incidentEdges x, (e.1.1.ncard - 2) := by
            simp [incidentExcess, Set.fintypeCard_eq_ncard]
    _ = ∑ e : H.incidentEdges x, (1 + (e.1.1.ncard - 2)) :=
      (Finset.sum_add_distrib).symm
    _ = ∑ e : H.incidentEdges x, (e.1.1.ncard - 1) := by
      apply Finset.sum_congr rfl
      intro e _
      have he := hsize e.1
      omega
    _ = Fintype.card X - 1 := H.sum_incident_ncard_sub_one_eq hlinear hcomplete x

lemma incidentExcess_eq_degree_deficit [Fintype X] (H : SetHypergraph X)
    (hlinear : H.IsLinear) (hcomplete : H.IsPairComplete)
    (hsize : ∀ e : H, 2 ≤ e.1.ncard) (x : X) :
    H.incidentExcess x = Fintype.card X - 1 - (H.incidentEdges x).ncard := by
  have h := H.incident_degree_add_excess hlinear hcomplete hsize x
  omega

/-- Neighbors in the graph part correspond exactly to incident two-edges. -/
lemma twoGraph_neighbor_ncard [Fintype X] (H : SetHypergraph X) (x : X) :
    (H.twoGraph.neighborSet x).ncard =
      Fintype.card {e : H.incidentEdges x // e.1.1.ncard = 2} := by
  classical
  let I := {e : H.incidentEdges x // e.1.1.ncard = 2}
  let f : H.twoGraph.neighborSet x → I := fun y ↦ by
    have hy : x ≠ y.1 ∧ ({x, y.1} : Set X) ∈ H :=
      (H.twoGraph_adj x y.1).mp y.2
    exact ⟨⟨⟨{x, y.1}, hy.2⟩, Or.inl rfl⟩, Set.ncard_pair hy.1⟩
  have hinj : Function.Injective f := by
    intro y z h
    have hp : ({x, y.1} : Set X) = {x, z.1} :=
      congrArg (fun e : I ↦ e.1.1.1) h
    have hy : y.1 ∈ ({x, z.1} : Set X) := hp ▸ (by simp)
    rcases hy with hy | hy
    · exact (y.2.1 hy.symm).elim
    · exact Subtype.ext hy
  have hsurj : Function.Surjective f := by
    intro e
    have hcard : e.1.1.1.ncard = 2 := e.2
    obtain ⟨y, hy, hyx⟩ := Set.exists_ne_of_one_lt_ncard (by omega :
      1 < e.1.1.1.ncard) x
    have hepair : e.1.1.1 = {x, y} :=
      eq_pair_of_ncard_eq_two hcard hyx.symm e.1.2 hy
    have hpair : ({x, y} : Set X) ∈ H := hepair ▸ e.1.1.2
    refine ⟨⟨y, hyx.symm, hpair⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact hepair.symm
  let _ : Fintype (H.twoGraph.neighborSet x) := Fintype.ofFinite _
  have hcard := Fintype.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)
  simpa only [Set.fintypeCard_eq_ncard] using hcard

/-- Number of incident edges with at least three vertices. -/
noncomputable def largeDegree [Fintype X] (H : SetHypergraph X) (x : X) : ℕ :=
  Fintype.card {e : H.incidentEdges x // 3 ≤ e.1.1.ncard}

lemma largeDegree_eq_sum [Fintype X] (H : SetHypergraph X) (x : X) :
    H.largeDegree x = ∑ e : H.incidentEdges x, if 3 ≤ e.1.1.ncard then 1 else 0 := by
  classical
  simp [largeDegree, Fintype.card_subtype]

lemma twoGraph_degree_add_largeDegree [Fintype X] (H : SetHypergraph X)
    (hsize : ∀ e : H, 2 ≤ e.1.ncard) (x : X) :
    (H.twoGraph.neighborSet x).ncard + H.largeDegree x =
      (H.incidentEdges x).ncard := by
  classical
  have htwo : Fintype.card {e : H.incidentEdges x // e.1.1.ncard = 2} =
      ∑ e : H.incidentEdges x, if e.1.1.ncard = 2 then 1 else 0 := by
    simp [Fintype.card_subtype]
  rw [H.twoGraph_neighbor_ncard, htwo, H.largeDegree_eq_sum, ← Finset.sum_add_distrib]
  calc
    (∑ e : H.incidentEdges x,
        ((if e.1.1.ncard = 2 then 1 else 0) + (if 3 ≤ e.1.1.ncard then 1 else 0))) =
        ∑ _e : H.incidentEdges x, 1 := by
          apply Finset.sum_congr rfl
          intro e _
          have he := hsize e.1
          split_ifs <;> omega
    _ = (H.incidentEdges x).ncard := by simp [Set.fintypeCard_eq_ncard]

lemma largeDegree_le_incidentExcess [Fintype X] (H : SetHypergraph X) (x : X) :
    H.largeDegree x ≤ H.incidentExcess x := by
  classical
  rw [H.largeDegree_eq_sum]
  unfold incidentExcess
  apply Finset.sum_le_sum
  intro e _
  split_ifs <;> omega

/-- The graph degree controls the total hypergraph degree: each larger edge
uses at least two units of the off-vertex incidence budget. -/
lemma twice_incident_degree_le_card_add_graph_degree [Fintype X]
    (H : SetHypergraph X) (hlinear : H.IsLinear) (hcomplete : H.IsPairComplete)
    (hsize : ∀ e : H, 2 ≤ e.1.ncard) (x : X) :
    2 * (H.incidentEdges x).ncard ≤
      Fintype.card X - 1 + (H.twoGraph.neighborSet x).ncard := by
  have hsplit := H.twoGraph_degree_add_largeDegree hsize x
  have hexcess := H.incident_degree_add_excess hlinear hcomplete hsize x
  have hlarge := H.largeDegree_le_incidentExcess x
  omega

#print axioms pairCompletion_isLinear
#print axioms pairCompletion_isPairComplete
#print axioms sum_incident_ncard_sub_one_eq
#print axioms incident_degree_add_excess
#print axioms twoGraph_neighbor_ncard
#print axioms twice_incident_degree_le_card_add_graph_degree

end Erdos19.SetHypergraph
