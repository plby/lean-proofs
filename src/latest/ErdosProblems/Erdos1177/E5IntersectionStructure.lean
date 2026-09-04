-- Modified for this repository: Lean 4.33.0 port and Erdos1177 namespace.
import ErdosProblems.Erdos1177.E5IntersectionCycle

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Local structure of the edge-intersection graph

This file develops structural consequences of linearity and 3-uniformity used
in the remaining Hajnal--Komjáth argument.  Around a fixed hyperedge, all
neighbours in the edge-intersection graph split into the three stars determined
by its vertices.  In particular, four pairwise disjoint host edges cannot all
meet one fixed edge; equivalently, the edge-intersection graph has no induced
four-claw.
-/

namespace Erdos1177

universe u

variable {W : Type u}

/-
In a linear hypergraph, two distinct edges have at most one common
vertex.
-/
theorem linear_intersection_subsingleton (H : Hypergraph W) (hlin : H.Linear)
    {e f : Set W} (he : e ∈ H.edges) (hf : f ∈ H.edges) (hef : e ≠ f) :
    (e ∩ f).Subsingleton := by
  exact fun x hx y hy => by have := hlin e he f hf hef; aesop;

/-
Two distinct intersecting edges of a linear hypergraph have a unique
common vertex.
-/
theorem existsUnique_common_vertex (H : Hypergraph W) (hlin : H.Linear)
    {e f : Set W} (he : e ∈ H.edges) (hf : f ∈ H.edges) (hef : e ≠ f)
    (hmeet : (e ∩ f).Nonempty) :
    ∃! x, x ∈ e ∩ f := by
  obtain ⟨ x, hx ⟩ := hmeet;
  exact ⟨ x, hx, fun y hy => by have := linear_intersection_subsingleton H hlin he hf hef; exact this hy hx ⟩

/-
Every edge meeting a fixed triple belongs to one of the three stars
through the vertices of that triple.
-/
theorem neighbour_meets_one_of_three (H : Hypergraph W)
    (htri : H.IsTripleSystem) {e f : Set W} (he : e ∈ H.edges)
    (hmeet : (e ∩ f).Nonempty) :
    ∃ a b c, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ e = {a, b, c} ∧
      (a ∈ f ∨ b ∈ f ∨ c ∈ f) := by
  have := htri e he;
  obtain ⟨ a, b, c, h ⟩ := Set.ncard_eq_three.mp this;
  exact ⟨ a, b, c, h.1, h.2.1, h.2.2.1, h.2.2.2, by obtain ⟨ x, hx ⟩ := hmeet; aesop ⟩

/-
A finite pairwise-disjoint family of host edges which all meet one fixed
triple has at most three members.
-/
theorem card_pairwiseDisjoint_edges_meeting_le_three
    (H : Hypergraph W) (htri : H.IsTripleSystem)
    (e : Set W) (he : e ∈ H.edges) (D : Finset (Set W))
    (hDmeet : ∀ f ∈ D, (e ∩ f).Nonempty)
    (hDdisj : ∀ ⦃f g⦄, f ∈ D → g ∈ D → f ≠ g → Disjoint f g) :
    D.card ≤ 3 := by
  have h_card : ∀ f ∈ D, (e ∩ f).Nonempty → ∃ x, x ∈ e ∧ x ∈ f := by
    exact fun f hf h => by obtain ⟨ x, hx ⟩ := h; exact ⟨ x, hx.1, hx.2 ⟩ ;
  choose! x hx₁ hx₂ using h_card;
  have h_inj : Function.Injective (fun f : { f : Set W // f ∈ D } => ⟨x f.1 f.2 (hDmeet f.1 f.2), hx₁ f.1 f.2 (hDmeet f.1 f.2)⟩ : { f : Set W // f ∈ D } → { w : W // w ∈ e }) := by
    intro f g hfg; simp_all +decide [ Set.disjoint_left ] ;
    grind +splitImp;
  have h_card : (Set.ncard e) ≥ D.card := by
    have h_card : (Set.ncard (Set.image (fun f : { f : Set W // f ∈ D } => x f.1 f.2 (hDmeet f.1 f.2)) Set.univ)) ≤ (Set.ncard e) := by
      apply Set.ncard_le_ncard;
      · exact Set.image_subset_iff.mpr fun f _ => hx₁ _ _ _;
      · exact Set.finite_of_ncard_pos ( by rw [ htri e he ] ; norm_num );
    rw [ Set.InjOn.ncard_image ] at h_card;
    · simpa [ Set.ncard_univ ] using! h_card;
    · exact fun f _ g _ hfg => by have := @h_inj f g; aesop;
  exact h_card.trans ( htri e he ▸ le_rfl )

/-
Four pairwise disjoint host edges cannot all intersect one fixed edge of a
triple system.  This is the hypergraph form of the forbidden induced
four-claw in its edge-intersection graph.
-/
theorem no_four_pairwise_disjoint_edges_meeting
    (H : Hypergraph W) (htri : H.IsTripleSystem)
    (e : Set W) (he : e ∈ H.edges)
    (f : Fin 4 → Set W)
    (hmeet : ∀ i, (e ∩ f i).Nonempty)
    (hdisj : ∀ ⦃i j⦄, i ≠ j → Disjoint (f i) (f j)) : False := by
  contrapose! htri;
  intro h;
  obtain ⟨a, b, c, habc⟩ : ∃ a b c, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ e = {a, b, c} := by
    have := h e he; simp_all +decide;
    rw [ Set.ncard_eq_three ] at this; tauto;
  simp_all +decide [ Set.Nonempty ];
  simp_all +decide [ Fin.forall_fin_succ, Set.disjoint_left ];
  grind

/-
In the edge-intersection graph of a triple system, there is no induced
`K_{1,4}` whose four leaves correspond to pairwise disjoint hyperedges.
-/
theorem edgeIntersectionGraph_no_four_claw
    (H : Hypergraph W) (htri : H.IsTripleSystem)
    (center : H.edges) (leaf : Fin 4 → H.edges)
    (hleaf : Function.Injective leaf)
    (hadj : ∀ i, (edgeIntersectionGraph H).Adj center (leaf i))
    (hnadj : ∀ ⦃i j⦄, i ≠ j →
      ¬ (edgeIntersectionGraph H).Adj (leaf i) (leaf j)) : False := by
  apply no_four_pairwise_disjoint_edges_meeting H htri center.val center.property (fun i => (leaf i).val) (fun i => ?_) (fun i j hij => ?_);
  · exact ( edgeIntersectionGraph_adj_iff H center ( leaf i ) ).mp ( hadj i ) |>.2;
  · simp_all +decide [ Set.disjoint_iff_inter_eq_empty, edgeIntersectionGraph_adj_iff ];
    exact Set.not_nonempty_iff_eq_empty.mp ( hnadj hij ( hleaf.ne hij ) )

/-
All distinct host edges through one vertex form a clique in the
edge-intersection graph.
-/
theorem edgeIntersectionGraph_adj_of_common_vertex
    (H : Hypergraph W) {e f : H.edges} (hef : e ≠ f)
    {x : W} (hxe : x ∈ e.1) (hxf : x ∈ f.1) :
    (edgeIntersectionGraph H).Adj e f := by
  constructor <;> tauto

/-
The neighbours of a fixed edge are covered by the vertex-stars indexed by
its three points.
-/
theorem edgeIntersectionGraph_neighbour_star_cover
    (H : Hypergraph W) (center leaf : H.edges)
    (hadj : (edgeIntersectionGraph H).Adj center leaf) :
    ∃ x ∈ center.1, x ∈ leaf.1 := by
  obtain ⟨ x, hx ⟩ := hadj;
  exact hx.elim ( fun h => h.imp fun x hx => ⟨ hx.1, hx.2 ⟩ ) fun h => h.imp fun x hx => ⟨ hx.2, hx.1 ⟩

/-
Every independent finite subset of the neighbourhood of one vertex in the
edge-intersection graph of a triple system has cardinality at most three.
-/
theorem edgeIntersectionGraph_independent_neighbour_card_le_three
    (H : Hypergraph W) (htri : H.IsTripleSystem)
    (center : H.edges) (D : Finset H.edges)
    (hadj : ∀ f ∈ D, (edgeIntersectionGraph H).Adj center f)
    (hind : ∀ ⦃f g⦄, f ∈ D → g ∈ D → f ≠ g →
      ¬ (edgeIntersectionGraph H).Adj f g) :
    D.card ≤ 3 := by
  convert! card_pairwiseDisjoint_edges_meeting_le_three H htri center.1 center.2 ( D.image Subtype.val ) ?_ using 1;
  all_goals try exact Classical.decEq _;
  · simp +decide only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right, ne_eq,
    forall_exists_index];
    contrapose! hind;
    obtain ⟨ f, g, hf, hf', hg, hg', hfg, h ⟩ := hind.1;
    exact ⟨ _, _, hf', hg', by aesop, by rw [ edgeIntersectionGraph_adj_iff ] ; exact ⟨ by aesop, by rw [ Set.not_disjoint_iff ] at h; tauto ⟩ ⟩;
  · intro f hf
    simp only [Finset.mem_image] at hf
    obtain ⟨g, hg, rfl⟩ := hf
    exact ((edgeIntersectionGraph_adj_iff H center g).mp (hadj g hg)).2

/-
Consequently, the neighbourhood of an edge in a triple system has
independence number at most three.
-/
theorem edgeIntersectionGraph_no_independent_four_neighbours
    (H : Hypergraph W) (htri : H.IsTripleSystem)
    (center : H.edges) (leaf : Fin 4 → H.edges)
    (hleaf : Function.Injective leaf)
    (hadj : ∀ i, (edgeIntersectionGraph H).Adj center (leaf i)) :
    ∃ i j, i ≠ j ∧ (edgeIntersectionGraph H).Adj (leaf i) (leaf j) := by
  have := @Erdos1177.edgeIntersectionGraph_no_four_claw W H htri center leaf hleaf hadj;
  grind

end Erdos1177
