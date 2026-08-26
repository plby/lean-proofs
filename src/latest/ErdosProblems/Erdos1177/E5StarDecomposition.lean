-- Modified for this repository: Lean 4.33.0 port and Erdos1177 namespace.
import ErdosProblems.Erdos1177.E5IntersectionStructure

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Star decomposition around an edge

This module sharpens the local structure of the edge-intersection graph of a
linear triple system.  Every neighbour of a fixed edge has a unique contact
vertex on that edge.  Consequently the neighbourhood is canonically partitioned
into three cliques, one through each point of the centre edge.  These facts are
useful local constraints for the remaining Hajnal--Komjáth extraction.
-/

namespace Erdos1177

universe u

variable {W : Type u}

/-- The family of host edges containing a specified vertex. -/
def edgeStar (H : Hypergraph W) (x : W) : Set H.edges :=
  {e | x ∈ e.1}

/-
Membership in an edge-star is exactly incidence with its centre.
-/
theorem mem_edgeStar_iff (H : Hypergraph W) (x : W) (e : H.edges) :
    e ∈ edgeStar H x ↔ x ∈ e.1 := by
  rfl

/-
Distinct members of one edge-star are adjacent in the edge-intersection
 graph.
-/
theorem edgeStar_pairwise_adjacent (H : Hypergraph W) (x : W)
    {e f : H.edges} (he : e ∈ edgeStar H x) (hf : f ∈ edgeStar H x)
    (hef : e ≠ f) :
    (edgeIntersectionGraph H).Adj e f := by
  exact Erdos1177.edgeIntersectionGraph_adj_of_common_vertex H hef ( by simpa using! he ) ( by simpa using! hf )

/-
Two distinct edges of a linear host have a unique contact vertex.
-/
theorem unique_contact_vertex (H : Hypergraph W) (hlin : H.Linear)
    {e f : H.edges} (hadj : (edgeIntersectionGraph H).Adj e f) :
    ∃! x, x ∈ e.1 ∧ x ∈ f.1 := by
  convert! existsUnique_common_vertex H hlin e.property f.property _ _ using 1;
  · exact fun h => hadj.1 ( Subtype.ext h );
  · convert! hadj.2 using 1;
    grind +qlia

/-- Choose the unique point at which two adjacent edges of a linear host meet. -/
noncomputable def contactVertex (H : Hypergraph W) (hlin : H.Linear)
    {e f : H.edges} (hadj : (edgeIntersectionGraph H).Adj e f) : W :=
  Classical.choose (unique_contact_vertex H hlin hadj)

/-
The chosen contact belongs to both adjacent edges.
-/
theorem contactVertex_mem (H : Hypergraph W) (hlin : H.Linear)
    {e f : H.edges} (hadj : (edgeIntersectionGraph H).Adj e f) :
    contactVertex H hlin hadj ∈ e.1 ∧ contactVertex H hlin hadj ∈ f.1 := by
  have := Classical.choose_spec ( unique_contact_vertex H hlin hadj );
  exact this.1

/-
Any common point of two adjacent edges is their chosen contact.
-/
theorem eq_contactVertex_of_mem (H : Hypergraph W) (hlin : H.Linear)
    {e f : H.edges} (hadj : (edgeIntersectionGraph H).Adj e f)
    {x : W} (hxe : x ∈ e.1) (hxf : x ∈ f.1) :
    x = contactVertex H hlin hadj := by
  exact ExistsUnique.unique ( unique_contact_vertex H hlin hadj ) ⟨ hxe, hxf ⟩ ( contactVertex_mem H hlin hadj )

/-
Neighbours of a fixed edge are covered by the stars through its vertices.
-/
theorem neighbourhood_subset_iUnion_edgeStar (H : Hypergraph W)
    (center : H.edges) :
    {f | (edgeIntersectionGraph H).Adj center f} ⊆
      ⋃ x ∈ center.1, edgeStar H x := by
  intro f hf; simp_all +decide [ Set.mem_iUnion ] ;
  exact Exists.elim ( edgeIntersectionGraph_neighbour_star_cover H center f hf ) fun x hx => ⟨ x, hx.1, by unfold edgeStar; aesop ⟩

/-
In a linear host a neighbour belongs to exactly one star through the centre
edge.
-/
theorem neighbour_unique_edgeStar (H : Hypergraph W) (hlin : H.Linear)
    (center leaf : H.edges)
    (hadj : (edgeIntersectionGraph H).Adj center leaf) :
    ∃! x, x ∈ center.1 ∧ leaf ∈ edgeStar H x := by
  convert! unique_contact_vertex H hlin hadj using 1

/-
If two different neighbours have the same contact with the centre, then
those neighbours are adjacent.
-/
theorem neighbours_adjacent_of_contact_eq
    (H : Hypergraph W) (hlin : H.Linear) (center : H.edges)
    {e f : H.edges}
    (he : (edgeIntersectionGraph H).Adj center e)
    (hf : (edgeIntersectionGraph H).Adj center f)
    (hef : e ≠ f)
    (hcontact : contactVertex H hlin he = contactVertex H hlin hf) :
    (edgeIntersectionGraph H).Adj e f := by
  by_contra h_contra;
  obtain ⟨x, hx⟩ : ∃ x, x ∈ e.1 ∧ x ∈ f.1 := by
    exact ⟨ contactVertex H hlin he, contactVertex_mem H hlin he |>.2, hcontact.symm ▸ contactVertex_mem H hlin hf |>.2 ⟩;
  exact h_contra ( edgeIntersectionGraph_adj_of_common_vertex H hef hx.1 hx.2 )

/-
Pairwise nonadjacent neighbours have pairwise distinct contact vertices.
-/
theorem contactVertex_injective_on_independent_neighbours
    (H : Hypergraph W) (hlin : H.Linear) (center : H.edges)
    {ι : Type*} {leaf : ι → H.edges}
    (hleaf : Function.Injective leaf)
    (hadj : ∀ i, (edgeIntersectionGraph H).Adj center (leaf i))
    (hind : ∀ ⦃i j⦄, i ≠ j →
      ¬ (edgeIntersectionGraph H).Adj (leaf i) (leaf j)) :
    Function.Injective (fun i => contactVertex H hlin (hadj i)) := by
  intro i j hij;
  exact Classical.not_not.1 fun hi => hind hi <| by simpa [ hij ] using! neighbours_adjacent_of_contact_eq H hlin center ( hadj i ) ( hadj j ) ( hleaf.ne hi ) hij;

/-
Distinct stars through a fixed centre edge are disjoint after restricting
to neighbours of that centre.
-/
theorem neighbour_not_mem_two_center_stars
    (H : Hypergraph W) (hlin : H.Linear) (center leaf : H.edges)
    (hadj : (edgeIntersectionGraph H).Adj center leaf)
    {x y : W} (hxc : x ∈ center.1) (hyc : y ∈ center.1) (hxy : x ≠ y)
    (hxl : leaf ∈ edgeStar H x) :
    leaf ∉ edgeStar H y := by
  contrapose! hxy; have := unique_contact_vertex H hlin hadj; simp_all +decide [ mem_edgeStar_iff ] ;
  exact this.unique ⟨ hxc, hxl ⟩ ⟨ hyc, hxy ⟩

/-
An independent family of distinct neighbours injects into the vertex set
of its centre via the contact map.
-/
theorem independent_neighbours_inject_into_center
    (H : Hypergraph W) (hlin : H.Linear) (center : H.edges)
    {ι : Type*} {leaf : ι → H.edges}
    (hleaf : Function.Injective leaf)
    (hadj : ∀ i, (edgeIntersectionGraph H).Adj center (leaf i))
    (hind : ∀ ⦃i j⦄, i ≠ j →
      ¬ (edgeIntersectionGraph H).Adj (leaf i) (leaf j)) :
    ∃ contact : ι → {x // x ∈ center.1}, Function.Injective contact := by
  have h_inj : Function.Injective (fun i => contactVertex H hlin (hadj i)) :=
    contactVertex_injective_on_independent_neighbours H hlin center hleaf hadj hind
  exact ⟨ fun i => ⟨ _, contactVertex_mem H hlin ( hadj i ) |>.1 ⟩, fun i j hij => h_inj <| Subtype.ext_iff.mp hij ⟩

/-
A centre edge in a triple system can be written as three distinct points,
and its entire neighbourhood is covered by the corresponding three cliques.
-/
theorem neighbourhood_three_clique_cover
    (H : Hypergraph W) (htri : H.IsTripleSystem) (center : H.edges) :
    ∃ a b c : W,
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ center.1 = {a, b, c} ∧
      {f | (edgeIntersectionGraph H).Adj center f} ⊆
        edgeStar H a ∪ edgeStar H b ∪ edgeStar H c ∧
      (∀ {e f}, e ∈ edgeStar H a → f ∈ edgeStar H a → e ≠ f →
        (edgeIntersectionGraph H).Adj e f) ∧
      (∀ {e f}, e ∈ edgeStar H b → f ∈ edgeStar H b → e ≠ f →
        (edgeIntersectionGraph H).Adj e f) ∧
      (∀ {e f}, e ∈ edgeStar H c → f ∈ edgeStar H c → e ≠ f →
        (edgeIntersectionGraph H).Adj e f) := by
  -- By definition of $IsTripleSystem$, there exist three distinct elements $a$, $b$, and $c$ such that $center.1 = \{a, b, c\}$.
  obtain ⟨a, b, c, h_distinct, h_eq⟩ : ∃ a b c : W, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ center.1 = {a, b, c} := by
    have := htri center.val center.prop; simp_all +decide [ Set.ncard_eq_three ] ;
  use a, b, c;
  simp_all +decide [ Set.subset_def, mem_edgeStar_iff ];
  refine' ⟨ _, _, _, _ ⟩;
  · intro e he hadj; have := edgeIntersectionGraph_neighbour_star_cover H center ⟨ e, he ⟩ hadj; aesop;
  · exact fun e he f hf hea hfa hef => edgeIntersectionGraph_adj_of_common_vertex H ( by aesop ) hea hfa;
  · exact fun e he f hf he' hf' hef => edgeIntersectionGraph_adj_of_common_vertex H ( by aesop ) ( by aesop ) ( by aesop );
  · exact fun e he f hf he' hf' hef => edgeIntersectionGraph_adj_of_common_vertex H ( by aesop ) ( by aesop ) ( by aesop )


/-- The neighbours of `center` meeting it at `x`. -/
def neighbourStar (H : Hypergraph W) (center : H.edges) (x : W) : Set H.edges :=
  {leaf | (edgeIntersectionGraph H).Adj center leaf ∧ leaf ∈ edgeStar H x}

/-
The full neighbourhood is the union of its contact stars.
-/
theorem neighbourhood_eq_iUnion_neighbourStar (H : Hypergraph W)
    (center : H.edges) :
    {leaf | (edgeIntersectionGraph H).Adj center leaf} =
      ⋃ x ∈ center.1, neighbourStar H center x := by
  ext leaf
  simp [neighbourStar];
  exact fun h => by obtain ⟨ x, hx ⟩ := edgeIntersectionGraph_neighbour_star_cover H center leaf h; exact ⟨ x, hx.1, hx.2 ⟩ ;

/-
Contact stars indexed by distinct centre vertices are disjoint in a linear
host.
-/
theorem disjoint_neighbourStar (H : Hypergraph W) (hlin : H.Linear)
    (center : H.edges) {x y : W} (hxc : x ∈ center.1) (hyc : y ∈ center.1)
    (hxy : x ≠ y) :
    Disjoint (neighbourStar H center x) (neighbourStar H center y) := by
  exact Set.disjoint_left.mpr fun leaf hleafx hleafy => Erdos1177.neighbour_not_mem_two_center_stars H hlin center leaf ( hleafx.1 ) hxc hyc hxy hleafx.2 hleafy.2

/-
Every contact star is a clique in the edge-intersection graph.
-/
theorem neighbourStar_pairwise_adjacent (H : Hypergraph W)
    (center : H.edges) (x : W) {e f : H.edges}
    (he : e ∈ neighbourStar H center x)
    (hf : f ∈ neighbourStar H center x) (hef : e ≠ f) :
    (edgeIntersectionGraph H).Adj e f := by
  convert! edgeStar_pairwise_adjacent H x _ _ _;
  · exact he.2;
  · exact hf.2;
  · exact hef

/-
The neighbourhood of an edge in a linear triple system is the disjoint
union of three cliques indexed by the three vertices of that edge.
-/
theorem neighbourhood_disjoint_three_cliques
    (H : Hypergraph W) (htri : H.IsTripleSystem) (hlin : H.Linear)
    (center : H.edges) :
    ∃ a b c : W,
      a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ center.1 = {a, b, c} ∧
      {leaf | (edgeIntersectionGraph H).Adj center leaf} =
        neighbourStar H center a ∪ neighbourStar H center b ∪
          neighbourStar H center c ∧
      Disjoint (neighbourStar H center a) (neighbourStar H center b) ∧
      Disjoint (neighbourStar H center a) (neighbourStar H center c) ∧
      Disjoint (neighbourStar H center b) (neighbourStar H center c) ∧
      (∀ {e f}, e ∈ neighbourStar H center a →
        f ∈ neighbourStar H center a → e ≠ f →
        (edgeIntersectionGraph H).Adj e f) ∧
      (∀ {e f}, e ∈ neighbourStar H center b →
        f ∈ neighbourStar H center b → e ≠ f →
        (edgeIntersectionGraph H).Adj e f) ∧
      (∀ {e f}, e ∈ neighbourStar H center c →
        f ∈ neighbourStar H center c → e ≠ f →
        (edgeIntersectionGraph H).Adj e f) := by
  obtain ⟨a, b, c, ha, hb, hc, h⟩ : ∃ a b c : W, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ (center : Set W) = {a, b, c} := by
    exact Set.ncard_eq_three.mp ( htri center center.2 ) |> fun ⟨ a, b, c, hab, hbc, hac ⟩ => ⟨ a, b, c, by aesop ⟩;
  refine' ⟨ a, b, c, ha, hb, hc, h, _, _, _, _ ⟩;
  · ext leaf; simp [neighbourStar];
    by_cases h : ( edgeIntersectionGraph H ).Adj center leaf <;> simp +decide [ h, edgeStar ];
    have := edgeIntersectionGraph_neighbour_star_cover H center leaf h; aesop;
  · exact disjoint_neighbourStar H hlin center ( h.symm ▸ by simp +decide ) ( h.symm ▸ by simp +decide ) ha;
  · exact disjoint_neighbourStar H hlin center ( by simp +decide [ h ] ) ( by simp +decide [ h ] ) hb;
  · grind +suggestions

end Erdos1177
