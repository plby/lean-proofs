import ErdosProblems.Erdos577.Chains

/-! Removing the added edge from a saturated graph's quadrilateral factor. -/

namespace Erdos577

open Finset Function

variable {V : Type*} [DecidableEq V] {G H : SimpleGraph V} {k : ℕ}

namespace Packing

/-- Restrict a packing to a finite collection of indices whose cycle edges
already belong to the smaller graph. -/
def selectPartition (p : Packing H k) (indices : Finset (Fin k))
    (h : ∀ i ∈ indices, ∀ j, G.Adj (p.vertices (i, j)) (p.vertices (i, j + 1))) :
    BlockPartition G (indices.biUnion fun i ↦ (p.cycle i).support) where
  blocks := indices.image fun i ↦ (p.cycle i).support
  disjoint := by
    intro b hb c hc hbc
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hb
    obtain ⟨j, hj, rfl⟩ := mem_image.mp hc
    apply p.disjoint_cycles
    intro hij
    exact hbc (congrArg (fun i ↦ (p.cycle i).support) hij)
  cover := by
    ext v
    simp only [mem_biUnion, mem_image]
    constructor
    · rintro ⟨b, ⟨i, hi, rfl⟩, hv⟩
      exact ⟨i, hi, hv⟩
    · rintro ⟨i, hi, hv⟩
      exact ⟨(p.cycle i).support, ⟨i, hi, rfl⟩, hv⟩
  quad := by
    intro b hb
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hb
    refine ⟨Quadrilateral.ofEdges {
      toFun := fun j ↦ p.vertices (i, j)
      inj' := fun _ _ he ↦ (Prod.mk.inj (p.vertices.injective he)).2 } (h i hi), rfl⟩

lemma omit_cycle_cover [Fintype V] (p : Packing H k)
    (hcard : Fintype.card V = 4 * k) (i : Fin k) :
    ((univ.erase i).biUnion fun j ↦ (p.cycle j).support) =
      univ \ (p.cycle i).support := by
  ext v
  simp only [mem_biUnion, mem_erase, mem_univ, and_true, mem_sdiff, true_and]
  constructor
  · rintro ⟨j, hji, hv⟩ hi
    exact (disjoint_left.mp (p.disjoint_cycles hji)) hv hi
  · intro hv
    have hvp : v ∈ p.support := by rw [p.support_eq_univ hcard]; exact mem_univ _
    obtain ⟨⟨j, a⟩, _, he⟩ := mem_image.mp hvp
    refine ⟨j, ?_, (Quadrilateral.mem_support _ _).mpr ⟨a, he⟩⟩
    intro hji
    subst j
    exact hv ((Quadrilateral.mem_support _ _).mpr ⟨a, he⟩)

end Packing

/-- An injective path on four vertices. No absent extra edges are required. -/
structure FourPath (G : SimpleGraph V) where
  vertices : Fin 4 ↪ V
  adjacent : ∀ i : Fin 3, G.Adj (vertices i.castSucc) (vertices i.succ)

namespace FourPath

def support (p : FourPath G) : Finset V := univ.image p.vertices

@[simp] lemma mem_support (p : FourPath G) (v : V) :
    v ∈ p.support ↔ ∃ i, p.vertices i = v := by simp [support]

@[simp] lemma card_support (p : FourPath G) : p.support.card = 4 := by
  rw [support, card_image_of_injective _ p.vertices.injective]
  simp

end FourPath

omit [DecidableEq V] in
lemma added_edge_endpoints {u v a b : V}
    (h : (G ⊔ SimpleGraph.edge u v).Adj a b) (hn : ¬G.Adj a b) :
    (a = u ∧ b = v) ∨ (a = v ∧ b = u) := by
  exact ((SimpleGraph.edge_adj _ _ _ _).mp
    ((SimpleGraph.sup_adj _ _ _ _).mp h |>.resolve_left hn)).1

namespace Quadrilateral

omit [DecidableEq V] in
/-- Only one edge of a four-cycle can be the specified newly added edge. -/
lemma other_edges {u v : V} (q : Quadrilateral (G ⊔ SimpleGraph.edge u v))
    (j : Fin 4) (hn : ¬G.Adj (q j) (q (j + 1)))
    (a : Fin 4) (ha : a ≠ j) : G.Adj (q a) (q (a + 1)) := by
  by_contra hna
  have hj := added_edge_endpoints (q.adjacent j) hn
  have ha' := added_edge_endpoints (q.adjacent a) hna
  have hsame : (a = j ∧ a + 1 = j + 1) ∨ (a = j + 1 ∧ a + 1 = j) := by
    rcases hj with ⟨hju, hjv⟩ | ⟨hjv, hju⟩ <;>
      rcases ha' with ⟨hau, hav⟩ | ⟨hav, hau⟩
    · exact Or.inl ⟨q.injective (hau.trans hju.symm), q.injective (hav.trans hjv.symm)⟩
    · exact Or.inr ⟨q.injective (hav.trans hjv.symm), q.injective (hau.trans hju.symm)⟩
    · exact Or.inr ⟨q.injective (hau.trans hju.symm), q.injective (hav.trans hjv.symm)⟩
    · exact Or.inl ⟨q.injective (hav.trans hjv.symm), q.injective (hau.trans hju.symm)⟩
  rcases hsame with hsame | ⟨haj, hja⟩
  · exact ha hsame.1
  · have hne : ∀ b : Fin 4, (b + 1) + 1 ≠ b := by decide
    exact hne j (by simpa only [haj] using hja)

/-- Rotate a four-cycle so that its unique possible new edge is omitted. -/
def delete_edge {u v : V} (q : Quadrilateral (G ⊔ SimpleGraph.edge u v))
    (j : Fin 4) (hn : ¬G.Adj (q j) (q (j + 1))) : FourPath G where
  vertices := {
    toFun := fun a ↦ q (a + (j + 1))
    inj' := fun _ _ he ↦ add_right_cancel (q.injective he) }
  adjacent := by
    intro a
    have ha : a.castSucc + (j + 1) ≠ j := by
      fin_cases j <;> fin_cases a <;> decide
    have he : a.succ + (j + 1) = (a.castSucc + (j + 1)) + 1 := by
      fin_cases j <;> fin_cases a <;> decide
    change G.Adj (q (a.castSucc + (j + 1))) (q (a.succ + (j + 1)))
    rw [he]
    exact q.other_edges j hn _ ha

lemma delete_edge_support {u v : V} (q : Quadrilateral (G ⊔ SimpleGraph.edge u v))
    (j : Fin 4) (hn : ¬G.Adj (q j) (q (j + 1))) :
    (q.delete_edge j hn).support = q.support := by
  apply eq_of_subset_of_card_le
  · intro x hx
    obtain ⟨a, rfl⟩ := (FourPath.mem_support _ _).mp hx
    exact (mem_support q _).mpr ⟨a + (j + 1), rfl⟩
  · simp

end Quadrilateral

namespace Packing

omit [DecidableEq V] in
/-- If a packing uses a missing edge in one block, every other block lies
in the original graph. Injectivity excludes both possible orientations. -/
lemma other_cycles {u v : V} (p : Packing (G ⊔ SimpleGraph.edge u v) k)
    (i : Fin k) (j : Fin 4)
    (hn : ¬G.Adj (p.vertices (i, j)) (p.vertices (i, j + 1)))
    (a : Fin k) (ha : a ≠ i) (b : Fin 4) :
    G.Adj (p.vertices (a, b)) (p.vertices (a, b + 1)) := by
  by_contra hab
  have hij := added_edge_endpoints (p.adjacent i j) hn
  have hab' := added_edge_endpoints (p.adjacent a b) hab
  have he : p.vertices (a, b) = p.vertices (i, j) ∨
      p.vertices (a, b) = p.vertices (i, j + 1) := by
    rcases hij with ⟨hju, hjv⟩ | ⟨hjv, hju⟩ <;>
      rcases hab' with ⟨hau, hav⟩ | ⟨hav, hau⟩
    · exact Or.inl (hau.trans hju.symm)
    · exact Or.inr (hav.trans hjv.symm)
    · exact Or.inr (hau.trans hju.symm)
    · exact Or.inl (hav.trans hjv.symm)
  rcases he with he | he <;> exact ha (Prod.mk.inj (p.vertices.injective he)).1

end Packing

/-- A saturated counterexample has a spanning path remainder and genuine
quadrilateral blocks on every remaining vertex. -/
theorem Saturated.exists_path_remainder [Fintype V]
    (h : Saturated G k) (hcard : Fintype.card V = 4 * k) :
    ∃ p : FourPath G, Nonempty (BlockPartition G (univ \ p.support)) := by
  classical
  obtain ⟨u, v, huv, huvG⟩ := exists_nonedge (ne_top_of_noPacking hcard h.1)
  obtain ⟨p⟩ := h.hasPacking_add_edge huv huvG
  have hn : ∃ i j, ¬G.Adj (p.vertices (i, j)) (p.vertices (i, j + 1)) := by
    by_contra! hall
    exact h.1 ⟨{ vertices := p.vertices, adjacent := hall }⟩
  obtain ⟨i, j, hij⟩ := hn
  let q := p.cycle i
  have hq : ¬G.Adj (q j) (q (j + 1)) := hij
  refine ⟨q.delete_edge j hq, ?_⟩
  rw [q.delete_edge_support j hq, ← p.omit_cycle_cover hcard i]
  exact ⟨p.selectPartition (univ.erase i)
    (fun a ha b ↦ p.other_cycles i j hij a (mem_erase.mp ha).1 b)⟩

namespace FourPath

lemma support_eq (p : FourPath G) :
    p.support = {p.vertices 0, p.vertices 1, p.vertices 2, p.vertices 3} := by
  have hu : (univ : Finset (Fin 4)) = {0, 1, 2, 3} := by decide
  simp [support, hu]

lemma quad_of_endpoints (p : FourPath G) (h : G.Adj (p.vertices 3) (p.vertices 0)) :
    QuadOn G p.support := by
  refine ⟨Quadrilateral.ofEdges p.vertices ?_, rfl⟩
  intro i
  fin_cases i
  · exact p.adjacent 0
  · exact p.adjacent 1
  · exact p.adjacent 2
  · exact h

lemma quad_of_diagonals (p : FourPath G)
    (h02 : G.Adj (p.vertices 0) (p.vertices 2))
    (h13 : G.Adj (p.vertices 1) (p.vertices 3)) : QuadOn G p.support := by
  let e : Fin 4 ↪ Fin 4 := {
    toFun := ![0, 1, 3, 2]
    inj' := by decide }
  let q := Quadrilateral.ofEdges (e.trans p.vertices) (by
    intro i
    fin_cases i
    · exact p.adjacent 0
    · exact h13
    · exact (p.adjacent 2).symm
    · exact h02.symm)
  refine ⟨q, eq_of_subset_of_card_le ?_ ?_⟩
  · intro x hx
    obtain ⟨i, rfl⟩ := (Quadrilateral.mem_support q x).mp hx
    exact (mem_support p _).mpr ⟨e i, rfl⟩
  · simp

/-- With no cycle on the remainder, its only possible extra edges are
the two distance-two edges, and at most one of them can occur. -/
lemma missing_edges (p : FourPath G) (hn : ¬QuadOn G p.support) :
    ¬G.Adj (p.vertices 0) (p.vertices 3) ∧
      ¬(G.Adj (p.vertices 0) (p.vertices 2) ∧
        G.Adj (p.vertices 1) (p.vertices 3)) := by
  exact ⟨fun h ↦ hn (p.quad_of_endpoints h.symm),
    fun h ↦ hn (p.quad_of_diagonals h.1 h.2)⟩

end FourPath

namespace BlockPartition

variable [Fintype V] {s : Finset V}

lemma no_quad_remainder (p : BlockPartition G (univ \ s))
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k) : ¬QuadOn G s := by
  intro hq
  let q := (single hq).union p disjoint_sdiff_self_right
  apply hn
  apply q.hasPacking_of_card k
  rw [union_sdiff_self_eq_union, union_eq_right.mpr (subset_univ _), card_univ, hcard]

end BlockPartition

/-- There is an actual triangle contained in the specified vertex set. -/
def TriangleIn (G : SimpleGraph V) (s : Finset V) : Prop :=
  ∃ t ⊆ s, G.IsNClique 3 t

namespace TriangleChain

variable [Fintype V]

/-- Assemble the finite chain data from a triangle and a partition of its
four-vertex remainder's complement. -/
def ofPartition {x : V} {t : Finset V} (ht : G.IsNClique 3 t) (hx : x ∉ t)
    (p : BlockPartition G (univ \ insert x t)) : TriangleChain G :=
  ⟨⟨x, t, p.blocks⟩, {
    triangle_clique := ht
    terminal_not_mem := hx
    blocks_quad := p.quad
    blocks_disjoint := p.disjoint
    remainder_disjoint := by
      change Disjoint (insert x t) (p.blocks.biUnion id)
      rw [p.cover]
      exact disjoint_sdiff_self_right
    cover := by
      change insert x t ∪ p.blocks.biUnion id = univ
      rw [p.cover, union_sdiff_self_eq_union, union_eq_right.mpr (subset_univ _)] }⟩

lemma exists_of_triangle {s : Finset V} (hs : s.card = 4)
    (p : BlockPartition G (univ \ s)) (ht : TriangleIn G s) :
    Nonempty (TriangleChain G) := by
  obtain ⟨t, hts, ht⟩ := ht
  have hd : (s \ t).card = 1 := by rw [card_sdiff_of_subset hts, hs, ht.card_eq]
  obtain ⟨x, hx⟩ := card_eq_one.mp hd
  have hxm : x ∈ s \ t := by rw [hx]; exact mem_singleton_self _
  have he : insert x t = s := by
    calc
      insert x t = t ∪ {x} := by ext v; simp
      _ = t ∪ (s \ t) := by rw [hx]
      _ = s := union_sdiff_of_subset hts
  have hp : BlockPartition G (univ \ insert x t) := he.symm ▸ p
  exact ⟨ofPartition ht (mem_sdiff.mp hxm).2 hp⟩

end TriangleChain

namespace FourPath

lemma triangle_of_first_diagonal (p : FourPath G)
    (h : G.Adj (p.vertices 0) (p.vertices 2)) : TriangleIn G p.support := by
  refine ⟨{p.vertices 0, p.vertices 1, p.vertices 2}, ?_,
    SimpleGraph.is3Clique_triple_iff.mpr ⟨p.adjacent 0, h, p.adjacent 1⟩⟩
  rw [p.support_eq]
  intro v hv
  simp only [mem_insert, mem_singleton] at hv ⊢
  tauto

lemma triangle_of_second_diagonal (p : FourPath G)
    (h : G.Adj (p.vertices 1) (p.vertices 3)) : TriangleIn G p.support := by
  refine ⟨{p.vertices 1, p.vertices 2, p.vertices 3}, ?_,
    SimpleGraph.is3Clique_triple_iff.mpr ⟨p.adjacent 1, h, p.adjacent 2⟩⟩
  rw [p.support_eq]
  intro v hv
  simp only [mem_insert, mem_singleton] at hv ⊢
  tauto

lemma induced_adj_iff (p : FourPath G) (hq : ¬QuadOn G p.support)
    (ht : ¬TriangleIn G p.support) (i j : Fin 4) :
    G.Adj (p.vertices i) (p.vertices j) ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val := by
  have h03 := (p.missing_edges hq).1
  have h30 : ¬G.Adj (p.vertices 3) (p.vertices 0) := fun h ↦ h03 h.symm
  have h02 : ¬G.Adj (p.vertices 0) (p.vertices 2) :=
    fun h ↦ ht (p.triangle_of_first_diagonal h)
  have h20 : ¬G.Adj (p.vertices 2) (p.vertices 0) := fun h ↦ h02 h.symm
  have h13 : ¬G.Adj (p.vertices 1) (p.vertices 3) :=
    fun h ↦ ht (p.triangle_of_second_diagonal h)
  have h31 : ¬G.Adj (p.vertices 3) (p.vertices 1) := fun h ↦ h13 h.symm
  have h01 := p.adjacent 0
  have h12 := p.adjacent 1
  have h23 := p.adjacent 2
  have h10 := h01.symm
  have h21 := h12.symm
  have h32 := h23.symm
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.reduceFinMk, Nat.reduceAdd, Nat.reduceEqDiff,
      or_self, or_false, false_or, iff_true, iff_false] <;>
    first | assumption | exact G.irrefl

variable [DecidableRel G.Adj]

lemma internal_contacts (p : FourPath G) (hq : ¬QuadOn G p.support)
    (ht : ¬TriangleIn G p.support) : contacts G p.support p.support = 6 := by
  rw [support, contacts_image_left G _ _ p.vertices.injective]
  simp_rw [degreeIn_image G _ _ _ p.vertices.injective, p.induced_adj_iff hq ht]
  decide

end FourPath

namespace BlockPartition

variable [Fintype V] [DecidableRel G.Adj]

/-- The degree sum forces a block with at least nine contacts from an
induced path remainder, including when an empty block family is excluded. -/
lemma exists_path_heavy_block (p : FourPath G)
    (b : BlockPartition G (univ \ p.support))
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v)
    (hn : ¬HasPacking G k) (ht : ¬TriangleIn G p.support) :
    ∃ q ∈ b.blocks, 9 ≤ contacts G p.support q := by
  have hq := b.no_quad_remainder hcard hn
  have hi := p.internal_contacts hq ht
  have hc := b.card
  rw [card_sdiff_of_subset (subset_univ _), card_univ, p.card_support, hcard] at hc
  have hpos : 1 ≤ k := by
    by_contra hh
    have hk : k = 0 := by omega
    exact hn (hk ▸ hasPacking_zero G)
  have hsum := minimum_degree_sum G p.support (2 * k) (fun v _ ↦ hdeg v)
  rw [p.card_support] at hsum
  have hcover : p.support ∪ b.blocks.biUnion id = univ := by
    rw [b.cover, union_sdiff_self_eq_union, union_eq_right.mpr (subset_univ _)]
  have hd : Disjoint p.support (b.blocks.biUnion id) := by
    rw [b.cover]
    exact disjoint_sdiff_self_right
  rw [← hcover, contacts_union_right G _ hd,
    contacts_biUnion_right G _ _ _ b.disjoint, hi] at hsum
  obtain ⟨q, hqb, hq9⟩ := exists_heavy_block G p.support b.blocks id 8 (by omega)
  exact ⟨q, hqb, Nat.succ_le_of_lt hq9⟩

end BlockPartition

end Erdos577
