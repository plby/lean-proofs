import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Tactic

open scoped Sym2

namespace Erdos1018Aux

open Function Finset
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- An endpoint of a longest path has all of its neighbours on the path. -/
lemma longestPath_neighbor_mem_support_end
    {a b : V} {p : G.Walk a b}
    (hp : p.IsPath)
    (hmax : ∀ (u v : V) (q : G.Walk u v), q.IsPath → q.length ≤ p.length)
    {x : V} (hbx : G.Adj b x) : x ∈ p.support := by
  by_contra hx
  have hpath : (p.concat hbx).IsPath := hp.concat hx hbx
  have hle := hmax a x (p.concat hbx) hpath
  simp at hle

/-- A longest path has length at least the minimum degree. -/
lemma exists_path_minDegree_le_length [Nonempty V] :
    ∃ (a b : V) (p : G.Walk a b), p.IsPath ∧ G.minDegree ≤ p.length := by
  obtain ⟨a, b, p, hp, hmax⟩ :=
    SimpleGraph.Walk.exists_isPath_forall_isPath_length_le_length G
  refine ⟨a, b, p, hp, ?_⟩
  have hsub : G.neighborFinset b ⊆ p.support.toFinset.erase b := by
    intro x hx
    have hxb : G.Adj b x := (SimpleGraph.mem_neighborFinset G b x).mp hx
    have hxs : x ∈ p.support := longestPath_neighbor_mem_support_end G hp hmax hxb
    exact Finset.mem_erase.mpr ⟨hxb.ne.symm, List.mem_toFinset.mpr hxs⟩
  calc
    G.minDegree ≤ G.degree b := G.minDegree_le_degree b
    _ = #(G.neighborFinset b) := (G.card_neighborFinset_eq_degree b).symm
    _ ≤ #(p.support.toFinset.erase b) := Finset.card_le_card hsub
    _ = p.length := by
      rw [Finset.card_erase_of_mem]
      · rw [List.toFinset_card_of_nodup hp.support_nodup, p.length_support]
        omega
      · exact List.mem_toFinset.mpr p.end_mem_support

/-- Minimum degree nine supplies a simple path with ten distinct vertices. -/
lemma exists_path_length_nine [Nonempty V] (hmin : 9 ≤ G.minDegree) :
    ∃ (a b : V) (p : G.Walk a b), p.IsPath ∧ 9 ≤ p.length := by
  obtain ⟨a, b, p, hp, hlen⟩ := exists_path_minDegree_le_length G
  exact ⟨a, b, p, hp, hmin.trans hlen⟩

/-- Removing a vertex after inducing on `S` is canonically the same graph
as first erasing the vertex from `S` and then inducing. -/
def induceEraseIso (S : Finset V) {v : V} (hv : v ∈ S) :
    G.induce (S.erase v : Set V) ≃g
      (G.induce (S : Set V)).induce ({(⟨v, hv⟩ : (S : Set V))}ᶜ) where
  toFun x := ⟨⟨x.1, Finset.mem_of_mem_erase x.2⟩, by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, Subtype.ext_iff,
      ne_eq] using (Finset.ne_of_mem_erase x.2)⟩
  invFun x := ⟨x.1.1, Finset.mem_erase.mpr ⟨by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, Subtype.ext_iff,
      ne_eq] using x.2, x.1.2⟩⟩
  left_inv x := rfl
  right_inv x := rfl
  map_rel_iff' := by simp

/-- Exact edge count after erasing one vertex from an induced vertex set. -/
lemma card_edges_induce_erase (S : Finset V) {v : V} (hv : v ∈ S) :
    #(G.induce (S.erase v : Set V)).edgeFinset =
      #(G.induce (S : Set V)).edgeFinset -
        (G.induce (S : Set V)).degree ⟨v, hv⟩ := by
  rw [(induceEraseIso G S hv).card_edgeFinset_eq]
  rw [(G.induce (S : Set V)).card_edgeFinset_induce_compl_singleton ⟨v, hv⟩]
  exact (G.induce (S : Set V)).card_edgeFinset_deleteIncidenceSet ⟨v, hv⟩

/-- The subtype cut out by the finite universal set is equivalent to the
original vertex type. -/
def induceFinsetUnivIso :
    G.induce ((Finset.univ : Finset V) : Set V) ≃g G where
  toFun x := x.1
  invFun x := ⟨x, Finset.mem_univ x⟩
  left_inv x := rfl
  right_inv x := rfl
  map_rel_iff' := Iff.rfl

/-- More than `8|V|` edges give an induced subgraph of minimum degree at
least nine (the standard minimal dense-core argument). -/
lemma exists_induced_minDegree_nine
    (hE : 8 * Fintype.card V < #G.edgeFinset) :
    ∃ S : Finset V, S.Nonempty ∧ 9 ≤ (G.induce (S : Set V)).minDegree := by
  let Good : Finset V → Prop := fun S ↦
    8 * #S < #(G.induce (S : Set V)).edgeFinset
  let _ : DecidablePred Good := Classical.decPred Good
  let candidates := (Finset.univ : Finset (Finset V)).filter Good
  have hcandidates : candidates.Nonempty := by
    refine ⟨Finset.univ, ?_⟩
    simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and, Good]
    rw [(induceFinsetUnivIso G).card_edgeFinset_eq]
    simpa using hE
  obtain ⟨S, hScand, hmincard⟩ :=
    candidates.exists_min_image Finset.card hcandidates
  have hSgood : Good S := (Finset.mem_filter.mp hScand).2
  have hScard : 0 < #S := by
    by_contra h
    have hSz : S = ∅ := Finset.card_eq_zero.mp (by omega)
    subst S
    simp only [Good, Finset.card_empty, mul_zero] at hSgood
    have hle :=
      SimpleGraph.card_edgeFinset_le_card_choose_two
        (G := G.induce (((∅ : Finset V) : Set V)))
    have hcardV : Fintype.card (((∅ : Finset V) : Set V)) = 0 := by simp
    rw [hcardV] at hle
    have hzero : #(G.induce (((∅ : Finset V) : Set V))).edgeFinset = 0 :=
      Nat.eq_zero_of_le_zero (by simpa using hle)
    exact (by omega)
  letI : Nonempty (S : Set V) := Fintype.card_pos_iff.mp (by simpa using hScard)
  refine ⟨S, Finset.card_pos.mp hScard,
    (G.induce (S : Set V)).le_minDegree_of_forall_le_degree 9 ?_⟩
  intro x
  by_contra hdeg
  have hdeg8 : (G.induce (S : Set V)).degree x ≤ 8 := by omega
  have heraseGood : Good (S.erase x.1) := by
    simp only [Good]
    rw [card_edges_induce_erase G S x.2, Finset.card_erase_of_mem x.2]
    change 8 * (#S - 1) < #(G.induce (S : Set V)).edgeFinset -
      (G.induce (S : Set V)).degree x
    dsimp only [Good] at hSgood
    have hdegEdge : (G.induce (S : Set V)).degree x ≤
        #(G.induce (S : Set V)).edgeFinset :=
      (G.induce (S : Set V)).degree_le_card_edgeFinset (v := x)
    have hsplit := Nat.sub_add_cancel hdegEdge
    omega
  have heraseCand : S.erase x.1 ∈ candidates :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, heraseGood⟩
  have hcardmin := hmincard (S.erase x.1) heraseCand
  rw [Finset.card_erase_of_mem x.2] at hcardmin
  omega

/-- Edge density alone supplies an induced path through ten vertices. -/
lemma exists_induced_path_length_nine
    (hE : 8 * Fintype.card V < #G.edgeFinset) :
    ∃ (S : Finset V) (a b : (S : Set V))
      (p : (G.induce (S : Set V)).Walk a b),
      p.IsPath ∧ 9 ≤ p.length := by
  obtain ⟨S, ⟨v, hv⟩, hmin⟩ := exists_induced_minDegree_nine G hE
  letI : Nonempty (S : Set V) := ⟨⟨v, hv⟩⟩
  obtain ⟨a, b, p, hp, hlen⟩ := exists_path_length_nine (G.induce (S : Set V)) hmin
  exact ⟨S, a, b, p, hp, hlen⟩

/-- The vertices at positions `0,...,4` of a path of length at least nine. -/
def firstFive {a b : V} {p : G.Walk a b} (hp : p.IsPath)
    (hlen : 9 ≤ p.length) : Fin 5 ↪ V where
  toFun i := p.getVert i.1
  inj' := by
    intro i j hij
    apply Fin.ext
    exact hp.getVert_injOn (by simp; omega) (by simp; omega) hij

/-- The vertices at positions `5,...,9` of a path of length at least nine. -/
def nextFive {a b : V} {p : G.Walk a b} (hp : p.IsPath)
    (hlen : 9 ≤ p.length) : Fin 5 ↪ V where
  toFun i := p.getVert (i.1 + 5)
  inj' := by
    intro i j hij
    apply Fin.ext
    have := hp.getVert_injOn (by simp; omega) (by simp; omega) hij
    omega

lemma firstFive_ne_nextFive {a b : V} {p : G.Walk a b} (hp : p.IsPath)
    (hlen : 9 ≤ p.length) (i j : Fin 5) :
    firstFive G hp hlen i ≠ nextFive G hp hlen j := by
  intro hij
  have hidx := hp.getVert_injOn (by simp; omega) (by simp; omega) hij
  omega

/-- Project the first block of five vertices of a path in an induced graph
back to the ambient vertex type. -/
def firstFiveAmbient (S : Finset V)
    {a b : (S : Set V)} {p : (G.induce (S : Set V)).Walk a b}
    (hp : p.IsPath) (hlen : 9 ≤ p.length) : Fin 5 ↪ V :=
  (firstFive (G.induce (S : Set V)) hp hlen).trans
    (Function.Embedding.subtype (S : Set V))

/-- Project the second block of five vertices of a path in an induced graph
back to the ambient vertex type. -/
def nextFiveAmbient (S : Finset V)
    {a b : (S : Set V)} {p : (G.induce (S : Set V)).Walk a b}
    (hp : p.IsPath) (hlen : 9 ≤ p.length) : Fin 5 ↪ V :=
  (nextFive (G.induce (S : Set V)) hp hlen).trans
    (Function.Embedding.subtype (S : Set V))

lemma firstFiveAmbient_ne_nextFiveAmbient (S : Finset V)
    {a b : (S : Set V)} {p : (G.induce (S : Set V)).Walk a b}
    (hp : p.IsPath) (hlen : 9 ≤ p.length) (i j : Fin 5) :
    firstFiveAmbient G S hp hlen i ≠ nextFiveAmbient G S hp hlen j := by
  intro hij
  change ((firstFive (G.induce (S : Set V)) hp hlen i : (S : Set V)) : V) =
    ((nextFive (G.induce (S : Set V)) hp hlen j : (S : Set V)) : V) at hij
  exact firstFive_ne_nextFive (G.induce (S : Set V)) hp hlen i j
    (Subtype.ext hij)

end Erdos1018Aux
