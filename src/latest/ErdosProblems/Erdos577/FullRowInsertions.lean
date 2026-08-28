import ErdosProblems.Erdos577.FullRowFirstBlock

/-! All six neighbor-pair insertions and their actual common-neighbor replacement consequence. -/

namespace Erdos577.FullRow

open Finset

namespace PairTable

def first : Fin 6 → Fin 4 := ![0, 0, 0, 1, 1, 2]
def second : Fin 6 → Fin 4 := ![1, 2, 3, 2, 3, 3]
def removed : Fin 6 → Fin 4 := ![2, 1, 2, 0, 0, 0]
def middle : Fin 6 → Fin 4 := ![3, 3, 1, 3, 2, 1]

lemma coverage (i j : Fin 4) (hij : i ≠ j) :
    ∃ tag : Fin 6, (first tag = i ∧ second tag = j) ∨ (first tag = j ∧ second tag = i) := by
  have hh : ∀ i j : Fin 4, i ≠ j →
      ∃ tag : Fin 6, (first tag = i ∧ second tag = j) ∨ (first tag = j ∧ second tag = i) := by
    decide +kernel
  exact hh i j hij

lemma removed_ne_three (tag : Fin 6) : removed tag ≠ 3 := by fin_cases tag <;> decide +kernel

lemma first_ne_second (tag : Fin 6) : first tag ≠ second tag := by
  fin_cases tag <;> decide +kernel

lemma cover (tag : Fin 6) :
    ({first tag, middle tag, second tag} : Finset (Fin 4)) = univ.erase (removed tag) := by
  fin_cases tag <;> decide +kernel

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

omit [DecidableEq V] in
lemma path_edges (q : Quadrilateral G) (hd : G.Adj (q 1) (q 3)) (tag : Fin 6) :
    G.Adj (q (first tag)) (q (middle tag)) ∧ G.Adj (q (middle tag)) (q (second tag)) := by
  fin_cases tag
  · exact ⟨(q.adjacent 3).symm, hd.symm⟩
  · exact ⟨(q.adjacent 3).symm, (q.adjacent 2).symm⟩
  · exact ⟨q.adjacent 0, hd⟩
  · exact ⟨hd, (q.adjacent 2).symm⟩
  · exact ⟨q.adjacent 1, q.adjacent 2⟩
  · exact ⟨(q.adjacent 1).symm, hd⟩

lemma replacement (q : Quadrilateral G) (z : V) (hz : z ∉ q.support)
    (hd : G.Adj (q 1) (q 3)) (tag : Fin 6)
    (hfirst : G.Adj z (q (first tag))) (hsecond : G.Adj z (q (second tag))) :
    QuadOn G (insert z (q.support.erase (q (removed tag)))) :=
  q.replace_using_path z hz (removed tag) (first tag) (middle tag) (second tag)
    (first_ne_second tag) (cover tag) hfirst (path_edges q hd tag).1 (path_edges q hd tag).2 hsecond

end PairTable

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma replacement_in_first_three (q : Quadrilateral G) (z : V) (hz : z ∉ q.support)
    (hd : G.Adj (q 1) (q 3)) (hrow : 2 ≤ degreeIn G z q.support) :
    ∃ i : Fin 4, i ≠ 3 ∧ QuadOn G (insert z (q.support.erase (q i))) := by
  obtain ⟨i, j, hij, hi, hj⟩ := q.exists_two_neighbor_indices z hrow
  obtain ⟨tag, he⟩ := PairTable.coverage i j hij
  refine ⟨PairTable.removed tag, PairTable.removed_ne_three tag, ?_⟩
  apply PairTable.replacement q z hz hd tag
  · rcases he with ⟨hfirst, _⟩ | ⟨hfirst, _⟩
    · rwa [hfirst]
    · rwa [hfirst]
  · rcases he with ⟨_, hsecond⟩ | ⟨_, hsecond⟩
    · rwa [hsecond]
    · rwa [hsecond]

lemma common_set_card (q : Quadrilateral G) (x y : V)
    (hseven : 7 ≤ degreeIn G x q.support + degreeIn G y q.support) :
    3 ≤ (q.support.filter (G.Adj x) ∩ q.support.filter (G.Adj y)).card := by
  have hsum := card_union_add_card_inter (q.support.filter (G.Adj x))
    (q.support.filter (G.Adj y))
  have hbound : (q.support.filter (G.Adj x) ∪ q.support.filter (G.Adj y)).card ≤ 4 :=
    (card_le_card (union_subset (filter_subset _ _) (filter_subset _ _))).trans_eq q.card_support
  change 7 ≤ (q.support.filter (G.Adj x)).card + (q.support.filter (G.Adj y)).card at hseven
  omega

variable [Fintype V]

theorem common_insertion {c : TriangleChain G} (hc : c.Feasible)
    (p : Paw G) (hp : p.support = c.remainder)
    {s : Finset V} (hs : s ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = s)
    (hleaf : ∀ j : Fin 4, j ≠ 3 → G.Adj p.leaf (q j))
    (hseven : 7 ≤ degreeIn G p.leaf q.support + degreeIn G (p.vertices 2) q.support)
    (z : V) (hz : z ∉ q.support) (hrow : 2 ≤ degreeIn G z q.support) :
    CommonReplacement G p.leaf (p.vertices 2) z q.support := by
  rcases row_dichotomy hc p hp hs q hq hleaf hseven with ⟨hcl, _⟩ | ⟨_, hb⟩
  · let t := q.support.filter (G.Adj p.leaf) ∩ q.support.filter (G.Adj (p.vertices 2))
    have ht : t ⊆ q.support := fun u hu ↦ (mem_filter.mp (mem_inter.mp hu).1).1
    obtain ⟨u, hu, hr⟩ := clique_replace_in_three_candidates hcl z hz hrow t ht
      (common_set_card q p.leaf (p.vertices 2) hseven)
    exact ⟨u, ht hu, (mem_filter.mp (mem_inter.mp hu).1).2,
      (mem_filter.mp (mem_inter.mp hu).2).2, hr⟩
  · obtain ⟨i, hi, hr⟩ := replacement_in_first_three q z hz
      (last_diagonal hc p hp hs q hq hleaf) hrow
    have hm : q i ∈ q.support := (q.mem_support _).mpr ⟨i, rfl⟩
    have hfull := (degreeIn_eq_card_iff (p.vertices 2) q.support).mp
      (hb.trans q.card_support.symm)
    exact ⟨q i, hm, hleaf i hi, hfull (q i) hm, hr⟩

end Erdos577.FullRow
