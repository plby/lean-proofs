/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

/-!
# Vertex 2-connectivity and cycle-linkage bookkeeping for Erdős Problem 58

This file deliberately keeps the usual deletion definition of vertex
2-connectivity separate from the conclusion of the two-path form of Menger's
theorem.  `TwoLinkage` is the finite certificate delivered by that theorem.

The last section contains the length and parity calculation used when two
vertex-disjoint cycles are joined by a `TwoLinkage`: of the parallel and
crossed pairings, exactly one consists of odd closed walks, and the sum of the
two lengths in either pairing is the sum of the old cycle lengths plus twice
the total length of the linking paths.
-/

namespace Erdos58

open SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V}

/-- The standard finite-graph definition of vertex 2-connectivity: there are
at least three vertices, the graph is connected, and deleting any one vertex
leaves a connected graph. -/
def TwoConnected (G : SimpleGraph V) : Prop :=
  3 ≤ Fintype.card V ∧ G.Connected ∧
    ∀ v : V, (G.induce ({v}ᶜ : Set V)).Connected

namespace TwoConnected

theorem card_three_le (hG : TwoConnected G) : 3 ≤ Fintype.card V := hG.1

theorem connected (hG : TwoConnected G) : G.Connected := hG.2.1

theorem delete_connected (hG : TwoConnected G) (v : V) :
    (G.induce ({v}ᶜ : Set V)).Connected :=
  hG.2.2 v

theorem nontrivial (hG : TwoConnected G) : Nontrivial V := by
  exact Fintype.one_lt_card_iff_nontrivial.mp (by
    have h := hG.card_three_le
    omega)

theorem exists_ne (hG : TwoConnected G) (v : V) : ∃ w : V, w ≠ v := by
  let := hG.nontrivial
  exact _root_.exists_ne v

theorem exists_two_ne (hG : TwoConnected G) (v : V) :
    ∃ x y : V, x ≠ v ∧ y ≠ v ∧ x ≠ y := by
  have hcard : 2 ≤ Fintype.card ({v}ᶜ : Set V) := by
    rw [Fintype.card_compl_set, Set.card_singleton]
    have h := hG.card_three_le
    omega
  let : Nontrivial ({v}ᶜ : Set V) :=
    Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨x, y, hxy⟩ := exists_pair_ne ({v}ᶜ : Set V)
  have hx : (x : V) ≠ v := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using x.2
  have hy : (y : V) ≠ v := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using y.2
  exact ⟨x, y, hx, hy, fun h ↦ hxy (Subtype.ext h)⟩

/-- In a 2-connected graph, any two vertices other than `z` can be joined by
a simple path avoiding `z`.  This is the direct path-level content of the
connectivity of `G - z`. -/
theorem exists_path_avoiding (hG : TwoConnected G) (z : V) {x y : V}
    (hx : x ≠ z) (hy : y ≠ z) :
    ∃ p : G.Walk x y, p.IsPath ∧ z ∉ p.support := by
  let x' : ({z}ᶜ : Set V) := ⟨x, hx⟩
  let y' : ({z}ᶜ : Set V) := ⟨y, hy⟩
  obtain ⟨p, hp⟩ := (hG.delete_connected z).exists_isPath x' y'
  let e : G.induce ({z}ᶜ : Set V) ↪g G :=
    SimpleGraph.Embedding.induce ({z}ᶜ : Set V)
  let q := p.map e.toHom
  have hqpath : q.IsPath := hp.map e.injective
  have hqavoid : z ∉ q.support := by
    intro hz
    have hsupport : q.support = p.support.map e := by
      exact SimpleGraph.Walk.support_map e.toHom p
    rw [hsupport, List.mem_map] at hz
    obtain ⟨w, hw, hwz⟩ := hz
    have hwne : (w : V) ≠ z := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using w.2
    exact hwne hwz
  have hex : e x' = x := by rfl
  have hey : e y' = y := by rfl
  let q' : G.Walk x y := q.copy hex hey
  have hq'path : q'.IsPath :=
    (SimpleGraph.Walk.isPath_copy q hex hey).2 hqpath
  have hq'avoid : z ∉ q'.support := by
    simpa only [q', SimpleGraph.Walk.support_copy] using hqavoid
  exact ⟨q', hq'path, hq'avoid⟩

/-- Any two distinct neighbors of a vertex in a 2-connected graph lie with
that vertex on a simple cycle.  This is a useful rigorously proved special
linkage consequence which needs only one application of
`exists_path_avoiding`, rather than the full two-set Menger theorem. -/
theorem exists_cycle_through_two_neighbors (hG : TwoConnected G)
    {x y z : V} (hxy : G.Adj x y) (hxz : G.Adj x z) (hyz : y ≠ z) :
    ∃ c : G.Walk x x, c.IsCycle := by
  obtain ⟨p, hp, hpx⟩ :=
    hG.exists_path_avoiding x hxy.ne.symm hxz.ne.symm
  let q : G.Walk y x := p.concat hxz.symm
  have hq : q.IsPath := hp.concat hpx hxz.symm
  have hedge : s(x, y) ∉ q.edges := by
    intro hedge
    have hedge' : s(y, x) ∈ q.edges := by
      simpa only [Sym2.eq_swap] using hedge
    have hlen : q.length = 1 := hq.length_eq_one_of_mem_edges hedge'
    have hplen : p.length = 0 := by
      have hq_length : q.length = p.length + 1 := by simp [q]
      omega
    exact hyz (p.eq_of_length_eq_zero hplen)
  exact ⟨Walk.cons hxy q, (Walk.cons_isCycle_iff q hxy).2 ⟨hq, hedge⟩⟩

end TwoConnected

/-! ## Two-linkage certificates -/

/-- A certificate consisting of two fully vertex-disjoint paths from `A` to
`B`.  Disjointness of their complete supports implies, in particular, that
the two endpoints in `A` are distinct and the two endpoints in `B` are
distinct.  The `interior` fields record the usual truncation convention in
the set form of Menger's theorem. -/
structure TwoLinkage (G : SimpleGraph V) (A B : Set V) where
  a₁ : V
  a₂ : V
  b₁ : V
  b₂ : V
  p : G.Walk a₁ b₁
  q : G.Walk a₂ b₂
  p_isPath : p.IsPath
  q_isPath : q.IsPath
  a₁_mem : a₁ ∈ A
  a₂_mem : a₂ ∈ A
  b₁_mem : b₁ ∈ B
  b₂_mem : b₂ ∈ B
  disjoint_support : p.support.Disjoint q.support
  p_interior : ∀ x ∈ p.support.tail.dropLast, x ∉ A ∪ B
  q_interior : ∀ x ∈ q.support.tail.dropLast, x ∉ A ∪ B

namespace TwoLinkage

variable {A B : Set V}

theorem a_ne (L : TwoLinkage G A B) : L.a₁ ≠ L.a₂ := by
  intro h
  exact L.disjoint_support L.p.start_mem_support (h.symm ▸ L.q.start_mem_support)

theorem b_ne (L : TwoLinkage G A B) : L.b₁ ≠ L.b₂ := by
  intro h
  exact L.disjoint_support L.p.end_mem_support (h.symm ▸ L.q.end_mem_support)

theorem p_nonempty (L : TwoLinkage G A B) (hAB : Disjoint A B) : 0 < L.p.length := by
  by_contra h
  have hp0 : L.p.length = 0 := by omega
  have hab : L.a₁ = L.b₁ := L.p.eq_of_length_eq_zero hp0
  exact Set.disjoint_left.1 hAB L.a₁_mem (hab.symm ▸ L.b₁_mem)

theorem q_nonempty (L : TwoLinkage G A B) (hAB : Disjoint A B) : 0 < L.q.length := by
  by_contra h
  have hq0 : L.q.length = 0 := by omega
  have hab : L.a₂ = L.b₂ := L.q.eq_of_length_eq_zero hq0
  exact Set.disjoint_left.1 hAB L.a₂_mem (hab.symm ▸ L.b₂_mem)

theorem total_length_pos (L : TwoLinkage G A B) (hAB : Disjoint A B) :
    0 < L.p.length + L.q.length := by
  have hp := L.p_nonempty hAB
  omega

end TwoLinkage

/-! ## The four closed walks obtained by splicing two cycles -/

/-- Data needed for the purely formal splicing calculation.  The walks `c₁`
and `c₂` are the complementary `a₁`--`a₂` arcs of the first cycle; `d₁` and
`d₂` are the complementary `b₁`--`b₂` arcs of the second.  They are stored
with a common orientation so that reversing them closes the linking paths. -/
structure SpliceData (G : SimpleGraph V) where
  a₁ : V
  a₂ : V
  b₁ : V
  b₂ : V
  p : G.Walk a₁ b₁
  q : G.Walk a₂ b₂
  c₁ : G.Walk a₁ a₂
  c₂ : G.Walk a₁ a₂
  d₁ : G.Walk b₁ b₂
  d₂ : G.Walk b₁ b₂

namespace SpliceData

/-- Close `p` using a second linking path and one arc from each old cycle. -/
def close {a₁ a₂ b₁ b₂ : V} (p : G.Walk a₁ b₁) (d : G.Walk b₁ b₂)
    (q : G.Walk a₂ b₂) (c : G.Walk a₁ a₂) : G.Walk a₁ a₁ :=
  ((p.append d).append q.reverse).append c.reverse

variable (S : SpliceData G)

def parallel₁ : G.Walk S.a₁ S.a₁ := close S.p S.d₁ S.q S.c₁
def parallel₂ : G.Walk S.a₁ S.a₁ := close S.p S.d₂ S.q S.c₂
def crossed₁ : G.Walk S.a₁ S.a₁ := close S.p S.d₂ S.q S.c₁
def crossed₂ : G.Walk S.a₁ S.a₁ := close S.p S.d₁ S.q S.c₂

/-- The remaining geometric obligation after the length/parity calculation:
the four closed walks produced by the two arc pairings are simple cycles. -/
def SplicesAreCycles : Prop :=
  S.parallel₁.IsCycle ∧ S.parallel₂.IsCycle ∧
    S.crossed₁.IsCycle ∧ S.crossed₂.IsCycle

@[simp] theorem length_close {a₁ a₂ b₁ b₂ : V}
    (p : G.Walk a₁ b₁) (d : G.Walk b₁ b₂)
    (q : G.Walk a₂ b₂) (c : G.Walk a₁ a₂) :
    (close p d q c).length = p.length + d.length + q.length + c.length := by
  simp [close]

@[simp] theorem length_parallel₁ :
    S.parallel₁.length = S.p.length + S.d₁.length + S.q.length + S.c₁.length := by
  simp [parallel₁]

@[simp] theorem length_parallel₂ :
    S.parallel₂.length = S.p.length + S.d₂.length + S.q.length + S.c₂.length := by
  simp [parallel₂]

@[simp] theorem length_crossed₁ :
    S.crossed₁.length = S.p.length + S.d₂.length + S.q.length + S.c₁.length := by
  simp [crossed₁]

@[simp] theorem length_crossed₂ :
    S.crossed₂.length = S.p.length + S.d₁.length + S.q.length + S.c₂.length := by
  simp [crossed₂]

/-- The sum of the two parallel splices. -/
theorem parallel_sum {cLen dLen : ℕ}
    (hc : S.c₁.length + S.c₂.length = cLen)
    (hd : S.d₁.length + S.d₂.length = dLen) :
    S.parallel₁.length + S.parallel₂.length =
      cLen + dLen + 2 * (S.p.length + S.q.length) := by
  simp only [length_parallel₁, length_parallel₂]
  omega

/-- The crossed pairing has the same total length as the parallel pairing. -/
theorem crossed_sum {cLen dLen : ℕ}
    (hc : S.c₁.length + S.c₂.length = cLen)
    (hd : S.d₁.length + S.d₂.length = dLen) :
    S.crossed₁.length + S.crossed₂.length =
      cLen + dLen + 2 * (S.p.length + S.q.length) := by
  simp only [length_crossed₁, length_crossed₂]
  omega

/-- If the two old cycles are odd, the two members of each pairing have the
same parity. -/
theorem parallel_same_parity
    (hc : Odd (S.c₁.length + S.c₂.length))
    (hd : Odd (S.d₁.length + S.d₂.length)) :
    (Odd S.parallel₁.length ↔ Odd S.parallel₂.length) := by
  simp only [length_parallel₁, length_parallel₂]
  simp only [Nat.odd_iff] at hc hd ⊢
  omega

theorem crossed_same_parity
    (hc : Odd (S.c₁.length + S.c₂.length))
    (hd : Odd (S.d₁.length + S.d₂.length)) :
    (Odd S.crossed₁.length ↔ Odd S.crossed₂.length) := by
  simp only [length_crossed₁, length_crossed₂]
  simp only [Nat.odd_iff] at hc hd ⊢
  omega

/-- Exactly one of the parallel and crossed first splices is odd. -/
theorem odd_parallel₁_iff_not_odd_crossed₁
    (hd : Odd (S.d₁.length + S.d₂.length)) :
    (Odd S.parallel₁.length ↔ ¬ Odd S.crossed₁.length) := by
  simp only [length_parallel₁, length_crossed₁]
  simp only [Nat.odd_iff] at hd ⊢
  omega

/-- Consequently one of the two pairings consists of two odd closed walks. -/
theorem odd_pairing
    (hc : Odd (S.c₁.length + S.c₂.length))
    (hd : Odd (S.d₁.length + S.d₂.length)) :
    (Odd S.parallel₁.length ∧ Odd S.parallel₂.length) ∨
      (Odd S.crossed₁.length ∧ Odd S.crossed₂.length) := by
  have hp := S.parallel_same_parity hc hd
  have hx := S.crossed_same_parity hc hd
  have hpx := S.odd_parallel₁_iff_not_odd_crossed₁ hd
  by_cases h₁ : Odd S.parallel₁.length
  · exact Or.inl ⟨h₁, hp.mp h₁⟩
  · have h₂ : Odd S.crossed₁.length := by tauto
    exact Or.inr ⟨h₂, hx.mp h₂⟩

/-- If the second old cycle is at least as long as the first and the linking
paths have positive total length, then in each pairing at least one new
closed walk is strictly longer than the first old cycle. -/
theorem parallel_one_longer {cLen dLen : ℕ}
    (hc : S.c₁.length + S.c₂.length = cLen)
    (hd : S.d₁.length + S.d₂.length = dLen) (hcd : cLen ≤ dLen)
    (hlink : 0 < S.p.length + S.q.length) :
    cLen < S.parallel₁.length ∨ cLen < S.parallel₂.length := by
  have hsum := S.parallel_sum hc hd
  omega

theorem crossed_one_longer {cLen dLen : ℕ}
    (hc : S.c₁.length + S.c₂.length = cLen)
    (hd : S.d₁.length + S.d₂.length = dLen) (hcd : cLen ≤ dLen)
    (hlink : 0 < S.p.length + S.q.length) :
    cLen < S.crossed₁.length ∨ cLen < S.crossed₂.length := by
  have hsum := S.crossed_sum hc hd
  omega

/-- The exact conclusion needed in the longest-odd-cycle argument, once the
four spliced closed walks have separately been shown to be simple cycles. -/
theorem exists_odd_longer_splice
    {cLen dLen : ℕ}
    (hc : S.c₁.length + S.c₂.length = cLen)
    (hd : S.d₁.length + S.d₂.length = dLen)
    (hcodd : Odd cLen) (hdodd : Odd dLen)
    (hcd : cLen ≤ dLen) (hlink : 0 < S.p.length + S.q.length) :
    (Odd S.parallel₁.length ∧ cLen < S.parallel₁.length) ∨
      (Odd S.parallel₂.length ∧ cLen < S.parallel₂.length) ∨
      (Odd S.crossed₁.length ∧ cLen < S.crossed₁.length) ∨
      (Odd S.crossed₂.length ∧ cLen < S.crossed₂.length) := by
  have hcp : Odd (S.c₁.length + S.c₂.length) := hc ▸ hcodd
  have hdp : Odd (S.d₁.length + S.d₂.length) := hd ▸ hdodd
  rcases S.odd_pairing hcp hdp with hp | hx
  · rcases S.parallel_one_longer hc hd hcd hlink with h₁ | h₂
    · exact Or.inl ⟨hp.1, h₁⟩
    · exact Or.inr (Or.inl ⟨hp.2, h₂⟩)
  · rcases S.crossed_one_longer hc hd hcd hlink with h₁ | h₂
    · exact Or.inr (Or.inr (Or.inl ⟨hx.1, h₁⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨hx.2, h₂⟩))

/-- Cycle-valued form of `exists_odd_longer_splice`.  It cleanly separates
the finite support-disjointness argument (`SplicesAreCycles`) from the
universal arithmetic/parity argument proved above. -/
theorem exists_odd_longer_cycle
    {cLen dLen : ℕ}
    (hcycles : S.SplicesAreCycles)
    (hc : S.c₁.length + S.c₂.length = cLen)
    (hd : S.d₁.length + S.d₂.length = dLen)
    (hcodd : Odd cLen) (hdodd : Odd dLen)
    (hcd : cLen ≤ dLen) (hlink : 0 < S.p.length + S.q.length) :
    ∃ c : G.Walk S.a₁ S.a₁,
      c.IsCycle ∧ Odd c.length ∧ cLen < c.length := by
  rcases S.exists_odd_longer_splice hc hd hcodd hdodd hcd hlink with
    h | h | h | h
  · exact ⟨S.parallel₁, hcycles.1, h.1, h.2⟩
  · exact ⟨S.parallel₂, hcycles.2.1, h.1, h.2⟩
  · exact ⟨S.crossed₁, hcycles.2.2.1, h.1, h.2⟩
  · exact ⟨S.crossed₂, hcycles.2.2.2, h.1, h.2⟩

end SpliceData

end Erdos58
