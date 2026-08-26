import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-!
# Bipartite graphs and odd cycles

This file proves that a graph is `2`-colorable if and only if it contains no odd cycle, which is
recorded as a TODO in `Mathlib/Combinatorics/SimpleGraph/Bipartite.lean`.

Mathlib already knows `two_colorable_iff_forall_loop_even`: a graph is `2`-colorable iff every
*closed walk* has even length. So the entire content that is missing is the passage from closed
walks to cycles:

> a closed walk of odd length yields a *cycle* of odd length.

That is `hasOddCycle_of_odd_length` below. It is proved by induction on an upper bound for the
length, peeling the first edge to write `w = cons h p`. By `Walk.cons_isCycle_iff`, `cons h p` is a
cycle exactly when `p` is a path avoiding the edge `uv`, which gives three cases:

* `p` is a path avoiding `uv`: then `w` is already an odd cycle.
* `p` is a path using `uv`: then `p` *is* that edge by `IsPath.length_eq_one_of_mem_edges`, so `w`
  has length `2`, contradicting oddness.
* `p` is not a path: some vertex repeats, and `w` splits into two strictly shorter closed walks
  whose lengths sum to `w.length`. One of them is odd, so the induction hypothesis applies.

## Main declarations

* `SimpleGraph.HasOddCycle`: `G` contains a cycle of odd length.
* `SimpleGraph.hasOddCycle_of_odd_length`: an odd closed walk yields an odd cycle.
* `SimpleGraph.colorable_two_iff_not_hasOddCycle`: `G.Colorable 2 ↔ ¬G.HasOddCycle`.
* `SimpleGraph.isBipartite_iff_not_hasOddCycle`: the same, phrased with `IsBipartite`.
-/

section

universe u

namespace SimpleGraph

variable {V : Type u} {G : SimpleGraph V}

/-- `G` contains a cycle of odd length. -/
def HasOddCycle (G : SimpleGraph V) : Prop :=
  ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ Odd c.length

/-- An odd cycle is in particular an odd closed walk. -/
theorem exists_odd_length_of_hasOddCycle (h : G.HasOddCycle) :
    ∃ (u : V) (w : G.Walk u u), Odd w.length := by
  obtain ⟨v, c, _, hodd⟩ := h
  exact ⟨v, c, hodd⟩

/-- Induction for `hasOddCycle_of_odd_length`, on an upper bound for the length of the walk. -/
private theorem hasOddCycle_aux :
    ∀ (n : ℕ) {u : V} (w : G.Walk u u), w.length ≤ n → Odd w.length → G.HasOddCycle := by
  intro n
  induction n with
  | zero =>
    intro u w hlen hodd
    rw [Nat.le_zero.1 hlen] at hodd
    simp at hodd
  | succ k ih =>
    intro u w hlen hodd
    classical
    cases w with
    | nil => simp at hodd
    | @cons _ v _ h p =>
      rw [Walk.length_cons] at hlen hodd
      by_cases hp : p.IsPath
      · by_cases he : s(u, v) ∈ p.edges
        · -- `p` is a path from `v` to `u` using the edge `uv`, so `p` *is* that edge and the closed
          -- walk has length `2`, contradicting oddness.
          exact absurd (hp.length_eq_one_of_mem_edges (Sym2.eq_swap ▸ he) ▸ hodd) (by simp)
        · -- `p` is a path avoiding `uv`, so `cons h p` is already an odd cycle.
          exact ⟨u, Walk.cons h p, (Walk.cons_isCycle_iff p h).2 ⟨hp, he⟩, by
            rwa [Walk.length_cons]⟩
      · -- `p` is not a path, so some vertex `x` occurs twice in `p.support`. Writing
        -- `p = A ++ (cons hb (C ++ D))` where `A : Walk v x`, `C : Walk _ x` and `D : Walk x u`,
        -- the two closed walks `cons hb C : Walk x x` and `cons h (A ++ D) : Walk u u` have lengths
        -- `C.length + 1` and `A.length + D.length + 1`, summing to `w.length`. Both are nonzero, so
        -- both are strictly shorter than `w`, and one of them is odd.
        rw [Walk.isPath_def] at hp
        obtain ⟨x, hdup⟩ := List.exists_duplicate_iff_not_nodup.2 hp
        have hx : x ∈ p.support := hdup.mem
        -- Split `p` at the first occurrence of `x`.
        have hspec := p.take_spec hx
        have hA1 : (p.takeUntil x hx).support.count x = 1 := p.count_support_takeUntil_eq_one hx
        -- `x` occurs again after the split, so the second piece is not `nil`.
        have hBt : 1 ≤ (p.dropUntil x hx).support.tail.count x := by
          have hsupp : p.support
              = (p.takeUntil x hx).support ++ (p.dropUntil x hx).support.tail :=
            (congrArg Walk.support hspec.symm).trans (Walk.support_append _ _)
          have hsplit : p.support.count x
              = (p.takeUntil x hx).support.count x + (p.dropUntil x hx).support.tail.count x := by
            rw [hsupp, List.count_append]
          have := List.duplicate_iff_two_le_count.1 hdup
          lia
        have hBnil : ¬(p.dropUntil x hx).Nil := by
          intro hnil
          rw [Walk.nil_iff_support_eq.1 hnil] at hBt
          simp at hBt
        obtain ⟨y, hb, Bt, hBeq⟩ := Walk.not_nil_iff.1 hBnil
        have hx2 : x ∈ Bt.support := by
          have hsupp : (p.dropUntil x hx).support.tail = Bt.support := by rw [hBeq]; simp
          rw [hsupp] at hBt
          exact List.count_pos_iff.1 (by lia)
        -- Split the second piece again at the next occurrence of `x`.
        have hspec2 := Bt.take_spec hx2
        -- Length bookkeeping: the two loops partition the length of `w`.
        have hlenp : p.length
            = (p.takeUntil x hx).length + (p.dropUntil x hx).length :=
          (congrArg Walk.length hspec.symm).trans (Walk.length_append _ _)
        have hlenB : (p.dropUntil x hx).length = Bt.length + 1 := by rw [hBeq]; simp
        have hlenBt : (Bt.takeUntil x hx2).length + (Bt.dropUntil x hx2).length = Bt.length :=
          ((Walk.length_append _ _).symm.trans (congrArg Walk.length hspec2))
        rcases Nat.even_or_odd (Walk.cons hb (Bt.takeUntil x hx2)).length with hev | hod
        · -- The loop through `x` is even, so the loop through `u` is odd.
          refine ih (Walk.cons h ((p.takeUntil x hx).append (Bt.dropUntil x hx2))) ?_ ?_
          · simp only [Walk.length_cons, Walk.length_append]
            lia
          · simp only [Walk.length_cons, Walk.length_append] at *
            rw [Nat.odd_iff] at hodd ⊢
            rw [Nat.even_iff] at hev
            omega
        · -- The loop through `x` is itself odd.
          refine ih (Walk.cons hb (Bt.takeUntil x hx2)) ?_ hod
          simp only [Walk.length_cons]
          lia

/-- A closed walk of odd length yields a cycle of odd length. -/
theorem hasOddCycle_of_odd_length {u : V} (w : G.Walk u u) (hodd : Odd w.length) :
    G.HasOddCycle :=
  hasOddCycle_aux _ w le_rfl hodd

/-- **A graph is `2`-colorable iff it contains no odd cycle.** -/
theorem colorable_two_iff_not_hasOddCycle : G.Colorable 2 ↔ ¬G.HasOddCycle := by
  rw [two_colorable_iff_forall_loop_even]
  constructor
  · rintro h ⟨v, c, _, hodd⟩
    exact (Nat.not_odd_iff_even.2 (h v c)) hodd
  · intro h u w
    rw [← Nat.not_odd_iff_even]
    exact fun hodd => h (hasOddCycle_of_odd_length w hodd)

/-- **A graph is bipartite iff it contains no odd cycle.** -/
theorem isBipartite_iff_not_hasOddCycle : G.IsBipartite ↔ ¬G.HasOddCycle :=
  colorable_two_iff_not_hasOddCycle

end SimpleGraph
