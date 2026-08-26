import ErdosProblems.Erdos593.Graph.Parity

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Bounded cycle parity

An odd closed walk always contains an odd simple cycle no longer than the
walk.  This file records the bounded form needed for girth arguments.
-/

namespace Erdos593

namespace SimpleGraph

universe u

variable {V : Type u}

/-- If every simple cycle of length at most `m` is even, then every closed
walk of length at most `m` is even. -/
theorem closedWalk_even_of_cycles_even_up_to
    (G : _root_.SimpleGraph V) (m : ℕ)
    (hcycle : ∀ ⦃v : V⦄ (c : G.Walk v v),
      c.IsCycle → c.length ≤ m → Even c.length) :
    ∀ ⦃v : V⦄ (w : G.Walk v v), w.length ≤ m → Even w.length := by
  intro v w hw
  induction hn : w.length using Nat.strongRec generalizing v with
  | ind n ih =>
    by_cases hc : w.IsCycle
    · simpa only [hn] using! hcycle w hc hw
    by_cases hs : 3 ≤ w.length
    · have hnp : ¬ w.tail.IsPath := by
        intro hp
        exact hc
          (_root_.SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mpr
            ⟨hp, hs⟩)
      cases w with
      | nil => simp at hs
      | @cons _ x _ hadj p =>
        have hnp' : ¬ p.IsPath := by
          simpa using! hnp
        rw [_root_.SimpleGraph.Walk.isPath_iff_isSubwalk_imp_nil] at hnp'
        push Not at hnp'
        obtain ⟨z, q, hqsub, hqnil⟩ := hnp'
        obtain ⟨r₁, r₂, hp⟩ := hqsub
        let r : G.Walk v v := (r₁.append r₂).cons hadj
        have hlen :
            (_root_.SimpleGraph.Walk.cons hadj p).length =
              q.length + r.length := by
          simp [r, hp, _root_.SimpleGraph.Walk.length_append]
          omega
        have hq_lt :
            q.length < (_root_.SimpleGraph.Walk.cons hadj p).length := by
          simp only [_root_.SimpleGraph.Walk.length_cons]
          simp [hp, _root_.SimpleGraph.Walk.length_append]
          omega
        have hr_lt :
            r.length < (_root_.SimpleGraph.Walk.cons hadj p).length := by
          have hqpos : 0 < q.length :=
            Nat.pos_of_ne_zero
              (fun hzero =>
                hqnil
                  (_root_.SimpleGraph.Walk.length_eq_zero_iff.mp hzero))
          omega
        have hq_le : q.length ≤ m := by omega
        have hr_le : r.length ≤ m := by omega
        have hqeven : Even q.length :=
          ih q.length (by simpa only [hn] using! hq_lt) q hq_le rfl
        have hreven : Even r.length :=
          ih r.length (by simpa only [hn] using! hr_lt) r hr_le rfl
        rw [← hn, hlen]
        exact hqeven.add hreven
    · have hne1 : w.length ≠ 1 := by
        intro hwlen
        exact G.loopless.irrefl v (w.adj_of_length_eq_one hwlen)
      have hnsmall : n = 0 ∨ n = 2 := by omega
      rcases hnsmall with rfl | rfl <;> simp

/-- Equivalently, the absence of a short odd simple cycle rules out a short
odd closed walk. -/
theorem no_odd_closedWalk_up_to_of_no_odd_cycle_up_to
    (G : _root_.SimpleGraph V) (m : ℕ)
    (hcycle : ∀ ⦃v : V⦄ (c : G.Walk v v),
      c.IsCycle → c.length ≤ m → ¬ Odd c.length) :
    ∀ ⦃v : V⦄ (w : G.Walk v v), w.length ≤ m → ¬ Odd w.length := by
  intro v w hw hodd
  have heven : Even w.length :=
    closedWalk_even_of_cycles_even_up_to G m
      (fun _ c hc hcm => Nat.not_odd_iff_even.mp (hcycle c hc hcm)) w hw
  exact Nat.not_even_iff_odd.mpr hodd heven

end SimpleGraph

end Erdos593
