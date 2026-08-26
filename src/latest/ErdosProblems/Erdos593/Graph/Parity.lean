import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Cycle parity and bipartiteness

Mathlib characterizes two-colourability by evenness of every closed walk.  The
finite structural proof naturally produces information about simple cycles, so
we isolate the standard reduction from closed walks to simple cycles here.
-/

namespace Erdos593

namespace SimpleGraph

universe u

variable {V : Type u}

/-- A simple graph is two-colourable exactly when every simple cycle has even
length. -/
-- ARISTOTLE_TARGET G5
theorem two_colorable_iff_every_cycle_even (G : _root_.SimpleGraph V) :
    G.Colorable 2 ↔
      ∀ ⦃v : V⦄ (c : G.Walk v v), c.IsCycle → Even c.length := by
  rw [_root_.SimpleGraph.two_colorable_iff_forall_loop_even]
  constructor
  · intro h v c _
    exact h v c
  · intro h v w
    induction hn : w.length using Nat.strongRec generalizing v with
    | ind n ih =>
      by_cases hc : w.IsCycle
      · simpa only [hn] using! h w hc
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
          have hqeven : Even q.length :=
            ih q.length (by simpa only [hn] using! hq_lt) z q rfl
          have hreven : Even r.length :=
            ih r.length (by simpa only [hn] using! hr_lt) v r rfl
          rw [← hn, hlen]
          exact hqeven.add hreven
      · have hne1 : w.length ≠ 1 := by
          intro hw
          exact G.loopless.irrefl v (w.adj_of_length_eq_one hw)
        have hnsmall : n = 0 ∨ n = 2 := by omega
        rcases hnsmall with rfl | rfl <;> simp

end SimpleGraph

end Erdos593
