/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos71

def HasCycleOfLength {V : Type*} (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ (v : V) (w : G.Walk v v), w.IsCycle ∧ w.length = n

structure InfiniteAP where
  a : ℕ
  d : ℕ
  a_pos : 1 ≤ a
  d_pos : 1 ≤ d

namespace InfiniteAP

def Mem (P : InfiniteAP) (n : ℕ) : Prop := ∃ m : ℕ, n = P.a + m * P.d

instance : Membership ℕ InfiniteAP where
  mem P n := P.Mem n

def ContainsEven (P : InfiniteAP) : Prop := ∃ n ∈ P, Even n

end InfiniteAP

noncomputable def avgDegree {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℚ :=
  (2 * G.edgeFinset.card : ℚ) / Fintype.card V

theorem erdos_71 (P : InfiniteAP) (heven : P.ContainsEven) :
    ∃ c : ℕ, ∀ (V : Type*) [Fintype V] [DecidableEq V] [Nonempty V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      (c : ℚ) ≤ avgDegree G →
      ∃ n ∈ P, HasCycleOfLength G n := by
  sorry

end Erdos71
