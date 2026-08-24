/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter

namespace Erdos127

noncomputable def baseline (m : ℕ) : ℝ :=
  (m : ℝ) / 2 + (Real.sqrt (8 * (m : ℝ) + 1) - 1) / 8

def Guarantees (m k : ℕ) : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    G.edgeSet.ncard = m →
      ∃ H : SimpleGraph V, H ≤ G ∧ H.IsBipartite ∧
        baseline m + k ≤ (H.edgeSet.ncard : ℝ)

noncomputable def correction (m : ℕ) : ℕ :=
  open scoped Classical in
  Nat.findGreatest (Guarantees m) m

theorem erdos_127 :
    ∃ mseq : ℕ → ℕ, Tendsto mseq atTop atTop ∧
      Tendsto (fun i ↦ correction (mseq i)) atTop atTop := by
  sorry

end Erdos127
