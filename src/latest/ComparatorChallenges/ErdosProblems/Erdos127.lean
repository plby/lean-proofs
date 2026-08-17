import Mathlib

open Filter Finset Set
open scoped ENNReal Topology

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

namespace Erdos127

noncomputable def baseline (m : ℕ) : ℝ :=
  (m : ℝ) / 2 + (Real.sqrt (8 * (m : ℝ) + 1) - 1) / 8

end Erdos127

namespace Erdos127

def Guarantees (m k : ℕ) : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
    G.edgeSet.ncard = m →
      ∃ H : SimpleGraph V, H ≤ G ∧ H.IsBipartite ∧
        baseline m + k ≤ (H.edgeSet.ncard : ℝ)

end Erdos127

namespace Erdos127

noncomputable def correction (m : ℕ) : ℕ :=
  open scoped Classical in
  Nat.findGreatest (Guarantees m) m

end Erdos127

namespace Erdos127

theorem erdos127 :
    ∃ mseq : ℕ → ℕ, Tendsto mseq atTop atTop ∧
      Tendsto (fun i ↦ correction (mseq i)) atTop atTop := by
  sorry

end Erdos127

end
