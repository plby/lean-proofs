import Mathlib

open Filter Finset
open scoped Asymptotics

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Erdos981

def oddPrimesBelow (x : ℕ) : Finset ℕ :=
  (range x).filter fun p => p.Prime ∧ Odd p

end Erdos981

namespace Erdos981

def legendrePartialSum (p N : ℕ) : ℤ :=
  ∑ n ∈ range N, jacobiSym (n + 1 : ℤ) p

end Erdos981

namespace Erdos981

def IsEventualThreshold (ε : ℝ) (p m : ℕ) : Prop :=
  1 ≤ m ∧ ∀ N : ℕ, m ≤ N → (legendrePartialSum p N : ℝ) < ε * (N : ℝ)

end Erdos981

namespace Erdos981

noncomputable def eventualThreshold (ε : ℝ) (p : ℕ) : ℕ :=
  by
    classical
    exact if h : ∃ m : ℕ, IsEventualThreshold ε p m then Nat.find h else 0

end Erdos981

namespace Erdos981

noncomputable def thresholdPrimeSum (ε : ℝ) (x : ℕ) : ℝ :=
  ∑ p ∈ oddPrimesBelow x, (eventualThreshold ε p : ℝ)

/-! ## The finite random completely multiplicative model -/

end Erdos981

namespace Erdos981

theorem erdos_981 {ε : ℝ} (hε : 0 < ε) :
    ∃ cε : ℝ, 0 < cε ∧
      thresholdPrimeSum ε ~[atTop]
        (fun x : ℕ => cε * ((x : ℝ) / Real.log (x : ℝ))) := by
  sorry

end Erdos981

end
