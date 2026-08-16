import Mathlib

namespace Erdos280

section Erdos280

open Nat

def isCoveredBy (n a : ℕ → ℕ) (m k : ℕ) : Prop :=
  ∃ i, 1 ≤ i ∧ i ≤ k ∧ m % n i = a i

noncomputable instance isCoveredBy_decidable (n a : ℕ → ℕ) (m k : ℕ) :
    Decidable (isCoveredBy n a m k) :=
  Classical.dec _
end Erdos280

end Erdos280

attribute [local instance] Classical.propDecidable

open Nat

namespace Erdos280

theorem erdos_280_counterexample :
    ∃ (n a : ℕ → ℕ) (ε : ℝ),
      0 < ε ∧
      StrictMono n ∧
      (∀ i, 1 ≤ i → a i < n i) ∧
      (∀ k, 1 ≤ k → (n k : ℝ) > (1 + ε) * ↑k * Real.log ↑k) ∧
      (∀ k, 1 ≤ k →
        ((Finset.range (n k)).filter
          (fun m => ¬ isCoveredBy n a m k)).card = 1) ∧
      Filter.Tendsto
        (fun k : ℕ =>
          (((Finset.range (n k)).filter
            (fun m => ¬ isCoveredBy n a m k)).card : ℝ) / ↑k)
        Filter.atTop (nhds 0) := by
  sorry

end Erdos280
