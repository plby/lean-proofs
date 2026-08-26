import ErdosProblems.Erdos489.Proof

/-!
Colin Snyder and GPT-5.6's proof claim for Erdős Problem 489, ported to
Lean 4.33.0 with a local real-cutoff bridge. See Erdos489/README.md.
-/

namespace Erdos489

open scoped Classical in
/-- The squared-gap average converges along natural cutoffs. -/
theorem erdos_489_nat (A : Set ℕ)
    (hthin : (fun x : ℕ => (((Finset.Icc 1 x).filter (· ∈ A)).card : ℝ))
      =o[Filter.atTop] (fun x : ℕ => Real.sqrt (x : ℝ)))
    (hB : (sievedSet A).Infinite) :
    ∃ L : ℝ, Filter.Tendsto (fun x : ℕ => gapSumSq A x / (x : ℝ))
      Filter.atTop (nhds L) := by
  exact erdos489_statement A hthin hB

open scoped Classical in
/-- The original real-cutoff limit. The ceiling keeps exactly the natural
left endpoints strictly below the real cutoff. -/
theorem erdos_489 (A : Set ℕ)
    (hthin : (fun x : ℝ => (((Finset.Icc 1 ⌊x⌋₊).filter (· ∈ A)).card : ℝ))
      =o[Filter.atTop] Real.sqrt)
    (hB : (sievedSet A).Infinite) :
    ∃ L : ℝ, Filter.Tendsto (fun x : ℝ => gapSumSq A ⌈x⌉₊ / x)
      Filter.atTop (nhds L) := by
  have hn : (fun x : ℕ => (((Finset.Icc 1 x).filter (· ∈ A)).card : ℝ))
      =o[Filter.atTop] (fun x : ℕ => Real.sqrt (x : ℝ)) := by
    simpa only [Function.comp_def, Nat.floor_natCast] using
      hthin.comp_tendsto tendsto_natCast_atTop_atTop
  obtain ⟨L, hL⟩ := erdos_489_nat A hn hB
  exact ⟨L, tendsto_ceil_cutoff (gapSumSq A) hL⟩

end Erdos489

#print axioms Erdos489.erdos_489_nat
#print axioms Erdos489.erdos_489
