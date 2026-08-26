import ErdosProblems.Erdos260.Proof

/-!
Lean version: 4.33.0 (ported from 4.32.0).
Formalization: Han Wang, with GPT-5.5 and GPT-5.6 assistance.
See Erdos260/README.md for the pinned source and attribution evidence.
The integer-valued endpoint `Erdos260.erdos_260` is imported from DeepMind.lean.
-/

open Filter

namespace Erdos260

/-- The positive natural-sequence formulation, with convergence supplied by the proof. -/
theorem erdos_260_nat (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (hgrowth : Tendsto (fun n => (a n : ℝ) / (n + 1)) atTop atTop) :
    Irrational (∑' n : ℕ, (a n : ℝ) / 2 ^ a n) := by
  simpa only [natSequenceTerm] using cor_erdos260 a ha hpos hgrowth

end Erdos260

#print axioms Erdos260.erdos_260
#print axioms Erdos260.erdos_260_nat
