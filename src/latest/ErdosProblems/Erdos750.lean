/-
Erdős Problem 750: almost-half independent sets at infinite chromatic number.

The local odd-cycle-transversal construction follows Chojecki and GPT-5.5 Pro,
https://www.ulam.ai/research/erdos750.pdf.
Its conditional Lean formalization was posted by paws (Shashi456):
https://www.erdosproblems.com/forum/thread/750#post-6255
https://github.com/Shashi456/erdos-formalizations/blob/main/Erdos/P750/Proof.lean

The original Stiebitz axiom is replaced here by the theorem proved in
ErdosProblems.Erdos750.Stiebitz. No computational limits are increased.
-/
import ErdosProblems.Erdos750.Conditional
import ErdosProblems.Erdos750.Stiebitz

namespace Erdos750

open SimpleGraph Filter
open scoped NNReal

/-- Finite generalized Mycielski graphs with the prescribed local OCT profile
and exactly the requested chromatic number. -/
theorem finite_oct_profile_with_chromatic
    (g : ℕ → ℕ) (hg_mono : Monotone g)
    (hg_top : Tendsto g atTop atTop) (r : ℕ) (hr : 2 ≤ r) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V),
      IsRecursivelyBuiltMr r G ∧ G.chromaticNumber = (r : ℕ∞) ∧
      ∀ X : Finset V, X.Nonempty → oct G X ≤ g X.card :=
  Conditional.finite_oct_profile_with_chromatic stiebitz_lower_bound g hg_mono hg_top r hr

/-- The stronger OCT form: every nondecreasing unbounded profile occurs in
a graph of infinite chromatic number. -/
theorem infinite_chromatic_local_oct (g : ℕ → ℕ) (hg_mono : Monotone g)
    (hg_top : Tendsto g atTop atTop) :
    ∃ (V : Type) (_ : DecidableEq V) (G : SimpleGraph V),
      G.chromaticNumber = ⊤ ∧
      ∀ X : Finset V, X.Nonempty → oct G X ≤ g X.card :=
  Conditional.infinite_chromatic_local_oct stiebitz_lower_bound g hg_mono hg_top

/-- **Erdős Problem 750**, in the real-valued independence-bound form. -/
theorem erdos_750_independence :
    ∀ (f : ℕ → ℝ≥0), Tendsto f atTop atTop →
      ∃ (V : Type) (G : SimpleGraph V), G.chromaticNumber = ⊤ ∧
        ∀ (m : ℕ) (S : Set V), 0 < m → S.ncard = m →
          ∃ I ⊆ S, G.IsIndepSet I ∧ (m : ℝ) / 2 - (f m : ℝ) ≤ (I.ncard : ℝ) :=
  Conditional.erdos_750_independence stiebitz_lower_bound

/-- **Erdős Problem 750**, with the nonnegative-real arithmetic used by
the formal-conjectures statement. -/
theorem erdos_750 :
    ∀ (f : ℕ → ℝ≥0), Tendsto f atTop atTop →
      ∃ (V : Type) (G : SimpleGraph V), G.chromaticNumber = ⊤ ∧
        ∀ (m : ℕ) (S : Set V), 0 < m → S.ncard = m →
          ∃ I ⊆ S, G.IsIndepSet I ∧ (m : ℝ≥0) / 2 - f m ≤ (I.ncard : ℝ≥0) :=
  Conditional.erdos_750_independence_FC_form stiebitz_lower_bound

end Erdos750
