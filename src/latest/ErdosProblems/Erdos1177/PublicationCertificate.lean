-- Modified for this repository: Lean 4.33.0 port and Erdos1177 namespace.
import ErdosProblems.Erdos1177.FinalResultsUnconditional

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Single publication certificate for Erdős Problems 593 and 1177

This module packages the final public results into one proposition and one
unconditional theorem.  It is intended to remove any possible ambiguity caused
by the repository's historical, hypothesis-parameterized intermediate files.

`FullResolution` is not an assumption and is not a weakened proxy: its four
fields state the classification in Problem 593 and the three assertions of
Problem 1177 directly.  In particular, `part2` uses the literal first
uncountable cardinal `Cardinal.aleph 1`, and `part3` quantifies over arbitrary
uncountable cardinals.  The theorem `full_resolution_unconditional` has no
hypotheses.  Its proof invokes the already discharged public theorems in
`FinalResultsUnconditional.lean`.
-/

open Cardinal

namespace Erdos1177

universe u

/-- The complete formal content of the resolutions of Erdős Problems 593 and
1177 at universe `u`.

The Problem-1177 fields correspond to the answers **yes / no / yes**:

1. `part1`: yes, every nonempty exact-`ℵ₁` avoidance class has a witness of the
   stated bounded size;
2. `part2`: no, two individually nonempty exact-`ℵ₁` avoidance classes need not
   have a common member;
3. `part3`: yes, nonemptiness at one uncountable chromatic cardinal transfers
   to every uncountable chromatic cardinal.
-/
structure FullResolution : Prop where
  /-- Problem 593: the constructive and intrinsic classifications of every
  finite triple system. -/
  problem593 : ∀ F : FTS,
    (FTS.Obligatory.{u} F ↔ Bclass F) ∧
      (Bclass F ↔ F.reduce.IntrinsicObligatory)
  /-- Problem 1177(1), with `ℵ₁` written literally. -/
  part1 : ∀ (G : FTS), G.FGnonempty (Cardinal.aleph 1 : Cardinal.{u}) →
    ∃ (W : Type u) (H : Hypergraph W),
      H.IsTripleSystem ∧
      H.HasChromatic (Cardinal.aleph 1 : Cardinal.{u}) ∧
      ¬ G.Embeds H ∧
      #W ≤ (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ (ℵ₀ : Cardinal.{u}))
  /-- Problem 1177(2): simultaneous avoidance can fail at exact chromatic
  cardinal `ℵ₁`, despite both individual avoidance classes being nonempty. -/
  part2 : ∃ (G H : FTS),
    G.FGnonempty (Cardinal.aleph 1 : Cardinal.{u}) ∧
    H.FGnonempty (Cardinal.aleph 1 : Cardinal.{u}) ∧
    ¬ ∃ (W : Type u) (K : Hypergraph W),
      K.IsTripleSystem ∧
      K.HasChromatic (Cardinal.aleph 1 : Cardinal.{u}) ∧
      ¬ G.Embeds K ∧ ¬ H.Embeds K
  /-- Problem 1177(3): exact-cardinal avoidance nonemptiness is independent of
  the chosen uncountable cardinal. -/
  part3 : ∀ (G : FTS) (kappa : Cardinal.{u}), ℵ₀ < kappa →
    G.FGnonempty kappa → ∀ (lam : Cardinal.{u}), ℵ₀ < lam → G.FGnonempty lam

/-- **Single unconditional publication certificate.**  This theorem jointly
proves Erdős Problem 593 and all three clauses of Erdős Problem 1177.  It has no
literature hypotheses or project-specific assumptions. -/
theorem full_resolution_unconditional : FullResolution.{u} := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact fun F => classification_unconditional F
  · exact fun G h => problem_1177_part1_aleph_one G h
  · exact problem_1177_part2_aleph_one
  · exact fun G kappa hk h lam hlam =>
      problem_1177_part3_unconditional G kappa hk h lam hlam

end Erdos1177
