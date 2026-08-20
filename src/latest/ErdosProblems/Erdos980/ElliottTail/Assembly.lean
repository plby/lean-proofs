/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import Mathlib

/-!
# Assembly of Elliott's medium and large tails

This module isolates the elementary final step in the uniform-integrability
argument for Erdős problem 980.  After a cutoff `M` is chosen, the weighted
tail is eventually bounded by a medium tail and a large tail.  The
large-sieve estimate makes the medium tail small after choosing `M`, while
the rarity estimate together with the Burgess bound makes the large tail
small independently of `M`.  Splitting `ε` in half and taking the maximum of
the three eventual thresholds gives the literal `ε`--`M`--`X` conclusion.

The hypotheses are deliberately abstract: the analytic Elliott-tail modules
can instantiate the three functions with the normalized sums occurring in
`tex/980.tex`.
-/

namespace Erdos980.ElliottTail

/-- The generic `ε`--`M`--`X` assembly step for Elliott's weighted tail.

`weightedTail M x` is the full normalized tail above the `M`-th cutoff,
`mediumTail M x` is its part below the logarithmic splitting point, and
`largeTail x` is its part above that point.  The splitting inequality is only
required eventually for each fixed `M`; this accounts for the eventual
comparison between the `M`-th rational prime and the logarithmic splitting
point.
-/
theorem weightedTail_uniformIntegrable_of_medium_large
    (weightedTail mediumTail : ℕ → ℕ → ℝ) (largeTail : ℕ → ℝ)
    (split_eventually :
      ∀ M : ℕ, ∃ X : ℕ, ∀ x : ℕ, X ≤ x →
        weightedTail M x ≤ mediumTail M x + largeTail x)
    (medium_eventually_small :
      ∀ ε : ℝ, 0 < ε → ∃ M X : ℕ, ∀ x : ℕ, X ≤ x →
        mediumTail M x ≤ ε)
    (large_eventually_small :
      ∀ ε : ℝ, 0 < ε → ∃ X : ℕ, ∀ x : ℕ, X ≤ x →
        largeTail x ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∃ M X : ℕ, ∀ x : ℕ, X ≤ x →
      weightedTail M x ≤ ε := by
  intro ε hε
  have hεhalf : 0 < ε / 2 := by positivity
  obtain ⟨M, Xmedium, hmedium⟩ := medium_eventually_small (ε / 2) hεhalf
  obtain ⟨Xlarge, hlarge⟩ := large_eventually_small (ε / 2) hεhalf
  obtain ⟨Xsplit, hsplit⟩ := split_eventually M
  refine ⟨M, max Xmedium (max Xlarge Xsplit), ?_⟩
  intro x hx
  have hxmedium : Xmedium ≤ x := le_trans (le_max_left _ _) hx
  have hxlarge : Xlarge ≤ x :=
    le_trans (le_trans (le_max_left _ _) (le_max_right Xmedium _)) hx
  have hxsplit : Xsplit ≤ x :=
    le_trans (le_trans (le_max_right _ _) (le_max_right Xmedium _)) hx
  calc
    weightedTail M x ≤ mediumTail M x + largeTail x := hsplit x hxsplit
    _ ≤ ε / 2 + ε / 2 := add_le_add (hmedium x hxmedium) (hlarge x hxlarge)
    _ = ε := by ring

end Erdos980.ElliottTail
