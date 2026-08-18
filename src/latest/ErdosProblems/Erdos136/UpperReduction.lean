/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos136.Asymptotics
import ErdosProblems.Erdos136.LeaveCompletion

/-!
# Erdős 136: reduction of the analytic theorem to sparse partial colorings

This file joins the already-closed parts of the upper construction.  Once
the conflict-free matching stage supplies `PartialGood` colorings with the
canonical ceiling leave bound, the finite local lemma completes them and the
analytic squeeze proves the asymptotic theorem for the minimum palette size.
-/

namespace Erdos136

open Filter
open scoped Topology

/-- An eventual family of Joos--Mubayi sparse partial colorings is the only
remaining combinatorial input needed for the Erdős 136 ratio limit. -/
theorem erdos136Fun_tendsto_of_eventually_partialGood
    {delta C C0 : ℝ}
    (hdelta0 : 0 < delta) (hdeltaHalf : delta < 1 / 2)
    (hC : 0 ≤ C) (hC0 : 0 ≤ C0)
    (hP : ∀ᶠ n : ℕ in atTop,
      Nonempty (PartialGood n (jmOldColors delta n)
        (jmCeilLeaveBound C C0 delta n))) :
    Tendsto (fun n => (erdos136Fun n : ℝ) / (n : ℝ)) atTop
      (nhds (5 / 6 : ℝ)) := by
  apply erdos136Fun_tendsto_of_eventually_colorable (jmTotalColors delta)
    (jmTotalColors_tendsto hdelta0)
  have hfour := eventually_jmCeilLeaveBound_four_mul_le_one
    hdelta0 hdeltaHalf hC hC0
  have hdelta1 : delta < 1 := hdeltaHalf.trans (by norm_num)
  have ht : ∀ᶠ n : ℕ in atTop, 0 < jmFreshColors delta n :=
    (jmFreshColors_tendsto_atTop hdelta1).eventually (eventually_gt_atTop 0)
  filter_upwards [hP, hfour, ht] with n hPn h4 htpos
  simpa [jmTotalColors] using
    LeaveCompletion.colorable_of_partialGood_jmLeaveBound hPn.some htpos h4

/-- The equivalent `~` formulation of the preceding ratio limit. -/
theorem erdos136Fun_isEquivalent_of_eventually_partialGood
    {delta C C0 : ℝ}
    (hdelta0 : 0 < delta) (hdeltaHalf : delta < 1 / 2)
    (hC : 0 ≤ C) (hC0 : 0 ≤ C0)
    (hP : ∀ᶠ n : ℕ in atTop,
      Nonempty (PartialGood n (jmOldColors delta n)
        (jmCeilLeaveBound C C0 delta n))) :
    Asymptotics.IsEquivalent atTop
      (fun n : ℕ => (erdos136Fun n : ℝ))
      (fun n : ℕ => (5 / 6 : ℝ) * (n : ℝ)) := by
  apply isEquivalent_of_tendsto_normalized _ _ (by norm_num)
  exact erdos136Fun_tendsto_of_eventually_partialGood
    hdelta0 hdeltaHalf hC hC0 hP

end Erdos136
