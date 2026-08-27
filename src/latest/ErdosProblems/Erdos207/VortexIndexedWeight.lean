/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.VortexInducedWellSpread
import ErdosProblems.Erdos207.VortexWeight

/-!
# Level-weighted absorber-induced extension bounds

The profile counts in `VortexInducedWellSpread` still display the powers of
the individual vortex sizes.  This file combines them with the cancellation
lemmas in `VortexWeight`.  The resulting coefficients are independent of all
nonterminal vortex sizes, which is the form required by the moment estimates
in the cover-down iteration.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- The coarse W1--W3 coefficient for one indexed absorber-induced family. -/
def indexedInducedVortexSpreadCoefficient
    {V : Type*} [Fintype V] [DecidableEq V]
    (q ell : ℕ) (B : TripleSystemOn V) (terminalSize : ℕ) : ℕ :=
  inducedVortexCoefficient q ell B * terminalSize + terminalSize ^ 3

/-- After weighting a level-`i` triangle by `c / |U_i|`, every nonempty
rooted extension sum in one indexed family has an ambient-size-free bound. -/
theorem extensionWeight_absorberInduced_vortex_nonempty_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell q j : ℕ}
    (W : Vortex V ell) (B : TripleSystemOn V) (c : ℝ≥0)
    (hj : 3 ≤ j) (hc : c ≤ 1)
    (houter : ∀ i : Fin ell, 0 < (W.U i.castSucc).card)
    (hterminal : 0 < W.terminalSize)
    (R : TripleSystemOn V) (hR : R.Nonempty) (hRcard : R.card ≤ j - 2) :
    extensionWeight
        (fun E : absorberInducedConfigurationsOn q j B ↦ E.1)
        (vortexTripleWeight W c) R ≤
      (((j + 1) ^ ell *
        indexedInducedVortexSpreadCoefficient q ell B W.terminalSize : ℕ) :
          ℝ≥0) := by
  exact (absorberInduced_vortexWellSpread W B hj hterminal).extensionWeight_nonempty_le_uniform
    c hc houter hterminal R hR hRcard

/-- The sharper W4 coefficient applies when the prescribed root is a single
triangle. -/
theorem extensionWeight_absorberInduced_vortex_singleton_le
    {V : Type*} [Fintype V] [DecidableEq V] {ell q j : ℕ}
    (W : Vortex V ell) (B : TripleSystemOn V) (c : ℝ≥0)
    (hj : 3 ≤ j) (hc : c ≤ 1)
    (houter : ∀ i : Fin ell, 0 < (W.U i.castSucc).card)
    (hterminal : 0 < W.terminalSize) (T : TripleOn V) :
    extensionWeight
        (fun E : absorberInducedConfigurationsOn q j B ↦ E.1)
        (vortexTripleWeight W c) {T} ≤
      (((j + 1) ^ ell * inducedVortexCoefficient q ell B : ℕ) : ℝ≥0) := by
  exact (absorberInduced_vortexWellSpread W B hj hterminal).extensionWeight_singleton_le_uniform
    c hc houter hterminal T

end

end Erdos207
