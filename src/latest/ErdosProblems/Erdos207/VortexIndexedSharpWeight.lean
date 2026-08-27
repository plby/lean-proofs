/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.VortexInducedWellSpread
import ErdosProblems.Erdos207.VortexIndexedWeight
import ErdosProblems.Erdos207.VortexSharpWeight

/-! # Density-sensitive indexed absorber weights -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- The sharp W1 estimate for one absorber-induced indexed family. -/
theorem extensionWeight_absorberInduced_vortex_nonempty_le_sharp
    {V : Type*} [Fintype V] [DecidableEq V] {ell q j : ℕ}
    (W : Vortex V ell) (B : TripleSystemOn V) (c : ℝ≥0)
    (hj : 3 ≤ j)
    (houter : ∀ i : Fin ell, 0 < (W.U i.castSucc).card)
    (hterminal : 0 < W.terminalSize)
    (R : TripleSystemOn V) (hR : R.Nonempty) (hRcard : R.card ≤ j - 2) :
    extensionWeight
        (fun E : absorberInducedConfigurationsOn q j B ↦ E.1)
        (vortexTripleWeight W c) R ≤
      (((j + 1) ^ ell *
        indexedInducedVortexSpreadCoefficient q ell B W.terminalSize : ℕ) :
          ℝ≥0) * c ^ (j - 2 - R.card) := by
  simpa only [indexedInducedVortexSpreadCoefficient, Nat.cast_mul,
    Nat.cast_pow, Nat.cast_add, Nat.cast_one] using
    (absorberInduced_vortexWellSpread (q := q) W B hj
      hterminal).extensionWeight_nonempty_le_sharp c houter hterminal
        R hR hRcard

/-- The sharp W4 estimate for one absorber-induced indexed family. -/
theorem extensionWeight_absorberInduced_vortex_singleton_le_sharp
    {V : Type*} [Fintype V] [DecidableEq V] {ell q j : ℕ}
    (W : Vortex V ell) (B : TripleSystemOn V) (c : ℝ≥0)
    (hj : 3 ≤ j)
    (houter : ∀ i : Fin ell, 0 < (W.U i.castSucc).card)
    (hterminal : 0 < W.terminalSize) (T : TripleOn V) :
    extensionWeight
        (fun E : absorberInducedConfigurationsOn q j B ↦ E.1)
        (vortexTripleWeight W c) {T} ≤
      (((j + 1) ^ ell * inducedVortexCoefficient q ell B : ℕ) : ℝ≥0) *
        c ^ (j - 3) := by
  simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one] using
    (absorberInduced_vortexWellSpread (q := q) W B hj
      hterminal).extensionWeight_singleton_le_sharp c hj houter hterminal T

end

end Erdos207
