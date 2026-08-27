/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceOuterAugmentation
import ErdosProblems.Erdos207.VortexShellGeometry

/-! # Future-prefix bounds retain the original future coefficients, not the outer ones -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem SourceAugmentationCounts.future_prefix_sourceWellSpread
    {V : Type*} [Fintype V] [DecidableEq V] {ell j : ℕ}
    (W : Vortex V ell) (k : Fin ell) (m : Fin (ell + 1)) (hkm : k.val < m.val)
    {F G : ForbiddenFamilyOn V} {y z a : ℝ≥0}
    (hcounts : SourceAugmentationCounts j (W.prefix k.castSucc).terminalSize F G a)
    (hF : SourceVortexWellSpread (W.prefix m) j F y z)
    (hshell : ∀ E ∈ G, ∀ T ∈ E, T.1 ⊆ W.U k.castSucc ∧ ¬ T.1 ⊆ W.U k.succ) :
    SourceVortexWellSpread (W.prefix m) j (F ∪ G) (y + a) (z + 3 * a) := by
  exact hcounts.outer_sourceWellSpread hF (⟨k.val, hkm⟩ : Fin m.val)
    (W.prefix_outer_level_size k m hkm)
    (fun E hE T hT ↦ W.prefix_level_eq_of_shell k m hkm T (hshell E hE T hT).1 (hshell E hE T hT).2)

theorem SourceAugmentationCounts.future_prefix_superset
    {V : Type*} [Fintype V] [DecidableEq V] {ell j : ℕ}
    (W : Vortex V ell) (k : Fin ell) (m : Fin (ell + 1)) (hkm : k.val < m.val)
    {F Fsup : ForbiddenFamilyOn V} {y z a : ℝ≥0}
    (hcounts : SourceAugmentationCounts j (W.prefix k.castSucc).terminalSize F (Fsup \ F) a)
    (hF : SourceVortexWellSpread (W.prefix m) j F y z) (hsub : F ⊆ Fsup)
    (hshell : ∀ E ∈ Fsup \ F, ∀ T ∈ E, T.1 ⊆ W.U k.castSucc ∧ ¬ T.1 ⊆ W.U k.succ) :
    SourceVortexWellSpread (W.prefix m) j Fsup (y + a) (z + 3 * a) := by
  have h := SourceAugmentationCounts.future_prefix_sourceWellSpread W k m hkm hcounts hF hshell
  simpa only [union_sdiff_of_subset hsub] using h

end

end Erdos207
