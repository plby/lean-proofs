/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourcePureProfileTransport
import ErdosProblems.Erdos207.VortexShellGeometry

/-! # Future-prefix well-spreadness from the actual augmentation support -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem SourceVortexWellSpread.future_prefix_augmentation
    {V : Type*} [Fintype V] [DecidableEq V] {ell j : ℕ}
    (W : Vortex V ell) (k : Fin ell) (m : Fin (ell + 1)) (hkm : k.val < m.val)
    {F Fsup : ForbiddenFamilyOn V} {y z y' z' : ℝ≥0}
    (hold : SourceVortexWellSpread (W.prefix m) j F y z)
    (hcurrent : SourceVortexWellSpread (W.prefix k.castSucc) j Fsup y' z')
    (hy : y ≤ y') (hz : z ≤ z')
    (hnew : ∀ E ∈ Fsup \ F, ∀ T ∈ E, T.1 ⊆ W.U k.castSucc ∧ ¬ T.1 ⊆ W.U k.succ) :
    SourceVortexWellSpread (W.prefix m) j Fsup y' z' := by
  exact SourceVortexWellSpread.transport_outer_augmentation (⟨k.val, hkm⟩ : Fin m.val)
    hold hcurrent hy hz (W.prefix_outer_level_size k m hkm)
    (W.prefix_outer_level_terminal_in_shorter k m hkm)
    (fun E hE T hT ↦ W.prefix_level_eq_of_shell k m hkm T (hnew E hE T hT).1 (hnew E hE T hT).2)

theorem SourceVortexWellSpread.future_prefix_protected_augmentation
    {V : Type*} [Fintype V] [DecidableEq V] {ell j : ℕ}
    (W : Vortex V ell) (k : Fin ell) (m : Fin (ell + 1)) (hkm : k.val < m.val)
    (G : SimpleGraph V) (R : Finset (Sym2 V)) (A : TripleSystemOn V)
    (hG : GraphSupportedOn G (W.U k.castSucc : Set V))
    (hA : ∀ T ∈ A, tripleEdgeFinset T ⊆ graphEdges G)
    {F Fsup : ForbiddenFamilyOn V} {y z y' z' : ℝ≥0}
    (hold : SourceVortexWellSpread (W.prefix m) j F y z)
    (hcurrent : SourceVortexWellSpread (W.prefix k.castSucc) j Fsup y' z')
    (hy : y ≤ y') (hz : z ≤ z')
    (hnew : ∀ E ∈ Fsup \ F, E ⊆ reserveProtectedOuterAvailable G (W.U k.succ) R A) :
    SourceVortexWellSpread (W.prefix m) j Fsup y' z' := by
  apply SourceVortexWellSpread.future_prefix_augmentation W k m hkm hold hcurrent hy hz
  intro E hE T hT
  exact reserveProtectedOuterAvailable_shell G (W.U k.castSucc) (W.U k.succ) R A hG hA T (hnew E hE hT)

end

end Erdos207
