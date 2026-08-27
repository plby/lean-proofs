/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FixedRandomAllOrders
import ErdosProblems.Erdos207.SourceFutureIncrementTransport

/-! # Fixed-shell envelopes preserve source bounds at every future prefix -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def vortexShellConfigurations
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (k : Fin ell) (j : ℕ) : ForbiddenFamilyOn V := by
  classical
  exact (terminalRandomConfigurations (W.prefix k.castSucc) j).filter
    (fun E ↦ ∀ T ∈ E, ¬ T.1 ⊆ W.U k.succ)

theorem vortexShellConfigurations_subset_terminal
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (k : Fin ell) (j : ℕ) :
    vortexShellConfigurations W k j ⊆ terminalRandomConfigurations (W.prefix k.castSucc) j :=
  filter_subset _ _

theorem vortexShellConfigurations_shell
    {V : Type*} [Fintype V] [DecidableEq V] {ell j : ℕ}
    (W : Vortex V ell) (k : Fin ell) {E : TripleSystemOn V}
    (hE : E ∈ vortexShellConfigurations W k j) {T : TripleOn V} (hT : T ∈ E) :
    T.1 ⊆ W.U k.castSucc ∧ ¬ T.1 ⊆ W.U k.succ := by
  have hh := mem_filter.mp hE
  refine ⟨?_, hh.2 T hT⟩
  have hsub := mem_triplesSupportedOn_iff.mp
    (((mem_terminalRandomConfigurations_iff (W.prefix k.castSucc) E).mp hh.1).1 hT)
  simpa only [Vortex.prefix_U, vortexPrefixEmbedding_last] using hsub

theorem vortexShellConfigurations_image_geometry
    {V I : Type*} [Fintype V] [DecidableEq V] [DecidableEq I] {ell j : ℕ}
    (W : Vortex V ell) (k : Fin ell) (e : I ↪ TripleOn V)
    (hshell : ∀ i, ¬ (e i).1 ⊆ W.U k.succ) (E : Finset I)
    (hE : E.map e ∈ terminalRandomConfigurations (W.prefix k.castSucc) j) :
    E.map e ∈ vortexShellConfigurations W k j := by
  apply mem_filter.mpr
  refine ⟨hE, ?_⟩
  intro T hT
  obtain ⟨i, _, rfl⟩ := mem_map.mp hT
  exact hshell i

theorem FixedRandomOrderResult.future_prefix_spread
    {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V]
    {I : D → Type*} [∀ d, Fintype (I d)] [∀ d, DecidableEq (I d)] [∀ d, Nonempty (I d)]
    {ell j b : ℕ} (W : Vortex V ell) (k : Fin ell) (m : Fin (ell + 1)) (hkm : k.val < m.val)
    {P : FiniteLaw D} {e : (d : D) → I d ↪ TripleOn V}
    {L earlier Lstar : (d : D) → Finset (Finset (I d))}
    {F R : ForbiddenFamilyOn V} {y z a rho yFuture zFuture : ℝ≥0}
    (h : FixedRandomOrderResult P (W.prefix k.castSucc) e j b L earlier F
      (vortexShellConfigurations W k j) y z a rho Lstar R)
    (hF : SourceVortexWellSpread (W.prefix m) j F yFuture zFuture) :
    SourceVortexWellSpread (W.prefix m) j (F ∪ R) (yFuture + a) (zFuture + 3 * a) :=
  h.counts.future_prefix_sourceWellSpread W k m hkm hF
    (fun E hE T hT ↦ vortexShellConfigurations_shell W k (h.support hE) hT)

end

end Erdos207
