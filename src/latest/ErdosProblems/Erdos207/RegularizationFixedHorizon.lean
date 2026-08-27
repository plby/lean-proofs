/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RegularizationHorizon
import ErdosProblems.Erdos207.FiniteLawKernelCalculus

/-! # Extending the regularizer to a deterministic common horizon -/

namespace Erdos207

open Finset

noncomputable section

theorem regularizationKernel_eq_pure_after_initial_gap
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] {k : ℕ}
    (G0 H0 : Finset (Finset V)) (hGH : G0 ⊆ H0) (hk : 2 ≤ k)
    (hsize : 16 * 2 ^ (k - 1) * (k - 1) ≤ Fintype.card V)
    (b t : ℕ) (ht : finiteHypergraphDegreeGap G0 ≤ t) (S : HypergraphRegularizationState V k) :
    regularizationKernel G0 H0 hGH hk hsize b t S = FiniteLaw.pure S := by
  apply regularizationKernel_inactive
  intro hA
  have hpos : 0 < finiteHypergraphDegreeGap (regularizationCurrentFamily G0 S) :=
    Nat.zero_lt_of_lt hA.2.1
  have hpower := Nat.le_mul_of_pos_right (2 ^ t) hpos
  exact t.lt_two_pow_self.not_ge ((hpower.trans hA.2.2.1).trans ht)

theorem regularizationEvolve_eq_processLaw_of_gap_le
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] {k : ℕ}
    (G0 H0 : Finset (Finset V)) (hGH : G0 ⊆ H0) (hk : 2 ≤ k)
    (hsize : 16 * 2 ^ (k - 1) * (k - 1) ≤ Fintype.card V)
    (b t : ℕ) (ht : finiteHypergraphDegreeGap G0 ≤ t) :
    FiniteLaw.evolveKernels (regularizationKernel G0 H0 hGH hk hsize b) t
      (FiniteLaw.pure (regularizationInitialState V k)) =
      regularizationProcessLaw G0 H0 hGH hk hsize b := by
  induction t, ht using Nat.le_induction with
  | base => rfl
  | succ t ht ih =>
      rw [FiniteLaw.evolveKernels_succ, ih]
      have hK : regularizationKernel G0 H0 hGH hk hsize b t = FiniteLaw.pure := by
        funext S
        exact regularizationKernel_eq_pure_after_initial_gap G0 H0 hGH hk hsize b t ht S
      rw [hK, FiniteLaw.bind_pure_right]

end

end Erdos207
