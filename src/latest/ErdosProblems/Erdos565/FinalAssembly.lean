/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Lean Formalization Project
-/
import ErdosProblems.Erdos565.FinalBridge
import ErdosProblems.Erdos565.KeyLemma
import ErdosProblems.Erdos565.RamseyNumber

/-!
# Final assembly for Erdős problem 565

This file applies the finite-host ACDFM key lemma to every terminal state of
the deterministic descent.  The local estimate is transferred through graph
restriction to the ambient labelled host, and the denominator-cleared union
bound produces the required induced Ramsey witness.
-/

namespace Erdos565
namespace FinalAssembly

open FinalBridge

/-- Every terminal bad event has the common saving used in the final union
bound.  The key lemma is applied on the actual induced vertex subtype. -/
theorem stateTerminal_card_mul_finalSaving_le {r k : ℕ}
    (hr : 2 ≤ r) (hk : 2 ≤ k)
    (s : DescentState (Numeric.hostOrder r k) r k) :
    (FinalReduction.terminalBadSet
        (StateBad (r := r) (k := k))
        (StateTerminal (r := r) (k := k)) s).card *
        2 ^ Numeric.finalNumerator r k ≤
      Fintype.card (SimpleGraph (Fin (Numeric.hostOrder r k))) := by
  classical
  by_cases hs : StateAdmissible s
  · have hhost := admissible_hostOrder_le_mul hr s hs
    have hscaleNat :
        r ^ (300 * (k + stateRank s)) ≤ s.vertices.card :=
      Numeric.key_lemma_size_of_hostOrder_le_mul hr hk (stateRank_le s) hhost
    have hscale :
        r ^ (300 * (k + Events.totalOrder (stateOrder s))) ≤
          Fintype.card
            (↑s.vertices : Set (Fin (Numeric.hostOrder r k))) := by
      simpa [stateRank_eq_totalOrder] using hscaleNat
    have hkey := KeyLemma.acdfm_key_lemma_on
      (V := (↑s.vertices : Set (Fin (Numeric.hostOrder r k))))
      (stateTargets s) hr hk
      (fun i ↦ BoundedTarget.order_le (s.targets i)) hscale
    have hsets : localTerminalBadSet s =
        KeyLemma.keyBadSetOn k (stateTargets s) := by
      rfl
    have hexponent : Numeric.finalNumerator r k ≤
        KeyLemma.keyExponent r
          (Fintype.card
            (↑s.vertices : Set (Fin (Numeric.hostOrder r k)))) := by
      simpa [KeyLemma.keyExponent] using
        (finalNumerator_le_keyExponent_of_admissible hr hk s hs)
    have hlocal : (localTerminalBadSet s).card *
          2 ^ Numeric.finalNumerator r k ≤
        Fintype.card
          (SimpleGraph
            (↑s.vertices : Set (Fin (Numeric.hostOrder r k)))) := by
      calc
        (localTerminalBadSet s).card * 2 ^ Numeric.finalNumerator r k ≤
            (localTerminalBadSet s).card *
              2 ^ KeyLemma.keyExponent r
                (Fintype.card
                  (↑s.vertices : Set (Fin (Numeric.hostOrder r k)))) := by
          exact Nat.mul_le_mul_left _
            (Nat.pow_le_pow_right (by decide : 0 < 2) hexponent)
        _ = (KeyLemma.keyBadSetOn k (stateTargets s)).card *
              2 ^ KeyLemma.keyExponent r
                (Fintype.card
                  (↑s.vertices : Set (Fin (Numeric.hostOrder r k)))) := by
          rw [hsets]
        _ ≤ Fintype.card
              (SimpleGraph
                (↑s.vertices : Set (Fin (Numeric.hostOrder r k)))) := hkey
    exact terminalBadSet_card_mul_le_of_local s
      (2 ^ Numeric.finalNumerator r k) hlocal
  · simp [FinalReduction.terminalBadSet, StateBad, hs]

/-- For targets of order at least two, the explicit ACDFM host order is an
induced Ramsey order. -/
theorem isInducedRamseyOrder_hostOrder_two {k : ℕ} (hk : 2 ≤ k)
    (G : SimpleGraph (Fin k)) :
    IsInducedRamseyOrder G (Numeric.hostOrder 2 k) := by
  classical
  refine inducedRamseyOrder_of_keyEstimate_mul
    (State := DescentState (Numeric.hostOrder 2 k) 2 k) G
    (fun s ↦ stateRank s)
    (fun H s ↦ StateBad H s)
    (fun H s ↦ StateTerminal H s)
    (fun _H ↦ initialState G)
    (2 ^ Numeric.finalNumerator 2 k) ?_ ?_ ?_ ?_
  · intro H hH
    exact state_start hk G H hH
  · intro H s hs hterminal
    exact state_descent (by decide) hk H s hs hterminal
  · intro s
    exact stateTerminal_card_mul_finalSaving_le (by decide) hk s
  · exact card_descentState_lt_finalSaving (by decide) hk

/-- Every labelled graph has an induced Ramsey host of order at most
`2^(3000 n)`. -/
theorem hasInducedRamseyOrderAtMost_explicit (n : ℕ)
    (G : SimpleGraph (Fin n)) :
    HasInducedRamseyOrderAtMost G (2 ^ (3000 * n)) := by
  by_cases hn0 : n = 0
  · subst n
    exact (isInducedRamseyOrder_zero G).hasAtMost.mono (Nat.zero_le _)
  by_cases hn1 : n = 1
  · subst n
    apply (isInducedRamseyOrder_one G).hasAtMost.mono
    exact one_le_pow₀ (by decide : (1 : ℕ) ≤ 2)
  · have hn : 2 ≤ n := by omega
    simpa [Numeric.hostOrder_eq_two_pow] using
      (isInducedRamseyOrder_hostOrder_two hn G).hasAtMost

/-- Uniform explicit exponential induced Ramsey bound. -/
theorem uniformInducedRamseyBound_explicit :
    UniformInducedRamseyBound (fun n ↦ 2 ^ (3000 * n)) :=
  fun n G ↦ hasInducedRamseyOrderAtMost_explicit n G

end FinalAssembly
end Erdos565
