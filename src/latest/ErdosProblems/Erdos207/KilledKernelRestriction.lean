/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FiniteKernelConcentration

/-!
# Killing a kernel outside a monotone region

If a Markov kernel can never re-enter an `alive` region after leaving it,
then replacing every transition outside that region by a self-loop does not
change the mass of any alive state.  Hence all events contained in the alive
region have the same probability under the original and killed evolutions.
This is the finite coupling lemma used to stop a pair-extension observable
when its pair becomes covered.
-/

namespace Erdos207

open scoped BigOperators NNReal

noncomputable section

namespace FiniteLaw

/-- Freeze a time-inhomogeneous kernel outside a prescribed region. -/
def killKernel
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (alive : Ω → Prop) [DecidablePred alive]
    (K : ℕ → Ω → FiniteLaw Ω) (i : ℕ) (x : Ω) : FiniteLaw Ω :=
  if alive x then K i x else pure x

/-- Killing outside a region which cannot be re-entered preserves the point
mass of every alive state at every time. -/
theorem evolveKernels_mass_killKernel_eq_of_alive
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (alive : Ω → Prop) [DecidablePred alive]
    (K : ℕ → Ω → FiniteLaw Ω) (L : FiniteLaw Ω)
    (hdead : ∀ i x, ¬ alive x →
      (K i x).SupportedOn (fun y ↦ ¬ alive y)) :
    ∀ n y, alive y →
      (evolveKernels K n L).mass y =
        (evolveKernels (killKernel alive K) n L).mass y := by
  intro n
  induction n with
  | zero =>
      intro y _hy
      rfl
  | succ n ih =>
      intro y hy
      simp only [evolveKernels_succ, bind]
      apply Finset.sum_congr rfl
      intro x _hx
      by_cases hx : alive x
      · rw [ih x hx]
        simp [killKernel, hx]
      · have hKzero : (K n x).mass y = 0 := by
          apply le_antisymm
          · apply not_lt.mp
            intro hpos
            exact (hdead n x hx y hpos) hy
          · exact zero_le
        have hyx : y ≠ x := by
          intro hyx
          subst x
          exact hx hy
        simp [killKernel, hx, hKzero, pure, hyx]

/-- Event-probability form of the killed-kernel comparison. -/
theorem evolveKernels_probability_killKernel_eq_of_subset_alive
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (alive : Ω → Prop) [DecidablePred alive]
    (K : ℕ → Ω → FiniteLaw Ω) (L : FiniteLaw Ω)
    (hdead : ∀ i x, ¬ alive x →
      (K i x).SupportedOn (fun y ↦ ¬ alive y))
    (n : ℕ) (P : Ω → Prop) (hP : ∀ x, P x → alive x) :
    (evolveKernels K n L).probability P =
      (evolveKernels (killKernel alive K) n L).probability P := by
  classical
  unfold probability
  apply Finset.sum_congr rfl
  intro x _hx
  by_cases hPx : P x
  · simp only [hPx, if_true]
    exact evolveKernels_mass_killKernel_eq_of_alive
      alive K L hdead n x (hP x hPx)
  · simp [hPx]

end FiniteLaw

end

end Erdos207
