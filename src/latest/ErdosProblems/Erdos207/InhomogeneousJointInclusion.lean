/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KernelJointInclusion
import ErdosProblems.Erdos207.FiniteKernelConcentration

/-!
# Joint inclusion for time-inhomogeneous kernels

The point hazard of the greedy process grows as availability falls.  This
version of the single-insertion lemma permits a separate one-step bound
`δ i` and pays only their sum.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

/-- A time-inhomogeneous monotone single-insertion process has the same
factorial joint-inclusion bound with cumulative hazard `∑ δᵢ`. -/
theorem evolveKernels_probability_subset_le
    {Ω W : Type*} [Fintype Ω] [DecidableEq Ω] [DecidableEq W]
    (K : ℕ → Ω → FiniteLaw Ω) (R : Ω → Finset W) (δ : ℕ → ℝ≥0)
    (hsingle : ∀ i, IsMonotoneSingleInsertionKernel (K i) R)
    (hpoint : ∀ i ω x, x ∉ R ω →
      (K i ω).probability (fun ω' ↦ x ∈ R ω') ≤ δ i)
    (ω₀ : Ω) (U : Finset W) (hdisjoint : Disjoint U (R ω₀)) (t : ℕ) :
    (FiniteLaw.evolveKernels K t (FiniteLaw.pure ω₀)).probability
        (fun ω ↦ U ⊆ R ω) ≤
      (U.card.factorial : ℝ≥0) *
        ((∑ i ∈ range t, δ i) ^ U.card) := by
  classical
  induction t generalizing U with
  | zero =>
      simp only [FiniteLaw.evolveKernels_zero, FiniteLaw.probability_pure,
        range_zero, sum_empty]
      by_cases hU : U = ∅
      · subst U
        simp
      · have hnot : ¬ U ⊆ R ω₀ := by
          intro hsub
          obtain ⟨x, hxU⟩ := nonempty_iff_ne_empty.mpr hU
          exact Finset.disjoint_left.mp hdisjoint hxU (hsub hxU)
        rw [if_neg hnot]
        exact bot_le
  | succ t ih =>
      by_cases hU : U = ∅
      · subst U
        simp [FiniteLaw.probability_true]
      · have hcardpos : 0 < U.card := card_pos.mpr
          (nonempty_iff_ne_empty.mpr hU)
        obtain ⟨s, hcard⟩ : ∃ s, U.card = s + 1 :=
          Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hcardpos)
        rw [FiniteLaw.evolveKernels_succ]
        have hrec := bind_probability_subset_le (K t) R (δ t)
          (hsingle t) (hpoint t)
          (FiniteLaw.evolveKernels K t (FiniteLaw.pure ω₀)) U
        have hUbound := ih U hdisjoint
        have herase (x : W) (hx : x ∈ U) :
            (FiniteLaw.evolveKernels K t (FiniteLaw.pure ω₀)).probability
                (fun ω ↦ U.erase x ⊆ R ω) ≤
              (s.factorial : ℝ≥0) *
                ((∑ i ∈ range t, δ i) ^ s) := by
          have hd : Disjoint (U.erase x) (R ω₀) :=
            hdisjoint.mono_left (erase_subset x U)
          have h := ih (U.erase x) hd
          simpa [card_erase_of_mem hx, hcard] using h
        have hsum :
            ∑ x ∈ U,
                (FiniteLaw.evolveKernels K t (FiniteLaw.pure ω₀)).probability
                  (fun ω ↦ U.erase x ⊆ R ω) ≤
              (s + 1 : ℝ≥0) *
                ((s.factorial : ℝ≥0) *
                  ((∑ i ∈ range t, δ i) ^ s)) := by
          calc
            ∑ x ∈ U,
                (FiniteLaw.evolveKernels K t (FiniteLaw.pure ω₀)).probability
                  (fun ω ↦ U.erase x ⊆ R ω) ≤
              ∑ _x ∈ U, (s.factorial : ℝ≥0) *
                ((∑ i ∈ range t, δ i) ^ s) := by
                  apply sum_le_sum
                  intro x hx
                  exact herase x hx
            _ = (s + 1 : ℝ≥0) *
                ((s.factorial : ℝ≥0) *
                  ((∑ i ∈ range t, δ i) ^ s)) := by simp [hcard]
        let D : ℝ≥0 := ∑ i ∈ range t, δ i
        have hpow : D ^ (s + 1) + δ t * D ^ s ≤
            (D + δ t) ^ (s + 1) := by
          have hmono : D ^ s ≤ (D + δ t) ^ s :=
            pow_le_pow_left' (le_add_of_nonneg_right bot_le) s
          calc
            D ^ (s + 1) + δ t * D ^ s = D ^ s * (D + δ t) := by
              rw [pow_succ]
              ring
            _ ≤ (D + δ t) ^ s * (D + δ t) := by
              simpa only [mul_comm] using mul_le_mul_left hmono (D + δ t)
            _ = (D + δ t) ^ (s + 1) := by rw [pow_succ]
        calc
          (FiniteLaw.bind
              (FiniteLaw.evolveKernels K t (FiniteLaw.pure ω₀))
              (K t)).probability (fun ω ↦ U ⊆ R ω) ≤
            (FiniteLaw.evolveKernels K t (FiniteLaw.pure ω₀)).probability
                (fun ω ↦ U ⊆ R ω) +
              δ t * ∑ x ∈ U,
                (FiniteLaw.evolveKernels K t (FiniteLaw.pure ω₀)).probability
                  (fun ω ↦ U.erase x ⊆ R ω) := hrec
          _ ≤ (U.card.factorial : ℝ≥0) *
                ((∑ i ∈ range t, δ i) ^ U.card) +
              δ t * ((s + 1 : ℝ≥0) *
                ((s.factorial : ℝ≥0) *
                  ((∑ i ∈ range t, δ i) ^ s))) :=
            add_le_add hUbound (by
              simpa only [mul_comm] using mul_le_mul_left hsum (δ t))
          _ = ((s + 1).factorial : ℝ≥0) *
              (D ^ (s + 1) + δ t * D ^ s) := by
            simp only [hcard, Nat.factorial_succ, Nat.cast_mul,
              Nat.cast_add, Nat.cast_one, D]
            ring
          _ ≤ ((s + 1).factorial : ℝ≥0) *
              (D + δ t) ^ (s + 1) := by
            simpa only [mul_comm] using
              mul_le_mul_left hpow ((s + 1).factorial : ℝ≥0)
          _ = (U.card.factorial : ℝ≥0) *
              ((∑ i ∈ range (t + 1), δ i) ^ U.card) := by
            rw [sum_range_succ]
            simp only [hcard, D]

end

end Erdos207
