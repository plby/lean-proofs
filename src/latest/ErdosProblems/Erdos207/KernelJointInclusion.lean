/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FiniteProbability
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Joint inclusion for finite single-insertion kernels

The constrained triangle process changes its chosen family by at most one
triangle per transition.  This file proves the abstract finite-probability
principle that turns a uniform one-point conditional bound into a joint
inclusion bound.  No independence assumption is made.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

/-- Every positive-mass transition enlarges `R` and adds at most one new
ground element. -/
def IsMonotoneSingleInsertionKernel
    {Ω W : Type*} [Fintype Ω] [DecidableEq W]
    (K : Ω → FiniteLaw Ω) (R : Ω → Finset W) : Prop :=
  ∀ ω, FiniteLaw.SupportedOn
    (fun ω' ↦ R ω ⊆ R ω' ∧ (R ω' \ R ω).card ≤ 1) (K ω)

/-- If `A` fits in `C`, does not fit in `B`, and `C \ B` has at most one
element, then deleting one missing element from `A` leaves a subset of `B`.
-/
lemma exists_erase_subset_of_sdiff_card_le_one
    {W : Type*} [DecidableEq W] {A B C : Finset W}
    (hAC : A ⊆ C) (hcard : (C \ B).card ≤ 1) (hAB : ¬ A ⊆ B) :
    ∃ x ∈ A, x ∉ B ∧ A.erase x ⊆ B := by
  obtain ⟨x, hxA, hxB⟩ := not_subset.mp hAB
  refine ⟨x, hxA, hxB, ?_⟩
  intro y hy
  have hy' := mem_erase.mp hy
  by_contra hyB
  have hxsd : x ∈ C \ B := mem_sdiff.mpr ⟨hAC hxA, hxB⟩
  have hysd : y ∈ C \ B := mem_sdiff.mpr ⟨hAC hy'.2, hyB⟩
  have hxy : x ≠ y := Ne.symm hy'.1
  have htwo : 1 < (C \ B).card :=
    one_lt_card.mpr ⟨x, hxsd, y, hysd, hxy⟩
  omega

/-- Conditional one-step subset bound.  The first term accounts for a set
already present; otherwise a single insertion can complete `U` only after
one of its one-point deletions was already present. -/
theorem kernel_probability_subset_le
    {Ω W : Type*} [Fintype Ω] [DecidableEq W]
    (K : Ω → FiniteLaw Ω) (R : Ω → Finset W) (δ : ℝ≥0)
    (hsingle : IsMonotoneSingleInsertionKernel K R)
    (hpoint : ∀ ω x, x ∉ R ω →
      (K ω).probability (fun ω' ↦ x ∈ R ω') ≤ δ)
    (ω : Ω) (U : Finset W) :
    (K ω).probability (fun ω' ↦ U ⊆ R ω') ≤
      (if U ⊆ R ω then 1 else 0) +
        ∑ x ∈ U, if U.erase x ⊆ R ω then δ else 0 := by
  classical
  by_cases hUR : U ⊆ R ω
  · calc
      (K ω).probability (fun ω' ↦ U ⊆ R ω') ≤ 1 :=
        (K ω).probability_le_one _
      _ ≤ (if U ⊆ R ω then 1 else 0) +
          ∑ x ∈ U, if U.erase x ⊆ R ω then δ else 0 := by
        simp only [if_pos hUR]
        exact le_add_of_nonneg_right bot_le
  · have himp : ∀ ω',
        (R ω ⊆ R ω' ∧ (R ω' \ R ω).card ≤ 1) →
        U ⊆ R ω' →
        ∃ x ∈ U, U.erase x ⊆ R ω ∧ x ∈ R ω' := by
      intro ω' hω' hUω'
      obtain ⟨x, hxU, hxR, herase⟩ :=
        exists_erase_subset_of_sdiff_card_le_one hUω' hω'.2 hUR
      exact ⟨x, hxU, herase, hUω' hxU⟩
    have hmono : (K ω).probability (fun ω' ↦ U ⊆ R ω') ≤
        (K ω).probability (fun ω' ↦
          ∃ x ∈ U, U.erase x ⊆ R ω ∧ x ∈ R ω') :=
      (K ω).probability_mono_of_supported (hsingle ω) himp
    have hunion := (K ω).probability_exists_le U
      (fun x ω' ↦ U.erase x ⊆ R ω ∧ x ∈ R ω')
    calc
      (K ω).probability (fun ω' ↦ U ⊆ R ω') ≤
          (K ω).probability (fun ω' ↦
            ∃ x ∈ U, U.erase x ⊆ R ω ∧ x ∈ R ω') := hmono
      _ ≤ ∑ x ∈ U,
          (K ω).probability
            (fun ω' ↦ U.erase x ⊆ R ω ∧ x ∈ R ω') := hunion
      _ ≤ ∑ x ∈ U, if U.erase x ⊆ R ω then δ else 0 := by
        apply Finset.sum_le_sum
        intro x hxU
        by_cases herase : U.erase x ⊆ R ω
        · simp only [if_pos herase]
          have hxR : x ∉ R ω := by
            intro hxR
            apply hUR
            intro y hyU
            by_cases hyx : y = x
            · simpa [hyx] using hxR
            · exact herase (mem_erase.mpr ⟨hyx, hyU⟩)
          exact ((K ω).probability_mono fun ω' h ↦ h.2).trans
            (hpoint ω x hxR)
        · have hfalse : (fun ω' ↦ U.erase x ⊆ R ω ∧ x ∈ R ω') =
              (fun _ ↦ False) := by
            funext ω'
            exact propext ⟨fun h ↦ herase h.1, False.elim⟩
          rw [hfalse, FiniteLaw.probability_false, if_neg herase]
      _ = (if U ⊆ R ω then 1 else 0) +
          ∑ x ∈ U, if U.erase x ⊆ R ω then δ else 0 := by
        simp [hUR]

/-- Averaging the conditional estimate gives the recurrence for one bind.
-/
theorem bind_probability_subset_le
    {Ω W : Type*} [Fintype Ω] [DecidableEq W]
    (K : Ω → FiniteLaw Ω) (R : Ω → Finset W) (δ : ℝ≥0)
    (hsingle : IsMonotoneSingleInsertionKernel K R)
    (hpoint : ∀ ω x, x ∉ R ω →
      (K ω).probability (fun ω' ↦ x ∈ R ω') ≤ δ)
    (L : FiniteLaw Ω) (U : Finset W) :
    (FiniteLaw.bind L K).probability (fun ω ↦ U ⊆ R ω) ≤
      L.probability (fun ω ↦ U ⊆ R ω) +
        δ * ∑ x ∈ U, L.probability (fun ω ↦ U.erase x ⊆ R ω) := by
  classical
  rw [FiniteLaw.probability_bind]
  calc
    (∑ ω, L.mass ω * (K ω).probability (fun ω' ↦ U ⊆ R ω')) ≤
        ∑ ω, L.mass ω *
          ((if U ⊆ R ω then 1 else 0) +
            ∑ x ∈ U, if U.erase x ⊆ R ω then δ else 0) := by
      apply Finset.sum_le_sum
      intro ω _hω
      simpa only [mul_comm] using mul_le_mul_left
        (kernel_probability_subset_le K R δ hsingle hpoint ω U) (L.mass ω)
    _ = L.probability (fun ω ↦ U ⊆ R ω) +
        δ * ∑ x ∈ U,
          L.probability (fun ω ↦ U.erase x ⊆ R ω) := by
      simp only [mul_add, Finset.sum_add_distrib]
      congr 1
      · unfold FiniteLaw.probability
        apply Finset.sum_congr rfl
        intro ω _hω
        by_cases hU : U ⊆ R ω <;> simp [hU]
      · rw [show (∑ ω, L.mass ω *
              ∑ x ∈ U, if U.erase x ⊆ R ω then δ else 0) =
            ∑ ω, ∑ x ∈ U,
              L.mass ω * (if U.erase x ⊆ R ω then δ else 0) by
            apply Finset.sum_congr rfl
            intro ω _hω
            rw [Finset.mul_sum]]
        rw [Finset.sum_comm]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hxU
        unfold FiniteLaw.probability
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ω _hω
        by_cases hx : U.erase x ⊆ R ω <;>
          simp [hx, mul_comm, mul_left_comm, mul_assoc]

/-- Iterating a monotone single-insertion kernel from a state disjoint from
`U` gives a genuine joint bound.  The factorial is the harmless cost of not
assuming independence; the decisive feature is the power `δ ^ |U|`. -/
theorem iterateKernel_probability_subset_le
    {Ω W : Type*} [Fintype Ω] [DecidableEq Ω] [DecidableEq W]
    (K : Ω → FiniteLaw Ω) (R : Ω → Finset W) (δ : ℝ≥0)
    (hsingle : IsMonotoneSingleInsertionKernel K R)
    (hpoint : ∀ ω x, x ∉ R ω →
      (K ω).probability (fun ω' ↦ x ∈ R ω') ≤ δ)
    (ω₀ : Ω) (U : Finset W) (hdisjoint : Disjoint U (R ω₀)) (t : ℕ) :
    (FiniteLaw.iterateKernel K t (FiniteLaw.pure ω₀)).probability
        (fun ω ↦ U ⊆ R ω) ≤
      (U.card.factorial : ℝ≥0) * (((t : ℝ≥0) * δ) ^ U.card) := by
  classical
  induction t generalizing U with
  | zero =>
      simp only [FiniteLaw.iterateKernel]
      rw [FiniteLaw.probability_pure]
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
        rw [FiniteLaw.iterateKernel_succ_right]
        have hrec := bind_probability_subset_le K R δ hsingle hpoint
          (FiniteLaw.iterateKernel K t (FiniteLaw.pure ω₀)) U
        have hUbound := ih U hdisjoint
        have herase (x : W) (hx : x ∈ U) :
            (FiniteLaw.iterateKernel K t (FiniteLaw.pure ω₀)).probability
                (fun ω ↦ U.erase x ⊆ R ω) ≤
              (s.factorial : ℝ≥0) * (((t : ℝ≥0) * δ) ^ s) := by
          have hd : Disjoint (U.erase x) (R ω₀) :=
            hdisjoint.mono_left (erase_subset x U)
          have h := ih (U.erase x) hd
          simpa [card_erase_of_mem hx, hcard] using h
        have hsum :
            ∑ x ∈ U,
                (FiniteLaw.iterateKernel K t (FiniteLaw.pure ω₀)).probability
                  (fun ω ↦ U.erase x ⊆ R ω) ≤
              (s + 1 : ℝ≥0) *
                ((s.factorial : ℝ≥0) * (((t : ℝ≥0) * δ) ^ s)) := by
          calc
            ∑ x ∈ U,
                (FiniteLaw.iterateKernel K t (FiniteLaw.pure ω₀)).probability
                  (fun ω ↦ U.erase x ⊆ R ω) ≤
                ∑ _x ∈ U,
                  (s.factorial : ℝ≥0) * (((t : ℝ≥0) * δ) ^ s) := by
              apply Finset.sum_le_sum
              intro x hx
              exact herase x hx
            _ = (s + 1 : ℝ≥0) *
                ((s.factorial : ℝ≥0) * (((t : ℝ≥0) * δ) ^ s)) := by
              simp [hcard]
        have htmono : (t : ℝ≥0) ^ s ≤ ((t : ℝ≥0) + 1) ^ s :=
          pow_le_pow_left' (by exact le_add_of_nonneg_right zero_le_one) s
        have hpow :
            (t : ℝ≥0) ^ (s + 1) + (t : ℝ≥0) ^ s ≤
              (t + 1 : ℝ≥0) ^ (s + 1) := by
          calc
            (t : ℝ≥0) ^ (s + 1) + (t : ℝ≥0) ^ s =
                (t : ℝ≥0) ^ s * ((t : ℝ≥0) + 1) := by
              rw [pow_succ]
              ring
            _ ≤ ((t : ℝ≥0) + 1) ^ s * ((t : ℝ≥0) + 1) :=
              by
                simpa only [mul_comm] using
                  mul_le_mul_left htmono ((t : ℝ≥0) + 1)
            _ = (t + 1 : ℝ≥0) ^ (s + 1) := by
              rw [pow_succ]
        calc
          (FiniteLaw.bind
              (FiniteLaw.iterateKernel K t (FiniteLaw.pure ω₀)) K).probability
                (fun ω ↦ U ⊆ R ω) ≤
              (FiniteLaw.iterateKernel K t (FiniteLaw.pure ω₀)).probability
                  (fun ω ↦ U ⊆ R ω) +
                δ * ∑ x ∈ U,
                  (FiniteLaw.iterateKernel K t (FiniteLaw.pure ω₀)).probability
                    (fun ω ↦ U.erase x ⊆ R ω) := hrec
          _ ≤ (U.card.factorial : ℝ≥0) * (((t : ℝ≥0) * δ) ^ U.card) +
                δ * ((s + 1 : ℝ≥0) *
                  ((s.factorial : ℝ≥0) * (((t : ℝ≥0) * δ) ^ s))) :=
            add_le_add hUbound (by
              simpa only [mul_comm] using mul_le_mul_left hsum δ)
          _ = ((s + 1).factorial : ℝ≥0) * δ ^ (s + 1) *
                ((t : ℝ≥0) ^ (s + 1) + (t : ℝ≥0) ^ s) := by
            simp only [hcard, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
              Nat.cast_one, mul_pow, pow_succ]
            ring
          _ ≤ ((s + 1).factorial : ℝ≥0) * δ ^ (s + 1) *
                (t + 1 : ℝ≥0) ^ (s + 1) :=
            by
              simpa only [mul_comm, mul_left_comm, mul_assoc] using
                mul_le_mul_left hpow
                  (((s + 1).factorial : ℝ≥0) * δ ^ (s + 1))
          _ = (U.card.factorial : ℝ≥0) *
                ((((t + 1 : ℕ) : ℝ≥0) * δ) ^ U.card) := by
            simp only [hcard, mul_pow, Nat.cast_add, Nat.cast_one]
            ring

end

end Erdos207
