/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KernelJointInclusion
import ErdosProblems.Erdos207.WeightSystem

/-!
# Element-weighted joint inclusion for single-insertion kernels

The scalar joint-inclusion lemma is insufficient for a vortex: triangles at
different levels have different natural hazards.  The proofs below retain a
pointwise one-step envelope `pi x`.  After `t` steps, the joint-inclusion
bound is `|U|! * t^|U| * setWeight pi U`.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

theorem kernel_probability_subset_le_pointWeight
    {Ω W : Type*} [Fintype Ω] [DecidableEq W]
    (K : Ω → FiniteLaw Ω) (R : Ω → Finset W) (pi : W → ℝ≥0)
    (hsingle : IsMonotoneSingleInsertionKernel K R)
    (hpoint : ∀ omega x, x ∉ R omega →
      (K omega).probability (fun omega' ↦ x ∈ R omega') ≤ pi x)
    (omega : Ω) (U : Finset W) :
    (K omega).probability (fun omega' ↦ U ⊆ R omega') ≤
      (if U ⊆ R omega then 1 else 0) +
        ∑ x ∈ U, if U.erase x ⊆ R omega then pi x else 0 := by
  classical
  by_cases hUR : U ⊆ R omega
  · calc
      (K omega).probability (fun omega' ↦ U ⊆ R omega') ≤ 1 :=
        (K omega).probability_le_one _
      _ ≤ (if U ⊆ R omega then 1 else 0) +
          ∑ x ∈ U, if U.erase x ⊆ R omega then pi x else 0 := by
        simp only [if_pos hUR]
        exact le_add_of_nonneg_right bot_le
  · have himp : ∀ omega',
        (R omega ⊆ R omega' ∧ (R omega' \ R omega).card ≤ 1) →
        U ⊆ R omega' →
        ∃ x ∈ U, U.erase x ⊆ R omega ∧ x ∈ R omega' := by
      intro omega' homega' hUomega'
      obtain ⟨x, hxU, hxR, herase⟩ :=
        exists_erase_subset_of_sdiff_card_le_one hUomega' homega'.2 hUR
      exact ⟨x, hxU, herase, hUomega' hxU⟩
    have hmono : (K omega).probability (fun omega' ↦ U ⊆ R omega') ≤
        (K omega).probability (fun omega' ↦
          ∃ x ∈ U, U.erase x ⊆ R omega ∧ x ∈ R omega') :=
      (K omega).probability_mono_of_supported (hsingle omega) himp
    have hunion := (K omega).probability_exists_le U
      (fun x omega' ↦ U.erase x ⊆ R omega ∧ x ∈ R omega')
    calc
      (K omega).probability (fun omega' ↦ U ⊆ R omega') ≤
          (K omega).probability (fun omega' ↦
            ∃ x ∈ U, U.erase x ⊆ R omega ∧ x ∈ R omega') := hmono
      _ ≤ ∑ x ∈ U,
          (K omega).probability
            (fun omega' ↦ U.erase x ⊆ R omega ∧ x ∈ R omega') := hunion
      _ ≤ ∑ x ∈ U,
          if U.erase x ⊆ R omega then pi x else 0 := by
        apply sum_le_sum
        intro x hxU
        by_cases herase : U.erase x ⊆ R omega
        · simp only [if_pos herase]
          have hxR : x ∉ R omega := by
            intro hxR
            apply hUR
            intro y hyU
            by_cases hyx : y = x
            · simpa [hyx] using hxR
            · exact herase (mem_erase.mpr ⟨hyx, hyU⟩)
          exact ((K omega).probability_mono fun omega' h ↦ h.2).trans
            (hpoint omega x hxR)
        · have hfalse :
              (fun omega' ↦ U.erase x ⊆ R omega ∧ x ∈ R omega') =
                (fun _ ↦ False) := by
            funext omega'
            exact propext ⟨fun h ↦ herase h.1, False.elim⟩
          rw [hfalse, FiniteLaw.probability_false, if_neg herase]
      _ = (if U ⊆ R omega then 1 else 0) +
          ∑ x ∈ U, if U.erase x ⊆ R omega then pi x else 0 := by
        simp [hUR]

theorem bind_probability_subset_le_pointWeight
    {Ω W : Type*} [Fintype Ω] [DecidableEq W]
    (K : Ω → FiniteLaw Ω) (R : Ω → Finset W) (pi : W → ℝ≥0)
    (hsingle : IsMonotoneSingleInsertionKernel K R)
    (hpoint : ∀ omega x, x ∉ R omega →
      (K omega).probability (fun omega' ↦ x ∈ R omega') ≤ pi x)
    (L : FiniteLaw Ω) (U : Finset W) :
    (FiniteLaw.bind L K).probability (fun omega ↦ U ⊆ R omega) ≤
      L.probability (fun omega ↦ U ⊆ R omega) +
        ∑ x ∈ U, pi x *
          L.probability (fun omega ↦ U.erase x ⊆ R omega) := by
  classical
  rw [FiniteLaw.probability_bind]
  calc
    (∑ omega, L.mass omega *
        (K omega).probability (fun omega' ↦ U ⊆ R omega')) ≤
      ∑ omega, L.mass omega *
        ((if U ⊆ R omega then 1 else 0) +
          ∑ x ∈ U, if U.erase x ⊆ R omega then pi x else 0) := by
      apply sum_le_sum
      intro omega _homega
      simpa only [mul_comm] using mul_le_mul_left
        (kernel_probability_subset_le_pointWeight
          K R pi hsingle hpoint omega U) (L.mass omega)
    _ = L.probability (fun omega ↦ U ⊆ R omega) +
        ∑ x ∈ U, pi x *
          L.probability (fun omega ↦ U.erase x ⊆ R omega) := by
      simp only [mul_add, sum_add_distrib]
      congr 1
      · unfold FiniteLaw.probability
        apply sum_congr rfl
        intro omega _homega
        by_cases hU : U ⊆ R omega <;> simp [hU]
      · rw [show (∑ omega, L.mass omega *
              ∑ x ∈ U,
                if U.erase x ⊆ R omega then pi x else 0) =
            ∑ omega, ∑ x ∈ U,
              L.mass omega *
                (if U.erase x ⊆ R omega then pi x else 0) by
            apply sum_congr rfl
            intro omega _homega
            rw [mul_sum]]
        rw [sum_comm]
        apply sum_congr rfl
        intro x hxU
        unfold FiniteLaw.probability
        rw [mul_sum]
        apply sum_congr rfl
        intro omega _homega
        by_cases hx : U.erase x ⊆ R omega <;>
          simp [hx, mul_comm, mul_left_comm, mul_assoc]

lemma pointWeight_mul_erase
    {W : Type*} [DecidableEq W] (pi : W → ℝ≥0)
    {U : Finset W} {x : W} (hx : x ∈ U) :
    pi x * setWeight pi (U.erase x) = setWeight pi U := by
  simpa only [setWeight] using Finset.mul_prod_erase U pi hx

/-- Joint-inclusion bound retaining the product of the individual point
hazards. -/
theorem iterateKernel_probability_subset_le_pointWeight
    {Ω W : Type*} [Fintype Ω] [DecidableEq Ω] [DecidableEq W]
    (K : Ω → FiniteLaw Ω) (R : Ω → Finset W) (pi : W → ℝ≥0)
    (hsingle : IsMonotoneSingleInsertionKernel K R)
    (hpoint : ∀ omega x, x ∉ R omega →
      (K omega).probability (fun omega' ↦ x ∈ R omega') ≤ pi x)
    (omega0 : Ω) (U : Finset W) (hdisjoint : Disjoint U (R omega0))
    (t : ℕ) :
    (FiniteLaw.iterateKernel K t (FiniteLaw.pure omega0)).probability
        (fun omega ↦ U ⊆ R omega) ≤
      (U.card.factorial : ℝ≥0) *
        (t : ℝ≥0) ^ U.card * setWeight pi U := by
  classical
  induction t generalizing U with
  | zero =>
      simp only [FiniteLaw.iterateKernel, FiniteLaw.probability_pure,
        Nat.cast_zero, zero_pow]
      by_cases hU : U = ∅
      · subst U
        simp [setWeight]
      · have hcard : U.card ≠ 0 :=
          card_ne_zero.mpr (nonempty_iff_ne_empty.mpr hU)
        have hnot : ¬ U ⊆ R omega0 := by
          intro hsub
          obtain ⟨x, hxU⟩ := nonempty_iff_ne_empty.mpr hU
          exact disjoint_left.mp hdisjoint hxU (hsub hxU)
        simp [hnot, hcard]
  | succ t ih =>
      by_cases hU : U = ∅
      · subst U
        simp [FiniteLaw.probability_true, setWeight]
      · have hcardpos : 0 < U.card := card_pos.mpr
          (nonempty_iff_ne_empty.mpr hU)
        obtain ⟨s, hcard⟩ : ∃ s, U.card = s + 1 :=
          Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hcardpos)
        rw [FiniteLaw.iterateKernel_succ_right]
        have hrec := bind_probability_subset_le_pointWeight
          K R pi hsingle hpoint
          (FiniteLaw.iterateKernel K t (FiniteLaw.pure omega0)) U
        have hUbound := ih U hdisjoint
        have herase (x : W) (hx : x ∈ U) :
            (FiniteLaw.iterateKernel K t (FiniteLaw.pure omega0)).probability
                (fun omega ↦ U.erase x ⊆ R omega) ≤
              (s.factorial : ℝ≥0) * (t : ℝ≥0) ^ s *
                setWeight pi (U.erase x) := by
          have hd : Disjoint (U.erase x) (R omega0) :=
            hdisjoint.mono_left (erase_subset x U)
          have h := ih (U.erase x) hd
          simpa [card_erase_of_mem hx, hcard] using h
        have hsum :
            ∑ x ∈ U, pi x *
                (FiniteLaw.iterateKernel K t
                  (FiniteLaw.pure omega0)).probability
                    (fun omega ↦ U.erase x ⊆ R omega) ≤
              (s + 1 : ℝ≥0) *
                ((s.factorial : ℝ≥0) * (t : ℝ≥0) ^ s *
                  setWeight pi U) := by
          calc
            ∑ x ∈ U, pi x *
                (FiniteLaw.iterateKernel K t
                  (FiniteLaw.pure omega0)).probability
                    (fun omega ↦ U.erase x ⊆ R omega) ≤
              ∑ x ∈ U, pi x *
                ((s.factorial : ℝ≥0) * (t : ℝ≥0) ^ s *
                  setWeight pi (U.erase x)) := by
                apply sum_le_sum
                intro x hx
                simpa only [mul_comm] using
                  mul_le_mul_left (herase x hx) (pi x)
            _ = ∑ _x ∈ U,
                ((s.factorial : ℝ≥0) * (t : ℝ≥0) ^ s *
                  setWeight pi U) := by
                apply sum_congr rfl
                intro x hx
                rw [← pointWeight_mul_erase pi hx]
                ring
            _ = (s + 1 : ℝ≥0) *
                ((s.factorial : ℝ≥0) * (t : ℝ≥0) ^ s *
                  setWeight pi U) := by simp [hcard]
        have hpow : (t : ℝ≥0) ^ (s + 1) + (t : ℝ≥0) ^ s ≤
            (t + 1 : ℝ≥0) ^ (s + 1) := by
          calc
            (t : ℝ≥0) ^ (s + 1) + (t : ℝ≥0) ^ s =
                (t : ℝ≥0) ^ s * ((t : ℝ≥0) + 1) := by
              rw [pow_succ]
              ring
            _ ≤ ((t : ℝ≥0) + 1) ^ s * ((t : ℝ≥0) + 1) := by
              gcongr
              exact le_add_of_nonneg_right zero_le_one
            _ = (t + 1 : ℝ≥0) ^ (s + 1) := by rw [pow_succ]
        calc
          (FiniteLaw.bind
              (FiniteLaw.iterateKernel K t (FiniteLaw.pure omega0)) K).probability
                (fun omega ↦ U ⊆ R omega) ≤
              (FiniteLaw.iterateKernel K t (FiniteLaw.pure omega0)).probability
                  (fun omega ↦ U ⊆ R omega) +
                ∑ x ∈ U, pi x *
                  (FiniteLaw.iterateKernel K t
                    (FiniteLaw.pure omega0)).probability
                      (fun omega ↦ U.erase x ⊆ R omega) := hrec
          _ ≤ (U.card.factorial : ℝ≥0) * (t : ℝ≥0) ^ U.card *
                setWeight pi U +
              (s + 1 : ℝ≥0) *
                ((s.factorial : ℝ≥0) * (t : ℝ≥0) ^ s *
                  setWeight pi U) := add_le_add hUbound hsum
          _ = ((s + 1).factorial : ℝ≥0) *
                ((t : ℝ≥0) ^ (s + 1) + (t : ℝ≥0) ^ s) *
                  setWeight pi U := by
            simp only [hcard, Nat.factorial_succ, Nat.cast_mul,
              Nat.cast_add, Nat.cast_one]
            ring
          _ ≤ ((s + 1).factorial : ℝ≥0) *
                (t + 1 : ℝ≥0) ^ (s + 1) * setWeight pi U := by
            gcongr
          _ = (U.card.factorial : ℝ≥0) *
                ((t + 1 : ℕ) : ℝ≥0) ^ U.card * setWeight pi U := by
            simp only [hcard, Nat.cast_add, Nat.cast_one]

end

end Erdos207
