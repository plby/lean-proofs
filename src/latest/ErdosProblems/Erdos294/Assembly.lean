/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos294.Definitions
import ErdosProblems.Erdos294.Representation

/-!
# Finite gluing for Erdős Problem 294

This is the exact combinatorial endgame of Liu--Sawhney's proof.  A first
prescribed subsum is scaled by `t`; a second, disjoint high subsum completes
the mass to one.
-/

open Finset
open scoped BigOperators

namespace Erdos294.Assembly

open Erdos297 Erdos297.LogisticNormalization

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Multiply every denominator in a finite set by `t`. -/
def scaleDenominators (t : ℕ) (B : Finset ℕ) : Finset ℕ :=
  B.image fun n ↦ t * n

@[simp] lemma mem_scaleDenominators {t n : ℕ} {B : Finset ℕ}
    (ht : 0 < t) : n ∈ scaleDenominators t B ↔
      ∃ b ∈ B, t * b = n := by
  simp [scaleDenominators, and_assoc]

lemma rec_sum_scaleDenominators {t : ℕ} (ht : 0 < t) (B : Finset ℕ) :
    UnitFractions.rec_sum (scaleDenominators t B) =
      UnitFractions.rec_sum B / t := by
  rw [scaleDenominators, UnitFractions.rec_sum,
    Finset.sum_image (fun _ _ _ _ h ↦ Nat.eq_of_mul_eq_mul_left ht h)]
  rw [UnitFractions.rec_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n hn
  push_cast
  field_simp [ht.ne']

/-- The first multiple of `t` strictly above `Q + floor(Q/3)`. -/
def glueMultiplier (t Q : ℕ) : ℕ := (Q + Q / 3) / t + 1

/-- Its excess over `Q`. -/
def glueResidual (t Q : ℕ) : ℕ := glueMultiplier t Q * t - Q

lemma glueResidual_bounds {t Q : ℕ} (ht : 3 ≤ t)
    (hlarge : 100 * t < Q) :
    Q / 3 ≤ glueResidual t Q ∧
      glueResidual t Q ≤ 2 * Q / 3 ∧
      glueMultiplier t Q ≤ 2 * Q / 3 := by
  have htpos : 0 < t := by omega
  have hQt : Q + Q / 3 < glueMultiplier t Q * t := by
    simpa [glueMultiplier, Nat.mul_comm] using
      Nat.lt_mul_div_succ (Q + Q / 3) htpos
  have hupper : glueMultiplier t Q * t ≤ Q + Q / 3 + t := by
    calc
      glueMultiplier t Q * t = ((Q + Q / 3) / t) * t + t := by
        simp [glueMultiplier, Nat.add_mul]
      _ ≤ (Q + Q / 3) + t :=
        Nat.add_le_add_right (Nat.div_mul_le_self (Q + Q / 3) t) t
  have htThird : t ≤ Q / 3 := by omega
  have hQle : Q ≤ glueMultiplier t Q * t := by omega
  have hresEq : glueResidual t Q + Q = glueMultiplier t Q * t := by
    rw [glueResidual, Nat.sub_add_cancel hQle]
  have hresLower : Q / 3 ≤ glueResidual t Q := by omega
  have hresUpper : glueResidual t Q ≤ 2 * Q / 3 := by omega
  have hthreeMul : 3 * glueMultiplier t Q ≤
      t * glueMultiplier t Q :=
    Nat.mul_le_mul_right (glueMultiplier t Q) ht
  have hmUpper : glueMultiplier t Q ≤ 2 * Q / 3 := by
    by_contra hnot
    have hm : 2 * Q / 3 < glueMultiplier t Q := Nat.lt_of_not_ge hnot
    have htSmall : t ≤ Q / 100 := by omega
    have hcomm : t * glueMultiplier t Q = glueMultiplier t Q * t :=
      Nat.mul_comm _ _
    omega
  exact ⟨hresLower, hresUpper, hmUpper⟩

/-- Finite two-scale gluing.  All analytic inputs have been reduced to the
two displayed reciprocal-sum witnesses and elementary range separation. -/
theorem represents_of_glued_subsums
    {N t X Q m s : ℕ} {B C : Finset ℕ}
    (ht : 1 ≤ t) (hQ : 0 < Q)
    (hs : s = m * t - Q) (hQmt : Q ≤ m * t)
    (hmQ : m ≤ Q)
    (hBX : B ⊆ goodSet X)
    (hCN : C ⊆ goodSet N)
    (hBsum : UnitFractions.rec_sum B = (s : ℚ) / Q)
    (hCsum : UnitFractions.rec_sum C = ((Q - m : ℕ) : ℚ) / Q)
    (hBbounds : ∀ n ∈ goodSet X, 2 ≤ n ∧ n ≤ X)
    (hCbounds : ∀ n ∈ goodSet N, N / 16 ≤ n ∧ n ≤ N)
    (htX : t * X ≤ N / 100)
    (htSmall : t < N / 100) (hN : 100 ≤ N) :
    Erdos294.Represents N t := by
  have htpos : 0 < t := ht
  let D := scaleDenominators t B
  let A := {t} ∪ D ∪ C
  have hDN : ∀ n ∈ D, n ≤ N / 100 := by
    intro n hn
    obtain ⟨b, hb, rfl⟩ := (mem_scaleDenominators (B := B) htpos).mp hn
    exact (Nat.mul_le_mul_left t (hBbounds b (hBX hb)).2).trans htX
  have hDt : ∀ n ∈ D, t < n := by
    intro n hn
    obtain ⟨b, hb, rfl⟩ := (mem_scaleDenominators (B := B) htpos).mp hn
    nlinarith [hBbounds b (hBX hb)]
  have hCt : ∀ n ∈ C, t < n := by
    intro n hn
    have hlow := (hCbounds n (hCN hn)).1
    have hsep : N / 100 < N / 16 := by omega
    omega
  have hDC : Disjoint D C := by
    rw [Finset.disjoint_left]
    intro n hnD hnC
    have hlow := (hCbounds n (hCN hnC)).1
    have hupp := hDN n hnD
    have hsep : N / 100 < N / 16 := by omega
    omega
  have htD : t ∉ D := by
    intro h
    exact (Nat.lt_irrefl t) (hDt t h)
  have htC : t ∉ C := by
    intro h
    exact (Nat.lt_irrefl t) (hCt t h)
  have hsumFirst : (1 : ℚ) / t + UnitFractions.rec_sum D = (m : ℚ) / Q := by
    rw [show UnitFractions.rec_sum D = UnitFractions.rec_sum B / t by
      simpa [D] using rec_sum_scaleDenominators htpos B, hBsum]
    have hsEq : s + Q = m * t := by
      rw [hs, Nat.sub_add_cancel hQmt]
    have hQne : (Q : ℚ) ≠ 0 := by exact_mod_cast hQ.ne'
    have htne : (t : ℚ) ≠ 0 := by exact_mod_cast htpos.ne'
    field_simp [hQne, htne]
    exact_mod_cast (by simpa [Nat.add_comm, Nat.mul_comm] using hsEq)
  have hsum : UnitFractions.rec_sum A = 1 := by
    have hsingleD : Disjoint ({t} : Finset ℕ) D := by
      simp [htD]
    have hsingleC : Disjoint ({t} : Finset ℕ) C := by
      simp [htC]
    have hunionC : Disjoint (({t} : Finset ℕ) ∪ D) C := by
      rw [Finset.disjoint_union_left]
      exact ⟨hsingleC, hDC⟩
    have htSum : UnitFractions.rec_sum ({t} : Finset ℕ) = (1 : ℚ) / t := by
      simp [UnitFractions.rec_sum]
    rw [show A = ({t} ∪ D) ∪ C by rfl,
      UnitFractions.rec_sum_disjoint hunionC,
      UnitFractions.rec_sum_disjoint hsingleD,
      htSum, hsumFirst, hCsum]
    have hmQ' : Q - m + m = Q := by omega
    have hQne : (Q : ℚ) ≠ 0 := by exact_mod_cast hQ.ne'
    field_simp [hQne]
    exact_mod_cast (by simpa [Nat.add_comm] using hmQ')
  refine ⟨ht, A, ?_, ?_, hsum⟩
  · simp [A]
  · intro n hn
    simp only [A, Finset.mem_union, Finset.mem_singleton] at hn
    rcases hn with (rfl | hnD) | hnC
    · exact ⟨le_rfl, htSmall.le.trans (Nat.div_le_self N 100)⟩
    · exact ⟨(hDt n hnD).le,
        (hDN n hnD).trans (Nat.div_le_self N 100)⟩
    · exact ⟨(hCt n hnC).le, (hCbounds n (hCN hnC)).2⟩

end

end Erdos294.Assembly
