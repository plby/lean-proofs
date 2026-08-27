/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InitialErdosRootDegree
import ErdosProblems.Erdos207.KSSSIndexedThreat

/-! # Fixed coefficient bounds for the exact initial Erdős targets -/

namespace Erdos207

open Finset

noncomputable section

def fullErdosDegreeCoefficient (q : ℕ) : ℕ := 2 ^ (q ^ 3) * (q + 1) * 2 ^ q

theorem fullErdosRootDegree_le_ambient_power
    {V : Type*} [Fintype V] [DecidableEq V] (q d : ℕ) (T : TripleOn V)
    (hd : d + 3 ≤ q) (hN : 1 ≤ (Fintype.card V : ℝ)) :
    fullErdosRootDegree V (d + 3) ≤
      (fullErdosDegreeCoefficient q : ℝ) * (Fintype.card V : ℝ) ^ d := by
  let N : ℝ := Fintype.card V
  have hN0 : 0 ≤ N := by dsimp only [N]; positivity
  have hdegree := card_rootedFullPackingErdosFamily_le_span_power (d + 3) T
  have hdegreeR : ((rootedFullPackingErdosFamily (d + 3) T).card : ℝ) ≤
      (2 ^ ((d + 3) ^ 3) * (d + 3 + 1) : ℕ) * (N + 1) ^ d := by
    have hdeg : d + 3 - 3 = d := by omega
    rw [hdeg] at hdegree
    dsimp only [N]
    exact_mod_cast hdegree
  have hcoef : 2 ^ ((d + 3) ^ 3) * (d + 3 + 1) ≤ 2 ^ (q ^ 3) * (q + 1) := by
    exact Nat.mul_le_mul (Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_left hd 3)) (by omega)
  have hcoefR : ((2 ^ ((d + 3) ^ 3) * (d + 3 + 1) : ℕ) : ℝ) ≤
      ((2 ^ (q ^ 3) * (q + 1) : ℕ) : ℝ) := by exact_mod_cast hcoef
  have hNp : (N + 1) ^ d ≤ (2 : ℝ) ^ q * N ^ d := by
    calc
      _ ≤ (2 * N) ^ d := pow_le_pow_left₀ (by positivity) (by dsimp only [N]; linarith) d
      _ = (2 : ℝ) ^ d * N ^ d := mul_pow _ _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega)) (pow_nonneg hN0 d)
  rw [fullErdosRootDegree_eq_root_card (d + 3) T]
  calc
    _ ≤ ((2 ^ ((d + 3) ^ 3) * (d + 3 + 1) : ℕ) : ℝ) * (N + 1) ^ d := hdegreeR
    _ ≤ ((2 ^ (q ^ 3) * (q + 1) : ℕ) : ℝ) * ((2 : ℝ) ^ q * N ^ d) :=
      mul_le_mul hcoefR hNp (by positivity) (by positivity)
    _ = _ := by simp only [fullErdosDegreeCoefficient, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, N]; ring

theorem initialErdosTrajectoryCoefficient_fixed_bound
    {V : Type*} [Fintype V] [DecidableEq V] (q d : ℕ) (T : TripleOn V) (E A c : ℝ)
    (hd : d + 3 ≤ q) (hN : 1 ≤ (Fintype.card V : ℝ))
    (hE : 0 < E) (hA : 0 < A) (hc : 0 < c)
    (hratio : (Fintype.card V : ℝ) / c ≤ A / E) :
    initialErdosTrajectoryCoefficient V A d * E ^ d ≤ (fullErdosDegreeCoefficient q : ℝ) * c ^ d := by
  let N : ℝ := Fintype.card V
  have hNpos : 0 < N := by dsimp only [N]; linarith
  have hratio' : E / A ≤ c / N := by
    have hmul := (div_le_div_iff₀ hc hE).mp hratio
    apply (div_le_div_iff₀ hA hNpos).mpr
    nlinarith only [hmul]
  have hdegree := fullErdosRootDegree_le_ambient_power q d T hd hN
  have hdegree0 : 0 ≤ fullErdosRootDegree V (d + 3) := by unfold fullErdosRootDegree; positivity
  calc
    _ = fullErdosRootDegree V (d + 3) * (E / A) ^ d := by
      unfold initialErdosTrajectoryCoefficient
      rw [div_pow]
      ring
    _ ≤ ((fullErdosDegreeCoefficient q : ℝ) * N ^ d) * (c / N) ^ d :=
      mul_le_mul hdegree (pow_le_pow_left₀ (div_nonneg hE.le hA.le) hratio' d)
        (by positivity) (by positivity)
    _ = _ := by rw [div_pow]; field_simp

end

end Erdos207
