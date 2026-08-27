/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceCorrelatedNumericBudget
import ErdosProblems.Erdos207.EventualPreliminaryDegreeBudget
import ErdosProblems.Erdos207.UniformSourceMomentBudgets
import ErdosProblems.Erdos207.SourceLinkFiniteUnionBudgets
import ErdosProblems.Erdos207.SourceMasterConstants
import ErdosProblems.Erdos207.FiniteBackwardErrorSchedule

/-! # Fixed error exponents construct the actual correlated internal-stage budgets -/

namespace Erdos207

open Finset
open scoped Classical NNReal

theorem eventually_source_internal_numeric_budget
    (q ell R b reserveExp v d D L : ℕ) (eta0 constant C B0 : ℝ≥0)
    (hb : 2 ≤ b) (heta0 : 0 < eta0) (heta01 : eta0 ≤ 1) (hconstant : 1 ≤ constant)
    (hinnerGap : 2*reserveExp+3*b+v+2 ≤ L)
    (hrateGap : 2*reserveExp+2*b+v+2 ≤ d) (hpointGap : 2*b+1 ≤ D) :
    ∃ degreeMoment M T : ℕ, 1 ≤ degreeMoment ∧ 1 ≤ M ∧ 1 ≤ T ∧ ∀ t : ℕ, T ≤ t →
      ∀ (N n c : ℕ) (u analytic p eta beta delta : ℝ≥0),
      N ≤ t^R → n ≤ t^R → t^D ≤ n → (t : ℝ≥0)^L ≤ u →
      (n : ℝ≥0) ≤ (t : ℝ≥0)^v*u → (t : ℝ≥0)^d ≤ analytic^c →
      1/(t : ℝ≥0)^b ≤ p → p ≤ 2/(t : ℝ≥0)^b → eta0 ≤ eta →
      beta ≤ B0/(t : ℝ≥0)^M → delta ≤ 1/(t : ℝ≥0)^M →
      let r := 1/(t : ℝ≥0)^reserveExp
      let mu := r^2*p^2*eta*u
      let factor := 152*constant/eta0
      let alpha := factor/(p^2*n)
      let rate := (2*constant)/(t : ℝ≥0)^d
      let rawC := 2*max (C^3*factor) (2*constant)
      1 ≤ factor ∧ 1 ≤ 2*constant ∧ alpha ≤ 1 ∧ rate ≤ 1 ∧ rate ≤ r ∧
      constant*(2/analytic^c) ≤ rate ∧
      constant*(24/(p^2*eta*n))+(constant*(2/analytic^c))*(64/mu) ≤ alpha ∧
      alpha*p^3 ≤ factor*(p/n) ∧
      512 ≤ mu ∧ 2*degreeMoment ≤ ⌊mu/256⌋₊+1 ∧
      (eta0/128)*p^2*r^2*u ≤ ⌈mu/128⌉₊ ∧
      (∀ k ≤ ell, ∀ j ≤ q,
        sourceLeftFailureBound k j (2*R+4) N p r rawC (beta+delta) (sourcePrefixY q k)
          ((eta0/128)/((Icc 4 q).card+1 : ℝ≥0)) u ≤ 1/(t : ℝ≥0)^(2*R+3)) ∧
      sourcePreliminaryDegreeFailure N n ⌊mu/256⌋₊ degreeMoment rate constant delta ≤ 1/(t : ℝ≥0)^3 ∧
      sourcePreliminaryDegreeFailure N n ⌊mu/256⌋₊ degreeMoment rate constant delta +
        (N : ℝ≥0)^2*∑ _j ∈ Icc 4 q, (1/(t : ℝ≥0)^(2*R+3)) ≤ 2/(t : ℝ≥0)^2 ∧
      2/(t : ℝ≥0)^2 ≤ 1/2 ∧
      sourcePreliminaryDegreeFailure N n ⌊mu/256⌋₊ degreeMoment rate constant delta /
        (1-2/(t : ℝ≥0)^2) ≤ 2/(t : ℝ≥0)^3 := by
  let orders := Icc 4 q
  let factor := 152*constant/eta0
  let rawC := 2*max (C^3*factor) (2*constant)
  let epsilonLeft := (eta0/128)/(orders.card+1 : ℝ≥0)
  have hepsilonLeft : 0 < epsilonLeft := by dsimp only [epsilonLeft]; positivity
  obtain ⟨degreeMoment, degreeExponent, Tdegree, hdegreeMoment, hTdegree, hdegree⟩ :=
    eventually_source_preliminary_degree_budget reserveExp b v d L R 3 eta0 constant heta0 (by omega) (by omega)
  obtain ⟨leftExponent, Tleft, hleftExponent, hTleft, hleft⟩ :=
    eventually_uniform_source_left_moments q ell R b reserveExp (2*R+3) rawC epsilonLeft (B0+1)
      (by omega) hepsilonLeft
  let constraints : Finset ℝ≥0 := {2, 2*constant, factor, (orders.card : ℝ≥0)}
  let Tscalar := ⌈∑ x ∈ constraints, x⌉₊
  let M := max degreeExponent leftExponent
  let T := Tdegree+Tleft+Tscalar+2
  refine ⟨degreeMoment, M, T, hdegreeMoment, hleftExponent.trans (le_max_right _ _),
    by dsimp only [T]; omega, ?_⟩
  intro t ht N n c u analytic p eta beta delta hN hn hnLower hu hsize hpower hp hpUpper heta hbeta hdelta
  dsimp only
  have ht2 : 2 ≤ t := by dsimp only [T] at ht; omega
  have htNN : (1 : ℝ≥0) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)
  have ht0 : (0 : ℝ≥0) < t := zero_lt_one.trans_le htNN
  have htScalar : Tscalar ≤ t := by dsimp only [T] at ht; omega
  have hconstraints : ∀ x ∈ constraints, x ≤ (t : ℝ≥0) := by
    intro x hx
    exact (single_le_sum (fun _ _ ↦ zero_le) hx).trans
      ((Nat.le_ceil (∑ x ∈ constraints, x)).trans (by exact_mod_cast htScalar))
  have hconstantT : 2*constant ≤ (t : ℝ≥0) :=
    hconstraints _ (by simp only [constraints, mem_insert, mem_singleton, eq_self, or_true, true_or])
  have hfactorT : factor ≤ (t : ℝ≥0) :=
    hconstraints _ (by simp only [constraints, mem_insert, mem_singleton, eq_self, or_true, true_or])
  have hordersT : (orders.card : ℝ≥0) ≤ t :=
    hconstraints _ (by simp only [constraints, mem_insert, mem_singleton, eq_self, or_true])
  let r : ℝ≥0 := 1/(t : ℝ≥0)^reserveExp
  let mu := r^2*p^2*eta*u
  let rate := (2*constant)/(t : ℝ≥0)^d
  have hu0 : 0 < u := (pow_pos ht0 L).trans_le hu
  have hnumeric := source_correlated_internal_numeric_budget t analytic n u p eta eta0 constant
    c d reserveExp b v D htNN hu0 heta0 heta01 heta hconstant hpower hp
    (by exact_mod_cast hnLower) hsize (by omega) (by omega) hpointGap hconstantT hfactorT
  have hdeltaDegree : delta ≤ 1/(t : ℝ≥0)^degreeExponent := hdelta.trans
    (polynomial_incoming_error_budget t 1 M degreeExponent htNN (le_max_left _ _))
  have hDegree := hdegree t (by dsimp only [T] at ht; omega) N n u p eta rate delta hN hn hsize hu hp heta
    le_rfl hdeltaDegree
  have herror : beta+delta ≤ (B0+1)/(t : ℝ≥0)^M := by
    calc
      _ ≤ B0/(t : ℝ≥0)^M+1/(t : ℝ≥0)^M := add_le_add hbeta hdelta
      _ = _ := by ring
  have herrorLeft : beta+delta ≤ (B0+1)/(t : ℝ≥0)^leftExponent := herror.trans
    (polynomial_incoming_error_budget t (B0+1) M leftExponent htNN (le_max_right _ _))
  have hUone : 1 ≤ u := (one_le_pow₀ htNN).trans hu
  have hLeft : ∀ k ≤ ell, ∀ j ≤ q,
      sourceLeftFailureBound k j (2*R+4) N p r rawC (beta+delta) (sourcePrefixY q k) epsilonLeft u ≤
        1/(t : ℝ≥0)^(2*R+3) := by
    intro k hk j hj
    exact hleft t (by dsimp only [T] at ht; omega) k hk j hj N p r (beta+delta) epsilonLeft u
      hN hUone hp hpUpper le_rfl le_rfl herrorLeft
  have hepsilonEta : (128 : ℝ≥0)*(eta0/128) ≤ eta := by
    calc
      (128 : ℝ≥0)*(eta0/128) = eta0 := by ring
      _ ≤ eta := heta
  have hcap := (internal_cover_rounded_left_and_point p r eta u (eta0/128) hDegree.1 hepsilonEta).1
  have hN2 : (N : ℝ≥0)^2 ≤ 1*(t : ℝ≥0)^(2*R) := by
    have hN' : (N : ℝ≥0) ≤ (t : ℝ≥0)^R := by exact_mod_cast hN
    simpa only [one_mul, ← pow_mul, Nat.mul_comm R 2] using pow_le_pow_left' hN' 2
  have hleftUnion := finite_order_power_union_bound orders t ((N : ℝ≥0)^2) 1 (2*R) 2
    (fun _ ↦ 1/(t : ℝ≥0)^(2*R+3)) htNN hN2 (fun _ _ ↦ le_rfl) (by simpa only [one_mul] using hordersT)
  have hfailure : sourcePreliminaryDegreeFailure N n ⌊mu/256⌋₊ degreeMoment rate constant delta+
      (N : ℝ≥0)^2*∑ _j ∈ orders, (1/(t : ℝ≥0)^(2*R+3)) ≤ 2/(t : ℝ≥0)^2 := by
    calc
      _ ≤ 1/(t : ℝ≥0)^3+1/(t : ℝ≥0)^2 := add_le_add hDegree.2.2 hleftUnion
      _ ≤ 1/(t : ℝ≥0)^2+1/(t : ℝ≥0)^2 := add_le_add
        (one_div_le_one_div_of_le (pow_pos ht0 _) (pow_le_pow_right₀ htNN (by norm_num : 2 ≤ 3))) le_rfl
      _ = _ := by ring
  have hhalf : 2/(t : ℝ≥0)^2 ≤ 1/2 := by
    apply (div_le_div_iff₀ (pow_pos ht0 2) (by norm_num : (0 : ℝ≥0) < 2)).mpr
    have ht2NN : (2 : ℝ≥0) ≤ t := by exact_mod_cast ht2
    simpa only [pow_two, one_mul] using pow_le_pow_left' ht2NN 2
  refine ⟨hnumeric.1, hnumeric.2.1, hnumeric.2.2.1, hnumeric.2.2.2.1, hnumeric.2.2.2.2.1,
    hnumeric.2.2.2.2.2.1, hnumeric.2.2.2.2.2.2.1, hnumeric.2.2.2.2.2.2.2,
    hDegree.1, hDegree.2.1, hcap, hLeft, hDegree.2.2, hfailure, hhalf, ?_⟩
  calc
    _ ≤ 2*sourcePreliminaryDegreeFailure N n ⌊mu/256⌋₊ degreeMoment rate constant delta :=
      conditioning_constant_le_double _ _ hhalf
    _ ≤ 2*(1/(t : ℝ≥0)^3) := mul_le_mul_of_nonneg_left hDegree.2.2 zero_le
    _ = _ := by ring

end Erdos207
