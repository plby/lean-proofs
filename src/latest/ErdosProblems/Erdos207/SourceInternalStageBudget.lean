/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.EventualSourceInternalBudget
import ErdosProblems.Erdos207.SourcePhysicalExtensionBudgets

/-! # Uniformly constructed numeric inputs for the actual correlated internal stage -/

namespace Erdos207

open Finset
open scoped Classical NNReal

structure SourceInternalStageBudget
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (i : Fin ell) (q : ℕ) (bank : TripleSystemOn V)
    (p eta r C beta survival point constant delta Cout : ℝ≥0) where
  factor : ℝ≥0
  alpha : ℝ≥0
  rate : ℝ≥0
  epsilon : ℝ≥0
  error : ℝ≥0
  degreeError : ℝ≥0
  degreeMoment : ℕ
  leftMoment : ℕ
  leftError : ℝ≥0
  factor_one : 1 ≤ factor
  mu_large : 512 ≤ r^2*p^2*eta*(W.U i.succ).card
  alpha_le_one : alpha ≤ 1
  rate_le_reserve : rate ≤ r
  epsilon_pos : 0 < epsilon
  point_charge : alpha*p^3 ≤ factor*(p/(W.U i.castSucc).card)
  combined_point : constant*point+(constant*survival)*(64/(r^2*p^2*eta*(W.U i.succ).card)) ≤ alpha
  combined_rate : constant*survival ≤ rate
  left_cap : epsilon*p^2*r^2*(W.U i.succ).card ≤ ⌈r^2*p^2*eta*(W.U i.succ).card/128⌉₊
  degree_moment : 2*degreeMoment ≤ ⌊r^2*p^2*eta*(W.U i.succ).card/256⌋₊+1
  source_scale : ∀ j ∈ Icc 4 q,
    sourcePrefixZ q bank i.val j ≤ sourcePrefixY q i.val*r^2*p^3*(W.U i.succ).card
  left_scalar : ∀ j ∈ Icc 4 q,
    sourceLeftFailureBound i.val j leftMoment (Fintype.card V) p r
      (2*max (C^3*factor) (2*constant)) (beta+delta) (sourcePrefixY q i.val)
      (epsilon/((Icc 4 q).card+1 : ℝ≥0)) (W.U i.succ).card ≤ leftError
  error_bound : sourcePreliminaryDegreeFailure (Fintype.card V) (W.U i.castSucc).card
    ⌊r^2*p^2*eta*(W.U i.succ).card/256⌋₊ degreeMoment rate constant delta +
    (Fintype.card V : ℝ≥0)^2*∑ _j ∈ Icc 4 q, leftError ≤ error
  error_lt_one : error < 1
  conditioned_constant : (2*max (C^3*factor) (2*constant))/(1-error) ≤ Cout
  out_pos : 1 ≤ Cout
  conditioned_degree : sourcePreliminaryDegreeFailure (Fintype.card V) (W.U i.castSucc).card
    ⌊r^2*p^2*eta*(W.U i.succ).card/256⌋₊ degreeMoment rate constant delta/(1-error) ≤ degreeError

theorem eventually_exists_source_internal_stage_budget
    (q ell R b reserveExp v d D L : ℕ) (eta0 constant C B0 : ℝ≥0)
    (hb : 2 ≤ b) (heta0 : 0 < eta0) (heta01 : eta0 ≤ 1) (hconstant : 1 ≤ constant)
    (hinnerGap : 2*reserveExp+3*b+v+2 ≤ L)
    (hrateGap : 2*reserveExp+2*b+v+2 ≤ d) (hpointGap : 2*b+1 ≤ D) :
    ∃ M T : ℕ, 1 ≤ M ∧ 1 ≤ T ∧ ∀ t : ℕ, T ≤ t →
      ∀ {V : Type*} [Fintype V] [DecidableEq V] (W : Vortex V ell) (i : Fin ell)
        (bank : TripleSystemOn V) (c : ℕ) (analytic p eta beta delta : ℝ≥0),
      Fintype.card V ≤ t^R → t^D ≤ (W.U i.castSucc).card → (t : ℝ≥0)^L ≤ (W.U i.succ).card →
      ((W.U i.castSucc).card : ℝ≥0) ≤ (t : ℝ≥0)^v*(W.U i.succ).card →
      (t : ℝ≥0)^d ≤ analytic^c →
      1/(t : ℝ≥0)^b ≤ p → p ≤ 2/(t : ℝ≥0)^b → eta0 ≤ eta →
      beta ≤ B0/(t : ℝ≥0)^M → delta ≤ 1/(t : ℝ≥0)^M →
      (∀ j ∈ Icc 4 q, sourcePrefixZ q bank i.val j ≤ (t : ℝ≥0)^v) →
      ∃ budget : SourceInternalStageBudget W i q bank p eta (1/(t : ℝ≥0)^reserveExp) C beta
        (2/analytic^c) (24/(p^2*eta*(W.U i.castSucc).card)) constant delta
        (4*max (C^3*(152*constant/eta0)) (2*constant)), budget.degreeError = 2/(t : ℝ≥0)^3 := by
  obtain ⟨degreeMoment, M, T, _, hM, hT, hnumeric⟩ := eventually_source_internal_numeric_budget
    q ell R b reserveExp v d D L eta0 constant C B0 hb heta0 heta01 hconstant hinnerGap hrateGap hpointGap
  refine ⟨M, T, hM, hT, ?_⟩
  intro t ht V _ _ W i bank c analytic p eta beta delta hN hn hu hratio hpower hp hpUpper heta hbeta hdelta hz
  have ht1 : 1 ≤ t := hT.trans ht
  have htNN : (1 : ℝ≥0) ≤ t := by exact_mod_cast ht1
  have hb := hnumeric t ht (Fintype.card V) (W.U i.castSucc).card c (W.U i.succ).card analytic p eta beta delta
    hN ((card_le_univ _).trans hN) hn hu hratio hpower hp hpUpper heta hbeta hdelta
  rcases hb with ⟨hfactor, hJ, halpha, _, hrate, hRate, hpoint, hcharge, hmu, hdegree, hcap,
    hleft, _, hfailure, hhalf, hconditionedDegree⟩
  let factor := 152*constant/eta0
  let r : ℝ≥0 := 1/(t : ℝ≥0)^reserveExp
  have hout : 1 ≤ 4*max (C^3*factor) (2*constant) := by
    have hmax : 1 ≤ max (C^3*factor) (2*constant) := hJ.trans (le_max_right _ _)
    simpa only [one_mul] using mul_le_mul (show (1 : ℝ≥0) ≤ 4 by norm_num) hmax zero_le zero_le
  refine ⟨{
    factor := factor
    alpha := factor/(p^2*(W.U i.castSucc).card)
    rate := 2*constant/(t : ℝ≥0)^d
    epsilon := eta0/128
    error := 2/(t : ℝ≥0)^2
    degreeError := 2/(t : ℝ≥0)^3
    degreeMoment := degreeMoment
    leftMoment := 2*R+4
    leftError := 1/(t : ℝ≥0)^(2*R+3)
    factor_one := hfactor
    mu_large := hmu
    alpha_le_one := halpha
    rate_le_reserve := hrate
    epsilon_pos := by positivity
    point_charge := hcharge
    combined_point := hpoint
    combined_rate := hRate
    left_cap := hcap
    degree_moment := hdegree
    source_scale := ?_
    left_scalar := fun j hj ↦ hleft i.val (by omega) j (mem_Icc.mp hj).2
    error_bound := hfailure
    error_lt_one := hhalf.trans_lt (by norm_num)
    conditioned_constant := ?_
    out_pos := hout
    conditioned_degree := hconditionedDegree }, rfl⟩
  · intro j hj
    exact source_left_extension_power t (W.U i.succ).card p r (sourcePrefixZ q bank i.val j)
      (sourcePrefixY q i.val) b reserveExp v L htNN (one_le_sourcePrefixY q i.val) hp le_rfl
      (hz j hj) hu (by omega)
  · have hc := conditioning_constant_le_double (2*max (C^3*factor) (2*constant)) _ hhalf
    simpa only [show (2 : ℝ≥0)*(2*max (C^3*factor) (2*constant)) = 4*max (C^3*factor) (2*constant) by ring] using hc

end Erdos207
