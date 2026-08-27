/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.EventualSourceCompressedStep
import ErdosProblems.Erdos207.ResidualMasterInduction

/-! # Close the finite master induction with actual uniform transitions -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem exists_source_finite_master_schedule
    (q h b ell R rootExp step : ℕ) (E : SourceOrdinaryParameters q h b)
    (v D : Fin ell → ℕ) (C0 B0 eta0 : ℝ≥0)
    (hb : 2 ≤ b) (hh : 4 ≤ h) (hv : ∀ i, 1 ≤ v i) (hD : ∀ i, E.K*v i ≤ D i)
    (hstep : 4*b+2 ≤ step) (hroot : b*(h+1)+2 ≤ rootExp)
    (hC0 : 1 ≤ C0) (hB0 : 1 ≤ B0) (heta0 : 0 < eta0) (heta01 : eta0 ≤ 1) :
    ∃ exponent : Fin (ell+1) → ℕ, ∃ T : ℕ, 18+ell ≤ T ∧
      ∀ t : ℕ, T ≤ t →
      ∀ {V : Type*} [Fintype V] [DecidableEq V] (W : Vortex V ell)
        (bank ambient : TripleSystemOn V) (Gamma : SimpleGraph V) (analytic : Fin ell → ℕ),
      Fintype.card V ≤ t^R →
      (∀ i, T ≤ analytic i ∧ analytic i ≤ t ∧ t^(E.P*v i) ≤ (analytic i)^(D i+1) ∧
        t^(D i) ≤ (W.U i.castSucc).card ∧ t^(D i-v i) ≤ (W.U i.succ).card ∧
        (W.U i.castSucc).card ≤ t^(v i)*(W.U i.succ).card ∧
        t^step*(W.U i.succ).card ≤ 2*(W.U i.castSucc).card ∧
        (analytic i)^ksssPowerDenominatorExponent q (2*(D i+1)) E.B ((26*q+12)*(D i+1)) (D i+1) ≤
          (W.U i.castSucc).card) →
      (∀ i, ∀ j ∈ Icc 4 q, sourcePrefixZ q bank i.val j ≤ (t : ℝ≥0)^(v i)) →
      (∀ a, t^rootExp ≤ (W.U a).card) →
      (∀ a : Fin ell, 0 < a.val → ∀ j ∈ Icc 4 q, sourcePrefixZ q bank a.val j ≤ t) →
      ∀ p eta : ℝ≥0, 1/(t : ℝ≥0)^b ≤ p → p ≤ 2/(t : ℝ≥0)^b → eta0 ≤ eta → eta ≤ 1 →
      (∀ a, (W.U a).Nonempty) → HasAbsorberSourcePrefixBounds q bank W →
      (∃ law : FiniteLaw (MasterStateOn V),
        IsResidualCompressedMasterLaw law W 0 (absorberErdosForbiddenConfigurationsOn q bank)
          Gamma ambient p eta (17/(t : ℝ≥0)) C0 (B0/(t : ℝ≥0)^(exponent 0)) h) →
      ∃ law : FiniteLaw (MasterStateOn V),
        IsResidualCompressedMasterLaw law W (Fin.last ell) (absorberErdosForbiddenConfigurationsOn q bank)
          Gamma ambient p eta ((17+ell : ℕ)/(t : ℝ≥0))
          (sourceMasterConstants (152*sourceOrdinaryProductConstant q/eta0)
            (2*sourceOrdinaryProductConstant q) C0 ell)
          (B0/(t : ℝ≥0)^(exponent (Fin.last ell))) h := by
  let factor := 152*sourceOrdinaryProductConstant q/eta0
  let J := 2*sourceOrdinaryProductConstant q
  let constants := sourceMasterConstants factor J C0
  have hconstants : ∀ j, 1 ≤ constants j := sourceMasterConstants_one_le factor J C0 hC0
  have hchoices := fun i : Fin ell ↦ eventually_source_compressed_step q h b ell R rootExp step (v i) (D i) i E
    (constants i.val) B0 eta0 hb hh (hv i) (hD i) hstep hroot (hconstants i.val) heta0 heta01
  choose minimum hminimum hsteps using hchoices
  obtain ⟨exponent, cutoff, _, hbudget⟩ := exists_finite_backward_error_schedule ell 1 minimum
    (fun i m ↦ sourceStageRequiredError q (D i+1) ((D i+1)*R) m)
  choose Tp Ta hTp hTa hstage using fun i ↦ hsteps i (cutoff i) (hbudget i).1
  let T := max (18+ell) (max (univ.sup Tp) (univ.sup Ta))
  have hphysical : ∀ i, Tp i ≤ T := fun i ↦ (le_sup (f := Tp) (mem_univ i)).trans
    ((le_max_left _ _).trans (le_max_right _ _))
  have hanalytic : ∀ i, Ta i ≤ T := fun i ↦ (le_sup (f := Ta) (mem_univ i)).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨exponent, T, le_max_left _ _, ?_⟩
  intro t ht V _ _ W bank ambient Gamma analytic hN hgeometry hz hrootSize hfutureZ p eta hp hpUpper heta heta1
    hnonempty hsource hbase
  let xi := fun a : Fin (ell+1) ↦ ((17+a.val : ℕ) : ℝ≥0)/(t : ℝ≥0)
  let errors := fun a : Fin (ell+1) ↦ B0/(t : ℝ≥0)^(exponent a)
  have ht2 : 2 ≤ t := by
    have htmin : 18+ell ≤ t := (le_max_left _ _).trans ht
    omega
  have htNN : (2 : ℝ≥0) ≤ t := by exact_mod_cast ht2
  have ht1 : (1 : ℝ≥0) ≤ t := (by norm_num : (1 : ℝ≥0) ≤ 2).trans htNN
  have ht0 : (0 : ℝ≥0) < t := zero_lt_one.trans_le ht1
  have hbase' : ∃ law : FiniteLaw (MasterStateOn V),
      IsResidualCompressedMasterLaw law W 0 (absorberErdosForbiddenConfigurationsOn q bank)
        Gamma ambient p eta (xi 0) (constants 0) (errors 0) h := by
    simpa only [xi, Fin.val_zero, Nat.add_zero, Nat.cast_ofNat, constants, sourceMasterConstants] using hbase
  have htransition : ∀ i : Fin ell, ∀ law : FiniteLaw (MasterStateOn V),
      IsResidualCompressedMasterLaw law W i.castSucc (absorberErdosForbiddenConfigurationsOn q bank)
        Gamma ambient p eta (xi i.castSucc) (constants i.val) (errors i.castSucc) h →
      ∃ law' : FiniteLaw (MasterStateOn V),
        IsResidualCompressedMasterLaw law' W i.succ (absorberErdosForbiddenConfigurationsOn q bank)
          Gamma ambient p eta (xi i.succ) (constants (i.val+1)) (errors i.succ) h := by
    intro i law hlaw
    obtain ⟨ha, hat, hpower, hn, hu, hratio, hstepRatio, hscale⟩ := hgeometry i
    have hxi : xi i.castSucc ≤ (17+ell : ℕ)/(t : ℝ≥0) := by
      apply div_le_div_of_nonneg_right _ zero_le
      exact_mod_cast (show 17+i.val ≤ 17+ell by omega)
    have hxiStep : xi i.castSucc+1/(t : ℝ≥0) ≤ xi i.succ := by
      apply le_of_eq
      dsimp only [xi, Fin.val_castSucc, Fin.val_succ]
      push_cast
      ring
    have hxiSize : 6/(t : ℝ≥0) ≤ xi i.succ := by
      apply div_le_div_of_nonneg_right _ zero_le
      exact_mod_cast (show 6 ≤ 17+(i.val+1) by omega)
    have hfuture : ∀ a ∈ futureLevelPairs i.succ, ∀ j ∈ Icc 4 q, sourcePrefixZ q bank a.1.val j ≤ t := by
      intro a ha
      have hh := ((mem_futureLevelPairs_iff i.succ a).mp ha).1
      exact hfutureZ a.1 (by change i.val+1 ≤ a.1.val at hh; omega)
    obtain ⟨law', hlaw'⟩ := hstage i t (analytic i) ((hphysical i).trans ht) ((hanalytic i).trans ha) hat hpower
      W bank ambient Gamma hN hn hu hratio hstepRatio hscale (hz i) (fun a _ ↦ hrootSize a.2) hfuture
      p eta (xi i.castSucc) (xi i.succ) (errors i.castSucc) (exponent i.castSucc) hp hpUpper heta heta1
      hxi hxiStep hxiSize (hbudget i).2.2.1 (hbudget i).2.2.2 le_rfl hnonempty hsource law hlaw
    have htac : (t : ℝ≥0) ≤ (analytic i : ℝ≥0)^(D i+1) := by
      have hpos : 1 ≤ E.P*v i := by simpa only [one_mul] using Nat.mul_le_mul E.P_pos (hv i)
      have hpowerNN : (t : ℝ≥0)^(E.P*v i) ≤ (analytic i : ℝ≥0)^(D i+1) := by exact_mod_cast hpower
      apply le_trans _ hpowerNN
      simpa only [pow_one] using pow_le_pow_right₀ ht1 hpos
    have hdelta : 1/(analytic i : ℝ≥0)^((D i+1)*cutoff i) ≤ 1/(t : ℝ≥0)^cutoff i :=
      cross_scale_fresh_error t (analytic i) (D i+1) (cutoff i) ht0 htac
    have herror : errors i.castSucc+1/(analytic i : ℝ≥0)^((D i+1)*cutoff i) ≤ errors i.succ :=
      polynomial_error_budget_step t B0 _ (exponent i.castSucc) (exponent i.succ) (cutoff i)
        htNN hB0 ((hbudget i).2.1.trans (hbudget i).2.2.1) (hbudget i).2.1 hdelta
    exact ⟨law', hlaw'.mono_constants le_rfl herror⟩
  obtain ⟨law, hlaw⟩ := exists_terminalResidualCompressedMasterLaw W (absorberErdosForbiddenConfigurationsOn q bank)
    Gamma ambient (fun _ ↦ p) (fun _ ↦ eta) xi (fun a ↦ constants a.val) errors h hbase' htransition
  exact ⟨law, hlaw⟩

end

end Erdos207
