/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ResidualMasterCompression

/-! # A finite ambient-order-independent schedule of corrected master constants -/

namespace Erdos207

open scoped NNReal

theorem conditioning_constant_le_double (C error : ℝ≥0) (herror : error ≤ 1/2) :
    C/(1-error) ≤ 2*C := by
  have hhalf : (1/2 : ℝ≥0) ≤ 1-error := by
    apply le_tsub_of_add_le_right
    calc
      _ ≤ (1/2 : ℝ≥0)+1/2 := add_le_add le_rfl herror
      _ = _ := by norm_num
  calc
    _ ≤ C/(1/2) := div_le_div_of_nonneg_left zero_le (by norm_num) hhalf
    _ = _ := by ring

theorem IsResidualMasterIterationGood.mono_constants
    {Omega V : Type*} [Fintype Omega] [Fintype V] [DecidableEq V] {ell h : ℕ}
    {L : FiniteLaw Omega} {W : Vortex V ell} {k : Fin (ell+1)} {Gamma : SimpleGraph V}
    {F : ForbiddenFamilyOn V} {G : Omega → SimpleGraph V} {A I D : Omega → TripleSystemOn V}
    {p eta xi C C' beta beta' : ℝ≥0}
    (hgood : IsResidualMasterIterationGood L W k Gamma F G A I D p eta xi C beta h)
    (hC : C ≤ C') (hbeta : beta ≤ beta') :
    IsResidualMasterIterationGood L W k Gamma F G A I D p eta xi C' beta' h :=
  ⟨hgood.1, hgood.2.1.mono hC hbeta, hgood.2.2⟩

theorem IsResidualCompressedMasterLaw.mono_constants
    {V : Type*} [Fintype V] [DecidableEq V] {ell h : ℕ}
    {L : FiniteLaw (MasterStateOn V)} {W : Vortex V ell} {k : Fin (ell+1)}
    {Gamma : SimpleGraph V} {F : ForbiddenFamilyOn V} {ambient : TripleSystemOn V}
    {p eta xi C C' beta beta' : ℝ≥0}
    (hgood : IsResidualCompressedMasterLaw L W k F Gamma ambient p eta xi C beta h)
    (hC : C ≤ C') (hbeta : beta ≤ beta') :
    IsResidualCompressedMasterLaw L W k F Gamma ambient p eta xi C' beta' h :=
  ⟨hgood.1.mono_constants hC hbeta, hgood.2⟩

def sourceMasterConstantStep (factor J C : ℝ≥0) : ℝ≥0 :=
  4*max ((4*max ((16*C)^3*factor) J)^5) 1

def sourceMasterConstants (factor J C0 : ℝ≥0) : ℕ → ℝ≥0
  | 0 => C0
  | i+1 => sourceMasterConstantStep factor J (sourceMasterConstants factor J C0 i)

theorem sourceMasterConstantStep_one_le (factor J C : ℝ≥0) : 1 ≤ sourceMasterConstantStep factor J C := by
  apply (le_max_right _ _).trans
  simpa only [sourceMasterConstantStep, one_mul] using mul_le_mul_of_nonneg_right (show (1 : ℝ≥0) ≤ 4 by norm_num)
    (show 0 ≤ max ((4*max ((16*C)^3*factor) J)^5) 1 from zero_le)

theorem source_master_conditioned_constant_step
    (factor J C prior internalError coverError : ℝ≥0)
    (hprior : prior ≤ 16*C) (hI : internalError ≤ 1/2) (hCover : coverError ≤ 1/2) :
    (2*max (((2*max (prior^3*factor) J)/(1-internalError))^5) 1)/(1-coverError) ≤
      sourceMasterConstantStep factor J C := by
  have hinternal : (2*max (prior^3*factor) J)/(1-internalError) ≤ 4*max ((16*C)^3*factor) J := by
    calc
      _ ≤ 2*(2*max (prior^3*factor) J) := conditioning_constant_le_double _ _ hI
      _ = 4*max (prior^3*factor) J := by ring
      _ ≤ _ := by gcongr
  calc
    _ ≤ 2*(2*max (((2*max (prior^3*factor) J)/(1-internalError))^5) 1) :=
      conditioning_constant_le_double _ _ hCover
    _ = 4*max (((2*max (prior^3*factor) J)/(1-internalError))^5) 1 := by ring
    _ ≤ _ := by unfold sourceMasterConstantStep; gcongr

theorem sourceMasterConstants_one_le (factor J C0 : ℝ≥0) (hC0 : 1 ≤ C0) (i : ℕ) :
    1 ≤ sourceMasterConstants factor J C0 i := by
  cases i with
  | zero => exact hC0
  | succ i => exact sourceMasterConstantStep_one_le factor J (sourceMasterConstants factor J C0 i)

theorem IsResidualCompressedMasterLaw.conditionPointwise_double
    {V : Type*} [Fintype V] [DecidableEq V] {ell h : ℕ}
    {L : FiniteLaw (MasterStateOn V)} {W : Vortex V ell} {k : Fin (ell+1)}
    {Gamma : SimpleGraph V} {F : ForbiddenFamilyOn V} {ambient : TripleSystemOn V}
    {p eta xi C beta : ℝ≥0}
    (hgood : IsResidualCompressedMasterLaw L W k F Gamma ambient p eta xi C beta h)
    (hxi : xi ≤ 1/2) :
    let Good := masterPointwiseGoodEvent W k F MasterStateOn.graph MasterStateOn.available
      MasterStateOn.initial MasterStateOn.later p eta xi h
    ∃ hpos : 0 < L.probability Good,
      IsResidualCompressedMasterLaw (L.conditionOn Good hpos) W k F Gamma ambient p eta xi (2*C) beta h ∧
      (L.conditionOn Good hpos).SupportedOn Good := by
  dsimp only
  have hxi1 : xi < 1 := hxi.trans_lt (by norm_num)
  obtain ⟨hpos, hconditioned, hsupport⟩ := hgood.conditionPointwise hxi1
  have hC : C/L.probability (masterPointwiseGoodEvent W k F MasterStateOn.graph MasterStateOn.available
      MasterStateOn.initial MasterStateOn.later p eta xi h) ≤ 2*C := by
    exact (div_le_div_of_nonneg_left zero_le (tsub_pos_iff_lt.mpr hxi1) hgood.1.2.2).trans
      (conditioning_constant_le_double C xi hxi)
  exact ⟨hpos, hconditioned.mono_constants hC le_rfl, hsupport⟩

end Erdos207
