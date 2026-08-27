/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.SourceCoverStageBudget
import ErdosProblems.Erdos207.SourcePreparedAuxiliaryAssembly
import ErdosProblems.Erdos207.SourceFrozenPreliminaryAssembly
import ErdosProblems.Erdos207.SourcePreparedCoverAssembly

/-! # Construct a cover-down transition from every compressed input law -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem eventually_source_compressed_cover
    (q h b Bexp k Rmin c R m : ℕ) (eta0 : ℝ≥0) (heta0 : 0 < eta0) :
    ∃ T : ℕ, 1 ≤ T ∧ ∀ analytic : ℕ, T ≤ analytic →
      ∀ {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
        (W : Vortex V ell) (i : Fin ell) (bank ambient : TripleSystemOn V) (Gamma : SimpleGraph V)
        (p eta xi xi' r C beta B0 error : ℝ≥0),
      SourceCoverStageBudget q h b Bexp k analytic Rmin c R m W i bank p eta xi xi' r C beta eta0 B0 error →
      (∀ a, (W.U a).Nonempty) → HasAbsorberSourcePrefixBounds q bank W →
      ∀ law : FiniteLaw (MasterStateOn V),
      IsResidualCompressedMasterLaw law W i.castSucc (absorberErdosForbiddenConfigurationsOn q bank)
        Gamma ambient p eta xi C beta h →
      ∃ law' : FiniteLaw (MasterStateOn V),
        IsResidualCompressedMasterLaw law' W i.succ (absorberErdosForbiddenConfigurationsOn q bank)
          Gamma ambient p eta xi'
          (sourceMasterConstantStep (152*sourceOrdinaryProductConstant q/eta0)
            (2*sourceOrdinaryProductConstant q) C) (beta+1/(analytic : ℝ≥0)^(c*m)) h := by
  obtain ⟨T, hT1, hregularize⟩ := eventually_regularize_source_prepared_law q b Bexp k Rmin R (c*m+3*c) eta0 heta0
  refine ⟨T, hT1, ?_⟩
  intro analytic ha V _ _ ell W i bank ambient Gamma p eta xi xi' r C beta B0 error budget hnonempty hsource law hlaw
  let F := fun j ↦ absorberInducedConfigurationsOn q j bank
  let y := fun _j : ℕ ↦ sourcePrefixY q i.val
  let z := sourcePrefixZ q bank i.val
  let theta : ℝ := 1/(24*(analytic : ℝ)^ksssPowerErrorExponent b Bexp)
  let mu := r^2*p^2*eta*(W.U i.succ).card
  have hxiHalf : xi ≤ 1/2 := budget.xi_small.trans (by apply NNReal.coe_le_coe.mp; norm_num)
  have herror : error < 1 := budget.error_half.trans_lt (by norm_num)
  have hC2 : 1 ≤ 2*C := by
    simpa only [one_mul] using mul_le_mul (show (1 : ℝ≥0) ≤ 2 by norm_num) budget.C_pos zero_le zero_le
  have hC4 : 1 ≤ 4*C := by
    simpa only [one_mul] using mul_le_mul (show (1 : ℝ≥0) ≤ 4 by norm_num) budget.C_pos zero_le zero_le
  have hC24 : (2*C)/(1-error) ≤ 4*C := by
    simpa only [show (2 : ℝ≥0)*(2*C) = 4*C by ring] using conditioning_constant_le_double (2*C) error budget.error_half
  have hC48 : (4*C)/(1-error) ≤ 8*C := by
    simpa only [show (2 : ℝ≥0)*(4*C) = 8*C by ring] using conditioning_constant_le_double (4*C) error budget.error_half
  have hC816 : (8*C)/(1-error) ≤ 16*C := by
    simpa only [show (2 : ℝ≥0)*(8*C) = 16*C by ring] using conditioning_constant_le_double (8*C) error budget.error_half
  obtain ⟨hpw, hpwLaw, hpwSupport⟩ := hlaw.conditionPointwise_double hxiHalf
  have hxiRef : (xi : ℝ) ≤ (1/1048576 : ℝ)/4 := by exact_mod_cast budget.xi_reference
  have hendpoint : 1 ≤ ((1/1048576 : ℝ)/4)*((p : ℝ)^2*eta*(W.U i.succ).card) := by
    exact_mod_cast budget.reference_endpoint
  have hsupply : (⌊mu/8⌋₊ : ℝ) ≤ (r : ℝ)^2*(p : ℝ)^2*eta*(W.U i.succ).card/8 := by
    have hh := Nat.floor_le (show 0 ≤ mu/8 from zero_le)
    exact_mod_cast hh
  obtain ⟨hreservePos, _, B, hprepared⟩ := hpwLaw.exists_source_prepared_reserve_data i hpwSupport hC2
    budget.sparse.p_pos budget.sparse.p_le_one budget.sparse.eta_pos budget.sparse.eta_le_one budget.h_large
    budget.r_le_one budget.r_small (1/1048576) theta (by norm_num) (by norm_num) hxiRef budget.xi_small
    hendpoint ⌊mu/8⌋₊ hsupply budget.current_density budget.inner_margin budget.theta_pos budget.theta_half
    budget.sampling eta0 heta0 budget.eta_floor (by have hn := budget.sparse.current_pos; omega)
    error budget.reserve_error herror
  have hprepared4 := hprepared.mono_constants hC24 le_rfl
  have hspread : ∀ j ∈ Icc 4 q, SourceVortexWellSpread (W.prefix i.castSucc) j (F j) (y j) (z j) :=
    fun j hj ↦ hsource.at_stage i.castSucc j (mem_Icc.mp hj).1 (mem_Icc.mp hj).2
  have hy : ∀ j ∈ Icc 4 q, y j ≤ (analytic : ℝ≥0) :=
    fun _ _ ↦ (sourcePrefixY_le_auxiliaryCoefficient q i.val).trans budget.auxiliary_coefficient
  have hcoeff : ∀ j ∈ Icc 4 q,
      (∑ j' ∈ Icc j q, sourceNibbleMomentCoefficient i.val j' 2*y j') ≤ sourceAuxiliaryCoefficient q i.val :=
    fun j hj ↦ source_auxiliary_order_sum_le q i.val j (mem_Icc.mp hj).1
  obtain ⟨hdegreePos, hdegreeLower, hdegreeData, hdegree, inst, Lstar, envelope, hresult, _⟩ :=
    hregularize analytic ha _ W i _ Gamma ambient _ _ _ _ _ _ p eta xi r (4*C) beta
      (1/1048576) theta ⌊mu/8⌋₊ h hprepared4 F y z (3*R+3*c) (3*c)
      (sourceStageRequiredError q c R m) B0 error budget.sparse.ambient le_rfl
      (sourceStageRequiredError_bounds q c R m).2.1 budget.sparse.p_le_one hC4
      (fun _ _ ↦ one_le_sourcePrefixY q i.val) budget.auxiliary_density budget.sparse.incoming_error hnonempty
      hspread budget.auxiliary_extension budget.auxiliary_error herror budget.sparse.scale
      budget.analytic_density_lower budget.analytic_density_upper hy
      (fun j hj ↦ (hcoeff j hj).trans budget.auxiliary_coefficient)
  have := inst
  have hdegreeData8 := hdegreeData.mono_constants hC48 le_rfl
  let : ∀ omega, Nonempty {T // T ∈ (B ∘ Subtype.val) omega} := fun omega ↦ by
    obtain ⟨T, hT⟩ := hdegreeData8.nonempty omega
    exact ⟨⟨T, hT⟩⟩
  have hsourceSubset : (Icc 4 q).biUnion F ⊆ absorberErdosForbiddenConfigurationsOn q bank :=
    fun _ hS ↦ (mem_absorberSourceFamily_iff.mp hS).1
  have hinner : ((W.U i.succ).card : ℝ≥0) ≤ p*(W.U i.castSucc).card/8 :=
    reserve_inner_margin_for_graph_mass _ _ p eta budget.sparse.p_le_one budget.sparse.eta_le_one budget.inner_margin
  obtain ⟨K, Good, hsparsePos, hsparseLower, hsparseData, hkernel⟩ :=
    hdegreeData8.exists_frozen_preliminary q b Bexp k analytic Rmin c R m
      (sourceAuxiliaryCoefficient q i.val) B0 error F envelope y z Lstar hresult hdegree hcoeff
      hsourceSubset hnonempty hxiHalf hinner budget.sparse
  have hsparseData16 := hsparseData.mono_constants hC816 le_rfl
  have hconstant : 1 ≤ sourceOrdinaryProductConstant q :=
    (by norm_num : (1 : ℝ≥0) ≤ 2).trans (le_max_left _ _)
  have hreference : (1/1048576 : ℝ) = (budget.link.referenceTolerance : ℝ) := by
    rw [budget.link_reference]
    norm_num
  have hC16 : 1 ≤ 16*C := by
    simpa only [one_mul] using mul_le_mul (show (1 : ℝ≥0) ≤ 16 by norm_num) budget.C_pos zero_le zero_le
  exact hsparseData16.exists_completed_cover (fun x ↦ K x.val)
    (fun _ S ↦ mapTripleSystem (Function.Embedding.subtype (fun v ↦ v ∈ W.U i.castSucc)) S.chosen)
    (2/(analytic : ℝ≥0)^c) (24/(p^2*eta*(W.U i.castSucc).card)) (sourceOrdinaryProductConstant q)
    (1/(analytic : ℝ≥0)^(c*m)) budget.internal budget.link budget.link_degree budget.degree_error hreference
    budget.sparse.p_pos budget.sparse.p_le_one budget.r_pos budget.r_le_one budget.sparse.eta_pos
    budget.sparse.eta_le_one hC16 hconstant (by have hh := budget.h_large; omega) hnonempty hsource
    (fun x ↦ (hkernel x).1) (fun x ↦ (hkernel x).2)

end

end Erdos207
