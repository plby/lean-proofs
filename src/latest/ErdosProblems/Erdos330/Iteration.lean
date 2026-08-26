/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- This file has been modified for Lean/Mathlib 4.33.0. -/
/-
Erdős Problem 330, positive upper density formulation.
Informal authors: GPT-5.5 Pro, David Turturean.
Formal authors: Codex, GPT-5.5 Pro, Allen Graham Hart.
Source: https://www.erdosproblems.com/forum/thread/330#post-6271
https://github.com/AllenGrahamHart/FormalConjectures-Bench/tree/6160036caab0dcee80395ba3beb7b6ef2731604e/formalizations/erdos330
Original Lean/Mathlib version: 4.27.0.
-/
import ErdosProblems.Erdos330.StageArithmetic

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Iterating budgeted service steps for Erdős Problem 330

This file packages the one-step budgeted service theorem into a reusable
iteration layer.  It constructs an infinite chain that repeatedly services one
fixed active element while preserving the canonical residue set and strict
reciprocal budget invariants.
-/

namespace Erdos330

open scoped Pointwise

/-- A stage state together with the invariants needed to keep servicing `a`. -/
structure BudgetedActiveState (a : ℕ) where
  st : StageState
  active : a ∈ st.P
  canonicalD : st.HasCanonicalD
  budget : st.HasStrictReciprocalBudget

namespace BudgetedActiveState

/-- Choose a budget-preserving service step whose protected endpoint is at least `B`. -/
noncomputable def service {a : ℕ} (node : BudgetedActiveState a) (B : ℕ) :
    CanonicalServiceExtension node.st a :=
  Classical.choose
    (exists_canonicalServiceExtension_of_active_preserving_strictBudget_ge_and_stageBlock
    node.active node.canonicalD node.budget B)

theorem service_full_spec {a : ℕ} (node : BudgetedActiveState a) (B : ℕ) :
    ∃ endpoint : ℕ, ∃ block : Finset ℕ,
      B ≤ (node.service B).service.protectedEndpoint ∧
        B ≤ (node.service B).next.R ∧
          B ≤ endpoint ∧
            (∀ n ∈ block, n ∈ (node.service B).next.S ∧ n < endpoint) ∧
              1 * endpoint ≤ (8 * node.st.m a) * block.card ∧
                (node.service B).service.protectedBlock.densityNumerator = 1 ∧
                  (node.service B).service.protectedBlock.densityDenominator =
                    8 * node.st.m a ∧
                    (node.service B).next.HasStrictReciprocalBudget := by
  exact Classical.choose_spec
    (exists_canonicalServiceExtension_of_active_preserving_strictBudget_ge_and_stageBlock
      node.active node.canonicalD node.budget B)

noncomputable def stageBlockEndpoint {a : ℕ} (node : BudgetedActiveState a)
    (B : ℕ) : ℕ :=
  Classical.choose (node.service_full_spec B)

noncomputable def stageBlock {a : ℕ} (node : BudgetedActiveState a) (B : ℕ) :
    Finset ℕ :=
  Classical.choose (Classical.choose_spec (node.service_full_spec B))

theorem stageBlock_spec {a : ℕ} (node : BudgetedActiveState a) (B : ℕ) :
    B ≤ (node.service B).service.protectedEndpoint ∧
      B ≤ (node.service B).next.R ∧
        B ≤ node.stageBlockEndpoint B ∧
          (∀ n ∈ node.stageBlock B,
            n ∈ (node.service B).next.S ∧ n < node.stageBlockEndpoint B) ∧
            1 * node.stageBlockEndpoint B ≤ (8 * node.st.m a) * (node.stageBlock B).card ∧
              (node.service B).service.protectedBlock.densityNumerator = 1 ∧
                (node.service B).service.protectedBlock.densityDenominator =
                  8 * node.st.m a ∧
                  (node.service B).next.HasStrictReciprocalBudget := by
  exact Classical.choose_spec (Classical.choose_spec (node.service_full_spec B))

theorem service_spec {a : ℕ} (node : BudgetedActiveState a) (B : ℕ) :
    B ≤ (node.service B).service.protectedEndpoint ∧
      B ≤ (node.service B).next.R ∧
        (node.service B).service.protectedBlock.densityNumerator = 1 ∧
          (node.service B).service.protectedBlock.densityDenominator = 8 * node.st.m a ∧
            (node.service B).next.HasStrictReciprocalBudget := by
  obtain ⟨hendpoint, hR, _hBendpoint, _hblock, _hdensity, hnum, hden, hbudget⟩ :=
    node.stageBlock_spec B
  exact ⟨hendpoint, hR, hnum, hden, hbudget⟩

theorem service_endpoint_ge {a : ℕ} (node : BudgetedActiveState a) (B : ℕ) :
    B ≤ (node.service B).service.protectedEndpoint :=
  (node.service_spec B).1

theorem service_R_ge {a : ℕ} (node : BudgetedActiveState a) (B : ℕ) :
    B ≤ (node.service B).next.R :=
  (node.service_spec B).2.1

theorem service_densityNumerator {a : ℕ} (node : BudgetedActiveState a) (B : ℕ) :
    (node.service B).service.protectedBlock.densityNumerator = 1 :=
  (node.service_spec B).2.2.1

theorem service_densityDenominator {a : ℕ} (node : BudgetedActiveState a) (B : ℕ) :
    (node.service B).service.protectedBlock.densityDenominator = 8 * node.st.m a :=
  (node.service_spec B).2.2.2.1

theorem service_next_budget {a : ℕ} (node : BudgetedActiveState a) (B : ℕ) :
    (node.service B).next.HasStrictReciprocalBudget :=
  (node.service_spec B).2.2.2.2

/-- The next invariant-carrying node after servicing `a` beyond bound `B`. -/
noncomputable def step {a : ℕ} (node : BudgetedActiveState a) (B : ℕ) :
    BudgetedActiveState a :=
  {
    st := (node.service B).next
    active := (node.service B).service.toStageExtension.P_subset node.active
    canonicalD := (node.service B).canonicalD
    budget := node.service_next_budget B
  }

/-- Repeatedly service the same active element, with the `k`th endpoint at least `k`. -/
noncomputable def iterate {a : ℕ} (node : BudgetedActiveState a) :
    ℕ → BudgetedActiveState a
  | 0 => node
  | k + 1 => (iterate node k).step k

/-- The stage sequence underlying the repeated-service iteration. -/
noncomputable def stage {a : ℕ} (node : BudgetedActiveState a) (k : ℕ) : StageState :=
  (node.iterate k).st

theorem stage_succ {a : ℕ} (node : BudgetedActiveState a) (k : ℕ) :
    node.stage (k + 1) = ((node.iterate k).service k).next := by
  rfl

theorem stage_active {a : ℕ} (node : BudgetedActiveState a) (k : ℕ) :
    a ∈ (node.stage k).P :=
  (node.iterate k).active

theorem stage_canonicalD {a : ℕ} (node : BudgetedActiveState a) (k : ℕ) :
    (node.stage k).HasCanonicalD :=
  (node.iterate k).canonicalD

theorem stage_strictBudget {a : ℕ} (node : BudgetedActiveState a) (k : ℕ) :
    (node.stage k).HasStrictReciprocalBudget :=
  (node.iterate k).budget

theorem active_mem_finalSet {a : ℕ} (node : BudgetedActiveState a) :
    a ∈ finalSet node.stage :=
  ⟨0, node.st.active_mem_state node.active⟩

theorem stage_m_eq_initial {a : ℕ} (node : BudgetedActiveState a) (k : ℕ) :
    (node.stage k).m a = node.st.m a := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [stage_succ node k]
      exact (((node.iterate k).service k).service.toStageExtension.m_eq_on_old a
        (node.iterate k).active).trans ih

theorem stageChain {a : ℕ} (node : BudgetedActiveState a) : StageChain node.stage := by
  refine ⟨?_⟩
  intro k
  rw [stage_succ node k]
  exact ((node.iterate k).service k).service.toStageExtension

theorem R_unbounded {a : ℕ} (node : BudgetedActiveState a) :
    ∀ N : ℕ, ∃ k : ℕ, N ≤ (node.stage k).R := by
  intro N
  refine ⟨N + 1, ?_⟩
  rw [stage_succ node N]
  exact (node.iterate N).service_R_ge N

/-- The selected canonical service recast as a service between consecutive stages. -/
noncomputable def serviceExtension {a : ℕ} (node : BudgetedActiveState a) (k : ℕ) :
    ServiceExtension (node.stage k) (node.stage (k + 1)) a := by
  rw [stage_succ node k]
  exact ((node.iterate k).service k).service

theorem frequent_services {a : ℕ} (node : BudgetedActiveState a) :
    ∀ N : ℕ, ∃ k : ℕ, ∃ svc : ServiceExtension (node.stage k) (node.stage (k + 1)) a,
      N ≤ svc.protectedEndpoint ∧
        svc.protectedBlock.densityNumerator = 1 ∧
          svc.protectedBlock.densityDenominator = 8 * node.st.m a := by
  intro N
  refine ⟨N, node.serviceExtension N, ?_, ?_, ?_⟩
  · simpa [serviceExtension] using (node.iterate N).service_endpoint_ge N
  · simpa [serviceExtension] using (node.iterate N).service_densityNumerator N
  · have hden := (node.iterate N).service_densityDenominator N
    have hm' : (node.iterate N).st.m a = node.st.m a := by
      simpa [stage] using node.stage_m_eq_initial N
    simpa [serviceExtension, hm'] using hden

theorem frequent_stage_blocks {a : ℕ} (node : BudgetedActiveState a) :
    ∀ N : ℕ, ∃ k endpoint : ℕ, ∃ B : Finset ℕ,
      N ≤ endpoint ∧ (∀ n ∈ B, n ∈ (node.stage k).S ∧ n < endpoint) ∧
        1 * endpoint ≤ (8 * node.st.m a) * B.card := by
  intro N
  let iter := node.iterate N
  refine ⟨N + 1, iter.stageBlockEndpoint N, iter.stageBlock N, ?_, ?_, ?_⟩
  · exact (iter.stageBlock_spec N).2.2.1
  · intro n hn
    have hmem := (iter.stageBlock_spec N).2.2.2.1 n hn
    constructor
    · rw [stage_succ node N]
      exact hmem.1
    · exact hmem.2
  · have hdensity := (iter.stageBlock_spec N).2.2.2.2.1
    have hm' : iter.st.m a = node.st.m a := by
      simpa [iter, stage] using node.stage_m_eq_initial N
    simpa [iter, hm'] using hdensity

theorem finalSet_isAsymptoticBasisTwo {a : ℕ} (node : BudgetedActiveState a) :
    IsAsymptoticBasisTwo (finalSet node.stage) :=
  Erdos330.finalSet_isAsymptoticBasisTwo node.stageChain node.R_unbounded

theorem finalSet_upperDensity_pos {a : ℕ} (node : BudgetedActiveState a) :
    HasPositiveUpperDensity (finalSet node.stage) := by
  refine finalSet_upperDensity_pos_of_frequent_stage_blocks (st := node.stage)
    (numerator := 1) (denominator := 8 * node.st.m a) ?_ ?_ ?_
  · norm_num
  · have hpos : 0 < node.st.m a := node.st.modulus_pos node.active
    omega
  · exact node.frequent_stage_blocks

theorem fixed_private_upperDensity_pos {a : ℕ} (node : BudgetedActiveState a) :
    HasPositiveUpperDensity (privateSet (finalSet node.stage) a) := by
  refine private_upperDensity_pos_of_frequent_services (st := node.stage) node.stageChain
    (a := a) (numerator := 1) (denominator := 8 * node.st.m a) ?_ ?_ ?_
  · norm_num
  · have hpos : 0 < node.st.m a := node.st.modulus_pos node.active
    omega
  · exact node.frequent_services

theorem fixedActive_finalSet_certificates {a : ℕ} (node : BudgetedActiveState a) :
    IsAsymptoticBasisTwo (finalSet node.stage) ∧
      HasPositiveUpperDensity (finalSet node.stage) ∧
        HasPositiveUpperDensity (privateSet (finalSet node.stage) a) :=
  ⟨node.finalSet_isAsymptoticBasisTwo, node.finalSet_upperDensity_pos,
    node.fixed_private_upperDensity_pos⟩

/-- The explicit initial state as an invariant-carrying node. -/
noncomputable def initialNode (a m H X : ℕ)
    (hmPrime : Nat.Prime m) (hm23 : 23 ≤ m) (hmMod4 : m % 4 = 3)
    (haX : a ≤ X) (hlong : H + 4 * m ≤ X) : BudgetedActiveState a :=
  {
    st := initialStageState a m H X hmPrime hm23 hmMod4 haX hlong
    active := by
      simp [initialStageState_active a m H X hmPrime hm23 hmMod4 haX hlong]
    canonicalD := initialStageState_hasCanonicalD a m H X hmPrime hm23 hmMod4 haX hlong
    budget := initialStageState_hasStrictReciprocalBudget a m H X hmPrime hm23 hmMod4
      haX hlong
  }

theorem exists_initialNode : ∃ a : ℕ, Nonempty (BudgetedActiveState a) := by
  obtain ⟨m, hm23, hmPrime, hmMod4⟩ := exists_prime_three_mod_four_ge 23
  let H := m + 2
  let X := H + 4 * m
  exact ⟨1, ⟨initialNode 1 m H X hmPrime hm23 hmMod4 (by omega) (by omega)⟩⟩

theorem exists_repeatedService_chain_certificates :
    ∃ a : ℕ, ∃ st : ℕ → StageState,
      StageChain st ∧
        a ∈ finalSet st ∧
          IsAsymptoticBasisTwo (finalSet st) ∧
            HasPositiveUpperDensity (finalSet st) ∧
              HasPositiveUpperDensity (privateSet (finalSet st) a) := by
  obtain ⟨a, ⟨node⟩⟩ := exists_initialNode
  exact ⟨a, node.stage, node.stageChain, node.active_mem_finalSet,
    node.finalSet_isAsymptoticBasisTwo, node.finalSet_upperDensity_pos,
    node.fixed_private_upperDensity_pos⟩

end BudgetedActiveState

end Erdos330
