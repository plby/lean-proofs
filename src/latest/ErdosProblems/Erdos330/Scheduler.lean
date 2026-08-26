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
import Mathlib.Data.Nat.Pairing

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
# Scheduler-oriented service steps for Erdős Problem 330

The repeated-service chain in `Iteration` fixes one active element.  This file
starts the fair-scheduler layer needed for the final construction: it packages
a state with the persistent invariants, chooses the least currently dormant
element, and proves a service step can activate that chosen dormant element
while preserving the canonical-residue and strict reciprocal-budget invariants.
-/

namespace Erdos330

open scoped Pointwise

/-- A fixed fair request stream: every natural number is requested arbitrarily far out. -/
def fairRequest (k : ℕ) : ℕ :=
  (Nat.unpair k).2

theorem fairRequest_frequently (a N : ℕ) :
    ∃ k : ℕ, N ≤ k ∧ fairRequest k = a := by
  refine ⟨Nat.pair N a, Nat.left_le_pair N a, ?_⟩
  simp [fairRequest]

/-- Invariant-carrying state, without fixing a single active element. -/
structure BudgetedState where
  st : StageState
  canonicalD : st.HasCanonicalD
  budget : st.HasStrictReciprocalBudget

namespace BudgetedState

/-- Elements of the current finite set that are not yet active. -/
def dormantSet (node : BudgetedState) : Finset ℕ :=
  node.st.S.filter fun n => n ∉ node.st.P

theorem dormantSet_nonempty (node : BudgetedState) : node.dormantSet.Nonempty := by
  obtain ⟨b, hbS, hbP⟩ := node.st.exists_dormant
  exact ⟨b, by simp [dormantSet, hbS, hbP]⟩

/-- The least currently dormant element. -/
noncomputable def leastDormant (node : BudgetedState) : ℕ :=
  node.dormantSet.min' node.dormantSet_nonempty

theorem leastDormant_mem_dormantSet (node : BudgetedState) :
    node.leastDormant ∈ node.dormantSet :=
  Finset.min'_mem node.dormantSet node.dormantSet_nonempty

theorem leastDormant_mem_S (node : BudgetedState) :
    node.leastDormant ∈ node.st.S := by
  have hmem := node.leastDormant_mem_dormantSet
  simpa [dormantSet] using (Finset.mem_filter.mp hmem).1

theorem leastDormant_not_mem_P (node : BudgetedState) :
    node.leastDormant ∉ node.st.P := by
  have hmem := node.leastDormant_mem_dormantSet
  simpa [dormantSet] using (Finset.mem_filter.mp hmem).2

theorem leastDormant_le_of_mem_S_not_mem_P (node : BudgetedState) {n : ℕ}
    (hnS : n ∈ node.st.S) (hnP : n ∉ node.st.P) :
    node.leastDormant ≤ n := by
  have hnDormant : n ∈ node.dormantSet := by
    simp [dormantSet, hnS, hnP]
  exact Finset.min'_le node.dormantSet n hnDormant

theorem mem_P_of_mem_S_lt_leastDormant (node : BudgetedState) {n : ℕ}
    (hnS : n ∈ node.st.S) (hnlt : n < node.leastDormant) :
    n ∈ node.st.P := by
  by_contra hnP
  have hle := node.leastDormant_le_of_mem_S_not_mem_P hnS hnP
  omega

/--
A scheduler step servicing active `a`, using a budget-preserving extension that
activates the least currently dormant element and also records a dense finite
block in the next stage.
-/
structure ScheduledService (node : BudgetedState) (a B : ℕ) where
  svc : CanonicalServiceExtension node.st a
  endpoint : ℕ
  block : Finset ℕ
  protectedEndpoint_ge : B ≤ svc.service.protectedEndpoint
  R_ge : B ≤ svc.next.R
  endpoint_ge : B ≤ endpoint
  block_subset_next : ∀ n ∈ block, n ∈ svc.next.S ∧ n < endpoint
  block_density : 1 * endpoint ≤ (8 * node.st.m a) * block.card
  private_densityNumerator : svc.service.protectedBlock.densityNumerator = 1
  private_densityDenominator : svc.service.protectedBlock.densityDenominator = 8 * node.st.m a
  next_budget : svc.next.HasStrictReciprocalBudget
  next_P_eq : svc.next.P = activatedActiveSet node.st node.leastDormant

theorem exists_scheduledService {node : BudgetedState} {a B : ℕ}
    (ha : a ∈ node.st.P) : Nonempty (ScheduledService node a B) := by
  let b := node.leastDormant
  have hbS : b ∈ node.st.S := node.leastDormant_mem_S
  have hbDormant : b ∉ node.st.P := node.leastDormant_not_mem_P
  obtain ⟨p, hp, hactivatedBudget⟩ :=
    exists_freshPrimeData_preserving_strictBudget hbDormant node.budget
  have hbudget_erase :
      ((activatedActiveSet node.st b).erase a).sum
          (fun c => (1 : ℝ) / (activatedModulus node.st b p c : ℝ)) ≤ (1 / 2 : ℝ) :=
    (activated_erase_budget_le_total (st := node.st) (a := a) (b := b) (p := p)).trans
      hactivatedBudget.le
  obtain ⟨svc, endpoint, block, hprot, hR, hBendpoint, hblock, hdensity, hnum, hden,
      hP, hm⟩ :=
    exists_canonicalServiceExtension_of_active_dormant_fresh_with_budget_ge_and_stageBlock
      ha hbS hbDormant hp node.canonicalD hbudget_erase B
  have hnextBudget : svc.next.HasStrictReciprocalBudget := by
    dsimp [StageState.HasStrictReciprocalBudget]
    rw [hP, hm]
    exact hactivatedBudget
  exact ⟨{
    svc := svc
    endpoint := endpoint
    block := block
    protectedEndpoint_ge := hprot
    R_ge := hR
    endpoint_ge := hBendpoint
    block_subset_next := hblock
    block_density := hdensity
    private_densityNumerator := hnum
    private_densityDenominator := hden
    next_budget := hnextBudget
    next_P_eq := hP
  }⟩

noncomputable def scheduledService (node : BudgetedState) {a B : ℕ}
    (ha : a ∈ node.st.P) : ScheduledService node a B :=
  Classical.choice (exists_scheduledService (node := node) (a := a) (B := B) ha)

/-- The next invariant-carrying state after a scheduled service step. -/
noncomputable def next (node : BudgetedState) {a B : ℕ} (ha : a ∈ node.st.P) :
    BudgetedState :=
  let step := node.scheduledService (a := a) (B := B) ha
  {
    st := step.svc.next
    canonicalD := step.svc.canonicalD
    budget := step.next_budget
  }

theorem next_P_eq_insert_leastDormant (node : BudgetedState) {a B : ℕ}
    (ha : a ∈ node.st.P) :
    (node.next (a := a) (B := B) ha).st.P = insert node.leastDormant node.st.P := by
  change (node.scheduledService (a := a) (B := B) ha).svc.next.P =
    insert node.leastDormant node.st.P
  simpa [activatedActiveSet] using
    (node.scheduledService (a := a) (B := B) ha).next_P_eq

theorem leastDormant_mem_next_P (node : BudgetedState) {a B : ℕ}
    (ha : a ∈ node.st.P) :
    node.leastDormant ∈ (node.next (a := a) (B := B) ha).st.P := by
  rw [node.next_P_eq_insert_leastDormant ha]
  simp

theorem old_active_mem_next_P (node : BudgetedState) {a B c : ℕ}
    (ha : a ∈ node.st.P) (hc : c ∈ node.st.P) :
    c ∈ (node.next (a := a) (B := B) ha).st.P := by
  change c ∈ (node.scheduledService (a := a) (B := B) ha).svc.next.P
  exact (node.scheduledService (a := a) (B := B) ha).svc.service.toStageExtension.P_subset hc

theorem old_S_lt_leastDormant_mem_next_P (node : BudgetedState) {a B n : ℕ}
    (ha : a ∈ node.st.P) (hnS : n ∈ node.st.S) (hnlt : n < node.leastDormant) :
    n ∈ (node.next (a := a) (B := B) ha).st.P := by
  exact node.old_active_mem_next_P ha (node.mem_P_of_mem_S_lt_leastDormant hnS hnlt)

theorem old_S_le_leastDormant_mem_next_P (node : BudgetedState) {a B n : ℕ}
    (ha : a ∈ node.st.P) (hnS : n ∈ node.st.S) (hnle : n ≤ node.leastDormant) :
    n ∈ (node.next (a := a) (B := B) ha).st.P := by
  by_cases hnlt : n < node.leastDormant
  · exact node.old_S_lt_leastDormant_mem_next_P ha hnS hnlt
  · have hn_eq : n = node.leastDormant := by omega
    subst n
    exact node.leastDormant_mem_next_P ha

/-- The explicit initial stage as a scheduler node. -/
noncomputable def initialBudgetedState (a m H X : ℕ)
    (hmPrime : Nat.Prime m) (hm23 : 23 ≤ m) (hmMod4 : m % 4 = 3)
    (haX : a ≤ X) (hlong : H + 4 * m ≤ X) : BudgetedState :=
  {
    st := initialStageState a m H X hmPrime hm23 hmMod4 haX hlong
    canonicalD := initialStageState_hasCanonicalD a m H X hmPrime hm23 hmMod4 haX hlong
    budget := initialStageState_hasStrictReciprocalBudget a m H X hmPrime hm23 hmMod4
      haX hlong
  }

theorem initial_active (a m H X : ℕ)
    (hmPrime : Nat.Prime m) (hm23 : 23 ≤ m) (hmMod4 : m % 4 = 3)
    (haX : a ≤ X) (hlong : H + 4 * m ≤ X) :
    a ∈ (initialBudgetedState a m H X hmPrime hm23 hmMod4 haX hlong).st.P := by
  simp [initialBudgetedState,
    initialStageState_active a m H X hmPrime hm23 hmMod4 haX hlong]

theorem exists_initialBudgetedState :
    ∃ a : ℕ, ∃ node : BudgetedState, a ∈ node.st.P := by
  obtain ⟨m, hm23, hmPrime, hmMod4⟩ := exists_prime_three_mod_four_ge 23
  let H := m + 2
  let X := H + 4 * m
  exact ⟨1, initialBudgetedState 1 m H X hmPrime hm23 hmMod4 (by omega) (by omega),
    initial_active 1 m H X hmPrime hm23 hmMod4 (by omega) (by omega)⟩

end BudgetedState

/--
Scheduler state with one distinguished active element that is serviced at each
step, while the least dormant element is activated.
-/
structure ScheduledActiveState (a : ℕ) where
  node : BudgetedState
  active : a ∈ node.st.P

namespace ScheduledActiveState

noncomputable def step {a : ℕ} (snode : ScheduledActiveState a) (B : ℕ) :
    ScheduledActiveState a :=
  {
    node := snode.node.next (a := a) (B := B) snode.active
    active := snode.node.old_active_mem_next_P (a := a) (B := B) snode.active snode.active
  }

/--
The fair scheduler services the current request when it is already active; if
not, it services the persistent seed active element.  Activation is still by
the least dormant element, so this target choice only affects which old active
element receives a private block at the step.
-/
def fairTarget {seed : ℕ} (snode : ScheduledActiveState seed) (k : ℕ) : ℕ :=
  if fairRequest k ∈ snode.node.st.P then fairRequest k else seed

theorem fairTarget_active {seed : ℕ} (snode : ScheduledActiveState seed) (k : ℕ) :
    snode.fairTarget k ∈ snode.node.st.P := by
  by_cases hreq : fairRequest k ∈ snode.node.st.P
  · simp [fairTarget, hreq]
  · simp [fairTarget, hreq, snode.active]

theorem fairTarget_eq_of_request_active {seed : ℕ} (snode : ScheduledActiveState seed)
    {k : ℕ} (hreq : fairRequest k ∈ snode.node.st.P) :
    snode.fairTarget k = fairRequest k := by
  simp [fairTarget, hreq]

theorem fairTarget_eq_seed_of_request_seed {seed : ℕ} (snode : ScheduledActiveState seed)
    {k : ℕ} (hreq : fairRequest k = seed) :
    snode.fairTarget k = seed := by
  simp [fairTarget, hreq, snode.active]

noncomputable def fairStep {seed : ℕ} (snode : ScheduledActiveState seed) (k : ℕ) :
    ScheduledActiveState seed :=
  {
    node := snode.node.next (a := snode.fairTarget k) (B := k)
      (snode.fairTarget_active k)
    active := snode.node.old_active_mem_next_P (a := snode.fairTarget k) (B := k)
      (snode.fairTarget_active k) snode.active
  }

/-- Iterate least-dormant activation while repeatedly servicing `a`. -/
noncomputable def iterate {a : ℕ} (snode : ScheduledActiveState a) :
    ℕ → ScheduledActiveState a
  | 0 => snode
  | k + 1 => (iterate snode k).step k

/-- Iterate least-dormant activation while servicing a fair active request stream. -/
noncomputable def fairIterate {seed : ℕ} (snode : ScheduledActiveState seed) :
    ℕ → ScheduledActiveState seed
  | 0 => snode
  | k + 1 => (fairIterate snode k).fairStep k

noncomputable def stage {a : ℕ} (snode : ScheduledActiveState a) (k : ℕ) :
    StageState :=
  (snode.iterate k).node.st

noncomputable def fairStage {seed : ℕ} (snode : ScheduledActiveState seed) (k : ℕ) :
    StageState :=
  (snode.fairIterate k).node.st

theorem stage_succ {a : ℕ} (snode : ScheduledActiveState a) (k : ℕ) :
    snode.stage (k + 1) =
      ((snode.iterate k).node.scheduledService (a := a) (B := k)
        (snode.iterate k).active).svc.next := by
  rfl

theorem fairStage_succ {seed : ℕ} (snode : ScheduledActiveState seed) (k : ℕ) :
    snode.fairStage (k + 1) =
      ((snode.fairIterate k).node.scheduledService
        (a := (snode.fairIterate k).fairTarget k) (B := k)
        ((snode.fairIterate k).fairTarget_active k)).svc.next := by
  rfl

theorem stageChain {a : ℕ} (snode : ScheduledActiveState a) :
    StageChain snode.stage := by
  refine ⟨?_⟩
  intro k
  rw [stage_succ snode k]
  exact ((snode.iterate k).node.scheduledService (a := a) (B := k)
    (snode.iterate k).active).svc.service.toStageExtension

theorem fairStageChain {seed : ℕ} (snode : ScheduledActiveState seed) :
    StageChain snode.fairStage := by
  refine ⟨?_⟩
  intro k
  rw [fairStage_succ snode k]
  exact ((snode.fairIterate k).node.scheduledService
    (a := (snode.fairIterate k).fairTarget k) (B := k)
    ((snode.fairIterate k).fairTarget_active k)).svc.service.toStageExtension

theorem leastDormant_activated_at_step {a : ℕ}
    (snode : ScheduledActiveState a) (k : ℕ) :
    (snode.iterate k).node.leastDormant ∈ (snode.stage (k + 1)).P := by
  change (snode.iterate k).node.leastDormant ∈ (((snode.iterate k).step k).node.st.P)
  exact (snode.iterate k).node.leastDormant_mem_next_P (a := a) (B := k)
    (snode.iterate k).active

theorem active_mem_stage {a : ℕ} (snode : ScheduledActiveState a) (k : ℕ) :
    a ∈ (snode.stage k).P :=
  (snode.iterate k).active

theorem leastDormant_activated_at_fairStep {seed : ℕ}
    (snode : ScheduledActiveState seed) (k : ℕ) :
    (snode.fairIterate k).node.leastDormant ∈ (snode.fairStage (k + 1)).P := by
  change (snode.fairIterate k).node.leastDormant ∈
    (((snode.fairIterate k).fairStep k).node.st.P)
  exact (snode.fairIterate k).node.leastDormant_mem_next_P
    (a := (snode.fairIterate k).fairTarget k) (B := k)
    ((snode.fairIterate k).fairTarget_active k)

theorem seed_mem_fairStage {seed : ℕ} (snode : ScheduledActiveState seed) (k : ℕ) :
    seed ∈ (snode.fairStage k).P :=
  (snode.fairIterate k).active

theorem stage_m_eq_initial {a : ℕ} (snode : ScheduledActiveState a) (k : ℕ) :
    (snode.stage k).m a = snode.node.st.m a := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [stage_succ snode k]
      exact (((snode.iterate k).node.scheduledService (a := a) (B := k)
        (snode.iterate k).active).svc.service.toStageExtension.m_eq_on_old a
        (snode.iterate k).active).trans ih

theorem fairStage_seed_m_eq_initial {seed : ℕ}
    (snode : ScheduledActiveState seed) (k : ℕ) :
    (snode.fairStage k).m seed = snode.node.st.m seed := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [fairStage_succ snode k]
      exact (((snode.fairIterate k).node.scheduledService
        (a := (snode.fairIterate k).fairTarget k) (B := k)
        ((snode.fairIterate k).fairTarget_active k)).svc.service.toStageExtension.m_eq_on_old
        seed (snode.fairIterate k).active).trans ih

theorem R_unbounded {a : ℕ} (snode : ScheduledActiveState a) :
    ∀ N : ℕ, ∃ k : ℕ, N ≤ (snode.stage k).R := by
  intro N
  refine ⟨N + 1, ?_⟩
  rw [stage_succ snode N]
  exact ((snode.iterate N).node.scheduledService (a := a) (B := N)
    (snode.iterate N).active).R_ge

theorem fair_R_unbounded {seed : ℕ} (snode : ScheduledActiveState seed) :
    ∀ N : ℕ, ∃ k : ℕ, N ≤ (snode.fairStage k).R := by
  intro N
  refine ⟨N + 1, ?_⟩
  rw [fairStage_succ snode N]
  exact ((snode.fairIterate N).node.scheduledService
    (a := (snode.fairIterate N).fairTarget N) (B := N)
    ((snode.fairIterate N).fairTarget_active N)).R_ge

noncomputable def serviceExtension {a : ℕ} (snode : ScheduledActiveState a) (k : ℕ) :
    ServiceExtension (snode.stage k) (snode.stage (k + 1)) a := by
  rw [stage_succ snode k]
  exact ((snode.iterate k).node.scheduledService (a := a) (B := k)
    (snode.iterate k).active).svc.service

noncomputable def fairServiceExtension {seed : ℕ} (snode : ScheduledActiveState seed)
    (k : ℕ) :
    ServiceExtension (snode.fairStage k) (snode.fairStage (k + 1))
      ((snode.fairIterate k).fairTarget k) := by
  rw [fairStage_succ snode k]
  exact ((snode.fairIterate k).node.scheduledService
    (a := (snode.fairIterate k).fairTarget k) (B := k)
    ((snode.fairIterate k).fairTarget_active k)).svc.service

noncomputable def fairRequestedServiceExtension_of_request_active {seed : ℕ}
    (snode : ScheduledActiveState seed) {k : ℕ}
    (hactive : fairRequest k ∈ (snode.fairStage k).P) :
    ServiceExtension (snode.fairStage k) (snode.fairStage (k + 1)) (fairRequest k) :=
  have hactive_node : fairRequest k ∈ (snode.fairIterate k).node.st.P := by
    simpa [fairStage] using hactive
  have htarget : (snode.fairIterate k).fairTarget k = fairRequest k :=
    (snode.fairIterate k).fairTarget_eq_of_request_active hactive_node
  let raw := snode.fairServiceExtension k
  {
    toStageExtension := raw.toStageExtension
    served_active := hactive
    protectedEndpoint := raw.protectedEndpoint
    protectedEndpoint_le_X := raw.protectedEndpoint_le_X
    protectedBlock := {
      block := raw.protectedBlock.block
      block_subset_private := by
        intro n hn
        simpa [htarget] using raw.protectedBlock.block_subset_private n hn
      block_le_endpoint := raw.protectedBlock.block_le_endpoint
      block_lt_endpoint := raw.protectedBlock.block_lt_endpoint
      densityNumerator := raw.protectedBlock.densityNumerator
      densityDenominator := raw.protectedBlock.densityDenominator
      densityDenominator_pos := raw.protectedBlock.densityDenominator_pos
      block_density_lower := raw.protectedBlock.block_density_lower
    }
  }

theorem fairRequestedServiceExtension_protectedEndpoint_ge {seed : ℕ}
    (snode : ScheduledActiveState seed) {k : ℕ}
    (hactive : fairRequest k ∈ (snode.fairStage k).P) :
    k ≤ (snode.fairRequestedServiceExtension_of_request_active hactive).protectedEndpoint := by
  let step := (snode.fairIterate k).node.scheduledService
    (a := (snode.fairIterate k).fairTarget k) (B := k)
    ((snode.fairIterate k).fairTarget_active k)
  have hactive_node : fairRequest k ∈ (snode.fairIterate k).node.st.P := by
    simpa [fairStage] using hactive
  have htarget : (snode.fairIterate k).fairTarget k = fairRequest k :=
    (snode.fairIterate k).fairTarget_eq_of_request_active hactive_node
  simpa [fairRequestedServiceExtension_of_request_active, fairServiceExtension, htarget, step]
    using step.protectedEndpoint_ge

theorem fairRequestedServiceExtension_densityNumerator {seed : ℕ}
    (snode : ScheduledActiveState seed) {k : ℕ}
    (hactive : fairRequest k ∈ (snode.fairStage k).P) :
    (snode.fairRequestedServiceExtension_of_request_active hactive).protectedBlock.densityNumerator =
      1 := by
  let step := (snode.fairIterate k).node.scheduledService
    (a := (snode.fairIterate k).fairTarget k) (B := k)
    ((snode.fairIterate k).fairTarget_active k)
  have hactive_node : fairRequest k ∈ (snode.fairIterate k).node.st.P := by
    simpa [fairStage] using hactive
  have htarget : (snode.fairIterate k).fairTarget k = fairRequest k :=
    (snode.fairIterate k).fairTarget_eq_of_request_active hactive_node
  simpa [fairRequestedServiceExtension_of_request_active, fairServiceExtension, htarget, step]
    using step.private_densityNumerator

theorem fairRequestedServiceExtension_densityDenominator {seed : ℕ}
    (snode : ScheduledActiveState seed) {k : ℕ}
    (hactive : fairRequest k ∈ (snode.fairStage k).P) :
    (snode.fairRequestedServiceExtension_of_request_active hactive).protectedBlock.densityDenominator =
      8 * (snode.fairStage k).m (fairRequest k) := by
  let step := (snode.fairIterate k).node.scheduledService
    (a := (snode.fairIterate k).fairTarget k) (B := k)
    ((snode.fairIterate k).fairTarget_active k)
  have hactive_node : fairRequest k ∈ (snode.fairIterate k).node.st.P := by
    simpa [fairStage] using hactive
  have htarget : (snode.fairIterate k).fairTarget k = fairRequest k :=
    (snode.fairIterate k).fairTarget_eq_of_request_active hactive_node
  simpa [fairRequestedServiceExtension_of_request_active, fairServiceExtension, fairStage,
    htarget, step] using step.private_densityDenominator

noncomputable def fairServiceExtension_of_active_request_eq {seed : ℕ}
    (snode : ScheduledActiveState seed) {k a : ℕ}
    (hreq : fairRequest k = a) (hactive : a ∈ (snode.fairStage k).P) :
    ServiceExtension (snode.fairStage k) (snode.fairStage (k + 1)) a :=
  have hactive_req : fairRequest k ∈ (snode.fairIterate k).node.st.P := by
    simpa [fairStage, hreq] using hactive
  have htarget : (snode.fairIterate k).fairTarget k = a := by
    exact ((snode.fairIterate k).fairTarget_eq_of_request_active hactive_req).trans hreq
  let raw := snode.fairServiceExtension k
  {
    toStageExtension := raw.toStageExtension
    served_active := hactive
    protectedEndpoint := raw.protectedEndpoint
    protectedEndpoint_le_X := raw.protectedEndpoint_le_X
    protectedBlock := {
      block := raw.protectedBlock.block
      block_subset_private := by
        intro n hn
        simpa [htarget] using raw.protectedBlock.block_subset_private n hn
      block_le_endpoint := raw.protectedBlock.block_le_endpoint
      block_lt_endpoint := raw.protectedBlock.block_lt_endpoint
      densityNumerator := raw.protectedBlock.densityNumerator
      densityDenominator := raw.protectedBlock.densityDenominator
      densityDenominator_pos := raw.protectedBlock.densityDenominator_pos
      block_density_lower := raw.protectedBlock.block_density_lower
    }
  }

theorem fairServiceExtension_of_active_request_eq_protectedEndpoint_ge {seed : ℕ}
    (snode : ScheduledActiveState seed) {k a : ℕ}
    (hreq : fairRequest k = a) (hactive : a ∈ (snode.fairStage k).P) :
    k ≤ (snode.fairServiceExtension_of_active_request_eq hreq hactive).protectedEndpoint := by
  let step := (snode.fairIterate k).node.scheduledService
    (a := (snode.fairIterate k).fairTarget k) (B := k)
    ((snode.fairIterate k).fairTarget_active k)
  have hactive_req : fairRequest k ∈ (snode.fairIterate k).node.st.P := by
    simpa [fairStage, hreq] using hactive
  have htarget : (snode.fairIterate k).fairTarget k = a :=
    ((snode.fairIterate k).fairTarget_eq_of_request_active hactive_req).trans hreq
  simpa [fairServiceExtension_of_active_request_eq, fairServiceExtension, htarget, step]
    using step.protectedEndpoint_ge

theorem fairServiceExtension_of_active_request_eq_densityNumerator {seed : ℕ}
    (snode : ScheduledActiveState seed) {k a : ℕ}
    (hreq : fairRequest k = a) (hactive : a ∈ (snode.fairStage k).P) :
    (snode.fairServiceExtension_of_active_request_eq hreq hactive).protectedBlock.densityNumerator =
      1 := by
  let step := (snode.fairIterate k).node.scheduledService
    (a := (snode.fairIterate k).fairTarget k) (B := k)
    ((snode.fairIterate k).fairTarget_active k)
  have hactive_req : fairRequest k ∈ (snode.fairIterate k).node.st.P := by
    simpa [fairStage, hreq] using hactive
  have htarget : (snode.fairIterate k).fairTarget k = a :=
    ((snode.fairIterate k).fairTarget_eq_of_request_active hactive_req).trans hreq
  simpa [fairServiceExtension_of_active_request_eq, fairServiceExtension, htarget, step]
    using step.private_densityNumerator

theorem fairServiceExtension_of_active_request_eq_densityDenominator {seed : ℕ}
    (snode : ScheduledActiveState seed) {k a : ℕ}
    (hreq : fairRequest k = a) (hactive : a ∈ (snode.fairStage k).P) :
    (snode.fairServiceExtension_of_active_request_eq hreq hactive).protectedBlock.densityDenominator =
      8 * (snode.fairStage k).m a := by
  let step := (snode.fairIterate k).node.scheduledService
    (a := (snode.fairIterate k).fairTarget k) (B := k)
    ((snode.fairIterate k).fairTarget_active k)
  have hactive_req : fairRequest k ∈ (snode.fairIterate k).node.st.P := by
    simpa [fairStage, hreq] using hactive
  have htarget : (snode.fairIterate k).fairTarget k = a :=
    ((snode.fairIterate k).fairTarget_eq_of_request_active hactive_req).trans hreq
  simpa [fairServiceExtension_of_active_request_eq, fairServiceExtension, fairStage,
    htarget, step] using step.private_densityDenominator

noncomputable def fairSeedServiceExtension_of_request_seed {seed : ℕ}
    (snode : ScheduledActiveState seed) {k : ℕ} (hreq : fairRequest k = seed) :
    ServiceExtension (snode.fairStage k) (snode.fairStage (k + 1)) seed :=
  have htarget : (snode.fairIterate k).fairTarget k = seed :=
    (snode.fairIterate k).fairTarget_eq_seed_of_request_seed hreq
  let raw := snode.fairServiceExtension k
  {
    toStageExtension := raw.toStageExtension
    served_active := snode.seed_mem_fairStage k
    protectedEndpoint := raw.protectedEndpoint
    protectedEndpoint_le_X := raw.protectedEndpoint_le_X
    protectedBlock := {
      block := raw.protectedBlock.block
      block_subset_private := by
        intro n hn
        simpa [htarget] using raw.protectedBlock.block_subset_private n hn
      block_le_endpoint := raw.protectedBlock.block_le_endpoint
      block_lt_endpoint := raw.protectedBlock.block_lt_endpoint
      densityNumerator := raw.protectedBlock.densityNumerator
      densityDenominator := raw.protectedBlock.densityDenominator
      densityDenominator_pos := raw.protectedBlock.densityDenominator_pos
      block_density_lower := raw.protectedBlock.block_density_lower
    }
  }

theorem fairSeedServiceExtension_protectedEndpoint_ge {seed : ℕ}
    (snode : ScheduledActiveState seed) {k : ℕ} (hreq : fairRequest k = seed) :
    k ≤ (snode.fairSeedServiceExtension_of_request_seed hreq).protectedEndpoint := by
  let step := (snode.fairIterate k).node.scheduledService
    (a := (snode.fairIterate k).fairTarget k) (B := k)
    ((snode.fairIterate k).fairTarget_active k)
  have htarget : (snode.fairIterate k).fairTarget k = seed :=
    (snode.fairIterate k).fairTarget_eq_seed_of_request_seed hreq
  simpa [fairSeedServiceExtension_of_request_seed, fairServiceExtension, htarget, step]
    using step.protectedEndpoint_ge

theorem fairSeedServiceExtension_densityNumerator {seed : ℕ}
    (snode : ScheduledActiveState seed) {k : ℕ} (hreq : fairRequest k = seed) :
    (snode.fairSeedServiceExtension_of_request_seed hreq).protectedBlock.densityNumerator = 1 := by
  let step := (snode.fairIterate k).node.scheduledService
    (a := (snode.fairIterate k).fairTarget k) (B := k)
    ((snode.fairIterate k).fairTarget_active k)
  have htarget : (snode.fairIterate k).fairTarget k = seed :=
    (snode.fairIterate k).fairTarget_eq_seed_of_request_seed hreq
  simpa [fairSeedServiceExtension_of_request_seed, fairServiceExtension, htarget, step]
    using step.private_densityNumerator

theorem fairSeedServiceExtension_densityDenominator {seed : ℕ}
    (snode : ScheduledActiveState seed) {k : ℕ} (hreq : fairRequest k = seed) :
    (snode.fairSeedServiceExtension_of_request_seed hreq).protectedBlock.densityDenominator =
      8 * snode.node.st.m seed := by
  let step := (snode.fairIterate k).node.scheduledService
    (a := (snode.fairIterate k).fairTarget k) (B := k)
    ((snode.fairIterate k).fairTarget_active k)
  have htarget : (snode.fairIterate k).fairTarget k = seed :=
    (snode.fairIterate k).fairTarget_eq_seed_of_request_seed hreq
  have hm' : (snode.fairIterate k).node.st.m seed = snode.node.st.m seed := by
    simpa [fairStage] using snode.fairStage_seed_m_eq_initial k
  simpa [fairSeedServiceExtension_of_request_seed, fairServiceExtension, htarget, hm', step]
    using step.private_densityDenominator

theorem fair_frequent_seed_services {seed : ℕ} (snode : ScheduledActiveState seed) :
    ∀ N : ℕ, ∃ k : ℕ,
      ∃ svc : ServiceExtension (snode.fairStage k) (snode.fairStage (k + 1)) seed,
        N ≤ svc.protectedEndpoint ∧
          svc.protectedBlock.densityNumerator = 1 ∧
            svc.protectedBlock.densityDenominator = 8 * snode.node.st.m seed := by
  intro N
  obtain ⟨k, hNk, hreq⟩ := fairRequest_frequently seed N
  let svc := snode.fairSeedServiceExtension_of_request_seed hreq
  refine ⟨k, svc, ?_, ?_, ?_⟩
  · exact hNk.trans (snode.fairSeedServiceExtension_protectedEndpoint_ge hreq)
  · exact snode.fairSeedServiceExtension_densityNumerator hreq
  · exact snode.fairSeedServiceExtension_densityDenominator hreq

theorem frequent_services {a : ℕ} (snode : ScheduledActiveState a) :
    ∀ N : ℕ, ∃ k : ℕ, ∃ svc : ServiceExtension (snode.stage k) (snode.stage (k + 1)) a,
      N ≤ svc.protectedEndpoint ∧
        svc.protectedBlock.densityNumerator = 1 ∧
          svc.protectedBlock.densityDenominator = 8 * snode.node.st.m a := by
  intro N
  refine ⟨N, snode.serviceExtension N, ?_, ?_, ?_⟩
  · simpa [serviceExtension] using
      ((snode.iterate N).node.scheduledService (a := a) (B := N)
        (snode.iterate N).active).protectedEndpoint_ge
  · simpa [serviceExtension] using
      ((snode.iterate N).node.scheduledService (a := a) (B := N)
        (snode.iterate N).active).private_densityNumerator
  · have hden := ((snode.iterate N).node.scheduledService (a := a) (B := N)
        (snode.iterate N).active).private_densityDenominator
    have hm' : (snode.iterate N).node.st.m a = snode.node.st.m a := by
      simpa [stage] using snode.stage_m_eq_initial N
    simpa [serviceExtension, hm'] using hden

theorem frequent_stage_blocks {a : ℕ} (snode : ScheduledActiveState a) :
    ∀ N : ℕ, ∃ k endpoint : ℕ, ∃ B : Finset ℕ,
      N ≤ endpoint ∧ (∀ n ∈ B, n ∈ (snode.stage k).S ∧ n < endpoint) ∧
        1 * endpoint ≤ (8 * snode.node.st.m a) * B.card := by
  intro N
  let step := (snode.iterate N).node.scheduledService (a := a) (B := N)
    (snode.iterate N).active
  refine ⟨N + 1, step.endpoint, step.block, step.endpoint_ge, ?_, ?_⟩
  · intro n hn
    have hmem := step.block_subset_next n hn
    constructor
    · rw [stage_succ snode N]
      exact hmem.1
    · exact hmem.2
  · have hm' : (snode.iterate N).node.st.m a = snode.node.st.m a := by
      simpa [stage] using snode.stage_m_eq_initial N
    simpa [step, hm'] using step.block_density

theorem fair_frequent_seed_stage_blocks {seed : ℕ} (snode : ScheduledActiveState seed) :
    ∀ N : ℕ, ∃ k endpoint : ℕ, ∃ B : Finset ℕ,
      N ≤ endpoint ∧ (∀ n ∈ B, n ∈ (snode.fairStage k).S ∧ n < endpoint) ∧
        1 * endpoint ≤ (8 * snode.node.st.m seed) * B.card := by
  intro N
  obtain ⟨j, hNj, hreq⟩ := fairRequest_frequently seed N
  let step := (snode.fairIterate j).node.scheduledService
    (a := (snode.fairIterate j).fairTarget j) (B := j)
    ((snode.fairIterate j).fairTarget_active j)
  have htarget : (snode.fairIterate j).fairTarget j = seed :=
    (snode.fairIterate j).fairTarget_eq_seed_of_request_seed hreq
  refine ⟨j + 1, step.endpoint, step.block, ?_, ?_, ?_⟩
  · exact hNj.trans step.endpoint_ge
  · intro n hn
    have hmem := step.block_subset_next n hn
    constructor
    · rw [fairStage_succ snode j]
      exact hmem.1
    · exact hmem.2
  · have hm' : (snode.fairIterate j).node.st.m seed = snode.node.st.m seed := by
      simpa [fairStage] using snode.fairStage_seed_m_eq_initial j
    simpa [step, htarget, hm'] using step.block_density

theorem fair_exists_common_active_stage_on_finset {seed : ℕ}
    (snode : ScheduledActiveState seed) (T : Finset ℕ)
    (hT : ∀ t ∈ T, t ∈ finalSet snode.fairStage →
      ∃ k : ℕ, t ∈ (snode.fairStage k).P) :
    ∃ K : ℕ, ∀ t ∈ T, t ∈ finalSet snode.fairStage → t ∈ (snode.fairStage K).P := by
  classical
  revert hT
  induction T using Finset.induction_on with
  | empty =>
      intro _hT
      refine ⟨0, ?_⟩
      simp
  | insert x s hxs ih =>
      intro hT
      have hs : ∀ t ∈ s, t ∈ finalSet snode.fairStage →
          ∃ k : ℕ, t ∈ (snode.fairStage k).P := by
        intro t ht hfinal
        exact hT t (Finset.mem_insert_of_mem ht) hfinal
      obtain ⟨Ks, hKs⟩ := ih hs
      by_cases hxFinal : x ∈ finalSet snode.fairStage
      · obtain ⟨Kx, hKx⟩ := hT x (by simp) hxFinal
        refine ⟨max Kx Ks, ?_⟩
        intro t ht hfinal
        rcases Finset.mem_insert.mp ht with htx | hts
        · subst t
          exact snode.fairStageChain.P_subset_of_le (by omega) hKx
        · exact snode.fairStageChain.P_subset_of_le (by omega) (hKs t hts hfinal)
      · refine ⟨Ks, ?_⟩
        intro t ht hfinal
        rcases Finset.mem_insert.mp ht with htx | hts
        · subst t
          exact False.elim (hxFinal hfinal)
        · exact hKs t hts hfinal

theorem fair_eventually_active_of_finalSet {seed : ℕ}
    (snode : ScheduledActiveState seed) :
    ∀ n ∈ finalSet snode.fairStage, ∃ k : ℕ, n ∈ (snode.fairStage k).P := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hnFinal
      have hPrefixEventual : ∀ t ∈ Finset.range n, t ∈ finalSet snode.fairStage →
          ∃ k : ℕ, t ∈ (snode.fairStage k).P := by
        intro t ht hfinal
        exact ih t (Finset.mem_range.mp ht) hfinal
      obtain ⟨Kprefix, hKprefix⟩ :=
        snode.fair_exists_common_active_stage_on_finset (Finset.range n) hPrefixEventual
      rcases hnFinal with ⟨j, hjS⟩
      let K := max Kprefix j
      have hKprefix_le : Kprefix ≤ K := by
        dsimp [K]
        omega
      have hj_le : j ≤ K := by
        dsimp [K]
        omega
      have hnS_K : n ∈ (snode.fairStage K).S :=
        snode.fairStageChain.S_subset_of_le hj_le hjS
      have hPrefixActive_K :
          ∀ t, t < n → t ∈ finalSet snode.fairStage → t ∈ (snode.fairStage K).P := by
        intro t htn htfinal
        have htRange : t ∈ Finset.range n := Finset.mem_range.mpr htn
        exact snode.fairStageChain.P_subset_of_le hKprefix_le
          (hKprefix t htRange htfinal)
      by_cases hnP_K : n ∈ (snode.fairStage K).P
      · exact ⟨K, hnP_K⟩
      · let current := snode.fairIterate K
        have hnS_current : n ∈ current.node.st.S := by
          simpa [fairStage, current] using hnS_K
        have hnP_current : n ∉ current.node.st.P := by
          simpa [fairStage, current] using hnP_K
        have hleast_le : current.node.leastDormant ≤ n :=
          current.node.leastDormant_le_of_mem_S_not_mem_P hnS_current hnP_current
        have hnot_less : ¬ current.node.leastDormant < n := by
          intro hlt
          have hleastS_stage : current.node.leastDormant ∈ (snode.fairStage K).S := by
            simpa [fairStage, current] using current.node.leastDormant_mem_S
          have hleastFinal : current.node.leastDormant ∈ finalSet snode.fairStage :=
            ⟨K, hleastS_stage⟩
          have hleastP_stage : current.node.leastDormant ∈ (snode.fairStage K).P :=
            hPrefixActive_K current.node.leastDormant hlt hleastFinal
          have hleastNotP_stage : current.node.leastDormant ∉ (snode.fairStage K).P := by
            simpa [fairStage, current] using current.node.leastDormant_not_mem_P
          exact hleastNotP_stage hleastP_stage
        have hleast_eq : current.node.leastDormant = n := by omega
        refine ⟨K + 1, ?_⟩
        have hactivated := snode.leastDormant_activated_at_fairStep K
        simpa [current, hleast_eq] using hactivated

theorem fair_frequent_services_of_finalSet {seed : ℕ}
    (snode : ScheduledActiveState seed) :
    ∀ a ∈ finalSet snode.fairStage, ∃ numerator denominator : ℕ,
      0 < numerator ∧ 0 < denominator ∧
        ∀ N : ℕ, ∃ k : ℕ,
          ∃ svc : ServiceExtension (snode.fairStage k) (snode.fairStage (k + 1)) a,
            N ≤ svc.protectedEndpoint ∧
              svc.protectedBlock.densityNumerator = numerator ∧
                svc.protectedBlock.densityDenominator = denominator := by
  intro a haFinal
  obtain ⟨k0, hk0_active⟩ := snode.fair_eventually_active_of_finalSet a haFinal
  refine ⟨1, 8 * (snode.fairStage k0).m a, by norm_num, ?_, ?_⟩
  · have hpos : 0 < (snode.fairStage k0).m a :=
      (snode.fairStage k0).modulus_pos hk0_active
    omega
  · intro N
    obtain ⟨k, hk_ge, hreq⟩ := fairRequest_frequently a (max N k0)
    have hN_le_k : N ≤ k := (le_max_left N k0).trans hk_ge
    have hk0_le_k : k0 ≤ k := (le_max_right N k0).trans hk_ge
    have hactive_k : a ∈ (snode.fairStage k).P :=
      snode.fairStageChain.P_subset_of_le hk0_le_k hk0_active
    let svc := snode.fairServiceExtension_of_active_request_eq hreq hactive_k
    refine ⟨k, svc, ?_, ?_, ?_⟩
    · exact hN_le_k.trans
        (snode.fairServiceExtension_of_active_request_eq_protectedEndpoint_ge hreq hactive_k)
    · exact snode.fairServiceExtension_of_active_request_eq_densityNumerator hreq hactive_k
    · have hden :=
        snode.fairServiceExtension_of_active_request_eq_densityDenominator hreq hactive_k
      have hm : (snode.fairStage k).m a = (snode.fairStage k0).m a :=
        snode.fairStageChain.m_eq_of_le_of_mem_P hk0_le_k hk0_active
      simpa [svc, hm] using hden

theorem finalSet_isAsymptoticBasisTwo {a : ℕ} (snode : ScheduledActiveState a) :
    IsAsymptoticBasisTwo (finalSet snode.stage) :=
  Erdos330.finalSet_isAsymptoticBasisTwo snode.stageChain snode.R_unbounded

theorem fair_finalSet_isAsymptoticBasisTwo {seed : ℕ} (snode : ScheduledActiveState seed) :
    IsAsymptoticBasisTwo (finalSet snode.fairStage) :=
  Erdos330.finalSet_isAsymptoticBasisTwo snode.fairStageChain snode.fair_R_unbounded

theorem finalSet_upperDensity_pos {a : ℕ} (snode : ScheduledActiveState a) :
    HasPositiveUpperDensity (finalSet snode.stage) := by
  refine finalSet_upperDensity_pos_of_frequent_stage_blocks (st := snode.stage)
    (numerator := 1) (denominator := 8 * snode.node.st.m a) ?_ ?_ ?_
  · norm_num
  · have hpos : 0 < snode.node.st.m a := snode.node.st.modulus_pos snode.active
    omega
  · exact snode.frequent_stage_blocks

theorem fair_finalSet_upperDensity_pos {seed : ℕ} (snode : ScheduledActiveState seed) :
    HasPositiveUpperDensity (finalSet snode.fairStage) := by
  refine finalSet_upperDensity_pos_of_frequent_stage_blocks (st := snode.fairStage)
    (numerator := 1) (denominator := 8 * snode.node.st.m seed) ?_ ?_ ?_
  · norm_num
  · have hpos : 0 < snode.node.st.m seed := snode.node.st.modulus_pos snode.active
    omega
  · exact snode.fair_frequent_seed_stage_blocks

theorem fixed_private_upperDensity_pos {a : ℕ} (snode : ScheduledActiveState a) :
    HasPositiveUpperDensity (privateSet (finalSet snode.stage) a) := by
  refine private_upperDensity_pos_of_frequent_services (st := snode.stage) snode.stageChain
    (a := a) (numerator := 1) (denominator := 8 * snode.node.st.m a) ?_ ?_ ?_
  · norm_num
  · have hpos : 0 < snode.node.st.m a := snode.node.st.modulus_pos snode.active
    omega
  · exact snode.frequent_services

theorem fair_seed_private_upperDensity_pos {seed : ℕ} (snode : ScheduledActiveState seed) :
    HasPositiveUpperDensity (privateSet (finalSet snode.fairStage) seed) := by
  refine private_upperDensity_pos_of_frequent_services (st := snode.fairStage) snode.fairStageChain
    (a := seed) (numerator := 1) (denominator := 8 * snode.node.st.m seed) ?_ ?_ ?_
  · norm_num
  · have hpos : 0 < snode.node.st.m seed := snode.node.st.modulus_pos snode.active
    omega
  · exact snode.fair_frequent_seed_services

theorem fair_mainTarget {seed : ℕ} (snode : ScheduledActiveState seed) :
    MainTarget := by
  refine mainTarget_of_frequent_stage_blocks_and_services snode.fairStageChain
    snode.fair_R_unbounded (setNumerator := 1)
    (setDenominator := 8 * snode.node.st.m seed) ?_ ?_ ?_ ?_
  · norm_num
  · have hpos : 0 < snode.node.st.m seed := snode.node.st.modulus_pos snode.active
    omega
  · exact snode.fair_frequent_seed_stage_blocks
  · exact snode.fair_frequent_services_of_finalSet

theorem fixedActive_finalSet_certificates {a : ℕ} (snode : ScheduledActiveState a) :
    IsAsymptoticBasisTwo (finalSet snode.stage) ∧
      HasPositiveUpperDensity (finalSet snode.stage) ∧
        HasPositiveUpperDensity (privateSet (finalSet snode.stage) a) :=
  ⟨snode.finalSet_isAsymptoticBasisTwo, snode.finalSet_upperDensity_pos,
    snode.fixed_private_upperDensity_pos⟩

theorem fairSeed_finalSet_certificates {seed : ℕ} (snode : ScheduledActiveState seed) :
    IsAsymptoticBasisTwo (finalSet snode.fairStage) ∧
      HasPositiveUpperDensity (finalSet snode.fairStage) ∧
        HasPositiveUpperDensity (privateSet (finalSet snode.fairStage) seed) :=
  ⟨snode.fair_finalSet_isAsymptoticBasisTwo, snode.fair_finalSet_upperDensity_pos,
    snode.fair_seed_private_upperDensity_pos⟩

noncomputable def initial (a m H X : ℕ)
    (hmPrime : Nat.Prime m) (hm23 : 23 ≤ m) (hmMod4 : m % 4 = 3)
    (haX : a ≤ X) (hlong : H + 4 * m ≤ X) : ScheduledActiveState a :=
  {
    node := BudgetedState.initialBudgetedState a m H X hmPrime hm23 hmMod4 haX hlong
    active := BudgetedState.initial_active a m H X hmPrime hm23 hmMod4 haX hlong
  }

theorem exists_initial : ∃ a : ℕ, Nonempty (ScheduledActiveState a) := by
  obtain ⟨m, hm23, hmPrime, hmMod4⟩ := exists_prime_three_mod_four_ge 23
  let H := m + 2
  let X := H + 4 * m
  exact ⟨1, ⟨initial 1 m H X hmPrime hm23 hmMod4 (by omega) (by omega)⟩⟩

theorem exists_leastActivation_chain_certificates :
    ∃ a : ℕ, ∃ st : ℕ → StageState,
      StageChain st ∧
        a ∈ finalSet st ∧
          IsAsymptoticBasisTwo (finalSet st) ∧
            HasPositiveUpperDensity (finalSet st) ∧
              HasPositiveUpperDensity (privateSet (finalSet st) a) := by
  obtain ⟨a, ⟨snode⟩⟩ := exists_initial
  exact ⟨a, snode.stage, snode.stageChain, ⟨0, snode.node.st.active_mem_state snode.active⟩,
    snode.finalSet_isAsymptoticBasisTwo, snode.finalSet_upperDensity_pos,
    snode.fixed_private_upperDensity_pos⟩

theorem exists_fairActivation_chain_seed_certificates :
    ∃ seed : ℕ, ∃ st : ℕ → StageState,
      StageChain st ∧
        seed ∈ finalSet st ∧
          IsAsymptoticBasisTwo (finalSet st) ∧
            HasPositiveUpperDensity (finalSet st) ∧
              HasPositiveUpperDensity (privateSet (finalSet st) seed) := by
  obtain ⟨seed, ⟨snode⟩⟩ := exists_initial
  exact ⟨seed, snode.fairStage, snode.fairStageChain,
    ⟨0, snode.node.st.active_mem_state snode.active⟩,
    snode.fair_finalSet_isAsymptoticBasisTwo, snode.fair_finalSet_upperDensity_pos,
    snode.fair_seed_private_upperDensity_pos⟩

end ScheduledActiveState

theorem erdos330_mainTarget : MainTarget := by
  obtain ⟨_seed, ⟨snode⟩⟩ := ScheduledActiveState.exists_initial
  exact snode.fair_mainTarget

end Erdos330
