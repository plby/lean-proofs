/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos163.RandomGreedy

/-!
# Deterministic part of the random-greedy argument

A successful run always chooses an unused common neighbor.  The invariant
below proves directly that every such completed run is an ordinary graph
embedding; no induced-edge condition is introduced.
-/

open Finset

namespace Erdos163
namespace RandomGreedy

universe u v w

variable {α : Type u} {β : Type v} {ι : Type w}
  [Fintype α] [DecidableEq α] [LinearOrder α]
  [Fintype β] [DecidableEq β] [DecidableEq ι]

/-- A run in which every transition uses the injective,
adjacency-preserving branch of the greedy rule. -/
inductive SuccessfulRun (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : α → ℕ)
    (momentExponent : ℕ) (default : β) :
    List α → State α β → State α β → Prop
  | nil (state) : SuccessfulRun G H host part threshold momentExponent default [] state state
  | cons {x : α} {xs : List α} {state final : State α β} {z : β}
      (hz : z ∈ unusedCandidates G H host part default state x)
      (hrest : SuccessfulRun G H host part threshold momentExponent default xs
        (step G H host part threshold momentExponent default x state z) final) :
      SuccessfulRun G H host part threshold momentExponent default (x :: xs) state final

def assigned (state : State α β) (x : α) : Prop :=
  (state.image x).isSome

/-- Invariant after precisely the vertices outside `remaining` have been
processed. -/
structure GoodState (G : SimpleGraph β) (H : SimpleGraph α)
    (host : ι → Finset β) (part : α → ι) (default : β)
    (remaining : List α) (state : State α β) : Prop where
  assigned_iff : ∀ x, assigned state x ↔ x ∉ remaining
  in_host : ∀ x, assigned state x → value default state x ∈ host (part x)
  injective : ∀ ⦃x y⦄, assigned state x → assigned state y →
    value default state x = value default state y → x = y
  map_adj : ∀ ⦃x y⦄, assigned state x → assigned state y →
    H.Adj x y → G.Adj (value default state x) (value default state y)
  before_remaining : ∀ ⦃x y⦄, x ∈ remaining → assigned state y → x < y

theorem goodState_initial (G : SimpleGraph β) (H : SimpleGraph α)
    (host : ι → Finset β) (part : α → ι) (default : β)
    (remaining : List α) (hcover : ∀ x, x ∈ remaining) :
    GoodState G H host part default remaining (initialState : State α β) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x
    simp [assigned, initialState, hcover x]
  · intro x hx
    simp [assigned, initialState] at hx
  · intro x y hx
    simp [assigned, initialState] at hx
  · intro x y hx
    simp [assigned, initialState] at hx
  · intro x y hx hy
    simp [assigned, initialState] at hy

@[simp] theorem assigned_step_self
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : α → ℕ)
    (momentExponent : ℕ) (default : β) (state : State α β) (x : α) (z : β) :
    assigned (step G H host part threshold momentExponent default x state z) x := by
  simp [assigned, step]

@[simp] theorem value_step_self
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : α → ℕ)
    (momentExponent : ℕ) (default : β) (state : State α β) (x : α) (z : β) :
    value default (step G H host part threshold momentExponent default x state z) x = z := by
  simp [value, step]

theorem assigned_step_of_ne
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : α → ℕ)
    (momentExponent : ℕ) (default : β) (state : State α β)
    {x y : α} (hyx : y ≠ x) (z : β) :
    assigned (step G H host part threshold momentExponent default x state z) y ↔
      assigned state y := by
  simp [assigned, step, hyx]

theorem value_step_of_ne
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : α → ℕ)
    (momentExponent : ℕ) (default : β) (state : State α β)
    {x y : α} (hyx : y ≠ x) (z : β) :
    value default (step G H host part threshold momentExponent default x state z) y =
      value default state y := by
  simp [value, step, hyx]

theorem mem_usedInPart_of_assigned
    (part : α → ι) (default : β) (state : State α β)
    {x y : α} (hy : assigned state y) (hpart : part y = part x) :
    value default state y ∈ usedInPart part default state x := by
  classical
  apply Finset.mem_image.mpr
  refine ⟨y, ?_, rfl⟩
  simp [assigned] at hy
  simp [hy, hpart]

theorem goodState_step
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : α → ℕ)
    (momentExponent : ℕ) (default : β)
    (hhost : ∀ ⦃i j⦄, i ≠ j → Disjoint (host i) (host j))
    (hpart : ∀ ⦃a b⦄, H.Adj a b → part a ≠ part b)
    {x : α} {xs : List α} {state : State α β} {z : β}
    (hxs : x ∉ xs) (hbelow : ∀ y ∈ xs, y < x)
    (hgood : GoodState G H host part default (x :: xs) state)
    (hz : z ∈ unusedCandidates G H host part default state x) :
    GoodState G H host part default xs
      (step G H host part threshold momentExponent default x state z) := by
  let state' := step G H host part threshold momentExponent default x state z
  have hzfull : z ∈ fullCandidates G H host part default state x :=
    (Finset.mem_sdiff.mp hz).1
  have hzhost : z ∈ host (part x) :=
    Defect.commonNeighbors_subset_target G _ _ hzfull
  have hnew_old_ne : ∀ ⦃y⦄, assigned state y → z ≠ value default state y := by
    intro y hy
    by_cases hpx : part y = part x
    · exact fun heq => (Finset.mem_sdiff.mp hz).2
        (heq ▸ mem_usedInPart_of_assigned part default state hy hpx)
    · have hyhost := hgood.in_host y hy
      intro heq
      rw [heq] at hzhost
      exact Finset.disjoint_left.mp (hhost hpx) hyhost hzhost
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro y
    by_cases hyx : y = x
    · subst y
      simp [state', assigned, step, hxs]
    · rw [assigned_step_of_ne G H host part threshold momentExponent default state hyx z]
      rw [hgood.assigned_iff]
      simp [hyx]
  · intro y hy
    by_cases hyx : y = x
    · subst y
      simpa [state'] using hzhost
    · rw [value_step_of_ne G H host part threshold momentExponent default state hyx z]
      exact hgood.in_host y
        ((assigned_step_of_ne G H host part threshold momentExponent default state hyx z).mp hy)
  · intro a b ha hb hab
    by_cases hax : a = x
    · subst a
      by_cases hbx : b = x
      · exact hbx.symm
      · exfalso
        have hbOld := (assigned_step_of_ne G H host part threshold momentExponent default state hbx z).mp hb
        have hvb := value_step_of_ne G H host part threshold momentExponent default state hbx z
        exact hnew_old_ne hbOld (by simpa [state', hvb] using hab)
    · by_cases hbx : b = x
      · subst b
        exfalso
        have haOld := (assigned_step_of_ne G H host part threshold momentExponent default state hax z).mp ha
        have hva := value_step_of_ne G H host part threshold momentExponent default state hax z
        exact hnew_old_ne haOld (by simpa [state', hva] using hab.symm)
      · have haOld := (assigned_step_of_ne G H host part threshold momentExponent default state hax z).mp ha
        have hbOld := (assigned_step_of_ne G H host part threshold momentExponent default state hbx z).mp hb
        apply hgood.injective haOld hbOld
        simpa [state', value_step_of_ne G H host part threshold momentExponent default state hax z,
          value_step_of_ne G H host part threshold momentExponent default state hbx z] using hab
  · intro a b ha hb hab
    by_cases hax : a = x
    · subst a
      have hbx : b ≠ x := fun h => H.irrefl (h ▸ hab)
      have hbOld := (assigned_step_of_ne G H host part threshold momentExponent default state hbx z).mp hb
      have hxb : x < b := hgood.before_remaining (by simp) hbOld
      have hbforward : b ∈ forwardNeighbors H x := by
        simp [forwardNeighbors, hab, hxb]
      have hadj : G.Adj z (value default state b) :=
        (((Defect.mem_commonNeighbors G _ _ z).mp hzfull).2
          ⟨b, hbforward⟩).symm
      simpa [state', value_step_of_ne G H host part threshold momentExponent default state hbx z]
        using hadj
    · by_cases hbx : b = x
      · subst b
        have hxa : x < a := hgood.before_remaining (by simp)
          ((assigned_step_of_ne G H host part threshold momentExponent default state hax z).mp ha)
        have haforward : a ∈ forwardNeighbors H x := by
          simp [forwardNeighbors, hab.symm, hxa]
        have hadj : G.Adj z (value default state a) :=
          (((Defect.mem_commonNeighbors G _ _ z).mp hzfull).2
            ⟨a, haforward⟩).symm
        simpa [state', value_step_of_ne G H host part threshold momentExponent default state hax z]
          using hadj.symm
      · have haOld := (assigned_step_of_ne G H host part threshold momentExponent default state hax z).mp ha
        have hbOld := (assigned_step_of_ne G H host part threshold momentExponent default state hbx z).mp hb
        simpa [state', value_step_of_ne G H host part threshold momentExponent default state hax z,
          value_step_of_ne G H host part threshold momentExponent default state hbx z] using
          hgood.map_adj haOld hbOld hab
  · intro a b ha hb
    by_cases hbx : b = x
    · subst b
      exact hbelow a ha
    · exact hgood.before_remaining (by simp [ha])
        ((assigned_step_of_ne G H host part threshold momentExponent default state hbx z).mp hb)

theorem SuccessfulRun.good_final
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : α → ℕ)
    (momentExponent : ℕ) (default : β)
    (hhost : ∀ ⦃i j⦄, i ≠ j → Disjoint (host i) (host j))
    (hpart : ∀ ⦃a b⦄, H.Adj a b → part a ≠ part b)
    {remaining : List α} {state final : State α β}
    (hrun : SuccessfulRun G H host part threshold momentExponent default remaining state final)
    (hpair : remaining.Pairwise fun x y => y < x)
    (hgood : GoodState G H host part default remaining state) :
    GoodState G H host part default [] final := by
  induction hrun with
  | nil state => simpa using hgood
  | @cons x xs state final z hz hrest ih =>
      have hxs : x ∉ xs := (List.nodup_cons.mp hpair.nodup).1
      have hp := (List.pairwise_cons.mp hpair)
      have hbelow : ∀ y ∈ xs, y < x := hp.1
      exact ih hp.2
        (goodState_step G H host part threshold momentExponent default hhost hpart
          hxs hbelow hgood hz)

theorem SuccessfulRun.hasCopy
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : α → ℕ)
    (momentExponent : ℕ) (default : β)
    (hhost : ∀ ⦃i j⦄, i ≠ j → Disjoint (host i) (host j))
    (hpart : ∀ ⦃a b⦄, H.Adj a b → part a ≠ part b)
    {remaining : List α} {final : State α β}
    (hcover : ∀ x, x ∈ remaining)
    (hpair : remaining.Pairwise fun x y => y < x)
    (hrun : SuccessfulRun G H host part threshold momentExponent default remaining
      (initialState : State α β) final) :
    HasCopy H G := by
  have hgood := hrun.good_final G H host part threshold momentExponent default hhost hpart hpair
    (goodState_initial G H host part default remaining hcover)
  refine ⟨{
    toFun := value default final
    injective' := ?_
    map_adj' := ?_
  }⟩
  · intro x y hxy
    exact hgood.injective
      ((hgood.assigned_iff x).2 (by simp))
      ((hgood.assigned_iff y).2 (by simp)) hxy
  · intro x y hxy
    exact hgood.map_adj
      ((hgood.assigned_iff x).2 (by simp))
      ((hgood.assigned_iff y).2 (by simp)) hxy

/-! ## The recorded failure count selects the successful branch -/

def partVertices (part : α → ι) (x : α) : Finset α :=
  Finset.univ.filter fun y => part y = part x

theorem usedInPart_card_le (part : α → ι) (default : β)
    (state : State α β) (x : α) :
    (usedInPart part default state x).card ≤ (partVertices part x).card := by
  classical
  calc
    (usedInPart part default state x).card ≤
        (Finset.univ.filter fun y => (state.image y).isSome ∧ part y = part x).card :=
      Finset.card_image_le
    _ ≤ (partVertices part x).card := by
      apply Finset.card_le_card
      intro y hy
      simp [partVertices] at hy ⊢
      exact hy.2

theorem choices_eq_unused_of_large
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : α → ℕ)
    (default : β) (state : State α β) (x : α)
    (hthreshold : 0 < threshold x)
    (hpartSize : 2 * (partVertices part x).card ≤ threshold x)
    (hfull : threshold x ≤
      (fullCandidates G H host part default state x).card) :
    choices G H host part default state x =
      unusedCandidates G H host part default state x := by
  classical
  let N := fullCandidates G H host part default state x
  let U := usedInPart part default state x
  let L := unusedCandidates G H host part default state x
  have hfullN : threshold x ≤ N.card := by simpa [N] using hfull
  have hNpos : 0 < N.card := hthreshold.trans_le hfullN
  have hNne : N ≠ ∅ := Finset.nonempty_iff_ne_empty.mp (Finset.card_pos.mp hNpos)
  have hU : U.card ≤ (partVertices part x).card := by
    simpa [U] using usedInPart_card_le part default state x
  have hNU : 2 * U.card ≤ N.card := by omega
  have hNLU : N.card ≤ L.card + U.card := by
    simpa [L, unusedCandidates, N, U] using
      (Finset.card_le_card_sdiff_add_card (s := N) (t := U))
  have hnotSmall : ¬2 * L.card < N.card := by omega
  unfold choices
  dsimp
  simpa [N, L, hNne, hnotSmall]

theorem stateRun_failures_le
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : α → ℕ)
    (momentExponent : ℕ) (default : β)
    {remaining : List α} {state final : State α β}
    (hrun : Process.StateRun
      (fun x state => choices G H host part default state x)
      (step G H host part threshold momentExponent default)
      remaining state final) :
    state.failures ≤ final.failures := by
  induction hrun with
  | nil state => exact le_rfl
  | @cons x xs state final z hz hrest ih =>
      apply (show state.failures ≤
        (step G H host part threshold momentExponent default x state z).failures by
          simp [step]) |>.trans
      exact ih

theorem stateRun_toSuccessfulRun
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : α → ℕ)
    (momentExponent : ℕ) (default : β)
    (hthreshold : ∀ x, 0 < threshold x)
    (hpartSize : ∀ x, 2 * (partVertices part x).card ≤ threshold x)
    {remaining : List α} {state final : State α β}
    (hrun : Process.StateRun
      (fun x state => choices G H host part default state x)
      (step G H host part threshold momentExponent default)
      remaining state final)
    (hfinal : final.failures = 0) :
    SuccessfulRun G H host part threshold momentExponent default remaining state final := by
  induction hrun with
  | nil state => exact .nil state
  | @cons x xs state final z hz hrest ih =>
      have hstepzero :
          (step G H host part threshold momentExponent default x state z).failures = 0 :=
        Nat.eq_zero_of_le_zero ((stateRun_failures_le G H host part threshold
          momentExponent default hrest).trans_eq hfinal)
      have hfull : threshold x ≤
          (fullCandidates G H host part default state x).card := by
        by_contra hnot
        have hlt : (fullCandidates G H host part default state x).card < threshold x :=
          Nat.lt_of_not_ge hnot
        simp [step, hlt] at hstepzero
      have hchoices := choices_eq_unused_of_large G H host part threshold default state x
        (hthreshold x) (hpartSize x) hfull
      exact .cons (hchoices ▸ hz) (ih hfinal)

theorem order_pairwise :
    (order : List α).Pairwise fun x y => y < x := by
  simpa [order] using (Finset.sortedGT_sort (Finset.univ : Finset α)).pairwise

theorem order_mem (x : α) : x ∈ (order : List α) := by
  rw [← List.mem_toFinset, order_toFinset]
  exact Finset.mem_univ x

theorem hasCopy_of_failure_free_run
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : α → ℕ)
    (momentExponent : ℕ) (default : β)
    (hhost : ∀ ⦃i j⦄, i ≠ j → Disjoint (host i) (host j))
    (hpart : ∀ ⦃a b⦄, H.Adj a b → part a ≠ part b)
    (hthreshold : ∀ x, 0 < threshold x)
    (hpartSize : ∀ x, 2 * (partVertices part x).card ≤ threshold x)
    {final : State α β}
    (hrun : Process.StateRun
      (fun x state => choices G H host part default state x)
      (step G H host part threshold momentExponent default)
      order (initialState : State α β) final)
    (hfinal : final.failures = 0) :
    HasCopy H G := by
  exact (stateRun_toSuccessfulRun G H host part threshold momentExponent default
    hthreshold hpartSize hrun hfinal).hasCopy G H host part threshold momentExponent default
      hhost hpart order_mem order_pairwise

theorem hasCopy_of_average_failures_lt_one
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : α → ℕ)
    (momentExponent : ℕ) (default : β)
    (hhostNonempty : ∀ i, (host i).Nonempty)
    (hhostDisjoint : ∀ ⦃i j⦄, i ≠ j → Disjoint (host i) (host j))
    (hpart : ∀ ⦃a b⦄, H.Adj a b → part a ≠ part b)
    (hthreshold : ∀ x, 0 < threshold x)
    (hpartSize : ∀ x, 2 * (partVertices part x).card ≤ threshold x)
    (haverage : average G H host part threshold momentExponent default
      (fun state => (state.failures : ℝ)) < 1) :
    HasCopy H G := by
  obtain ⟨final, hrun, hle⟩ := Process.exists_stateRun_le_average
    (fun x state => choices G H host part default state x)
    (step G H host part threshold momentExponent default)
    (fun x state => choices_nonempty G H host hhostNonempty part default state x)
    order (initialState : State α β) (fun state => (state.failures : ℝ))
  have hfinalLt : (final.failures : ℝ) < 1 := hle.trans_lt haverage
  have hfinal : final.failures = 0 := by
    exact_mod_cast (Nat.lt_one_iff.mp (by exact_mod_cast hfinalLt))
  exact hasCopy_of_failure_free_run G H host part threshold momentExponent default
    hhostDisjoint hpart hthreshold hpartSize hrun hfinal

/-! ## Failures are dominated by the recorded defect powers -/

structure FailureState (remaining : List α) (state : State α β) : Prop where
  observed_zero : ∀ x ∈ remaining, state.observed x = 0
  failures_le : (state.failures : ℝ) ≤ ∑ x, state.observed x

theorem failureState_initial (remaining : List α) :
    FailureState remaining (initialState : State α β) := by
  constructor
  · intro x hx
    rfl
  · simp [initialState]

theorem one_le_defectPower_of_small
    (G : SimpleGraph β) [DecidableRel G.Adj]
    {θ exponent : ℕ} (hθ : 0 < θ)
    {κ : Type*} [Fintype κ] (q : κ → β) (T : Finset β)
    (hsmall : (FiniteDefect.commonNeighbors G q T).card < θ) :
    1 ≤ FiniteDefect.defectPower G θ q T exponent := by
  have hne : FiniteDefect.defect G θ q T ≠ 0 := by
    unfold FiniteDefect.defect
    dsimp
    rw [if_neg (Nat.not_le_of_lt hsmall)]
    split_ifs with hz
    · positivity
    · positivity
  simp only [FiniteDefect.defectPower, hne, if_false]
  have hone := FiniteDefect.one_le_defect_of_ne_zero G hne
  simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hone exponent

theorem failureState_step
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : α → ℕ)
    (momentExponent : ℕ) (default : β)
    {x : α} {xs : List α} {state : State α β} (z : β)
    (hθ : 0 < threshold x) (hxs : x ∉ xs)
    (hstate : FailureState (x :: xs) state) :
    FailureState xs
      (step G H host part threshold momentExponent default x state z) := by
  let q : forwardNeighbors H x → β := fun y => value default state y
  let T := host (part x)
  let w := FiniteDefect.defectPower G (threshold x) q T momentExponent
  have hxzero : state.observed x = 0 := hstate.observed_zero x (by simp)
  have hw0 : 0 ≤ w := FiniteDefect.defectPower_nonneg G _ _ _ _
  constructor
  · intro y hy
    have hyx : y ≠ x := by
      intro h
      subst y
      exact hxs hy
    simp [step, hyx, hstate.observed_zero y (by simp [hy])]
  · have hsum :
        (∑ y, (step G H host part threshold momentExponent default x state z).observed y) =
          (∑ y, state.observed y) + w := by
      rw [show (step G H host part threshold momentExponent default x state z).observed =
          Function.update state.observed x w by rfl]
      rw [Finset.sum_update_of_mem (Finset.mem_univ x)]
      rw [← Finset.sum_erase_add Finset.univ state.observed (Finset.mem_univ x)]
      rw [show (Finset.univ : Finset α) \ {x} = Finset.univ.erase x by
        ext y
        simp]
      simp only [hxzero, add_zero, w, q, T]
      ring
    rw [hsum]
    by_cases hsmall :
        (fullCandidates G H host part default state x).card < threshold x
    · have hw1 : 1 ≤ w := by
        apply one_le_defectPower_of_small G hθ q T
        simpa [q, T, fullCandidates]
      simp only [step, hsmall, if_pos, Nat.cast_add, Nat.cast_one]
      linarith [hstate.failures_le]
    · simp [step, hsmall]
      linarith [hstate.failures_le]

theorem stateRun_failures_le_sum_observed
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : α → ℕ)
    (momentExponent : ℕ) (default : β)
    (hthreshold : ∀ x, 0 < threshold x)
    {remaining : List α} {state final : State α β}
    (hrun : Process.StateRun
      (fun x state => choices G H host part default state x)
      (step G H host part threshold momentExponent default)
      remaining state final)
    (hnodup : remaining.Nodup)
    (hstate : FailureState remaining state) :
    (final.failures : ℝ) ≤ ∑ x, final.observed x := by
  induction hrun with
  | nil state => exact hstate.failures_le
  | @cons x xs state final z hz hrest ih =>
      exact ih (List.nodup_cons.mp hnodup).2
        (failureState_step G H host part threshold momentExponent default z
          (hthreshold x) (List.nodup_cons.mp hnodup).1 hstate)

theorem average_failures_le_observed
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : α → ℕ)
    (momentExponent : ℕ) (default : β)
    (hthreshold : ∀ x, 0 < threshold x) :
    average G H host part threshold momentExponent default
        (fun state => (state.failures : ℝ)) ≤
      average G H host part threshold momentExponent default
        (fun state => ∑ x, state.observed x) := by
  apply Process.stateAverage_mono
  intro final hrun
  exact stateRun_failures_le_sum_observed G H host part threshold momentExponent default
    hthreshold hrun order_nodup (failureState_initial order)

theorem average_sum_observed
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : α → ℕ)
    (momentExponent : ℕ) (default : β) :
    average G H host part threshold momentExponent default
        (fun state => ∑ x, state.observed x) =
      ∑ x, average G H host part threshold momentExponent default
        (fun state => state.observed x) := by
  exact Process.stateAverage_sum _ _ order (initialState : State α β)
    Finset.univ (fun x state => state.observed x)

theorem hasCopy_of_observed_bounds
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : α → ℕ)
    (momentExponent : ℕ) (default : β)
    (hhostNonempty : ∀ i, (host i).Nonempty)
    (hhostDisjoint : ∀ ⦃i j⦄, i ≠ j → Disjoint (host i) (host j))
    (hpart : ∀ ⦃a b⦄, H.Adj a b → part a ≠ part b)
    (hthreshold : ∀ x, 0 < threshold x)
    (hpartSize : ∀ x, 2 * (partVertices part x).card ≤ threshold x)
    {B : ℝ}
    (hobserved : ∀ x, average G H host part threshold momentExponent default
      (fun state => state.observed x) ≤ B)
    (htotal : (Fintype.card α : ℝ) * B < 1) :
    HasCopy H G := by
  apply hasCopy_of_average_failures_lt_one G H host part threshold momentExponent default
    hhostNonempty hhostDisjoint hpart hthreshold hpartSize
  calc
    average G H host part threshold momentExponent default
        (fun state => (state.failures : ℝ)) ≤
        average G H host part threshold momentExponent default
          (fun state => ∑ x, state.observed x) :=
      average_failures_le_observed G H host part threshold momentExponent default hthreshold
    _ = ∑ x, average G H host part threshold momentExponent default
          (fun state => state.observed x) :=
      average_sum_observed G H host part threshold momentExponent default
    _ ≤ ∑ _x : α, B := Finset.sum_le_sum fun x _ => hobserved x
    _ = (Fintype.card α : ℝ) * B := by simp
    _ < 1 := htotal

end RandomGreedy
end Erdos163
