/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos163.Process
import Mathlib.Data.Finset.Sort

/-!
# Erdős Problem 163: finite random-greedy embedding process

This is the exact three-branch process used in Lee's argument, expressed as
nested finite averages.  A state records the partial map, the number of
threshold failures, and the defect observed when each target vertex was
processed.
-/

open scoped BigOperators
open Finset

namespace Erdos163
namespace RandomGreedy

universe u v w

variable {α : Type u} {β : Type v} {ι : Type w}
  [Fintype α] [DecidableEq α] [LinearOrder α]
  [Fintype β] [DecidableEq β] [DecidableEq ι]

structure State (α : Type u) (β : Type v) where
  image : α → Option β
  failures : ℕ
  defectSeen : α → ℝ
  costSeen : α → ℝ
  observed : α → ℝ

def initialState : State α β where
  image := fun _ => none
  failures := 0
  defectSeen := fun _ => 0
  costSeen := fun _ => 0
  observed := fun _ => 0

def value (default : β) (state : State α β) (x : α) : β :=
  (state.image x).getD default

/-- Target neighbors which occur earlier in the descending greedy process. -/
def forwardNeighbors (H : SimpleGraph α) [DecidableRel H.Adj]
    (x : α) : Finset α :=
  Finset.univ.filter fun y => H.Adj x y ∧ x < y

/-- Host common neighborhood available before enforcing injectivity. -/
def fullCandidates (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (default : β)
    (state : State α β) (x : α) : Finset β :=
  FiniteDefect.commonNeighbors G
    (fun y : forwardNeighbors H x => value default state y) (host (part x))

/-- Images already occupying the same host part. -/
def usedInPart (part : α → ι) (default : β)
    (state : State α β) (x : α) : Finset β :=
  (Finset.univ.filter fun y => (state.image y).isSome ∧ part y = part x).image
    (fun y => value default state y)

def unusedCandidates (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (default : β)
    (state : State α β) (x : α) : Finset β :=
  fullCandidates G H host part default state x \ usedInPart part default state x

/-- Lee's three branches: a total fallback when the common neighborhood is
empty, the full common neighborhood when deleting occupied vertices loses
more than half, and otherwise the unused common neighborhood. -/
def choices (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (default : β)
    (state : State α β) (x : α) : Finset β :=
  let N := fullCandidates G H host part default state x
  let L := unusedCandidates G H host part default state x
  if N = ∅ then host (part x) else if 2 * L.card < N.card then N else L

/-- Likelihood-ratio cost of replacing the greedy choice at `x` by a
uniform choice in its whole host part. -/
noncomputable def localCost (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (default : β)
    (state : State α β) (x : α) : ℝ :=
  let m := (fullCandidates G H host part default state x).card
  if m = 0 then 1 else 2 * (host (part x)).card / m

theorem localCost_nonneg (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (default : β)
    (state : State α β) (x : α) :
    0 ≤ localCost G H host part default state x := by
  unfold localCost
  dsimp
  split_ifs
  · norm_num
  · positivity

theorem choices_nonempty (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (hhost : ∀ i, (host i).Nonempty)
    (part : α → ι) (default : β) (state : State α β) (x : α) :
    (choices G H host part default state x).Nonempty := by
  classical
  unfold choices
  dsimp
  let N := fullCandidates G H host part default state x
  let L := unusedCandidates G H host part default state x
  change (if N = ∅ then host (part x) else if 2 * L.card < N.card then N else L).Nonempty
  by_cases hN : N = ∅
  · rw [if_pos hN]
    exact hhost _
  rw [if_neg hN]
  by_cases hsmall : 2 * L.card < N.card
  · rw [if_pos hsmall]
    exact Finset.nonempty_iff_ne_empty.mpr hN
  · rw [if_neg hsmall]
    have hNpos : 0 < N.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hN)
    apply Finset.card_pos.mp
    by_contra hLpos
    have hLzero : L.card = 0 := Nat.eq_zero_of_not_pos hLpos
    exact hsmall (by simpa [hLzero] using hNpos)

theorem choices_subset_host (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (default : β)
    (state : State α β) (x : α) :
    choices G H host part default state x ⊆ host (part x) := by
  classical
  unfold choices
  dsimp
  split_ifs
  · exact subset_rfl
  · exact Defect.commonNeighbors_subset_target G _ _
  · exact (Finset.sdiff_subset.trans
      (Defect.commonNeighbors_subset_target G _ _))

theorem host_card_div_choices_card_le_cost
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (hhost : ∀ i, (host i).Nonempty)
    (part : α → ι) (default : β) (state : State α β) (x : α) :
    ((host (part x)).card : ℝ) /
        (choices G H host part default state x).card ≤
      localCost G H host part default state x := by
  classical
  unfold choices localCost
  dsimp
  set N := fullCandidates G H host part default state x with hNdef
  set L := unusedCandidates G H host part default state x with hLdef
  by_cases hN : N = ∅
  · have hV0 : ((host (part x)).card : ℝ) ≠ 0 := by
      exact_mod_cast (hhost (part x)).card_ne_zero
    simp [hN, hV0]
  have hNcard : N.card ≠ 0 := by simpa [Finset.card_eq_zero] using hN
  rw [if_neg hN, if_neg hNcard]
  by_cases hsmall : 2 * L.card < N.card
  · rw [if_pos hsmall]
    have hNnonneg : 0 ≤ ((host (part x)).card : ℝ) / N.card := by positivity
    calc
      ((host (part x)).card : ℝ) / N.card ≤
          2 * (((host (part x)).card : ℝ) / N.card) := by linarith
      _ = 2 * (host (part x)).card / N.card := by ring
  · rw [if_neg hsmall]
    have hNpos : (0 : ℝ) < N.card := by exact_mod_cast Nat.pos_of_ne_zero hNcard
    have hLposNat : 0 < L.card := by
      by_contra hnot
      have hLzero : L.card = 0 := Nat.eq_zero_of_not_pos hnot
      exact hsmall (by simpa [hLzero] using Nat.pos_of_ne_zero hNcard)
    have hLpos : (0 : ℝ) < L.card := by exact_mod_cast hLposNat
    apply (div_le_div_iff₀ hLpos hNpos).2
    have hNL : (N.card : ℝ) ≤ 2 * L.card := by
      exact_mod_cast Nat.le_of_not_gt hsmall
    have hmul := mul_le_mul_of_nonneg_left hNL
      (show (0 : ℝ) ≤ (host (part x)).card by positivity)
    simpa [mul_assoc, mul_comm, mul_left_comm] using hmul

theorem localCost_le_defect
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : α → ℕ)
    (default : β) (state : State α β) (x : α)
    {γ : ℝ} (hγ : 1 ≤ γ)
    (hsize : ((host (part x)).card : ℝ) ≤ γ * threshold x) :
    localCost G H host part default state x ≤
      2 * γ * max 1
        (FiniteDefect.defect G (threshold x)
          (fun y : forwardNeighbors H x => value default state y) (host (part x))) := by
  classical
  unfold localCost
  dsimp
  set q : forwardNeighbors H x → β := fun y => value default state y with hq
  set m := (fullCandidates G H host part default state x).card with hmdef
  have hcardEq : (FiniteDefect.commonNeighbors G q (host (part x))).card = m := by
    simp [m, q, fullCandidates]
  by_cases hm : m = 0
  · rw [if_pos hm]
    have : (1 : ℝ) ≤ 2 * γ := by linarith
    have hmax : (1 : ℝ) ≤ max 1
        (FiniteDefect.defect G (threshold x) q (host (part x))) := le_max_left _ _
    apply this.trans
    calc
      (2 * γ : ℝ) = (2 * γ) * 1 := by ring
      _ ≤ (2 * γ) * max 1
          (FiniteDefect.defect G (threshold x) q (host (part x))) :=
        mul_le_mul_of_nonneg_left hmax (by positivity)
  rw [if_neg hm]
  have hmpos : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
  by_cases hlarge : threshold x ≤ m
  · have hlarge' : threshold x ≤
        (FiniteDefect.commonNeighbors G q (host (part x))).card := by
      simpa [hcardEq] using hlarge
    rw [FiniteDefect.defect_eq_zero_of_threshold_le G hlarge']
    simp only [max_eq_left (by norm_num : (0 : ℝ) ≤ 1)]
    apply (div_le_iff₀ hmpos).2
    have hcast : ((threshold x : ℕ) : ℝ) ≤ m := by exact_mod_cast hlarge
    have hγ0 : 0 ≤ γ := hγ.trans' zero_le_one
    have := hsize.trans (mul_le_mul_of_nonneg_left hcast hγ0)
    nlinarith
  · have hsmall : m < threshold x := Nat.lt_of_not_ge hlarge
    have hmpos' : 0 < (FiniteDefect.commonNeighbors G q (host (part x))).card := by
      simpa [hcardEq] using Nat.pos_of_ne_zero hm
    have hsmall' : (FiniteDefect.commonNeighbors G q (host (part x))).card < threshold x := by
      simpa [hcardEq] using hsmall
    rw [FiniteDefect.defect_eq_div_of_pos_card_lt G hmpos' hsmall', hcardEq]
    have hone : (1 : ℝ) ≤ (threshold x : ℝ) / m :=
      (one_le_div₀ hmpos).2 (by exact_mod_cast hsmall.le)
    rw [max_eq_right hone]
    apply (div_le_iff₀ hmpos).2
    have hγ0 : 0 ≤ γ := hγ.trans' zero_le_one
    have hscaled := mul_le_mul_of_nonneg_left hsize (show (0 : ℝ) ≤ 2 by norm_num)
    calc
      (2 : ℝ) * (host (part x)).card ≤ 2 * (γ * threshold x) := hscaled
      _ = (2 * γ * ((threshold x : ℝ) / m)) * m := by field_simp

noncomputable def step (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : α → ℕ)
    (momentExponent : ℕ) (default : β)
    (x : α) (state : State α β) (z : β) : State α β where
  image := Function.update state.image x (some z)
  failures := state.failures +
    if (fullCandidates G H host part default state x).card < threshold x then 1 else 0
  defectSeen := Function.update state.defectSeen x
    (FiniteDefect.defect G (threshold x)
      (fun y : forwardNeighbors H x => value default state y) (host (part x)))
  costSeen := Function.update state.costSeen x
    (localCost G H host part default state x)
  observed := Function.update state.observed x
    (FiniteDefect.defectPower G (threshold x)
      (fun y : forwardNeighbors H x => value default state y)
      (host (part x)) momentExponent)

/-- Descending enumeration of the target vertices. -/
def order : List α := Finset.univ.sort (fun x y => y ≤ x)

theorem order_nodup : (order : List α).Nodup :=
  Finset.sort_nodup _ _

@[simp] theorem order_toFinset : (order : List α).toFinset = Finset.univ := by
  simp [order]

/-- The finite expectation defining the greedy process. -/
noncomputable def average (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : α → ℕ)
    (momentExponent : ℕ) (default : β) (payoff : State α β → ℝ) : ℝ :=
  Process.stateAverage
    (fun x state => choices G H host part default state x)
    (step G H host part threshold momentExponent default)
    order (initialState : State α β) payoff

end RandomGreedy
end Erdos163
