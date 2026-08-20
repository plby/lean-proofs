/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos163.Embedding

/-!
# Neutralizing random-greedy transitions

At a neutralized target vertex the process chooses uniformly from its entire
host part.  This file proves the exact finite change-of-measure comparison
between two neutralization sets.
-/

open Finset

namespace Erdos163
namespace RandomGreedy

universe u v w

variable {α : Type u} {β : Type v} {ι : Type w}
  [Fintype α] [DecidableEq α] [LinearOrder α]
  [Fintype β] [DecidableEq β] [DecidableEq ι]

def maskedChoices (I : Finset α)
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (default : β)
    (x : α) (state : State α β) : Finset β :=
  if x ∈ I then host (part x) else choices G H host part default state x

noncomputable def neutralAverage (I : Finset α)
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : α → ℕ)
    (momentExponent : ℕ) (default : β) (payoff : State α β → ℝ) : ℝ :=
  Process.stateAverage (maskedChoices I G H host part default)
    (step G H host part threshold momentExponent default)
    order (initialState : State α β) payoff

def changeSet (I₁ I₂ : Finset α) : Finset α := I₂ \ I₁

noncomputable def changeWeight (I₁ I₂ : Finset α)
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (default : β)
    (x : α) (state : State α β) : ℝ :=
  if x ∈ changeSet I₁ I₂ then localCost G H host part default state x else 1

theorem maskedChoices_nonempty (I : Finset α)
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (hhost : ∀ i, (host i).Nonempty)
    (part : α → ι) (default : β) (x : α) (state : State α β) :
    (maskedChoices I G H host part default x state).Nonempty := by
  unfold maskedChoices
  split_ifs
  · exact hhost _
  · exact choices_nonempty G H host hhost part default state x

theorem maskedChoices_mono {I₁ I₂ : Finset α} (hI : I₁ ⊆ I₂)
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (default : β)
    (x : α) (state : State α β) :
    maskedChoices I₁ G H host part default x state ⊆
      maskedChoices I₂ G H host part default x state := by
  by_cases hx₁ : x ∈ I₁
  · have hx₂ := hI hx₁
    simp [maskedChoices, hx₁, hx₂]
  · by_cases hx₂ : x ∈ I₂
    · simpa [maskedChoices, hx₁, hx₂] using
        choices_subset_host G H host part default state x
    · simp [maskedChoices, hx₁, hx₂]

theorem maskedChoices_ratio_le_weight {I₁ I₂ : Finset α} (hI : I₁ ⊆ I₂)
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (hhost : ∀ i, (host i).Nonempty)
    (part : α → ι) (default : β) (x : α) (state : State α β) :
    ((maskedChoices I₂ G H host part default x state).card : ℝ) /
        (maskedChoices I₁ G H host part default x state).card ≤
      changeWeight I₁ I₂ G H host part default x state := by
  by_cases hx₁ : x ∈ I₁
  · have hx₂ := hI hx₁
    have hcard : ((host (part x)).card : ℝ) ≠ 0 := by
      exact_mod_cast (hhost (part x)).card_ne_zero
    simp [maskedChoices, changeWeight, changeSet, hx₁, hx₂, hcard]
  · by_cases hx₂ : x ∈ I₂
    · simp only [maskedChoices, hx₁, hx₂, if_false, if_true]
      rw [changeWeight, if_pos (by simp [changeSet, hx₁, hx₂])]
      exact host_card_div_choices_card_le_cost G H host hhost part default state x
    · have hne := choices_nonempty G H host hhost part default state x
      have hcard : ((choices G H host part default state x).card : ℝ) ≠ 0 := by
        exact_mod_cast hne.card_ne_zero
      simp [maskedChoices, changeWeight, changeSet, hx₁, hx₂, hcard]

theorem changeWeight_nonneg (I₁ I₂ : Finset α)
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (default : β)
    (x : α) (state : State α β) :
    0 ≤ changeWeight I₁ I₂ G H host part default x state := by
  unfold changeWeight
  split_ifs
  · exact localCost_nonneg G H host part default state x
  · norm_num

/-- Lee's likelihood-ratio comparison, before the product of local costs is
expanded by Young's inequality. -/
theorem neutralAverage_le_weighted {I₁ I₂ : Finset α} (hI : I₁ ⊆ I₂)
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (hhost : ∀ i, (host i).Nonempty)
    (part : α → ι) (threshold : α → ℕ) (momentExponent : ℕ)
    (default : β) (payoff : State α β → ℝ)
    (hpayoff : ∀ state, 0 ≤ payoff state) :
    neutralAverage I₁ G H host part threshold momentExponent default payoff ≤
      Process.weightedStateAverage
        (maskedChoices I₂ G H host part default)
        (step G H host part threshold momentExponent default)
        (changeWeight I₁ I₂ G H host part default)
        order (initialState : State α β) payoff := by
  apply Process.stateAverage_le_weightedStateAverage
  · exact fun x state => maskedChoices_nonempty I₁ G H host hhost part default x state
  · exact fun x state => maskedChoices_nonempty I₂ G H host hhost part default x state
  · exact fun x state => maskedChoices_mono hI G H host part default x state
  · exact fun x state =>
      maskedChoices_ratio_le_weight hI G H host hhost part default x state
  · exact fun x state => changeWeight_nonneg I₁ I₂ G H host part default x state
  · exact hpayoff

def costProduct (J : Finset α) (remaining : List α) (state : State α β) : ℝ :=
  ∏ x ∈ J.filter fun x => x ∈ remaining, state.costSeen x

theorem stateRun_costSeen_eq_of_not_mem
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : α → ℕ)
    (momentExponent : ℕ) (default : β)
    {remaining : List α} {state final : State α β}
    (hrun : Process.StateRun
      (fun x state => maskedChoices I G H host part default x state)
      (step G H host part threshold momentExponent default)
      remaining state final)
    {a : α} (ha : a ∉ remaining) :
    final.costSeen a = state.costSeen a := by
  induction hrun with
  | nil state => rfl
  | @cons x xs state final z hz hrest ih =>
      have hax : a ≠ x := by
        intro h
        subst a
        exact ha (by simp)
      have haTail : a ∉ xs := fun h => ha (by simp [h])
      rw [ih haTail]
      simp [step, hax]

theorem costProduct_cons_of_mem (J : Finset α) {x : α} {xs : List α}
    (hxJ : x ∈ J) (hxs : x ∉ xs) (state : State α β) :
    costProduct J (x :: xs) state =
      state.costSeen x * costProduct J xs state := by
  classical
  unfold costProduct
  have hfilter : J.filter (fun y => y ∈ x :: xs) =
      insert x (J.filter fun y => y ∈ xs) := by
    ext y
    simp only [mem_filter, List.mem_cons, mem_insert]
    constructor
    · rintro ⟨hyJ, hyx | hyxs⟩
      · exact Or.inl hyx
      · exact Or.inr ⟨hyJ, hyxs⟩
    · rintro (hyx | ⟨hyJ, hyxs⟩)
      · subst y
        exact ⟨hxJ, Or.inl rfl⟩
      · exact ⟨hyJ, Or.inr hyxs⟩
  rw [hfilter, Finset.prod_insert]
  simp [hxs]

theorem costProduct_cons_of_not_mem (J : Finset α) {x : α} {xs : List α}
    (hxJ : x ∉ J) (state : State α β) :
    costProduct J (x :: xs) state = costProduct J xs state := by
  classical
  unfold costProduct
  have hfilter : J.filter (fun y => y ∈ x :: xs) =
      J.filter fun y => y ∈ xs := by
    ext y
    simp only [mem_filter, List.mem_cons]
    constructor
    · rintro ⟨hyJ, hyx | hyxs⟩
      · subst y
        exact (hxJ hyJ).elim
      · exact ⟨hyJ, hyxs⟩
    · rintro ⟨hyJ, hyxs⟩
      exact ⟨hyJ, Or.inr hyxs⟩
  rw [hfilter]

/-- The inserted transition factors are exactly the product of the local
costs recorded at the newly neutralized vertices. -/
theorem weightedStateAverage_eq_costProduct (I₁ I₂ : Finset α)
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : α → ℕ)
    (momentExponent : ℕ) (default : β)
    {remaining : List α} (hnodup : remaining.Nodup) (state : State α β)
    (payoff : State α β → ℝ) :
    Process.weightedStateAverage
        (maskedChoices I₂ G H host part default)
        (step G H host part threshold momentExponent default)
        (changeWeight I₁ I₂ G H host part default)
        remaining state payoff =
      Process.stateAverage
        (maskedChoices I₂ G H host part default)
        (step G H host part threshold momentExponent default)
        remaining state
        (fun final => payoff final * costProduct (changeSet I₁ I₂) remaining final) := by
  induction remaining generalizing state with
  | nil => simp [costProduct]
  | cons x xs ih =>
      have hxs : x ∉ xs := (List.nodup_cons.mp hnodup).1
      have hxsNodup : xs.Nodup := (List.nodup_cons.mp hnodup).2
      rw [Process.weightedStateAverage_cons, Process.stateAverage_cons]
      apply Finset.expect_congr rfl
      intro z hz
      rw [ih hxsNodup]
      by_cases hxJ : x ∈ changeSet I₁ I₂
      · rw [changeWeight, if_pos hxJ]
        rw [← Process.stateAverage_const_mul]
        apply Process.stateAverage_congr
        intro final hrun
        have hcost : final.costSeen x =
            localCost G H host part default state x := by
          rw [stateRun_costSeen_eq_of_not_mem G H host part threshold momentExponent
            default hrun hxs]
          simp [step]
        rw [costProduct_cons_of_mem _ hxJ hxs]
        rw [hcost]
        ring
      · rw [changeWeight, if_neg hxJ]
        simp only [one_mul]
        apply Process.stateAverage_congr
        intro final hrun
        rw [costProduct_cons_of_not_mem _ hxJ]

theorem neutralAverage_le_costProduct {I₁ I₂ : Finset α} (hI : I₁ ⊆ I₂)
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (hhost : ∀ i, (host i).Nonempty)
    (part : α → ι) (threshold : α → ℕ) (momentExponent : ℕ)
    (default : β) (payoff : State α β → ℝ)
    (hpayoff : ∀ state, 0 ≤ payoff state) :
    neutralAverage I₁ G H host part threshold momentExponent default payoff ≤
      neutralAverage I₂ G H host part threshold momentExponent default
        (fun final => payoff final * costProduct (changeSet I₁ I₂) order final) := by
  refine (neutralAverage_le_weighted hI G H host hhost part threshold momentExponent
    default payoff hpayoff).trans_eq ?_
  exact weightedStateAverage_eq_costProduct I₁ I₂ G H host part threshold
    momentExponent default order_nodup (initialState : State α β) payoff

end RandomGreedy
end Erdos163
