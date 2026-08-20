/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos163.AdaptiveAverage

/-!
# Change of measure for the adaptive greedy schedule

Neutralizing a target vertex replaces its three-branch candidate set by its
whole host part.  The next target may depend on the current state, so this
file uses `AdaptiveProcess.average_le_weightedAverage` and proves that its
state weights are exactly the recorded product of local likelihood costs.
-/

open scoped BigOperators
open Finset

namespace Erdos163
namespace AdaptiveGreedy

universe u v w

variable {α : Type u} {β : Type v} {ι : Type w}
  [Fintype α] [DecidableEq α] [LinearOrder α]
  [Fintype β] [DecidableEq β]
  [DecidableEq ι] [LinearOrder ι]

noncomputable def maskedChoices (I : Finset α)
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : ι → ℕ)
    (defaultTarget : α) (default : β) (state : State α β) : Finset β :=
  let x := next G H host part threshold defaultTarget default state
  if x ∈ I then host (part x)
  else choices G H host part threshold defaultTarget default state

noncomputable def neutralAverage (I : Finset α)
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : ι → ℕ)
    (momentExponent : ℕ) (defaultTarget : α) (default : β)
    (payoff : State α β → ℝ) : ℝ :=
  AdaptiveProcess.average
    (maskedChoices I G H host part threshold defaultTarget default)
    (step G H host part threshold momentExponent defaultTarget default)
    (Fintype.card α) initialState payoff

def changeSet (I₁ I₂ : Finset α) : Finset α := I₂ \ I₁

noncomputable def changeWeight (I₁ I₂ : Finset α)
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : ι → ℕ)
    (defaultTarget : α) (default : β) (state : State α β) : ℝ :=
  let x := next G H host part threshold defaultTarget default state
  if x ∈ changeSet I₁ I₂ then
    RandomGreedy.localCost G H host part default state.core x
  else 1

theorem maskedChoices_nonempty (I : Finset α)
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (hhost : ∀ i, (host i).Nonempty)
    (part : α → ι) (threshold : ι → ℕ)
    (defaultTarget : α) (default : β) (state : State α β) :
    (maskedChoices I G H host part threshold defaultTarget default state).Nonempty := by
  unfold maskedChoices
  dsimp
  split_ifs
  · exact hhost _
  · exact choices_nonempty G H host hhost part threshold defaultTarget default state

theorem maskedChoices_mono {I₁ I₂ : Finset α} (hI : I₁ ⊆ I₂)
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : ι → ℕ)
    (defaultTarget : α) (default : β) (state : State α β) :
    maskedChoices I₁ G H host part threshold defaultTarget default state ⊆
      maskedChoices I₂ G H host part threshold defaultTarget default state := by
  let x := next G H host part threshold defaultTarget default state
  by_cases hx₁ : x ∈ I₁
  · have hx₂ := hI hx₁
    simp [maskedChoices, x, hx₁, hx₂]
  · by_cases hx₂ : x ∈ I₂
    · simpa [maskedChoices, choices, x, hx₁, hx₂] using
        RandomGreedy.choices_subset_host G H host part default state.core x
    · simp [maskedChoices, x, hx₁, hx₂]

theorem maskedChoices_ratio_le_weight {I₁ I₂ : Finset α} (hI : I₁ ⊆ I₂)
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (hhost : ∀ i, (host i).Nonempty)
    (part : α → ι) (threshold : ι → ℕ)
    (defaultTarget : α) (default : β) (state : State α β) :
    ((maskedChoices I₂ G H host part threshold defaultTarget default state).card : ℝ) /
        (maskedChoices I₁ G H host part threshold defaultTarget default state).card ≤
      changeWeight I₁ I₂ G H host part threshold defaultTarget default state := by
  let x := next G H host part threshold defaultTarget default state
  by_cases hx₁ : x ∈ I₁
  · have hx₂ := hI hx₁
    have hcard : ((host (part x)).card : ℝ) ≠ 0 := by
      exact_mod_cast (hhost (part x)).card_ne_zero
    simp [maskedChoices, changeWeight, changeSet, x, hx₁, hx₂, hcard]
  · by_cases hx₂ : x ∈ I₂
    · simp only [maskedChoices, x, hx₁, hx₂, if_false, if_true]
      rw [changeWeight, if_pos (by simp [changeSet, x, hx₁, hx₂])]
      simpa [choices] using
        RandomGreedy.host_card_div_choices_card_le_cost G H host hhost part
          default state.core x
    · have hne := choices_nonempty G H host hhost part threshold defaultTarget
        default state
      have hcard :
          ((choices G H host part threshold defaultTarget default state).card : ℝ) ≠ 0 := by
        exact_mod_cast hne.card_ne_zero
      simp [maskedChoices, changeWeight, changeSet, x, hx₁, hx₂, hcard]

theorem changeWeight_nonneg (I₁ I₂ : Finset α)
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : ι → ℕ)
    (defaultTarget : α) (default : β) (state : State α β) :
    0 ≤ changeWeight I₁ I₂ G H host part threshold defaultTarget default state := by
  unfold changeWeight
  dsimp
  split_ifs
  · exact RandomGreedy.localCost_nonneg G H host part default state.core _
  · norm_num

theorem neutralAverage_le_weighted {I₁ I₂ : Finset α} (hI : I₁ ⊆ I₂)
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (hhost : ∀ i, (host i).Nonempty)
    (part : α → ι) (threshold : ι → ℕ) (momentExponent : ℕ)
    (defaultTarget : α) (default : β) (payoff : State α β → ℝ)
    (hpayoff : ∀ state, 0 ≤ payoff state) :
    neutralAverage I₁ G H host part threshold momentExponent defaultTarget
        default payoff ≤
      AdaptiveProcess.weightedAverage
        (maskedChoices I₂ G H host part threshold defaultTarget default)
        (step G H host part threshold momentExponent defaultTarget default)
        (changeWeight I₁ I₂ G H host part threshold defaultTarget default)
        (Fintype.card α) initialState payoff := by
  apply AdaptiveProcess.average_le_weightedAverage
  · exact fun state => maskedChoices_nonempty I₁ G H host hhost part threshold
      defaultTarget default state
  · exact fun state => maskedChoices_nonempty I₂ G H host hhost part threshold
      defaultTarget default state
  · exact fun state => maskedChoices_mono hI G H host part threshold
      defaultTarget default state
  · exact fun state => maskedChoices_ratio_le_weight hI G H host hhost part
      threshold defaultTarget default state
  · exact fun state => changeWeight_nonneg I₁ I₂ G H host part threshold
      defaultTarget default state
  · exact hpayoff

noncomputable def costProduct (J remaining : Finset α)
    (state : State α β) : ℝ :=
  ∏ x ∈ J.filter (· ∈ remaining), state.core.costSeen x

theorem stateRun_costSeen_eq_of_not_mem (I : Finset α)
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : ι → ℕ)
    (momentExponent : ℕ) (defaultTarget : α) (default : β)
    {fuel : ℕ} {state final : State α β}
    (hrun : AdaptiveProcess.StateRun
      (maskedChoices I G H host part threshold defaultTarget default)
      (step G H host part threshold momentExponent defaultTarget default)
      fuel state final)
    (hfuel : fuel ≤ state.remaining.card)
    {a : α} (ha : a ∉ state.remaining) :
    final.core.costSeen a = state.core.costSeen a := by
  induction hrun with
  | nil state => rfl
  | @cons fuel state final z hz hrest ih =>
      have hcardpos : 0 < state.remaining.card := by omega
      have hne : state.remaining.Nonempty := Finset.card_pos.mp hcardpos
      let x := next G H host part threshold defaultTarget default state
      have hx : x ∈ state.remaining :=
        next_mem G H host part threshold defaultTarget default state hne
      have hax : a ≠ x := fun h => ha (h ▸ hx)
      have hfuel' : fuel ≤
          (step G H host part threshold momentExponent defaultTarget default
            state z).remaining.card := by
        simp only [step, stepAt]
        rw [Finset.card_erase_of_mem hx]
        omega
      rw [ih hfuel' (by simpa [step, stepAt, x, hax] using ha)]
      simp [step, stepAt, RandomGreedy.step, x, hax]

theorem costProduct_erase_of_mem (J remaining : Finset α) {x : α}
    (hxJ : x ∈ J) (hxrem : x ∈ remaining) (state : State α β) :
    costProduct J remaining state =
      state.core.costSeen x * costProduct J (remaining.erase x) state := by
  classical
  unfold costProduct
  have hfilter : J.filter (· ∈ remaining) =
      insert x (J.filter (· ∈ remaining.erase x)) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_erase]
    constructor
    · rintro ⟨hyJ, hyrem⟩
      by_cases hyx : y = x
      · exact Or.inl hyx
      · exact Or.inr ⟨hyJ, hyx, hyrem⟩
    · rintro (rfl | ⟨hyJ, hyx, hyrem⟩)
      · exact ⟨hxJ, hxrem⟩
      · exact ⟨hyJ, hyrem⟩
  rw [hfilter, Finset.prod_insert]
  simp

theorem costProduct_erase_of_not_mem (J remaining : Finset α) {x : α}
    (hxJ : x ∉ J) (state : State α β) :
    costProduct J remaining state = costProduct J (remaining.erase x) state := by
  classical
  unfold costProduct
  congr 1
  ext y
  simp only [Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨hyJ, hyrem⟩
    exact ⟨hyJ, fun hyx => hxJ (hyx ▸ hyJ), hyrem⟩
  · rintro ⟨hyJ, hyx, hyrem⟩
    exact ⟨hyJ, hyrem⟩

/-- The adaptive weighted average is the ordinary neutralized average with
the product of all newly inserted local costs. -/
theorem weightedAverage_eq_costProduct (I₁ I₂ : Finset α)
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : ι → ℕ)
    (momentExponent : ℕ) (defaultTarget : α) (default : β)
    {fuel : ℕ} (state : State α β) (hfuel : fuel = state.remaining.card)
    (payoff : State α β → ℝ) :
    AdaptiveProcess.weightedAverage
        (maskedChoices I₂ G H host part threshold defaultTarget default)
        (step G H host part threshold momentExponent defaultTarget default)
        (changeWeight I₁ I₂ G H host part threshold defaultTarget default)
        fuel state payoff =
      AdaptiveProcess.average
        (maskedChoices I₂ G H host part threshold defaultTarget default)
        (step G H host part threshold momentExponent defaultTarget default)
        fuel state
        (fun final => payoff final *
          costProduct (changeSet I₁ I₂) state.remaining final) := by
  induction fuel generalizing state with
  | zero =>
      have hempty : state.remaining = ∅ := Finset.card_eq_zero.mp hfuel.symm
      simp [costProduct, hempty]
  | succ fuel ih =>
      have hcardpos : 0 < state.remaining.card := by omega
      have hne : state.remaining.Nonempty := Finset.card_pos.mp hcardpos
      let x := next G H host part threshold defaultTarget default state
      have hx : x ∈ state.remaining :=
        next_mem G H host part threshold defaultTarget default state hne
      have hcard : fuel =
          (step G H host part threshold momentExponent defaultTarget default
            state (default : β)).remaining.card := by
        simp only [step, stepAt]
        rw [Finset.card_erase_of_mem hx]
        omega
      rw [AdaptiveProcess.weightedAverage_succ, AdaptiveProcess.average_succ]
      apply Finset.expect_congr rfl
      intro z hz
      have hcardz : fuel =
          (step G H host part threshold momentExponent defaultTarget default
            state z).remaining.card := by simpa [step, stepAt] using hcard
      rw [ih _ hcardz]
      have hremaining :
          (step G H host part threshold momentExponent defaultTarget default
            state z).remaining = state.remaining.erase x := rfl
      by_cases hxJ : x ∈ changeSet I₁ I₂
      · rw [changeWeight, if_pos (by simpa [x] using hxJ)]
        rw [← AdaptiveProcess.average_const_mul]
        apply AdaptiveProcess.average_congr
        intro final hrun
        have hcost : final.core.costSeen x =
            RandomGreedy.localCost G H host part default state.core x := by
          rw [stateRun_costSeen_eq_of_not_mem I₂ G H host part threshold
            momentExponent defaultTarget default hrun hcardz.le]
          · simp [step, stepAt, RandomGreedy.step, x]
          · simp [step, stepAt, x]
        rw [hremaining]
        rw [costProduct_erase_of_mem (changeSet I₁ I₂) state.remaining hxJ hx final]
        rw [hcost]
        ring
      · rw [changeWeight, if_neg (by simpa [x] using hxJ)]
        simp only [one_mul]
        apply AdaptiveProcess.average_congr
        intro final hrun
        rw [hremaining]
        rw [costProduct_erase_of_not_mem (changeSet I₁ I₂) state.remaining hxJ final]

theorem neutralAverage_le_costProduct {I₁ I₂ : Finset α} (hI : I₁ ⊆ I₂)
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (hhost : ∀ i, (host i).Nonempty)
    (part : α → ι) (threshold : ι → ℕ) (momentExponent : ℕ)
    (defaultTarget : α) (default : β) (payoff : State α β → ℝ)
    (hpayoff : ∀ state, 0 ≤ payoff state) :
    neutralAverage I₁ G H host part threshold momentExponent defaultTarget
        default payoff ≤
      neutralAverage I₂ G H host part threshold momentExponent defaultTarget
        default (fun final => payoff final *
          costProduct (changeSet I₁ I₂) Finset.univ final) := by
  refine (neutralAverage_le_weighted hI G H host hhost part threshold
    momentExponent defaultTarget default payoff hpayoff).trans_eq ?_
  have hcard : Fintype.card α =
      (initialState : State α β).remaining.card := by simp [initialState]
  simpa [neutralAverage, initialState] using
    weightedAverage_eq_costProduct I₁ I₂ G H host part threshold
      momentExponent defaultTarget default (initialState : State α β) hcard payoff

end AdaptiveGreedy
end Erdos163
