/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos163.Neutralization

/-!
# Propagation of defect moments

This file begins the quantitative half of Lee's random-greedy argument.  It
proves that every recorded likelihood cost is bounded by the corresponding
defect and packages the product estimate needed for neutralization.
-/

open scoped BigOperators
open Finset

namespace Erdos163
namespace RandomGreedy

universe u v w

variable {α : Type u} {β : Type v} {ι : Type w}
  [Fintype α] [DecidableEq α] [LinearOrder α]
  [Fintype β] [DecidableEq β] [DecidableEq ι]

structure CostBoundState (C : ℝ) (remaining : List α) (state : State α β) : Prop where
  cost_nonneg : ∀ x, x ∉ remaining → 0 ≤ state.costSeen x
  cost_le : ∀ x, x ∉ remaining →
    state.costSeen x ≤ C * max 1 (state.defectSeen x)

theorem costBoundState_initial (C : ℝ) (remaining : List α)
    (hcover : ∀ x, x ∈ remaining) :
    CostBoundState C remaining (initialState : State α β) := by
  constructor <;> intro x hx
  · exact (hx (hcover x)).elim
  · exact (hx (hcover x)).elim

theorem costBoundState_step
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : α → ℕ)
    (momentExponent : ℕ) (default : β) {γ : ℝ} (hγ : 1 ≤ γ)
    (hsize : ∀ x, ((host (part x)).card : ℝ) ≤ γ * threshold x)
    {x : α} {xs : List α} {state : State α β} (z : β)
    (hxs : x ∉ xs)
    (hstate : CostBoundState (2 * γ) (x :: xs) state) :
    CostBoundState (2 * γ) xs
      (step G H host part threshold momentExponent default x state z) := by
  constructor
  · intro y hy
    by_cases hyx : y = x
    · subst y
      simpa [step] using localCost_nonneg G H host part default state x
    · simpa [step, hyx] using hstate.cost_nonneg y (by simp [hyx, hy])
  · intro y hy
    by_cases hyx : y = x
    · subst y
      simpa [step] using localCost_le_defect G H host part threshold default state x
        hγ (hsize x)
    · simpa [step, hyx] using hstate.cost_le y (by simp [hyx, hy])

theorem stateRun_costBound_final (I : Finset α)
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : α → ℕ)
    (momentExponent : ℕ) (default : β) {γ : ℝ} (hγ : 1 ≤ γ)
    (hsize : ∀ x, ((host (part x)).card : ℝ) ≤ γ * threshold x)
    {remaining : List α} {state final : State α β}
    (hrun : Process.StateRun
      (maskedChoices I G H host part default)
      (step G H host part threshold momentExponent default)
      remaining state final)
    (hnodup : remaining.Nodup)
    (hstate : CostBoundState (2 * γ) remaining state) :
    CostBoundState (2 * γ) [] final := by
  induction hrun with
  | nil state => simpa using hstate
  | @cons x xs state final z hz hrest ih =>
      exact ih (List.nodup_cons.mp hnodup).2
        (costBoundState_step G H host part threshold momentExponent default hγ hsize z
          (List.nodup_cons.mp hnodup).1 hstate)

theorem final_cost_bounds (I : Finset α)
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : α → ℕ)
    (momentExponent : ℕ) (default : β) {γ : ℝ} (hγ : 1 ≤ γ)
    (hsize : ∀ x, ((host (part x)).card : ℝ) ≤ γ * threshold x)
    {final : State α β}
    (hrun : Process.StateRun
      (maskedChoices I G H host part default)
      (step G H host part threshold momentExponent default)
      order (initialState : State α β) final) :
    ∀ x, 0 ≤ final.costSeen x ∧
      final.costSeen x ≤ (2 * γ) * max 1 (final.defectSeen x) := by
  have hfinal := stateRun_costBound_final I G H host part threshold momentExponent default
    hγ hsize hrun order_nodup
    (costBoundState_initial (α := α) (β := β) (2 * γ) order order_mem)
  intro x
  exact ⟨hfinal.cost_nonneg x (by simp), hfinal.cost_le x (by simp)⟩

theorem costProduct_order_le (I J : Finset α)
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : α → ℕ)
    (momentExponent : ℕ) (default : β) {γ : ℝ} (hγ : 1 ≤ γ)
    (hsize : ∀ x, ((host (part x)).card : ℝ) ≤ γ * threshold x)
    {final : State α β}
    (hrun : Process.StateRun
      (maskedChoices I G H host part default)
      (step G H host part threshold momentExponent default)
      order (initialState : State α β) final) :
    costProduct J order final ≤
      (2 * γ) ^ J.card * ∏ x ∈ J, max 1 (final.defectSeen x) := by
  have hb := final_cost_bounds I G H host part threshold momentExponent default
    hγ hsize hrun
  have hfilter : J.filter (fun x => x ∈ (order : List α)) = J := by
    ext x
    simp [order_mem]
  rw [costProduct, hfilter]
  calc
    (∏ x ∈ J, final.costSeen x) ≤
        ∏ x ∈ J, ((2 * γ) * max 1 (final.defectSeen x)) := by
      apply Finset.prod_le_prod
      · intro x hx
        exact (hb x).1
      · intro x hx
        exact (hb x).2
    _ = (2 * γ) ^ J.card * ∏ x ∈ J, max 1 (final.defectSeen x) := by
      rw [Finset.prod_mul_distrib]
      simp

/-! ## Relations between the two recorded defect fields -/

structure RecordedDefects (momentExponent : ℕ) (remaining : List α)
    (state : State α β) : Prop where
  recorded : ∀ x, x ∉ remaining →
    state.observed x =
      if state.defectSeen x = 0 then 0 else state.defectSeen x ^ momentExponent
  defect_zero_or_one_le : ∀ x, x ∉ remaining →
    state.defectSeen x = 0 ∨ 1 ≤ state.defectSeen x

theorem recordedDefects_initial (momentExponent : ℕ) (remaining : List α)
    (hcover : ∀ x, x ∈ remaining) :
    RecordedDefects momentExponent remaining (initialState : State α β) := by
  constructor <;> intro x hx
  · exact (hx (hcover x)).elim
  · exact (hx (hcover x)).elim

theorem recordedDefects_step
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : α → ℕ)
    (momentExponent : ℕ) (default : β)
    {x : α} {xs : List α} {state : State α β} (z : β)
    (hstate : RecordedDefects momentExponent (x :: xs) state) :
    RecordedDefects momentExponent xs
      (step G H host part threshold momentExponent default x state z) := by
  constructor
  · intro y hy
    by_cases hyx : y = x
    · subst y
      simp [step, FiniteDefect.defectPower]
    · simpa [step, hyx] using hstate.recorded y (by simp [hyx, hy])
  · intro y hy
    by_cases hyx : y = x
    · subst y
      simp only [step, Function.update_self]
      by_cases hz : FiniteDefect.defect G (threshold x)
          (fun y : forwardNeighbors H x => value default state y) (host (part x)) = 0
      · exact Or.inl hz
      · exact Or.inr (FiniteDefect.one_le_defect_of_ne_zero G hz)
    · simpa [step, hyx] using hstate.defect_zero_or_one_le y (by simp [hyx, hy])

theorem stateRun_recordedDefects_final (I : Finset α)
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : α → ℕ)
    (momentExponent : ℕ) (default : β)
    {remaining : List α} {state final : State α β}
    (hrun : Process.StateRun
      (maskedChoices I G H host part default)
      (step G H host part threshold momentExponent default)
      remaining state final)
    (hstate : RecordedDefects momentExponent remaining state) :
    RecordedDefects momentExponent [] final := by
  induction hrun with
  | nil state => simpa using hstate
  | @cons x xs state final z hz hrest ih =>
      exact ih (recordedDefects_step G H host part threshold momentExponent default z hstate)

theorem final_recordedDefects (I : Finset α)
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : α → ℕ)
    (momentExponent : ℕ) (default : β)
    {final : State α β}
    (hrun : Process.StateRun
      (maskedChoices I G H host part default)
      (step G H host part threshold momentExponent default)
      order (initialState : State α β) final) :
    ∀ x, final.observed x =
      if final.defectSeen x = 0 then 0 else
        final.defectSeen x ^ momentExponent := by
  have hfinal := stateRun_recordedDefects_final I G H host part threshold
    momentExponent default hrun (recordedDefects_initial momentExponent order order_mem)
  intro x
  exact hfinal.recorded x (by simp)

theorem final_defect_zero_or_one_le (I : Finset α)
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : α → ℕ)
    (momentExponent : ℕ) (default : β)
    {final : State α β}
    (hrun : Process.StateRun
      (maskedChoices I G H host part default)
      (step G H host part threshold momentExponent default)
      order (initialState : State α β) final) (x : α) :
    final.defectSeen x = 0 ∨ 1 ≤ final.defectSeen x := by
  have hfinal := stateRun_recordedDefects_final I G H host part threshold
    momentExponent default hrun (recordedDefects_initial momentExponent order order_mem)
  exact hfinal.defect_zero_or_one_le x (by simp)

theorem final_observed_nonneg (I : Finset α)
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : α → ℕ)
    (momentExponent : ℕ) (default : β)
    {final : State α β}
    (hrun : Process.StateRun
      (maskedChoices I G H host part default)
      (step G H host part threshold momentExponent default)
      order (initialState : State α β) final) (x : α) :
    0 ≤ final.observed x := by
  rw [final_recordedDefects I G H host part threshold momentExponent default hrun x]
  split_ifs with hz
  · exact le_rfl
  · exact pow_nonneg ((final_defect_zero_or_one_le I G H host part threshold
      momentExponent default hrun x).resolve_left hz |>.trans' zero_le_one) _

theorem final_observed_zero_or_one_le (I : Finset α)
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : α → ℕ)
    (momentExponent : ℕ) (default : β)
    {final : State α β}
    (hrun : Process.StateRun
      (maskedChoices I G H host part default)
      (step G H host part threshold momentExponent default)
      order (initialState : State α β) final) (x : α) :
    final.observed x = 0 ∨ 1 ≤ final.observed x := by
  rw [final_recordedDefects I G H host part threshold momentExponent default hrun x]
  by_cases hz : final.defectSeen x = 0
  · simp [hz]
  · rw [if_neg hz]
    right
    simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1)
      ((final_defect_zero_or_one_le I G H host part threshold momentExponent default
        hrun x).resolve_left hz) momentExponent

theorem final_defect_pow_le_observed (I : Finset α)
    (G : SimpleGraph β) [DecidableRel G.Adj]
    (H : SimpleGraph α) [DecidableRel H.Adj]
    (host : ι → Finset β) (part : α → ι) (threshold : α → ℕ)
    (momentExponent : ℕ) (default : β)
    {final : State α β}
    (hrun : Process.StateRun
      (maskedChoices I G H host part default)
      (step G H host part threshold momentExponent default)
      order (initialState : State α β) final)
    {t : ℕ} (ht : 0 < t) (hts : t ≤ momentExponent) (x : α) :
    final.defectSeen x ^ t ≤ final.observed x := by
  rw [final_recordedDefects I G H host part threshold momentExponent default hrun x]
  by_cases hz : final.defectSeen x = 0
  · simp [hz, Nat.ne_of_gt ht]
  · rw [if_neg hz]
    exact pow_le_pow_right₀
      ((final_defect_zero_or_one_le I G H host part threshold momentExponent default
        hrun x).resolve_left hz) hts

/-- A product of `q` nonnegative factors is controlled by the largest
`2q`-th power, hence by the sum of all such powers. -/
theorem prod_sq_le_sum_pow_card {κ : Type*} [DecidableEq κ]
    {J : Finset κ} (hJ : J.Nonempty) (a : κ → ℝ)
    (ha : ∀ x ∈ J, 0 ≤ a x) :
    (∏ x ∈ J, a x) ^ 2 ≤ ∑ x ∈ J, a x ^ (2 * J.card) := by
  let M := J.sup' hJ a
  have hM0 : 0 ≤ M := by
    obtain ⟨x, hx⟩ := hJ
    exact (ha x hx).trans (Finset.le_sup' a hx)
  have hprod : (∏ x ∈ J, a x) ≤ M ^ J.card := by
    calc
      (∏ x ∈ J, a x) ≤ ∏ _x ∈ J, M := by
        apply Finset.prod_le_prod
        · exact ha
        · intro x hx
          exact Finset.le_sup' a hx
      _ = M ^ J.card := by simp
  obtain ⟨x, hx, hMx⟩ := Finset.exists_mem_eq_sup' hJ a
  have hterm : a x ^ (2 * J.card) ≤ ∑ y ∈ J, a y ^ (2 * J.card) := by
    exact Finset.single_le_sum (fun y hy => pow_nonneg (ha y hy) _) hx
  calc
    (∏ x ∈ J, a x) ^ 2 ≤ (M ^ J.card) ^ 2 :=
      pow_le_pow_left₀ (Finset.prod_nonneg ha) hprod 2
    _ = M ^ (2 * J.card) := by rw [← pow_mul]; congr 1; omega
    _ = a x ^ (2 * J.card) := by rw [← hMx]
    _ ≤ ∑ y ∈ J, a y ^ (2 * J.card) := hterm

/-- Scaled Young inequality used at a branching vertex of the propagation
tree.  The factor `J.card` makes the total coefficient of all children at
most one half. -/
theorem two_mul_product_le_scaled_sum {κ : Type*} [DecidableEq κ]
    {J : Finset κ} (hJ : J.Nonempty) (a : κ → ℝ)
    (ha : ∀ x ∈ J, 0 ≤ a x) (C X : ℝ) :
    2 * (C ^ J.card * X * ∏ x ∈ J, a x) ≤
      (((J.card : ℝ) * C ^ J.card * X) ^ 2) +
        (∑ x ∈ J, a x ^ (2 * J.card)) / (J.card : ℝ) ^ 2 := by
  have hcard : (0 : ℝ) < J.card := by
    exact_mod_cast hJ.card_pos
  have hprod := prod_sq_le_sum_pow_card hJ a ha
  have hdiv :
      ((∏ x ∈ J, a x) / (J.card : ℝ)) ^ 2 ≤
        (∑ x ∈ J, a x ^ (2 * J.card)) / (J.card : ℝ) ^ 2 := by
    rw [div_pow]
    exact div_le_div_of_nonneg_right hprod (sq_nonneg (J.card : ℝ))
  calc
    2 * (C ^ J.card * X * ∏ x ∈ J, a x) =
        2 * ((J.card : ℝ) * C ^ J.card * X) *
          ((∏ x ∈ J, a x) / (J.card : ℝ)) := by
            field_simp
            <;> ring
    _ ≤ (((J.card : ℝ) * C ^ J.card * X) ^ 2) +
        ((∏ x ∈ J, a x) / (J.card : ℝ)) ^ 2 :=
      two_mul_le_add_sq _ _
    _ ≤ (((J.card : ℝ) * C ^ J.card * X) ^ 2) +
        (∑ x ∈ J, a x ^ (2 * J.card)) / (J.card : ℝ) ^ 2 :=
      add_le_add_right hdiv _

theorem max_pow_le_sq_add {X d Y : ℝ} {q : ℕ}
    (hX : 1 ≤ X) (hpow : d ^ (2 * q) ≤ Y) :
    (max 1 d) ^ (2 * q) ≤ X ^ 2 + Y := by
  by_cases hd : d ≤ 1
  · rw [max_eq_left hd]
    have hsq : (1 : ℝ) ≤ X ^ 2 := by
      simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hX 2
    have hdpow : 0 ≤ d ^ (2 * q) := by
      rw [show 2 * q = q * 2 by omega, pow_mul]
      exact sq_nonneg _
    simpa using hsq.trans (le_add_of_nonneg_right (hdpow.trans hpow))
  · rw [max_eq_right (le_of_not_ge hd)]
    exact hpow.trans (le_add_of_nonneg_left (sq_nonneg X))

/-- Pointwise branching estimate.  A zero root contributes nothing.  For a
nonzero root observation, its being at least one absorbs the `max 1` terms;
the scaled Young inequality leaves total child coefficient at most `1/2`. -/
theorem root_mul_product_le_root_sq_add_children {κ : Type*} [DecidableEq κ]
    {J : Finset κ} (hJ : J.Nonempty) (a Y : κ → ℝ) (C X : ℝ)
    (hX : X = 0 ∨ 1 ≤ X) (hY : ∀ y ∈ J, 0 ≤ Y y)
    (hpow : ∀ y ∈ J, a y ^ (2 * J.card) ≤ Y y) :
    C ^ J.card * X * ∏ y ∈ J, max 1 (a y) ≤
      ((((J.card : ℝ) * C ^ J.card) ^ 2 + 1) / 2) * X ^ 2 +
        (∑ y ∈ J, Y y) / (2 * (J.card : ℝ) ^ 2) := by
  rcases hX with rfl | hX
  · simp only [mul_zero, zero_mul, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    simpa only [zero_add] using
      (div_nonneg (Finset.sum_nonneg hY)
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg (J.card : ℝ))))
  have hcard : (0 : ℝ) < J.card := by exact_mod_cast hJ.card_pos
  have honecard : (1 : ℝ) ≤ J.card := by exact_mod_cast hJ.card_pos
  have hsum :
      (∑ y ∈ J, (max 1 (a y)) ^ (2 * J.card)) ≤
        (J.card : ℝ) * X ^ 2 + ∑ y ∈ J, Y y := by
    calc
      (∑ y ∈ J, (max 1 (a y)) ^ (2 * J.card)) ≤
          ∑ y ∈ J, (X ^ 2 + Y y) := by
            exact Finset.sum_le_sum fun y hy => max_pow_le_sq_add hX (hpow y hy)
      _ = (J.card : ℝ) * X ^ 2 + ∑ y ∈ J, Y y := by
        rw [Finset.sum_add_distrib]
        simp
  have hqratio :
      ((J.card : ℝ) * X ^ 2) / (J.card : ℝ) ^ 2 ≤ X ^ 2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hcard)).2
    have hXsq : 0 ≤ X ^ 2 := sq_nonneg X
    have hq_sq : (J.card : ℝ) ≤ (J.card : ℝ) ^ 2 := by nlinarith
    calc
      (J.card : ℝ) * X ^ 2 ≤ (J.card : ℝ) ^ 2 * X ^ 2 :=
        mul_le_mul_of_nonneg_right hq_sq hXsq
      _ = X ^ 2 * (J.card : ℝ) ^ 2 := by ring
  have hdiv :
      (∑ y ∈ J, (max 1 (a y)) ^ (2 * J.card)) / (J.card : ℝ) ^ 2 ≤
        X ^ 2 + (∑ y ∈ J, Y y) / (J.card : ℝ) ^ 2 := by
    calc
      _ ≤ ((J.card : ℝ) * X ^ 2 + ∑ y ∈ J, Y y) /
          (J.card : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hsum (sq_nonneg _)
      _ = ((J.card : ℝ) * X ^ 2) / (J.card : ℝ) ^ 2 +
          (∑ y ∈ J, Y y) / (J.card : ℝ) ^ 2 := by ring
      _ ≤ X ^ 2 + (∑ y ∈ J, Y y) / (J.card : ℝ) ^ 2 :=
        add_le_add hqratio le_rfl
  have hyoung := two_mul_product_le_scaled_sum hJ (fun y => max 1 (a y))
    (fun y hy => (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left 1 (a y))) C X
  have htwo :
      2 * (C ^ J.card * X * ∏ y ∈ J, max 1 (a y)) ≤
        (((J.card : ℝ) * C ^ J.card * X) ^ 2) + X ^ 2 +
          (∑ y ∈ J, Y y) / (J.card : ℝ) ^ 2 := by
    calc
      _ ≤ (((J.card : ℝ) * C ^ J.card * X) ^ 2) +
          (∑ y ∈ J, (max 1 (a y)) ^ (2 * J.card)) /
            (J.card : ℝ) ^ 2 := hyoung
      _ ≤ (((J.card : ℝ) * C ^ J.card * X) ^ 2) +
          (X ^ 2 + (∑ y ∈ J, Y y) / (J.card : ℝ) ^ 2) :=
        calc
          _ = (∑ y ∈ J, (max 1 (a y)) ^ (2 * J.card)) /
                (J.card : ℝ) ^ 2 +
              (((J.card : ℝ) * C ^ J.card * X) ^ 2) := add_comm _ _
          _ ≤ (X ^ 2 + (∑ y ∈ J, Y y) / (J.card : ℝ) ^ 2) +
              (((J.card : ℝ) * C ^ J.card * X) ^ 2) :=
            add_le_add_left hdiv _
          _ = (((J.card : ℝ) * C ^ J.card * X) ^ 2) +
              (X ^ 2 + (∑ y ∈ J, Y y) / (J.card : ℝ) ^ 2) := add_comm _ _
      _ = (((J.card : ℝ) * C ^ J.card * X) ^ 2) + X ^ 2 +
          (∑ y ∈ J, Y y) / (J.card : ℝ) ^ 2 := by ring
  have heq :
      ((((J.card : ℝ) * C ^ J.card * X) ^ 2) + X ^ 2 +
          (∑ y ∈ J, Y y) / (J.card : ℝ) ^ 2) =
        2 * (((((J.card : ℝ) * C ^ J.card) ^ 2 + 1) / 2) * X ^ 2 +
          (∑ y ∈ J, Y y) / (2 * (J.card : ℝ) ^ 2)) := by
    field_simp
    <;> ring
  rw [heq] at htwo
  linarith

end RandomGreedy
end Erdos163
