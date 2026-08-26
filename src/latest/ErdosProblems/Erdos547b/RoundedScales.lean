/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Claim617
import ErdosProblems.Erdos547b.Claim618

/-!
# Integral scales for Zhao's Claims 6.17 and 6.18

The reduced-graph arguments use natural thresholds, whereas their published
conclusions use real parameters.  These definitions make the rounding choice
literal.  Downward-rounded scales feed the two real-bound wrappers; upward
rounding is available for hypotheses which need an integral upper bound.  The
error in either direction is strictly less than one.
-/

noncomputable section

namespace Erdos547b.ZhaoRoundedScales

/-- The natural scale obtained by rounding a nonnegative real target down. -/
def lowerScale (x : ℝ) : ℕ := ⌊x⌋₊

/-- The natural scale obtained by rounding a real target up. -/
def upperScale (x : ℝ) : ℕ := ⌈x⌉₊

theorem lowerScale_cast_le {x : ℝ} (hx : 0 ≤ x) :
    (lowerScale x : ℝ) ≤ x := by
  exact Nat.floor_le hx

theorem lt_lowerScale_cast_add_one (x : ℝ) :
    x < (lowerScale x : ℝ) + 1 := by
  exact Nat.lt_floor_add_one x

theorem le_upperScale_cast (x : ℝ) :
    x ≤ (upperScale x : ℝ) := by
  exact Nat.le_ceil x

theorem upperScale_cast_lt_add_one {x : ℝ} (hx : 0 ≤ x) :
    (upperScale x : ℝ) < x + 1 := by
  exact Nat.ceil_lt_add_one hx

theorem lowerScale_pos {x : ℝ} (hx : 1 ≤ x) : 0 < lowerScale x := by
  have hx' : ((1 : ℕ) : ℝ) ≤ x := by norm_num at hx ⊢; exact hx
  have : 1 ≤ lowerScale x := Nat.le_floor hx'
  omega

/-- Summing downward-rounded real capacities loses at most one unit per
finite index. -/
theorem sum_le_cast_sum_lowerScale_add_card
    {α : Type*} [DecidableEq α]
    (s : Finset α) (x : α → ℝ) :
    ∑ a ∈ s, x a ≤
      (((∑ a ∈ s, lowerScale (x a)) + s.card : ℕ) : ℝ) := by
  push_cast
  calc
    ∑ a ∈ s, x a ≤
        ∑ a ∈ s, (((lowerScale (x a) : ℕ) : ℝ) + 1) := by
      apply Finset.sum_le_sum
      intro a ha
      exact (lt_lowerScale_cast_add_one (x a)).le
    _ = (∑ a ∈ s, ((lowerScale (x a) : ℕ) : ℝ)) +
          ∑ _a ∈ s, (1 : ℝ) := by
      rw [Finset.sum_add_distrib]
    _ = _ := by simp

/-- A real aggregate budget with one extra unit per bin implies the natural
capacity-packing budget for the downward-rounded capacities. -/
theorem demand_add_slack_le_sum_lowerScale
    {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℝ) (demand slack : ℕ)
    (hbudget : ((demand + Fintype.card α * slack +
        Fintype.card α : ℕ) : ℝ) ≤ ∑ a, x a) :
    demand + Fintype.card α * slack ≤ ∑ a, lowerScale (x a) := by
  have hround := sum_le_cast_sum_lowerScale_add_card
    (Finset.univ : Finset α) x
  simp only [Finset.card_univ] at hround
  have hreal :
      ((demand + Fintype.card α * slack : ℕ) : ℝ) ≤
        ((∑ a, lowerScale (x a) : ℕ) : ℝ) := by
    push_cast at hbudget hround ⊢
    linarith
  exact_mod_cast hreal

/-- The integer `r` used in Claim 6.17. -/
def claim617R (rho : ℝ) (k : ℕ) : ℕ :=
  lowerScale (rho * k)

/-- The integer `a` used to prune high-degree vertices in Claim 6.18. -/
def claim618A (rho₁ : ℝ) (k : ℕ) : ℕ :=
  lowerScale (8 * rho₁ * k)

theorem claim617R_cast_le {rho : ℝ} (hrho : 0 ≤ rho) (k : ℕ) :
    (claim617R rho k : ℝ) ≤ rho * k := by
  apply lowerScale_cast_le
  positivity

theorem claim617R_additive_slack (rho : ℝ) (k : ℕ) :
    rho * k < (claim617R rho k : ℝ) + 1 := by
  exact lt_lowerScale_cast_add_one _

theorem claim618A_cast_le {rho₁ : ℝ} (hrho₁ : 0 ≤ rho₁) (k : ℕ) :
    (claim618A rho₁ k : ℝ) ≤ 8 * rho₁ * k := by
  apply lowerScale_cast_le
  positivity

theorem claim618A_additive_slack (rho₁ : ℝ) (k : ℕ) :
    8 * rho₁ * k < (claim618A rho₁ k : ℝ) + 1 := by
  exact lt_lowerScale_cast_add_one _

theorem claim617R_pos {rho : ℝ} {k : ℕ}
    (hlarge : 1 ≤ rho * k) : 0 < claim617R rho k :=
  lowerScale_pos hlarge

theorem claim618A_pos {rho₁ : ℝ} {k : ℕ}
    (hlarge : 1 ≤ 8 * rho₁ * k) : 0 < claim618A rho₁ k :=
  lowerScale_pos hlarge

/-- A convenient upward-rounded auxiliary scale, with its explicit unit
additive loss. -/
def roundedUpperProduct (c rho : ℝ) (k : ℕ) : ℕ :=
  upperScale (c * rho * k)

theorem target_le_roundedUpperProduct (c rho : ℝ) (k : ℕ) :
    c * rho * k ≤ (roundedUpperProduct c rho k : ℝ) := by
  exact le_upperScale_cast _

theorem roundedUpperProduct_lt_target_add_one
    {c rho : ℝ} (hc : 0 ≤ c) (hrho : 0 ≤ rho) (k : ℕ) :
    (roundedUpperProduct c rho k : ℝ) < c * rho * k + 1 := by
  apply upperScale_cast_lt_add_one
  positivity

#print axioms lowerScale_cast_le
#print axioms sum_le_cast_sum_lowerScale_add_card
#print axioms demand_add_slack_le_sum_lowerScale
#print axioms claim617R_cast_le
#print axioms claim618A_cast_le
#print axioms roundedUpperProduct_lt_target_add_one

end Erdos547b.ZhaoRoundedScales
