module
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
## Register some bound lemmas
-/

variable {α G₀ : Type*}

attribute [bound] norm_add_le mul_lt_of_lt_one_left Complex.normSq_nonneg norm_inner_le_norm
  Units.norm_pos Real.cosh_pos norm_sub_norm_le neg_le_self Finset.norm_prod_le Real.one_le_exp
  Real.toNNReal_le_toNNReal mul_le_of_le_one_left sub_le_self sub_lt_self Finset.prod_nonneg
  pow_le_of_le_one mul_lt_of_lt_one_right Real.lt_sqrt_of_sq_lt Real.le_sqrt_of_sq_le
  le_mul_of_one_le_left Real.sqrt_nonneg abs_norm_sub_norm_le

@[bound] public alias ⟨_, Bound.neg_pos⟩ := neg_pos

@[bound] public alias ⟨_, Bound.ennreal_coe_pos⟩ := ENNReal.coe_pos

@[bound] public alias ⟨_, Bound.sq_lt_one₀⟩ := sq_lt_one_iff₀

@[bound] public alias ⟨_, Bound.sq_le_one₀⟩ := sq_le_one_iff₀

-- These are declared as `private alias` in Mathlib, but they need to be public aliases
@[bound] public alias ⟨_, Bound.ofReal_pos_of_pos⟩ := ENNReal.ofReal_pos
@[bound] public alias ⟨_, Bound.one_lt_exp_of_pos⟩ := Real.one_lt_exp_iff

@[bound] public lemma Bound.lt_mul_of_one_lt_left [MulOneClass α] [Zero α] {a b : α} [Preorder α]
    [MulPosStrictMono α] [MulPosReflectLT α] (a0 : 0 < a) (b1 : 1 < b) : a < b * a :=
  (lt_mul_iff_one_lt_left a0).mpr b1

@[bound] public lemma Bound.one_le_div₀ [GroupWithZero G₀] [PartialOrder G₀] [MulPosReflectLT G₀]
    {a b : G₀} (hb : 0 < b) (ba : b ≤ a) : 1 ≤ a / b :=
  (_root_.one_le_div₀ hb).mpr ba

@[bound] public lemma Bound.nat_cast_le [AddMonoidWithOne α] [PartialOrder α] [AddLeftMono α]
    [ZeroLEOneClass α] [CharZero α] {m n : ℕ} (h : m ≤ n) : (m : α) ≤ n :=
  Nat.cast_le.mpr h

@[bound] public lemma Bound.one_le_rpow {x y : ℝ} (h : 1 ≤ x ∧ 0 ≤ y ∨ 0 < x ∧ x ≤ 1 ∧ y ≤ 0) :
    1 ≤ x ^ y := by
  rcases h with ⟨a,b⟩ | ⟨a,b,c⟩
  · exact Real.one_le_rpow a b
  · exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos a b c

@[bound] public lemma Bound.div_nonpos {x y : ℝ} (h : 0 ≤ x ∧ y ≤ 0 ∨ x ≤ 0 ∧ 0 ≤ y) :
    x / y ≤ 0 := by
  rcases h with ⟨a,b⟩ | ⟨a,b⟩
  · exact div_nonpos_of_nonneg_of_nonpos a b
  · exact div_nonpos_of_nonpos_of_nonneg a b

@[bound] public lemma Bound.div_neg {x y : ℝ} (h : 0 < x ∧ y < 0 ∨ x < 0 ∧ 0 < y) : x / y < 0 := by
  rcases h with ⟨a,b⟩ | ⟨a,b⟩
  · exact div_neg_of_pos_of_neg a b
  · exact div_neg_of_neg_of_pos a b

@[bound] public lemma Bound.add_pos {x y : ℝ} (h : 0 ≤ x ∧ 0 < y ∨ 0 < x ∧ 0 ≤ y) : 0 < x + y := by
  rcases h with ⟨a,b⟩ | ⟨a,b⟩
  · exact add_pos_of_nonneg_of_pos a b
  · exact add_pos_of_pos_of_nonneg a b

/-- Attribute for `destruct` rules for the `bound` tactic.

`@[bound_destruct]` is the same as `@[bound_forward]`, but removes the input in the process. -/
macro "bound_destruct" : attr =>
  `(attr|aesop safe destruct (rule_sets := [$(Lean.mkIdent `Bound):ident]))

-- Unpack membership in intervals
section Intervals
open Set
variable {α : Type} [Preorder α] {a b x : α}
@[bound_destruct] public alias ⟨Bound.mem_Icc, _⟩ := Set.mem_Icc
@[bound_destruct] public alias ⟨Bound.mem_Ico, _⟩ := Set.mem_Ico
@[bound_destruct] public alias ⟨Bound.mem_Ioc, _⟩ := Set.mem_Ioc
@[bound_destruct] public alias ⟨Bound.mem_Ioo, _⟩ := Set.mem_Ioo
@[bound_destruct] public alias ⟨Bound.mem_Ici, _⟩ := Set.mem_Ici
@[bound_destruct] public alias ⟨Bound.mem_Iic, _⟩ := Set.mem_Iic
@[bound_destruct] public alias ⟨Bound.mem_Iio, _⟩ := Set.mem_Iio
@[bound_destruct] public alias ⟨Bound.mem_Ioi, _⟩ := Set.mem_Ioi
end Intervals
