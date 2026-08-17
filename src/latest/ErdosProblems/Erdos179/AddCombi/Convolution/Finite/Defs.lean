/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import ErdosProblems.Erdos179.AddCombi.Mathlib.Algebra.Notation.Indicator
public import ErdosProblems.Erdos179.AddCombi.Mathlib.Combinatorics.Additive.Energy
public import Mathlib.Algebra.Group.Action.Pointwise.Finset
public import Mathlib.Algebra.Group.Translate
public import Mathlib.Algebra.Star.Conjneg
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Data.Complex.Basic
public import Mathlib.Data.NNReal.Star

import ErdosProblems.Erdos179.AddCombi.Mathlib.Algebra.GroupWithZero.Indicator
import ErdosProblems.Erdos179.AddCombi.Mathlib.Algebra.Star.Pi
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Group.Pointwise.Finset.Density
import Mathlib.Analysis.Complex.Basic

/-!
# Convolution in the compact normalisation

This file defines several versions of the discrete convolution of functions with the compact
normalisation.

## Main declarations

* `conv`: Discrete convolution of two functions in the compact normalisation
* `dconv`: Discrete difference convolution of two functions in the compact normalisation
* `iterConv`: Iterated convolution of a function in the compact normalisation

## Notation

* `f ∗ g`: Convolution
* `f ○ g`: Difference convolution
* `f ∗^ n`: Iterated convolution

## Notes

Some lemmas could technically be generalised to a division ring. Doesn't seem very useful given that
the codomain in applications is either `ℝ`, `ℝ≥0` or `ℂ`.

Similarly we could drop the commutativity assumption on the domain, but this is unneeded at this
point in time.
-/

public section

open Finset Fintype Function
open scoped BigOperators ComplexConjugate NNReal Pointwise translate Indicator
  Combinatorics.Additive'

local notation a " /ℚ " q => (q : ℚ≥0)⁻¹ • a

variable {G H K L : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]

section Semifield
variable [Semifield K] [CharZero K] {f g : G → K}

/-- Compact convolution on a finite group.

The value of `f ∗ g` at `a` is the average of the value of `f b * g c` over `b + c = a`. -/
@[expose] def conv (f g : G → K) : G → K := fun a ↦ 𝔼 x : G × G with x.1 + x.2 = a, f x.1 * g x.2

@[inherit_doc] infixl:71 " ∗ " => conv

lemma conv_apply (f g : G → K) (a : G) :
    (f ∗ g) a = 𝔼 x : G × G with x.1 + x.2 = a, f x.1 * g x.2 := rfl

lemma conv_eq_smul_sum (f g : G → K) (a : G) :
    (f ∗ g) a = (∑ x : G × G with x.1 + x.2 = a, f x.1 * g x.2) /ℚ Fintype.card G := by
  simp [conv_apply, expect, ← univ_product_univ, card_add_eq]

@[simp] lemma conv_zero (f : G → K) : f ∗ 0 = 0 := by ext; simp [conv_apply]
@[simp] lemma zero_conv (f : G → K) : 0 ∗ f = 0 := by ext; simp [conv_apply]

lemma conv_add (f g h : G → K) : f ∗ (g + h) = f ∗ g + f ∗ h := by
  ext; simp [conv_apply, mul_add, expect_add_distrib]

lemma add_conv (f g h : G → K) : (f + g) ∗ h = f ∗ h + g ∗ h := by
  ext; simp [conv_apply, add_mul, expect_add_distrib]

lemma smul_conv [DistribSMul H K] [IsScalarTower H K K] [SMulCommClass H K K] (c : H)
    (f g : G → K) : c • f ∗ g = c • (f ∗ g) := by
  have := SMulCommClass.symm H K K
  ext a
  simp only [Pi.smul_apply, smul_expect, conv_apply, smul_mul_assoc]

lemma conv_smul [DistribSMul H K] [SMulCommClass H K K] (c : H)
    (f g : G → K) : f ∗ c • g = c • (f ∗ g) := by
  have := SMulCommClass.symm H K K
  ext a
  simp only [Pi.smul_apply, smul_expect, conv_apply, mul_smul_comm]

alias smul_conv_assoc := smul_conv
alias smul_conv_left_comm := conv_smul

@[simp] lemma translate_conv (a : G) (f g : G → K) : τ a f ∗ g = τ a (f ∗ g) :=
  funext fun b ↦ expect_equiv ((Equiv.subRight a).prodCongr <| Equiv.refl _)
    (by simp [sub_add_eq_add_sub]) (by simp)

@[simp] lemma conv_translate (a : G) (f g : G → K) : f ∗ τ a g = τ a (f ∗ g) :=
  funext fun b ↦ expect_equiv ((Equiv.refl _).prodCongr <| Equiv.subRight a)
    (by simp [← add_sub_assoc]) (by simp)

lemma conv_comm (f g : G → K) : f ∗ g = g ∗ f :=
  funext fun a ↦ Finset.expect_equiv (Equiv.prodComm _ _) (by simp [add_comm]) (by simp [mul_comm])

lemma mul_smul_conv_comm [Monoid H] [DistribMulAction H K] [IsScalarTower H K K]
    [SMulCommClass H K K] (c d : H) (f g : G → K) : (c * d) • (f ∗ g) = c • f ∗ d • g := by
  rw [smul_conv, conv_smul, mul_smul]

lemma conv_assoc (f g h : G → K) : f ∗ g ∗ h = f ∗ (g ∗ h) := by
  ext a
  simp only [conv_eq_smul_sum, mul_smul_comm, smul_mul_assoc, ← smul_sum, sum_mul, mul_sum,
    Finset.sum_sigma']
  congr! 2
  apply sum_nbij' (fun ⟨(_b, c), (d, e)⟩ ↦ ⟨(d, e + c), (e, c)⟩)
    (fun ⟨(b, _c), (d, e)⟩ ↦ ⟨(b + d, e), (b, d)⟩) <;> grind

lemma conv_right_comm (f g h : G → K) : f ∗ g ∗ h = f ∗ h ∗ g := by
  rw [conv_assoc, conv_assoc, conv_comm g]

lemma conv_left_comm (f g h : G → K) : f ∗ (g ∗ h) = g ∗ (f ∗ h) := by
  rw [← conv_assoc, ← conv_assoc, conv_comm g]

lemma conv_conv_conv_comm (f g h i : G → K) : f ∗ g ∗ (h ∗ i) = f ∗ h ∗ (g ∗ i) := by
  rw [conv_assoc, conv_assoc, conv_left_comm g]

lemma map_conv [Semifield L] [CharZero L] (m : K →+* L) (f g : G → K) (a : G) : m
    ((f ∗ g) a) = (m ∘ f ∗ m ∘ g) a := by
  simp_rw [conv_apply, map_expect, map_mul, Function.comp_apply]

lemma comp_conv [Semifield L] [CharZero L] (m : K →+* L) (f g : G → K) :
    m ∘ (f ∗ g) = m ∘ f ∗ m ∘ g := funext <| map_conv _ _ _

lemma conv_eq_expect_sub (f g : G → K) (a : G) : (f ∗ g) a = 𝔼 t, f (a - t) * g t := by
  rw [conv_apply]
  refine expect_nbij (fun x ↦ x.2) (fun x _ ↦ mem_univ _) ?_ ?_ fun b _ ↦
    ⟨(a - b, b), mem_filter.2 ⟨mem_univ _, sub_add_cancel _ _⟩, rfl⟩
  any_goals unfold Set.InjOn
  all_goals aesop

lemma conv_eq_expect_add (f g : G → K) (a : G) : (f ∗ g) a = 𝔼 t, f (a + t) * g (-t) :=
  (conv_eq_expect_sub _ _ _).trans <| Fintype.expect_equiv (Equiv.neg _) _ _ fun t ↦ by
    simp only [sub_eq_add_neg, Equiv.neg_apply, neg_neg]

lemma conv_eq_expect_sub' (f g : G → K) (a : G) : (f ∗ g) a = 𝔼 t, f t * g (a - t) := by
  rw [conv_comm, conv_eq_expect_sub]; grind

lemma conv_eq_expect_add' (f g : G → K) (a : G) : (f ∗ g) a = 𝔼 t, f (-t) * g (a + t) := by
  rw [conv_comm, conv_eq_expect_add]; grind

lemma conv_apply_add (f g : G → K) (a b : G) : (f ∗ g) (a + b) = 𝔼 t, f (a + t) * g (b - t) :=
  (conv_eq_expect_sub _ _ _).trans <| Fintype.expect_equiv (Equiv.subLeft b) _ _ fun t ↦ by
    simp [add_sub_assoc]

lemma expect_conv_mul (f g h : G → K) :
    𝔼 a, (f ∗ g) a * h a = 𝔼 a, 𝔼 b, f a * g b * h (a + b) := by
  simp_rw [conv_eq_expect_sub', expect_mul]
  rw [expect_comm]
  exact expect_congr rfl fun x _ ↦ Fintype.expect_equiv (Equiv.subRight x) _ _ fun y ↦ by simp

lemma expect_conv (f g : G → K) : 𝔼 a, (f ∗ g) a = (𝔼 a, f a) * 𝔼 a, g a := by
  simpa only [Fintype.expect_mul_expect, Pi.one_apply, mul_one] using expect_conv_mul f g 1

@[simp] lemma conv_const (f : G → K) (b : K) : f ∗ const _ b = const _ ((𝔼 x, f x) * b) := by
  ext; simp [conv_eq_expect_sub', expect_mul]

@[simp] lemma const_conv (b : K) (f : G → K) : const _ b ∗ f = const _ (b * 𝔼 x, f x) := by
  ext; simp [conv_eq_expect_sub, mul_expect]

lemma support_conv_subset (f g : G → K) : support (f ∗ g) ⊆ support f + support g := by
  rintro a ha
  obtain ⟨x, hx, h⟩ := exists_ne_zero_of_expect_ne_zero ha
  exact ⟨_, left_ne_zero_of_mul h, _, right_ne_zero_of_mul h, (mem_filter.1 hx).2⟩

lemma indicator_one_conv (s : Finset G) (f : G → K) :
    𝟭_[s] ∗ f = (∑ a ∈ s, τ a f) /ℚ Fintype.card G := by
  ext; simp [conv_eq_expect_sub', Set.indicator_apply, expect]

lemma conv_indicator_one (f : G → K) (s : Finset G) :
    f ∗ 𝟭_[s] = (∑ a ∈ s, τ a f) /ℚ Fintype.card G := by
  ext; simp [conv_eq_expect_sub, Set.indicator_apply, expect]

lemma indicator_one_conv_indicator_one_eq_dens (s t : Finset G) (a : G) :
    (𝟭_[s, K] ∗ 𝟭_[t]) a = (s ∩ (a +ᵥ -t)).dens := by
  rw [← dens_vadd_finset (-a), ← dens_neg, inter_comm, neg_vadd_finset_distrib,
    neg_inter, vadd_finset_inter]
  simp [conv_indicator_one, Set.indicator_apply, NNRat.smul_def, dens, div_eq_inv_mul,
    ← filter_mem_eq_inter, ← neg_vadd_mem_iff, sub_eq_add_neg]

variable [StarRing K]

/-- Compact difference convolution on a finite group.

The value of `f ∗ g` at `a` is the average of the value of `f b * g c` over `b - c = a`. -/
@[expose]
def dconv (f g : G → K) : G → K := fun a ↦ 𝔼 x : G × G with x.1 - x.2 = a, f x.1 * conj g x.2

@[inherit_doc] infixl:71 " ○ " => dconv

lemma dconv_apply (f g : G → K) (a : G) :
    (f ○ g) a = 𝔼 x : G × G with x.1 - x.2 = a, f x.1 * conj g x.2 := rfl

lemma dconv_eq_smul_sum (f g : G → K) (a : G) :
    (f ○ g) a = (∑ x : G × G with x.1 - x.2 = a, f x.1 * conj g x.2) /ℚ Fintype.card G := by
  simp [dconv_apply, expect, ← univ_product_univ, card_sub_eq]

@[simp] lemma conv_conjneg (f g : G → K) : f ∗ conjneg g = f ○ g :=
  funext fun a ↦ expect_bij (fun x _ ↦ (x.1, -x.2)) (fun x hx ↦ by simpa using hx) (fun x _ ↦ rfl)
    (fun x y _ _ h ↦ by grind) fun x hx ↦
      ⟨(x.1, -x.2), by grind, by simp⟩

@[simp] lemma dconv_conjneg (f g : G → K) : f ○ conjneg g = f ∗ g := by
  rw [← conv_conjneg, conjneg_conjneg]

@[simp] lemma translate_dconv (a : G) (f g : G → K) : τ a f ○ g = τ a (f ○ g) :=
  funext fun b ↦ expect_equiv ((Equiv.subRight a).prodCongr <| Equiv.refl _)
    (by simp [sub_right_comm _ a]) (by simp)

@[simp] lemma dconv_translate (a : G) (f g : G → K) : f ○ τ a g = τ (-a) (f ○ g) :=
  funext fun b ↦ expect_equiv ((Equiv.refl _).prodCongr <| Equiv.subRight a)
    (by simp [sub_sub_eq_add_sub, ← sub_add_eq_add_sub]) (by simp)

@[simp] lemma conj_conv (f g : G → K) : conj (f ∗ g) = conj f ∗ conj g :=
  funext fun a ↦ by simp only [Pi.conj_apply, conv_apply, map_expect, map_mul]

@[simp] lemma conj_dconv (f g : G → K) : conj (f ○ g) = conj f ○ conj g := by
  simp_rw [← conv_conjneg, conj_conv, conjneg_conj]

lemma IsSelfAdjoint.conv (hf : IsSelfAdjoint f) (hg : IsSelfAdjoint g) : IsSelfAdjoint (f ∗ g) :=
  (conj_conv _ _).trans <| congr_arg₂ _ hf hg

lemma IsSelfAdjoint.dconv (hf : IsSelfAdjoint f) (hg : IsSelfAdjoint g) : IsSelfAdjoint (f ○ g) :=
  (conj_dconv _ _).trans <| congr_arg₂ _ hf hg

@[simp] lemma conjneg_conv (f g : G → K) : conjneg (f ∗ g) = conjneg f ∗ conjneg g := by
  funext a
  simp only [conv_apply, conjneg_apply, map_expect, map_mul]
  exact Finset.expect_equiv (Equiv.neg (G × G)) (by simp [eq_comm, ← neg_eq_iff_eq_neg, add_comm])
    (by simp)

@[simp] lemma conjneg_dconv (f g : G → K) : conjneg (f ○ g) = g ○ f := by
  simp_rw [← conv_conjneg, conjneg_conv, conjneg_conjneg, conv_comm]

@[simp] lemma dconv_zero (f : G → K) : f ○ 0 = 0 := by simp [← conv_conjneg]
@[simp] lemma zero_dconv (f : G → K) : 0 ○ f = 0 := by rw [← conv_conjneg]; simp [-conv_conjneg]

lemma dconv_add (f g h : G → K) : f ○ (g + h) = f ○ g + f ○ h := by
  simp_rw [← conv_conjneg, conjneg_add, conv_add]

lemma add_dconv (f g h : G → K) : (f + g) ○ h = f ○ h + g ○ h := by
  simp_rw [← conv_conjneg, add_conv]

lemma smul_dconv [DistribSMul H K] [IsScalarTower H K K] [SMulCommClass H K K] (c : H)
    (f g : G → K) : c • f ○ g = c • (f ○ g) := by
  have := SMulCommClass.symm H K K
  ext a
  simp only [Pi.smul_apply, smul_expect, dconv_apply, smul_mul_assoc]

lemma dconv_smul [Star H] [DistribSMul H K] [SMulCommClass H K K]
    [StarModule H K] (c : H) (f g : G → K) : f ○ c • g = star c • (f ○ g) := by
  have := SMulCommClass.symm H K K
  ext a
  simp only [Pi.smul_apply, smul_expect, dconv_apply, mul_smul_comm, starRingEnd_apply, star_smul]

alias smul_dconv_assoc := smul_dconv
alias smul_dconv_left_comm := dconv_smul

lemma conv_dconv_conv_comm (f g h i : G → K) : f ∗ g ○ (h ∗ i) = f ○ h ∗ (g ○ i) := by
  simp_rw [← conv_conjneg, conjneg_conv, conv_conv_conv_comm]

lemma dconv_conv_dconv_comm (f g h i : G → K) : f ○ g ∗ (h ○ i) = f ∗ h ○ (g ∗ i) :=
  (conv_dconv_conv_comm f h g i).symm

lemma dconv_dconv_dconv_comm (f g h i : G → K) : f ○ g ○ (h ○ i) = f ○ h ○ (g ○ i) := by
  simp_rw [← conv_conjneg, conjneg_conv, conv_conv_conv_comm]

--TODO: Can we generalise to star ring homs?
-- lemma map_dconv (f g : G → ℝ≥0) (a : G) : (↑((f ○ g) a) : ℝ) = ((↑) ∘ f ○ (↑) ∘ g) a := by
--   simp_rw [dconv_apply, NNReal.coe_expect, NNReal.coe_mul, starRingEnd_apply, star_trivial,
--     Function.comp_apply]

lemma dconv_eq_expect_add (f g : G → K) (a : G) : (f ○ g) a = 𝔼 t, f (a + t) * conj (g t) := by
  simp [← conv_conjneg, conv_eq_expect_add]

lemma dconv_eq_expect_sub (f g : G → K) (a : G) : (f ○ g) a = 𝔼 t, f t * conj (g (t - a)) := by
  simp [← conv_conjneg, conv_eq_expect_sub']

lemma dconv_apply_neg (f g : G → K) (a : G) : (f ○ g) (-a) = conj ((g ○ f) a) := by
  rw [← conjneg_dconv f, conjneg_apply, Complex.conj_conj]

lemma dconv_apply_sub (f g : G → K) (a b : G) :
    (f ○ g) (a - b) = 𝔼 t, f (a + t) * conj (g (b + t)) := by
  simp [← conv_conjneg, sub_eq_add_neg, conv_apply_add, add_comm]

lemma expect_dconv_mul (f g h : G → K) :
    𝔼 a, (f ○ g) a * h a = 𝔼 a, 𝔼 b, f a * conj (g b) * h (a - b) := by
  simp_rw [dconv_eq_expect_sub, expect_mul]
  rw [expect_comm]
  exact expect_congr rfl fun x _ ↦ Fintype.expect_equiv (Equiv.subLeft x) _ _ fun y ↦ by simp

lemma expect_dconv (f g : G → K) : 𝔼 a, (f ○ g) a = (𝔼 a, f a) * 𝔼 a, conj (g a) := by
  simpa only [Fintype.expect_mul_expect, Pi.one_apply, mul_one] using expect_dconv_mul f g 1

@[simp]
lemma dconv_const (f : G → K) (b : K) : f ○ const _ b = const _ ((𝔼 x, f x) * conj b) := by
  ext; simp [dconv_eq_expect_sub, expect_mul]

@[simp]
lemma const_dconv (b : K) (f : G → K) : const _ b ○ f = const _ (b * 𝔼 x, conj (f x)) := by
  ext; simp [dconv_eq_expect_add, mul_expect]

lemma support_dconv_subset (f g : G → K) : support (f ○ g) ⊆ support f - support g := by
  simpa [sub_eq_add_neg] using support_conv_subset f (conjneg g)

lemma indicator_one_dconv (s : Finset G) (f : G → K) :
    𝟭_[s] ○ f = (∑ a ∈ s, τ a (conjneg f)) /ℚ Fintype.card G := by
  ext; simp [dconv_eq_expect_sub, Set.indicator_apply, expect]

lemma dconv_indicator_one (f : G → K) (s : Finset G) :
    f ○ 𝟭_[s] = (∑ a ∈ s, τ (-a) f) /ℚ Fintype.card G := by
  ext; simp [dconv_eq_expect_add, Set.indicator_apply, expect]

lemma indicator_one_dconv_indicator_one_eq_dens (s t : Finset G) (a : G) :
    (𝟭_[s, K] ○ 𝟭_[t]) a = (s ∩ (a +ᵥ t)).dens := by
  rw [← dens_vadd_finset (-a), inter_comm, vadd_finset_inter]
  simp [dconv_indicator_one, Set.indicator_apply, NNRat.smul_def, dens, div_eq_inv_mul,
    ← filter_mem_eq_inter, ← neg_vadd_mem_iff, sub_eq_add_neg]

lemma indicator_one_dconv_indicator_one_eq_addConvolution_div (s t : Finset G) (a : G) :
    (𝟭_[s, K] ○ 𝟭_[t]) a = s.addConvolution (-t) a / card G := by
  rw [indicator_one_dconv_indicator_one_eq_dens, dens, card_inter_vadd]
  simp

lemma expect_indicator_one_dconv_indicator_one (s t : Finset G) :
    𝔼 a, (𝟭_[(s : Set G), K] ○ 𝟭_[t]) a = s.dens * t.dens := by
  simp [expect_dconv, Set.conj_indicator_one_apply]; simp [← Pi.one_def]

lemma expect_indicator_one_dconv_indicator_sq (s t : Finset G) :
    𝔼 x, (𝟭_[(s : Set G), K] ○ 𝟭_[t]) x ^ 2 = E[s, t] := by
  suffices
      ∑ x, #{yz ∈ s ×ˢ t | yz.1 - yz.2 = x} ^ 2 =
        #{x ∈ (s ×ˢ s) ×ˢ t ×ˢ t | x.1.1 + x.2.1 = x.1.2 + x.2.2} by
    simp only [expect, card_univ, indicator_one_dconv_indicator_one_eq_dens, dens, NNRat.cast_div,
      NNRat.cast_natCast, sq, div_mul_div_comm, ← sum_div, NNRat.smul_def, NNRat.cast_inv,
      addEnergy', NNRat.cast_pow, card_inter_vadd, ← card_sub_eq]
    field_simp
    norm_cast
  simp only [card_eq_sum_ones, sq, Finset.sum_mul_sum, sum_filter, sum_product, boole_mul,
    univ.sum_comm, Finset.sum_ite_eq, mem_univ, ite_true, sub_eq_sub_iff_add_eq_add]
  exact sum_comm

end Semifield

section Field
variable [Field K] [CharZero K]

@[simp] lemma conv_neg (f g : G → K) : f ∗ -g = -(f ∗ g) := by ext; simp [conv_apply]
@[simp] lemma neg_conv (f g : G → K) : -f ∗ g = -(f ∗ g) := by ext; simp [conv_apply]

lemma conv_sub (f g h : G → K) : f ∗ (g - h) = f ∗ g - f ∗ h := by
  simp only [sub_eq_add_neg, conv_add, conv_neg]

lemma sub_conv (f g h : G → K) : (f - g) ∗ h = f ∗ h - g ∗ h := by
  simp only [sub_eq_add_neg, add_conv, neg_conv]

@[simp] lemma balance_conv (f g : G → K) : balance (f ∗ g) = balance f ∗ balance g := by
  simp [balance, conv_sub, sub_conv, expect_conv, expect_sub_distrib]

variable [StarRing K]

@[simp] lemma dconv_neg (f g : G → K) : f ○ -g = -(f ○ g) := by ext; simp [dconv_apply]
@[simp] lemma neg_dconv (f g : G → K) : -f ○ g = -(f ○ g) := by ext; simp [dconv_apply]

lemma dconv_sub (f g h : G → K) : f ○ (g - h) = f ○ g - f ○ h := by
  simp only [sub_eq_add_neg, dconv_add, dconv_neg]

lemma sub_dconv (f g h : G → K) : (f - g) ○ h = f ○ h - g ○ h := by
  simp only [sub_eq_add_neg, add_dconv, neg_dconv]

@[simp] lemma balance_dconv (f g : G → K) : balance (f ○ g) = balance f ○ balance g := by
  simp [balance, dconv_sub, sub_dconv, expect_dconv, map_expect, expect_sub_distrib]

end Field

namespace RCLike
variable {𝕜 : Type} [RCLike 𝕜] (f g : G → ℝ) (a : G)

@[simp, norm_cast] lemma coe_conv : (f ∗ g) a = ((↑) ∘ f ∗ (↑) ∘ g : G → 𝕜) a :=
  map_conv (algebraMap ℝ 𝕜) ..

@[simp, norm_cast] lemma coe_dconv : (f ○ g) a = ((↑) ∘ f ○ (↑) ∘ g : G → 𝕜) a := by
  simp [dconv_apply]

@[simp]
lemma coe_comp_conv : ofReal ∘ (f ∗ g) = ((↑) ∘ f ∗ (↑) ∘ g : G → 𝕜) := funext <| coe_conv _ _

@[simp]
lemma coe_comp_dconv : ofReal ∘ (f ○ g) = ((↑) ∘ f ○ (↑) ∘ g : G → 𝕜) := funext <| coe_dconv _ _

end RCLike

namespace Complex
variable (f g : G → ℝ) (a : G)

@[simp, norm_cast]
lemma coe_conv : (f ∗ g) a = ((↑) ∘ f ∗ (↑) ∘ g : G → ℂ) a := RCLike.coe_conv _ _ _

@[simp, norm_cast]
lemma coe_dconv : (f ○ g) a = ((↑) ∘ f ○ (↑) ∘ g : G → ℂ) a := RCLike.coe_dconv _ _ _

@[simp] lemma ofReal_comp_conv : ofReal ∘ (f ∗ g) = ((↑) ∘ f ∗ (↑) ∘ g : G → ℂ) :=
  funext <| coe_conv _ _

@[simp] lemma ofReal_comp_dconv : ofReal ∘ (f ○ g) = ((↑) ∘ f ○ (↑) ∘ g : G → ℂ) :=
  funext <| coe_dconv _ _

end Complex

namespace NNReal
variable (f g : G → ℝ≥0) (a : G)

@[simp, norm_cast]
lemma coe_conv : (f ∗ g) a = ((↑) ∘ f ∗ (↑) ∘ g : G → ℝ) a := map_conv NNReal.toRealHom _ _ _

@[simp, norm_cast]
lemma coe_dconv : (f ○ g) a = ((↑) ∘ f ○ (↑) ∘ g : G → ℝ) a := by simp [dconv_apply, coe_expect]

@[simp]
lemma coe_comp_conv : ((↑) : _ → ℝ) ∘ (f ∗ g) = (↑) ∘ f ∗ (↑) ∘ g := funext <| coe_conv _ _

@[simp]
lemma coe_comp_dconv : ((↑) : _ → ℝ) ∘ (f ○ g) = (↑) ∘ f ○ (↑) ∘ g := funext <| coe_dconv _ _

end NNReal
