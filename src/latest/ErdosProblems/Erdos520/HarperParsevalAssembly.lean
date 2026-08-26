import ErdosProblems.Erdos520.HarperParseval
import ErdosProblems.Erdos520.HarperWeightedAssembly

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory Set
open scoped BigOperators

namespace Erdos
namespace Problem520

/-!
# Unit-interval assembly for the Harman--Parseval identity

This file supplies the exact interface between the Euler-product vertical
integral and `HarperWeightedAssembly`.  Its local energies are the actual
unweighted Euler-density integrals on the positive and reflected negative
unit intervals.  The remainder is the actual Cauchy-weighted mass outside a
finite vertical truncation.
-/

/-- `true` is the positive unit interval `[n,n+1)` and `false` is its
reflected negative interval `(-(n+1),-n]`. -/
def harperEulerUnitInterval (positive : Bool) (n : ℕ) : Set ℝ :=
  if positive then Ico (n : ℝ) ((n + 1 : ℕ) : ℝ)
  else Ioc (-((n + 1 : ℕ) : ℝ)) (-(n : ℝ))

theorem measurableSet_harperEulerUnitInterval (positive : Bool) (n : ℕ) :
    MeasurableSet (harperEulerUnitInterval positive n) := by
  cases positive <;> simp [harperEulerUnitInterval]

/-- The unweighted unit-interval mass normalized by `log y`, in exactly the
form expected by the weighted assembly. -/
noncomputable def harperEulerLocalEnergy
    (y : ℕ) (positive : Bool) (n : ℕ) (omega : Omega) : ℝ :=
  (∫ t in harperEulerUnitInterval positive n,
      harperEulerDensity y omega t) / Real.log (y : ℝ)

/-- The two weighted vertical tails omitted after the first `M` shells. -/
def harperEulerTailSet (M : ℕ) : Set ℝ :=
  Iic (-((M : ℕ) : ℝ)) ∪ Ici (M : ℝ)

theorem measurableSet_harperEulerTailSet (M : ℕ) :
    MeasurableSet (harperEulerTailSet M) := by
  exact measurableSet_Iic.union measurableSet_Ici

noncomputable def harperEulerTailRemainder
    (y M : ℕ) (omega : Omega) : ℝ :=
  (∫ t in harperEulerTailSet M,
      harperEulerDensity y omega t / ((1 / 2 : ℝ) ^ 2 + t ^ 2)) /
    Real.log (y : ℝ)

theorem integrableOn_harperEulerDensity_unitInterval
    (y : ℕ) (positive : Bool) (n : ℕ) (omega : Omega) :
    IntegrableOn (fun t : ℝ ↦ harperEulerDensity y omega t)
      (harperEulerUnitInterval positive n) := by
  have hcont := continuous_harperEulerDensity_vertical y omega
  cases positive
  · exact (hcont.continuousOn.integrableOn_compact isCompact_Icc).mono_set
      Ioc_subset_Icc_self
  · exact (hcont.continuousOn.integrableOn_compact isCompact_Icc).mono_set
      Ico_subset_Icc_self

theorem harperEulerLocalEnergy_nonneg
    {y : ℕ} (hy : 1 < y) (positive : Bool) (n : ℕ) (omega : Omega) :
    0 ≤ harperEulerLocalEnergy y positive n omega := by
  unfold harperEulerLocalEnergy
  apply div_nonneg
  · exact setIntegral_nonneg
      (measurableSet_harperEulerUnitInterval positive n)
      fun t ht ↦ harperEulerDensity_nonneg y omega t
  · exact (Real.log_pos (by exact_mod_cast hy)).le

theorem harperEulerTailRemainder_nonneg
    {y : ℕ} (hy : 1 < y) (M : ℕ) (omega : Omega) :
    0 ≤ harperEulerTailRemainder y M omega := by
  unfold harperEulerTailRemainder
  apply div_nonneg
  · exact setIntegral_nonneg (measurableSet_harperEulerTailSet M)
      fun t ht ↦ div_nonneg (harperEulerDensity_nonneg y omega t) (by positivity)
  · exact (Real.log_pos (by exact_mod_cast hy)).le

/-- Parseval rewrites the initial smooth energy as the normalized full
Cauchy-weighted vertical Euler mass. -/
theorem harperInitialNormalizedEnergy_eq_verticalIntegral
    (y : ℕ) (omega : Omega) :
    harperInitialNormalizedEnergy y omega =
      (∫ t : ℝ, harperEulerDensity y omega t /
        ((1 / 2 : ℝ) ^ 2 + t ^ 2)) / Real.log (y : ℝ) := by
  unfold harperInitialNormalizedEnergy
  norm_num [show ((1 / 2 : ℝ) ^ 2) = 1 / 4 by norm_num]
  rw [integral_harperEulerDensity_div_cauchyKernel]

private theorem integral_Ico_zero_nat_eq_sum
    (f : ℝ → ℝ) (hf : Integrable f) (M : ℕ) :
    (∫ t in Ico (0 : ℝ) (M : ℝ), f t) =
      ∑ n ∈ Finset.range M,
        ∫ t in Ico (n : ℝ) ((n + 1 : ℕ) : ℝ), f t := by
  induction M with
  | zero => simp
  | succ M ih =>
      have hUnion :
          Ico (0 : ℝ) (M : ℝ) ∪
              Ico (M : ℝ) ((M + 1 : ℕ) : ℝ) =
            Ico (0 : ℝ) ((M + 1 : ℕ) : ℝ) :=
        Set.Ico_union_Ico_eq_Ico
          (by exact_mod_cast Nat.zero_le M)
          (by exact_mod_cast Nat.le_succ M)
      have hdisj : Disjoint (Ico (0 : ℝ) (M : ℝ))
          (Ico (M : ℝ) ((M + 1 : ℕ) : ℝ)) := by
        rw [Set.disjoint_left]
        intro x hx hy
        exact (not_lt_of_ge hy.1) hx.2
      rw [← hUnion, setIntegral_union hdisj measurableSet_Ico
        hf.integrableOn hf.integrableOn, ih, Finset.sum_range_succ]

private theorem integral_Ioc_neg_nat_zero_eq_sum
    (f : ℝ → ℝ) (hf : Integrable f) (M : ℕ) :
    (∫ t in Ioc (-(M : ℝ)) (0 : ℝ), f t) =
      ∑ n ∈ Finset.range M,
        ∫ t in Ioc (-((n + 1 : ℕ) : ℝ)) (-(n : ℝ)), f t := by
  induction M with
  | zero => simp
  | succ M ih =>
      have hUnion :
          Ioc (-((M + 1 : ℕ) : ℝ)) (-(M : ℝ)) ∪
              Ioc (-(M : ℝ)) (0 : ℝ) =
            Ioc (-((M + 1 : ℕ) : ℝ)) (0 : ℝ) :=
        Set.Ioc_union_Ioc_eq_Ioc (by norm_num)
          (neg_nonpos.mpr (Nat.cast_nonneg M))
      have hdisj :
          Disjoint
            (Ioc (-((M + 1 : ℕ) : ℝ)) (-(M : ℝ)))
            (Ioc (-(M : ℝ)) (0 : ℝ)) := by
        rw [Set.disjoint_left]
        intro x hx hy
        exact (not_lt_of_ge hx.2) hy.1
      rw [← hUnion, setIntegral_union hdisj measurableSet_Ioc
        hf.integrableOn hf.integrableOn, ih, Finset.sum_range_succ]
      ring

/-- The abstract two-sided assembly specializes to one positive and one
negative Euler interval at each shell. -/
theorem truncatedHarperTwoSidedAssembly_harperEulerLocalEnergy_eq
    (y M : ℕ) (omega : Omega) :
    truncatedHarperTwoSidedAssembly M (harperEulerLocalEnergy y) omega =
      ∑ n ∈ Finset.range M,
        harperKernelShellCoefficient n *
          (harperEulerLocalEnergy y true n omega +
            harperEulerLocalEnergy y false n omega) := by
  classical
  unfold truncatedHarperTwoSidedAssembly truncatedHarperWeightedAssembly
  rw [Finset.product_eq_sprod, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro n hn
  simp
  ring

/-- Exact finite partition of the full weighted vertical integral into the
first `M` positive and negative unit shells and the two omitted tails. -/
theorem integral_harperEulerDensity_eq_sum_unitIntervals_add_tail
    (y M : ℕ) (omega : Omega) :
    (∫ t : ℝ,
        harperEulerDensity y omega t / ((1 / 2 : ℝ) ^ 2 + t ^ 2)) =
      (∑ n ∈ Finset.range M,
        ((∫ t in harperEulerUnitInterval true n,
            harperEulerDensity y omega t /
              ((1 / 2 : ℝ) ^ 2 + t ^ 2)) +
          (∫ t in harperEulerUnitInterval false n,
            harperEulerDensity y omega t /
              ((1 / 2 : ℝ) ^ 2 + t ^ 2)))) +
        ∫ t in harperEulerTailSet M,
          harperEulerDensity y omega t / ((1 / 2 : ℝ) ^ 2 + t ^ 2) := by
  let w : ℝ → ℝ := fun t ↦
    harperEulerDensity y omega t / ((1 / 2 : ℝ) ^ 2 + t ^ 2)
  have hw : Integrable w := by
    simpa only [w, show ((1 / 2 : ℝ) ^ 2) = 1 / 4 by norm_num] using!
      integrable_harperEulerDensity_div_cauchyKernel y omega
  change (∫ t : ℝ, w t) =
    (∑ n ∈ Finset.range M,
      ((∫ t in harperEulerUnitInterval true n, w t) +
        ∫ t in harperEulerUnitInterval false n, w t)) +
      ∫ t in harperEulerTailSet M, w t
  have hcentral :
      (∫ t in Ioo (-(M : ℝ)) (M : ℝ), w t) =
        (∫ t in Ioc (-(M : ℝ)) (0 : ℝ), w t) +
          ∫ t in Ico (0 : ℝ) (M : ℝ), w t := by
    have hneg : (-(M : ℝ)) ≤ 0 := neg_nonpos.mpr (Nat.cast_nonneg M)
    have hpos : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
    have hdisj :
        Disjoint (Ioc (-(M : ℝ)) (0 : ℝ))
          (Ioc (0 : ℝ) (M : ℝ)) := by
      rw [Set.disjoint_left]
      intro t ht hs
      exact (not_lt_of_ge ht.2) hs.1
    calc
      (∫ t in Ioo (-(M : ℝ)) (M : ℝ), w t) =
          ∫ t in Ioc (-(M : ℝ)) (M : ℝ), w t :=
        integral_Ioc_eq_integral_Ioo.symm
      _ = ∫ t in
          Ioc (-(M : ℝ)) (0 : ℝ) ∪ Ioc (0 : ℝ) (M : ℝ), w t := by
        rw [Set.Ioc_union_Ioc_eq_Ioc hneg hpos]
      _ = (∫ t in Ioc (-(M : ℝ)) (0 : ℝ), w t) +
          ∫ t in Ioc (0 : ℝ) (M : ℝ), w t :=
        setIntegral_union hdisj measurableSet_Ioc hw.integrableOn hw.integrableOn
      _ = (∫ t in Ioc (-(M : ℝ)) (0 : ℝ), w t) +
          ∫ t in Ico (0 : ℝ) (M : ℝ), w t := by
        rw [integral_Ico_eq_integral_Ioc]
  have hcover :
      Ioo (-(M : ℝ)) (M : ℝ) ∪ harperEulerTailSet M = Set.univ := by
    ext t
    simp only [harperEulerTailSet, Set.mem_union, Set.mem_Ioo, Set.mem_Iic,
      Set.mem_Ici, Set.mem_univ, iff_true]
    by_cases hleft : t ≤ -(M : ℝ)
    · exact Or.inr (Or.inl hleft)
    by_cases hright : (M : ℝ) ≤ t
    · exact Or.inr (Or.inr hright)
    · exact Or.inl ⟨lt_of_not_ge hleft, lt_of_not_ge hright⟩
  have hdisjTail :
      Disjoint (Ioo (-(M : ℝ)) (M : ℝ)) (harperEulerTailSet M) := by
    rw [Set.disjoint_left]
    intro t ht htail
    rcases htail with htail | htail
    · exact (not_lt_of_ge htail) ht.1
    · exact (not_le_of_gt ht.2) htail
  have hsplit :
      (∫ t : ℝ, w t) =
        (∫ t in Ioo (-(M : ℝ)) (M : ℝ), w t) +
          ∫ t in harperEulerTailSet M, w t := by
    calc
      (∫ t : ℝ, w t) = ∫ t in Set.univ, w t := by simp
      _ = ∫ t in
          Ioo (-(M : ℝ)) (M : ℝ) ∪ harperEulerTailSet M, w t := by
        rw [hcover]
      _ = _ := setIntegral_union hdisjTail
        (measurableSet_harperEulerTailSet M) hw.integrableOn hw.integrableOn
  rw [hsplit, hcentral, integral_Ioc_neg_nat_zero_eq_sum w hw M,
    integral_Ico_zero_nat_eq_sum w hw M, ← Finset.sum_add_distrib]
  simp only [harperEulerUnitInterval]
  simp
  apply Finset.sum_congr rfl
  intro n hn
  ring

/-- On either reflected unit interval, the normalized weighted mass is
bounded by the shell coefficient times the actual normalized local energy. -/
theorem weighted_harperEulerUnitInterval_div_log_le
    {y : ℕ} (hy : 1 < y) (positive : Bool) (n : ℕ) (omega : Omega) :
    (∫ t in harperEulerUnitInterval positive n,
        harperEulerDensity y omega t /
          ((1 / 2 : ℝ) ^ 2 + t ^ 2)) / Real.log (y : ℝ) ≤
      harperKernelShellCoefficient n *
        harperEulerLocalEnergy y positive n omega := by
  have hlog : 0 < Real.log (y : ℝ) := Real.log_pos (by exact_mod_cast hy)
  cases positive with
  | false =>
      have hshell := setIntegral_Ioc_neg_div_cauchyKernel_le_shell
        (integrableOn_harperEulerDensity_unitInterval y false n omega)
        (fun t ht ↦ harperEulerDensity_nonneg y omega t)
      have hdiv := (div_le_div_iff_of_pos_right hlog).2 hshell
      simpa only [harperEulerUnitInterval, Bool.false_eq_true, if_false,
        harperEulerLocalEnergy] using!
        hdiv.trans_eq (by ring)
  | true =>
      have hshell := setIntegral_Ico_div_cauchyKernel_le_shell
        (integrableOn_harperEulerDensity_unitInterval y true n omega)
        (fun t ht ↦ harperEulerDensity_nonneg y omega t)
      have hdiv := (div_le_div_iff_of_pos_right hlog).2 hshell
      simpa only [harperEulerUnitInterval, if_true,
        harperEulerLocalEnergy] using!
        hdiv.trans_eq (by ring)

/-- The concrete Euler local energies and concrete tail remainder satisfy the
pointwise decomposition hypothesis of `HarperWeightedAssembly`.  Thus after
this theorem the only substantive inputs are the local fractional-moment
bounds and the vanishing tail moment. -/
theorem harperInitialNormalizedEnergy_le_eulerAssembly_add_tail
    {y : ℕ} (hy : 1 < y) (M : ℕ) (omega : Omega) :
    harperInitialNormalizedEnergy y omega ≤
      truncatedHarperTwoSidedAssembly M (harperEulerLocalEnergy y) omega +
        harperEulerTailRemainder y M omega := by
  rw [harperInitialNormalizedEnergy_eq_verticalIntegral y omega,
    integral_harperEulerDensity_eq_sum_unitIntervals_add_tail y M omega]
  unfold harperEulerTailRemainder
  rw [add_div]
  apply add_le_add
  · rw [Finset.sum_div,
      truncatedHarperTwoSidedAssembly_harperEulerLocalEnergy_eq]
    apply Finset.sum_le_sum
    intro n hn
    rw [add_div]
    have hp := weighted_harperEulerUnitInterval_div_log_le hy true n omega
    have hn' := weighted_harperEulerUnitInterval_div_log_le hy false n omega
    calc
      (∫ t in harperEulerUnitInterval true n,
            harperEulerDensity y omega t /
              ((1 / 2 : ℝ) ^ 2 + t ^ 2)) / Real.log (y : ℝ) +
          (∫ t in harperEulerUnitInterval false n,
            harperEulerDensity y omega t /
              ((1 / 2 : ℝ) ^ 2 + t ^ 2)) / Real.log (y : ℝ) ≤
          harperKernelShellCoefficient n *
              harperEulerLocalEnergy y true n omega +
            harperKernelShellCoefficient n *
              harperEulerLocalEnergy y false n omega := add_le_add hp hn'
      _ = harperKernelShellCoefficient n *
          (harperEulerLocalEnergy y true n omega +
            harperEulerLocalEnergy y false n omega) := by ring
  · rfl

end Problem520
end Erdos
