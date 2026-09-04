import Util.Linnik.FamilyExceptionalZero
import ErdosProblems.Erdos48.EndpointFarZero

/-!
# From primitive-family moments to complete zero kernels

The upper-half family and its strict-positive-ordinate part control the
two signs in the explicit formula.  A real exceptional zero therefore
appears once, not twice.
-/

namespace Linnik

open Complex Erdos48 BoundedGaps.Maynard
open scoped BigOperators Classical

local instance {Q : ℕ} (q : ↥(Finset.Ioc 1 Q)) : NeZero q.val :=
  ⟨by have hq := (Finset.mem_Ioc.mp q.property).1; omega⟩

noncomputable def upperHighZeroKernelWeight {Q : ℕ} {T : ℝ}
    (x : ℝ) (i : upperHighZeroIndex Q T) : ℝ :=
  ‖(analyticOrderNatAt (DirichletCharacter.LFunction i.2.1.1) i.2.2.val : ℂ) *
    dirichletExplicitFormulaKernel x i.2.2.val‖

theorem highZeroRealBand_zero_eq_rectangle
    {q : ℕ} [NeZero q] (hq : 1 < q) (psi : primitiveCharacters q)
    {eta T : ℝ} (heta : eta ≤ 1) (hT : 0 ≤ T) :
    highZeroRealBand hq psi.1 psi.2 0 eta T = highZeroRectangle hq psi.1 psi.2 eta T := by
  apply Finset.filter_eq_self.mpr
  intro rho hrho
  have hz := ((mem_highZeroRectangle_iff hq psi.1 psi.2 heta hT rho).mp hrho).1
  simpa only [sub_zero] using LFunction_zero_re_lt_one_of_isPrimitive hq psi.1 psi.2 hz

theorem norm_primitiveKernel_le_upper_positive_far
    {q : ℕ} (hq : 1 < q) (psi : primitiveCharacters q)
    {x T : ℝ} (hx : 0 < x) (hT : 0 ≤ T) :
    ‖primitiveZeroKernelSumAt q psi x T‖ ≤
      ‖primitiveHighZeroRealBandKernelSumAt q psi x 0 (1 / 16) T‖ +
      ‖primitiveLowZeroRealBandKernelSumAt q psi x 0 (1 / 16) T‖ +
      ‖primitiveFarZeroKernelSumAt q psi x (1 / 16) 0 T‖ := by
  let : NeZero q := ⟨by omega⟩
  rw [primitiveZeroKernelSumAt_eq hq,
    dirichletNontrivialZeroKernelSum_eq_firstBand_add_far psi.1 x (1 / 16) T,
    ← primitiveTwoSidedZeroRealBandKernelSumAt_eq hq,
    primitiveTwoSidedZeroRealBandKernelSumAt_eq_high_add_low hq psi hx (by norm_num) hT,
    primitiveFarZeroKernelSumAt_eq hq]
  exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)

theorem sum_upperKernel_norm_le_index
    {Q : ℕ} {x T : ℝ} (hT : 0 ≤ T) :
    (∑ q ∈ Finset.Ioc 1 Q, ∑ psi : primitiveCharacters q,
      ‖primitiveHighZeroRealBandKernelSumAt q psi x 0 (1 / 16) T‖) ≤
      ∑ i : upperHighZeroIndex Q T, upperHighZeroKernelWeight x i := by
  rw [Finset.sum_subtype (Finset.Ioc 1 Q) (fun _ ↦ Iff.rfl)]
  simp only [upperHighZeroIndex, upperHighZeroKernelWeight, Fintype.sum_sigma]
  apply Finset.sum_le_sum
  intro q _
  apply Finset.sum_le_sum
  intro psi _
  have hq := (Finset.mem_Ioc.mp q.property).1
  rw [primitiveHighZeroRealBandKernelSumAt_eq hq, highZeroRealBandKernelSum,
    highZeroRealBand_zero_eq_rectangle hq psi (by norm_num) hT,
    Finset.sum_subtype (highZeroRectangle hq psi.1 psi.2 (1 / 16) T) (fun _ ↦ Iff.rfl)]
  exact norm_sum_le _ _

theorem sum_positiveKernel_norm_le_index
    {Q : ℕ} {x T : ℝ} (hT : 0 ≤ T) :
    (∑ q ∈ Finset.Ioc 1 Q, ∑ psi : primitiveCharacters q,
      ‖primitiveHighZeroPositiveRealBandKernelSumAt q psi x 0 (1 / 16) T‖) ≤
      ∑ i ∈ (Finset.univ : Finset (upperHighZeroIndex Q T)).filter (fun i ↦ 0 < i.2.2.val.im),
        upperHighZeroKernelWeight x i := by
  rw [Finset.sum_filter, Finset.sum_subtype (Finset.Ioc 1 Q) (fun _ ↦ Iff.rfl)]
  simp only [upperHighZeroIndex, upperHighZeroKernelWeight, Fintype.sum_sigma]
  apply Finset.sum_le_sum
  intro q _
  apply Finset.sum_le_sum
  intro psi _
  have hq := (Finset.mem_Ioc.mp q.property).1
  rw [primitiveHighZeroPositiveRealBandKernelSumAt_eq hq, highZeroPositiveRealBandKernelSum,
    highZeroPositiveRealBand, highZeroRealBand_zero_eq_rectangle hq psi (by norm_num) hT,
    Finset.sum_filter,
    Finset.sum_subtype (highZeroRectangle hq psi.1 psi.2 (1 / 16) T) (fun _ ↦ Iff.rfl)]
  simpa only [apply_ite, norm_zero] using norm_sum_le Finset.univ
    (fun rho : ↥(highZeroRectangle hq psi.1 psi.2 (1 / 16) T) ↦
      if 0 < rho.val.im then
        (analyticOrderNatAt (DirichletCharacter.LFunction psi.1) rho.val : ℂ) *
          dirichletExplicitFormulaKernel x rho.val else 0)

theorem sum_primitiveKernel_norm_le_upper_positive_far
    {Q : ℕ} {x T : ℝ} (hx : 0 < x) (hT : 0 ≤ T) :
    (∑ q ∈ Finset.Ioc 1 Q, ∑ psi : primitiveCharacters q,
      ‖primitiveZeroKernelSumAt q psi x T‖) ≤
      (∑ i : upperHighZeroIndex Q T, upperHighZeroKernelWeight x i) +
      (∑ i ∈ (Finset.univ : Finset (upperHighZeroIndex Q T)).filter (fun i ↦ 0 < i.2.2.val.im),
        upperHighZeroKernelWeight x i) + primitiveFarZeroKernelMass Q x (1 / 16) 0 T := by
  have hpoint := Finset.sum_le_sum (s := Finset.Ioc 1 Q) fun q hq ↦
    Finset.sum_le_sum (s := Finset.univ) fun psi _ ↦
      norm_primitiveKernel_le_upper_positive_far (Finset.mem_Ioc.mp hq).1 psi hx hT
  simp_rw [Finset.sum_add_distrib] at hpoint
  rw [sum_norm_primitiveLowZeroRealBandKernelSumAt_eq] at hpoint
  exact hpoint.trans (add_le_add (add_le_add
    (sum_upperKernel_norm_le_index hT) (sum_positiveKernel_norm_le_index hT)) le_rfl)

theorem upperHighZeroKernelWeight_le_exp
    {Q : ℕ} {x T D H : ℝ} (hx : 1 ≤ x) (hT : 0 ≤ T)
    (hscale : D * H ≤ Real.log x) (i : upperHighZeroIndex Q T) :
    upperHighZeroKernelWeight x i ≤
      4 * x * (upperHighZeroWeight i * Real.exp (-D * (H * upperHighZeroGap i))) := by
  have hrect := (mem_highZeroRectangle_iff (Finset.mem_Ioc.mp i.1.property).1
    i.2.1.1 i.2.1.2 (by norm_num : (1 / 16 : ℝ) ≤ 1) hT i.2.2.val).mp i.2.2.property
  have hkernel := norm_dirichletExplicitFormulaKernel_le_four_rpow hx
    (by linarith [hrect.2.1] : 1 / 2 ≤ i.2.2.val.re)
  have hgap := (upperHighZeroGap_bounds hT i).1
  have hx₀ := zero_lt_one.trans_le hx
  have hpow : x ^ i.2.2.val.re ≤ x * Real.exp (-D * (H * upperHighZeroGap i)) := by
    rw [Real.rpow_def_of_pos hx₀, ← Real.exp_log hx₀, ← Real.exp_add, Real.exp_le_exp,
      Real.log_exp]
    dsimp [upperHighZeroGap] at hgap ⊢
    nlinarith [mul_le_mul_of_nonneg_right hscale hgap]
  unfold upperHighZeroKernelWeight upperHighZeroWeight
  rw [norm_mul, Complex.norm_natCast]
  calc
    _ ≤ (analyticOrderNatAt (DirichletCharacter.LFunction i.2.1.1) i.2.2.val : ℝ) *
        (4 * x ^ i.2.2.val.re) := mul_le_mul_of_nonneg_left hkernel (by positivity)
    _ ≤ (analyticOrderNatAt (DirichletCharacter.LFunction i.2.1.1) i.2.2.val : ℝ) *
        (4 * (x * Real.exp (-D * (H * upperHighZeroGap i)))) := by gcongr
    _ = _ := by ring

theorem sum_upperHighZeroKernelWeight_le_moment
    {Q : ℕ} {x T D H : ℝ} (hx : 1 ≤ x) (hT : 0 ≤ T)
    (hscale : D * H ≤ Real.log x) (S : Finset (upperHighZeroIndex Q T)) :
    (∑ i ∈ S, upperHighZeroKernelWeight x i) ≤
      4 * x * ∑ i ∈ S,
        upperHighZeroWeight i * Real.exp (-D * (H * upperHighZeroGap i)) := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ ↦ upperHighZeroKernelWeight_le_exp hx hT hscale i

theorem sum_primitiveKernel_norm_le_moment_add_far
    {Q : ℕ} {x T D H E : ℝ} (hx : 1 ≤ x) (hT : 0 ≤ T)
    (hscale : D * H ≤ Real.log x)
    (hmoment : (∑ i : upperHighZeroIndex Q T,
      upperHighZeroWeight i * Real.exp (-D * (H * upperHighZeroGap i))) ≤ E) :
    (∑ q ∈ Finset.Ioc 1 Q, ∑ psi : primitiveCharacters q,
      ‖primitiveZeroKernelSumAt q psi x T‖) ≤
      8 * x * E + primitiveFarZeroKernelMass Q x (1 / 16) 0 T := by
  have hall := (sum_upperHighZeroKernelWeight_le_moment hx hT hscale Finset.univ).trans
    (mul_le_mul_of_nonneg_left hmoment (by positivity : 0 ≤ 4 * x))
  have hpos : (∑ i ∈ (Finset.univ : Finset (upperHighZeroIndex Q T)).filter
      (fun i ↦ 0 < i.2.2.val.im), upperHighZeroKernelWeight x i) ≤
      ∑ i : upperHighZeroIndex Q T, upperHighZeroKernelWeight x i :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun i _ _ ↦ norm_nonneg _)
  have hkernel := sum_primitiveKernel_norm_le_upper_positive_far (Q := Q)
    (zero_lt_one.trans_le hx) hT
  exact hkernel.trans (by linarith [hpos.trans hall])

theorem sum_primitiveKernel_norm_le_exceptional_moment_add_far
    {Q : ℕ} {x T D H E : ℝ} (hx : 1 ≤ x) (hT : 0 ≤ T)
    (hscale : D * H ≤ Real.log x) (i₀ : upperHighZeroIndex Q T)
    (him : i₀.2.2.val.im = 0) (hweight : upperHighZeroWeight i₀ = 1)
    (hmoment : (∑ i ∈ (Finset.univ : Finset (upperHighZeroIndex Q T)).erase i₀,
      upperHighZeroWeight i * Real.exp (-D * (H * upperHighZeroGap i))) ≤ E) :
    (∑ q ∈ Finset.Ioc 1 Q, ∑ psi : primitiveCharacters q,
      ‖primitiveZeroKernelSumAt q psi x T‖) ≤
      ‖dirichletExplicitFormulaKernel x (i₀.2.2.val.re : ℂ)‖ +
      8 * x * E + primitiveFarZeroKernelMass Q x (1 / 16) 0 T := by
  let S : Finset (upperHighZeroIndex Q T) := Finset.univ.erase i₀
  have hsum := (sum_upperHighZeroKernelWeight_le_moment hx hT hscale S).trans
    (mul_le_mul_of_nonneg_left hmoment (by positivity : 0 ≤ 4 * x))
  have hpos : (∑ i ∈ (Finset.univ : Finset (upperHighZeroIndex Q T)).filter
      (fun i ↦ 0 < i.2.2.val.im), upperHighZeroKernelWeight x i) ≤
      ∑ i ∈ S, upperHighZeroKernelWeight x i := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro i hi
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
      intro heq
      subst i
      have h := (Finset.mem_filter.mp hi).2
      rw [him] at h
      exact lt_irrefl 0 h
    · intro i _ _
      exact norm_nonneg _
  have hsingle : upperHighZeroKernelWeight x i₀ =
      ‖dirichletExplicitFormulaKernel x (i₀.2.2.val.re : ℂ)‖ := by
    have horder : analyticOrderNatAt (DirichletCharacter.LFunction i₀.2.1.1) i₀.2.2.val = 1 := by
      dsimp [upperHighZeroWeight] at hweight
      exact_mod_cast hweight
    have hrho : i₀.2.2.val = (i₀.2.2.val.re : ℂ) := by apply Complex.ext <;> simp [him]
    rw [upperHighZeroKernelWeight, horder, Nat.cast_one, one_mul, hrho]
    rfl
  have hall := Finset.sum_erase_add Finset.univ (upperHighZeroKernelWeight x)
    (Finset.mem_univ i₀)
  rw [hsingle] at hall
  have hkernel := sum_primitiveKernel_norm_le_upper_positive_far (Q := Q)
    (zero_lt_one.trans_le hx) hT
  dsimp [S] at hsum hpos
  linarith

end Linnik
