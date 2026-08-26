import ErdosProblems.Erdos520.HarperSpecialization
import Mathlib.Analysis.PSeries

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory Set
open scoped BigOperators

namespace Erdos.Problem520

/-!
# Elementary weighted assembly for Harper's initial-energy estimate

This file formalizes the local-to-global part of the Harper specialization,
without asserting any of Harper's deep low-moment propositions.  A unit-shell
moment is allowed to grow like `(n + 1)^(1/6)`.  The Cauchy kernel contributes
`(n + 1)^(-2)`; `2/3`-subadditivity therefore leaves the summable power
`(n + 1)^(-7/6)`.

The principal result is finite and two-sided, with a bound uniform in the
vertical truncation.  `integral_twoThird_le_twoSidedAssembly_add_remainder`
also records the exact omitted-tail term needed to pass from a finite
partition to the full vertical integral.  The final theorem specializes that
statement to the repository's existing `harperInitialNormalizedEnergy`.
-/

noncomputable def harperTwoThird : ℝ := (2 : ℝ) / 3

def harperShellScale (n : ℕ) : ℝ := (n + 1 : ℕ)

noncomputable def harperKernelShellCoefficient (n : ℕ) : ℝ :=
  4 / harperShellScale n ^ 2

noncomputable def harperLocalMomentLoss (n : ℕ) : ℝ :=
  harperShellScale n ^ ((1 : ℝ) / 6)

noncomputable def harperGlobalMomentSeriesTerm (n : ℕ) : ℝ :=
  harperShellScale n ^ (-(7 : ℝ) / 6)

lemma harperShellScale_pos (n : ℕ) : 0 < harperShellScale n := by
  change 0 < ((n + 1 : ℕ) : ℝ)
  exact_mod_cast Nat.zero_lt_succ n

lemma harperKernelShellCoefficient_nonneg (n : ℕ) :
    0 ≤ harperKernelShellCoefficient n := by
  exact div_nonneg (by norm_num) (sq_nonneg _)

lemma harper_kernel_le_shell {n : ℕ} {t : ℝ}
    (ht : (n : ℝ) ≤ |t|) :
    1 / ((1 / 2 : ℝ) ^ 2 + t ^ 2) ≤ harperKernelShellCoefficient n := by
  have hden : 0 < (1 / 2 : ℝ) ^ 2 + t ^ 2 := by positivity
  have hscale : 0 < harperShellScale n ^ 2 := by
    exact sq_pos_of_pos (harperShellScale_pos n)
  rw [harperKernelShellCoefficient, div_le_div_iff₀ hden hscale]
  have hsq : (n : ℝ) ^ 2 ≤ |t| ^ 2 := (sq_le_sq₀ (Nat.cast_nonneg n) (abs_nonneg t)).2 ht
  rw [sq_abs] at hsq
  by_cases hn : n = 0
  · subst n
    norm_num [harperShellScale]
    nlinarith [sq_nonneg t]
  · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
    dsimp [harperShellScale]
    norm_num at hsq ⊢
    nlinarith [sq_nonneg ((n : ℝ) - 1)]

lemma harper_scaled_moment_factor (n : ℕ) :
    harperKernelShellCoefficient n ^ harperTwoThird *
        harperLocalMomentLoss n =
      4 ^ harperTwoThird * harperGlobalMomentSeriesTerm n := by
  have hs : 0 < harperShellScale n := harperShellScale_pos n
  rw [harperKernelShellCoefficient, harperTwoThird, harperLocalMomentLoss,
    harperGlobalMomentSeriesTerm]
  rw [Real.div_rpow (by norm_num : (0 : ℝ) ≤ 4) (sq_nonneg _) ((2 : ℝ) / 3)]
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul hs.le]
  rw [div_eq_mul_inv, ← Real.rpow_neg hs.le, mul_assoc]
  rw [← Real.rpow_add hs]
  congr 1
  ring_nf

lemma summable_harperGlobalMomentSeriesTerm :
    Summable harperGlobalMomentSeriesTerm := by
  have hbase : Summable (fun n : ℕ ↦ (n : ℝ) ^ (-(7 : ℝ) / 6)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hshift := (summable_nat_add_iff (f := fun n : ℕ ↦
    (n : ℝ) ^ (-(7 : ℝ) / 6)) 1).2 hbase
  change Summable (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ) ^ (-(7 : ℝ) / 6))
  simpa only [Nat.cast_add, Nat.cast_one] using! hshift


lemma finset_sum_rpow_twoThird_le {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) :
    (∑ i ∈ s, a i) ^ harperTwoThird ≤
      ∑ i ∈ s, a i ^ harperTwoThird := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [harperTwoThird]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      apply (Real.rpow_add_le_add_rpow (ha i (by simp))
        (Finset.sum_nonneg fun j hj ↦ ha j (by simp [hj]))
        (by norm_num [harperTwoThird]) (by norm_num [harperTwoThird])).trans
      exact add_le_add_right (ih fun j hj ↦ ha j (by simp [hj])) _


noncomputable def truncatedHarperWeightedAssembly
    {α ι : Type*} (s : Finset ι) (shell : ι → ℕ)
    (localEnergy : ι → α → ℝ) (omega : α) : ℝ :=
  ∑ i ∈ s, harperKernelShellCoefficient (shell i) * localEnergy i omega

/-- The elementary finite local-to-global estimate in Harper's specialization.
Each local unit interval may lose `scale^(1/6)`.  The Cauchy kernel contributes
`scale^(-2)`, and raising to the `2/3` moment leaves `scale^(-7/6)`. -/
theorem integral_truncatedHarperWeightedAssembly_twoThird_le
    {α ι : Type*} [MeasurableSpace α] {ν : Measure α}
    {A : ℝ} (s : Finset ι) (shell : ι → ℕ)
    (localEnergy : ι → α → ℝ)
    (hlocal : ∀ i ∈ s, ∀ omega, 0 ≤ localEnergy i omega)
    (hintegrable : ∀ i ∈ s,
      Integrable (fun omega ↦ localEnergy i omega ^ harperTwoThird) ν)
    (hmoment : ∀ i ∈ s,
      (∫ omega, localEnergy i omega ^ harperTwoThird ∂ν) ≤
        A * harperLocalMomentLoss (shell i)) :
    (∫ omega,
        truncatedHarperWeightedAssembly s shell localEnergy omega ^
          harperTwoThird ∂ν) ≤
      A * 4 ^ harperTwoThird *
        ∑ i ∈ s, harperGlobalMomentSeriesTerm (shell i) := by
  classical
  let term : ι → α → ℝ := fun i omega ↦
    (harperKernelShellCoefficient (shell i) * localEnergy i omega) ^
      harperTwoThird
  have hterm_eq (i : ι) (hi : i ∈ s) (omega : α) :
      term i omega =
        harperKernelShellCoefficient (shell i) ^ harperTwoThird *
          localEnergy i omega ^ harperTwoThird := by
    exact Real.mul_rpow (harperKernelShellCoefficient_nonneg _)
      (hlocal i hi omega)
  have hterm_integrable (i : ι) (hi : i ∈ s) :
      Integrable (term i) ν := by
    have h := (hintegrable i hi).const_mul
      (harperKernelShellCoefficient (shell i) ^ harperTwoThird)
    apply h.congr
    exact ae_of_all ν fun omega ↦ (hterm_eq i hi omega).symm
  have hsum_integrable :
      Integrable (fun omega ↦ ∑ i ∈ s, term i omega) ν :=
    integrable_finset_sum s hterm_integrable
  calc
    (∫ omega,
        truncatedHarperWeightedAssembly s shell localEnergy omega ^
          harperTwoThird ∂ν) ≤
        ∫ omega, ∑ i ∈ s, term i omega ∂ν := by
      apply integral_mono_of_nonneg
      · exact ae_of_all ν fun omega ↦ Real.rpow_nonneg
          (Finset.sum_nonneg fun i hi ↦ mul_nonneg
            (harperKernelShellCoefficient_nonneg _) (hlocal i hi omega)) _
      · exact hsum_integrable
      · exact ae_of_all ν fun omega ↦
          finset_sum_rpow_twoThird_le s
            (fun i ↦ harperKernelShellCoefficient (shell i) * localEnergy i omega)
            (fun i hi ↦ mul_nonneg (harperKernelShellCoefficient_nonneg _)
              (hlocal i hi omega))
    _ = ∑ i ∈ s, ∫ omega, term i omega ∂ν :=
      integral_finset_sum s hterm_integrable
    _ ≤ ∑ i ∈ s,
        A * 4 ^ harperTwoThird * harperGlobalMomentSeriesTerm (shell i) := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        (∫ omega, term i omega ∂ν) =
            harperKernelShellCoefficient (shell i) ^ harperTwoThird *
              ∫ omega, localEnergy i omega ^ harperTwoThird ∂ν := by
          simp_rw [hterm_eq i hi]
          exact integral_const_mul _ _
        _ ≤ harperKernelShellCoefficient (shell i) ^ harperTwoThird *
              (A * harperLocalMomentLoss (shell i)) :=
          mul_le_mul_of_nonneg_left (hmoment i hi)
            (Real.rpow_nonneg (harperKernelShellCoefficient_nonneg _) _)
        _ = A *
              (harperKernelShellCoefficient (shell i) ^ harperTwoThird *
                harperLocalMomentLoss (shell i)) := by ring
        _ = A * 4 ^ harperTwoThird *
              harperGlobalMomentSeriesTerm (shell i) := by
          rw [harper_scaled_moment_factor]
          ring
    _ = A * 4 ^ harperTwoThird *
        ∑ i ∈ s, harperGlobalMomentSeriesTerm (shell i) := by
      rw [Finset.mul_sum]


/-- On a shell on which `|t| ≥ n`, the Cauchy kernel is bounded by the
coefficient used in the discrete assembly. -/
theorem setIntegral_div_cauchyKernel_le_shell
    {n : ℕ} {s : Set ℝ} {g : ℝ → ℝ}
    (hs : MeasurableSet s) (hg : IntegrableOn g s)
    (hg_nonneg : ∀ t ∈ s, 0 ≤ g t)
    (hshell : ∀ t ∈ s, (n : ℝ) ≤ |t|) :
    (∫ t in s, g t / ((1 / 2 : ℝ) ^ 2 + t ^ 2)) ≤
      harperKernelShellCoefficient n * ∫ t in s, g t := by
  rw [← integral_const_mul]
  apply integral_mono_of_nonneg
  · filter_upwards [ae_restrict_mem hs] with t ht
    exact div_nonneg (hg_nonneg t ht) (by positivity)
  · exact hg.const_mul (harperKernelShellCoefficient n)
  · filter_upwards [ae_restrict_mem hs] with t ht
    rw [div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_right
      (by simpa [one_div] using! harper_kernel_le_shell (hshell t ht))
      (hg_nonneg t ht)


/-- Positive unit-interval form of the kernel comparison. -/
theorem setIntegral_Ico_div_cauchyKernel_le_shell
    {n : ℕ} {g : ℝ → ℝ}
    (hg : IntegrableOn g (Ico (n : ℝ) (n + 1 : ℕ)))
    (hg_nonneg : ∀ t ∈ Ico (n : ℝ) (n + 1 : ℕ), 0 ≤ g t) :
    (∫ t in Ico (n : ℝ) (n + 1 : ℕ),
        g t / ((1 / 2 : ℝ) ^ 2 + t ^ 2)) ≤
      harperKernelShellCoefficient n *
        ∫ t in Ico (n : ℝ) (n + 1 : ℕ), g t := by
  apply setIntegral_div_cauchyKernel_le_shell measurableSet_Ico hg hg_nonneg
  intro t ht
  exact ht.1.trans (le_abs_self t)

/-- Reflected negative unit-interval form of the kernel comparison. -/
theorem setIntegral_Ioc_neg_div_cauchyKernel_le_shell
    {n : ℕ} {g : ℝ → ℝ}
    (hg : IntegrableOn g (Ioc (-((n + 1 : ℕ) : ℝ)) (-(n : ℝ))))
    (hg_nonneg : ∀ t ∈ Ioc (-((n + 1 : ℕ) : ℝ)) (-(n : ℝ)), 0 ≤ g t) :
    (∫ t in Ioc (-((n + 1 : ℕ) : ℝ)) (-(n : ℝ)),
        g t / ((1 / 2 : ℝ) ^ 2 + t ^ 2)) ≤
      harperKernelShellCoefficient n *
        ∫ t in Ioc (-((n + 1 : ℕ) : ℝ)) (-(n : ℝ)), g t := by
  apply setIntegral_div_cauchyKernel_le_shell measurableSet_Ioc hg hg_nonneg
  intro t ht
  have hneg : (n : ℝ) ≤ -t := by linarith [ht.2]
  exact hneg.trans (neg_le_abs t)


/-- The two tails of the real line, truncated after `M` unit shells. -/
noncomputable def truncatedHarperTwoSidedAssembly
    {α : Type*} (M : ℕ) (localEnergy : Bool → ℕ → α → ℝ)
    (omega : α) : ℝ :=
  truncatedHarperWeightedAssembly
    ((Finset.range M).product Finset.univ) Prod.fst
    (fun i omega ↦ localEnergy i.2 i.1 omega) omega

/-- Two-sided finite assembly.  The factor `2` is exactly the two reflected
unit intervals in every shell. -/
theorem integral_truncatedHarperTwoSidedAssembly_twoThird_le
    {α : Type*} [MeasurableSpace α] {ν : Measure α}
    {A : ℝ} (M : ℕ) (localEnergy : Bool → ℕ → α → ℝ)
    (hlocal : ∀ d n, n < M → ∀ omega, 0 ≤ localEnergy d n omega)
    (hintegrable : ∀ d n, n < M →
      Integrable (fun omega ↦ localEnergy d n omega ^ harperTwoThird) ν)
    (hmoment : ∀ d n, n < M →
      (∫ omega, localEnergy d n omega ^ harperTwoThird ∂ν) ≤
        A * harperLocalMomentLoss n) :
    (∫ omega,
        truncatedHarperTwoSidedAssembly M localEnergy omega ^
          harperTwoThird ∂ν) ≤
      2 * A * 4 ^ harperTwoThird *
        ∑ n ∈ Finset.range M, harperGlobalMomentSeriesTerm n := by
  have h := integral_truncatedHarperWeightedAssembly_twoThird_le
    ((Finset.range M).product Finset.univ) Prod.fst
    (fun i omega ↦ localEnergy i.2 i.1 omega)
    (fun i hi omega ↦ hlocal i.2 i.1 (Finset.mem_range.mp
      (Finset.mem_product.mp hi).1) omega)
    (fun i hi ↦ hintegrable i.2 i.1 (Finset.mem_range.mp
      (Finset.mem_product.mp hi).1))
    (fun i hi ↦ hmoment i.2 i.1 (Finset.mem_range.mp
      (Finset.mem_product.mp hi).1))
  change (∫ omega,
        truncatedHarperTwoSidedAssembly M localEnergy omega ^
          harperTwoThird ∂ν) ≤ _ at h
  calc
    (∫ omega,
        truncatedHarperTwoSidedAssembly M localEnergy omega ^
          harperTwoThird ∂ν) ≤
        A * 4 ^ harperTwoThird *
          ∑ i ∈ (Finset.range M).product Finset.univ,
            harperGlobalMomentSeriesTerm i.1 := h
    _ = 2 * A * 4 ^ harperTwoThird *
        ∑ n ∈ Finset.range M, harperGlobalMomentSeriesTerm n := by
      have hp := Finset.sum_product (Finset.range M) (Finset.univ : Finset Bool)
        (fun i : ℕ × Bool ↦ harperGlobalMomentSeriesTerm i.1)
      rw [Finset.product_eq_sprod, hp]
      simp only [Fintype.univ_bool, Finset.sum_const, Finset.mem_singleton,
        Bool.true_eq_false, not_false_eq_true, Finset.card_insert_of_notMem,
        Finset.card_singleton, Nat.reduceAdd, nsmul_eq_mul, Nat.cast_ofNat]
      rw [← Finset.mul_sum]
      ring

/-- The `7/6` tail gives a uniform constant for every finite two-sided
truncation. -/
theorem integral_truncatedHarperTwoSidedAssembly_twoThird_le_tsum
    {α : Type*} [MeasurableSpace α] {ν : Measure α}
    {A : ℝ} (hA : 0 ≤ A) (M : ℕ)
    (localEnergy : Bool → ℕ → α → ℝ)
    (hlocal : ∀ d n, n < M → ∀ omega, 0 ≤ localEnergy d n omega)
    (hintegrable : ∀ d n, n < M →
      Integrable (fun omega ↦ localEnergy d n omega ^ harperTwoThird) ν)
    (hmoment : ∀ d n, n < M →
      (∫ omega, localEnergy d n omega ^ harperTwoThird ∂ν) ≤
        A * harperLocalMomentLoss n) :
    (∫ omega,
        truncatedHarperTwoSidedAssembly M localEnergy omega ^
          harperTwoThird ∂ν) ≤
      2 * A * 4 ^ harperTwoThird *
        ∑' n : ℕ, harperGlobalMomentSeriesTerm n := by
  refine (integral_truncatedHarperTwoSidedAssembly_twoThird_le
    M localEnergy hlocal hintegrable hmoment).trans ?_
  have hsum : (∑ n ∈ Finset.range M, harperGlobalMomentSeriesTerm n) ≤
      ∑' n : ℕ, harperGlobalMomentSeriesTerm n :=
    summable_harperGlobalMomentSeriesTerm.sum_le_tsum _
      (fun n _ ↦ Real.rpow_nonneg (harperShellScale_pos n).le _)
  exact mul_le_mul_of_nonneg_left hsum (by positivity)


/-- Fractional integrability of a finite weighted assembly follows from the
local fractional integrability; no first moment is needed. -/
theorem integrable_truncatedHarperWeightedAssembly_twoThird
    {α ι : Type*} [MeasurableSpace α] {ν : Measure α}
    (s : Finset ι) (shell : ι → ℕ) (localEnergy : ι → α → ℝ)
    (hlocal : ∀ i ∈ s, ∀ omega, 0 ≤ localEnergy i omega)
    (hmeasurable : ∀ i ∈ s, AEStronglyMeasurable (localEnergy i) ν)
    (hintegrable : ∀ i ∈ s,
      Integrable (fun omega ↦ localEnergy i omega ^ harperTwoThird) ν) :
    Integrable (fun omega ↦
      truncatedHarperWeightedAssembly s shell localEnergy omega ^
        harperTwoThird) ν := by
  classical
  let term : ι → α → ℝ := fun i omega ↦
    (harperKernelShellCoefficient (shell i) * localEnergy i omega) ^
      harperTwoThird
  have hterm_eq (i : ι) (hi : i ∈ s) (omega : α) :
      term i omega =
        harperKernelShellCoefficient (shell i) ^ harperTwoThird *
          localEnergy i omega ^ harperTwoThird := by
    exact Real.mul_rpow (harperKernelShellCoefficient_nonneg _)
      (hlocal i hi omega)
  have hterm_integrable (i : ι) (hi : i ∈ s) :
      Integrable (term i) ν := by
    have h := (hintegrable i hi).const_mul
      (harperKernelShellCoefficient (shell i) ^ harperTwoThird)
    apply h.congr
    exact ae_of_all ν fun omega ↦ (hterm_eq i hi omega).symm
  have hsum_integrable :
      Integrable (fun omega ↦ ∑ i ∈ s, term i omega) ν :=
    integrable_finset_sum s hterm_integrable
  have hassembly_measurable : AEStronglyMeasurable
      (fun omega ↦ truncatedHarperWeightedAssembly s shell localEnergy omega) ν := by
    unfold truncatedHarperWeightedAssembly
    have hm := Finset.aestronglyMeasurable_sum s fun i hi ↦
      (hmeasurable i hi).const_mul
        (harperKernelShellCoefficient (shell i))
    apply hm.congr
    exact ae_of_all ν fun omega ↦
      Finset.sum_apply omega s (fun i omega ↦
        harperKernelShellCoefficient (shell i) * localEnergy i omega)
  have hpow_measurable : AEStronglyMeasurable
      (fun omega ↦ truncatedHarperWeightedAssembly s shell localEnergy omega ^
        harperTwoThird) ν :=
    (Real.continuous_rpow_const (by norm_num [harperTwoThird])).comp_aestronglyMeasurable
      hassembly_measurable
  apply hsum_integrable.mono' hpow_measurable
  exact ae_of_all ν fun omega ↦ by
    change |(∑ i ∈ s, harperKernelShellCoefficient (shell i) *
      localEnergy i omega) ^ harperTwoThird| ≤
        ∑ i ∈ s, (harperKernelShellCoefficient (shell i) *
          localEnergy i omega) ^ harperTwoThird
    rw [abs_of_nonneg (Real.rpow_nonneg
      (Finset.sum_nonneg fun i hi ↦ mul_nonneg
        (harperKernelShellCoefficient_nonneg _) (hlocal i hi omega)) _)]
    exact finset_sum_rpow_twoThird_le s
      (fun i ↦ harperKernelShellCoefficient (shell i) * localEnergy i omega)
      (fun i hi ↦ mul_nonneg (harperKernelShellCoefficient_nonneg _)
        (hlocal i hi omega))


/-- Measurable local interval energies give fractional integrability of the
two-sided truncation. -/
theorem integrable_truncatedHarperTwoSidedAssembly_twoThird
    {α : Type*} [MeasurableSpace α] {ν : Measure α}
    (M : ℕ) (localEnergy : Bool → ℕ → α → ℝ)
    (hlocal : ∀ d n, n < M → ∀ omega, 0 ≤ localEnergy d n omega)
    (hmeasurable : ∀ d n, n < M →
      AEStronglyMeasurable (localEnergy d n) ν)
    (hintegrable : ∀ d n, n < M →
      Integrable (fun omega ↦ localEnergy d n omega ^ harperTwoThird) ν) :
    Integrable (fun omega ↦
      truncatedHarperTwoSidedAssembly M localEnergy omega ^
        harperTwoThird) ν := by
  apply integrable_truncatedHarperWeightedAssembly_twoThird
    ((Finset.range M).product Finset.univ) Prod.fst
    (fun i omega ↦ localEnergy i.2 i.1 omega)
  · intro i hi omega
    exact hlocal i.2 i.1 (Finset.mem_range.mp (Finset.mem_product.mp hi).1) omega
  · intro i hi
    exact hmeasurable i.2 i.1 (Finset.mem_range.mp (Finset.mem_product.mp hi).1)
  · intro i hi
    exact hintegrable i.2 i.1 (Finset.mem_range.mp (Finset.mem_product.mp hi).1)

/-- Exact finite-truncation statement with a remainder.  This is the complete
elementary local-to-global passage needed before taking the vertical cutoff
to infinity: the only unclosed term is the displayed fractional moment of the
omitted tail. -/
theorem integral_twoThird_le_twoSidedAssembly_add_remainder
    {α : Type*} [MeasurableSpace α] {ν : Measure α}
    {A R : ℝ} (M : ℕ) (W : α → ℝ)
    (localEnergy : Bool → ℕ → α → ℝ) (remainder : α → ℝ)
    (hW_nonneg : ∀ omega, 0 ≤ W omega)
    (hW_integrable : Integrable (fun omega ↦ W omega ^ harperTwoThird) ν)
    (hlocal : ∀ d n, n < M → ∀ omega, 0 ≤ localEnergy d n omega)
    (hmeasurable : ∀ d n, n < M →
      AEStronglyMeasurable (localEnergy d n) ν)
    (hintegrable : ∀ d n, n < M →
      Integrable (fun omega ↦ localEnergy d n omega ^ harperTwoThird) ν)
    (hmoment : ∀ d n, n < M →
      (∫ omega, localEnergy d n omega ^ harperTwoThird ∂ν) ≤
        A * harperLocalMomentLoss n)
    (hremainder_nonneg : ∀ omega, 0 ≤ remainder omega)
    (hremainder_integrable :
      Integrable (fun omega ↦ remainder omega ^ harperTwoThird) ν)
    (hremainder_moment :
      (∫ omega, remainder omega ^ harperTwoThird ∂ν) ≤ R)
    (hdecomp : ∀ omega,
      W omega ≤ truncatedHarperTwoSidedAssembly M localEnergy omega +
        remainder omega) :
    (∫ omega, W omega ^ harperTwoThird ∂ν) ≤
      2 * A * 4 ^ harperTwoThird *
          ∑ n ∈ Finset.range M, harperGlobalMomentSeriesTerm n + R := by
  have hassembly_integrable :=
    integrable_truncatedHarperTwoSidedAssembly_twoThird
      M localEnergy hlocal hmeasurable hintegrable
  have hsum_integrable := hassembly_integrable.add hremainder_integrable
  calc
    (∫ omega, W omega ^ harperTwoThird ∂ν) ≤
        ∫ omega,
          truncatedHarperTwoSidedAssembly M localEnergy omega ^
              harperTwoThird +
            remainder omega ^ harperTwoThird ∂ν := by
      apply integral_mono hW_integrable hsum_integrable
      intro omega
      exact (Real.rpow_le_rpow (z := harperTwoThird)
        (hW_nonneg omega) (hdecomp omega)
          (by norm_num [harperTwoThird])).trans
        (Real.rpow_add_le_add_rpow (p := harperTwoThird)
          (Finset.sum_nonneg fun i hi ↦ mul_nonneg
            (harperKernelShellCoefficient_nonneg _)
            (hlocal i.2 i.1 (Finset.mem_range.mp
              (Finset.mem_product.mp hi).1) omega))
          (hremainder_nonneg omega)
          (by norm_num [harperTwoThird]) (by norm_num [harperTwoThird]))
    _ = (∫ omega,
          truncatedHarperTwoSidedAssembly M localEnergy omega ^
            harperTwoThird ∂ν) +
        ∫ omega, remainder omega ^ harperTwoThird ∂ν := by
      exact integral_add hassembly_integrable hremainder_integrable
    _ ≤ 2 * A * 4 ^ harperTwoThird *
          ∑ n ∈ Finset.range M, harperGlobalMomentSeriesTerm n + R :=
      add_le_add
        (integral_truncatedHarperTwoSidedAssembly_twoThird_le
          M localEnergy hlocal hintegrable hmoment)
        hremainder_moment

/-- The independent-cutoff Harper energy is integrable. -/
theorem integrable_harperInitialNormalizedEnergy (y : ℕ) :
    Integrable (harperInitialNormalizedEnergy y) μ := by
  unfold harperInitialNormalizedEnergy
  simpa only [mul_div_assoc] using!
    ((integrable_smoothEnergy y).div_const (Real.log (y : ℝ))).const_mul
      (2 * Real.pi)

/-- Consequently its positive `2/3` moment is integrable for every `y > 1`. -/
theorem integrable_harperInitialNormalizedEnergy_twoThird
    {y : ℕ} (hy : 1 < y) :
    Integrable (fun omega ↦
      harperInitialNormalizedEnergy y omega ^ harperTwoThird) μ := by
  apply integrable_rpow_of_integrable_nonneg
    (integrable_harperInitialNormalizedEnergy y)
  · intro omega
    rw [← caichNormalizedEnergy_initial_eq_harper 1 1 y hy omega]
    exact caichNormalizedEnergy_nonneg hy omega
  · norm_num [harperTwoThird]
  · norm_num [harperTwoThird]

/-- Specialization of the exact-remainder theorem to the existing
`smoothEnergy`/`harperInitialNormalizedEnergy` definition. -/
theorem integral_harperInitialNormalizedEnergy_twoThird_le_of_localIntervals
    {A R : ℝ} {y M : ℕ} (hy : 1 < y)
    (localEnergy : Bool → ℕ → Omega → ℝ) (remainder : Omega → ℝ)
    (hlocal : ∀ d n, n < M → ∀ omega, 0 ≤ localEnergy d n omega)
    (hmeasurable : ∀ d n, n < M →
      AEStronglyMeasurable (localEnergy d n) μ)
    (hintegrable : ∀ d n, n < M →
      Integrable (fun omega ↦ localEnergy d n omega ^ harperTwoThird) μ)
    (hmoment : ∀ d n, n < M →
      (∫ omega, localEnergy d n omega ^ harperTwoThird ∂μ) ≤
        A * harperLocalMomentLoss n)
    (hremainder_nonneg : ∀ omega, 0 ≤ remainder omega)
    (hremainder_integrable :
      Integrable (fun omega ↦ remainder omega ^ harperTwoThird) μ)
    (hremainder_moment :
      (∫ omega, remainder omega ^ harperTwoThird ∂μ) ≤ R)
    (hdecomp : ∀ omega,
      harperInitialNormalizedEnergy y omega ≤
        truncatedHarperTwoSidedAssembly M localEnergy omega +
          remainder omega) :
    (∫ omega,
        harperInitialNormalizedEnergy y omega ^ harperTwoThird ∂μ) ≤
      2 * A * 4 ^ harperTwoThird *
          ∑ n ∈ Finset.range M, harperGlobalMomentSeriesTerm n + R := by
  apply integral_twoThird_le_twoSidedAssembly_add_remainder
    M (harperInitialNormalizedEnergy y) localEnergy remainder
  · intro omega
    rw [← caichNormalizedEnergy_initial_eq_harper 1 1 y hy omega]
    exact caichNormalizedEnergy_nonneg hy omega
  · exact integrable_harperInitialNormalizedEnergy_twoThird hy
  · exact hlocal
  · exact hmeasurable
  · exact hintegrable
  · exact hmoment
  · exact hremainder_nonneg
  · exact hremainder_integrable
  · exact hremainder_moment
  · exact hdecomp

end Erdos.Problem520
