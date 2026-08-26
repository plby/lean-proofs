import ErdosProblems.Erdos1002.FixedAwayPVDecayBV

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-! # Sampling a real-line BV profile on the integers -/

open Filter MeasureTheory Set Finset
open scoped BigOperators Real

namespace Erdos1002

noncomputable section

def integerSampleVariation (f : ℝ → ℂ) (n : ℤ) : ℝ :=
  ‖f (n : ℝ) - f ((n : ℝ) + 1)‖

theorem integerSampleVariation_le_intervalIntegral
    (f : ℝ → ℂ) (hf : ∀ x, DifferentiableAt ℝ f x)
    (hderiv : Integrable (fun x ↦ ‖deriv f x‖)) (n : ℤ) :
    integerSampleVariation f n ≤
      ∫ x in (n : ℝ)..((n : ℝ) + 1), ‖deriv f x‖ := by
  have hn : (n : ℝ) ≤ (n : ℝ) + 1 := by norm_num
  have hFTC :
      ∫ x in (n : ℝ)..((n : ℝ) + 1), deriv f x =
        f ((n : ℝ) + 1) - f (n : ℝ) := by
    have hderiv' : Integrable (deriv f) :=
      ((integrable_norm_iff
        (measurable_deriv f).aestronglyMeasurable).mp hderiv)
    exact intervalIntegral.integral_deriv_eq_sub
      (fun x _hx ↦ hf x)
      hderiv'.intervalIntegrable
  unfold integerSampleVariation
  calc
    ‖f (n : ℝ) - f ((n : ℝ) + 1)‖ =
        ‖∫ x in (n : ℝ)..((n : ℝ) + 1), deriv f x‖ := by
      rw [hFTC]
      rw [show f (n : ℝ) - f ((n : ℝ) + 1) =
        -(f ((n : ℝ) + 1) - f (n : ℝ)) by abel,
        norm_neg]
    _ ≤ ∫ x in (n : ℝ)..((n : ℝ) + 1), ‖deriv f x‖ :=
      intervalIntegral.norm_integral_le_integral_norm hn

theorem summable_integerSampleVariation
    (f : ℝ → ℂ) (hf : ∀ x, DifferentiableAt ℝ f x)
    (hderiv : Integrable (fun x ↦ ‖deriv f x‖)) :
    Summable (integerSampleVariation f) := by
  have hsum := hderiv.hasSum_intervalIntegral (0 : ℝ)
  simp only [zero_add] at hsum
  exact hsum.summable.of_nonneg_of_le
    (fun n ↦ norm_nonneg _)
    (integerSampleVariation_le_intervalIntegral f hf hderiv)

theorem tsum_integerSampleVariation_le_integral_norm_deriv
    (f : ℝ → ℂ) (hf : ∀ x, DifferentiableAt ℝ f x)
    (hderiv : Integrable (fun x ↦ ‖deriv f x‖)) :
    (∑' n : ℤ, integerSampleVariation f n) ≤
      ∫ x : ℝ, ‖deriv f x‖ := by
  have hsum := hderiv.hasSum_intervalIntegral (0 : ℝ)
  simp only [zero_add] at hsum
  exact (summable_integerSampleVariation f hf hderiv).tsum_le_tsum
    (integerSampleVariation_le_intervalIntegral f hf hderiv)
    hsum.summable |>.trans_eq hsum.tsum_eq

def singleJumpCharge (x q : ℝ) (n : ℤ) : ℝ :=
  (if n = ⌊x⌋ then q else 0) +
    (if n = ⌊x⌋ - 1 then q else 0)

def finiteJumpCharge (J : Finset ℝ) (c : ℝ → ℝ) (n : ℤ) : ℝ :=
  J.sum fun x ↦ singleJumpCharge x (c x) n

theorem summable_finiteJumpCharge (J : Finset ℝ) (c : ℝ → ℝ) :
    Summable (finiteJumpCharge J c) := by
  induction J using Finset.induction with
  | empty =>
      change Summable (fun _n : ℤ ↦ (0 : ℝ))
      exact summable_zero
  | @insert x J hx ih =>
      rw [show finiteJumpCharge (insert x J) c = fun n ↦
          singleJumpCharge x (c x) n + finiteJumpCharge J c n by
        funext n
        simp [finiteJumpCharge, hx]]
      have hxsum := (hasSum_ite_eq (⌊x⌋ : ℤ) (c x)).add
        (hasSum_ite_eq (⌊x⌋ - 1 : ℤ) (c x))
      exact ((show Summable (singleJumpCharge x (c x)) by
        simpa only [singleJumpCharge] using! hxsum.summable).add ih)

theorem tsum_finiteJumpCharge
    (J : Finset ℝ) (c : ℝ → ℝ) :
    (∑' n : ℤ, finiteJumpCharge J c n) = 2 * J.sum c := by
  induction J using Finset.induction with
  | empty => simp [finiteJumpCharge]
  | @insert x J hx ih =>
      have hxsum : HasSum
          (singleJumpCharge x (c x)) (c x + c x) := by
        unfold singleJumpCharge
        exact
        (hasSum_ite_eq (⌊x⌋ : ℤ) (c x)).add
          (hasSum_ite_eq (⌊x⌋ - 1 : ℤ) (c x))
      rw [show finiteJumpCharge (insert x J) c = fun n ↦
          singleJumpCharge x (c x) n +
            finiteJumpCharge J c n by
        funext n
        simp [finiteJumpCharge, hx]]
      rw [hxsum.summable.tsum_add (summable_finiteJumpCharge J c),
        hxsum.tsum_eq, ih, Finset.sum_insert hx]
      ring

theorem summable_integerSampleVariation_of_jump_charge
    (f : ℝ → ℂ) (g q : ℤ → ℝ)
    (hg : Summable g) (hq : Summable q)
    (hcell : ∀ n, integerSampleVariation f n ≤ g n + q n) :
    Summable (integerSampleVariation f) := by
  exact (hg.add hq).of_nonneg_of_le (fun n ↦ norm_nonneg _) hcell

theorem tsum_integerSampleVariation_le_of_jump_charge
    (f : ℝ → ℂ) (g q : ℤ → ℝ)
    (hg : Summable g) (hq : Summable q)
    (hcell : ∀ n, integerSampleVariation f n ≤ g n + q n) :
    (∑' n : ℤ, integerSampleVariation f n) ≤
      (∑' n : ℤ, g n) + ∑' n : ℤ, q n := by
  have hv := summable_integerSampleVariation_of_jump_charge
    f g q hg hq hcell
  exact (hv.tsum_le_tsum hcell (hg.add hq)).trans_eq (hg.tsum_add hq)

end

end Erdos1002
