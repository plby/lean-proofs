/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierTotientCutoffLimit
import ErdosProblems.Erdos4b.GeneralFourierKernelTail

/-!
# Scaled totient kernel and its uniform measurable correction

The local correction is measurable even where its denominator vanishes.
On the positive exponent half-plane that denominator does not vanish,
so the exact product factorization and the uniform error estimate apply.
-/

namespace Erdos4b

noncomputable section

open Filter MeasureTheory
open scoped BigOperators Topology

def doubledFourierTotientCorrection {ι : Type*} [Fintype ι]
    (w : ℕ) (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (L : (ι ⊕ ι) → ℝ) (ξ : ((ι ⊕ ι) × Bool) → ℝ) : ℂ :=
  ∏' p : Nat.Primes, roughTotientFourierCorrection w
    (doubledFourierPrimeNumerator edges companion
      (doubledFourierTensorExponents (fun i _ ↦ L i) ξ)) p

def normalizedTotientDoubledFourierKernel {ι : Type*} [Fintype ι]
    (w : ℕ) (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    (L : (ι ⊕ ι) → ℝ) (ξ : ((ι ⊕ ι) × Bool) → ℝ) : ℂ :=
  doubledFourierNormalization w edges companion L *
    ∏' p : Nat.Primes, roughTotientDoubledFourierPrimeFactor w edges companion
      (doubledFourierTensorExponents (fun i _ ↦ L i) ξ) p

theorem continuous_doubledFourierPrimeNumerator
    {ι : Type*} [Fintype ι] (edges : ℕ → Finset (ι × ι))
    (companion : ℕ → Bool) (p : ℕ) :
    Continuous (fun s : (ι ⊕ ι) → Bool → ℂ ↦
      doubledFourierPrimeNumerator edges companion s p) := by
  unfold doubledFourierPrimeNumerator doubledFourierLocalPolynomial
    selbergPairPolynomial primeFourierPower
  split_ifs <;> fun_prop

theorem stronglyMeasurable_doubledFourierTotientCorrection
    {ι : Type*} [Fintype ι] (w : ℕ) (edges : ℕ → Finset (ι × ι))
    (companion : ℕ → Bool) (L : (ι ⊕ ι) → ℝ) :
    StronglyMeasurable (doubledFourierTotientCorrection w edges companion L) := by
  apply StronglyMeasurable.tprod
  intro p
  have ha := ((continuous_doubledFourierPrimeNumerator edges companion p).comp
    (continuous_doubledFourierTensorExponents (fun i _ ↦ L i))).measurable
  unfold roughTotientFourierCorrection totientFourierLocalCorrection
  split_ifs
  · exact ((measurable_const.add (ha.div_const _)).div
      (measurable_const.add (ha.div_const _))).stronglyMeasurable
  · exact stronglyMeasurable_const

theorem normalizedTotientDoubledFourierKernel_eq_correction_mul
    {ι : Type*} [Fintype ι] (w : ℕ) (edges : ℕ → Finset (ι × ι))
    (companion : ℕ → Bool) (L : (ι ⊕ ι) → ℝ) (hL : ∀ i, 0 < L i)
    (hw : 2 * (Fintype.card (NonemptyDoubledPrimeChoice ι) : ℝ) ≤ w)
    (ξ : ((ι ⊕ ι) × Bool) → ℝ) :
    normalizedTotientDoubledFourierKernel w edges companion L ξ =
      doubledFourierTotientCorrection w edges companion L ξ *
        normalizedDoubledFourierKernel w edges companion L ξ := by
  obtain ⟨σ, hσ, hscale⟩ := exists_doubledFourierTensor_halfPlane
    (fun i _ ↦ L i) (fun i _ ↦ hL i)
  have hprod := hasProd_roughTotientDoubledFourierPrimeFactor edges companion
    (doubledFourierTensorExponents (fun i _ ↦ L i) ξ) hw hσ
    (fun i b ↦ by rw [doubledFourierTensorExponents_re]; exact hscale i b)
  unfold normalizedTotientDoubledFourierKernel normalizedDoubledFourierKernel
    doubledFourierTotientCorrection
  rw [hprod.tprod_eq]
  ring

theorem norm_doubledFourierTotientCorrection_sub_one_le
    {ι : Type*} [Fintype ι] (w : ℕ) (edges : ℕ → Finset (ι × ι))
    (companion : ℕ → Bool) (L : (ι ⊕ ι) → ℝ) (hL : ∀ i, 0 < L i)
    (hw0 : 0 < w) (hw : 2 * (Fintype.card (NonemptyDoubledPrimeChoice ι) : ℝ) ≤ w)
    (ξ : ((ι ⊕ ι) × Bool) → ℝ) :
    ‖doubledFourierTotientCorrection w edges companion L ξ - 1‖ ≤
      Real.exp (8 * (Fintype.card (NonemptyDoubledPrimeChoice ι) : ℝ) / w) - 1 := by
  apply norm_tprod_totientDoubledFourierCorrection_sub_one_le _ _ _ hw0 hw
  intro i b
  rw [doubledFourierTensorExponents_re]
  exact (inv_pos.mpr (hL i)).le

theorem tendsto_totientFourierUniformError_zero
    {α : Type*} {l : Filter α} (D : ℕ) (w : α → ℕ) (hw : Tendsto w l atTop) :
    Tendsto (fun a ↦ Real.exp (8 * (D : ℝ) / w a) - 1) l (𝓝 0) := by
  have hdiv : Tendsto (fun a ↦ 8 * (D : ℝ) / w a) l (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hw)
  simpa only [Function.comp_def, Real.exp_zero, sub_self] using
    ((Real.continuous_exp.tendsto 0).comp hdiv).sub_const 1

end

end Erdos4b
