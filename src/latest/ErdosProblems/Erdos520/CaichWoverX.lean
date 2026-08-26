import ErdosProblems.Erdos520.CaichAuxiliaryMomentTail
import ErdosProblems.Erdos520.CaichConcreteAuxiliaryAssembly
import ErdosProblems.Erdos520.CaichHypercontractive
import ErdosProblems.Erdos520.MinkowskiIntegral
import ErdosProblems.Erdos520.OrthogonalMaximal
import ErdosProblems.Erdos520.AlignedSmoothContribution
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Filter Finset MeasureTheory Set
open scoped BigOperators ENNReal Interval Topology

namespace Erdos
namespace Problem520

/-!
# The short-interval `W/x` auxiliary

This file isolates the exact probabilistic and arithmetic content of
Proposition 2 in Caich's argument.  For a prime `p` and a point
`p < t <= p(1+1/X)`, the difference of the two smooth sums is represented by
its literal short support.  Orthogonality controls its second moment and the
already proved finite Bonami inequality controls its high moment with the
weight `tau_(4r-3)`.

The final arithmetic input is deliberately stated as a bound for an explicit
prime/integral divisor-energy budget.  Thus it cannot conceal either a
probabilistic assertion or the desired conclusion.  The Markov step uses the
common wrapper in `CaichAuxiliaryMomentTail`; in particular there is no
spurious factor involving `T(ell)^(-r)`.
-/

/-! ## The exact short support -/

/-- Integers present at the endpoint `x/p` but absent at the real cutoff
`x/t`, with the same strict prime cutoff `p`. -/
noncomputable def caichWShortSupport (x p : ℕ) (t : ℝ) : Finset ℕ :=
  Nat.smoothNumbersUpTo (x / p) p \
    Nat.smoothNumbersUpTo (Nat.floor ((x : ℝ) / t)) p

/-- The smooth cutoff at `x/t` lies below the endpoint cutoff at `x/p`
whenever `p <= t`. -/
theorem caichW_floor_div_le_nat_div
    (x p : ℕ) {t : ℝ} (hp : 0 < p) (hpt : (p : ℝ) ≤ t) :
    Nat.floor ((x : ℝ) / t) ≤ x / p := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hdiv : (x : ℝ) / t ≤ (x : ℝ) / (p : ℝ) :=
    div_le_div_of_nonneg_left (by positivity) hpR hpt
  have hfloor := Nat.floor_mono hdiv
  simpa only [Nat.floor_div_natCast, Nat.floor_natCast] using! hfloor

theorem caichW_lowerSmooth_subset_upper
    (x p : ℕ) {t : ℝ} (hp : 0 < p) (hpt : (p : ℝ) ≤ t) :
    Nat.smoothNumbersUpTo (Nat.floor ((x : ℝ) / t)) p ⊆
      Nat.smoothNumbersUpTo (x / p) p := by
  intro n hn
  rw [Nat.mem_smoothNumbersUpTo] at hn ⊢
  exact ⟨hn.1.trans (caichW_floor_div_le_nat_div x p hp hpt), hn.2⟩

/-- The analytic difference occurring in `W`. -/
noncomputable def caichWShortDifference
    (x p : ℕ) (t : ℝ) (omega : Omega) : ℝ :=
  Ψ' omega (x / p) p -
    caichStrictSmoothReal omega ((x : ℝ) / t) p

/-- On the short interval the difference is exactly the RMF sum over the
literal set difference above. -/
theorem caichWShortDifference_eq_sum
    (x p : ℕ) {t : ℝ} (hp : 0 < p) (hpt : (p : ℝ) ≤ t)
    (omega : Omega) :
    caichWShortDifference x p t omega =
      ∑ n ∈ caichWShortSupport x p t, f omega n := by
  unfold caichWShortDifference caichStrictSmoothReal ΨReal Ψ'
    caichWShortSupport Ψ
  rw [Finset.sum_sdiff_eq_sub
    (caichW_lowerSmooth_subset_upper x p hp hpt)]
  rw [Nat.sub_add_cancel hp]

/-- Every short-support integer is positive and at most `x/p`. -/
theorem caichWShortSupport_subset_Ioc (x p : ℕ) (t : ℝ) :
    caichWShortSupport x p t ⊆ Finset.Ioc 0 (x / p) := by
  intro n hn
  have hupper : n ∈ Nat.smoothNumbersUpTo (x / p) p :=
    Finset.sdiff_subset hn
  rw [Nat.mem_smoothNumbersUpTo] at hupper
  exact Finset.mem_Ioc.mpr
    ⟨Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers hupper.2), hupper.1⟩

/-! ## Measurability and finite moments -/

set_option maxHeartbeats 800000 in
theorem measurable_caichWShortDifference (x : ℕ) {p : ℕ} (hp : 0 < p) :
    Measurable fun u : ℝ × Omega ↦
      caichWShortDifference x p u.1 u.2 := by
  have hfirst : Measurable fun u : ℝ × Omega ↦ Ψ' u.2 (x / p) p := by
    have hΨ : Measurable fun omega : Omega ↦ Ψ' omega (x / p) p := by
      simpa only [Ψ'_eq_Ψ_pred _ (x / p) hp] using!
        (((stronglyMeasurable_Ψ_filtration (x / p) (p - 1)).mono
          (εFiltration.le (p - 1))).measurable)
    exact hΨ.comp measurable_snd
  have hsecond : Measurable fun u : ℝ × Omega ↦
      caichStrictSmoothReal u.2 ((x : ℝ) / u.1) p := by
    change Measurable fun u : ℝ × Omega ↦
      ΨReal u.2 ((x : ℝ) / u.1) (p - 1)
    exact (measurable_ΨReal_joint (p - 1)).comp
      ((measurable_const.div measurable_fst).prodMk measurable_snd)
  exact hfirst.sub hsecond

theorem measurable_caichWShortKernel (x : ℕ) {p : ℕ} (hp : 0 < p) :
    Measurable fun u : ℝ × Omega ↦
      |caichWShortDifference x p u.1 u.2| ^ 2 :=
  (measurable_caichWShortDifference x hp).abs.pow_const 2

/-- A deliberately crude uniform bound used only to establish finite
moments and justify the Bochner integrals. -/
noncomputable def caichWShortUniformBound (x p : ℕ) : ℝ :=
  (squarefreeSmoothSets (x / p) (p - 1)).card +
    ((p - 1 + 1).primesBelow.powerset.card : ℝ)

theorem abs_caichWShortDifference_le
    (x : ℕ) {p : ℕ} (hp : 0 < p) (t : ℝ) (omega : Omega) :
    |caichWShortDifference x p t omega| ≤
      caichWShortUniformBound x p := by
  have hfirst : |Ψ' omega (x / p) p| ≤
      (squarefreeSmoothSets (x / p) (p - 1)).card := by
    rw [Ψ'_eq_Ψ_pred omega (x / p) hp]
    simpa only [Real.norm_eq_abs] using!
      norm_Ψ_le_card omega (x / p) (p - 1)
  have hsecond := abs_caichStrictSmoothReal_le omega ((x : ℝ) / t) p
  unfold caichWShortDifference caichWShortUniformBound
  exact (abs_sub _ _).trans (add_le_add hfirst hsecond)

theorem integrable_caichWShortKernel_pow
    (x : ℕ) {p q : ℕ} (hp : 0 < p) (t : ℝ) :
    Integrable (fun omega ↦
      |caichWShortDifference x p t omega| ^ (2 * q)) μ := by
  have hmeas : Measurable fun omega : Omega ↦
      |caichWShortDifference x p t omega| ^ (2 * q) :=
    (measurable_caichWShortDifference x hp).comp
      (measurable_const.prodMk measurable_id) |>.abs.pow_const (2 * q)
  apply Integrable.of_bound hmeas.aestronglyMeasurable
    (caichWShortUniformBound x p ^ (2 * q))
  exact ae_of_all μ fun omega ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
    exact pow_le_pow_left₀ (abs_nonneg _)
      (abs_caichWShortDifference_le x hp t omega) _

theorem memLp_abs_caichWShortDifference_pow
    (x : ℕ) {p : ℕ} (hp : 0 < p) (t : ℝ) (k : ℕ)
    (q : ℝ≥0∞) :
    MemLp (fun omega ↦ |caichWShortDifference x p t omega| ^ k) q μ := by
  have hmeas : Measurable fun omega : Omega ↦
      |caichWShortDifference x p t omega| ^ k :=
    (measurable_caichWShortDifference x hp).comp
      (measurable_const.prodMk measurable_id) |>.abs.pow_const k
  apply MemLp.of_bound hmeas.aestronglyMeasurable
    (caichWShortUniformBound x p ^ k)
  exact ae_of_all μ fun omega ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
    exact pow_le_pow_left₀ (abs_nonneg _)
      (abs_caichWShortDifference_le x hp t omega) _

/-! ## Orthogonality and the `tau_(4r-3)` high moment -/

/-- Exact second moment for an arbitrary finite RMF support. -/
theorem integral_sq_sum_f_finset (s : Finset ℕ) :
    ∫ omega, (∑ n ∈ s, f omega n) ^ 2 ∂μ =
      ∑ n ∈ s, if Squarefree n then 1 else 0 := by
  rw [show (fun omega : Omega ↦ (∑ n ∈ s, f omega n) ^ 2) =
      fun omega ↦ ∑ m ∈ s, ∑ n ∈ s, f omega m * f omega n by
    funext omega
    rw [pow_two, Finset.sum_mul_sum],
    integral_finset_sum s (fun m _ ↦
      integrable_finset_sum s fun n _ ↦ integrable_f_mul_f m n)]
  apply Finset.sum_congr rfl
  intro m hm
  rw [integral_finset_sum s
    (fun n _ ↦ integrable_f_mul_f m n)]
  by_cases hsq : Squarefree m
  · rw [if_pos hsq]
    have hdiag :
        (∫ omega, f omega m * f omega m ∂μ) = 1 := by
      rw [integral_f_mul_f]
      simp [hsq]
    rw [← hdiag]
    apply Finset.sum_eq_single m
    · intro n hn hne
      rw [integral_f_mul_f, if_neg]
      exact fun h ↦ hne h.2.2.symm
    · exact fun h ↦ (h hm).elim
  · rw [if_neg hsq]
    apply Finset.sum_eq_zero
    intro n hn
    rw [integral_f_mul_f]
    simp [hsq]

theorem integral_sq_sum_f_finset_le_card (s : Finset ℕ) :
    ∫ omega, (∑ n ∈ s, f omega n) ^ 2 ∂μ ≤ s.card := by
  rw [integral_sq_sum_f_finset]
  calc
    (∑ n ∈ s, if Squarefree n then 1 else 0) ≤
        ∑ _n ∈ s, (1 : ℝ) := by
      gcongr with n hn
      split_ifs <;> norm_num
    _ = s.card := by simp

/-- The explicit divisor energy in the short interval. -/
noncomputable def caichWShortDivisorEnergy
    (r x p : ℕ) (t : ℝ) : ℝ :=
  ∑ n ∈ caichWShortSupport x p t,
    (orderedDivisorCount (4 * r - 3) n : ℝ)

/-- Bonami at exponent `2(2r-1)` gives exactly the weight
`tau_(4r-3)`. -/
theorem caichWShort_highMoment_root_le
    (r x : ℕ) {p : ℕ} (hr : 1 ≤ r) (hp : 0 < p)
    {t : ℝ} (hpt : (p : ℝ) ≤ t) :
    (∫ omega, |caichWShortDifference x p t omega| ^
        (2 * (2 * r - 1)) ∂μ) ^ (1 / ((2 * r - 1 : ℕ) : ℝ)) ≤
      caichWShortDivisorEnergy r x p t := by
  let q : ℕ := 2 * r - 1
  have hq : 1 ≤ q := by omega
  have hsub := caichWShortSupport_subset_Ioc x p t
  have hhyper := caichFiniteRMFSum_hypercontractive q hq (x / p)
    (caichWShortSupport x p t) (fun _ ↦ 1) hsub
  simp only [caichFiniteRMFSum_one, one_pow, mul_one] at hhyper
  simp_rw [caichWShortDifference_eq_sum x p hp hpt]
  simpa only [q, caichWShortDivisorEnergy,
    show 2 * (2 * r - 1) - 1 = 4 * r - 3 by omega] using! hhyper

/-- Raw form of the preceding high-moment estimate. -/
theorem caichWShort_highMoment_le
    (r x : ℕ) {p : ℕ} (hr : 1 ≤ r) (hp : 0 < p)
    {t : ℝ} (hpt : (p : ℝ) ≤ t) :
    (∫ omega, |caichWShortDifference x p t omega| ^
        (2 * (2 * r - 1)) ∂μ) ≤
      caichWShortDivisorEnergy r x p t ^ (2 * r - 1) := by
  let I : ℝ := ∫ omega, |caichWShortDifference x p t omega| ^
    (2 * (2 * r - 1)) ∂μ
  let E : ℝ := caichWShortDivisorEnergy r x p t
  have hI : 0 ≤ I := integral_nonneg fun _ ↦ by positivity
  have hroot : I ^ (1 / ((2 * r - 1 : ℕ) : ℝ)) ≤ E := by
    simpa only [I, E] using! caichWShort_highMoment_root_le r x hr hp hpt
  have hpow := pow_le_pow_left₀ (Real.rpow_nonneg hI _) hroot (2 * r - 1)
  have hq0 : 2 * r - 1 ≠ 0 := by omega
  simpa only [I, E, one_div, Real.rpow_inv_natCast_pow hI hq0] using! hpow

/-- The exact root budget obtained by the source's Cauchy--Schwarz
interpolation between moments `2` and `2(2r-1)`. -/
noncomputable def caichWShortMomentRootBudget
    (r x p : ℕ) (t : ℝ) : ℝ :=
  (Real.sqrt (caichWShortSupport x p t).card *
      Real.sqrt (caichWShortDivisorEnergy r x p t ^ (2 * r - 1))) ^
    (1 / (r : ℝ))

/-- Cauchy--Schwarz between the exact second moment and the
`tau_(4r-3)` high moment.  This is the `2r` short-interval moment in the
source proof. -/
theorem caichWShort_moment_root_le
    (r x : ℕ) {p : ℕ} (hr : 1 ≤ r) (hp : 0 < p)
    {t : ℝ} (hpt : (p : ℝ) ≤ t) :
    (∫ omega, |caichWShortDifference x p t omega| ^ (2 * r) ∂μ) ^
        (1 / (r : ℝ)) ≤ caichWShortMomentRootBudget r x p t := by
  let D : Omega → ℝ := fun omega ↦
    |caichWShortDifference x p t omega|
  let I₂ : ℝ := ∫ omega, D omega ^ 2 ∂μ
  let Ihi : ℝ := ∫ omega, D omega ^ (2 * (2 * r - 1)) ∂μ
  let C : ℝ := ((caichWShortSupport x p t).card : ℝ)
  let E : ℝ := caichWShortDivisorEnergy r x p t
  have hholder :
      (∫ omega, D omega ^ (2 * r) ∂μ) ≤
        Real.sqrt I₂ * Real.sqrt Ihi := by
    have hmem₁ : MemLp D (ENNReal.ofReal 2) μ := by
      simpa only [D, pow_one, ENNReal.ofReal_ofNat] using!
        (memLp_abs_caichWShortDifference_pow x hp t 1 2)
    have hmemhi : MemLp (fun omega ↦ D omega ^ (2 * r - 1))
        (ENNReal.ofReal 2) μ := by
      simpa only [D, ENNReal.ofReal_ofNat] using!
        (memLp_abs_caichWShortDifference_pow x hp t (2 * r - 1) 2)
    have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg
      (f := D) (g := fun omega ↦ D omega ^ (2 * r - 1))
      (p := (2 : ℝ)) (q := (2 : ℝ)) (μ := μ)
      (Real.holderConjugate_iff.mpr (by norm_num))
      (Eventually.of_forall fun omega ↦ abs_nonneg _)
      (Eventually.of_forall fun omega ↦ pow_nonneg (abs_nonneg _) _)
      hmem₁ hmemhi
    have hleft : (fun omega ↦ D omega ^ (2 * r)) =
        fun omega ↦ D omega * D omega ^ (2 * r - 1) := by
      funext omega
      rw [← pow_succ']
      congr 1
      omega
    rw [hleft]
    simpa only [D, I₂, Ihi, Real.rpow_two, ← Real.sqrt_eq_rpow,
      one_mul, pow_one, ← pow_mul, Nat.mul_comm] using! hcs
  have hsecond : I₂ ≤ C := by
    have h := integral_sq_sum_f_finset_le_card
      (caichWShortSupport x p t)
    simp_rw [← caichWShortDifference_eq_sum x p hp hpt] at h
    simpa only [D, I₂, C, sq_abs] using! h
  have hhigh : Ihi ≤ E ^ (2 * r - 1) := by
    simpa only [D, Ihi, E] using! caichWShort_highMoment_le r x hr hp hpt
  have hraw :
      (∫ omega, D omega ^ (2 * r) ∂μ) ≤
        Real.sqrt C * Real.sqrt (E ^ (2 * r - 1)) :=
    hholder.trans (mul_le_mul (Real.sqrt_le_sqrt hsecond)
      (Real.sqrt_le_sqrt hhigh) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have hleft_nonneg : 0 ≤ ∫ omega, D omega ^ (2 * r) ∂μ :=
    integral_nonneg fun omega ↦ pow_nonneg (abs_nonneg _) _
  have hexp : 0 ≤ 1 / (r : ℝ) := by positivity
  unfold caichWShortMomentRootBudget
  exact Real.rpow_le_rpow hleft_nonneg hraw hexp

/-! ## Integral Minkowski for one prime and for the finite prime sum -/

/-- The nonnegative squared-difference kernel whose short average is one
prime's contribution to `W`. -/
noncomputable def caichWShortKernel
    (x p : ℕ) (t : ℝ) (omega : Omega) : ℝ :=
  |caichWShortDifference x p t omega| ^ 2

noncomputable def caichWPrimeContribution
    (X : ℝ) (x p : ℕ) (omega : Omega) : ℝ :=
  caichShortPrimeAverage X p (fun t ↦ caichWShortKernel x p t omega)

theorem caichInitialSmoothingError_eq_sum_primeContributions
    (X : ℝ) (omega : Omega) (x a b : ℕ) :
    caichInitialSmoothingError X omega x a b =
      ∑ p ∈ freshPrimes a b, caichWPrimeContribution X x p omega := by
  rfl

theorem caichWShortKernel_nonneg
    (x p : ℕ) (t : ℝ) (omega : Omega) :
    0 ≤ caichWShortKernel x p t omega := by
  exact sq_nonneg _

theorem caichWPrimeContribution_nonneg
    {X : ℝ} (hX : 0 < X) (x : ℕ) {p : ℕ} (hp : 0 < p)
    (omega : Omega) :
    0 ≤ caichWPrimeContribution X x p omega := by
  exact caichShortPrimeAverage_nonneg hX hp _
    (fun t ↦ caichWShortKernel_nonneg x p t omega)

noncomputable def caichWPrimeUniformBound
    (X : ℝ) (x p : ℕ) : ℝ :=
  |X / (p : ℝ)| *
    (caichWShortUniformBound x p ^ 2 *
      |(p : ℝ) * (1 + 1 / X) - (p : ℝ)|)

theorem norm_caichWPrimeContribution_le
    (X : ℝ) (x : ℕ) {p : ℕ} (hp : 0 < p) (omega : Omega) :
    ‖caichWPrimeContribution X x p omega‖ ≤
      caichWPrimeUniformBound X x p := by
  unfold caichWPrimeContribution caichShortPrimeAverage
    caichWPrimeUniformBound caichWShortKernel
  rw [norm_mul, Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (abs_nonneg _)
    (abs_caichWShortDifference_le x hp t omega) 2

set_option maxHeartbeats 800000 in
theorem measurable_caichWPrimeContribution
    {X : ℝ} (hX : 0 < X) (x : ℕ) {p : ℕ} (hp : 0 < p) :
    Measurable fun omega ↦ caichWPrimeContribution X x p omega := by
  let q : ℝ := (p : ℝ) * (1 + 1 / X)
  have hpq : (p : ℝ) ≤ q := by
    have hinv : 0 ≤ 1 / X := by positivity
    dsimp only [q]
    have hpR : (0 : ℝ) ≤ (p : ℝ) := by positivity
    nlinarith
  have hkernel : Measurable fun u : ℝ × Omega ↦
      caichWShortKernel x p u.1 u.2 := by
    simpa only [caichWShortKernel] using! measurable_caichWShortKernel x hp
  have hswap : StronglyMeasurable fun u : Omega × ℝ ↦
      caichWShortKernel x p u.2 u.1 :=
    (hkernel.comp measurable_swap).stronglyMeasurable
  have hint : StronglyMeasurable fun omega ↦
      ∫ t in Set.Ioc (p : ℝ) q, caichWShortKernel x p t omega :=
    hswap.integral_prod_right'
      (ν := volume.restrict (Set.Ioc (p : ℝ) q))
  unfold caichWPrimeContribution caichShortPrimeAverage
  have heq : (fun omega ↦
      (X / (p : ℝ)) * ∫ t in (p : ℝ)..q,
        caichWShortKernel x p t omega) =
      fun omega ↦ (X / (p : ℝ)) *
        ∫ t in Set.Ioc (p : ℝ) q,
          caichWShortKernel x p t omega := by
    funext omega
    rw [intervalIntegral.integral_of_le hpq]
  rw [heq]
  exact measurable_const.mul hint.measurable

theorem memLp_caichWPrimeContribution
    {X : ℝ} (hX : 0 < X) (x : ℕ) {p : ℕ} (hp : 0 < p)
    (q : ℝ≥0∞) :
    MemLp (caichWPrimeContribution X x p) q μ := by
  apply MemLp.of_bound
    (measurable_caichWPrimeContribution hX x hp).aestronglyMeasurable
    (caichWPrimeUniformBound X x p)
  exact ae_of_all μ (norm_caichWPrimeContribution_le X x hp)

theorem integrable_caichWPrimeContribution_pow
    {X : ℝ} (hX : 0 < X) (x : ℕ) {p r : ℕ}
    (hp : 0 < p) (hr : 0 < r) :
    Integrable (fun omega ↦ caichWPrimeContribution X x p omega ^ r) μ := by
  have hmem := memLp_caichWPrimeContribution hX x hp (r : ℝ≥0∞)
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (caichWPrimeContribution_nonneg hX x hp _)] using!
      hmem.integrable_norm_pow (Nat.ne_of_gt hr)

theorem measurable_caichWShortMomentRootBudget
    {r : ℕ} (hr : 0 < r) (x p : ℕ) :
    Measurable fun t ↦ caichWShortMomentRootBudget r x p t := by
  let B : ℕ → ℝ := fun z ↦
    (Real.sqrt
        ((Nat.smoothNumbersUpTo (x / p) p \
          Nat.smoothNumbersUpTo z p).card : ℝ) *
      Real.sqrt
        ((∑ n ∈ (Nat.smoothNumbersUpTo (x / p) p \
            Nat.smoothNumbersUpTo z p),
              (orderedDivisorCount (4 * r - 3) n : ℝ)) ^
          (2 * r - 1))) ^ (1 / (r : ℝ))
  have hB : Measurable B := measurable_of_countable B
  have hfloor : Measurable fun t : ℝ ↦ Nat.floor ((x : ℝ) / t) :=
    Nat.measurable_floor.comp (measurable_const.div measurable_id)
  simpa only [B, caichWShortMomentRootBudget,
    caichWShortDivisorEnergy, caichWShortSupport] using! hB.comp hfloor

/-- A fixed finite bound for every section budget; it is used only for
integrability on the bounded `t` interval. -/
noncomputable def caichWShortMomentUniformBudget
    (r x p : ℕ) : ℝ :=
  (Real.sqrt (Nat.smoothNumbersUpTo (x / p) p).card *
      Real.sqrt
        ((∑ n ∈ Nat.smoothNumbersUpTo (x / p) p,
          (orderedDivisorCount (4 * r - 3) n : ℝ)) ^ (2 * r - 1))) ^
    (1 / (r : ℝ))

theorem caichWShortMomentRootBudget_nonneg
    (r x p : ℕ) (t : ℝ) :
    0 ≤ caichWShortMomentRootBudget r x p t := by
  unfold caichWShortMomentRootBudget
  positivity

theorem caichWShortMomentRootBudget_le_uniform
    {r : ℕ} (hr : 0 < r) (x p : ℕ) (t : ℝ) :
    caichWShortMomentRootBudget r x p t ≤
      caichWShortMomentUniformBudget r x p := by
  let s : Finset ℕ := caichWShortSupport x p t
  let S : Finset ℕ := Nat.smoothNumbersUpTo (x / p) p
  let e : ℝ := ∑ n ∈ s,
    (orderedDivisorCount (4 * r - 3) n : ℝ)
  let E : ℝ := ∑ n ∈ S,
    (orderedDivisorCount (4 * r - 3) n : ℝ)
  have hsS : s ⊆ S := by
    exact Finset.sdiff_subset
  have hcard : ((s.card : ℕ) : ℝ) ≤ S.card := by
    exact_mod_cast Finset.card_le_card hsS
  have henergy : e ≤ E := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsS
      (fun n hn hns ↦ by positivity)
  have he : 0 ≤ e := Finset.sum_nonneg fun n hn ↦ by positivity
  have hE : 0 ≤ E := Finset.sum_nonneg fun n hn ↦ by positivity
  have hpow : e ^ (2 * r - 1) ≤ E ^ (2 * r - 1) :=
    pow_le_pow_left₀ he henergy _
  have hbase :
      Real.sqrt (s.card : ℝ) * Real.sqrt (e ^ (2 * r - 1)) ≤
        Real.sqrt (S.card : ℝ) * Real.sqrt (E ^ (2 * r - 1)) :=
    mul_le_mul (Real.sqrt_le_sqrt hcard) (Real.sqrt_le_sqrt hpow)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hbase_nonneg :
      0 ≤ Real.sqrt (s.card : ℝ) * Real.sqrt (e ^ (2 * r - 1)) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hexp : 0 ≤ 1 / (r : ℝ) := by positivity
  simpa only [caichWShortMomentRootBudget,
    caichWShortMomentUniformBudget, s, S, e, E,
    caichWShortDivisorEnergy] using!
      Real.rpow_le_rpow hbase_nonneg hbase hexp

theorem intervalIntegrable_caichWShortMomentRootBudget
    {r : ℕ} (hr : 0 < r) (x p : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun t ↦ caichWShortMomentRootBudget r x p t)
      volume a b := by
  rw [intervalIntegrable_iff]
  apply IntegrableOn.of_bound (by rw [Real.volume_uIoc]; finiteness)
    (measurable_caichWShortMomentRootBudget hr x p).aestronglyMeasurable
    (caichWShortMomentUniformBudget r x p)
  exact ae_of_all _ fun t ↦ by
    rw [Real.norm_eq_abs,
      abs_of_nonneg (caichWShortMomentRootBudget_nonneg r x p t)]
    exact caichWShortMomentRootBudget_le_uniform hr x p t

/-- The explicit result of moving the probability `L^r` norm through one
short prime average. -/
noncomputable def caichWPrimeMomentRootBudget
    (r : ℕ) (X : ℝ) (x p : ℕ) : ℝ :=
  (X / (p : ℝ)) *
    ∫ t in (p : ℝ)..(p : ℝ) * (1 + 1 / X),
      caichWShortMomentRootBudget r x p t

set_option maxHeartbeats 1200000 in
/-- Integral Minkowski followed by the exact short-section interpolation
bound. -/
theorem caichWPrimeContribution_moment_root_le
    (r x : ℕ) {X : ℝ} {p : ℕ}
    (hr : 1 ≤ r) (hX : 0 < X) (hp : p.Prime) :
    (∫ omega, caichWPrimeContribution X x p omega ^ r ∂μ) ^
        (1 / (r : ℝ)) ≤ caichWPrimeMomentRootBudget r X x p := by
  let q : ℝ := (p : ℝ) * (1 + 1 / X)
  let ν : Measure ℝ := volume.restrict (Set.Ioc (p : ℝ) q)
  let G : ℝ → Omega → ℝ := fun t omega ↦
    caichWShortKernel x p t omega
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hpq : (p : ℝ) ≤ q := by
    have hinv : 0 ≤ 1 / X := by positivity
    dsimp only [q]
    nlinarith
  have hc : 0 ≤ X / (p : ℝ) := div_nonneg hX.le hpR.le
  have hG : Measurable fun u : ℝ × Omega ↦ G u.1 u.2 := by
    simpa only [G, caichWShortKernel] using!
      measurable_caichWShortKernel x hp.pos
  have hG_nonneg : ∀ t omega, 0 ≤ G t omega :=
    fun t omega ↦ caichWShortKernel_nonneg x p t omega
  have hG_bound : ∀ t omega, ‖G t omega‖ ≤
      caichWShortUniformBound x p ^ 2 := by
    intro t omega
    change ‖|caichWShortDifference x p t omega| ^ 2‖ ≤ _
    simpa only [norm_pow, Real.norm_eq_abs, abs_abs] using!
      (pow_le_pow_left₀ (abs_nonneg _)
        (abs_caichWShortDifference_le x hp.pos t omega) 2)
  have hinner : ∀ omega, Integrable (fun t ↦ G t omega) ν := by
    intro omega
    apply Integrable.of_bound
      ((hG.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
      (caichWShortUniformBound x p ^ 2)
    exact ae_of_all ν fun t ↦ hG_bound t omega
  have hAmeas : StronglyMeasurable fun omega ↦ ∫ t, G t omega ∂ν := by
    have hswap : StronglyMeasurable fun u : Omega × ℝ ↦ G u.2 u.1 :=
      (hG.comp measurable_swap).stronglyMeasurable
    exact hswap.integral_prod_right' (ν := ν)
  have hAbound : ∀ omega, ‖∫ t, G t omega ∂ν‖ ≤
      (caichWShortUniformBound x p ^ 2) * ν.real univ := by
    intro omega
    exact norm_integral_le_of_norm_le_const
      (ae_of_all ν fun t ↦ hG_bound t omega)
  have hmoment : Integrable
      (fun omega ↦ (∫ t, G t omega ∂ν) ^ r) μ := by
    apply Integrable.of_bound
      ((hAmeas.measurable.pow_const r).aestronglyMeasurable)
      (((caichWShortUniformBound x p ^ 2) * ν.real univ) ^ r)
    exact ae_of_all μ fun omega ↦ by
      change ‖(∫ t, G t omega ∂ν) ^ r‖ ≤ _
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (hAbound omega) r
  have hsection : ∀ t, Integrable (fun omega ↦ G t omega ^ r) μ := by
    intro t
    simpa only [G, caichWShortKernel, ← pow_mul, Nat.mul_comm] using!
      (integrable_caichWShortKernel_pow (q := r) x hp.pos t)
  have hroot_meas : StronglyMeasurable fun t ↦
      (∫ omega, G t omega ^ r ∂μ) ^ (1 / (r : ℝ)) := by
    have hpow : StronglyMeasurable fun u : ℝ × Omega ↦
        G u.1 u.2 ^ r := (hG.pow_const r).stronglyMeasurable
    have hint : StronglyMeasurable fun t ↦
        ∫ omega, G t omega ^ r ∂μ :=
      hpow.integral_prod_right' (ν := μ)
    exact (Real.continuous_rpow_const (by positivity :
      0 ≤ 1 / (r : ℝ))).measurable.comp hint.measurable |>.stronglyMeasurable
  have hsectionIntegralBound : ∀ t,
      (∫ omega, G t omega ^ r ∂μ) ^ (1 / (r : ℝ)) ≤
        (caichWShortUniformBound x p ^ (2 * r)) ^ (1 / (r : ℝ)) := by
    intro t
    have hnonneg : 0 ≤ ∫ omega, G t omega ^ r ∂μ :=
      integral_nonneg fun omega ↦ pow_nonneg (hG_nonneg t omega) r
    have hraw : ∫ omega, G t omega ^ r ∂μ ≤
        caichWShortUniformBound x p ^ (2 * r) := by
      have hnorm := norm_integral_le_of_norm_le_const (μ := μ)
        (f := fun omega ↦ G t omega ^ r)
        (C := caichWShortUniformBound x p ^ (2 * r))
        (ae_of_all μ fun omega ↦ by
          change ‖G t omega ^ r‖ ≤ _
          rw [norm_pow]
          have hk := hG_bound t omega
          have hpower : caichWShortUniformBound x p ^ (2 * r) =
              (caichWShortUniformBound x p ^ 2) ^ r := by
            rw [← pow_mul]
          rw [hpower]
          exact pow_le_pow_left₀ (norm_nonneg _) hk r)
      simpa only [probReal_univ, mul_one,
        Real.norm_of_nonneg hnonneg] using! hnorm
    exact Real.rpow_le_rpow hnonneg hraw (by positivity)
  have hroot : Integrable (fun t ↦
      (∫ omega, G t omega ^ r ∂μ) ^ (1 / (r : ℝ))) ν := by
    apply Integrable.of_bound hroot_meas.aestronglyMeasurable
      ((caichWShortUniformBound x p ^ (2 * r)) ^ (1 / (r : ℝ)))
    exact ae_of_all ν fun t ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg
        (integral_nonneg fun omega ↦ pow_nonneg (hG_nonneg t omega) r) _)]
      exact hsectionIntegralBound t
  have hmink := IntegralMinkowski.integral_Lp_const_mul_integral_le
    (ν := ν) (μ := μ) hG hG_nonneg hr hc hinner hmoment hsection hroot
  have hbudgetOn : Integrable (fun t ↦
      caichWShortMomentRootBudget r x p t) ν := by
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hpq).mp
      (intervalIntegrable_caichWShortMomentRootBudget
        (lt_of_lt_of_le Nat.zero_lt_one hr) x p (p : ℝ) q)
  have hroot_le_budget :
      (∫ t, (∫ omega, G t omega ^ r ∂μ) ^
          (1 / (r : ℝ)) ∂ν) ≤
        ∫ t, caichWShortMomentRootBudget r x p t ∂ν := by
    apply integral_mono_ae hroot hbudgetOn
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    simpa only [G, caichWShortKernel, ← pow_mul, Nat.mul_comm] using!
      caichWShort_moment_root_le r x hr hp.pos ht.1.le
  have hscaled := hmink.trans
    (mul_le_mul_of_nonneg_left hroot_le_budget hc)
  unfold caichWPrimeContribution caichShortPrimeAverage
    caichWPrimeMomentRootBudget
  simpa only [G, q, ν, intervalIntegral.integral_of_le hpq] using! hscaled

/-- The displayed prime/integral budget after both applications of
Minkowski. -/
noncomputable def caichWTotalMomentRootBudget
    (r : ℕ) (X : ℝ) (x a b : ℕ) : ℝ :=
  ∑ p ∈ freshPrimes a b, caichWPrimeMomentRootBudget r X x p

theorem measurable_caichInitialSmoothingError
    {X : ℝ} (hX : 0 < X) (x a b : ℕ) :
    Measurable fun omega ↦ caichInitialSmoothingError X omega x a b := by
  rw [show (fun omega ↦ caichInitialSmoothingError X omega x a b) =
      fun omega ↦ ∑ p ∈ freshPrimes a b,
        caichWPrimeContribution X x p omega by
    funext omega
    exact caichInitialSmoothingError_eq_sum_primeContributions X omega x a b]
  exact Finset.measurable_fun_sum _ fun p hp ↦
    measurable_caichWPrimeContribution hX x (mem_freshPrimes.mp hp).1.pos

theorem memLp_caichInitialSmoothingError
    {X : ℝ} (hX : 0 < X) (x a b : ℕ) (q : ℝ≥0∞) :
    MemLp (fun omega ↦ caichInitialSmoothingError X omega x a b) q μ := by
  rw [show (fun omega ↦ caichInitialSmoothingError X omega x a b) =
      ∑ p ∈ freshPrimes a b, caichWPrimeContribution X x p by
    funext omega
    simpa only [Finset.sum_apply] using!
      caichInitialSmoothingError_eq_sum_primeContributions X omega x a b]
  exact memLp_finset_sum' _ fun p hp ↦
    memLp_caichWPrimeContribution hX x (mem_freshPrimes.mp hp).1.pos q

theorem integrable_caichInitialSmoothingError_pow
    {X : ℝ} (hX : 0 < X) (x a b r : ℕ) (hr : 0 < r) :
    Integrable (fun omega ↦ caichInitialSmoothingError X omega x a b ^ r) μ := by
  have hmem := memLp_caichInitialSmoothingError hX x a b (r : ℝ≥0∞)
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (caichInitialSmoothingError_nonneg hX _ _ _ _)] using!
      hmem.integrable_norm_pow (Nat.ne_of_gt hr)

set_option maxHeartbeats 800000 in
/-- Finite-prime Minkowski, with every prime section already replaced by
the explicit divisor-energy budget. -/
theorem caichInitialSmoothingError_moment_root_le
    (r x a b : ℕ) {X : ℝ} (hr : 1 ≤ r) (hX : 0 < X) :
    (∫ omega, caichInitialSmoothingError X omega x a b ^ r ∂μ) ^
        (1 / (r : ℝ)) ≤ caichWTotalMomentRootBudget r X x a b := by
  let P : Finset ℕ := freshPrimes a b
  let F : ℕ → Omega → ℝ := fun p ↦ caichWPrimeContribution X x p
  have hr0 : r ≠ 0 := by omega
  have hsum := lpNorm_sum_le
    (p := (r : ℝ≥0∞)) (μ := μ) (s := P) (f := F)
    (fun p hp ↦ memLp_caichWPrimeContribution hX x
      (mem_freshPrimes.mp hp).1.pos (r : ℝ≥0∞))
    (by exact_mod_cast hr)
  have hsum_eq : (∑ p ∈ P, F p) =
      fun omega ↦ caichInitialSmoothingError X omega x a b := by
    funext omega
    simpa only [Finset.sum_apply] using!
      (caichInitialSmoothingError_eq_sum_primeContributions
        X omega x a b).symm
  have hleft : lpNorm (fun omega ↦
      caichInitialSmoothingError X omega x a b) (r : ℝ≥0∞) μ =
      (∫ omega, caichInitialSmoothingError X omega x a b ^ r ∂μ) ^
        (1 / (r : ℝ)) := by
    rw [lpNorm_eq_integral_norm_rpow_toReal (by exact_mod_cast hr0)
      (by simp) (measurable_caichInitialSmoothingError hX x a b).aestronglyMeasurable]
    simp only [ENNReal.toReal_natCast, Real.rpow_natCast, Real.norm_eq_abs,
      abs_of_nonneg (caichInitialSmoothingError_nonneg hX _ _ _ _), inv_eq_one_div]
  have hprime (p : ℕ) (hp : p ∈ P) :
      lpNorm (F p) (r : ℝ≥0∞) μ ≤
        caichWPrimeMomentRootBudget r X x p := by
    rw [lpNorm_eq_integral_norm_rpow_toReal (by exact_mod_cast hr0)
      (by simp) (measurable_caichWPrimeContribution hX x
        (mem_freshPrimes.mp hp).1.pos).aestronglyMeasurable]
    simp only [ENNReal.toReal_natCast, Real.rpow_natCast, Real.norm_eq_abs,
      abs_of_nonneg (caichWPrimeContribution_nonneg hX x
        (mem_freshPrimes.mp hp).1.pos _), inv_eq_one_div]
    exact caichWPrimeContribution_moment_root_le r x hr hX
      (mem_freshPrimes.mp hp).1
  rw [hsum_eq, hleft] at hsum
  exact hsum.trans (by
    unfold caichWTotalMomentRootBudget P
    exact Finset.sum_le_sum fun p hp ↦ hprime p hp)

theorem caichInitialSmoothingError_moment_le
    (r x a b : ℕ) {X : ℝ} (hr : 1 ≤ r) (hX : 0 < X) :
    (∫ omega, caichInitialSmoothingError X omega x a b ^ r ∂μ) ≤
      caichWTotalMomentRootBudget r X x a b ^ r := by
  let I : ℝ := ∫ omega, caichInitialSmoothingError X omega x a b ^ r ∂μ
  let B : ℝ := caichWTotalMomentRootBudget r X x a b
  have hI : 0 ≤ I := integral_nonneg fun omega ↦
    pow_nonneg (caichInitialSmoothingError_nonneg hX omega x a b) r
  have hroot : I ^ (1 / (r : ℝ)) ≤ B := by
    simpa only [I, B] using!
      caichInitialSmoothingError_moment_root_le r x a b hr hX
  have hpow := pow_le_pow_left₀ (Real.rpow_nonneg hI _) hroot r
  have hr0 : r ≠ 0 := by omega
  simpa only [I, B, one_div, Real.rpow_inv_natCast_pow hI hr0] using! hpow

/-- Moment estimate for the literal normalized `W/x` auxiliary. -/
theorem caichConcreteWoverX_moment_le
    (r x a b : ℕ) {X : ℝ} (hr : 1 ≤ r) (hX : 0 < X)
    (hx : 0 < x) :
    (∫ omega, (caichInitialSmoothingError X omega x a b / (x : ℝ)) ^ r ∂μ) ≤
      (caichWTotalMomentRootBudget r X x a b / (x : ℝ)) ^ r := by
  have hxR : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx
  simp_rw [div_pow]
  rw [integral_div]
  exact div_le_div_of_nonneg_right
    (caichInitialSmoothingError_moment_le r x a b hr hX)
    (pow_nonneg hxR.le r)

/-! ## Exact aligned application and the remaining arithmetic proposition -/

/-- Caich's choice `X = (log x)^(8r^2-8r+4)`. -/
def caichWSmoothingExponent (r : ℕ) : ℕ :=
  8 * r ^ 2 - 8 * r + 4

noncomputable def caichWSmoothingParameter (r x : ℕ) : ℝ :=
  Real.log (x : ℝ) ^ caichWSmoothingExponent r

/-- Floor-safe natural version for the scheduled core, whose smoothing
parameter is natural-valued.  Its cast can be fed literally to
`caichInitialSmoothingError`; this avoids choosing two unrelated `X`'s in
the final assembly. -/
noncomputable def caichWSmoothingParameterNat (r x : ℕ) : ℕ :=
  max 1 (Nat.floor (caichWSmoothingParameter r x))

noncomputable def caichWSmoothingParameterNatCast (r x : ℕ) : ℝ :=
  (caichWSmoothingParameterNat r x : ℝ)

theorem caichWSmoothingParameterNat_pos (r x : ℕ) :
    0 < caichWSmoothingParameterNat r x := by
  unfold caichWSmoothingParameterNat
  omega

theorem caichWSmoothingParameterNatCast_pos (r x : ℕ) :
    0 < caichWSmoothingParameterNatCast r x := by
  unfold caichWSmoothingParameterNatCast
  exact_mod_cast caichWSmoothingParameterNat_pos r x

theorem caichWSmoothingParameter_pos {r x : ℕ} (hx : 1 < x) :
    0 < caichWSmoothingParameter r x := by
  unfold caichWSmoothingParameter
  exact pow_pos (Real.log_pos (by exact_mod_cast hx)) _

/-- The literal `caichConcreteWoverX` on the aligned root-exponential test
mesh, with an arbitrary (in applications, clamped Harper) lower cutoff. -/
noncomputable def caichAlignedConcreteWoverX
    (r m : ℕ) (a : ℕ → ℕ → ℕ)
    (ell i : ℕ) (omega : Omega) : ℝ :=
  caichConcreteWoverX
    (fun _ell i ↦ caichWSmoothingParameter r
      (alignedRootExpTestPoint m i))
    (fun _ell i ↦ alignedRootExpTestPoint m i)
    a
    (fun _ell i ↦ alignedRootExpTestPoint m i)
    ell i omega

theorem one_lt_alignedRootExpTestPoint_of_mem
    {K m ell i : ℕ} (hi : i ∈ alignedRootExpTests K m ell) :
    1 < alignedRootExpTestPoint m i := by
  have htwo : 2 ≤ alignedThinEndpoint K ell 0 :=
    two_le_alignedThinEndpoint K ell 0
  exact Nat.one_lt_two.trans_le
    (htwo.trans_lt (alignedThinInitial_lt_testPoint_of_mem hi)).le

/-- The sole number-theoretic input left in the `W` argument.  Every term
is the explicit short-support divisor-energy/prime-integral budget above;
there is no probability, `W`, exceptional event, or desired conclusion in
this proposition. -/
def CaichWDivisorPrimeBudgetBound
    (r K m : ℕ) (a : ℕ → ℕ → ℕ) (C : ℝ) : Prop :=
  0 ≤ C ∧
  ∀ ell i, i ∈ alignedRootExpTests K m ell →
    caichWTotalMomentRootBudget r
        (caichWSmoothingParameter r (alignedRootExpTestPoint m i))
        (alignedRootExpTestPoint m i) (a ell i)
        (alignedRootExpTestPoint m i) ≤
      C * (alignedRootExpTestPoint m i : ℝ) /
        Real.log (alignedRootExpTestPoint m i : ℝ)

noncomputable def caichAlignedWMoment
    (r m : ℕ) (C : ℝ) (_ell i : ℕ) : ℝ :=
  (C / Real.log (alignedRootExpTestPoint m i : ℝ)) ^ r

/-- A harmless positive extension of the published threshold across the
four empty initial aligned scales. -/
noncomputable def caichAlignedWSafeThreshold (K ell : ℕ) : ℝ :=
  if ell < 5 then 1 else caichWAuxThreshold K ell

theorem caichAlignedWSafeThreshold_pos (K ell : ℕ) :
    0 < caichAlignedWSafeThreshold K ell := by
  unfold caichAlignedWSafeThreshold
  split_ifs with hell
  · norm_num
  · have hell0 : (0 : ℝ) < (ell : ℝ) := by
      exact_mod_cast (show 0 < ell by omega)
    unfold caichWAuxThreshold caichAuxiliaryPower
    positivity

/-- Purely scalar remainder of the finite-test calculation.  This is the
exact deterministic series produced by corrected Markov plus the aligned
finite union. -/
def CaichWAlignedScalarSummability
    (r K m : ℕ) (C : ℝ) : Prop :=
  Summable (caichAuxiliaryFiniteUnionMomentBudget
    (alignedRootExpTests K m)
    (fun ell i ↦ if i ∈ alignedRootExpTests K m ell then
      caichAlignedWMoment r m C ell i else 0)
    (caichAlignedWSafeThreshold K) r)

theorem caichAlignedConcreteWoverX_nonneg
    {r K m : ℕ} {a : ℕ → ℕ → ℕ}
    {ell i : ℕ} (hi : i ∈ alignedRootExpTests K m ell)
    (omega : Omega) :
    0 ≤ caichAlignedConcreteWoverX r m a ell i omega := by
  unfold caichAlignedConcreteWoverX
  apply caichConcreteWoverX_nonneg
  · exact caichWSmoothingParameter_pos
      (one_lt_alignedRootExpTestPoint_of_mem hi)
  · exact Nat.zero_lt_of_lt (one_lt_alignedRootExpTestPoint_of_mem hi)

theorem integrable_caichAlignedConcreteWoverX_pow
    {r K m : ℕ} (hr : 1 ≤ r) {a : ℕ → ℕ → ℕ}
    {ell i : ℕ} (hi : i ∈ alignedRootExpTests K m ell) :
    Integrable (fun omega ↦
      caichAlignedConcreteWoverX r m a ell i omega ^ r) μ := by
  let x := alignedRootExpTestPoint m i
  have hx : 1 < x := one_lt_alignedRootExpTestPoint_of_mem hi
  have hW := integrable_caichInitialSmoothingError_pow
    (X := caichWSmoothingParameter r x)
    (caichWSmoothingParameter_pos (r := r) hx)
    x (a ell i) x r (by omega)
  unfold caichAlignedConcreteWoverX caichConcreteWoverX
  simpa only [div_pow] using! hW.div_const ((x : ℝ) ^ r)

theorem integral_caichAlignedConcreteWoverX_pow_le
    {r K m : ℕ} (hr : 1 ≤ r) {a : ℕ → ℕ → ℕ}
    {C : ℝ} (hbudget : CaichWDivisorPrimeBudgetBound r K m a C)
    {ell i : ℕ} (hi : i ∈ alignedRootExpTests K m ell) :
    (∫ omega, caichAlignedConcreteWoverX r m a ell i omega ^ r ∂μ) ≤
      caichAlignedWMoment r m C ell i := by
  let x := alignedRootExpTestPoint m i
  let X := caichWSmoothingParameter r x
  have hx : 1 < x := one_lt_alignedRootExpTestPoint_of_mem hi
  have hxR : (0 : ℝ) < (x : ℝ) := by positivity
  have hlog : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hx)
  have hX : 0 < X := caichWSmoothingParameter_pos hx
  have hbase := caichConcreteWoverX_moment_le r x (a ell i) x hr hX
    (by omega : 0 < x)
  have hrootBudget := hbudget.2 ell i hi
  have hnormalized :
      caichWTotalMomentRootBudget r X x (a ell i) x / (x : ℝ) ≤
        C / Real.log (x : ℝ) := by
    rw [div_le_iff₀ hxR]
    calc
      caichWTotalMomentRootBudget r X x (a ell i) x ≤
          C * (x : ℝ) / Real.log (x : ℝ) := by
        simpa only [X, x] using! hrootBudget
      _ = (C / Real.log (x : ℝ)) * (x : ℝ) := by ring
  have htotalNonneg : 0 ≤
      caichWTotalMomentRootBudget r X x (a ell i) x := by
    unfold caichWTotalMomentRootBudget caichWPrimeMomentRootBudget
    exact Finset.sum_nonneg fun p hp ↦
      mul_nonneg (div_nonneg hX.le (by positivity))
        (intervalIntegral.integral_nonneg (by
          have : 0 ≤ 1 / X := by positivity
          nlinarith) fun t ht ↦ caichWShortMomentRootBudget_nonneg r x p t)
  have hpow := pow_le_pow_left₀ (div_nonneg htotalNonneg hxR.le)
    hnormalized r
  unfold caichAlignedConcreteWoverX caichAlignedWMoment
  simpa only [x, X] using! hbase.trans hpow

/-- Corrected Markov + exact finite test union + summability.  The bound has
no factor `T(ell)^(-r)`: the threshold contributes only its own reciprocal
power through `caichAuxiliaryFiniteUnionMomentBudget`. -/
theorem summable_measureReal_caichAlignedConcreteWoverX_failure
    {r K m : ℕ} (hr : 1 ≤ r) {a : ℕ → ℕ → ℕ} {C : ℝ}
    (harith : CaichWDivisorPrimeBudgetBound r K m a C)
    (hscalar : CaichWAlignedScalarSummability r K m C) :
    Summable fun ell ↦ μ.real
      (caichAuxiliaryComponentFailure (alignedRootExpTests K m)
        (caichAlignedConcreteWoverX r m a) (caichWAuxThreshold K) ell) := by
  let tests := alignedRootExpTests K m
  let value := caichAlignedConcreteWoverX r m a
  let moment := caichAlignedWMoment r m C
  let safeValue : ℕ → ℕ → Omega → ℝ := fun ell i omega ↦
    if i ∈ tests ell then value ell i omega else 0
  let safeMoment : ℕ → ℕ → ℝ := fun ell i ↦
    if i ∈ tests ell then moment ell i else 0
  have hsafe := summable_measureReal_caichAuxiliaryComponentFailure_of_natMoment
    tests safeValue safeMoment (caichAlignedWSafeThreshold K) r (by omega)
    (fun ell i omega ↦ by
      unfold safeValue
      by_cases hi : i ∈ tests ell
      · rw [if_pos hi]
        exact caichAlignedConcreteWoverX_nonneg hi omega
      · rw [if_neg hi])
    (caichAlignedWSafeThreshold_pos K)
    (fun ell i ↦ by
      unfold safeValue
      by_cases hi : i ∈ tests ell
      · simp only [if_pos hi]
        exact integrable_caichAlignedConcreteWoverX_pow hr hi
      · simp [hi])
    (fun ell i ↦ by
      unfold safeValue safeMoment
      by_cases hi : i ∈ tests ell
      · simp only [if_pos hi]
        exact integral_caichAlignedConcreteWoverX_pow_le hr harith hi
      · simp [hi, show r ≠ 0 by omega])
    (by simpa only [tests, safeMoment, moment] using! hscalar)
  apply hsafe.congr
  intro ell
  by_cases hell : ell < 5
  · have hempty : tests ell = ∅ := by
      simp [tests, alignedRootExpTests, hell]
    simp [tests, safeValue, value, hempty, caichAuxiliaryComponentFailure,
      caichAuxiliaryComponentGoodAtScale]
  · congr 1
    ext omega
    simp only [safeValue, value, caichAlignedWSafeThreshold, if_neg hell,
      caichAuxiliaryComponentFailure, caichAuxiliaryComponentGoodAtScale,
      Set.mem_setOf_eq, not_forall, not_le]
    constructor
    · rintro ⟨i, hi, hbad⟩
      exact ⟨i, by simpa only [tests] using! hi, by simpa only [if_pos hi] using! hbad⟩
    · rintro ⟨i, hi, hbad⟩
      have hi' : i ∈ tests ell := by simpa only [tests] using! hi
      exact ⟨i, hi', by simpa only [if_pos hi'] using! hbad⟩

end Problem520
end Erdos
