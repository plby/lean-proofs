import ErdosProblems.Erdos520.ThinSchedule
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory Set
open scoped BigOperators Nat.Prime Interval

namespace Erdos
namespace Problem520

/-!
# Reciprocal-prime mass from Chebyshev's theorem

The thin-block argument does not require the asymptotic Mertens theorem for
reciprocal primes.  An eventual Chebyshev upper bound for the prime-counting
function, followed by Abel summation on one block, already gives the required
`O(1 / ell)` estimate.
-/

/-- A uniform prime-counting upper bound beyond a fixed threshold. -/
def PrimeCountingUpperBound (C : ℝ) (N : ℕ) : Prop :=
  ∀ x : ℝ, (N : ℝ) ≤ x →
    (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ C * x / Real.log x

/-- Mathlib's Chebyshev theorem supplies an unconditional eventual
prime-counting bound. -/
theorem exists_primeCountingUpperBound :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 2 ≤ N ∧ PrimeCountingUpperBound C N := by
  let C : ℝ := Real.log 4 + 1
  have hC : 0 < C := by
    dsimp [C]
    have : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)
    linarith
  have hev := Chebyshev.eventually_primeCounting_le (by norm_num : (0 : ℝ) < 1)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨A, hA⟩ := hev
  let N : ℕ := max 2 ⌈A⌉₊
  refine ⟨C, hC, N, le_max_left _ _, ?_⟩
  intro x hx
  apply hA
  have hceil : A ≤ (⌈A⌉₊ : ℝ) := Nat.le_ceil A
  exact hceil.trans ((Nat.cast_le.mpr (le_max_right 2 ⌈A⌉₊)).trans hx)

/-- The indicator sequence whose partial sums are the prime-counting
function. -/
private noncomputable def primeIndicator (n : ℕ) : ℝ :=
  if n.Prime then 1 else 0

private theorem sum_primeIndicator_Icc (n : ℕ) :
    ∑ k ∈ Icc 0 n, primeIndicator k = (Nat.primeCounting n : ℝ) := by
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  rw [← Finset.sum_boole (p := Nat.Prime)]
  simp only [primeIndicator, Nat.range_succ_eq_Icc_zero]

/-- Abel summation for the reciprocal primes in `(a,b]`. -/
theorem freshReciprocalSum_eq_primeCounting_integral
    {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    freshReciprocalSum a b =
      (Nat.primeCounting b : ℝ) / b - (Nat.primeCounting a : ℝ) / a +
        ∫ t in Ioc (a : ℝ) b, (Nat.primeCounting ⌊t⌋₊ : ℝ) / t ^ 2 := by
  classical
  let c : ℕ → ℝ := primeIndicator
  let f : ℝ → ℝ := fun x ↦ x⁻¹
  have hdiff : ∀ t ∈ Icc (a : ℝ) b, DifferentiableAt ℝ f t := by
    intro t ht
    exact differentiableAt_inv (ne_of_gt (lt_of_lt_of_le (by exact_mod_cast ha) ht.1))
  have hint : IntegrableOn (deriv f) (Icc (a : ℝ) b) := by
    have hcont : ContinuousOn (fun t : ℝ ↦ -(t ^ 2)⁻¹) (Icc (a : ℝ) b) := by
      apply ContinuousOn.neg
      apply ContinuousOn.inv₀ (continuousOn_pow 2)
      intro t ht hzero
      have htpos : 0 < t := lt_of_lt_of_le (by exact_mod_cast ha) ht.1
      exact (pow_ne_zero 2 htpos.ne') hzero
    have heq : deriv f = fun t : ℝ ↦ -(t ^ 2)⁻¹ := by
      funext t
      dsimp [f]
      exact deriv_inv
    rw [heq]
    exact hcont.integrableOn_Icc (μ := volume)
  have habel := sum_mul_eq_sub_sub_integral_mul' c hab hdiff hint
  simp only [c, f, sum_primeIndicator_Icc] at habel
  have hi :
      (∫ t in Ioc (a : ℝ) b,
          deriv (fun x : ℝ ↦ x⁻¹) t * (Nat.primeCounting ⌊t⌋₊ : ℝ)) =
        -∫ t in Ioc (a : ℝ) b,
          (Nat.primeCounting ⌊t⌋₊ : ℝ) / t ^ 2 := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards with t
    rw [deriv_inv]
    ring
  rw [hi] at habel
  calc
    freshReciprocalSum a b =
        ∑ p ∈ Ioc a b, (p : ℝ)⁻¹ * primeIndicator p := by
      rw [freshReciprocalSum]
      have hfin : freshPrimes a b = (Finset.Ioc a b).filter Nat.Prime := by
        ext p
        simp [mem_freshPrimes, and_comm]
      rw [hfin, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p hp
      by_cases hprime : p.Prime <;> simp [primeIndicator, hprime]
    _ = (Nat.primeCounting b : ℝ) / b - (Nat.primeCounting a : ℝ) / a +
          ∫ t in Ioc (a : ℝ) b, (Nat.primeCounting ⌊t⌋₊ : ℝ) / t ^ 2 := by
      simpa only [div_eq_mul_inv, mul_comm, sub_neg_eq_add] using! habel

/-- Chebyshev plus Abel summation bounds a reciprocal-prime block by its
`log log` width and a lower-endpoint error.  This is the only form needed by
the thin schedule. -/
theorem freshReciprocalSum_le_of_primeCountingUpperBound
    {C : ℝ} {N a b : ℕ}
    (hC : 0 ≤ C) (hP : PrimeCountingUpperBound C N)
    (hNa : N ≤ a) (ha : 2 ≤ a) (hab : a ≤ b) :
    freshReciprocalSum a b ≤
      C * (logLogNat b - logLogNat a) + 2 * C / Real.log (a : ℝ) := by
  have haR : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  have habR : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  have haPos : 0 < (a : ℝ) := by positivity
  have hbPos : 0 < (b : ℝ) := haPos.trans_le habR
  have hlogA : 0 < Real.log (a : ℝ) := Real.log_pos (by linarith)
  have hlogB : 0 < Real.log (b : ℝ) :=
    hlogA.trans_le (Real.log_le_log haPos habR)
  have hEq := freshReciprocalSum_eq_primeCounting_integral (a := a) (b := b)
    (by omega) hab
  have hboundary :
      (Nat.primeCounting b : ℝ) / b ≤ C / Real.log (b : ℝ) := by
    calc
      (Nat.primeCounting b : ℝ) / b ≤
          (C * (b : ℝ) / Real.log (b : ℝ)) / b := by
        apply div_le_div_of_nonneg_right
        · have hb := hP (b : ℝ) (by exact_mod_cast hNa.trans hab)
          simpa using! hb
        · positivity
      _ = C / Real.log (b : ℝ) := by field_simp
  let c : ℕ → ℝ := primeIndicator
  have hgCont : ContinuousOn (fun t : ℝ ↦ -(t ^ 2)⁻¹) (Icc (a : ℝ) b) := by
    apply ContinuousOn.neg
    apply ContinuousOn.inv₀ (continuousOn_pow 2)
    intro t ht
    exact pow_ne_zero 2 (ne_of_gt (haPos.trans_le ht.1))
  have hgInt : IntegrableOn (fun t : ℝ ↦ -(t ^ 2)⁻¹) (Icc (a : ℝ) b) :=
    hgCont.integrableOn_Icc
  have hmulInt := integrableOn_mul_sum_Icc (m := 0) c haPos.le hgInt
  have hnegInt : IntegrableOn
      (fun t : ℝ ↦ -(Nat.primeCounting ⌊t⌋₊ : ℝ) / t ^ 2)
      (Icc (a : ℝ) b) := by
    apply hmulInt.congr_fun
    · intro t ht
      simp only [c, sum_primeIndicator_Icc]
      ring
    · exact measurableSet_Icc
  have hleftInt : IntegrableOn
      (fun t : ℝ ↦ (Nat.primeCounting ⌊t⌋₊ : ℝ) / t ^ 2)
      (Icc (a : ℝ) b) := by
    apply hnegInt.neg.congr_fun
    · intro t ht
      simp only [Pi.neg_apply]
      ring
    · exact measurableSet_Icc
  have hlogCont : ContinuousOn (fun t : ℝ ↦ Real.log t)
      (Icc (a : ℝ) b) := by
    apply Real.continuousOn_log.mono
    intro t ht
    simp only [mem_compl_iff, mem_singleton_iff]
    exact ne_of_gt (haPos.trans_le ht.1)
  have hrightCont : ContinuousOn
      (fun t : ℝ ↦ C / (t * Real.log t)) (Icc (a : ℝ) b) := by
    apply ContinuousOn.div continuousOn_const
      (continuousOn_id.mul hlogCont)
    intro t ht
    exact mul_ne_zero (ne_of_gt (haPos.trans_le ht.1))
      (ne_of_gt (hlogA.trans_le (Real.log_le_log haPos (ht.1))))
  have hrightInt : IntegrableOn
      (fun t : ℝ ↦ C / (t * Real.log t)) (Icc (a : ℝ) b) :=
    hrightCont.integrableOn_Icc
  have hintegral :
      (∫ t in Ioc (a : ℝ) b,
          (Nat.primeCounting ⌊t⌋₊ : ℝ) / t ^ 2) ≤
        ∫ t in Ioc (a : ℝ) b, C / (t * Real.log t) := by
    apply setIntegral_mono_on
    · exact hleftInt.mono_set Ioc_subset_Icc_self
    · exact hrightInt.mono_set Ioc_subset_Icc_self
    · exact measurableSet_Ioc
    · intro t ht
      have htA : (a : ℝ) ≤ t := ht.1.le
      have htPos : 0 < t := haPos.trans_le htA
      have hlogT : 0 < Real.log t := hlogA.trans_le (Real.log_le_log haPos htA)
      calc
        (Nat.primeCounting ⌊t⌋₊ : ℝ) / t ^ 2 ≤
            (C * t / Real.log t) / t ^ 2 := by
          have hNt : (N : ℝ) ≤ t := by
            exact (by exact_mod_cast hNa : (N : ℝ) ≤ (a : ℝ)).trans htA
          exact div_le_div_of_nonneg_right
            (hP t hNt) (sq_nonneg t)
        _ = C / (t * Real.log t) := by field_simp
  have hloglogIntegral :
      (∫ t in Ioc (a : ℝ) b, C / (t * Real.log t)) =
        C * (logLogNat b - logLogNat a) := by
    rw [← intervalIntegral.integral_of_le habR]
    have hderiv : ∀ t ∈ uIcc (a : ℝ) b,
        HasDerivAt (fun x : ℝ ↦ Real.log (Real.log x))
          (1 / (t * Real.log t)) t := by
      intro t ht
      rw [uIcc_of_le habR] at ht
      have htPos : 0 < t := haPos.trans_le ht.1
      have hlogT : 0 < Real.log t := hlogA.trans_le (Real.log_le_log haPos ht.1)
      convert! (Real.hasDerivAt_log htPos.ne').log hlogT.ne' using 1 <;> field_simp
    have honeCont : ContinuousOn (fun t : ℝ ↦ 1 / (t * Real.log t))
        (Icc (a : ℝ) b) := by
      apply ContinuousOn.div continuousOn_const
        (continuousOn_id.mul hlogCont)
      intro t ht
      exact mul_ne_zero (ne_of_gt (haPos.trans_le ht.1))
        (ne_of_gt (hlogA.trans_le (Real.log_le_log haPos ht.1)))
    have honeContU : ContinuousOn (fun t : ℝ ↦ 1 / (t * Real.log t))
        (uIcc (a : ℝ) b) := by
      simpa [uIcc_of_le habR] using! honeCont
    have hbase := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      honeContU.intervalIntegrable
    rw [show (fun t : ℝ ↦ C / (t * Real.log t)) =
        fun t ↦ C * (1 / (t * Real.log t)) by funext t; ring,
      intervalIntegral.integral_const_mul, hbase]
    rfl
  rw [hloglogIntegral] at hintegral
  rw [hEq]
  have hpaNonneg : 0 ≤ (Nat.primeCounting a : ℝ) / a := by positivity
  have hlogMono : Real.log (a : ℝ) ≤ Real.log (b : ℝ) :=
    Real.log_le_log haPos habR
  have herror : C / Real.log (b : ℝ) ≤ C / Real.log (a : ℝ) := by
    exact div_le_div_of_nonneg_left hC hlogA hlogMono
  calc
    (Nat.primeCounting b : ℝ) / b - (Nat.primeCounting a : ℝ) / a +
          ∫ t in Ioc (a : ℝ) b, (Nat.primeCounting ⌊t⌋₊ : ℝ) / t ^ 2
        ≤ C / Real.log (b : ℝ) + C * (logLogNat b - logLogNat a) := by
      linarith
    _ ≤ C / Real.log (a : ℝ) + C * (logLogNat b - logLogNat a) := by
      linarith
    _ ≤ C * (logLogNat b - logLogNat a) + 2 * C / Real.log (a : ℝ) := by
      have : 0 ≤ C / Real.log (a : ℝ) := div_nonneg hC hlogA.le
      have heq : 2 * C / Real.log (a : ℝ) =
          2 * (C / Real.log (a : ℝ)) := by ring
      rw [heq]
      linarith

/-- A thin `log log` block whose lower endpoint satisfies
`ell ≤ log a` has reciprocal-prime mass at most `3 * C / ell`.

This is the schedule-level form of the Chebyshev estimate: unlike a Mertens
asymptotic, it only uses an upper bound for the prime-counting function. -/
theorem freshReciprocalSum_le_three_mul_div_of_primeCountingUpperBound
    {C : ℝ} {N a b ell : ℕ}
    (hC : 0 ≤ C) (hP : PrimeCountingUpperBound C N)
    (hNa : N ≤ a) (ha : 2 ≤ a) (hab : a ≤ b) (hell : 0 < ell)
    (hwidth : logLogNat b - logLogNat a ≤ 1 / (ell : ℝ))
    (hlarge : (ell : ℝ) ≤ Real.log (a : ℝ)) :
    freshReciprocalSum a b ≤ 3 * C / (ell : ℝ) := by
  have hellR : 0 < (ell : ℝ) := by exact_mod_cast hell
  have hlogA : 0 < Real.log (a : ℝ) := hellR.trans_le hlarge
  have hwidth' :
      C * (logLogNat b - logLogNat a) ≤ C * (1 / (ell : ℝ)) :=
    mul_le_mul_of_nonneg_left hwidth hC
  have herror : 2 * C / Real.log (a : ℝ) ≤ 2 * C / (ell : ℝ) := by
    exact div_le_div_of_nonneg_left (by positivity) hellR hlarge
  calc
    freshReciprocalSum a b ≤
        C * (logLogNat b - logLogNat a) + 2 * C / Real.log (a : ℝ) :=
      freshReciprocalSum_le_of_primeCountingUpperBound hC hP hNa ha hab
    _ ≤ C * (1 / (ell : ℝ)) + 2 * C / (ell : ℝ) :=
      add_le_add hwidth' herror
    _ = 3 * C / (ell : ℝ) := by ring

/-- There are absolute constants giving the `O(1 / ell)` reciprocal-prime
bound for every sufficiently large thin block.  The constants are obtained
unconditionally from Mathlib's Chebyshev theorem. -/
theorem exists_unconditional_thinBlockReciprocalBound :
    ∃ A : ℝ, 0 < A ∧ ∃ N : ℕ, 2 ≤ N ∧
      ∀ {a b ell : ℕ}, N ≤ a → 2 ≤ a → a ≤ b → 0 < ell →
        logLogNat b - logLogNat a ≤ 1 / (ell : ℝ) →
        (ell : ℝ) ≤ Real.log (a : ℝ) →
        freshReciprocalSum a b ≤ A / (ell : ℝ) := by
  obtain ⟨C, hC, N, hN, hP⟩ := exists_primeCountingUpperBound
  refine ⟨3 * C, mul_pos (by norm_num) hC, N, hN, ?_⟩
  intro a b ell hNa ha hab hell hwidth hlarge
  exact freshReciprocalSum_le_three_mul_div_of_primeCountingUpperBound
    hC.le hP hNa ha hab hell hwidth hlarge

end Problem520
end Erdos
