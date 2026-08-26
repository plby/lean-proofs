import ErdosProblems.Erdos67b.MRSmoothPrimeDerivative
import ErdosProblems.Erdos67b.MRFiniteSmoothRiemann

/-!
# Smooth progression sums with an explicit uniform error

Multiples are reindexed at their exact rounded real endpoints. The finite
Riemann estimate then costs at most `400 * (1 + |t|)`, independently of
the positive modulus, provided twice the modulus is at most the scale.
-/

open MeasureTheory
open scoped BigOperators

namespace Erdos67b

noncomputable section

theorem mrSum_multiples_rounded_interval (F : ℕ → ℂ) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) {q : ℕ} (hq : 0 < q) :
    (∑ n ∈ Finset.Icc ⌈a⌉₊ ⌊b⌋₊ with q ∣ n, F n) =
      ∑ m ∈ Finset.Icc ⌈a / (q : ℝ)⌉₊ ⌊b / (q : ℝ)⌋₊, F (q * m) := by
  classical
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hb : 0 ≤ b := ha.trans hab
  symm
  apply Finset.sum_bij (fun m _hm ↦ q * m)
  · intro m hm
    have hmRange := Finset.mem_Icc.mp hm
    have hlo := (Nat.ceil_le.mp hmRange.1)
    have hhi := (Nat.le_floor_iff (div_nonneg hb hqR.le)).mp hmRange.2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨Nat.ceil_le.mpr ?_, Nat.le_floor ?_⟩, dvd_mul_right q m⟩
    · have hh := (div_le_iff₀ hqR).1 hlo
      simpa only [Nat.cast_mul, mul_comm] using hh
    · have hh := (le_div_iff₀ hqR).1 hhi
      simpa only [Nat.cast_mul, mul_comm] using hh
  · intro m _hm n _hn heq
    exact Nat.eq_of_mul_eq_mul_left hq heq
  · intro n hn
    obtain ⟨hnRange, m, rfl⟩ := Finset.mem_filter.mp hn
    have hlo := Nat.ceil_le.mp (Finset.mem_Icc.mp hnRange).1
    have hhi := (Nat.le_floor_iff hb).mp (Finset.mem_Icc.mp hnRange).2
    refine ⟨m, Finset.mem_Icc.mpr ⟨Nat.ceil_le.mpr ?_, Nat.le_floor ?_⟩, rfl⟩
    · apply (div_le_iff₀ hqR).2
      simpa only [Nat.cast_mul, mul_comm] using hlo
    · apply (le_div_iff₀ hqR).2
      simpa only [Nat.cast_mul, mul_comm] using hhi
  · intro m _hm
    rfl

theorem mrSmoothPrime_progression_integral_eq {P : ℝ} {q : ℕ} (hq : 0 < q) (t : ℝ) :
    (∫ y in (P / 2) / (q : ℝ)..(3 * P) / (q : ℝ),
      mrSmoothPrimeKernelIntegrand P t ((q : ℝ) * y)) =
        mrScaledPrimeMellinIntegral P t / (q : ℂ) := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [intervalIntegral.integral_comp_mul_left _ hqR,
    mul_div_cancel₀ _ hqR, mul_div_cancel₀ _ hqR]
  change (q : ℝ)⁻¹ • mrScaledPrimeMellinIntegral P t = _
  simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast, div_eq_mul_inv]
  ring

theorem mrSmoothPrime_progression_error_le {P : ℝ} (hP : 0 < P)
    {q : ℕ} (hq : 0 < q) (hqP : 2 * (q : ℝ) ≤ P) (t : ℝ) :
    ‖(∑ n ∈ Finset.Icc ⌈P / 2⌉₊ ⌊3 * P⌋₊ with q ∣ n,
        mrSmoothPrimeKernelIntegrand P t n) -
      mrScaledPrimeMellinIntegral P t / (q : ℂ)‖ ≤ 400 * (1 + |t|) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  let a := (P / 2) / (q : ℝ)
  let b := (3 * P) / (q : ℝ)
  let F : ℝ → ℂ := fun y ↦ mrSmoothPrimeKernelIntegrand P t ((q : ℝ) * y)
  let F' : ℝ → ℂ := fun y ↦ (q : ℝ) • mrSmoothPrimeKernelDerivative P t ((q : ℝ) * y)
  let C := (q : ℝ) * (80 * (1 + |t|) / P)
  have ha : 1 ≤ a := (le_div_iff₀ hqR).2 (by linarith)
  have hb : b = 6 * a := by dsimp only [a, b]; ring
  have hab : a ≤ b := by rw [hb]; linarith
  have hround : ⌈a⌉₊ ≤ ⌊b⌋₊ := by
    apply Nat.le_floor
    have hh := Nat.ceil_lt_add_one (by linarith : 0 ≤ a)
    rw [hb]
    linarith
  have hscaled {y : ℝ} (hy : y ∈ Set.Icc a b) :
      (q : ℝ) * y ∈ Set.Icc (P / 2) (3 * P) := by
    constructor
    · have hh := (div_le_iff₀ hqR).1 hy.1
      simpa only [mul_comm] using hh
    · have hh := (le_div_iff₀ hqR).1 hy.2
      simpa only [mul_comm] using hh
  have hderiv : ∀ y ∈ Set.Icc a b, HasDerivAt F (F' y) y := by
    intro y hy
    have hxy : 0 < (q : ℝ) * y := by linarith [(hscaled hy).1]
    exact (hasDerivAt_mrSmoothPrimeKernelIntegrand hxy t).scomp y
      (by simpa only [id_eq, mul_one] using (hasDerivAt_id y).const_mul (q : ℝ))
  have hsup : ∀ y ∈ Set.Icc a b, ‖F y‖ ≤ 40 :=
    fun y hy ↦ norm_mrSmoothPrimeKernelIntegrand_le hP (hscaled hy) t
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hderivBound : ∀ y ∈ Set.Icc a b, ‖F' y‖ ≤ C := by
    intro y hy
    dsimp only [F', C]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hqR]
    exact mul_le_mul_of_nonneg_left
      (norm_mrSmoothPrimeKernelDerivative_le hP (hscaled hy) t) hqR.le
  have hh := mrNorm_sum_rounded_sub_integral_le (by linarith : 0 ≤ a) hab hround
    (by norm_num : (0 : ℝ) ≤ 40) hC hderiv hsup hderivBound
  have hcost : C * (b - a) = 200 * (1 + |t|) := by
    dsimp only [C, a, b]
    field_simp
    ring
  rw [hcost] at hh
  have hsum := mrSum_multiples_rounded_interval (fun n ↦ mrSmoothPrimeKernelIntegrand P t n)
    (by positivity : (0 : ℝ) ≤ P / 2) (by linarith : P / 2 ≤ 3 * P) hq
  have hsum' : (∑ n ∈ Finset.Icc ⌈P / 2⌉₊ ⌊3 * P⌋₊ with q ∣ n,
      mrSmoothPrimeKernelIntegrand P t n) = ∑ m ∈ Finset.Icc ⌈a⌉₊ ⌊b⌋₊, F m := by
    simpa only [a, b, F, Nat.cast_mul] using hsum
  rw [hsum', ← mrSmoothPrime_progression_integral_eq hq t]
  apply hh.trans
  nlinarith [abs_nonneg t]

end

end Erdos67b
