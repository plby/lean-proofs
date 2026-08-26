import ErdosProblems.Erdos421.SamplePacking
import Mathlib.Topology.Order.Compact

/-! # Controlling a nonnegative continuous integral by separated samples -/

namespace Erdos421

open MeasureTheory

theorem unit_cells_separated_of_equal_parity {A : ℝ} {t : ℕ → ℝ}
    (ht : ∀ n, A + n ≤ t n ∧ t n ≤ A + n + 1) {i j : ℕ} (hij : i ≠ j)
    (hpar : i % 2 = j % 2) : 1 ≤ |t i - t j| := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have hstep : i + 2 ≤ j := by omega
    have hstep' : (i : ℝ) + 2 ≤ j := by exact_mod_cast hstep
    have hb : 1 ≤ t j - t i := by linarith [(ht i).2, (ht j).1]
    exact hb.trans (by rw [abs_sub_comm]; exact le_abs_self _)
  · have hstep : j + 2 ≤ i := by omega
    have hstep' : (j : ℝ) + 2 ≤ i := by exact_mod_cast hstep
    have hb : 1 ≤ t i - t j := by linarith [(ht j).2, (ht i).1]
    exact hb.trans (le_abs_self _)

theorem integral_le_twice_separated_samples {f : ℝ → ℝ} (hf : Continuous f)
    (hf0 : ∀ x, 0 ≤ f x) {A B ε : ℝ} (hAB : A ≤ B)
    (hsample : ∀ (F : Finset ℕ) (t : ℕ → ℝ), (∀ i ∈ F, A ≤ t i ∧ t i ≤ B + 1) →
      (∀ i ∈ F, ∀ j ∈ F, i ≠ j → 1 ≤ |t i - t j|) → (∑ i ∈ F, f (t i)) ≤ ε) :
    (∫ x in A..B, f x) ≤ 2 * ε := by
  classical
  let N : ℕ := ⌈B - A⌉₊
  have hNlo : B ≤ A + N := by
    have h := Nat.le_ceil (B - A)
    change B - A ≤ (N : ℝ) at h
    linarith
  have hNhi : A + N ≤ B + 1 := by
    have h := (Nat.ceil_lt_add_one (sub_nonneg.mpr hAB)).le
    change (N : ℝ) ≤ B - A + 1 at h
    linarith
  have hmaxExists : ∀ n : ℕ, ∃ x ∈ Set.Icc (A + n) (A + n + 1),
      ∀ y ∈ Set.Icc (A + n) (A + n + 1), f y ≤ f x := by
    intro n
    exact isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr (by linarith)) hf.continuousOn
  choose t ht hmax using hmaxExists
  have htall : ∀ n, A + n ≤ t n ∧ t n ≤ A + n + 1 := ht
  have htRange : ∀ n ∈ Finset.range N, A ≤ t n ∧ t n ≤ B + 1 := by
    intro n hn
    have hnN : n + 1 ≤ N := Finset.mem_range.mp hn
    have hnN' : (n : ℝ) + 1 ≤ N := by exact_mod_cast hnN
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    constructor <;> linarith [(ht n).1, (ht n).2]
  have hunit : ∀ n ∈ Finset.range N, (∫ x in (A + n)..(A + (n + 1 : ℕ)), f x) ≤ f (t n) := by
    intro n _
    have hb := intervalIntegral.integral_mono_on (μ := volume)
      (show A + n ≤ A + n + 1 by linarith)
      (hf.intervalIntegrable (A + n) (A + n + 1))
      (continuous_const.intervalIntegrable (A + n) (A + n + 1)) (hmax n)
    rw [intervalIntegral.integral_const, smul_eq_mul,
      show A + n + 1 - (A + n) = 1 by ring, one_mul] at hb
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using hb
  have hpartition : (∫ x in A..(A + N), f x) =
      ∑ n ∈ Finset.range N, ∫ x in (A + n)..(A + (n + 1 : ℕ)), f x := by
    simpa only [Nat.cast_zero, add_zero] using
      (intervalIntegral.sum_integral_adjacent_intervals (a := fun n : ℕ ↦ A + n)
        (n := N) (fun n _ ↦ hf.intervalIntegrable _ _)).symm
  let F₀ := (Finset.range N).filter (fun n ↦ n % 2 = 0)
  let F₁ := (Finset.range N).filter (fun n ↦ ¬n % 2 = 0)
  have hzero : (∑ n ∈ F₀, f (t n)) ≤ ε := by
    apply hsample F₀ t (fun i hi ↦ htRange i (Finset.mem_filter.mp hi).1)
    intro i hi j hj hij
    exact unit_cells_separated_of_equal_parity htall hij
      ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm)
  have hone : (∑ n ∈ F₁, f (t n)) ≤ ε := by
    apply hsample F₁ t (fun i hi ↦ htRange i (Finset.mem_filter.mp hi).1)
    intro i hi j hj hij
    have hi0 := (Finset.mem_filter.mp hi).2
    have hj0 := (Finset.mem_filter.mp hj).2
    apply unit_cells_separated_of_equal_parity htall hij
    omega
  have hsplit : (∑ n ∈ F₀, f (t n)) + (∑ n ∈ F₁, f (t n)) =
      ∑ n ∈ Finset.range N, f (t n) := Finset.sum_filter_add_sum_filter_not _ _ _
  calc
    _ ≤ ∫ x in A..(A + N), f x := intervalIntegral.integral_mono_interval le_rfl hAB hNlo
      (Filter.Eventually.of_forall hf0) (hf.intervalIntegrable _ _)
    _ = _ := hpartition
    _ ≤ ∑ n ∈ Finset.range N, f (t n) := Finset.sum_le_sum hunit
    _ = (∑ n ∈ F₀, f (t n)) + ∑ n ∈ F₁, f (t n) := hsplit.symm
    _ ≤ ε + ε := add_le_add hzero hone
    _ = _ := by ring

end Erdos421
