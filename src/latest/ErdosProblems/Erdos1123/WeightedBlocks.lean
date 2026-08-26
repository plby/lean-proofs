import ErdosProblems.Erdos1123.WeightedQuotient
import ErdosProblems.Erdos1123.RatioLimits
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp

/-! # The geometric-block criterion for weighted density zero -/

namespace Erdos1123

open Filter
open scoped Topology Classical

/-- The weighted count of a set in `1, ..., n`. -/
noncomputable def cumulative (w : ℕ → ℝ) (A : Set ℕ) (n : ℕ) : ℝ :=
  ∑ x ∈ Finset.Ioc 0 n, if x ∈ A then w x else 0

theorem cumulative_eq_sum_filter (w : ℕ → ℝ) (A : Set ℕ) (n : ℕ) :
    cumulative w A n = ∑ x ∈ (Finset.Icc 1 n).filter (· ∈ A), w x := by
  have hI : Finset.Ioc 0 n = Finset.Icc 1 n := by
    ext x
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  simp only [cumulative, hI, Finset.sum_filter]

theorem cumulative_nonneg {w : ℕ → ℝ} (hw : ∀ x, 0 ≤ w x) (A : Set ℕ) (n : ℕ) :
    0 ≤ cumulative w A n := by
  apply Finset.sum_nonneg
  intro x _
  split_ifs
  · exact hw x
  · exact le_rfl

theorem cumulative_mono {w : ℕ → ℝ} (hw : ∀ x, 0 ≤ w x) (A : Set ℕ) :
    Monotone (cumulative w A) := by
  intro n m hnm
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx
    exact Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hx).1, (Finset.mem_Ioc.mp hx).2.trans hnm⟩
  · intro x _ _
    split_ifs
    · exact hw x
    · exact le_rfl

theorem cumulative_increment (w : ℕ → ℝ) (A : Set ℕ) {n m : ℕ} (hnm : n ≤ m) :
    cumulative w A m - cumulative w A n =
      ∑ x ∈ Finset.Ioc n m, if x ∈ A then w x else 0 := by
  have h := Finset.sum_Ioc_consecutive (fun x => if x ∈ A then w x else 0) (Nat.zero_le n) hnm
  unfold cumulative
  linarith

/-- Block weights use the sampled prefix denominator; total block mass need
only tend to one, not equal one at each finite coordinate. -/
noncomputable def geometricBlocks (w D : ℕ → ℝ) (b : ℕ → ℕ)
    (hw : ∀ x, 0 ≤ w x) (hD : ∀ n, 0 ≤ D n) : WeightSequence ℕ where
  support n := Finset.Ioc (b n) (b (n + 1))
  weight n x := w x / D (b n)
  nonneg n x := div_nonneg (hw x) (hD (b n))

theorem geometricBlocks_mass (w D : ℕ → ℝ) (b : ℕ → ℕ)
    (hw : ∀ x, 0 ≤ w x) (hD : ∀ n, 0 ≤ D n) (hb : Monotone b)
    (A : Set ℕ) (n : ℕ) :
    (geometricBlocks w D b hw hD).mass A n =
      (cumulative w A (b (n + 1)) - cumulative w A (b n)) / D (b n) := by
  rw [cumulative_increment w A (hb (Nat.le_succ n))]
  simp only [WeightSequence.mass, geometricBlocks, Finset.sum_div, ite_div, zero_div]

theorem geometricBlocks_disjoint (w D : ℕ → ℝ) (b : ℕ → ℕ)
    (hw : ∀ x, 0 ≤ w x) (hD : ∀ n, 0 ≤ D n) (hb : StrictMono b)
    (n m : ℕ) (hnm : n ≠ m) :
    Disjoint ((geometricBlocks w D b hw hD).support n)
      ((geometricBlocks w D b hw hD).support m) := by
  apply Finset.disjoint_left.mpr
  intro x hxn hxm
  obtain ⟨hn₁, hn₂⟩ := Finset.mem_Ioc.mp hxn
  obtain ⟨hm₁, hm₂⟩ := Finset.mem_Ioc.mp hxm
  rcases lt_or_gt_of_ne hnm with hlt | hgt
  · have h : b (n + 1) ≤ b m := hb.monotone (by omega)
    omega
  · have h : b (m + 1) ≤ b n := hb.monotone (by omega)
    omega

/-- The weighted density-zero ideal equals the block-null ideal whenever the
prefix denominator doubles at the chosen block boundaries. -/
theorem geometricBlocks_null_iff (w D : ℕ → ℝ) (b : ℕ → ℕ)
    (hw : ∀ x, 0 ≤ w x) (hD : ∀ n, 0 ≤ D n) (hb : StrictMono b)
    (hDMono : Monotone D) (hDTop : Tendsto D atTop atTop)
    (hDPos : ∀ k, 0 < D (b k)) (hDouble : ∀ k, D (b (k + 1)) = 2 * D (b k))
    (A : Set ℕ) :
    (geometricBlocks w D b hw hD).IsNull A ↔
      Tendsto (fun n => cumulative w A n / D n) atTop (𝓝 0) := by
  have hSample := ratio_zero_iff_sampled (cumulative w A) D b (cumulative_nonneg hw A)
    hD (cumulative_mono hw A) hDMono hb hDPos (fun k => (hDouble k).le)
  constructor
  · intro hBlock
    apply hSample.mpr
    apply ratio_zero_of_increment_ratio_zero (fun k => cumulative w A (b k)) (fun k => D (b k))
      (fun k => cumulative_nonneg hw A (b k)) hDPos
    · intro k
      rw [hDouble]
      linarith [hDPos k]
    · exact hDTop.comp hb.tendsto_atTop
    · have heq : (fun n =>
          (cumulative w A (b (n + 1)) - cumulative w A (b n)) /
            (D (b (n + 1)) - D (b n))) = (geometricBlocks w D b hw hD).mass A := by
        funext n
        rw [geometricBlocks_mass w D b hw hD hb.monotone, hDouble]
        congr 1
        ring
      rw [heq]
      exact hBlock
  · intro hPrefix
    have hs := hSample.mp hPrefix
    have hnext : Tendsto (fun n => cumulative w A (b (n + 1)) / D (b (n + 1))) atTop (𝓝 0) :=
      (tendsto_add_atTop_iff_nat 1).2 hs
    have hlim := (hnext.const_mul 2).sub hs
    have heq : (fun n => 2 * (cumulative w A (b (n + 1)) / D (b (n + 1))) -
        cumulative w A (b n) / D (b n)) = (geometricBlocks w D b hw hD).mass A := by
      funext n
      rw [geometricBlocks_mass w D b hw hD hb.monotone, hDouble]
      field_simp [(hDPos n).ne']
    simpa only [WeightSequence.IsNull, heq, mul_zero, sub_zero] using hlim

end Erdos1123
