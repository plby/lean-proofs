import ErdosProblems.Erdos19.ReservoirLoads
import ErdosProblems.Erdos19.DiscreteGrowth
import Mathlib.Data.Nat.Cast.Order.Field

/-! # Deterministic bounds for the cumulative repair load -/

namespace Erdos19

def packingTotalBound (n a c K : ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => packingTotalBound n a c K i +
      3 * c * (5 * a + K * packingTotalBound n a c K i / n + 3)

def packingLoadBound (n a c K i : ℕ) : ℕ :=
  K * packingTotalBound n a c K i / n + 2

theorem packingTotalBound_succ (n a c K i : ℕ) :
    packingTotalBound n a c K (i + 1) = packingTotalBound n a c K i +
      3 * (c * (5 * a + packingLoadBound n a c K i + 1)) := by
  simp only [packingTotalBound, packingLoadBound]
  ring

theorem packingTotalBound_monotone (n a c K : ℕ) : Monotone (packingTotalBound n a c K) := by
  apply monotone_nat_of_le_succ
  intro i
  rw [packingTotalBound_succ]
  exact Nat.le_add_right _ _

theorem packingLoadBound_monotone (n a c K : ℕ) : Monotone (packingLoadBound n a c K) := by
  intro i j hij
  exact Nat.add_le_add_right
    (Nat.div_le_div_right (Nat.mul_le_mul_left K (packingTotalBound_monotone n a c K hij))) 2

theorem IsLoadBalanced.le_packingLoadBound {V : Type*} [Fintype V] [DecidableEq V]
    (load : V → ℕ) (a c K i : ℕ) (hn : 0 < Fintype.card V)
    (hbal : IsLoadBalanced K load)
    (htotal : totalLoad load ≤ packingTotalBound (Fintype.card V) a c K i) :
    ∀ v, load v ≤ packingLoadBound (Fintype.card V) a c K i := by
  intro v
  have h : load v * Fintype.card V ≤
      K * packingTotalBound (Fintype.card V) a c K i + 2 * Fintype.card V := by
    have ht := Nat.mul_le_mul_left K htotal
    have hb := hbal v
    nlinarith only [ht, hb]
  have hd := (Nat.le_div_iff_mul_le hn).mpr h
  simpa only [Nat.add_mul_div_right _ _ hn, packingLoadBound] using hd

theorem packingTotalBound_le_exponential (n a c K : ℕ) (hn : 0 < n) (i : ℕ) (hi : i ≤ n) :
    (packingTotalBound n a c K i : ℝ) ≤
      (3 * c * (5 * a + 3)) * n * Real.exp (3 * c * K) := by
  have hstep : ∀ j < n,
      (packingTotalBound n a c K (j + 1) : ℝ) ≤
        (1 + (3 * c * K : ℝ) / n) * packingTotalBound n a c K j + 3 * c * (5 * a + 3) := by
    intro j _
    have hd : ((K * packingTotalBound n a c K j / n : ℕ) : ℝ) ≤
        (K : ℝ) * packingTotalBound n a c K j / n := by
      simpa only [Nat.cast_mul] using
        (Nat.cast_div_le (m := K * packingTotalBound n a c K j) (n := n) (α := ℝ))
    rw [packingTotalBound]
    push_cast
    calc
      (packingTotalBound n a c K j : ℝ) + 3 * c *
          (5 * a + (K * packingTotalBound n a c K j / n : ℕ) + 3) ≤
        packingTotalBound n a c K j + 3 * c *
          (5 * a + (K : ℝ) * packingTotalBound n a c K j / n + 3) := by
        nlinarith only [mul_le_mul_of_nonneg_left hd (show (0 : ℝ) ≤ 3 * c by positivity)]
      _ = _ := by ring
  exact affine_growth_le_exponential (fun j ↦ (packingTotalBound n a c K j : ℝ))
    (3 * c * K) (3 * c * (5 * a + 3)) (by positivity) (by positivity)
    (by simp [packingTotalBound]) n hn hstep i hi

theorem packingLoadBound_le_exponential (n a c K : ℕ) (hn : 0 < n) (i : ℕ) (hi : i ≤ n) :
    (packingLoadBound n a c K i : ℝ) ≤
      (3 * c * K * (5 * a + 3)) * Real.exp (3 * c * K) + 2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hd : ((K * packingTotalBound n a c K i / n : ℕ) : ℝ) ≤
      (K : ℝ) * packingTotalBound n a c K i / n := by
    simpa only [Nat.cast_mul] using
      (Nat.cast_div_le (m := K * packingTotalBound n a c K i) (n := n) (α := ℝ))
  have ht := packingTotalBound_le_exponential n a c K hn i hi
  have hdiv := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ht
    (show (0 : ℝ) ≤ K by positivity)) hnR.le
  have heq : (K : ℝ) * ((3 * c * (5 * a + 3)) * n * Real.exp (3 * c * K)) / n =
      (3 * c * K * (5 * a + 3)) * Real.exp (3 * c * K) := by
    field_simp
  rw [heq] at hdiv
  dsimp only [packingLoadBound]
  push_cast
  linarith only [hd, hdiv]

#print axioms packingLoadBound_le_exponential

theorem eventually_packing_load_small (c K B : ℕ) (hB : 0 < B) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ a : ℕ, (a : ℝ) ≤ epsilon * n + 2 → ∀ i ≤ n,
        B * a ≤ n ∧ B * packingLoadBound n a c K i ≤ n := by
  let C : ℝ := 3 * c * K * Real.exp (3 * c * K)
  let epsilon : ℝ := 1 / (20 * B * (C + 1))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hepsilon : 0 < epsilon := by dsimp [epsilon]; positivity
  have hε : (20 * B * (C + 1)) * epsilon = 1 := by
    dsimp only [epsilon]
    field_simp
  obtain ⟨N, hN⟩ := exists_nat_gt (4 * B * (13 * C + 4))
  refine ⟨epsilon, hepsilon, N, ?_⟩
  intro n hn a ha i hi
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hnR : (0 : ℝ) < n := by nlinarith only [hN, hNn, hC, hBR]
  have hnpos : 0 < n := by exact_mod_cast hnR
  have hnlarge : 4 * B * (13 * C + 4) < (n : ℝ) := hN.trans_le hNn
  have hεn := congrArg (fun x : ℝ ↦ x * n) hε
  have haB := mul_le_mul_of_nonneg_left ha hBR.le
  have hCε : 0 ≤ (B : ℝ) * C * epsilon * n := by positivity
  have hεn0 : 0 ≤ (B : ℝ) * epsilon * n := by positivity
  have hBa : (B : ℝ) * a ≤ n := by
    nlinarith only [haB, hεn, hCε, hnlarge, hBR, mul_nonneg hBR.le hC]
  have hload := packingLoadBound_le_exponential n a c K hnpos i hi
  have hload' : (packingLoadBound n a c K i : ℝ) ≤ C * (5 * a + 3) + 2 := by
    dsimp only [C]
    nlinarith only [hload]
  have hlB := mul_le_mul_of_nonneg_left hload' hBR.le
  have haBC := mul_le_mul_of_nonneg_left ha (mul_nonneg hBR.le hC)
  have hBL : (B : ℝ) * packingLoadBound n a c K i ≤ n := by
    nlinarith only [hlB, haBC, hεn, hεn0, hnlarge, hBR, mul_nonneg hBR.le hC]
  exact ⟨by exact_mod_cast hBa, by exact_mod_cast hBL⟩

#print axioms eventually_packing_load_small

end Erdos19
