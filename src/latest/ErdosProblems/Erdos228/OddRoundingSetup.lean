import ErdosProblems.Erdos228.OddSine

/-!
# The explicit second-colouring mesh for the odd sine construction

This file supplies the finite mesh and the numerical parameters used in the
second BBMST colouring.  The mesh consists of the midpoints of the `16 * n`
equal subintervals of the first quadrant.
-/

namespace Erdos228.OddSine

open scoped BigOperators Interval
open Set

noncomputable section

/-- The number of equal pieces into which the first quadrant is divided. -/
def roundingMeshSize (n : ℕ) : ℕ := 16 * n

/-- The midpoint of the `g`-th piece of the first-quadrant mesh. -/
def roundingMeshPoint (n : ℕ) (g : Fin (roundingMeshSize n)) : ℝ :=
  (2 * (g : ℕ) + 1 : ℕ) * Real.pi / (64 * n)

/-- The BBMST parameter attached to derivative order `l`. -/
def roundingParameter (l : ℕ) : ℝ :=
  14 * Real.sqrt ((9 + l : ℕ) * Real.log 2)

@[simp] theorem roundingMeshSize_eq (n : ℕ) : roundingMeshSize n = 16 * n := rfl

theorem roundingParameter_nonneg (l : ℕ) : 0 ≤ roundingParameter l := by
  exact mul_nonneg (by norm_num) (Real.sqrt_nonneg _)

/-- Squaring the chosen parameter removes its square root exactly. -/
theorem roundingParameter_sq (l : ℕ) :
    (roundingParameter l) ^ 2 = 196 * ((9 + l : ℕ) * Real.log 2) := by
  rw [roundingParameter, mul_pow, Real.sq_sqrt]
  · norm_num
  · exact mul_nonneg (by positivity) (Real.log_nonneg (by norm_num))

/-- Each exponential weight is the corresponding dyadic geometric term. -/
theorem exp_roundingParameter (l : ℕ) :
    Real.exp (-(roundingParameter l) ^ 2 / 196) =
      (1 / 2 : ℝ) ^ (9 + l) := by
  rw [roundingParameter_sq]
  have hcancel :
      -(196 * (((9 + l : ℕ) : ℝ) * Real.log 2)) / 196 =
        -(((9 + l : ℕ) : ℝ) * Real.log 2) := by ring
  rw [hcancel]
  calc
    Real.exp (-(((9 + l : ℕ) : ℝ) * Real.log 2)) =
        Real.exp (((9 + l : ℕ) : ℝ) * (-Real.log 2)) := by ring_nf
    _ = Real.exp (-Real.log 2) ^ (9 + l) := Real.exp_nat_mul _ _
    _ = (1 / 2 : ℝ) ^ (9 + l) := by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      norm_num

/-- The finite geometric sum needed by the exponential budget. -/
theorem sum_exp_roundingParameter_le (n : ℕ) :
    (∑ l : Fin n, Real.exp (-(roundingParameter l) ^ 2 / 196)) ≤
      (1 / 256 : ℝ) := by
  simp_rw [exp_roundingParameter]
  calc
    (∑ l : Fin n, (1 / 2 : ℝ) ^ (9 + (l : ℕ))) =
        (1 / 512 : ℝ) * ∑ l : Fin n, (1 / 2 : ℝ) ^ (l : ℕ) := by
          simp_rw [pow_add]
          norm_num
          rw [Finset.mul_sum]
    _ ≤ (1 / 512 : ℝ) * 2 := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      rw [Fin.sum_univ_eq_sum_range]
      exact sum_geometric_two_le n
    _ = 1 / 256 := by norm_num

/-- The numerical parameter bound used after the full-colouring theorem. -/
theorem roundingParameter_add_thirty_le (l : ℕ) :
    roundingParameter l + 30 ≤ 65 + 2 * l := by
  have htwo_exp : (2 : ℝ) < Real.exp (25 / 36) := by
    refine lt_of_lt_of_le ?_
      (Real.sum_le_exp_of_nonneg (x := (25 / 36 : ℝ)) (by norm_num) 5)
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hlog : Real.log 2 < 25 / 36 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 2)]
    exact htwo_exp
  have hradicand :
      ((9 + l : ℕ) : ℝ) * Real.log 2 ≤
        ((35 + 2 * (l : ℝ)) / 14) ^ 2 := by
    push_cast
    have hmul := mul_le_mul_of_nonneg_left (le_of_lt hlog)
      (show (0 : ℝ) ≤ ((9 + l : ℕ) : ℝ) by positivity)
    push_cast at hmul
    nlinarith [sq_nonneg (l : ℝ)]
  have hsqrt := Real.sqrt_le_sqrt hradicand
  have hright : 0 ≤ (35 + 2 * (l : ℝ)) / 14 := by positivity
  rw [Real.sqrt_sq hright] at hsqrt
  unfold roundingParameter
  nlinarith

/-- Every point in the first quadrant is within half a mesh spacing of a
mesh midpoint. -/
theorem exists_roundingMeshPoint {n : ℕ} (hn : 0 < n) (theta : ℝ)
    (htheta : theta ∈ Icc (0 : ℝ) (Real.pi / 2)) :
    ∃ g : Fin (roundingMeshSize n),
      |theta - roundingMeshPoint n g| ≤ Real.pi / (64 * n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hmesh : 0 < roundingMeshSize n := by
    simp [roundingMeshSize, hn]
  by_cases hend : theta = Real.pi / 2
  · let g : Fin (roundingMeshSize n) :=
      ⟨roundingMeshSize n - 1, Nat.sub_lt hmesh (by omega)⟩
    refine ⟨g, ?_⟩
    have hsub : (roundingMeshSize n - 1 : ℕ) + 1 = roundingMeshSize n := by
      omega
    have hdifference :
        theta - roundingMeshPoint n g = Real.pi / (64 * n) := by
      rw [hend]
      simp only [roundingMeshPoint, g]
      rw [show 2 * (roundingMeshSize n - 1) + 1 =
          2 * roundingMeshSize n - 1 by omega]
      simp only [roundingMeshSize]
      push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * (16 * n))]
      field_simp
      ring
    rw [hdifference, abs_of_nonneg (by positivity)]
  · have htheta_lt : theta < Real.pi / 2 :=
      lt_of_le_of_ne htheta.2 hend
    let y : ℝ := theta * (32 * n) / Real.pi
    have hy_nonneg : 0 ≤ y := by
      exact div_nonneg (mul_nonneg htheta.1 (by positivity)) hpi.le
    have hy_lt : y < (roundingMeshSize n : ℕ) := by
      rw [roundingMeshSize]
      apply (div_lt_iff₀ hpi).2
      have hmul := mul_lt_mul_of_pos_right htheta_lt
        (show (0 : ℝ) < 32 * n by positivity)
      push_cast at hmul ⊢
      nlinarith
    let k : ℕ := ⌊y⌋₊
    have hk_le : (k : ℝ) ≤ y := Nat.floor_le hy_nonneg
    have hy_succ : y < (k : ℝ) + 1 := by
      simpa [k] using Nat.lt_floor_add_one y
    have hk_mesh : k < roundingMeshSize n := by
      exact_mod_cast lt_of_le_of_lt hk_le hy_lt
    let g : Fin (roundingMeshSize n) := ⟨k, hk_mesh⟩
    refine ⟨g, ?_⟩
    have habs : |y - ((k : ℝ) + 1 / 2)| ≤ 1 / 2 := by
      rw [abs_le]
      constructor <;> linarith
    have hdifference :
        theta - roundingMeshPoint n g =
          (y - ((k : ℝ) + 1 / 2)) * (Real.pi / (32 * n)) := by
      simp only [roundingMeshPoint, g]
      dsimp only [y]
      push_cast
      field_simp
      ring
    rw [hdifference, abs_mul, abs_of_nonneg (by positivity :
      0 ≤ Real.pi / (32 * (n : ℝ)))]
    calc
      |y - ((k : ℝ) + 1 / 2)| * (Real.pi / (32 * n)) ≤
          (1 / 2) * (Real.pi / (32 * n)) :=
        mul_le_mul_of_nonneg_right habs (by positivity)
      _ = Real.pi / (64 * n) := by ring

/-- The explicit BBMST second-colouring setup. -/
def explicitRoundingSetup {n : ℕ} (hn : 0 < n) :
    RoundingSetup n (Fin (roundingMeshSize n)) where
  point := roundingMeshPoint n
  parameter := fun q ↦ roundingParameter q.2
  parameter_nonneg := fun q ↦ roundingParameter_nonneg q.2
  budget := by
    rw [Fintype.sum_prod_type]
    simp only
    calc
      (∑ _g : Fin (roundingMeshSize n),
          ∑ l : Fin n, Real.exp (-(roundingParameter l) ^ 2 / 196)) =
          (roundingMeshSize n : ℝ) *
            ∑ l : Fin n, Real.exp (-(roundingParameter l) ^ 2 / 196) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
      _ ≤ (roundingMeshSize n : ℝ) * (1 / 256 : ℝ) := by
        apply mul_le_mul_of_nonneg_left (sum_exp_roundingParameter_le n)
        positivity
      _ = (n : ℝ) / 16 := by
        simp [roundingMeshSize]
        ring
  parameter_bound := fun _g l ↦ roundingParameter_add_thirty_le l
  cover := by
    intro a theta
    obtain ⟨theta', htheta', habs⟩ :=
      exists_firstQuadrant_abs_oddSineSum_eq n a theta
    obtain ⟨g, hnear⟩ := exists_roundingMeshPoint hn theta' htheta'
    exact ⟨g, theta', hnear, habs⟩

/-- There is an explicit second-colouring setup for every positive `n`, with
no additional geometric or numerical hypotheses. -/
theorem exists_roundingSetup {n : ℕ} (hn : 0 < n) :
    Nonempty (RoundingSetup n (Fin (16 * n))) := by
  exact ⟨explicitRoundingSetup hn⟩

end

end Erdos228.OddSine
