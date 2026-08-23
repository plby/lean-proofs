import ErdosProblems.Erdos1166.Erdos1166PotentialKernelAnalytic
import ErdosProblems.Erdos1166.Erdos1166HLOZPoissonOscillation

namespace Erdos1166.PotentialConvergence

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology
open HeatKernel KilledGreen

theorem planarPotentialKernel_sub_abs_le (u v : Site) :
    |planarPotentialKernel u - planarPotentialKernel v| ≤
      planarPotentialKernel (u - v) + 2500 := by
  have huv := planarPotentialKernel_quasiTriangle u v
  have hvu := planarPotentialKernel_quasiTriangle v u
  have hneg : v - u = -(u - v) := by abel
  rw [hneg, planarPotentialKernel_neg] at hvu
  rw [abs_le]
  constructor <;> linarith

theorem planarPotentialKernel_sub_abs_le_log
    {r : ℕ} (hr : 1 ≤ r) {u v : Site}
    (huv : siteNormInf (u - v) ≤ r) :
    |planarPotentialKernel u - planarPotentialKernel v| ≤
      (2 / Real.pi) * Real.log (r : ℝ) + 2520 := by
  have hbase := planarPotentialKernel_sub_abs_le u v
  by_cases hzero : u - v = 0
  · have huvEq : u = v := sub_eq_zero.mp hzero
    subst v
    simp only [sub_self, abs_zero]
    have hlog : 0 ≤ Real.log (r : ℝ) := by
      exact Real.log_nonneg (by exact_mod_cast hr)
    positivity
  · have hnorm : 0 < siteNormInf (u - v) :=
      siteNormInf_pos_of_ne_zero hzero
    have hupper := planarPotentialKernel_log_upper (u - v) hnorm
    have hlog : Real.log (siteNormInf (u - v) : ℝ) ≤ Real.log (r : ℝ) := by
      apply Real.log_le_log (by positivity)
      exact_mod_cast huv
    have hc : 0 ≤ 2 / Real.pi := by positivity
    nlinarith

theorem squareExitPotentialDifference_planarPotentialKernel_le_log
    {r R : ℕ} (hr : 1 ≤ r) {x x' y : Site}
    (hxx' : siteNormInf (x - x') ≤ r) :
    squareExitPotentialDifference R planarPotentialKernel x x' y ≤
      (2 / Real.pi) * Real.log (r : ℝ) + 2520 := by
  let B : ℝ := (2 / Real.pi) * Real.log (r : ℝ) + 2520
  have hB : 0 ≤ B := by
    have hlog : 0 ≤ Real.log (r : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hr)
    dsimp only [B]
    positivity
  unfold squareExitPotentialDifference
  calc
    (1 / 4 : ℝ) * ∑ d : Direction,
        (if y - directionStep d ∈ squareDisk R then
          |planarPotentialKernel (x - (y - directionStep d)) -
            planarPotentialKernel (x' - (y - directionStep d))|
        else 0) ≤
      (1 / 4 : ℝ) * ∑ _d : Direction, B := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Finset.sum_le_sum
        intro d hd
        split_ifs with hpred
        · apply planarPotentialKernel_sub_abs_le_log hr
          simpa only [sub_sub_sub_cancel_right] using hxx'
        · exact hB
    _ = B := by simp [B] <;> ring
    _ = (2 / Real.pi) * Real.log (r : ℝ) + 2520 := rfl

theorem planarPotentialKernel_boundary_bounds
    {R : ℕ} {p w : Site} (hp : p ∈ squareDisk R)
    (hwOuter : w ∈ squareDisk (R + 1)) (hw : w ∉ squareDisk R) :
    -1225 ≤ planarPotentialKernel (w - p) ∧
      planarPotentialKernel (w - p) ≤
        (2 / Real.pi) * Real.log ((2 * R + 1 : ℕ) : ℝ) + 20 := by
  have hwp : w - p ≠ 0 := by
    intro hzero
    have hEq : w = p := sub_eq_zero.mp hzero
    exact hw (hEq ▸ hp)
  have hnormPos : 0 < siteNormInf (w - p) :=
    siteNormInf_pos_of_ne_zero hwp
  have hnormOne : 1 ≤ siteNormInf (w - p) := hnormPos
  have hpNorm : siteNormInf p ≤ R := siteNormInf_le_of_mem_squareDisk hp
  have hwNorm : siteNormInf w ≤ R + 1 :=
    siteNormInf_le_of_mem_squareDisk hwOuter
  have hnormUpper : siteNormInf (w - p) ≤ 2 * R + 1 := by
    exact (siteNormInf_sub_le w p).trans (by omega)
  have hlower := planarPotentialKernel_log_lower (w - p) hnormPos
  have hupper := planarPotentialKernel_log_upper (w - p) hnormPos
  have hlogNonneg : 0 ≤ Real.log (siteNormInf (w - p) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hnormOne)
  have hlogUpper : Real.log (siteNormInf (w - p) : ℝ) ≤
      Real.log ((2 * R + 1 : ℕ) : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hnormUpper
  have hc : 0 ≤ 2 / Real.pi := by positivity
  constructor <;> nlinarith

theorem squareExitBoundaryPotentialRange_planarPotentialKernel_le_log
    (R : ℕ) (y : Site) :
    squareExitBoundaryPotentialRange R (fun _ ↦ -1225)
        (fun _ ↦ (2 / Real.pi) *
          Real.log ((2 * R + 1 : ℕ) : ℝ) + 20) y ≤
      (2 / Real.pi) * Real.log ((2 * R + 1 : ℕ) : ℝ) + 1245 := by
  let B : ℝ :=
    (2 / Real.pi) * Real.log ((2 * R + 1 : ℕ) : ℝ) + 1245
  have hB : 0 ≤ B := by
    have hone : (1 : ℝ) ≤ (2 * R + 1 : ℕ) := by exact_mod_cast (by omega : 1 ≤ 2 * R + 1)
    have hlog : 0 ≤ Real.log ((2 * R + 1 : ℕ) : ℝ) := Real.log_nonneg hone
    dsimp only [B]
    positivity
  unfold squareExitBoundaryPotentialRange
  calc
    (1 / 4 : ℝ) * ∑ d : Direction,
        (if y - directionStep d ∈ squareDisk R then
          ((2 / Real.pi) * Real.log ((2 * R + 1 : ℕ) : ℝ) + 20) - -1225
        else 0) ≤
      (1 / 4 : ℝ) * ∑ _d : Direction, B := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Finset.sum_le_sum
        intro d hd
        split_ifs <;> dsimp only [B] <;> linarith
    _ = B := by simp [B] <;> ring
    _ = (2 / Real.pi) * Real.log ((2 * R + 1 : ℕ) : ℝ) + 1245 := rfl

theorem one_fourth_le_squareGreenExitKernel_at_predecessor
    {R : ℕ} {p y : Site} (hp : p ∈ squareDisk R)
    (d : Direction) (hpy : p = y - directionStep d) :
    (1 / 4 : ℝ) ≤ squareGreenExitKernel R p y := by
  have hdiagENN : (1 : ℝ≥0∞) ≤ diskGreen R p p := by
    exact one_le_killedGreen_diagonal hp
  have hdiag : (1 : ℝ) ≤ (diskGreen R p p).toReal := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_le_toReal ENNReal.one_ne_top
      (diskGreen_ne_top R p p)).2 hdiagENN
  have hterm : (1 : ℝ) ≤
      (if y - directionStep d ∈ squareDisk R then
        (diskGreen R p (y - directionStep d)).toReal else 0) := by
    rw [← hpy]
    simp only [if_pos hp]
    exact hdiag
  have hsum : (1 : ℝ) ≤ ∑ e : Direction,
      if y - directionStep e ∈ squareDisk R then
        (diskGreen R p (y - directionStep e)).toReal else 0 := by
    calc
      (1 : ℝ) ≤
          (if y - directionStep d ∈ squareDisk R then
            (diskGreen R p (y - directionStep d)).toReal else 0) := hterm
      _ ≤ ∑ e : Direction,
          if y - directionStep e ∈ squareDisk R then
            (diskGreen R p (y - directionStep e)).toReal else 0 := by
        have hsingle := Finset.single_le_sum
          (s := (Finset.univ : Finset Direction))
          (f := fun e : Direction ↦
            if y - directionStep e ∈ squareDisk R then
              (diskGreen R p (y - directionStep e)).toReal else 0)
          (fun e he ↦ by
            split_ifs
            · exact ENNReal.toReal_nonneg
            · exact le_rfl)
          (Finset.mem_univ d)
        exact hsingle
  unfold squareGreenExitKernel
  nlinarith

/-- A strictly positive comparison denominator from an interior chain ending
one step before an exit predecessor.  This is the positivity input needed to
take the actual reference exit kernel itself as `denominatorLower`. -/
theorem squareGreenExitKernel_pos_of_inner_chain_to_predecessor
    {r R n : ℕ} {path : ℕ → Site} {η : ℕ → Direction}
    {y : Site} (hstep : ∀ k, k < n →
      path (k + 1) = path k + directionStep (η k))
    (hinner : ∀ k, k ≤ n → path k ∈ squareDisk r)
    (hrR : r + 1 ≤ R) (hy : y ∉ squareDisk R)
    (e d : Direction)
    (hexitStep : path n + directionStep e = y - directionStep d)
    (hpredecessor : y - directionStep d ∈ squareDisk R) :
    0 < squareGreenExitKernel R (path 0) y := by
  let p : Site := y - directionStep d
  have hpn : path n ∈ squareDisk R :=
    squareDisk_mono (by omega : r ≤ R) (hinner n le_rfl)
  have hfar : ∀ d' : Direction, path n ≠ y - directionStep d' :=
    inner_point_not_exit_predecessor (hinner n le_rfl) hrR hy
  have hlocal := squareGreenExitKernel_neighbor_le_four_mul
    (R := R) (x := path n) (y := y) hpn hfar e
  rw [hexitStep] at hlocal
  have hpredLower : (1 / 4 : ℝ) ≤ squareGreenExitKernel R p y := by
    exact one_fourth_le_squareGreenExitKernel_at_predecessor
      hpredecessor d rfl
  have hchain := squareGreenExitKernel_chain_le
    (R := R) (y := y) hstep hinner hrR hy
  have hpow : 0 < (4 : ℝ) ^ n := by positivity
  dsimp only [p] at hpredLower
  have hpositiveProduct : 0 < (4 : ℝ) ^ n *
      squareGreenExitKernel R (path 0) y := by
    nlinarith
  rcases mul_pos_iff.mp hpositiveProduct with h | h
  · exact h.2
  · exact (not_lt_of_ge hpow.le h.1).elim

theorem squareGreenExitKernel_self_denominator
    {R : ℕ} {x y : Site} (hpos : 0 < squareGreenExitKernel R x y) :
    0 < squareGreenExitKernel R x y ∧
      squareGreenExitKernel R x y ≤ squareGreenExitKernel R x y :=
  ⟨hpos, le_rfl⟩

/-- All potential-kernel fields of the Appendix-A exit comparison, with the
actual reference exit kernel used as the positive denominator. -/
theorem firstExitAtWeight_square_ratio_planarPotentialKernel_le
    {r R : ℕ} (hr : 1 ≤ r) {x x' y : Site}
    (hx : x ∈ squareDisk R) (hx' : x' ∈ squareDisk R)
    (hy : y ∉ squareDisk R)
    (hxx' : siteNormInf (x - x') ≤ r)
    (hdenpos : 0 < squareGreenExitKernel R x' y) :
    |(firstExitAtWeight (squareDisk R : Set Site) x y).toReal /
        (firstExitAtWeight (squareDisk R : Set Site) x' y).toReal - 1| ≤
      ((2 / Real.pi) * Real.log (r : ℝ) + 2520 +
        ((2 / Real.pi) * Real.log ((2 * R + 1 : ℕ) : ℝ) + 1245)) /
          squareGreenExitKernel R x' y := by
  let lowerBoundary : Site → ℝ := fun _ ↦ -1225
  let upperBoundary : Site → ℝ := fun _ ↦
    (2 / Real.pi) * Real.log ((2 * R + 1 : ℕ) : ℝ) + 20
  have hboundary : ∀ d : Direction,
      y - directionStep d ∈ squareDisk R →
      ∀ w ∈ squareDisk (R + 1), w ∉ squareDisk R →
        lowerBoundary (y - directionStep d) ≤
            planarPotentialKernel (w - (y - directionStep d)) ∧
          planarPotentialKernel (w - (y - directionStep d)) ≤
            upperBoundary (y - directionStep d) := by
    intro d hpred w hwOuter hw
    simpa only [lowerBoundary, upperBoundary] using
      planarPotentialKernel_boundary_bounds hpred hwOuter hw
  have hratio :=
    firstExitAtWeight_square_ratio_sub_one_abs_le_potential_boundary
      (R := R) (a := planarPotentialKernel) planarPotentialKernel_isPlanar
      hx hx' lowerBoundary upperBoundary hy hdenpos le_rfl hboundary
  have hpotential :=
    squareExitPotentialDifference_planarPotentialKernel_le_log
      (R := R) (y := y) hr hxx'
  have hboundaryRange :=
    squareExitBoundaryPotentialRange_planarPotentialKernel_le_log R y
  have hnum :
      squareExitPotentialDifference R planarPotentialKernel x x' y +
          squareExitBoundaryPotentialRange R lowerBoundary upperBoundary y ≤
        (2 / Real.pi) * Real.log (r : ℝ) + 2520 +
          ((2 / Real.pi) * Real.log ((2 * R + 1 : ℕ) : ℝ) + 1245) := by
    simpa only [lowerBoundary, upperBoundary] using
      add_le_add hpotential hboundaryRange
  exact hratio.trans (div_le_div_of_nonneg_right hnum hdenpos.le)

end Erdos1166.PotentialConvergence
