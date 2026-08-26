import ErdosProblems.Erdos1165.RadialHarnackSpecialization

/-! # Coarse spatial estimates for the covering argument -/

namespace Erdos1164

open Erdos1165 Erdos1165.Annulus Erdos1165.PotentialConvergence
open Erdos1165.PotentialEuclideanGeometry Erdos1165.PotentialRadialAll
open Erdos1165.RadialHarnackSpecialization

noncomputable def potentialSlope : ℝ := 2 / Real.pi
noncomputable def potentialError : ℝ := |PotentialRadialAsymptotic.cPotential| + 6500000010

theorem potentialSlope_pos : 0 < potentialSlope := by
  unfold potentialSlope
  positivity

theorem potentialSlope_le_one : potentialSlope ≤ 1 := by
  unfold potentialSlope
  exact (div_le_one Real.pi_pos).mpr Real.two_le_pi

theorem potentialError_pos : 0 < potentialError := by
  unfold potentialError
  positivity

/-- A single absolute error suffices for all radii used below. -/
theorem potential_log_error {x : Point} (hx : 4 ≤ euclideanRadius x) :
    |planarPotentialKernel x - potentialSlope * Real.log (euclideanRadius x)| ≤
      potentialError - 10 := by
  have h := abs_planarPotentialKernel_sub_log_euclideanRadius_sub_cPotential_le hx
  have herr : 6500000000 / euclideanRadius x ≤ 6500000000 := by
    apply (div_le_iff₀ (by linarith : 0 < euclideanRadius x)).mpr
    linarith
  have htri := abs_add_le
    (planarPotentialKernel x - potentialSlope * Real.log (euclideanRadius x) -
      PotentialRadialAsymptotic.cPotential) PotentialRadialAsymptotic.cPotential
  rw [sub_add_cancel] at htri
  unfold potentialSlope at htri
  unfold potentialSlope potentialError
  linarith

/-- Coarse squared triangle inequalities avoid any choice of a normed-space
representation of the lattice. -/
theorem euclideanRadius_sub_sq_le (x y : Point) :
    euclideanRadius (x - y) ^ 2 ≤ 2 * euclideanRadius x ^ 2 + 2 * euclideanRadius y ^ 2 := by
  simp only [euclideanRadius_sq, euclideanRadiusSq, Prod.fst_sub, Prod.snd_sub, Int.cast_sub]
  nlinarith [sq_nonneg ((x.1 : ℝ) + y.1), sq_nonneg ((x.2 : ℝ) + y.2)]

theorem euclideanRadius_sq_le_sub (x y : Point) :
    euclideanRadius x ^ 2 ≤ 2 * euclideanRadius (x - y) ^ 2 + 2 * euclideanRadius y ^ 2 := by
  have h := euclideanRadius_sub_sq_le (x - y) (-y)
  simpa only [sub_neg_eq_add, sub_add_cancel, euclideanRadius, euclideanRadiusSq,
    Prod.fst_neg, Prod.snd_neg, Int.cast_neg, neg_sq] using h

/-- Boundary distances remain within a factor two when the target is in the
inner quarter of a sufficiently large disc. -/
theorem boundary_distance_bounds {R : ℕ} (hR : 8 ≤ R) {y z : Point}
    (hy : euclideanRadius y ≤ (R : ℝ) / 4)
    (hz : z ∈ outerBoundary (closedDisc R)) :
    (R : ℝ) / 2 ≤ euclideanRadius (z - y) ∧
      euclideanRadius (z - y) ≤ 2 * R := by
  have hzR := outerBoundary_closedDisc_euclideanRadius_bounds hz
  have hlow := euclideanRadius_sq_le_sub z y
  have hupp := euclideanRadius_sub_sq_le z y
  have hr : (8 : ℝ) ≤ R := by exact_mod_cast hR
  have hny := euclideanRadius_nonneg y
  have hnz := euclideanRadius_nonneg z
  have hnd := euclideanRadius_nonneg (z - y)
  have hysq : euclideanRadius y ^ 2 ≤ ((R : ℝ) / 4) ^ 2 := by nlinarith
  have hzlo : (R : ℝ) ^ 2 ≤ euclideanRadius z ^ 2 := by nlinarith
  have hzup : euclideanRadius z ^ 2 ≤ ((R : ℝ) + 1) ^ 2 := by nlinarith
  constructor <;> nlinarith

/-- A common boundary window for every target in the inner quarter disc. -/
theorem boundary_potential_window {R : ℕ} (hR : 8 ≤ R) {y z : Point}
    (hy : euclideanRadius y ≤ (R : ℝ) / 4)
    (hz : z ∈ outerBoundary (closedDisc R)) :
    potentialSlope * Real.log (R : ℝ) - potentialError ≤ planarPotentialKernel (z - y) ∧
      planarPotentialKernel (z - y) ≤ potentialSlope * Real.log (R : ℝ) + potentialError := by
  have hb := boundary_distance_bounds hR hy hz
  have hr : (8 : ℝ) ≤ R := by exact_mod_cast hR
  have hrpos : (0 : ℝ) < R := by linarith
  have hdpos : 0 < euclideanRadius (z - y) := by linarith
  have he := abs_le.mp (potential_log_error (by linarith : 4 ≤ euclideanRadius (z - y)))
  have hlo := Real.log_le_log (by positivity : (0 : ℝ) < (R : ℝ) / 2) hb.1
  have hup := Real.log_le_log hdpos hb.2
  rw [Real.log_div hrpos.ne' (by norm_num : (2 : ℝ) ≠ 0)] at hlo
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hrpos.ne'] at hup
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog2up : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hs := potentialSlope_pos.le
  have hsmall : potentialSlope * Real.log 2 ≤ 1 :=
    (mul_le_mul_of_nonneg_right potentialSlope_le_one hlog2).trans (by simpa using hlog2up)
  have hlom := mul_le_mul_of_nonneg_left hlo hs
  have hupm := mul_le_mul_of_nonneg_left hup hs
  constructor <;> nlinarith

end Erdos1164
