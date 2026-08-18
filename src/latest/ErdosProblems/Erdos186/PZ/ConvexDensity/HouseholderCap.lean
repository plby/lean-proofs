/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.ConvexDensity.CapToGraph
import ErdosProblems.Erdos186.PZ.ConvexDensity.BoundaryGraph

/-!
# Householder straightening of a finite direction cap

This file turns the projective cap control from `CapToGraph` into ordinary
Euclidean graph coordinates after the representative is sent to the last
basis vector by a Householder reflection.
-/

open Set

namespace Erdos186.PZ.ConvexDensity

noncomputable section

/-- The positive rescaling which matches the pivot coordinates of two
directions in the same cap. -/
def capMatchingScale {n m : ℕ} (c : DirectionCapIndex n m)
    (representative y : EuclideanPoint (n + 1)) : ℝ :=
  capLastCoordinate c y / capLastCoordinate c representative

theorem capMatchingScale_pos {n m : ℕ} {c : DirectionCapIndex n m}
    {representative y : EuclideanPoint (n + 1)}
    (hrepresentative : representative ∈ directionCap m c)
    (hy : y ∈ directionCap m c) :
    0 < capMatchingScale c representative y := by
  exact div_pos (capLastCoordinate_pos hy) (capLastCoordinate_pos hrepresentative)

/-- Matching the last chart coordinate makes the pivot coordinate of the
difference vanish. -/
theorem coordinate_sub_capMatchingScale_smul_pivot {n m : ℕ}
    {c : DirectionCapIndex n m}
    {representative y : EuclideanPoint (n + 1)}
    (hrepresentative : representative ∈ directionCap m c) :
    coordinate (y - capMatchingScale c representative y • representative) c.1 = 0 := by
  have hlast : capLastCoordinate c representative ≠ 0 :=
    capLastCoordinate_ne_zero hrepresentative
  rcases c with ⟨i, b, g⟩
  cases b <;>
    simp [capMatchingScale, capLastCoordinate, capSign, coordinate] at hlast ⊢ <;>
    field_simp <;> ring

/-- The other coordinates of the matched difference are, up to the cap sign,
exactly the base residuals defined in `CapToGraph`. -/
theorem abs_coordinate_sub_capMatchingScale_smul_succAbove {n m : ℕ}
    {c : DirectionCapIndex n m}
    {representative y : EuclideanPoint (n + 1)}
    (hrepresentative : representative ∈ directionCap m c) (j : Fin n) :
    |coordinate (y - capMatchingScale c representative y • representative)
        (c.1.succAbove j)| = |capBaseResidual c representative y j| := by
  have hlast : capLastCoordinate c representative ≠ 0 :=
    capLastCoordinate_ne_zero hrepresentative
  rcases c with ⟨i, b, g⟩
  have habs (a d : ℝ) : |a - d| = |-a + d| := by
    rw [show -a + d = d - a by ring, abs_sub_comm]
  cases b
  · simp [capMatchingScale, capLastCoordinate, capBaseResidual, capBaseCoordinate,
      capSlope, capSign, coordinate] at hlast ⊢
    simpa only [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      habs (y.ofLp (i.succAbove j))
        (y.ofLp i / representative.ofLp i * representative.ofLp (i.succAbove j))
  · simp [capMatchingScale, capLastCoordinate, capBaseResidual, capBaseCoordinate,
      capSlope, capSign, coordinate] at hlast ⊢
    field_simp

/-- The matched difference of two unit directions has norm at most
`sqrt(n)/m`. -/
theorem norm_sub_capMatchingScale_smul_le {n m : ℕ} (hm : 0 < m)
    {c : DirectionCapIndex n m}
    {representative y : EuclideanPoint (n + 1)}
    (hrepresentative : representative ∈ directionCap m c)
    (hy : y ∈ directionCap m c) (hyNorm : ‖y‖ = 1) :
    ‖y - capMatchingScale c representative y • representative‖ ≤
      Real.sqrt n / m := by
  let w := y - capMatchingScale c representative y • representative
  have hpivot : coordinate w c.1 = 0 :=
    coordinate_sub_capMatchingScale_smul_pivot hrepresentative
  have hcoord : ∀ j : Fin n, |coordinate w (c.1.succAbove j)| ≤ (m : ℝ)⁻¹ := by
    intro j
    rw [abs_coordinate_sub_capMatchingScale_smul_succAbove hrepresentative j]
    exact abs_capBaseResidual_le_inv hm hrepresentative hy hyNorm j
  have hsq : ‖w‖ ^ 2 ≤ (n : ℝ) * (m : ℝ)⁻¹ ^ 2 := by
    change WithLp.ofLp w c.1 = 0 at hpivot
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succAbove _ c.1, hpivot]
    have hsum :
        (∑ j : Fin n, coordinate w (c.1.succAbove j) ^ 2) ≤
          ∑ _j : Fin n, (m : ℝ)⁻¹ ^ 2 := by
      apply Finset.sum_le_sum
      intro j _hj
      have hj := hcoord j
      nlinarith [sq_abs (coordinate w (c.1.succAbove j)),
        abs_nonneg (coordinate w (c.1.succAbove j)),
        inv_nonneg.mpr (by positivity : (0 : ℝ) ≤ m)]
    calc
      0 ^ 2 + ∑ j : Fin n, coordinate w (c.1.succAbove j) ^ 2 ≤
          0 ^ 2 + ∑ _j : Fin n, (m : ℝ)⁻¹ ^ 2 := by
        simpa using hsum
      _ = (n : ℝ) * (m : ℝ)⁻¹ ^ 2 := by simp
  have hsqrt0 : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hinv0 : 0 ≤ (m : ℝ)⁻¹ := inv_nonneg.mpr (by positivity)
  have hsqrtSq : Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt (by positivity)
  rw [div_eq_mul_inv]
  nlinarith [norm_nonneg w, mul_nonneg hsqrt0 hinv0]

/-- Unit directions in one cap are close in Euclidean norm. -/
theorem norm_sub_normalized_directions_le {n m : ℕ} (hm : 0 < m)
    {c : DirectionCapIndex n m}
    {representative y : EuclideanPoint (n + 1)}
    (hrepresentative : representative ∈ directionCap m c)
    (hy : y ∈ directionCap m c)
    (hrepresentativeNorm : ‖representative‖ = 1) (hyNorm : ‖y‖ = 1) :
    ‖y - representative‖ ≤ 2 * Real.sqrt n / m := by
  let t := capMatchingScale c representative y
  have ht : 0 < t := capMatchingScale_pos hrepresentative hy
  have hw : ‖y - t • representative‖ ≤ Real.sqrt n / m :=
    norm_sub_capMatchingScale_smul_le hm hrepresentative hy hyNorm
  have htOne : |t - 1| ≤ ‖y - t • representative‖ := by
    have h := abs_norm_sub_norm_le y (t • representative)
    rw [hyNorm, norm_smul, hrepresentativeNorm, mul_one, Real.norm_eq_abs,
      abs_of_pos ht] at h
    simpa [abs_sub_comm] using h
  calc
    ‖y - representative‖ =
        ‖(y - t • representative) + (t • representative - representative)‖ := by
      congr 1
      module
    _ ≤ ‖y - t • representative‖ +
        ‖t • representative - representative‖ := norm_add_le _ _
    _ = ‖y - t • representative‖ + |t - 1| := by
      rw [show t • representative - representative = (t - 1) • representative by module,
        norm_smul, hrepresentativeNorm, mul_one, Real.norm_eq_abs]
    _ ≤ 2 * (Real.sqrt n / m) := by linarith
    _ = 2 * Real.sqrt n / m := by ring

/-! ## Transfer through the Householder reflection -/

/-- Orthogonal projection to the first `n` coordinates does not increase
norm. -/
theorem norm_baseCoordinates_le_norm {n : ℕ} (z : EuclideanPoint (n + 1)) :
    ‖baseCoordinates z‖ ≤ ‖z‖ := by
  have hsquare := norm_appendCoordinate_sq (baseCoordinates z) (lastCoordinate z)
  rw [appendCoordinate_baseCoordinates_lastCoordinate] at hsquare
  nlinarith [norm_nonneg (baseCoordinates z), norm_nonneg z,
    sq_nonneg |lastCoordinate z|]

/-- After the representative Householder rotation, the base norm of another
direction in the cap is `O(sqrt(n)/m)`. -/
theorem norm_baseCoordinates_representativeToLast_le {n m : ℕ} (hm : 0 < m)
    {c : DirectionCapIndex n m}
    {representative y : EuclideanPoint (n + 1)}
    (hrepresentative : representative ∈ directionCap m c)
    (hy : y ∈ directionCap m c)
    (hrepresentativeNorm : ‖representative‖ = 1) (hyNorm : ‖y‖ = 1) :
    ‖baseCoordinates (representativeToLast representative y)‖ ≤
      2 * Real.sqrt n / m := by
  let R := representativeToLast representative
  have hRu : R representative = lastBasisVector n :=
    representativeToLast_apply hrepresentativeNorm
  have hbaseLast : baseCoordinates (lastBasisVector n) = 0 := by
    ext j
    simp [lastBasisVector, coordinate]
  have hbaseEq : baseCoordinates (R y) = baseCoordinates (R (y - representative)) := by
    ext j
    rw [map_sub]
    have hzero : coordinate (R representative) j.castSucc = 0 := by
      rw [hRu]
      simp [lastBasisVector, coordinate]
    change coordinate (R y) j.castSucc =
      coordinate (R y) j.castSucc - coordinate (R representative) j.castSucc
    rw [hzero, sub_zero]
  rw [hbaseEq]
  calc
    ‖baseCoordinates (R (y - representative))‖ ≤ ‖R (y - representative)‖ :=
      norm_baseCoordinates_le_norm _
    _ = ‖y - representative‖ := R.norm_map _
    _ ≤ 2 * Real.sqrt n / m :=
      norm_sub_normalized_directions_le hm hrepresentative hy
        hrepresentativeNorm hyNorm

/-- The last coordinate after Householder rotation differs from one by at
most the same angular error. -/
theorem abs_lastCoordinate_representativeToLast_sub_one_le {n m : ℕ} (hm : 0 < m)
    {c : DirectionCapIndex n m}
    {representative y : EuclideanPoint (n + 1)}
    (hrepresentative : representative ∈ directionCap m c)
    (hy : y ∈ directionCap m c)
    (hrepresentativeNorm : ‖representative‖ = 1) (hyNorm : ‖y‖ = 1) :
    |lastCoordinate (representativeToLast representative y) - 1| ≤
      2 * Real.sqrt n / m := by
  let R := representativeToLast representative
  have hRu : R representative = lastBasisVector n :=
    representativeToLast_apply hrepresentativeNorm
  have hlast : lastCoordinate (lastBasisVector n) = 1 := by
    exact coordinate_lastBasisVector_last n
  have hcoord :
      lastCoordinate (R y) - 1 = lastCoordinate (R (y - representative)) := by
    rw [map_sub]
    change lastCoordinate (R y) - 1 =
      lastCoordinate (R y) - lastCoordinate (R representative)
    rw [hRu, hlast]
  rw [hcoord]
  calc
    |lastCoordinate (R (y - representative))| ≤ ‖R (y - representative)‖ :=
      abs_lastCoordinate_le_norm _
    _ = ‖y - representative‖ := R.norm_map _
    _ ≤ 2 * Real.sqrt n / m :=
      norm_sub_normalized_directions_le hm hrepresentative hy
        hrepresentativeNorm hyNorm

/-- If `m ≥ 4 sqrt(n)`, every rotated unit direction in the cap has last
coordinate at least `1/2`. -/
theorem one_half_le_lastCoordinate_representativeToLast {n m : ℕ} (hm : 0 < m)
    (hmLarge : 4 * Real.sqrt n ≤ m)
    {c : DirectionCapIndex n m}
    {representative y : EuclideanPoint (n + 1)}
    (hrepresentative : representative ∈ directionCap m c)
    (hy : y ∈ directionCap m c)
    (hrepresentativeNorm : ‖representative‖ = 1) (hyNorm : ‖y‖ = 1) :
    (1 : ℝ) / 2 ≤ lastCoordinate (representativeToLast representative y) := by
  have herr := abs_lastCoordinate_representativeToLast_sub_one_le hm
    hrepresentative hy hrepresentativeNorm hyNorm
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hsqrt0 := Real.sqrt_nonneg (n : ℝ)
  have hsmall : 2 * Real.sqrt n / m ≤ (1 : ℝ) / 2 := by
    apply (div_le_iff₀ hmR).2
    nlinarith
  have hlower := (neg_le_of_abs_le herr)
  linarith

/-! ## Scaling back to annulus points -/

theorem norm_smul_normalizedDirection {n : ℕ} {x : EuclideanPoint n}
    (hx : x ≠ 0) : ‖x‖ • normalizedDirection x = x := by
  simp [normalizedDirection, norm_ne_zero_iff.mpr hx]

/-- Scaled form used for points in a bounded annulus. -/
theorem householder_annulus_base_last_bounds {n m : ℕ} (hm : 0 < m)
    (hmLarge : 4 * Real.sqrt n ≤ m)
    {inner outer : ℝ} (hinner : 0 < inner)
    {c : DirectionCapIndex n m}
    {representative y : EuclideanPoint (n + 1)}
    (hrepAnnulus : representative ∈ boundedAnnulus inner outer)
    (hyAnnulus : y ∈ boundedAnnulus inner outer)
    (hrepresentative : normalizedDirection representative ∈ directionCap m c)
    (hy : normalizedDirection y ∈ directionCap m c) :
    ‖baseCoordinates
        (representativeToLast (normalizedDirection representative) y)‖ ≤
        outer * (2 * Real.sqrt n / m) ∧
      inner / 2 ≤
        lastCoordinate (representativeToLast (normalizedDirection representative) y) := by
  have hrep0 : representative ≠ 0 :=
    ne_zero_of_mem_boundedAnnulus hinner hrepAnnulus
  have hy0 : y ≠ 0 := ne_zero_of_mem_boundedAnnulus hinner hyAnnulus
  let R := representativeToLast (normalizedDirection representative)
  have hbaseUnit := norm_baseCoordinates_representativeToLast_le hm
    hrepresentative hy (norm_normalizedDirection hrep0) (norm_normalizedDirection hy0)
  have hlastUnit := one_half_le_lastCoordinate_representativeToLast hm hmLarge
    hrepresentative hy (norm_normalizedDirection hrep0) (norm_normalizedDirection hy0)
  have hyReconstruct : ‖y‖ • normalizedDirection y = y :=
    norm_smul_normalizedDirection hy0
  have hRy : R y = ‖y‖ • R (normalizedDirection y) := by
    calc
      R y = R (‖y‖ • normalizedDirection y) := congrArg R hyReconstruct.symm
      _ = ‖y‖ • R (normalizedDirection y) := map_smul R _ _
  constructor
  · rw [hRy, baseCoordinates_smul, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg y)]
    have hnormUpper : ‖y‖ ≤ outer := hyAnnulus.2
    have houter0 : 0 ≤ outer := le_trans (norm_nonneg y) hnormUpper
    exact mul_le_mul hnormUpper hbaseUnit (norm_nonneg _) houter0
  · rw [hRy, lastCoordinate_smul]
    have hnormLower : inner ≤ ‖y‖ := hyAnnulus.1
    have hmul := mul_le_mul hnormLower hlastUnit
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (norm_nonneg y)
    nlinarith

end

end Erdos186.PZ.ConvexDensity
