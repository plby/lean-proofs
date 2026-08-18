/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.ConvexDensity.EnclosingBox

/-! # Elementary metric and volume constants in the normalized model -/

open Set MeasureTheory
open scoped ENNReal BigOperators

namespace Erdos186.PZ.ConvexDensity

set_option autoImplicit false
noncomputable section

/-- Every coordinate is bounded by the Euclidean norm.  This local version
keeps the normalized-geometry base layer independent of the later cap
decomposition. -/
private theorem abs_coordinate_le_norm' {d : ℕ} (x : EuclideanPoint d) (i : Fin d) :
    |coordinate x i| ≤ ‖x‖ := by
  have hi : coordinate x i ^ 2 ≤ ∑ j, coordinate x j ^ 2 := by
    exact Finset.single_le_sum (fun j _ ↦ sq_nonneg (coordinate x j))
      (Finset.mem_univ i)
  rw [← EuclideanSpace.real_norm_sq_eq] at hi
  nlinarith [sq_abs (coordinate x i), abs_nonneg (coordinate x i), norm_nonneg x]

/-- The fixed inner cube is genuinely full-dimensional. -/
theorem normalizedInnerCube_interior_nonempty (d : ℕ) :
    (interior (normalizedInnerCube d)).Nonempty := by
  let a : ℝ := (2 * ((d + 1 : ℕ) : ℝ))⁻¹
  let c : EuclideanPoint d := WithLp.toLp 2 (fun _ ↦ a)
  have ha : 0 < a := by simp only [a]; positivity
  have hball : Metric.ball c a ⊆ normalizedInnerCube d := by
    intro x hx
    rw [Metric.mem_ball, dist_eq_norm] at hx
    intro i
    have hcoord : |coordinate (x - c) i| ≤ ‖x - c‖ :=
      abs_coordinate_le_norm' (x - c) i
    have hci : coordinate c i = a := by simp [c]
    have hxi : coordinate (x - c) i = coordinate x i - a := by
      simp [coordinate, hci]
    rw [hxi] at hcoord
    have habs : |coordinate x i - a| < a := hcoord.trans_lt hx
    have htwice : 2 * a = (((d + 1 : ℕ) : ℝ))⁻¹ := by
      simp only [a]
      field_simp
    constructor
    · linarith [(abs_lt.mp habs).1]
    · rw [← htwice]
      linarith [(abs_lt.mp habs).2]
  refine ⟨c, ?_⟩
  rw [mem_interior_iff_mem_nhds]
  exact Filter.mem_of_superset (Metric.ball_mem_nhds c ha) hball

/-- A finite convex hull containing the normalized inner cube is a convex
body, with no separate affine-span argument at call sites. -/
theorem isConvexBody_convexHull_of_normalizedInnerCube_subset {d : ℕ}
    {X : Finset (EuclideanPoint d)}
    (hinner : normalizedInnerCube d ⊆
      convexHull ℝ (X : Set (EuclideanPoint d))) :
    IsConvexBody (convexHull ℝ (X : Set (EuclideanPoint d))) := by
  refine ⟨convex_convexHull ℝ _, X.finite_toSet.isCompact_convexHull ℝ, ?_⟩
  exact (normalizedInnerCube_interior_nonempty d).mono
    (interior_mono hinner)

/-- The normalized outer cube is contained in the Euclidean ball of radius
`sqrt d`. -/
theorem normalizedOuterCube_subset_closedBall (d : ℕ) :
    normalizedOuterCube d ⊆
      Metric.closedBall (0 : EuclideanPoint d) (Real.sqrt d) := by
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (sq_le_sq₀ (norm_nonneg x) (Real.sqrt_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq]
  calc
    ∑ i, (x i) ^ 2 ≤ ∑ _i : Fin d, (1 : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _hi
      have habs : |x i| ≤ 1 := by
        apply abs_le.mpr
        simpa [normalizedOuterCube, closedAxisBox] using hx i
      rw [← sq_abs]
      exact (sq_le_sq₀ (abs_nonneg _) zero_le_one).mpr habs
    _ = (Real.sqrt (d : ℝ)) ^ 2 := by
      rw [Real.sq_sqrt (Nat.cast_nonneg d)]
      simp

/-- Recentring a set contained in a radius-`R` ball at one of its own points
costs at most a factor two in the enclosing radius. -/
theorem subset_closedBall_center_two_mul {d : ℕ}
    {P : Set (EuclideanPoint d)} {center : EuclideanPoint d} {R : ℝ}
    (hP : P ⊆ Metric.closedBall 0 R) (hcenter : center ∈ P) :
    P ⊆ Metric.closedBall center (2 * R) := by
  intro x hx
  rw [Metric.mem_closedBall]
  have hx0 : dist x 0 ≤ R := by
    simpa [Metric.mem_closedBall] using hP hx
  have hc0 : dist center 0 ≤ R := by
    simpa [Metric.mem_closedBall] using hP hcenter
  calc
    dist x center ≤ dist x 0 + dist 0 center := dist_triangle _ _ _
    _ = dist x 0 + dist center 0 := by rw [dist_comm 0 center]
    _ ≤ 2 * R := by linarith

/-- A frontier point cannot lie strictly inside a ball contained in the set. -/
theorem radius_le_dist_of_closedBall_subset_of_mem_frontier {d : ℕ}
    {P : Set (EuclideanPoint d)} {center x : EuclideanPoint d} {r : ℝ}
    (hball : Metric.closedBall center r ⊆ P) (hx : x ∈ frontier P) :
    r ≤ dist x center := by
  by_contra hnot
  have hdist : dist x center < r := lt_of_not_ge hnot
  let e := r - dist x center
  have he : 0 < e := sub_pos.mpr hdist
  have hsmall : Metric.ball x e ⊆ P := by
    intro z hz
    apply hball
    rw [Metric.mem_closedBall]
    have hz' : dist z x < e := by simpa [Metric.mem_ball] using hz
    calc
      dist z center ≤ dist z x + dist x center := dist_triangle _ _ _
      _ ≤ r := by dsimp only [e] at hz'; linarith
  have hxInterior : x ∈ interior P := by
    rw [mem_interior_iff_mem_nhds]
    exact Filter.mem_of_superset (Metric.ball_mem_nhds x he) hsmall
  exact Set.disjoint_left.1 disjoint_interior_frontier hxInterior hx

/-- Exact real form of the normalized inner-cube volume. -/
theorem volume_normalizedInnerCube_eq_ofReal_pow (d : ℕ) :
    volume (normalizedInnerCube d) =
      ENNReal.ofReal ((((d + 1 : ℕ) : ℝ)⁻¹) ^ d) := by
  rw [volume_normalizedInnerCube]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact (ENNReal.ofReal_pow (by positivity) d).symm

/-- Any measurable ambient set containing the normalized inner cube has the
corresponding explicit absolute volume lower bound. -/
theorem normalizedInnerCube_volume_le {d : ℕ}
    {Omega : Set (EuclideanPoint d)}
    (hinner : normalizedInnerCube d ⊆ Omega) :
    ENNReal.ofReal ((((d + 1 : ℕ) : ℝ)⁻¹) ^ d) ≤ volume Omega := by
  rw [← volume_normalizedInnerCube_eq_ofReal_pow]
  exact measure_mono hinner

/-- A relative-volume threshold yields either the small branch or an
absolute lower bound, provided the ambient body has a known absolute volume
lower bound. -/
theorem relativeVolume_le_or_volume_lower {d : ℕ}
    {P Omega : Set (EuclideanPoint d)} {eta c : ℝ}
    (hOmega : IsConvexBody Omega) (heta : 0 ≤ eta) (hc : 0 ≤ c)
    (hOmegaLower : ENNReal.ofReal c ≤ volume Omega) :
    relativeVolume P Omega ≤ ENNReal.ofReal eta ∨
      ENNReal.ofReal (eta * c) ≤ volume P := by
  by_cases hsmall : relativeVolume P Omega ≤ ENNReal.ofReal eta
  · exact Or.inl hsmall
  · right
    have hlarge : ENNReal.ofReal eta * volume Omega < volume P := by
      have hnot : ¬ volume P ≤ ENNReal.ofReal eta * volume Omega := by
        intro h
        exact hsmall ((relativeVolume_le_iff hOmega eta).2 h)
      exact lt_of_not_ge hnot
    calc
      ENNReal.ofReal (eta * c) =
          ENNReal.ofReal eta * ENNReal.ofReal c := ENNReal.ofReal_mul heta
      _ ≤ ENNReal.ofReal eta * volume Omega := by gcongr
      _ ≤ volume P := hlarge.le

/-- The preceding dichotomy with the explicit normalized inner-cube
constant. -/
theorem relativeVolume_le_or_normalized_volume_lower {d : ℕ}
    {P Omega : Set (EuclideanPoint d)} {eta : ℝ}
    (hOmega : IsConvexBody Omega) (heta : 0 ≤ eta)
    (hinner : normalizedInnerCube d ⊆ Omega) :
    relativeVolume P Omega ≤ ENNReal.ofReal eta ∨
      ENNReal.ofReal
          (eta * (((d + 1 : ℕ) : ℝ)⁻¹) ^ d) ≤ volume P := by
  exact relativeVolume_le_or_volume_lower hOmega heta (by positivity)
    (normalizedInnerCube_volume_le hinner)

end

end Erdos186.PZ.ConvexDensity
