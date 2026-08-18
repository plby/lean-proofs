/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.Algebra.Order.ToIntervalMod
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Topology.Instances.AddCircle.Real
import ErdosProblems.Erdos984.HunterAnnulus

/-!
# Canonical centered lifts for the unit torus

Hunter's geometric argument repeatedly chooses the representative of a
circle point in `[-1/2,1/2)`.  The definitions and lemmas here make that
choice canonical and record that projecting the lift returns the original
torus point.
-/

open scoped BigOperators

namespace Erdos984

noncomputable section

/-- The standard interval equivalence underlying the centered lift. -/
def centeredCircleEquiv :
    UnitAddCircle ≃ Set.Ico (-(1 : ℝ) / 2) (-(1 : ℝ) / 2 + 1) :=
  QuotientAddGroup.equivIcoMod (p := (1 : ℝ)) (by norm_num)
    (-(1 : ℝ) / 2)

/-- The unique representative of a point of `ℝ / ℤ` in `[-1/2,1/2)`. -/
def centeredCircleLift (x : UnitAddCircle) : ℝ :=
  (centeredCircleEquiv x).1

lemma centeredCircleLift_mem_Ico (x : UnitAddCircle) :
    centeredCircleLift x ∈ Set.Ico (-(1 : ℝ) / 2) (1 / 2) := by
  have h := (centeredCircleEquiv x).2
  change -(1 : ℝ) / 2 ≤ centeredCircleLift x ∧
    centeredCircleLift x < -(1 : ℝ) / 2 + 1 at h
  norm_num at h ⊢
  exact h

lemma centeredCircleLift_lower (x : UnitAddCircle) :
    -(1 : ℝ) / 2 ≤ centeredCircleLift x :=
  (centeredCircleLift_mem_Ico x).1

lemma centeredCircleLift_upper (x : UnitAddCircle) :
    centeredCircleLift x < (1 : ℝ) / 2 :=
  (centeredCircleLift_mem_Ico x).2

lemma centeredCircleLift_abs_le (x : UnitAddCircle) :
    |centeredCircleLift x| ≤ (1 : ℝ) / 2 := by
  rw [abs_le]
  constructor
  · linarith [centeredCircleLift_lower x]
  · exact (centeredCircleLift_upper x).le

/-- The centered representative is genuinely a lift through the quotient. -/
@[simp] lemma coe_centeredCircleLift (x : UnitAddCircle) :
    ((centeredCircleLift x : ℝ) : UnitAddCircle) = x := by
  change ((centeredCircleEquiv x).1 : UnitAddCircle) = x
  rw [← QuotientAddGroup.equivIcoMod_symm_apply]
  exact centeredCircleEquiv.symm_apply_apply x

/-- The quotient norm is the absolute value of the centered lift. -/
lemma norm_eq_abs_centeredCircleLift (x : UnitAddCircle) :
    ‖x‖ = |centeredCircleLift x| := by
  calc
    ‖x‖ = ‖(centeredCircleLift x : UnitAddCircle)‖ := by
      rw [coe_centeredCircleLift]
    _ = |centeredCircleLift x| :=
      (AddCircle.norm_coe_eq_abs_iff
        (x := centeredCircleLift x) (1 : ℝ) (by norm_num)).2 (by
          simpa using centeredCircleLift_abs_le x)

/-- The centered lift minimizes absolute value among all real lifts. -/
lemma centeredCircleLift_abs_le_of_coe_eq {x : UnitAddCircle} {z : ℝ}
    (hz : (z : UnitAddCircle) = x) :
    |centeredCircleLift x| ≤ |z| := by
  calc
    |centeredCircleLift x| = ‖x‖ := (norm_eq_abs_centeredCircleLift x).symm
    _ = ‖(z : UnitAddCircle)‖ := by rw [hz]
    _ ≤ ‖z‖ := QuotientAddGroup.norm_mk_le_norm
    _ = |z| := Real.norm_eq_abs z

/-- A real number of absolute value strictly below one cannot be a
nonzero period of the unit circle. -/
lemma eq_zero_of_coe_eq_zero_of_abs_lt_one {z : ℝ}
    (hz : (z : UnitAddCircle) = 0) (hsmall : |z| < 1) : z = 0 := by
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).1 hz
  have hn' : (n : ℝ) = z := by simpa using hn
  have hnabs : |(n : ℝ)| < 1 := by simpa only [hn'] using hsmall
  have hnlow : (-1 : ℤ) < n := by
    exact_mod_cast (abs_lt.mp hnabs).1
  have hnup : n < (1 : ℤ) := by
    exact_mod_cast (abs_lt.mp hnabs).2
  have : n = 0 := by omega
  simpa [this] using hn'.symm

/-- Coordinatewise centered lift of a finite-dimensional unit torus. -/
def centeredTorusLift {D : Type*} (x : UnitAddTorus D) :
    EuclideanSpace ℝ D :=
  WithLp.toLp 2 fun i ↦ centeredCircleLift (x i)

@[simp] lemma centeredTorusLift_apply {D : Type*} (x : UnitAddTorus D) (i : D) :
    centeredTorusLift x i = centeredCircleLift (x i) := rfl

/-- The coordinatewise quotient map from Euclidean space to the torus. -/
def euclideanToTorus {D : Type*} :
    EuclideanSpace ℝ D →+ UnitAddTorus D where
  toFun u i := (u i : UnitAddCircle)
  map_zero' := by
    ext i
    simp
  map_add' u v := by
    ext i
    simp

@[simp] lemma euclideanToTorus_apply {D : Type*}
    (u : EuclideanSpace ℝ D) (i : D) :
    euclideanToTorus u i = (u i : UnitAddCircle) := rfl

/-- Projecting the canonical lift is the identity on the torus. -/
@[simp] lemma euclideanToTorus_centeredTorusLift {D : Type*}
    (x : UnitAddTorus D) :
    euclideanToTorus (centeredTorusLift x) = x := by
  ext i
  exact coe_centeredCircleLift (x i)

lemma centeredTorusLift_coordinate_abs_le {D : Type*}
    (x : UnitAddTorus D) (i : D) :
    |centeredTorusLift x i| ≤ (1 : ℝ) / 2 := by
  exact centeredCircleLift_abs_le (x i)

lemma centeredTorusLift_coordinate_minimal {D : Type*}
    {x : UnitAddTorus D} {u : EuclideanSpace ℝ D}
    (hu : euclideanToTorus u = x) (i : D) :
    |centeredTorusLift x i| ≤ |u i| := by
  apply centeredCircleLift_abs_le_of_coe_eq
  exact congrFun hu i

/-- Coordinatewise no-wrap criterion for the Euclidean-to-torus quotient. -/
lemma eq_zero_of_euclideanToTorus_eq_zero_of_coordinate_abs_lt_one
    {D : Type*} {u : EuclideanSpace ℝ D}
    (hu : euclideanToTorus u = 0) (hsmall : ∀ i, |u i| < 1) :
    u = 0 := by
  ext i
  apply eq_zero_of_coe_eq_zero_of_abs_lt_one
  · exact congrFun hu i
  · exact hsmall i

/-- A crude Euclidean norm bound for the canonical lift. -/
lemma centeredTorusLift_squaredNorm_le {D : Type*} [Fintype D]
    (x : UnitAddTorus D) :
    squaredNorm (centeredTorusLift x) ≤ (Fintype.card D : ℝ) / 4 := by
  rw [squaredNorm, EuclideanSpace.real_norm_sq_eq]
  calc
    ∑ i : D, (centeredTorusLift x i) ^ 2 ≤
        ∑ _i : D, ((1 : ℝ) / 2) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _hi
      have habs := centeredTorusLift_coordinate_abs_le x i
      have hsq : |centeredTorusLift x i| ^ 2 ≤ ((1 : ℝ) / 2) ^ 2 :=
        (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 habs
      simpa only [sq_abs] using hsq
    _ = (Fintype.card D : ℝ) / 4 := by
      simp
      ring

/-- The centered torus lift minimizes the sum of coordinate squares among
all Euclidean lifts. -/
lemma centeredTorusLift_squaredNorm_le_of_map_eq
    {D : Type*} [Fintype D] {x : UnitAddTorus D}
    {u : EuclideanSpace ℝ D} (hu : euclideanToTorus u = x) :
    squaredNorm (centeredTorusLift x) ≤ squaredNorm u := by
  rw [squaredNorm, squaredNorm, EuclideanSpace.real_norm_sq_eq,
    EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_le_sum
  intro i _hi
  have hmin := centeredTorusLift_coordinate_minimal hu i
  have hsq : |centeredTorusLift x i| ^ 2 ≤ |u i| ^ 2 :=
    (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).2 hmin
  simpa only [sq_abs] using hsq

/-- The Euclidean norm of the centered lift dominates the product (sup)
norm on the torus. -/
lemma torus_norm_le_centeredTorusLift_norm
    {D : Type*} [Fintype D] [Nonempty D] (x : UnitAddTorus D) :
    ‖x‖ ≤ ‖centeredTorusLift x‖ := by
  rw [pi_norm_le_iff_of_nonempty]
  intro i
  rw [norm_eq_abs_centeredCircleLift]
  simpa only [centeredTorusLift_apply, Real.norm_eq_abs] using
    PiLp.norm_apply_le (centeredTorusLift x) i

lemma sq_lt_squaredNorm_centeredTorusLift_of_lt_norm
    {D : Type*} [Fintype D] [Nonempty D] {x : UnitAddTorus D} {τ : ℝ}
    (hτ : 0 ≤ τ) (hx : τ < ‖x‖) :
    τ ^ 2 < squaredNorm (centeredTorusLift x) := by
  rw [squaredNorm]
  exact (sq_lt_sq₀ hτ (norm_nonneg _)).2
    (hx.trans_le (torus_norm_le_centeredTorusLift_norm x))

end

end Erdos984
