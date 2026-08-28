import Wikipedia.HopfProblem.CuspCircleNormalTrivializationRealFour
import Wikipedia.HopfProblem.CuspCircleNormalTrivializationOpenRestriction

/-!
# Native real-analytic coordinates on round open normal disks

The ambient real-linear coordinate map restricts to the original open-subtype
atlases on the normal-radius disk and the standard Euclidean ball. Its forward
and inverse formulas are unchanged by this restriction.
-/

noncomputable section

open Set Metric
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspCircleNormalTrivialization.RealFour

/-- The actual round-radius open subset of the original complex-pair fibre. -/
def roundFibreBall (r : ℝ) : TopologicalSpace.Opens Fibre :=
  ⟨{v | radiusSq v < r ^ 2},
    isOpen_lt (contDiff_radiusSq (n := ω)).continuous continuous_const⟩

/-- The standard open Euclidean four-ball, with its inherited native atlas. -/
def standardFibreBall (r : ℝ) : TopologicalSpace.Opens Space :=
  ⟨ball (0 : Space) r, isOpen_ball⟩

@[simp] theorem mem_roundFibreBall (r : ℝ) (v : Fibre) :
    v ∈ roundFibreBall r ↔ radiusSq v < r ^ 2 := Iff.rfl

@[simp] theorem mem_standardFibreBall (r : ℝ) (x : Space) :
    x ∈ standardFibreBall r ↔ x ∈ ball (0 : Space) r := Iff.rfl

theorem coordinateEquiv_mapsTo_ball (r : ℝ) (hr : 0 ≤ r) :
    MapsTo coordinateEquiv (roundFibreBall r) (standardFibreBall r) :=
  fun v hv => (radiusSq_lt_iff_mem_ball r hr v).mp hv

theorem coordinateEquiv_symm_mapsTo_ball (r : ℝ) (hr : 0 ≤ r) :
    MapsTo coordinateEquiv.symm (standardFibreBall r) (roundFibreBall r) := by
  intro x hx
  change x ∈ ball (0 : Space) r at hx
  apply (radiusSq_lt_iff_mem_ball r hr (coordinateEquiv.symm x)).mpr
  simpa only [coordinateEquiv.apply_symm_apply] using hx

/-- The literal round-ball coordinate map is real analytic in both native atlases. -/
def openBallDiffeomorph (r : ℝ) (hr : 0 ≤ r) :
    Diffeomorph 𝓘(ℝ, Fibre) 𝓘(ℝ, Space)
      (roundFibreBall r) (standardFibreBall r) ω where
  toEquiv := (openBallHomeomorph r hr).toEquiv
  contMDiff_toFun :=
    (OpenRestriction.isLocalDiffeomorph_restrictOpens 𝓘(ℝ, Fibre) 𝓘(ℝ, Space)
      diffeomorph.isLocalDiffeomorph (roundFibreBall r) (standardFibreBall r)
      (coordinateEquiv_mapsTo_ball r hr)).contMDiff
  contMDiff_invFun :=
    (OpenRestriction.isLocalDiffeomorph_restrictOpens 𝓘(ℝ, Space) 𝓘(ℝ, Fibre)
      diffeomorph.symm.isLocalDiffeomorph (standardFibreBall r) (roundFibreBall r)
      (coordinateEquiv_symm_mapsTo_ball r hr)).contMDiff

@[simp] theorem openBallDiffeomorph_coe (r : ℝ) (hr : 0 ≤ r)
    (v : roundFibreBall r) :
    (openBallDiffeomorph r hr v : Space) = coordinateEquiv v := rfl

@[simp] theorem openBallDiffeomorph_symm_coe (r : ℝ) (hr : 0 ≤ r)
    (x : standardFibreBall r) :
    ((openBallDiffeomorph r hr).symm x : Fibre) = coordinateEquiv.symm x := rfl

theorem zero_mem_roundFibreBall (r : ℝ) (hr : 0 < r) :
    (0 : Fibre) ∈ roundFibreBall r := by
  change radiusSq (0 : Fibre) < r ^ 2
  rw [radiusSq_zero]
  exact sq_pos_of_pos hr

theorem zero_mem_standardFibreBall (r : ℝ) (hr : 0 < r) :
    (0 : Space) ∈ standardFibreBall r := by
  simpa only [mem_standardFibreBall, mem_ball, dist_self] using hr

@[simp] theorem openBallDiffeomorph_zero (r : ℝ) (hr : 0 < r) :
    openBallDiffeomorph r hr.le ⟨0, zero_mem_roundFibreBall r hr⟩ =
      ⟨0, zero_mem_standardFibreBall r hr⟩ := by
  apply Subtype.ext
  exact coordinateEquiv.map_zero

@[simp] theorem openBallDiffeomorph_symm_zero (r : ℝ) (hr : 0 < r) :
    (openBallDiffeomorph r hr.le).symm ⟨0, zero_mem_standardFibreBall r hr⟩ =
      ⟨0, zero_mem_roundFibreBall r hr⟩ := by
  apply Subtype.ext
  exact coordinateEquiv.symm.map_zero

end Wikipedia.HopfProblem.CuspCircleNormalTrivialization.RealFour
