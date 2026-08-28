import Wikipedia.SmoothSixDPoincare.DiskAnnulusHomotopy
import Wikipedia.HopfProblem.SixSphereCubeCollapseTopology
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph

/-!
# The actual disk with its boundary collapsed to infinity

Collapse exactly the unit boundary, and identify the remaining open disk
with the original vector space by the standard radial homeomorphism. The
result is continuous on the full closed disk and has the expected exact
finite fibers. Near zero its finite coordinate is the smooth radial expansion.
-/

noncomputable section

open Set Metric Function Topology ContinuousMap
open scoped OnePoint

namespace Wikipedia.SmoothSixDPoincare.DiskOnePointCollapse

open MorseHandle

variable {N : Type*} [NormedAddCommGroup N]

def boundary : Set (UnitDisk N) := {z | ‖(z : N)‖ = 1}

theorem boundary_closed : IsClosed (boundary (N := N)) :=
  isClosed_eq continuous_subtype_val.norm continuous_const

theorem not_mem_boundary_iff (z : UnitDisk N) : z ∉ boundary ↔ ‖(z : N)‖ < 1 := by
  change ‖(z : N)‖ ≠ 1 ↔ ‖(z : N)‖ < 1
  constructor
  · exact lt_of_le_of_ne (mem_closedBall_zero_iff.mp z.property)
  · exact ne_of_lt

variable [NormedSpace ℝ N]

def interiorHomeomorph : ↥(boundary (N := N))ᶜ ≃ₜ N :=
  (Homeomorph.setCongr (by ext z; exact not_mem_boundary_iff z)).trans
    (DiskAnnulus.openDiskHomeomorph.trans Homeomorph.unitBall.symm)

def collapse : C(UnitDisk N, OnePoint N) :=
  ⟨fun z => interiorHomeomorph.onePointCongr
      (Wikipedia.HopfProblem.SixSphereCube.collapse boundary z),
    interiorHomeomorph.onePointCongr.continuous.comp
      (Wikipedia.HopfProblem.SixSphereCube.continuous_collapse boundary boundary_closed)⟩

theorem collapse_boundary (z : UnitDisk N) (hz : ‖(z : N)‖ = 1) : collapse z = ∞ := by
  change interiorHomeomorph.onePointCongr
    (Wikipedia.HopfProblem.SixSphereCube.collapse boundary z) = ∞
  rw [Wikipedia.HopfProblem.SixSphereCube.collapse_of_mem boundary hz]
  rfl

/-- On the open disk, the finite coordinate is the standard radial expansion. -/
theorem collapse_interior (z : UnitDisk N) (hz : ‖(z : N)‖ < 1) :
    collapse z = ((OpenPartialHomeomorph.univUnitBall.symm (z : N) : N) : OnePoint N) := by
  change interiorHomeomorph.onePointCongr
    (Wikipedia.HopfProblem.SixSphereCube.collapse boundary z) = _
  rw [Wikipedia.HopfProblem.SixSphereCube.collapse_of_not_mem boundary
    ((not_mem_boundary_iff z).mpr hz)]
  rfl

theorem collapse_eq_iff (z w : UnitDisk N) :
    collapse z = collapse w ↔ z = w ∨ ‖(z : N)‖ = 1 ∧ ‖(w : N)‖ = 1 := by
  change interiorHomeomorph.onePointCongr
    (Wikipedia.HopfProblem.SixSphereCube.collapse boundary z) =
    interiorHomeomorph.onePointCongr
      (Wikipedia.HopfProblem.SixSphereCube.collapse boundary w) ↔ _
  rw [interiorHomeomorph.onePointCongr.injective.eq_iff,
    Wikipedia.HopfProblem.SixSphereCube.collapse_eq_iff]
  rfl

def compress (x : N) : UnitDisk N :=
  ⟨Homeomorph.unitBall x, ball_subset_closedBall (Homeomorph.unitBall x).property⟩

theorem norm_compress_lt (x : N) : ‖(compress x : N)‖ < 1 :=
  mem_ball_zero_iff.mp (Homeomorph.unitBall x).property

theorem compress_zero : (compress (0 : N) : N) = 0 := Homeomorph.coe_unitBall_apply_zero

theorem collapse_compress (x : N) : collapse (compress x) = (x : OnePoint N) := by
  rw [collapse_interior _ (norm_compress_lt x)]
  exact congrArg (fun y : N => (y : OnePoint N))
    (OpenPartialHomeomorph.univUnitBall.left_inv (mem_univ x))

theorem collapse_eq_coe_iff (z : UnitDisk N) (x : N) :
    collapse z = (x : OnePoint N) ↔ z = compress x := by
  rw [← collapse_compress x, collapse_eq_iff]
  constructor
  · rintro (h | h)
    · exact h
    · exact ((ne_of_lt (norm_compress_lt x)) h.2).elim
  · exact Or.inl

/-- The finite zero fiber is precisely the original disk center. -/
theorem collapse_eq_zero_iff (z : UnitDisk N) :
    collapse z = ((0 : N) : OnePoint N) ↔ (z : N) = 0 := by
  rw [collapse_eq_coe_iff]
  constructor
  · intro hz
    exact (congrArg Subtype.val hz).trans compress_zero
  · intro hz
    exact Subtype.ext (hz.trans compress_zero.symm)

theorem collapse_eq_infty_iff (z : UnitDisk N) : collapse z = ∞ ↔ ‖(z : N)‖ = 1 := by
  by_cases hz : ‖(z : N)‖ = 1
  · rw [collapse_boundary z hz]
    exact iff_of_true rfl hz
  · rw [collapse_interior z ((not_mem_boundary_iff z).mp hz)]
    exact iff_of_false (OnePoint.coe_ne_infty _) hz

end Wikipedia.SmoothSixDPoincare.DiskOnePointCollapse
