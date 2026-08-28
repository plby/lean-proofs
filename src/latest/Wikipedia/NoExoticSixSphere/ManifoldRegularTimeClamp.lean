import Wikipedia.NoExoticSixSphere.ManifoldParityBallPush
import Mathlib.Topology.Order.ProjIcc

/-!
# Clamping time without introducing an intrinsic singularity

All actual singularities lie strictly between the two endpoint times, as
follows from the constructed ball system. Clamping time to the closed unit
interval is therefore continuous on the actual regular parameter space and
fixes every parameter already in the closed time cylinder.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereFamily

def clampTime : C(ℝ × Sphere 3, ℝ × Sphere 3) where
  toFun y := ((projIcc (0 : ℝ) 1 zero_le_one y.1 : ℝ), y.2)
  continuous_toFun := (continuous_subtype_val.comp
    (continuous_projIcc.comp continuous_fst)).prodMk continuous_snd

theorem clampTime_mem_Icc (y : ℝ × Sphere 3) :
    (clampTime y).1 ∈ Icc (0 : ℝ) 1 := (projIcc 0 1 zero_le_one y.1).property

theorem clampTime_eq_of_mem (y : ℝ × Sphere 3) (hy : y.1 ∈ Icc (0 : ℝ) 1) :
    clampTime y = y := by
  change ((projIcc 0 1 zero_le_one y.1 : ℝ), y.2) = y
  rw [projIcc_of_mem zero_le_one hy]

theorem clampTime_eq_of_interior (y : ℝ × Sphere 3)
    (hy : (clampTime y).1 ∈ Ioo (0 : ℝ) 1) : clampTime y = y := by
  by_cases hl : y.1 ≤ 0
  · have he := projIcc_of_le_left (b := (1 : ℝ)) zero_le_one hl
    simp only [clampTime, ContinuousMap.coe_mk, he, mem_Ioo,
      lt_self_iff_false, false_and] at hy
  · by_cases hr : 1 ≤ y.1
    · have he := projIcc_of_right_le (a := (0 : ℝ)) zero_le_one hr
      simp only [clampTime, ContinuousMap.coe_mk, he, mem_Ioo,
        lt_self_iff_false, and_false] at hy
    · exact clampTime_eq_of_mem y ⟨(lt_of_not_ge hl).le, (lt_of_not_ge hr).le⟩

namespace ParityBallSystem

open GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  {g : ℝ → Sphere 3 → M} (P : ParityBallSystem g)

include P in
theorem singular_time_interior {y : ℝ × Sphere 3}
    (hy : y ∈ singularParameters (n := 6) g) : y.1 ∈ Ioo (0 : ℝ) 1 :=
  (P.closedHoles_subset_interiorTime
    (P.openHoles_subset_closedHoles (P.singular_subset_openHoles hy))).1

def clampRegular : C(RegularParameters g, RegularParameters g) where
  toFun y := ⟨clampTime y.val, fun hs ↦ y.property
    (clampTime_eq_of_interior y.val (P.singular_time_interior hs) ▸ hs)⟩
  continuous_toFun := (clampTime.continuous.comp continuous_subtype_val).subtype_mk _

theorem clampRegular_mem_Icc (y : RegularParameters g) :
    (P.clampRegular y).val.1 ∈ Icc (0 : ℝ) 1 := clampTime_mem_Icc y.val

theorem clampRegular_fixed (y : RegularParameters g) (hy : y.val.1 ∈ Icc (0 : ℝ) 1) :
    P.clampRegular y = y := Subtype.ext (clampTime_eq_of_mem y.val hy)

end ParityBallSystem
end NoExoticSixSphere.SphereFamily
