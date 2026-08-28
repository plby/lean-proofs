import Wikipedia.HopfProblem.CuspCentralHomologyAttaching
import Wikipedia.HopfProblem.CuspCentralHomologyAttachingCrossProjection
import Wikipedia.HopfProblem.CuspCentralHomologyOpenCoverCompatibility
import Wikipedia.HopfProblem.CuspCentralHomologyTopDegreesRegions

/-!
# The actual Mayer–Vietoris maps in the middle degrees

The proved vanishing of the actual boundary attaching map makes the
outer component zero. The inner component is the actual phase
projection, by the explicit open-cover coordinate compatibility.
Consequently its kernel is the preceding homology group of the fibre
phase torus, using the actual circle-product splitting.
-/

noncomputable section

open Set Topology
open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace CuspRetraction SingularMayerVietoris PeriodTorusHigherHomology

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε)

def middleInnerHomologyEquiv (n : ℕ) :
    SingularHomology (innerRegion C ε hε) n ≃ₗ[ℤ] SingularHomology CompactFibreTorus n :=
  homotopyEquivHomologyEquiv (innerRegionHomotopyEquiv C ε hε hε1 hC hR) n

variable (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1)

local notation "U" => outerRegion C ε hε a
local notation "V" => innerRegion C ε hε
local notation "I" => overlapRegion C ε hε a

def middleOverlapHomologyEquiv (n : ℕ) :
    SingularHomology I n ≃ₗ[ℤ] SingularHomology (CompactFibreTorus × Circle) n :=
  homotopyEquivHomologyEquiv (overlapCircleHomotopyEquiv C ε hε hε1 hC hR a ha ha1) n

include hε1 hC hR ha ha1

/-- This is the actual inclusion into the outer open subset, not a
postulated zero component in a model exact sequence. -/
theorem overlapIntoOuter_homology_eq_zero (n : ℕ) :
    singularHomologyMap (overlapIntoOuter C ε hε a) (n + 1) = 0 := by
  have hm := congrArg
    (fun f : C(I, centralBoundary C ε hε) => singularHomologyMap f (n + 1))
    (overlapIntoOuter_boundary_map C ε hε hε1 hC hR a ha ha1)
  rw [singularHomologyMap_comp, singularHomologyMap_comp,
    circleBoundaryCellMap_homology_eq_zero C ε hε hε1 hC hR n] at hm
  apply LinearMap.ext
  intro z
  apply (homotopyEquivHomologyEquiv
    (outerRegionBoundaryHomotopyEquiv C ε hε a ha ha1 hε1 hC hR) (n + 1)).injective
  simpa only [homotopyEquivHomologyEquiv_apply, LinearMap.comp_apply,
    LinearMap.zero_apply, map_zero] using LinearMap.congr_fun hm z

theorem middleInnerProjection_natural (n : ℕ) :
    (middleInnerHomologyEquiv C ε hε hε1 hC hR n).toLinearMap.comp
        (singularHomologyMap (overlapIntoInner C ε hε a) n) =
      (singularHomologyMap
        (ContinuousMap.fst : C(CompactFibreTorus × Circle, CompactFibreTorus)) n).comp
        (middleOverlapHomologyEquiv C ε hε hε1 hC hR a ha ha1 n).toLinearMap := by
  have hm := congrArg
    (fun f : C(I, CompactFibreTorus) => singularHomologyMap f n)
    (overlapIntoInner_phase_map C ε hε hε1 hC hR a ha ha1)
  simpa only [singularHomologyMap_comp, middleInnerHomologyEquiv,
    middleOverlapHomologyEquiv, homotopyEquivHomologyEquiv_toLinearMap] using hm

theorem middleInnerProjection_zero_iff (n : ℕ) (z : SingularHomology I n) :
    singularHomologyMap (overlapIntoInner C ε hε a) n z = 0 ↔
      singularHomologyMap
        (ContinuousMap.fst : C(CompactFibreTorus × Circle, CompactFibreTorus)) n
          (middleOverlapHomologyEquiv C ε hε hε1 hC hR a ha ha1 n z) = 0 := by
  have hm := LinearMap.congr_fun (middleInnerProjection_natural C ε hε hε1 hC hR a ha ha1 n) z
  change middleInnerHomologyEquiv C ε hε hε1 hC hR n
    (singularHomologyMap (overlapIntoInner C ε hε a) n z) = _ at hm
  constructor
  · intro hz
    rw [hz, map_zero] at hm
    exact hm.symm
  · intro hz
    apply (middleInnerHomologyEquiv C ε hε hε1 hC hR n).injective
    simpa only [map_zero] using hm.trans hz

theorem overlapIntoInner_homology_surjective (n : ℕ) :
    Function.Surjective (singularHomologyMap (overlapIntoInner C ε hε a) (n + 1)) := by
  intro z
  obtain ⟨w, hw⟩ := rightCircleProjection_surjective CompactFibreTorus n
    (middleInnerHomologyEquiv C ε hε hε1 hC hR (n + 1) z)
  refine ⟨(middleOverlapHomologyEquiv C ε hε hε1 hC hR a ha ha1 (n + 1)).symm w, ?_⟩
  apply (middleInnerHomologyEquiv C ε hε hε1 hC hR (n + 1)).injective
  have hm := LinearMap.congr_fun
    (middleInnerProjection_natural C ε hε hε1 hC hR a ha ha1 (n + 1))
    ((middleOverlapHomologyEquiv C ε hε hε1 hC hR a ha ha1 (n + 1)).symm w)
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, hw] using hm

/-- The actual difference map has exactly the proved zero/projection form. -/
theorem middleLeftHomologyMap_apply (n : ℕ) (z : SingularHomology I (n + 1)) :
    leftHomologyMap U V (n + 1) z =
      (0, -singularHomologyMap (overlapIntoInner C ε hε a) (n + 1) z) := by
  calc
    leftHomologyMap U V (n + 1) z =
        (singularHomologyMap (overlapIntoOuter C ε hε a) (n + 1) z,
          -singularHomologyMap (overlapIntoInner C ε hε a) (n + 1) z) :=
      leftHomologyMap_apply U V (n + 1) z
    _ = _ := by
      rw [overlapIntoOuter_homology_eq_zero C ε hε hε1 hC hR a ha ha1 n,
        LinearMap.zero_apply]

theorem middleLeftHomology_mem_ker_iff (n : ℕ) (z : SingularHomology I (n + 1)) :
    z ∈ LinearMap.ker (leftHomologyMap U V (n + 1)) ↔
      singularHomologyMap
        (ContinuousMap.fst : C(CompactFibreTorus × Circle, CompactFibreTorus)) (n + 1)
          (middleOverlapHomologyEquiv C ε hε hε1 hC hR a ha ha1 (n + 1) z) = 0 := by
  change leftHomologyMap U V (n + 1) z = 0 ↔ _
  rw [middleLeftHomologyMap_apply C ε hε hε1 hC hR a ha ha1 n z]
  constructor
  · intro hz
    have hi : -singularHomologyMap (overlapIntoInner C ε hε a) (n + 1) z = 0 :=
      congrArg Prod.snd hz
    exact (middleInnerProjection_zero_iff C ε hε hε1 hC hR a ha ha1 (n + 1) z).mp
      (neg_eq_zero.mp hi)
  · intro hz
    rw [(middleInnerProjection_zero_iff C ε hε hε1 hC hR a ha ha1 (n + 1) z).mpr hz,
      neg_zero]
    rfl

/-- The kernel identification is induced by the actual overlap homotopy
equivalence; it does not replace the Mayer–Vietoris map by an assumed matrix. -/
def middleLeftKernelToProjectionEquiv (n : ℕ) :
    LinearMap.ker (leftHomologyMap U V (n + 1)) ≃ₗ[ℤ]
      LinearMap.ker (singularHomologyMap
        (ContinuousMap.fst : C(CompactFibreTorus × Circle, CompactFibreTorus)) (n + 1)) :=
  ({ toFun z := ⟨middleOverlapHomologyEquiv C ε hε hε1 hC hR a ha ha1 (n + 1) z.1,
       (middleLeftHomology_mem_ker_iff C ε hε hε1 hC hR a ha ha1 n z.1).mp z.2⟩
     invFun z := ⟨(middleOverlapHomologyEquiv C ε hε hε1 hC hR a ha ha1 (n + 1)).symm z.1,
       (middleLeftHomology_mem_ker_iff C ε hε hε1 hC hR a ha ha1 n _).mpr (by
         rw [LinearEquiv.apply_symm_apply]
         exact z.2)⟩
     left_inv z := Subtype.ext (LinearEquiv.symm_apply_apply _ z.1)
     right_inv z := Subtype.ext (LinearEquiv.apply_symm_apply _ z.1)
     map_add' z w := by
       apply Subtype.ext
       exact map_add (middleOverlapHomologyEquiv C ε hε hε1 hC hR a ha ha1 (n + 1)) z.1 w.1 } :
    LinearMap.ker (leftHomologyMap U V (n + 1)) ≃+
      LinearMap.ker (singularHomologyMap
        (ContinuousMap.fst : C(CompactFibreTorus × Circle, CompactFibreTorus))
          (n + 1))).toIntLinearEquiv

def middleLeftKernelEquiv (n : ℕ) :
    LinearMap.ker (leftHomologyMap U V (n + 1)) ≃ₗ[ℤ] SingularHomology CompactFibreTorus n :=
  ((middleLeftKernelToProjectionEquiv C ε hε hε1 hC hR a ha ha1 n).toAddEquiv.trans
    (rightCircleProjectionKernelEquiv CompactFibreTorus n).toAddEquiv).toIntLinearEquiv

end Wikipedia.HopfProblem.CuspCentralHomology
