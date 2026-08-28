import Wikipedia.HopfProblem.CuspCentralHomologyBaseCoverProduct
import Wikipedia.HopfProblem.CuspCentralHomologyBaseCoverAttaching
import Wikipedia.HopfProblem.CuspCentralHomologySpecializationProductAttachment

/-!
# Actual connecting lifts for the phase-product source cover

The circle-to-theta attaching map has proved zero first homology. Its
product with the unchanged compact phases therefore kills precisely the
classes needed for the source Mayer–Vietoris connecting lifts. Both
components of the actual difference map vanish on the phase-projection
kernel, and exactness supplies genuine source homology classes.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology.BaseCover

open ToricSpace SingularMayerVietoris PeriodTorusHigherHomology

variable (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1)

local notation "U" => phaseOuterRegion a
local notation "V" => phaseInnerRegion
local notation "A" => phaseOverlapRegion a

def phaseOverlapHomologyEquiv (n : ℕ) :
    SingularHomology A n ≃ₗ[ℤ] SingularHomology (CompactFibreTorus × Circle) n :=
  homotopyEquivHomologyEquiv (phaseOverlapCircleHomotopyEquiv a ha ha1) n

def phaseOuterHomologyEquiv (n : ℕ) :
    SingularHomology U n ≃ₗ[ℤ] SingularHomology (CompactFibreTorus × Theta) n :=
  homotopyEquivHomologyEquiv (phaseOuterThetaHomotopyEquiv a ha ha1) n

def phaseInnerHomologyEquiv (n : ℕ) :
    SingularHomology V n ≃ₗ[ℤ] SingularHomology CompactFibreTorus n :=
  homotopyEquivHomologyEquiv phaseInnerHomotopyEquiv n

theorem phaseInnerProjection_natural (n : ℕ) (z : SingularHomology A n) :
    phaseInnerHomologyEquiv n (singularHomologyMap (phaseOverlapIntoInner a) n z) =
      singularHomologyMap
        (ContinuousMap.fst : C(CompactFibreTorus × Circle, CompactFibreTorus)) n
        (phaseOverlapHomologyEquiv a ha ha1 n z) := by
  have hm := congrArg
    (fun f : C(A, CompactFibreTorus) => singularHomologyMap f n)
    (phaseOverlapIntoInner_phase_map a ha ha1)
  simpa only [singularHomologyMap_comp, LinearMap.comp_apply,
    phaseInnerHomologyEquiv, phaseOverlapHomologyEquiv,
    homotopyEquivHomologyEquiv_apply] using LinearMap.congr_fun hm z

theorem phaseOuterParameter_natural (n : ℕ) (z : SingularHomology A n) :
    phaseOuterHomologyEquiv a ha ha1 n
        (singularHomologyMap (phaseOverlapIntoOuter a) n z) =
      singularHomologyMap ((ContinuousMap.id CompactFibreTorus).prodMap circleThetaMap) n
        (phaseOverlapHomologyEquiv a ha ha1 n z) := by
  have hm := congrArg
    (fun f : C(A, CompactFibreTorus × Theta) => singularHomologyMap f n)
    (phaseOverlapIntoOuter_theta_map a ha ha1)
  simpa only [singularHomologyMap_comp, LinearMap.comp_apply,
    phaseOuterHomologyEquiv, phaseOverlapHomologyEquiv,
    homotopyEquivHomologyEquiv_apply] using LinearMap.congr_fun hm z

/-- The actual outer inclusion kills every class whose unchanged-phase
projection vanishes, by the proved product-attachment factorization. -/
theorem phaseOverlapIntoOuter_homology_eq_zero_of_projection
    (n : ℕ) (z : SingularHomology A (n + 1))
    (hz : singularHomologyMap
      (ContinuousMap.fst : C(CompactFibreTorus × Circle, CompactFibreTorus)) (n + 1)
      (phaseOverlapHomologyEquiv a ha ha1 (n + 1) z) = 0) :
    singularHomologyMap (phaseOverlapIntoOuter a) (n + 1) z = 0 := by
  apply (phaseOuterHomologyEquiv a ha ha1 (n + 1)).injective
  rw [map_zero, phaseOuterParameter_natural]
  exact productParameter_homology_eq_zero_of_projection circleThetaMap
    circleThetaMap_homology_one_eq_zero n _ hz

/-- The actual source difference map has exactly the phase-projection
kernel in every positive degree. -/
theorem phaseLeftHomologyMap_eq_zero_iff_projection
    (n : ℕ) (z : SingularHomology A (n + 1)) :
    leftHomologyMap U V (n + 1) z = 0 ↔
      singularHomologyMap
        (ContinuousMap.fst : C(CompactFibreTorus × Circle, CompactFibreTorus)) (n + 1)
        (phaseOverlapHomologyEquiv a ha ha1 (n + 1) z) = 0 := by
  have hleft : leftHomologyMap U V (n + 1) z =
      (singularHomologyMap (phaseOverlapIntoOuter a) (n + 1) z,
        -singularHomologyMap (phaseOverlapIntoInner a) (n + 1) z) :=
    leftHomologyMap_apply U V (n + 1) z
  constructor
  · intro hz
    have hi : singularHomologyMap (phaseOverlapIntoInner a) (n + 1) z = 0 := by
      apply neg_eq_zero.mp
      exact congrArg Prod.snd (hleft.symm.trans hz)
    rw [← phaseInnerProjection_natural a ha ha1 (n + 1) z, hi, map_zero]
  · intro hz
    have hi : singularHomologyMap (phaseOverlapIntoInner a) (n + 1) z = 0 := by
      apply (phaseInnerHomologyEquiv (n + 1)).injective
      rw [map_zero, phaseInnerProjection_natural a ha ha1 (n + 1) z]
      exact hz
    have ho := phaseOverlapIntoOuter_homology_eq_zero_of_projection a ha ha1 n z hz
    exact hleft.trans (by rw [ho, hi, neg_zero]; rfl)

/-- Every class in the actual phase-projection kernel is the connecting
image of a genuine homology class of the original phase-product source. -/
theorem phaseConnecting_lift (n : ℕ)
    (x : SingularHomology (CompactFibreTorus × Circle) (n + 1))
    (hx : singularHomologyMap
      (ContinuousMap.fst : C(CompactFibreTorus × Circle, CompactFibreTorus)) (n + 1) x = 0) :
    ∃ y : SingularHomology PhaseBase (n + 2),
      phaseOverlapHomologyEquiv a ha ha1 (n + 1)
        (connectingHomomorphism U V (phaseOuterRegion_isOpen a) phaseInnerRegion_isOpen
          (phaseOuterRegion_union_phaseInnerRegion a ha1) (n + 1) y) = x := by
  let e := phaseOverlapHomologyEquiv a ha ha1 (n + 1)
  have hz : e.symm x ∈ LinearMap.ker (leftHomologyMap U V (n + 1)) := by
    apply (phaseLeftHomologyMap_eq_zero_iff_projection a ha ha1 n (e.symm x)).mpr
    change singularHomologyMap
      (ContinuousMap.fst : C(CompactFibreTorus × Circle, CompactFibreTorus)) (n + 1)
      (e (e.symm x)) = 0
    rw [e.apply_symm_apply]
    exact hx
  have hmem := (exact_at_intersection U V (phaseOuterRegion_isOpen a)
    phaseInnerRegion_isOpen (phaseOuterRegion_union_phaseInnerRegion a ha1) (n + 1)).symm.le hz
  obtain ⟨y, hy⟩ := hmem
  exact ⟨y, (congrArg e hy).trans (e.apply_symm_apply x)⟩

/-- The half-radius cover used in the central specialization calculation. -/
theorem phaseHalfConnecting_lift (n : ℕ)
    (x : SingularHomology (CompactFibreTorus × Circle) (n + 1))
    (hx : singularHomologyMap
      (ContinuousMap.fst : C(CompactFibreTorus × Circle, CompactFibreTorus)) (n + 1) x = 0) :
    ∃ y : SingularHomology PhaseBase (n + 2),
      phaseOverlapHomologyEquiv (1 / 2) (by norm_num) (by norm_num) (n + 1)
        (connectingHomomorphism (phaseOuterRegion (1 / 2)) phaseInnerRegion
          (phaseOuterRegion_isOpen (1 / 2)) phaseInnerRegion_isOpen
          (phaseOuterRegion_union_phaseInnerRegion (1 / 2) (by norm_num)) (n + 1) y) = x :=
  phaseConnecting_lift (1 / 2) (by norm_num) (by norm_num) n x hx

end Wikipedia.HopfProblem.CuspCentralHomology.BaseCover
