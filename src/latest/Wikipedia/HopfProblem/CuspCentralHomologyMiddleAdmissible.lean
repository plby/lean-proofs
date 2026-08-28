import Wikipedia.HopfProblem.CuspCentralHomologyMiddleSequence

/-!
# Middle integral homology at an admissible radius

The actual connecting homomorphism identifies degree three with the
degree-one homology of the fibre torus. In degree two, the actual split
extension consists of the three boundary-suspension classes and one
integer connecting coordinate.
-/

noncomputable section

open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace CuspRetraction SingularMayerVietoris PeriodTorusHigherHomology

/-- The three boundary coordinates and the connecting coordinate form
four integral coordinates. -/
def middleIntegerFourEquiv : ((Fin 3 → ℤ) × ℤ) ≃ₗ[ℤ] (Fin 4 → ℤ) :=
  ({ toFun p := ![p.1 0, p.1 1, p.1 2, p.2]
     invFun v := (![v 0, v 1, v 2], v 3)
     left_inv p := by
       apply Prod.ext
       · funext i
         fin_cases i <;> rfl
       · rfl
     right_inv v := by
       funext i
       fin_cases i <;> rfl
     map_add' p q := by
       funext i
       fin_cases i <;> rfl } : ((Fin 3 → ℤ) × ℤ) ≃+ (Fin 4 → ℤ)).toIntLinearEquiv

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε)

/-- The actual outer open subset has the three suspension classes in
degree two. -/
def middleOuterHomologyTwoEquiv (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) :
    SingularHomology (outerRegion C ε hε a) 2 ≃ₗ[ℤ] (Fin 3 → ℤ) :=
  (homotopyEquivHomologyEquiv
    (outerRegionSuspensionHomotopyEquiv C ε hε hε1 hC hR a ha ha1) 2).trans
      threeCircleSuspensionHomologyTwoEquiv

local notation "U" => outerRegion C ε hε (1 / 2)
local notation "V" => innerRegion C ε hε

/-- The two degree-three classes are obtained from the actual
Mayer–Vietoris connecting map into the actual phase-projection kernel. -/
def centralSingularH3Equiv_of_admissible :
    SingularHomology (QuotientCentralFibre C ε) 3 ≃ₗ[ℤ] (Fin 2 → ℤ) := by
  letI := outerRegion_homology_subsingleton C ε hε hε1 hC hR
    (1 / 2) (by norm_num) (by norm_num) 0
  letI := innerRegion_homology_subsingleton C ε hε hε1 hC hR 0
  exact ((coverConnectingKernelEquivOfVanishing U V
    (outerRegion_isOpen C ε hε hε1 hC hR (1 / 2))
    (innerRegion_isOpen C ε hε hε1 hC hR)
    (outerRegion_union_innerRegion C ε hε (1 / 2) (by norm_num)) 2).trans
      (middleLeftKernelEquiv C ε hε hε1 hC hR
        (1 / 2) (by norm_num) (by norm_num) 1)).trans
          (compactFibreTorusHomologyEquiv 1)

/-- The actual degree-two homology consists of the three outer-boundary
classes and one class lifting the integer connecting generator. -/
def centralSingularH2Equiv_of_admissible :
    SingularHomology (QuotientCentralFibre C ε) 2 ≃ₗ[ℤ] (Fin 4 → ℤ) :=
  (((middleSecondHomologySplit C ε hε hε1 hC hR
      (1 / 2) (by norm_num) (by norm_num)).toAddEquiv.trans
    (AddEquiv.prodCongr
      (middleOuterHomologyTwoEquiv C ε hε hε1 hC hR
        (1 / 2) (by norm_num) (by norm_num)).toAddEquiv
      (AddEquiv.refl ℤ))).trans middleIntegerFourEquiv.toAddEquiv).toIntLinearEquiv

end Wikipedia.HopfProblem.CuspCentralHomology
