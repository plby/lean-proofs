import Wikipedia.HopfProblem.ThreefoldHomologyFinitenessCuspRetraction
import Wikipedia.HopfProblem.CuspCentralHomology
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleHomotopy

/-!
# Actual all-degree integral homology of the full fixed-radius cusp cap

The whole original cap, not an assumed sufficiently small replacement,
has the homology of its literal central fibre.  The comparison comes
from the proved homotopy equivalence whose forward map is exactly the
central inclusion.  It transfers the genuine central-fibre calculation
to every full cusp-family cap used in the construction.
-/

noncomputable section

open CategoryTheory Limits

namespace Wikipedia.HopfProblem.ThreefoldHomologyFinitenessCusp

open SpecialPeriods.CuspFamily CuspCentralHomology
open SingularMayerVietoris PeriodTorusHigherHomology

/-- The actual central inclusion induces an equivalence in every degree. -/
def fullCentralHomologyEquiv (D : Data) (n : ℕ) :
    SingularHomology (CuspRetraction.QuotientCentralFibre D.correction D.radius) n ≃ₗ[ℤ]
      SingularHomology (FullSpace D) n :=
  homotopyEquivHomologyEquiv (fullCentralHomotopyEquiv D) n

@[simp] theorem fullCentralHomologyEquiv_toLinearMap (D : Data) (n : ℕ) :
    (fullCentralHomologyEquiv D n).toLinearMap =
      singularHomologyMap (fullCentralInclusion D) n := by
  change singularHomologyMap (fullCentralHomotopyEquiv D).toFun n = _
  rw [fullCentralHomotopyEquiv_toFun]

/-- Finite free coordinates for the actual full cap in every integral degree. -/
def fullHomologyCoordinates (D : Data) (n : ℕ) :
    SingularHomology (FullSpace D) n ≃ₗ[ℤ] (Fin (centralBetti n) → ℤ) :=
  (fullCentralHomologyEquiv D n).symm.trans
    (centralSingularHomologyEquiv D.correction D.radius D.radius_pos D.holomorphic n)

/-- These coordinates preserve the actual central inclusion, not just an
abstract isomorphism type of the two homology groups. -/
theorem fullHomologyCoordinates_centralInclusion (D : Data) (n : ℕ)
    (a : SingularHomology (CuspRetraction.QuotientCentralFibre D.correction D.radius) n) :
    fullHomologyCoordinates D n (singularHomologyMap (fullCentralInclusion D) n a) =
      centralSingularHomologyEquiv D.correction D.radius D.radius_pos D.holomorphic n a := by
  rw [← fullCentralHomologyEquiv_toLinearMap]
  change centralSingularHomologyEquiv D.correction D.radius D.radius_pos D.holomorphic n
    ((fullCentralHomologyEquiv D n).symm (fullCentralHomologyEquiv D n a)) = _
  rw [LinearEquiv.symm_apply_apply]

theorem fullHomology_free (D : Data) (n : ℕ) :
    Module.Free ℤ (SingularHomology (FullSpace D) n) :=
  Module.Free.of_equiv (fullHomologyCoordinates D n).symm

theorem fullHomology_finite (D : Data) (n : ℕ) :
    Module.Finite ℤ (SingularHomology (FullSpace D) n) :=
  Module.Finite.of_surjective (fullHomologyCoordinates D n).symm.toLinearMap
    (fullHomologyCoordinates D n).symm.surjective

theorem fullHomology_finrank (D : Data) (n : ℕ) :
    Module.finrank ℤ (SingularHomology (FullSpace D) n) = centralBetti n := by
  rw [(fullHomologyCoordinates D n).finrank_eq]
  exact Module.finrank_fin_fun ℤ

theorem fullHomology_subsingleton_of_four_lt (D : Data) {n : ℕ} (hn : 4 < n) :
    Subsingleton (SingularHomology (FullSpace D) n) := by
  have := centralSingularHomology_subsingleton_of_four_lt
    D.correction D.radius D.radius_pos D.holomorphic hn
  refine ⟨fun a b => (fullCentralHomologyEquiv D n).symm.injective ?_⟩
  exact Subsingleton.elim _ _

theorem fullHomology_isZero_of_four_lt (D : Data) {n : ℕ} (hn : 4 < n) :
    IsZero (SingularHomology (FullSpace D) n) := by
  have := fullHomology_subsingleton_of_four_lt D hn
  exact ModuleCat.isZero_of_subsingleton _

theorem fullHomology_finranks (D : Data) :
    (fun n : Fin 5 => Module.finrank ℤ (SingularHomology (FullSpace D) n)) =
      ![1, 2, 4, 2, 1] := by
  funext n
  rw [fullHomology_finrank]
  fin_cases n <;> rfl

end Wikipedia.HopfProblem.ThreefoldHomologyFinitenessCusp
