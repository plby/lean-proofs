import Wikipedia.HopfProblem.ThreefoldHomologyCuspKernelCoinvariantsConjugacy
import Wikipedia.HopfProblem.ThreefoldHomologyBoundaryFirstMonodromy
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyTopDegree
import Wikipedia.HopfProblem.CuspCentralHomology

/-!
# Finite free native cusp Wang cokernels in every degree

The actual second and third quotients are transported by the original
flat-to-circle homology equivalence.  The first quotient retains its
proved native period-loop marking.  The zeroth and fourth Wang operators
vanish on actual homology, and higher source homology vanishes.  Thus the
literal native cokernels have ranks `1, 2, 4, 2, 1`, extended by zero,
without any assumption about a specialization or a fibre-to-cap kernel.
-/

noncomputable section

namespace Wikipedia.HopfProblem.ThreefoldHomologyCuspFibre

open SpecialPeriods SpecialPeriods.Threefold SingularMayerVietoris
open SpecialPeriods.Threefold.Homology
open PeriodTorusHigherHomology MappingTorusHomology CuspCentralHomology
open CuspCentralHomology.SpecializationCoinvariants

local notation "f₀" => ThreefoldOverlapMappingTorus.monodromy none

/-- The original cusp fixes zeroth homology, so its native Wang operator is zero. -/
theorem cuspWangDifference_zero : wangDifference f₀ 0 = 0 :=
  BoundaryFirst.boundaryWangDifference_zero none

/-- The actual cusp monodromy preserves the genuine top torus class. -/
theorem cuspWangDifference_four : wangDifference f₀ 4 = 0 := by
  apply LinearMap.ext
  intro a
  apply (cuspTorusHomologyEquiv 4).injective
  rw [LinearMap.zero_apply, map_zero, cuspWangDifference_conjugacy, LinearMap.neg_apply,
    torusDifference_apply, TrianglePeriodFamily.Homology.torusMatrixMap_M₀_homologyFour,
    LinearMap.id_apply, sub_self, neg_zero]

private def cuspWangCokernelOfZeroAddEquiv (n : ℕ) (h : wangDifference f₀ n = 0) :
    CuspWangCokernel n ≃+ SingularHomology RealTorus₄ n := by
  letI := Submodule.Quotient.module (LinearMap.range (wangDifference f₀ n))
  exact ((LinearMap.range (wangDifference f₀ n)).quotEquivOfEqBot
    (by rw [h, LinearMap.range_zero])).toAddEquiv

/-- The actual zeroth Wang quotient is marked by integral augmentation. -/
def cuspWangCokernelZeroEquiv : CuspWangCokernel 0 ≃ₗ[ℤ] ℤ :=
  ((cuspWangCokernelOfZeroAddEquiv 0 cuspWangDifference_zero).trans
    (connectedHomologyZeroEquiv RealTorus₄).toAddEquiv).toIntLinearEquiv

/-- The actual first Wang quotient has its two primitive integral coordinates. -/
def cuspWangCokernelOneEquiv : CuspWangCokernel 1 ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  (BoundaryFirst.boundaryCokernelOneEquiv none).toAddEquiv.toIntLinearEquiv

/-- The actual fourth Wang quotient retains the native top-fibre marking. -/
def cuspWangCokernelFourEquiv : CuspWangCokernel 4 ≃ₗ[ℤ] ℤ :=
  ((cuspWangCokernelOfZeroAddEquiv 4 cuspWangDifference_four).trans
    realTorusH4Equiv.toAddEquiv).toIntLinearEquiv

/-- Above dimension four the actual source homology, hence its literal quotient, vanishes. -/
theorem cuspWangCokernel_subsingleton_of_four_lt {n : ℕ} (hn : 4 < n) :
    Subsingleton (CuspWangCokernel n) := by
  have := realTorus_homology_subsingleton_of_lt hn
  infer_instance

/-- Every native cusp Wang cokernel has the independently computed
central-fibre rank, with no specialization or kernel premise. -/
def cuspWangCokernelEquiv (n : ℕ) :
    CuspWangCokernel n ≃ₗ[ℤ] (Fin (centralBetti n) → ℤ) :=
  match n with
  | 0 => cuspWangCokernelZeroEquiv.trans (LinearEquiv.funUnique (Fin 1) ℤ ℤ).symm
  | 1 => cuspWangCokernelOneEquiv
  | 2 => cuspWangCokernelTwoEquiv
  | 3 => cuspWangCokernelThreeEquiv
  | 4 => cuspWangCokernelFourEquiv.trans (LinearEquiv.funUnique (Fin 1) ℤ ℤ).symm
  | n + 5 => by
      have := cuspWangCokernel_subsingleton_of_four_lt (show 4 < n + 5 by omega)
      change CuspWangCokernel (n + 5) ≃ₗ[ℤ] (Fin 0 → ℤ)
      exact LinearEquiv.ofSubsingleton _ _

/-- Freeness of the literal quotient, not only its rationalization. -/
theorem cuspWangCokernel_free (n : ℕ) : Module.Free ℤ (CuspWangCokernel n) :=
  Module.Free.of_equiv (cuspWangCokernelEquiv n).symm

/-- Finite generation of the literal integral quotient in every degree. -/
theorem cuspWangCokernel_finite (n : ℕ) : Module.Finite ℤ (CuspWangCokernel n) :=
  Module.Finite.of_surjective (cuspWangCokernelEquiv n).symm.toLinearMap
    (cuspWangCokernelEquiv n).symm.surjective

theorem cuspWangCokernel_torsionFree (n : ℕ) :
    Module.IsTorsionFree ℤ (CuspWangCokernel n) := by
  have := cuspWangCokernel_free n
  infer_instance

/-- The native Wang cokernel has ranks `1, 2, 4, 2, 1`, and zero above four. -/
theorem cuspWangCokernel_finrank (n : ℕ) :
    Module.finrank ℤ (CuspWangCokernel n) = centralBetti n := by
  rw [(cuspWangCokernelEquiv n).finrank_eq]
  exact Module.finrank_fin_fun ℤ

theorem cuspWangCokernel_finranks :
    (fun n : Fin 5 => Module.finrank ℤ (CuspWangCokernel n)) = ![1, 2, 4, 2, 1] := by
  funext n
  rw [cuspWangCokernel_finrank]
  fin_cases n <;> rfl

theorem cuspWangCokernel_finrank_eq_zero_of_four_lt {n : ℕ} (hn : 4 < n) :
    Module.finrank ℤ (CuspWangCokernel n) = 0 := by
  have := cuspWangCokernel_subsingleton_of_four_lt hn
  exact Module.finrank_zero_of_subsingleton

end Wikipedia.HopfProblem.ThreefoldHomologyCuspFibre
