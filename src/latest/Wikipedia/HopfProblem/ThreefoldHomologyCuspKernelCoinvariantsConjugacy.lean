import Wikipedia.HopfProblem.CuspCentralHomologySpecializationCoinvariantsHomology
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryCuspWang
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyTransportTorus
import Wikipedia.HopfProblem.ThreefoldOverlapMappingTorusSpaces

/-!
# The actual cusp Wang quotient in coordinate-torus homology

The genuine flat-to-circle homeomorphism conjugates the native cusp
monodromy to the actual coordinate torus map of `M₀`.  Its Wang operator
is the negative of the action-minus-identity convention used by the
existing integral coinvariant calculation.  Equality of those ranges
therefore gives an actual quotient equivalence, preserving every native
quotient representative through the original homeomorphism.
-/

noncomputable section

namespace Wikipedia.HopfProblem.ThreefoldHomologyCuspFibre

open SpecialPeriods SpecialPeriods.Threefold SingularMayerVietoris
open PeriodTorusHigherHomology MappingTorusHomology TrianglePeriodFamily
open CuspCentralHomology.SpecializationCoinvariants

local notation "f₀" => ThreefoldOverlapMappingTorus.monodromy none

/-- The literal native cusp Wang cokernel, with its original forward convention. -/
abbrev CuspWangCokernel (n : ℕ) :=
  SingularHomology RealTorus₄ n ⧸ LinearMap.range (wangDifference f₀ n)

/-- Actual homology transport by the original flat-to-circle homeomorphism. -/
def cuspTorusHomologyEquiv (n : ℕ) :
    SingularHomology RealTorus₄ n ≃ₗ[ℤ] SingularHomology (ProductTorus 4) n :=
  homeomorphHomologyEquiv flatTorusCircleHomeomorph n

@[simp] theorem cuspTorusHomologyEquiv_apply (n : ℕ)
    (a : SingularHomology RealTorus₄ n) :
    cuspTorusHomologyEquiv n a =
      singularHomologyMap
        (flatTorusCircleHomeomorph : C(RealTorus₄, ProductTorus 4)) n a := rfl

/-- The actual geometric conjugacy, applied to native singular homology. -/
theorem cuspTorusHomologyEquiv_monodromy (n : ℕ) (a : SingularHomology RealTorus₄ n) :
    cuspTorusHomologyEquiv n (monodromyHomologyMap f₀ n a) =
      singularHomologyMap (torusMatrixMap M₀) n (cuspTorusHomologyEquiv n a) := by
  have h := FlatTorus.flatTorusCircleHomology_triangle_apply triangleCuspGenerator n a
  rw [triangleDualRepresentation_cusp_matrix] at h
  have hm := LinearMap.congr_fun
    (TrianglePeriodFamily.Boundary.Cusp.monodromyHomology_triangle n) a
  exact (congrArg (cuspTorusHomologyEquiv n) hm).trans h

/-- The native `id - H(f₀)` operator is exactly the negative of the old
coordinate-torus `H(M₀) - id` operator under the actual homeomorphism. -/
theorem cuspWangDifference_conjugacy (n : ℕ) (a : SingularHomology RealTorus₄ n) :
    cuspTorusHomologyEquiv n (wangDifference f₀ n a) =
      (-torusDifference n) (cuspTorusHomologyEquiv n a) := by
  change cuspTorusHomologyEquiv n (a - monodromyHomologyMap f₀ n a) = _
  rw [map_sub, cuspTorusHomologyEquiv_monodromy, LinearMap.neg_apply,
    torusDifference_apply]
  abel

/-- Changing the sign changes no relation subgroup. -/
theorem cuspWangDifference_range_map (n : ℕ) :
    (LinearMap.range (wangDifference f₀ n)).map (cuspTorusHomologyEquiv n).toLinearMap =
      LinearMap.range (torusDifference n) := by
  have h := map_range_of_intertwines (cuspTorusHomologyEquiv n)
    (wangDifference f₀ n) (-torusDifference n) (cuspWangDifference_conjugacy n)
  rw [LinearMap.range_neg] at h
  exact h

private def cuspWangCokernelTorusAddEquiv (n : ℕ) :
    CuspWangCokernel n ≃+ TorusCoinvariants n := by
  letI := Submodule.Quotient.module (LinearMap.range (wangDifference f₀ n))
  letI := Submodule.Quotient.module (LinearMap.range (torusDifference n))
  exact (Submodule.Quotient.equiv (LinearMap.range (wangDifference f₀ n))
    (LinearMap.range (torusDifference n)) (cuspTorusHomologyEquiv n)
    (cuspWangDifference_range_map n)).toAddEquiv

/-- The actual native cusp Wang quotient is the actual coordinate-torus
coinvariant quotient, not a separately assigned homology group. -/
def cuspWangCokernelTorusEquiv (n : ℕ) :
    CuspWangCokernel n ≃ₗ[ℤ] TorusCoinvariants n :=
  (cuspWangCokernelTorusAddEquiv n).toIntLinearEquiv

@[simp] theorem cuspWangCokernelTorusEquiv_mk (n : ℕ)
    (a : SingularHomology RealTorus₄ n) :
    cuspWangCokernelTorusEquiv n (Submodule.Quotient.mk a) =
      Submodule.Quotient.mk (cuspTorusHomologyEquiv n a) := rfl

/-- The native second cusp Wang cokernel has four free integral coordinates. -/
def cuspWangCokernelTwoEquiv : CuspWangCokernel 2 ≃ₗ[ℤ] (Fin 4 → ℤ) :=
  ((cuspWangCokernelTorusEquiv 2).toAddEquiv.trans
    torusTwoCoinvariantEquiv.toAddEquiv).toIntLinearEquiv

/-- The native third cusp Wang cokernel has two free integral coordinates. -/
def cuspWangCokernelThreeEquiv : CuspWangCokernel 3 ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  ((cuspWangCokernelTorusEquiv 3).toAddEquiv.trans
    torusThreeCoinvariantEquiv.toAddEquiv).toIntLinearEquiv

@[simp] theorem cuspWangCokernelTwoEquiv_mk (a : SingularHomology RealTorus₄ 2) :
    cuspWangCokernelTwoEquiv (Submodule.Quotient.mk a) =
      squareProjection (coordinateTorusH2Coordinates (cuspTorusHomologyEquiv 2 a)) := by
  change torusTwoCoinvariantEquiv
    (cuspWangCokernelTorusEquiv 2 (Submodule.Quotient.mk a)) = _
  rw [cuspWangCokernelTorusEquiv_mk, torusTwoCoinvariantEquiv_mk]

@[simp] theorem cuspWangCokernelThreeEquiv_mk (a : SingularHomology RealTorus₄ 3) :
    cuspWangCokernelThreeEquiv (Submodule.Quotient.mk a) =
      cubeProjection (coordinateTorusH3Coordinates (cuspTorusHomologyEquiv 3 a)) := by
  change torusThreeCoinvariantEquiv
    (cuspWangCokernelTorusEquiv 3 (Submodule.Quotient.mk a)) = _
  rw [cuspWangCokernelTorusEquiv_mk, torusThreeCoinvariantEquiv_mk]

end Wikipedia.HopfProblem.ThreefoldHomologyCuspFibre
