import Wikipedia.HopfProblem.DegreeCollapseBalancedFrameComponents
import Wikipedia.HopfProblem.DegreeCollapseQuaternionicClutching

/-!
# Reduction of the actual first stable stem to orthogonal components

The actual sphere suspensions identify pi10(S9) with pi4(S3). The original
quaternionic fiber inclusion then identifies the latter with pi4(Sp(2)).
Three proved Bott maps and the actual frame endpoint bijection reduce this
to pi0(O(4)). No numerical value for these groups, generator, or
Whitehead--eta nonvanishing is assumed here.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.FirstStemReduction

open NoExoticSixSphere GLOrthonormalization
open Wikipedia.HomotopyGroupsOfSpheres QuaternionicColumns
open QuaternionicSymmetricMatrices

def firstBott (n : ℕ) (hn : 4 < n) :
    π_ 4 QuaternionicFibration.SpTwo 1 ≃*
      π_ 3 (ComplexStructures.Space n) (ComplexStructures.standard n) := by
  have e := stabilizationInRangeIterate 2 4 (by decide) (n - 1)
  have hdim : 2 + (n - 1) = n + 1 := by omega
  rw [hdim] at e
  exact e.trans (Polygon.bottMatrixDegreeShiftMulEquiv 3
    (ComplexStructures.standard n) hn).symm

def secondBott (n : ℕ) (hn : 4 < n) :
    π_ 4 QuaternionicFibration.SpTwo 1 ≃*
      π_ 2 (AnticommutingStructures.Space (ComplexStructures.standard n))
        (AnticommutingStructures.standard n) :=
  (firstBott n hn).trans
    (SecondPaths.bottDegreeShiftMulEquiv 2 (AnticommutingStructures.standard n) (by omega)).symm

def symmetricCoordinates (n : ℕ) (hn : 4 < n) :
    π_ 4 QuaternionicFibration.SpTwo 1 ≃*
      π_ 2 (SpecialSpace (Fin (n + 1))) specialIdentity :=
  ((secondBott n hn).trans (symmetricUnitaryCoordinatesMulEquiv n 2)).trans
    (specialInclusionMulEquiv n 0).symm

def thirdBott (n : ℕ) (hn : 2 < n) :
    π_ 4 QuaternionicFibration.SpTwo 1 ≃*
      π_ 1 (BalancedRealInvolutions.Space n) (BalancedRealInvolutions.standard n) :=
  ((symmetricCoordinates (2 * n - 1) (by omega)).trans
    (specialReindexHomotopyMulEquiv (balancedIndexEquiv n (by omega)) 2)).trans
      (BalancedRealInvolutions.bottDegreeShiftMulEquiv n 1 hn).symm

def orthogonalComparison (n : ℕ) (hn : 2 < n) :
    π_ 4 QuaternionicFibration.SpTwo 1 ≃ π_ 0 (OrthogonalOperators n) 1 :=
  (thirdBott n hn).toEquiv.trans
    (BalancedFrameComponents.balancedOrthogonalComponentsEquiv n (by omega))

theorem northAxis_eq :
    (QuaternionicFibration.northSubgroup : Set QuaternionicFibration.SpTwo) =
      (axisSubgroup (0 : Fin 2) : Set QuaternionicFibration.SpTwo) := by
  ext A
  change QuaternionicFibration.projection A = QuaternionicFibration.north ↔
    column 0 A = axisColumn 0
  rw [QuaternionicFibration.projection_eq_north_iff]
  constructor
  · rintro ⟨h₀, h₁⟩
    apply Subtype.ext
    funext i
    fin_cases i <;>
      simp [column, axisColumn, QuaternionicRankOne.axis, h₀, h₁]
  · intro h
    have h₀ := congrArg (fun v : UnitColumn (Fin 2) ↦ v.val 0) h
    have h₁ := congrArg (fun v : UnitColumn (Fin 2) ↦ v.val 1) h
    constructor
    · simpa [column, axisColumn, QuaternionicRankOne.axis] using h₀
    · simpa [column, axisColumn, QuaternionicRankOne.axis] using h₁

def northAxisHomeomorph :
    QuaternionicFibration.northSubgroup ≃ₜ axisSubgroup (0 : Fin 2) :=
  Homeomorph.setCongr northAxis_eq

theorem northAxisHomeomorph_one : northAxisHomeomorph 1 = 1 := Subtype.ext rfl

def fiberInclusionEquiv :
    π_ 4 QuaternionicFibration.northSubgroup 1 ≃* π_ 4 QuaternionicFibration.SpTwo 1 := by
  let := unitColumn_homotopy_subsingleton 1 4 (by decide) (axisColumn 0)
  let := unitColumn_homotopy_subsingleton 1 5 (by decide) (axisColumn 0)
  exact (pointedHomeomorphMulEquiv northAxisHomeomorph 1 1 northAxisHomeomorph_one).trans
    (inclusionMulEquiv (0 : Fin 2) 4)

def threeSphereComparison :
    π_ 4 (NoExoticSixSphere.Sphere 3) (spherePole 3) ≃*
      π_ 4 QuaternionicFibration.SpTwo 1 :=
  (pointedHomeomorphMulEquiv QuaternionicFibration.fiberSphereHomeomorph 1 (spherePole 3)
    QuaternionicClutching.fiberSphereHomeomorph_one).symm.trans fiberInclusionEquiv

def sphereStep (k : ℕ) :
    π_ (k + 4) (NoExoticSixSphere.Sphere (k + 3)) (spherePole (k + 3)) ≃*
      π_ (k + 4 + 1) (NoExoticSixSphere.Sphere (k + 3 + 1)) (spherePole (k + 3 + 1)) :=
  MulEquiv.ofBijective (CubicalSphereSuspension.hom (k + 4) (k + 3))
    (CubicalSphereSuspension.hom_bijective (by omega))

def sphereNineComparison :
    π_ 10 (NoExoticSixSphere.Sphere 9) (spherePole 9) ≃ π_ 0 (OrthogonalOperators 4) 1 :=
  ((((((sphereStep 0).trans (sphereStep 1)).trans (sphereStep 2)).trans
    (sphereStep 3)).trans (sphereStep 4)).trans (sphereStep 5)).symm.toEquiv.trans
      (threeSphereComparison.toEquiv.trans (orthogonalComparison 4 (by decide)))

end Wikipedia.HopfProblem.DegreeCollapse.FirstStemReduction
