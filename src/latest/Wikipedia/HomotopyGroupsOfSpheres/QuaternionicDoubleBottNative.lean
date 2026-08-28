import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicDoubleBottComparison
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottOriginalMap
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSecondBottHomotopy

/-! # The explicit matrix cubes represent the actual composite Bott isomorphism -/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottMatrix

open QuaternionicColumns QuaternionicSymmetricMatrices NoExoticSixSphere

variable {n d : ℕ}

local notation "Source" => AnticommutingStructures.Space (ComplexStructures.standard n)
local notation "sourcePoint" => AnticommutingStructures.standard n

attribute [local irreducible] operatorTwoCubeFamily conjugatedOperatorTwoCubeFamily
  doubleBottConjugationHomotopy

def doubleBottNativeCube (p : GenLoop (Fin d) Source sourcePoint) :
    GenLoop (Fin (d + 2)) (symplecticSubgroup n) 1 :=
  GeneralizedLoopCurrying.uncurry
    (HigherHomotopy.genLoopMap (MinimumPaths.loopMap (ComplexStructures.standard n))
      (MinimumPaths.loopMap_reference (ComplexStructures.standard n))
      (SecondPaths.inducedCube sourcePoint p))

theorem doubleBottNativeCube_apply (p : GenLoop (Fin d) Source sourcePoint)
    (u : Fin (d + 2) → I) :
    doubleBottNativeCube p u =
      MinimumPaths.loopMap (ComplexStructures.standard n)
        (SecondPaths.loopMap sourcePoint (p (Fin.tail (Fin.tail u))) (u 1)) (u 0) := rfl

def doubleBottCubeParameters (p : GenLoop (Fin d) Source sourcePoint) :
    C((Fin (d + 2) → I), Space (Fin (n + 1)) × (Fin 2 → I)) where
  toFun u := (AnticommutingStructures.toSymmetricUnitary (p (Fin.tail (Fin.tail u))), ![u 0, u 1])
  continuous_toFun := by
    apply Continuous.prodMk
    · exact AnticommutingStructures.continuous_toSymmetricUnitary.comp
        (p.val.continuous.comp (continuous_pi (fun i ↦ continuous_apply i.succ.succ)))
    · apply continuous_pi
      intro i
      fin_cases i <;> exact continuous_apply _

theorem doubleBottCubeParameters_boundary (p : GenLoop (Fin d) Source sourcePoint)
    (u : Fin (d + 2) → I) (hu : u ∈ Cube.boundary (Fin (d + 2))) :
    (doubleBottCubeParameters p u).1 = identity ∨
      (doubleBottCubeParameters p u).2 ∈ Cube.boundary (Fin 2) := by
  rcases (CubeFirstCoordinate.boundary_split_iff (d + 1) u).mp hu with h | h | h
  · exact Or.inr ⟨0, Or.inl h⟩
  · exact Or.inr ⟨0, Or.inr h⟩
  · rcases (CubeFirstCoordinate.boundary_split_iff d (Fin.tail u)).mp h with h | h | h
    · exact Or.inr ⟨1, Or.inl h⟩
    · exact Or.inr ⟨1, Or.inr h⟩
    · left
      change AnticommutingStructures.toSymmetricUnitary (p (Fin.tail (Fin.tail u))) = identity
      have hp : p (Fin.tail (Fin.tail u)) = sourcePoint := p.property _ h
      rw [hp]
      exact AnticommutingStructures.symmetricUnitaryHomeomorph_standard n

def operatorMatrixCube (p : GenLoop (Fin d) Source sourcePoint) :
    GenLoop (Fin (d + 2)) (symplecticSubgroup n) 1 :=
  ⟨operatorTwoCubeFamily.comp (doubleBottCubeParameters p), by
    intro u hu
    rcases doubleBottCubeParameters_boundary p u hu with h | h
    · change operatorTwoCubeFamily ((doubleBottCubeParameters p u).1,
        (doubleBottCubeParameters p u).2) = 1
      rw [h, operatorTwoCubeFamily_identity]
    · exact operatorTwoCubeFamily_boundary _ _ h⟩

theorem operatorMatrixCube_apply (p : GenLoop (Fin d) Source sourcePoint)
    (u : Fin (d + 2) → I) :
    operatorMatrixCube p u = symplecticHomeomorph n
      (basedRotation ((u 0 : ℝ) * Real.pi) ((u 1 : ℝ) * Real.pi)
        (AnticommutingStructures.toSymmetricUnitary (p (Fin.tail (Fin.tail u))))) := by
  unfold operatorMatrixCube operatorTwoCubeFamily
  rfl

theorem conjugatedOperatorFamily_nativeCube (p : GenLoop (Fin d) Source sourcePoint) :
    conjugatedOperatorTwoCubeFamily.comp (doubleBottCubeParameters p) =
      (doubleBottNativeCube p).val := by
  apply ContinuousMap.ext
  intro u
  change conjugatedOperatorTwoCubeFamily
    (AnticommutingStructures.toSymmetricUnitary (p (Fin.tail (Fin.tail u))), ![u 0, u 1]) = _
  rw [conjugatedOperatorTwoCubeFamily_apply,
    AnticommutingStructures.ofSymmetricUnitary_toSymmetricUnitary]
  rfl

def operatorMatrixCubeHomotopy (p : GenLoop (Fin d) Source sourcePoint) :
    (operatorMatrixCube p).val.HomotopyRel (doubleBottNativeCube p).val
      (Cube.boundary (Fin (d + 2))) where
  toHomotopy := (doubleBottConjugationHomotopy.compContinuousMap
    (doubleBottCubeParameters p)).cast rfl (conjugatedOperatorFamily_nativeCube p)
  prop' r u hu := by
    change doubleBottConjugationHomotopy (r, doubleBottCubeParameters p u) = operatorMatrixCube p u
    have hp : operatorMatrixCube p u = 1 := (operatorMatrixCube p).property u hu
    rw [hp]
    rcases doubleBottCubeParameters_boundary p u hu with h | h
    · change doubleBottConjugationHomotopy (r,
        ((doubleBottCubeParameters p u).1, (doubleBottCubeParameters p u).2)) = 1
      rw [h, doubleBottConjugationHomotopy_identity]
    · exact doubleBottConjugationHomotopy_boundary r _ _ h

theorem operatorMatrixCube_class_eq (p : GenLoop (Fin d) Source sourcePoint) :
    (⟦operatorMatrixCube p⟧ : π_ (d + 2) (symplecticSubgroup n) 1) = ⟦doubleBottNativeCube p⟧ :=
  Quotient.sound ⟨operatorMatrixCubeHomotopy p⟩

def doubleBottDegreeShiftMulEquiv (d : ℕ) [NeZero d] (hd : d + 2 < n) :
    π_ d Source sourcePoint ≃* π_ (d + 2) (symplecticSubgroup n) 1 :=
  (SecondPaths.bottDegreeShiftMulEquiv d sourcePoint (by omega)).trans
    (Polygon.bottDegreeShiftMulEquiv (d + 1) 1 (ComplexStructures.antipode n)
      (Polygon.identity_antipodal n) (ComplexStructures.standard n) hd)

theorem doubleBottDegreeShiftMulEquiv_mk [NeZero d] (hd : d + 2 < n)
    (p : GenLoop (Fin d) Source sourcePoint) :
    doubleBottDegreeShiftMulEquiv d hd (⟦p⟧ : π_ d Source sourcePoint) =
      (⟦operatorMatrixCube p⟧ : π_ (d + 2) (symplecticSubgroup n) 1) := by
  have h₁ := congrArg
    (Polygon.bottDegreeShiftMulEquiv (d + 1) 1 (ComplexStructures.antipode n)
      (Polygon.identity_antipodal n) (ComplexStructures.standard n) hd)
    (SecondPaths.bottDegreeShiftMulEquiv_mk d sourcePoint (by omega) p)
  have h₂ := Polygon.bottDegreeShiftMulEquiv_mk (d + 1) (ComplexStructures.standard n) hd
    (SecondPaths.inducedCube sourcePoint p)
  exact h₁.trans (h₂.trans (operatorMatrixCube_class_eq p).symm)

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottMatrix
