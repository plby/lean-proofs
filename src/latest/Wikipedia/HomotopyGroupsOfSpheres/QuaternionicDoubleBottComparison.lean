import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicDoubleBottCube
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSecondLoopMap
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicMinimumPathFamily
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSkewConjugationExponential

/-!
# The explicit double Bott matrix and the two actual based loop maps

The second comparison uses a conjugated reference rotation. Its subsequent
first Bott loop is therefore conjugate to the explicit reference-divided
matrix, by the same reference path. This conjugation is removed by a
continuous homotopy that fixes the angular boundary and reference parameter.
-/

noncomputable section

open scoped unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructures

variable {n : ℕ}

theorem exp_smul_conjugate (a : symplecticSubgroup n) (J : Space n) (s : ℝ) :
    Exponential.exp (s • (conjugate a J).val) =
      a * Exponential.exp (s • J.val) * a⁻¹ := by
  have hs : s • (conjugate a J).val = conjugateSkew a (s • J.val) := by
    apply Subtype.ext
    change s • (a.val.val.val * (J.val.val * (a⁻¹).val.val.val)) =
      a.val.val.val * ((s • J.val.val) * (a⁻¹).val.val.val)
    simp only [mul_smul_comm, smul_mul_assoc]
  rw [hs, exp_conjugateSkew]

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructures

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottMatrix

open QuaternionicColumns QuaternionicSymmetricMatrices

variable {n : ℕ}

attribute [local irreducible] rotation AnticommutingStructures.ofSymmetricUnitary

theorem symplecticHomeomorph_basedRotation (s t : ℝ) (B : Space (Fin (n + 1))) :
    symplecticHomeomorph n (basedRotation s t B) =
      Exponential.exp (s • (AnticommutingStructures.rotation
        (AnticommutingStructures.ofSymmetricUnitary B) t).val) *
      (Exponential.exp (s • (AnticommutingStructures.rotation
        (AnticommutingStructures.standard n) t).val))⁻¹ := by
  change symplecticMulEquiv n (rotation s t B * (rotation s t identity)⁻¹) = _
  rw [map_mul, map_inv]
  change symplecticHomeomorph n (rotation s t B) *
    (symplecticHomeomorph n (rotation s t identity))⁻¹ = _
  rw [symplecticHomeomorph_rotation, symplecticHomeomorph_rotation,
    AnticommutingStructures.ofSymmetricUnitary_identity]

/-- Pointwise formula for the composition of the original two Bott loop maps. -/
theorem doubleBottLoop_apply (B : Space (Fin (n + 1))) (s t : I) :
    MinimumPaths.loopMap (ComplexStructures.standard n)
      (SecondPaths.loopMap (AnticommutingStructures.standard n)
        (AnticommutingStructures.ofSymmetricUnitary B) t) s =
      (AnticommutingStructures.conjugator (AnticommutingStructures.standard n)
        ((t : ℝ) * Real.pi))⁻¹ *
      symplecticHomeomorph n (basedRotation ((s : ℝ) * Real.pi) ((t : ℝ) * Real.pi) B) *
      AnticommutingStructures.conjugator (AnticommutingStructures.standard n)
        ((t : ℝ) * Real.pi) := by
  let c := AnticommutingStructures.conjugator (AnticommutingStructures.standard n)
    ((t : ℝ) * Real.pi)
  have href : Exponential.exp (((s : ℝ) * Real.pi) •
      (AnticommutingStructures.rotation (AnticommutingStructures.standard n)
        ((t : ℝ) * Real.pi)).val) =
      c * Exponential.exp (((s : ℝ) * Real.pi) • (ComplexStructures.standard n).val) * c⁻¹ := by
    rw [← AnticommutingStructures.conjugator_rotation]
    exact ComplexStructures.exp_smul_conjugate c (ComplexStructures.standard n) _
  rw [MinimumPaths.loopMap_apply, SecondPaths.loopMap_apply,
    ComplexStructures.exp_smul_conjugate, inv_inv, symplecticHomeomorph_basedRotation, href]
  change c⁻¹ * _ * c * _ = c⁻¹ * (_ * (c * _ * c⁻¹)⁻¹) * c
  group

def operatorTwoCubeFamily :
    C(Space (Fin (n + 1)) × (Fin 2 → I), symplecticSubgroup n) :=
  (symplecticHomeomorph n : C(_, _)).comp twoCubeFamily

theorem operatorTwoCubeFamily_identity (u : Fin 2 → I) :
    operatorTwoCubeFamily (n := n) (identity, u) = 1 := by
  change symplecticMulEquiv n (twoCubeMap identity u) = 1
  rw [twoCubeMap_identity]
  exact map_one (symplecticMulEquiv n)

theorem operatorTwoCubeFamily_boundary (B : Space (Fin (n + 1))) (u : Fin 2 → I)
    (hu : u ∈ Cube.boundary (Fin 2)) : operatorTwoCubeFamily (B, u) = 1 := by
  change symplecticMulEquiv n (twoCubeFamily (B, u)) = 1
  rw [twoCubeFamily_boundary B u hu, map_one]

def referenceConjugatorFamily : C(I × (Space (Fin (n + 1)) × (Fin 2 → I)),
    symplecticSubgroup n) where
  toFun p := AnticommutingStructures.conjugator (AnticommutingStructures.standard n)
    ((p.1 : ℝ) * ((p.2.2 1 : ℝ) * Real.pi))
  continuous_toFun :=
    (AnticommutingStructures.continuous_conjugator (AnticommutingStructures.standard n)).comp
      ((continuous_subtype_val.comp continuous_fst).mul
        ((continuous_subtype_val.comp ((continuous_apply 1).comp
          (continuous_snd.comp continuous_snd))).mul_const Real.pi))

theorem referenceConjugatorFamily_zero (z : Space (Fin (n + 1)) × (Fin 2 → I)) :
    referenceConjugatorFamily (0, z) = 1 := by
  change AnticommutingStructures.conjugator (AnticommutingStructures.standard n)
    ((0 : ℝ) * _) = 1
  rw [zero_mul, AnticommutingStructures.conjugator_zero]

def conjugatedOperatorTwoCubeFamily :
    C(Space (Fin (n + 1)) × (Fin 2 → I), symplecticSubgroup n) :=
  let c := referenceConjugatorFamily.comp ⟨fun z ↦ (1, z), continuous_const.prodMk continuous_id⟩
  c⁻¹ * operatorTwoCubeFamily * c

theorem conjugatedOperatorTwoCubeFamily_apply (B : Space (Fin (n + 1))) (u : Fin 2 → I) :
    conjugatedOperatorTwoCubeFamily (B, u) =
      MinimumPaths.loopMap (ComplexStructures.standard n)
        (SecondPaths.loopMap (AnticommutingStructures.standard n)
          (AnticommutingStructures.ofSymmetricUnitary B) (u 1)) (u 0) := by
  rw [doubleBottLoop_apply]
  change (AnticommutingStructures.conjugator (AnticommutingStructures.standard n)
      ((1 : ℝ) * _))⁻¹ * _ *
      AnticommutingStructures.conjugator (AnticommutingStructures.standard n)
        ((1 : ℝ) * _) = _
  simp only [one_mul]
  rfl

def doubleBottConjugationHomotopy :
    operatorTwoCubeFamily.Homotopy (conjugatedOperatorTwoCubeFamily (n := n)) where
  toContinuousMap := referenceConjugatorFamily⁻¹ *
    (operatorTwoCubeFamily.comp ⟨Prod.snd, continuous_snd⟩) * referenceConjugatorFamily
  map_zero_left z := by
    change (referenceConjugatorFamily (0, z))⁻¹ * operatorTwoCubeFamily z *
      referenceConjugatorFamily (0, z) = _
    rw [referenceConjugatorFamily_zero, inv_one, one_mul, mul_one]
  map_one_left _ := rfl

theorem doubleBottConjugationHomotopy_identity (r : I) (u : Fin 2 → I) :
    doubleBottConjugationHomotopy (n := n) (r, (identity, u)) = 1 := by
  change (referenceConjugatorFamily (r, (identity, u)))⁻¹ *
    operatorTwoCubeFamily (identity, u) * referenceConjugatorFamily (r, (identity, u)) = 1
  rw [operatorTwoCubeFamily_identity, mul_one, inv_mul_cancel]

theorem doubleBottConjugationHomotopy_boundary (r : I)
    (B : Space (Fin (n + 1))) (u : Fin 2 → I) (hu : u ∈ Cube.boundary (Fin 2)) :
    doubleBottConjugationHomotopy (r, (B, u)) = 1 := by
  change (referenceConjugatorFamily (r, (B, u)))⁻¹ * operatorTwoCubeFamily (B, u) *
    referenceConjugatorFamily (r, (B, u)) = 1
  rw [operatorTwoCubeFamily_boundary B u hu, mul_one, inv_mul_cancel]

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicBottMatrix
