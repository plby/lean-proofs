import Wikipedia.HopfProblem.EllipticHigherHomologyData
import Wikipedia.HopfProblem.EllipticFlatTorus
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Real coordinates adapted to the special elliptic twist

The first coordinate is measured along the actual primitive twist,
including its negative sign in the order-four case.  The remaining
coordinates lie in the kernel of the original first-coordinate
functional.  In this explicit continuous linear equivalence the actual
affine transformation is a translation by `1 / m` times the actual
three-dimensional fibre matrix.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology

abbrev FibreCoordinates := Fin 3 → ℝ

/-- The real restriction of the actual integral elliptic matrix. -/
def fibreLinear (j : Kind) : FibreCoordinates →ₗ[ℝ] FibreCoordinates :=
  ((fibreMatrix j).map (Int.castRingHom ℝ)).mulVecLin

@[simp] theorem fibreLinear_apply (j : Kind) (k : FibreCoordinates) :
    fibreLinear j k = (fibreMatrix j).map (Int.castRingHom ℝ) *ᵥ k := rfl

/-- Splitting into the actual twist direction and the kernel of `γ`.
The first coordinate is `γ(v) γ(x)`, since the chosen `γ(v)` is `±1`. -/
def splitRealCoordinates (j : Kind) : RealCoordinates ≃L[ℝ] ℝ × FibreCoordinates :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun x => ((j.twist 0 : ℝ) * x 0,
        fun i => x i.succ - ((j.twist 0 : ℝ) * x 0) * (j.twist i.succ : ℝ))
      invFun := fun x => x.1 • realCast j.twist + Fin.cons 0 x.2
      left_inv := by
        intro x
        funext i
        refine Fin.cases ?_ (fun k => ?_) i
        · cases j <;> simp [Kind.twist, realCast, ε, ε']
        · simp [realCast]
      right_inv := by
        rintro ⟨t, k⟩
        apply Prod.ext
        · cases j <;> simp [Kind.twist, realCast, ε, ε']
        · funext i
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.cons_zero, Fin.cons_succ]
          cases j <;> fin_cases i <;> simp [Kind.twist, realCast, ε, ε']
      map_add' := by
        intro x y
        apply Prod.ext
        · simp [mul_add]
        · funext i
          simp only [Pi.add_apply, Prod.mk_add_mk]
          ring
      map_smul' := by
        intro r x
        apply Prod.ext
        · simp only [Pi.smul_apply, smul_eq_mul, Prod.smul_mk,
            RingHom.id_apply]
          ring
        · funext i
          simp only [Pi.smul_apply, smul_eq_mul, Prod.smul_mk,
            RingHom.id_apply]
          ring }

@[simp] theorem splitRealCoordinates_apply (j : Kind) (x : RealCoordinates) :
    splitRealCoordinates j x = ((j.twist 0 : ℝ) * x 0,
      fun i => x i.succ - ((j.twist 0 : ℝ) * x 0) * (j.twist i.succ : ℝ)) := rfl

@[simp] theorem splitRealCoordinates_symm_apply (j : Kind) (x : ℝ × FibreCoordinates) :
    (splitRealCoordinates j).symm x = x.1 • realCast j.twist + Fin.cons 0 x.2 := rfl

/-- The fibre subspace is precisely the kernel of the original first coordinate. -/
theorem flatLinear_fibre (j : Kind) (k : FibreCoordinates) :
    flatLinear j (Fin.cons 0 k) = Fin.cons 0 (fibreLinear j k) := by
  ext i
  refine Fin.cases ?_ (fun a => ?_) i
  · cases j <;> simp [flatLinear, Kind.matrix, A₁, A₂,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  · rw [Fin.cons_succ]
    cases j <;> fin_cases a <;>
      simp [flatLinear, fibreLinear, fibreMatrix, Kind.matrix, A₁, A₂,
        Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- The chosen twist direction is fixed by the actual real linear action. -/
theorem flatLinear_twist (j : Kind) :
    flatLinear j (realCast j.twist) = realCast j.twist := by
  rw [flatLinear_realCast, j.matrix_fixes_twist]

/-- The linear action in split coordinates fixes the twist coordinate
and acts on the other three coordinates by the actual fibre matrix. -/
theorem splitRealCoordinates_flatLinear (j : Kind) (x : RealCoordinates) :
    splitRealCoordinates j (flatLinear j x) =
      ((splitRealCoordinates j x).1, fibreLinear j (splitRealCoordinates j x).2) := by
  obtain ⟨⟨t, k⟩, rfl⟩ := (splitRealCoordinates j).symm.surjective x
  simp only [ContinuousLinearEquiv.apply_symm_apply]
  apply (splitRealCoordinates j).symm.injective
  simp only [ContinuousLinearEquiv.symm_apply_apply, splitRealCoordinates_symm_apply,
    map_add, map_smul, flatLinear_twist, flatLinear_fibre]

/-- The actual affine elliptic action translates once by `1 / m` in
the primitive twist direction and acts linearly on the fibre coordinates. -/
theorem splitRealCoordinates_flatAffine (j : Kind) (x : RealCoordinates) :
    splitRealCoordinates j (flatAffine j j.twist x) =
      ((splitRealCoordinates j x).1 + 1 / (j.order : ℝ),
        fibreLinear j (splitRealCoordinates j x).2) := by
  obtain ⟨⟨t, k⟩, rfl⟩ := (splitRealCoordinates j).symm.surjective x
  simp only [ContinuousLinearEquiv.apply_symm_apply]
  apply (splitRealCoordinates j).symm.injective
  simp only [ContinuousLinearEquiv.symm_apply_apply, splitRealCoordinates_symm_apply,
    flatAffine, map_add, map_smul, flatLinear_twist, flatLinear_fibre]
  simp only [add_smul]
  abel

/-- The affine formula directly on the assembled split real coordinates. -/
theorem flatAffine_splitRealCoordinates_symm (j : Kind) (t : ℝ) (k : FibreCoordinates) :
    flatAffine j j.twist ((splitRealCoordinates j).symm (t, k)) =
      (splitRealCoordinates j).symm (t + 1 / (j.order : ℝ), fibreLinear j k) := by
  apply (splitRealCoordinates j).injective
  rw [splitRealCoordinates_flatAffine, ContinuousLinearEquiv.apply_symm_apply,
    ContinuousLinearEquiv.apply_symm_apply]

end Wikipedia.HopfProblem.Elliptic.HigherHomology
