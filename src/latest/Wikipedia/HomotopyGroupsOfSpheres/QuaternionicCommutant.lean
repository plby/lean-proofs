import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicRealRepresentation

/-!
# Quaternionic matrices are the real operators commuting with right multiplication

This gives the operator model needed to restrict real orthogonal geometry
to the original symplectic group. The inverse map extracts actual matrix
entries from the images of the quaternionic coordinate vectors.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns

open QuaternionicRankOne NoExoticSixSphere.GLOrthonormalization

local notation "ℍ" => Quaternion ℝ

/-- Right scalar multiplication on the real quaternionic vector space. -/
def rightMulLinear (n : ℕ) (q : ℍ) : QuaternionSpace n →ₗ[ℝ] QuaternionSpace n where
  toFun v := WithLp.toLp 2 (fun i => WithLp.ofLp v i * q)
  map_add' u v := by
    apply (WithLp.equiv 2 (Fin (n + 1) → ℍ)).injective
    funext i
    exact add_mul _ _ _
  map_smul' c v := by
    apply (WithLp.equiv 2 (Fin (n + 1) → ℍ)).injective
    funext i
    exact smul_mul_assoc c _ q

/-- The same right action in orthonormal real coordinates. -/
def rightAction (n : ℕ) (q : ℍ) : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4) :=
  ((quaternionCoordinates n).toLinearEquiv.toLinearMap.comp
    ((rightMulLinear n q).comp
      (quaternionCoordinates n).symm.toLinearEquiv.toLinearMap)).toContinuousLinearMap

theorem rightAction_apply (n : ℕ) (q : ℍ) (v : Vector (4 * n + 4)) :
    rightAction n q v = quaternionCoordinates n
      (rightMulLinear n q ((quaternionCoordinates n).symm v)) := rfl

/-- The full real commutant of quaternionic right scalar multiplication. -/
def commutant (n : ℕ) : Subalgebra ℝ (Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)) :=
  Subalgebra.centralizer ℝ (Set.range (rightAction n))

theorem mem_commutant_iff (n : ℕ) (T : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)) :
    T ∈ commutant n ↔ ∀ q, T.comp (rightAction n q) = (rightAction n q).comp T := by
  rw [commutant, Subalgebra.mem_centralizer_iff]
  constructor
  · intro h q
    exact (h (rightAction n q) ⟨q, rfl⟩).symm
  · rintro h _ ⟨q, rfl⟩
    exact (h q).symm

theorem realAction_mem_commutant (n : ℕ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ) : realAction n A ∈ commutant n := by
  apply (mem_commutant_iff n _).mpr
  intro q
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.comp_apply, rightAction_apply, realAction_apply,
    (quaternionCoordinates n).symm_apply_apply]
  apply congrArg (quaternionCoordinates n)
  apply (WithLp.equiv 2 (Fin (n + 1) → ℍ)).injective
  funext i
  change (∑ k, A i k * (WithLp.ofLp ((quaternionCoordinates n).symm v) k * q)) =
    (∑ k, A i k * WithLp.ofLp ((quaternionCoordinates n).symm v) k) * q
  simp only [Finset.sum_mul, mul_assoc]

/-- Extract the quaternionic coefficients of an arbitrary real operator. -/
def coefficients (n : ℕ) (T : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ :=
  fun i j => WithLp.ofLp ((quaternionCoordinates n).symm
    (T (quaternionCoordinates n (WithLp.toLp 2 (axis j))))) i

theorem coefficients_realAction (n : ℕ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ) : coefficients n (realAction n A) = A := by
  apply Matrix.ext
  intro i j
  simp [coefficients, realAction_apply, axis]

theorem continuous_coefficients (n : ℕ) : Continuous (coefficients n) := by
  apply continuous_matrix
  intro i j
  exact (continuous_apply i).comp
    ((PiLp.homeomorph 2 (fun _ : Fin (n + 1) => ℍ)).continuous.comp
      ((quaternionCoordinates n).symm.continuous.comp
        (continuous_id.clm_apply continuous_const)))

/-- An operator written back in the quaternionic coordinates. -/
def coordinateOperator (n : ℕ) (T : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)) :
    QuaternionSpace n →ₗ[ℝ] QuaternionSpace n :=
  (quaternionCoordinates n).symm.toLinearEquiv.toLinearMap.comp
    (T.toLinearMap.comp (quaternionCoordinates n).toLinearEquiv.toLinearMap)

theorem coordinateOperator_apply (n : ℕ)
    (T : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)) (v : QuaternionSpace n) :
    coordinateOperator n T v = (quaternionCoordinates n).symm (T (quaternionCoordinates n v)) := rfl

theorem coordinateOperator_rightMul (n : ℕ)
    (T : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)) (hT : T ∈ commutant n)
    (q : ℍ) (v : QuaternionSpace n) :
    coordinateOperator n T (rightMulLinear n q v) =
      rightMulLinear n q (coordinateOperator n T v) := by
  have h := congrArg (fun L : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4) =>
    (quaternionCoordinates n).symm (L (quaternionCoordinates n v)))
      ((mem_commutant_iff n T).mp hT q)
  simpa only [ContinuousLinearMap.comp_apply, rightAction_apply,
    (quaternionCoordinates n).symm_apply_apply, coordinateOperator_apply] using h

theorem quaternionic_coordinate_decomposition (n : ℕ) (v : QuaternionSpace n) :
    v = ∑ j, rightMulLinear n (WithLp.ofLp v j) (WithLp.toLp 2 (axis j)) := by
  apply (WithLp.equiv 2 (Fin (n + 1) → ℍ)).injective
  change WithLp.ofLp v = WithLp.ofLp (∑ j,
    rightMulLinear n (WithLp.ofLp v j) (WithLp.toLp 2 (axis j)))
  rw [WithLp.ofLp_sum]
  funext i
  simp [rightMulLinear, axis, Finset.sum_apply]

theorem realAction_coefficients (n : ℕ)
    (T : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)) (hT : T ∈ commutant n) :
    realAction n (coefficients n T) = T := by
  have hcoord (v : QuaternionSpace n) :
      coordinateOperator n T v = lpAction n (coefficients n T) v := by
    conv_lhs => rhs; rw [quaternionic_coordinate_decomposition n v]
    rw [map_sum]
    simp_rw [coordinateOperator_rightMul n T hT]
    apply (WithLp.equiv 2 (Fin (n + 1) → ℍ)).injective
    change WithLp.ofLp (∑ j, rightMulLinear n (WithLp.ofLp v j)
      (coordinateOperator n T (WithLp.toLp 2 (axis j)))) =
        (coefficients n T) *ᵥ WithLp.ofLp v
    rw [WithLp.ofLp_sum]
    funext i
    simp only [Finset.sum_apply, rightMulLinear, LinearMap.coe_mk, AddHom.coe_mk,
      WithLp.ofLp_toLp, coefficients, coordinateOperator_apply, Matrix.mulVec, dotProduct]
  apply ContinuousLinearMap.ext
  intro v
  have h := congrArg (quaternionCoordinates n) (hcoord ((quaternionCoordinates n).symm v))
  change quaternionCoordinates n (lpAction n (coefficients n T)
    ((quaternionCoordinates n).symm v)) = T v
  simpa only [coordinateOperator_apply, (quaternionCoordinates n).apply_symm_apply] using h.symm

/-- The real representation identifies the matrix algebra with this actual commutant. -/
def commutantAlgEquiv (n : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℍ ≃ₐ[ℝ] commutant n :=
  AlgEquiv.ofBijective ((realRepresentation n).codRestrict (commutant n)
    (realAction_mem_commutant n)) (by
      constructor
      · intro A B h
        exact realAction_injective n (congrArg Subtype.val h)
      · intro T
        exact ⟨coefficients n T.val, Subtype.ext (realAction_coefficients n T.val T.property)⟩)

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns
