import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicProjectedCoordinates
import Wikipedia.HomotopyGroupsOfSpheres.DiagonalSymmetricCurveTangent
import Wikipedia.HomotopyGroupsOfSpheres.SymmetricTraceZeroThreeCoordinates

/-!
# The polynomial sphere differential in the actual symmetric tangent model

The derivative is taken in the existing stereographic sphere chart. At a
diagonal image it maps into the real symmetric trace-zero model, and its
coordinate expression reconstructs the original matrix derivative exactly.
-/

noncomputable section

open scoped ContDiff Matrix.Norms.Elementwise

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary

open QuaternionicSymmetricMatrices RealSymmetricMixing

def sphereSymmetricChart (z : UnitSphere) (v : SphereCenteredCoordinates.Tangent z) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  (symmetricMap (SphereCenteredCoordinates.inverse z v)).val.val

theorem contDiff_sphereInverse_entry (z : UnitSphere) {n : ℕ∞ω} (r : Fin 3) :
    ContDiff ℝ n (fun v : SphereCenteredCoordinates.Tangent z ↦
      (SphereCenteredCoordinates.inverse z v).val r) :=
  (PiLp.proj 2 (fun _ : Fin 3 ↦ ℂ) r : EuclideanSpace ℂ (Fin 3) →L[ℝ] ℂ).contDiff.comp
    (SphereCenteredCoordinates.contDiff_inverse_val z)

theorem contDiff_sphereSymmetricChart (z : UnitSphere) {n : ℕ∞ω} :
    ContDiff ℝ n (sphereSymmetricChart z) := by
  apply contDiff_pi.mpr
  intro r
  apply contDiff_pi.mpr
  intro s
  exact contDiff_symmetricMap_entry (SphereCenteredCoordinates.inverse z)
    (contDiff_sphereInverse_entry z) r s

theorem hasDerivAt_sphereInverse_line_entry (z : UnitSphere)
    (v : SphereCenteredCoordinates.Tangent z) (r : Fin 3) :
    HasDerivAt (fun t : ℝ ↦ (SphereCenteredCoordinates.inverse z (t • v)).val r) (v.val r) 0 := by
  have he := (PiLp.proj 2 (fun _ : Fin 3 ↦ ℂ) r :
    EuclideanSpace ℂ (Fin 3) →L[ℝ] ℂ).hasFDerivAt.comp_hasDerivAt 0
      (SphereCenteredCoordinates.hasDerivAt_inverse_line z v)
  convert he using 1 <;> rfl

def sphereSymmetricDifferential (z : UnitSphere) :
    SphereCenteredCoordinates.Tangent z →L[ℝ] Matrix (Fin 3) (Fin 3) ℂ :=
  fderiv ℝ (sphereSymmetricChart z) 0

theorem sphereSymmetricDifferential_apply (z : UnitSphere)
    (v : SphereCenteredCoordinates.Tangent z) :
    sphereSymmetricDifferential z v = symmetricVariation z.val v.val := by
  have hf := (contDiff_sphereSymmetricChart z (n := 1)).differentiable (by decide)
  have hfd : HasFDerivAt (sphereSymmetricChart z) (sphereSymmetricDifferential z)
      ((0 : ℝ) • v) := by
    rw [zero_smul]
    convert (hf 0).hasFDerivAt using 1 <;> rfl
  have hl : HasDerivAt (fun t : ℝ ↦ sphereSymmetricChart z (t • v))
      (sphereSymmetricDifferential z v) 0 := by
    convert hfd.comp_hasDerivAt 0 ((hasDerivAt_id (0 : ℝ)).smul_const v) using 1 <;> try rfl
    simp only [one_smul]
    rfl
  apply Matrix.ext
  intro r s
  have he := hasDerivAt_symmetricMap_entry (fun t : ℝ ↦ SphereCenteredCoordinates.inverse z (t • v))
    v.val 0 (hasDerivAt_sphereInverse_line_entry z v) r s
  rw [zero_smul, SphereCenteredCoordinates.inverse_zero] at he
  exact (hasDerivAt_pi.mp (hasDerivAt_pi.mp hl r) s).unique he

theorem sphereSymmetricDifferential_curve_entry (z : UnitSphere)
    (v : SphereCenteredCoordinates.Tangent z) (r s : Fin 3) :
    HasDerivAt (fun t : ℝ ↦
      (symmetricMap (SphereCenteredCoordinates.inverse z (t • v))).val.val r s)
      (sphereSymmetricDifferential z v r s) 0 := by
  rw [sphereSymmetricDifferential_apply]
  have he := hasDerivAt_symmetricMap_entry (fun t : ℝ ↦ SphereCenteredCoordinates.inverse z (t • v))
    v.val 0 (hasDerivAt_sphereInverse_line_entry z v) r s
  simpa only [zero_smul, SphereCenteredCoordinates.inverse_zero] using he

theorem sphereDiagonal_coordinates_mem (z : UnitSphere) (q : Fin 3 → unitary ℂ)
    (hq : (symmetricMap z).val.val = Matrix.diagonal (fun r ↦ (q r).val ^ 2))
    (v : SphereCenteredCoordinates.Tangent z) :
    diagonalTangentCoordinates q (sphereSymmetricDifferential z v) ∈
      symmetricTraceZero (Fin 3) := by
  apply diagonal_curve_coordinates_mem q
    (fun t : ℝ ↦ symmetricMap (SphereCenteredCoordinates.inverse z (t • v)))
    (sphereSymmetricDifferential z v) 0 (sphereSymmetricDifferential_curve_entry z v)
    (by simpa only [zero_smul, SphereCenteredCoordinates.inverse_zero] using hq) 1
  intro t
  exact symmetricMap_det _

def sphereDiagonalDifferential (z : UnitSphere) (q : Fin 3 → unitary ℂ)
    (hq : (symmetricMap z).val.val = Matrix.diagonal (fun r ↦ (q r).val ^ 2)) :
    SphereCenteredCoordinates.Tangent z →ₗ[ℝ] DirectionSpace (Fin 3) :=
  LinearMap.codRestrict (symmetricTraceZero (Fin 3))
    ((diagonalTangentCoordinates q).comp (sphereSymmetricDifferential z).toLinearMap)
    (sphereDiagonal_coordinates_mem z q hq)

theorem sphereDiagonalDifferential_reconstruction (z : UnitSphere) (q : Fin 3 → unitary ℂ)
    (hq : (symmetricMap z).val.val = Matrix.diagonal (fun r ↦ (q r).val ^ 2))
    (v : SphereCenteredCoordinates.Tangent z) (r s : Fin 3) :
    sphereSymmetricDifferential z v r s =
      (q r).val * (Complex.I * ((sphereDiagonalDifferential z q hq v).val r s : ℂ)) * (q s).val :=
  diagonal_curve_reconstruction q
    (fun t : ℝ ↦ symmetricMap (SphereCenteredCoordinates.inverse z (t • v)))
    (sphereSymmetricDifferential z v) 0 (sphereSymmetricDifferential_curve_entry z v)
    (by simpa only [zero_smul, SphereCenteredCoordinates.inverse_zero] using hq) r s

theorem sphereDiagonalDifferential_injective (z : UnitSphere) (q : Fin 3 → unitary ℂ)
    (hq : (symmetricMap z).val.val = Matrix.diagonal (fun r ↦ (q r).val ^ 2))
    (hinj : Function.Injective (sphereSymmetricDifferential z)) :
    Function.Injective (sphereDiagonalDifferential z q hq) := by
  intro v w h
  apply hinj
  ext r s
  rw [sphereDiagonalDifferential_reconstruction z q hq v r s,
    sphereDiagonalDifferential_reconstruction z q hq w r s, h]

def sphereDiagonalDifferentialEquiv (z : UnitSphere) (q : Fin 3 → unitary ℂ)
    (hq : (symmetricMap z).val.val = Matrix.diagonal (fun r ↦ (q r).val ^ 2))
    (hinj : Function.Injective (sphereSymmetricDifferential z)) :
    SphereCenteredCoordinates.Tangent z ≃ₗ[ℝ] DirectionSpace (Fin 3) := by
  have hdim : Module.finrank ℝ (EuclideanSpace ℂ (Fin 3)) = 6 := by
    rw [(WithLp.linearEquiv 2 ℝ (Fin 3 → ℂ)).finrank_eq, Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex]
  let : Fact (Module.finrank ℝ (EuclideanSpace ℂ (Fin 3)) = 5 + 1) := ⟨hdim⟩
  exact (sphereDiagonalDifferential z q hq).linearEquivOfInjective
    (sphereDiagonalDifferential_injective z q hq hinj)
    (by rw [SphereCenteredCoordinates.tangent_finrank z (n := 5), directionSpace_three_finrank])

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary
