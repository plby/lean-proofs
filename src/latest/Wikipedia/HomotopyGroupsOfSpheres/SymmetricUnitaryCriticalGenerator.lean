import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryStationaryPolygon
import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitaryAntipodalMinimum
import Wikipedia.HomotopyGroupsOfSpheres.BalancedRotationPaths

/-!
# The real symmetric trace-zero generator of a critical identity-based polygon

At the identity, reversibility is ordinary transpose symmetry. Taking
entrywise imaginary parts recovers the exact real generator used in the
antipodal spectral and negative-variation theorems.
-/

noncomputable section

open scoped Matrix.Norms.Frobenius
open Set

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices

open RealSymmetricMixing ImaginarySymmetricMatrices ComplexMatrixRealRepresentation

variable {N : Type*} [Fintype N] [DecidableEq N]

theorem identityDirection_transpose (K : ReversibleDirection (specialIdentity (N := N))) :
    K.val.val.transpose = K.val.val := by
  have h := K.property.2
  change K.val.val.transpose * 1 = 1 * K.val.val at h
  simpa only [mul_one, one_mul] using h

def identityRealDirection (K : ReversibleDirection (specialIdentity (N := N))) :
    DirectionSpace N :=
  ⟨K.val.val.map Complex.im, map_im_transpose _ (identityDirection_transpose K), by
    have ht := congrArg Complex.im K.property.1
    simpa only [Matrix.trace, Matrix.diag, Matrix.map_apply, Complex.im_sum, Complex.zero_im]
      using ht⟩

theorem imaginary_identityRealDirection (K : ReversibleDirection (specialIdentity (N := N))) :
    imaginary (identityRealDirection K).val = K.val.val :=
  imaginary_map_im _ (identityDirection_transpose K) K.val.property

theorem reversibleStep_identity (K : ReversibleDirection (specialIdentity (N := N))) (t : ℝ) :
    reversibleStep specialIdentity K.val K.property.1 K.property.2 t =
      exponentialCurve (identityRealDirection K) t := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  change (1 : Matrix N N ℂ) * NormedSpace.exp (t • K.val.val) =
    NormedSpace.exp (imaginary (t • (identityRealDirection K).val))
  rw [one_mul, map_smul, imaginary_identityRealDirection]

namespace Polygon

open VertexSpace

variable {m : ℕ}

theorem critical_identity_is_exponential (b : SpecialSpace N) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (v : VertexSpace.Space N m) (hv : v ∈ admissible specialIdentity b m)
    (hcrit : fderiv ℝ (localEnergy specialIdentity b τ v) 0 = 0) :
    ∃ A : DirectionSpace N, exponential A = b ∧
      ∀ t ∈ Icc (0 : ℝ) 1, path specialIdentity b τ hτ v hv t = exponentialCurve A t := by
  obtain ⟨K, hend, hpath⟩ := critical_is_exponential specialIdentity b τ hτ v hv hcrit
  simp only [hzero, hone, sub_zero, reversibleStep_identity] at hend hpath
  refine ⟨identityRealDirection K, ?_, hpath⟩
  simpa only [exponentialCurve, one_smul] using hend

theorem energy_eq_squareNorm_of_exponential (b : SpecialSpace N) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (v : VertexSpace.Space N m) (hv : v ∈ admissible specialIdentity b m)
    (A : DirectionSpace N)
    (hpath : ∀ t ∈ Icc (0 : ℝ) 1,
      path specialIdentity b τ hτ v hv t = exponentialCurve A t) :
    energy specialIdentity b τ v = 2 * RealMatrixSquareNorm.squareNorm A.val := by
  have he := path_energy_eq specialIdentity b τ hτ v hv
  rw [hzero, hone] at he
  have hc : NoExoticSixSphere.OrthogonalPathEnergy.energy
      (fun t ↦ action (path specialIdentity b τ hτ v hv t).val.val.val) 0 1 =
      NoExoticSixSphere.OrthogonalPathEnergy.energy
        (fun t ↦ (NoExoticSixSphere.OrthogonalExponential.exp (t • skewMap A)).val.val) 0 1 := by
    apply NoExoticSixSphere.OrthogonalPathEnergy.energy_congr_Icc zero_le_one
    intro t ht
    change action (path specialIdentity b τ hτ v hv t).val.val.val =
      (NoExoticSixSphere.OrthogonalExponential.exp (t • skewMap A)).val.val
    rw [hpath t ht]
    exact congrArg (fun Q ↦ Q.val.val) (specialOrthogonal_curve A t)
  have hcalc := NoExoticSixSphere.OrthogonalPathEnergy.energy_left_exp 1 (skewMap A) 0 1
  simp only [one_mul, sub_zero] at hcalc
  have hn : NoExoticSixSphere.HilbertSchmidt.squareNorm (skewMap A).val =
      2 * RealMatrixSquareNorm.squareNorm A.val := by
    rw [skewMap_coe, squareNorm_action, squareNorm_imaginary]
  exact he.symm.trans (hc.trans (hcalc.trans hn))

theorem critical_antipodal_generator (n : ℕ) (τ : Fin (m + 2) → ℝ)
    (hτ : StrictMono τ) (hzero : τ 0 = 0) (hone : τ (Fin.last (m + 1)) = 1)
    (v : VertexSpace.Space (BalancedRealInvolutions.Index n) m)
    (hv : v ∈ admissible specialIdentity (BalancedRealInvolutions.antipode n) m)
    (hcrit : fderiv ℝ (localEnergy specialIdentity (BalancedRealInvolutions.antipode n) τ v) 0 = 0)
    (habove : (4 * n : ℝ) * Real.pi ^ 2 <
      energy specialIdentity (BalancedRealInvolutions.antipode n) τ v) :
    ∃ A : DirectionSpace (BalancedRealInvolutions.Index n),
      NormedSpace.exp (imaginary A.val) = -1 ∧
      A.val * A.val ≠ Real.pi ^ 2 • (1 : Matrix _ _ ℝ) ∧
      ∀ t ∈ Icc (0 : ℝ) 1,
        path specialIdentity (BalancedRealInvolutions.antipode n) τ hτ v hv t =
          exponentialCurve A t := by
  obtain ⟨A, hend, hpath⟩ := critical_identity_is_exponential
    (BalancedRealInvolutions.antipode n) τ hτ hzero hone v hv hcrit
  have hexp : NormedSpace.exp (imaginary A.val) = -1 :=
    (congrArg (fun B : SpecialSpace (BalancedRealInvolutions.Index n) ↦ B.val.val.val) hend).trans
      (BalancedRealInvolutions.antipode_matrix n)
  refine ⟨A, hexp, ?_, hpath⟩
  intro hsq
  have he := energy_eq_squareNorm_of_exponential
    (BalancedRealInvolutions.antipode n) τ hτ hzero hone v hv A hpath
  have hn := (antipodal_squareNorm_eq_iff A.val A.property.1 hexp).mpr hsq
  have hcard : (Fintype.card (BalancedRealInvolutions.Index n) : ℝ) = 2 * n := by
    simp [BalancedRealInvolutions.Index, two_mul]
  rw [hn, hcard] at he
  rw [he] at habove
  nlinarith only [habove]

end Polygon
end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices
