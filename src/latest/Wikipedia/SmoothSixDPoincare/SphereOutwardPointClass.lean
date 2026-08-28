import Wikipedia.SmoothSixDPoincare.SphereChartTransportSign
import Wikipedia.SmoothSixDPoincare.SpherePointClassTransport
import Wikipedia.SmoothSixDPoincare.SpherePointConnecting

/-!
# Point classes agree with the fixed outward sphere convention

The actual one-point connecting class, multiplied by its native chart's
outward sign, is independent of both the point and its auxiliary chart ball.
It is an actual homology isomorphism, not a postulated orientation class.
-/

noncomputable section

open Set Metric ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.SpherePoint

open Wikipedia.HopfProblem.SphereHomology
  Wikipedia.HopfProblem.SingularMayerVietoris SphereNormalCoordinates

local instance (n : ℕ) :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 3))) = (n + 2) + 1) := ⟨by simp⟩

variable (n : ℕ) {F G H : Type}
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  (j : (ℝ × H) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 3)))
  (B : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] H)
  (x y : UnitSphere (n + 2)) {fx : UnitSphere (n + 2) → F} {fy : UnitSphere (n + 2) → G}
  {Lx : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] F}
  {Ly : EuclideanSpace ℝ (Fin (n + 2)) ≃L[ℝ] G} {Wx Wy : Set (UnitSphere (n + 2))}
  (dx : LocalDegree.NeighborhoodData (fx ∘ NativeParametrization.centered x) Lx
    ((NativeParametrization.centered x).source ∩ NativeParametrization.centered x ⁻¹' Wx))
  (dy : LocalDegree.NeighborhoodData (fy ∘ NativeParametrization.centered y) Ly
    ((NativeParametrization.centered y).source ∩ NativeParametrization.centered y ⁻¹' Wy))

def outwardPointClass (k : ℕ) :
    SingularHomology (UnitSphere (n + 2)) (k + 2) →ₗ[ℤ]
      SingularHomology (UnitSphere (n + 1)) (k + 1) :=
  (SignType.sign (chartJacobian (NativeParametrization.centered x) j B 0) : ℤ) •
    LocalDegree.NativeNeighborhood.sphereConnecting x dx (k + 1)

theorem outwardPointClass_eq (k : ℕ) :
    outwardPointClass n j B y dy k = outwardPointClass n j B x dx k := by
  have hs := chartJacobian_transport_sign x y (positiveTransport (n + 1) x y)
    (positiveTransport_moves (n + 1) x y) (positiveTransport_det (n + 1) x y) j B
  have hs' : SignType.sign (chartJacobian (NativeParametrization.centered y) j B 0) *
      SignType.sign (pointChartLinear n x y).toLinearEquiv.toLinearMap.det =
      SignType.sign (chartJacobian (NativeParametrization.centered x) j B 0) := hs
  apply LinearMap.ext
  intro a
  change (SignType.sign (chartJacobian (NativeParametrization.centered y) j B 0) : ℤ) •
    LocalDegree.NativeNeighborhood.sphereConnecting y dy (k + 1) a = _
  rw [pointClass_sign_compare n x y dx dy k a, smul_smul, ← SignType.coe_mul, hs']
  rfl

theorem chartSign_mul_self :
    (SignType.sign (chartJacobian (NativeParametrization.centered x) j B 0) : ℤ) *
      (SignType.sign (chartJacobian (NativeParametrization.centered x) j B 0) : ℤ) = 1 := by
  have hn := chartJacobian_ne_zero (NativeParametrization.centered x) j B
    (NativeParametrization.zero_mem_centered_source x)
  have hs : SignType.sign (chartJacobian (NativeParametrization.centered x) j B 0) *
      SignType.sign (chartJacobian (NativeParametrization.centered x) j B 0) = 1 := by
    rw [← sign_mul]
    exact sign_eq_one_iff.mpr (mul_self_pos.mpr hn)
  simpa only [SignType.coe_mul, SignType.coe_one] using
    congrArg (fun s : SignType => (s : ℤ)) hs

theorem connecting_eq_sign_outward (k : ℕ)
    (a : SingularHomology (UnitSphere (n + 2)) (k + 2)) :
    LocalDegree.NativeNeighborhood.sphereConnecting x dx (k + 1) a =
      (SignType.sign (chartJacobian (NativeParametrization.centered x) j B 0) : ℤ) •
        outwardPointClass n j B x dx k a := by
  change _ = (SignType.sign (chartJacobian (NativeParametrization.centered x) j B 0) : ℤ) •
    ((SignType.sign (chartJacobian (NativeParametrization.centered x) j B 0) : ℤ) •
      LocalDegree.NativeNeighborhood.sphereConnecting x dx (k + 1) a)
  rw [smul_smul, chartSign_mul_self n j B x, one_smul]

def outwardPointClassEquiv (k : ℕ) :
    SingularHomology (UnitSphere (n + 2)) (k + 2) ≃ₗ[ℤ]
      SingularHomology (UnitSphere (n + 1)) (k + 1) := by
  let C := connectingHomologyEquiv x dx k
  let s : ℤ := SignType.sign (chartJacobian (NativeParametrization.centered x) j B 0)
  have hs : s * s = 1 := chartSign_mul_self n j B x
  refine LinearEquiv.ofBijective (outwardPointClass n j B x dx k) ⟨?_, ?_⟩
  · intro a b hab
    apply C.injective
    have h := congrArg (fun z => s • z) hab
    change s • (s • C a) = s • (s • C b) at h
    simpa only [smul_smul, hs, one_smul] using h
  · intro b
    refine ⟨C.symm (s • b), ?_⟩
    change s • C (C.symm (s • b)) = b
    rw [C.apply_symm_apply, smul_smul, hs, one_smul]

theorem outwardPointClassEquiv_apply (k : ℕ)
    (a : SingularHomology (UnitSphere (n + 2)) (k + 2)) :
    outwardPointClassEquiv n j B x dx k a = outwardPointClass n j B x dx k a := rfl

end Wikipedia.SmoothSixDPoincare.SpherePoint
