import Wikipedia.NoExoticSixSphere.QuaternionicHopfProjectionOperator
import Wikipedia.HopfProblem.OrbitPairLocalTransportLifting

/-!
# Compact homotopy lifting for the literal quaternionic Hopf polynomial

For nearby target points, project a source vector onto the new quaternionic
line and normalize it. Operator-norm closeness ensures this vector is nonzero.
On the diagonal this construction fixes the source vector exactly.
-/

noncomputable section

open scoped Quaternion unitInterval

namespace NoExoticSixSphere.QuaternionicHopf

def transportDomain : TopologicalSpace.Opens (Sphere 4 × Sphere 4) :=
  ⟨{z | ‖projectionOperator z.2.val - projectionOperator z.1.val‖ < 1},
    isOpen_lt (((continuous_projectionOperator.comp
      (continuous_subtype_val.comp continuous_snd)).sub
        (continuous_projectionOperator.comp
          (continuous_subtype_val.comp continuous_fst))).norm) continuous_const⟩

theorem transportDomain_diagonal (y : Sphere 4) : (y, y) ∈ transportDomain := by
  change ‖projectionOperator y.val - projectionOperator y.val‖ < 1
  simp only [sub_self, norm_zero, zero_lt_one]

abbrev TransportInput :=
  {z : Sphere 7 × Sphere 4 // (sphereMap z.1, z.2) ∈ transportDomain}

def transportVector : C(TransportInput, V 8) :=
  ⟨fun z ↦ projectionOperator z.val.2.val z.val.1.val,
    (continuous_projectionOperator.comp
      (continuous_subtype_val.comp continuous_subtype_val.snd)).clm_apply
        (continuous_subtype_val.comp continuous_subtype_val.fst)⟩

theorem transportVector_ne_zero (z : TransportInput) : transportVector z ≠ 0 := by
  intro hz
  have hn := (projectionOperator z.val.2.val -
    projectionOperator (sphereMap z.val.1).val).le_opNorm z.val.1.val
  rw [sub_apply] at hn
  change projectionOperator z.val.2.val z.val.1.val = 0 at hz
  rw [hz, projectionOperator_self, zero_sub, norm_neg, norm_smul,
    mem_sphere_zero_iff_norm.mp z.val.1.property, mul_one, mul_one] at hn
  have hc := z.property
  change ‖projectionOperator z.val.2.val - projectionOperator (sphereMap z.val.1).val‖ < 1 at hc
  norm_num at hn
  linarith

def transport : C(TransportInput, Sphere 7) :=
  normalizedSphereMap transportVector transportVector_ne_zero

theorem transport_project (z : TransportInput) : sphereMap (transport z) = z.val.2 := by
  apply polynomial_of_eigen
  · change (1 - z.val.2.val 0) • first (‖transportVector z‖⁻¹ • transportVector z) =
      tailQuaternion z.val.2.val * second (‖transportVector z‖⁻¹ • transportVector z)
    rw [map_smul, map_smul, smul_comm, mul_smul_comm]
    congr 1
    exact projectionOperator_image_first z.val.2 z.val.1.val
  · change (1 + z.val.2.val 0) • second (‖transportVector z‖⁻¹ • transportVector z) =
      star (tailQuaternion z.val.2.val) * first (‖transportVector z‖⁻¹ • transportVector z)
    rw [map_smul, map_smul, smul_comm, mul_smul_comm]
    congr 1
    exact projectionOperator_image_second z.val.2 z.val.1.val

theorem transport_self (x : Sphere 7) :
    transport ⟨(x, sphereMap x), transportDomain_diagonal (sphereMap x)⟩ = x := by
  apply Subtype.ext
  change NormedSpace.normalize (projectionOperator (sphereMap x).val x.val) = x.val
  rw [projectionOperator_self]
  change ‖(2 : ℝ) • x.val‖⁻¹ • ((2 : ℝ) • x.val) = x.val
  rw [norm_smul, mem_sphere_zero_iff_norm.mp x.property, mul_one, smul_smul]
  norm_num

def localTransport : Wikipedia.HopfProblem.OrbitPair.LocalTransport sphereMap where
  domain := transportDomain
  diagonal := transportDomain_diagonal
  transport := transport
  project := transport_project
  self := transport_self

theorem exists_homotopy_lift {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (H : C(I × X, Sphere 4)) (a₀ : C(X, Sphere 7))
    (ha₀ : ∀ x, sphereMap (a₀ x) = H (0, x)) :
    ∃ L : C(I × X, Sphere 7), (∀ x, L (0, x) = a₀ x) ∧
      (∀ t x, sphereMap (L (t, x)) = H (t, x)) ∧
      ∀ x, (∀ t, H (t, x) = H (0, x)) → ∀ t, L (t, x) = a₀ x :=
  localTransport.exists_lift_stationary H a₀ ha₀

end NoExoticSixSphere.QuaternionicHopf
