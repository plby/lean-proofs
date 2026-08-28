import Wikipedia.HomotopyGroupsOfSpheres.RankSixSpinorFiber
import Wikipedia.HopfProblem.OrbitPairLocalTransportLifting

/-!
# Stationary compact homotopy lifting for the spinor map

Projection intertwiners and normalization transport a unit spinor to the
new line. The open domain also requires agreement of the Pfaffian signs,
so the recovered complex structure is the original target, not its negative.
-/

noncomputable section

open scoped unitInterval

namespace NoExoticSixSphere.RankSixComplexProjection.SpinorFibration

open RankSixSkewMatrix Wikipedia.HopfProblem.OrbitPair

def pairIntertwiner (z : OrthogonalComplexStructures.Space 6 ×
    OrthogonalComplexStructures.Space 6) : Spinor →L[ℝ] Spinor :=
  projectionIntertwiner (realProjection z.1) (realProjection z.2)

theorem continuous_pairIntertwiner : Continuous pairIntertwiner :=
  ((continuous_realProjection.comp continuous_snd).clm_comp
    (continuous_realProjection.comp continuous_fst)).add
    ((continuous_const.sub (continuous_realProjection.comp continuous_snd)).clm_comp
      (continuous_const.sub (continuous_realProjection.comp continuous_fst)))

def transportDomain : TopologicalSpace.Opens (OrthogonalComplexStructures.Space 6 ×
    OrthogonalComplexStructures.Space 6) :=
  ⟨{z | (pairIntertwiner z).IsInvertible ∧
    0 < pfaffian (matrix z.1) * pfaffian (matrix z.2)},
    (ContinuousLinearEquiv.isOpen.preimage continuous_pairIntertwiner).inter
      (isOpen_lt continuous_const
        ((continuous_pfaffian.comp (continuous_matrix.comp continuous_fst)).mul
          (continuous_pfaffian.comp (continuous_matrix.comp continuous_snd))))⟩

theorem transportDomain_diagonal (J : OrthogonalComplexStructures.Space 6) :
    (J, J) ∈ transportDomain := by
  constructor
  · change (projectionIntertwiner (realProjection J) (realProjection J)).IsInvertible
    rw [projectionIntertwiner_self _ (realProjection_idempotent J)]
    exact ⟨ContinuousLinearEquiv.refl ℝ Spinor, rfl⟩
  · change 0 < pfaffian (matrix J) * pfaffian (matrix J)
    rw [← pow_two, pfaffian_sq_one _ (matrix_transpose J) (matrix_square J)]
    norm_num

abbrev TransportInput :=
  {z : UnitSpinor × OrthogonalComplexStructures.Space 6 // (fromSpinor z.1, z.2) ∈ transportDomain}

def rawTransport (z : TransportInput) : Spinor :=
  pairIntertwiner (fromSpinor z.val.1, z.val.2) z.val.1.val

theorem rawTransport_ne_zero (z : TransportInput) : rawTransport z ≠ 0 := by
  intro h
  apply unitSpinor_ne_zero z.val.1
  apply z.property.1.injective
  exact h.trans (map_zero _).symm

theorem continuous_rawTransport : Continuous rawTransport :=
  (continuous_pairIntertwiner.comp
    ((continuous_fromSpinor.comp continuous_subtype_val.fst).prodMk
      continuous_subtype_val.snd)).clm_apply
    (continuous_subtype_val.comp continuous_subtype_val.fst)

theorem rawTransport_fixed (z : TransportInput) :
    projection z.val.2 (rawTransport z) = rawTransport z := by
  have h := congrArg (fun T : Spinor →L[ℝ] Spinor ↦ T z.val.1.val)
    (projectionIntertwiner_intertwines (realProjection (fromSpinor z.val.1))
      (realProjection z.val.2) (realProjection_idempotent _) (realProjection_idempotent _))
  change projection z.val.2 (rawTransport z) =
    pairIntertwiner (fromSpinor z.val.1, z.val.2)
      (projection (fromSpinor z.val.1) z.val.1) at h
  rw [projection_fromSpinor_fixed] at h
  exact h

theorem target_pfaffian (z : TransportInput) : pfaffian (matrix z.val.2) = -1 := by
  have hs := z.property.2
  change 0 < pfaffian (matrix (fromSpinor z.val.1)) * pfaffian (matrix z.val.2) at hs
  rw [pfaffian_fromSpinor] at hs
  rcases sq_eq_one_iff.mp
    (pfaffian_sq_one _ (matrix_transpose z.val.2) (matrix_square z.val.2)) with h | h
  · rw [h] at hs
    norm_num at hs
  · exact h

def transport : C(TransportInput, UnitSpinor) where
  toFun z := ⟨NormedSpace.normalize (rawTransport z), by
    simpa only [Metric.mem_sphere, dist_zero_right] using
      NormedSpace.norm_normalize (rawTransport_ne_zero z)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_rawTransport.norm.inv₀
      (fun z ↦ norm_ne_zero_iff.mpr (rawTransport_ne_zero z))).smul continuous_rawTransport

theorem transport_fixed (z : TransportInput) : projection z.val.2 (transport z) =
    (transport z : Spinor) := by
  change realProjection z.val.2 (‖rawTransport z‖⁻¹ • rawTransport z) =
    ‖rawTransport z‖⁻¹ • rawTransport z
  rw [map_smul]
  exact congrArg (fun v : Spinor ↦ ‖rawTransport z‖⁻¹ • v) (rawTransport_fixed z)

theorem transport_project (z : TransportInput) : fromSpinor (transport z) = z.val.2 :=
  fromSpinor_eq_of_fixed z.val.2 (target_pfaffian z) (transport z) (transport_fixed z)

theorem transport_self (q : UnitSpinor) :
    transport ⟨(q, fromSpinor q), transportDomain_diagonal (fromSpinor q)⟩ = q := by
  apply Subtype.ext
  change NormedSpace.normalize
    (rawTransport ⟨(q, fromSpinor q), transportDomain_diagonal (fromSpinor q)⟩) = (q : Spinor)
  have hr : rawTransport ⟨(q, fromSpinor q), transportDomain_diagonal (fromSpinor q)⟩ =
      (q : Spinor) := by
    change projectionIntertwiner (realProjection (fromSpinor q))
      (realProjection (fromSpinor q)) (q : Spinor) = (q : Spinor)
    rw [projectionIntertwiner_self _ (realProjection_idempotent _)]
    rfl
  rw [hr]
  exact NormedSpace.normalize_eq_self_of_norm_eq_one (unitSpinor_norm q)

def localTransport : LocalTransport fromSpinor where
  domain := transportDomain
  diagonal := transportDomain_diagonal
  transport := transport
  project := transport_project
  self := transport_self

theorem exists_homotopy_lift {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (H : C(I × X, OrthogonalComplexStructures.Space 6)) (a₀ : C(X, UnitSpinor))
    (ha₀ : ∀ x, fromSpinor (a₀ x) = H (0, x)) :
    ∃ L : C(I × X, UnitSpinor), (∀ x, L (0, x) = a₀ x) ∧
      (∀ t x, fromSpinor (L (t, x)) = H (t, x)) ∧
      ∀ x, (∀ t, H (t, x) = H (0, x)) → ∀ t, L (t, x) = a₀ x :=
  localTransport.exists_lift_stationary H a₀ ha₀

end NoExoticSixSphere.RankSixComplexProjection.SpinorFibration
