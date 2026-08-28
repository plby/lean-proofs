import Wikipedia.HomotopyGroupsOfSpheres.BalancedFrameFiber
import Wikipedia.HomotopyGroupsOfSpheres.FrameOrthonormalization
import Wikipedia.NoExoticSixSphere.ProjectionTransport
import Wikipedia.HopfProblem.OrbitPairLocalTransportLifting

/-!
# Stationary homotopy lifting for the balanced frame projection

Invertible projection intertwiners carry a frame into the new range.
Rectangular Gram--Schmidt makes it orthonormal, continuously and without
changing that range. On the diagonal both steps fix the original frame.
Compact subdivision then gives stationary homotopy lifting.
-/

noncomputable section

open scoped unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.BalancedRealInvolutions.FrameProjection

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization HopfProblem.OrbitPair

variable {n : ℕ}

def pairIntertwiner (z : Space n × Space n) : Vector (n + n) →L[ℝ] Vector (n + n) :=
  projectionIntertwiner (positiveProjection z.1) (positiveProjection z.2)

theorem continuous_pairIntertwiner (n : ℕ) : Continuous (pairIntertwiner (n := n)) :=
  ((continuous_positiveProjection n).comp continuous_snd).clm_comp
      ((continuous_positiveProjection n).comp continuous_fst) |>.add
    ((continuous_const.sub ((continuous_positiveProjection n).comp continuous_snd)).clm_comp
      (continuous_const.sub ((continuous_positiveProjection n).comp continuous_fst)))

def transportDomain (n : ℕ) : TopologicalSpace.Opens (Space n × Space n) :=
  ⟨{z | (pairIntertwiner z).IsInvertible},
    ContinuousLinearEquiv.isOpen.preimage (continuous_pairIntertwiner n)⟩

theorem transportDomain_diagonal (J : Space n) : (J, J) ∈ transportDomain n := by
  change (projectionIntertwiner (positiveProjection J) (positiveProjection J)).IsInvertible
  rw [projectionIntertwiner_self _ (positiveProjection_idempotent J)]
  exact ⟨ContinuousLinearEquiv.refl ℝ (Vector (n + n)), rfl⟩

abbrev TransportInput (n : ℕ) :=
  {z : Stiefel.Space (n + n) n × Space n // (toBalanced z.1, z.2) ∈ transportDomain n}

def rawTransport (z : TransportInput n) : Vector n →L[ℝ] Vector (n + n) :=
  (pairIntertwiner (toBalanced z.val.1, z.val.2)).comp z.val.1.val

theorem rawTransport_injective (z : TransportInput n) : Function.Injective (rawTransport z) :=
  z.property.injective.comp (Stiefel.injective z.val.1)

theorem continuous_rawTransport (n : ℕ) : Continuous (rawTransport (n := n)) :=
  ((continuous_pairIntertwiner n).comp
    (((continuous_toBalanced n).comp continuous_subtype_val.fst).prodMk
      continuous_subtype_val.snd)).clm_comp
    (continuous_subtype_val.comp continuous_subtype_val.fst)

theorem rawTransport_range (z : TransportInput n) :
    (rawTransport z).range = (positiveProjection z.val.2).range := by
  change ((pairIntertwiner (toBalanced z.val.1, z.val.2)).toLinearMap.comp
    z.val.1.val.toLinearMap).range = _
  rw [LinearMap.range_comp, ← operator_range z.val.1, ← positiveProjection_toBalanced]
  exact projectionIntertwiner_map_range _ _ (positiveProjection_idempotent _)
    (positiveProjection_idempotent _) z.property

def transport (n : ℕ) : C(TransportInput n, Stiefel.Space (n + n) n) :=
  Stiefel.Orthonormalization.map rawTransport rawTransport_injective (continuous_rawTransport n)

theorem transport_range (z : TransportInput n) :
    (transport n z).val.range = (positiveProjection z.val.2).range :=
  (Stiefel.Orthonormalization.frame_range rawTransport rawTransport_injective z).trans
    (rawTransport_range z)

theorem transport_project (z : TransportInput n) : toBalanced (transport n z) = z.val.2 := by
  apply (projectionHomeomorph n).injective
  apply projection_eq_of_range
  change (positiveProjection (toBalanced (transport n z))).range =
    (positiveProjection z.val.2).range
  rw [positiveProjection_toBalanced, operator_range]
  exact transport_range z

theorem transport_self (A : Stiefel.Space (n + n) n) :
    transport n ⟨(A, toBalanced A), transportDomain_diagonal (toBalanced A)⟩ = A := by
  apply Stiefel.Orthonormalization.frame_eq_of_frame rawTransport rawTransport_injective _ A
  change (projectionIntertwiner (positiveProjection (toBalanced A))
    (positiveProjection (toBalanced A))).comp A.val = A.val
  rw [projectionIntertwiner_self _ (positiveProjection_idempotent _),
    ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp]

def localTransport (n : ℕ) : LocalTransport (toBalanced (n := n)) where
  domain := transportDomain n
  diagonal := transportDomain_diagonal
  transport := transport n
  project := transport_project
  self := transport_self

/-- Compact homotopies lift while fixing every stationary parameter. -/
theorem exists_homotopy_lift {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (H : C(I × X, Space n)) (a₀ : C(X, Stiefel.Space (n + n) n))
    (ha₀ : ∀ x, toBalanced (a₀ x) = H (0, x)) :
    ∃ L : C(I × X, Stiefel.Space (n + n) n), (∀ x, L (0, x) = a₀ x) ∧
      (∀ t x, toBalanced (L (t, x)) = H (t, x)) ∧
      ∀ x, (∀ t, H (t, x) = H (0, x)) → ∀ t, L (t, x) = a₀ x :=
  (localTransport n).exists_lift_stationary H a₀ ha₀

end Wikipedia.HomotopyGroupsOfSpheres.BalancedRealInvolutions.FrameProjection
