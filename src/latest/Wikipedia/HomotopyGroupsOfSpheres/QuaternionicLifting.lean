import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicAction
import Wikipedia.HopfProblem.OrbitPairLocalTransportLifting

/-!
# Homotopy lifting for `Sp(2) → S⁷`

The first-column projection admits continuous local transport. To move a
frame from `u` to a nearby vector `v`, first express `v` in the frame's
coordinates, use the section near the first standard basis vector, and
multiply the original frame by this correction. On the diagonal the
correction is exactly the identity.

The proved compact subdivision theorem then gives homotopy lifts with
prescribed initial lift, fixing every stationary parameter.
-/

noncomputable section

open scoped unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicFibration

open HopfProblem.OrbitPair

/-- The open neighborhood of the diagonal where the Hermitian pairing is nonzero. -/
def transportDomain : TopologicalSpace.Opens (BaseSphere × BaseSphere) :=
  ⟨{z | hermitianPairing z.1 z.2 ≠ 0}, isOpen_ne.preimage continuous_hermitianPairing⟩

theorem transportDomain_diagonal (v : BaseSphere) : (v, v) ∈ transportDomain := by
  change hermitianPairing v v ≠ 0
  rw [hermitianPairing_self]
  exact one_ne_zero

abbrev TransportInput := {z : SpTwo × BaseSphere // (projection z.1, z.2) ∈ transportDomain}

/-- Coordinates of the target vector in the original frame. -/
def transportChart (z : TransportInput) : firstChart :=
  ⟨sphereAction z.val.1⁻¹ z.val.2, by
    change (sphereAction z.val.1⁻¹ z.val.2).val.fst ≠ 0
    rw [sphereAction_inv_fst]
    exact z.property⟩

theorem continuous_transportChart : Continuous transportChart := by
  apply Continuous.subtype_mk
  exact continuous_sphereAction.comp
    (continuous_subtype_val.fst.inv.prodMk continuous_subtype_val.snd)

/-- Correct a frame to have the prescribed nearby first column. -/
def transport : C(TransportInput, SpTwo) :=
  ⟨fun z => z.val.1 * firstSection (transportChart z),
    continuous_subtype_val.fst.mul (continuous_firstSection.comp continuous_transportChart)⟩

theorem transport_projection (z : TransportInput) : projection (transport z) = z.val.2 := by
  change projection (z.val.1 * firstSection (transportChart z)) = z.val.2
  rw [← sphereAction_projection, projection_firstSection]
  exact sphereAction_inv_cancel _ _

theorem transport_self (A : SpTwo) :
    transport ⟨(A, projection A), transportDomain_diagonal (projection A)⟩ = A := by
  have h : transportChart ⟨(A, projection A), transportDomain_diagonal (projection A)⟩ =
      ⟨north, north_mem_firstChart⟩ := by
    apply Subtype.ext
    exact sphereAction_inv_projection A
  change A * firstSection (transportChart _) = A
  rw [h, firstSection_north, mul_one]

/-- Local transport on the original quaternionic matrix projection. -/
def localTransport : LocalTransport projection where
  domain := transportDomain
  diagonal := transportDomain_diagonal
  transport := transport
  project := transport_projection
  self := transport_self

/-- Compact homotopies lift, preserving their initial lift and all stationary parameters. -/
theorem exists_homotopy_lift {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (H : C(I × X, BaseSphere)) (a₀ : C(X, SpTwo))
    (ha₀ : ∀ x, projection (a₀ x) = H (0, x)) :
    ∃ L : C(I × X, SpTwo), (∀ x, L (0, x) = a₀ x) ∧
      (∀ t x, projection (L (t, x)) = H (t, x)) ∧
      ∀ x, (∀ t, H (t, x) = H (0, x)) → ∀ t, L (t, x) = a₀ x :=
  localTransport.exists_lift_stationary H a₀ ha₀

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicFibration
