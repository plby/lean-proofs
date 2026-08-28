import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumnAction
import Wikipedia.HopfProblem.OrbitPairLocalTransportLifting

/-! # Stationary compact homotopy lifting for quaternionic column projections -/

noncomputable section

open scoped unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns

open QuaternionicRankOne HopfProblem.OrbitPair

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- Local transport is defined wherever the Hermitian pairing is not `-1`. -/
def transportDomain : TopologicalSpace.Opens (UnitColumn N × UnitColumn N) :=
  ⟨{z | pairing z.1.val z.2.val ≠ -1}, isOpen_ne.preimage continuous_pairing⟩

omit [DecidableEq N] in
theorem transportDomain_diagonal (v : UnitColumn N) :
    (v, v) ∈ transportDomain := by
  change pairing v.val v.val ≠ -1
  rw [v.property]
  intro h
  have hr := congrArg (fun q : Quaternion ℝ => q.re) h
  change (1 : ℝ) = -1 at hr
  norm_num at hr

abbrev TransportInput (j : N) :=
  {z : SpGroup N × UnitColumn N // (column j z.1, z.2) ∈ transportDomain}

def transportChart (j : N) (z : TransportInput j) : columnChart j :=
  ⟨action j z.val.1⁻¹ z.val.2, by
    change (action j z.val.1⁻¹ z.val.2).val j ≠ -1
    rw [action_inv_coordinate]
    exact z.property⟩

theorem continuous_transportChart (j : N) : Continuous (transportChart j) := by
  have hA : Continuous (fun z : TransportInput j => z.val.1.val) :=
    continuous_subtype_val.comp continuous_subtype_val.fst
  have hv : Continuous (fun z : TransportInput j => z.val.2.val) :=
    continuous_subtype_val.comp continuous_subtype_val.snd
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  change Continuous (fun z : TransportInput j => ∑ k, star (z.val.1.val k i) * z.val.2.val k)
  apply continuous_finsetSum
  intro k _
  exact (hA.matrix_elem k i).star.mul ((continuous_apply k).comp hv)

/-- Correct the old frame by the continuous section in its own coordinates. -/
def transport (j : N) : C(TransportInput j, SpGroup N) :=
  ⟨fun z => z.val.1 * sectionMap j (transportChart j z),
    continuous_subtype_val.fst.mul ((continuous_sectionMap j).comp (continuous_transportChart j))⟩

theorem transport_column (j : N) (z : TransportInput j) :
    column j (transport j z) = z.val.2 := by
  change column j (z.val.1 * sectionMap j (transportChart j z)) = z.val.2
  rw [← action_column, column_sectionMap]
  exact action_inv_cancel j _ _

theorem transport_self (j : N) (A : SpGroup N) :
    transport j ⟨(A, column j A), transportDomain_diagonal (column j A)⟩ = A := by
  have h : transportChart j ⟨(A, column j A), transportDomain_diagonal (column j A)⟩ =
      ⟨axisColumn j, axisColumn_mem_chart j⟩ := by
    apply Subtype.ext
    exact action_inv_column j A
  change A * sectionMap j (transportChart j _) = A
  rw [h, sectionMap_axis, mul_one]

def localTransport (j : N) : LocalTransport (column j) where
  domain := transportDomain
  diagonal := transportDomain_diagonal
  transport := transport j
  project := transport_column j
  self := transport_self j

/-- Compact homotopies lift with their specified initial lift and stationary parameters. -/
theorem exists_homotopy_lift (j : N) {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (H : C(I × X, UnitColumn N)) (a₀ : C(X, SpGroup N))
    (ha₀ : ∀ x, column j (a₀ x) = H (0, x)) :
    ∃ L : C(I × X, SpGroup N), (∀ x, L (0, x) = a₀ x) ∧
      (∀ t x, column j (L (t, x)) = H (t, x)) ∧
      ∀ x, (∀ t, H (t, x) = H (0, x)) → ∀ t, L (t, x) = a₀ x :=
  (localTransport j).exists_lift_stationary H a₀ ha₀

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns
