import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionFixedRegularBasic
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldVerticalActionEllipticSpecial

/-!
# No total-action fixed points in the actual elliptic fillings

The genuine finite-affine quotient, including its central fibre, is a
local homeomorphism.  Composing it with the original period-vector
cover rules out an orbit fixed at every complex time: such an orbit
would lift to a constant vector translation.  The result restricts to
the existing small elliptic pieces by their literal subtype inclusions.
It does not assert that every nonintegral time has no fixed points.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.Elliptic

open Wikipedia.HopfProblem.Elliptic EllipticFilling

variable {j : Kind} (D : Equivariant.Data j)

/-- The actual full root-and-vector cover is locally homeomorphic even
over root zero, because the genuine affine cyclic action is free. -/
theorem vectorCover_isLocalHomeomorph (v : Lattice) (hv : AdmissibleTwist j v) :
    IsLocalHomeomorph (D.quotient v hv ∘ D.periods.quotientMap) :=
  (D.quotient_isLocalHomeomorph v hv).comp D.periods.quotientMap_localHomeomorph

/-- No point of the actual finite-affine filling quotient is fixed by
all complex translations, with no exception for the central fibre. -/
theorem not_forall_flow_eq_self (v : Lattice) (hv : AdmissibleTwist j v)
    (x : D.Space v hv) : ¬ ∀ s : ℂ, flow D v hv s x = x := by
  obtain ⟨y, rfl⟩ := D.quotient_surjective v hv x
  obtain ⟨z, rfl⟩ := D.periods.quotientMap_surjective y
  intro h
  apply FixedVectors.not_forall_vectorFlow_projection_eq_self
    (D.quotient v hv ∘ D.periods.quotientMap) (vectorCover_isLocalHomeomorph D v hv) z
  intro s
  exact (flow_quotient_quotientMap D v hv s z).symm.trans (h s)

/-- The original full filling for the constructed special periods has
no fixed point for the entire complex-time action. -/
theorem not_forall_specialFullFlow_eq_self (j : Kind) (x : SpecialFullFilling j) :
    ¬ ∀ s : ℂ, specialFullFlow j s x = x :=
  not_forall_flow_eq_self (specialLocalData j) j.twist (mainTwist_admissible j) x

/-- No point of either actual small elliptic filling is fixed at every
complex time.  In particular, the central elliptic fibres contribute
no points to the fixed locus of the entire action. -/
theorem not_forall_specialFlow_eq_self (j : Kind) (x : EllipticGeometry.LocalSpace j) :
    ¬ ∀ s : ℂ, specialFlow j s x = x := by
  intro h
  apply not_forall_specialFullFlow_eq_self j x.val
  intro s
  exact congrArg Subtype.val (h s)

theorem exists_specialFlow_ne_self (j : Kind) (x : EllipticGeometry.LocalSpace j) :
    ∃ s : ℂ, specialFlow j s x ≠ x :=
  not_forall.mp (not_forall_specialFlow_eq_self j x)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.Elliptic
