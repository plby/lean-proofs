import Wikipedia.HopfProblem.EllipticFamilyAction

/-!
# Arbitrary equivariant elliptic period data

The logarithmic construction should apply to an arbitrary admissible
holomorphic period family satisfying the source's exact rotation law,
not only to one explicit local period triple.  This input contains only
the period map and its covariance identity.  No quotient manifold,
properness, or other desired conclusion is an input field.
-/

noncomputable section

open scoped Matrix ContDiff

namespace Wikipedia.HopfProblem.Elliptic.Equivariant

open SpecialPeriods

/-- Arbitrary actual holomorphic period data with elliptic covariance. -/
structure Data (j : Kind) where
  periods : HolomorphicPeriodMap ℂ Disc
  covariance : ∀ z, periods.point (familyRotation j z) = periodStep j (periods.point z)

namespace Data

variable {j : Kind} (D : Data j)

/-- The actual varying-period torus family, with its canonical product
topology and its separately selected varying-period complex atlas. -/
abbrev TotalSpace := D.periods.TotalSpace

/-- The fixed integral affine permutation of the underlying real family. -/
def permutation (v : Lattice) : Equiv.Perm D.TotalSpace := familyPermutation j v

@[simp] theorem permutation_apply (v : Lattice) (x : D.TotalSpace) :
    D.permutation v x = (familyRotation j x.1, flatTorusAffine j v x.2) := rfl

theorem permutation_pow_order (v : Lattice) (hv : j.matrix *ᵥ v = v) :
    D.permutation v ^ j.order = 1 := familyPermutation_pow_order j v hv

theorem permutation_pow_ne (v : Lattice) (hv : AdmissibleTwist j v)
    (r : ℕ) (hr : 0 < r) (hrm : r < j.order) (x : D.TotalSpace) :
    (D.permutation v ^ r) x ≠ x := familyPermutation_pow_ne j v hv r hr hrm x

theorem permutation_free_iff (v : Lattice) (hv : j.matrix *ᵥ v = v) :
    (∀ r : ℕ, 0 < r → r < j.order → ∀ x : D.TotalSpace,
      (D.permutation v ^ r) x ≠ x) ↔ AdmissibleTwist j v :=
  familyPermutation_free_iff j v hv

/-- The actual selected affine cyclic action; its topology is independent
of the varying periods, while its holomorphicity will be proved from covariance. -/
@[instance_reducible] def action (v : Lattice) (hv : j.matrix *ᵥ v = v) :
    MulAction (CyclicGroup j) D.TotalSpace := familyAction j v hv

theorem action_apply (v : Lattice) (hv : j.matrix *ᵥ v = v)
    (g : CyclicGroup j) (x : D.TotalSpace) :
    letI := D.action v hv
    g • x = ((familyRotation j)^[g.toAdd.val] x.1,
      (flatTorusAffine j v)^[g.toAdd.val] x.2) := familyAction_apply j v hv g x

theorem action_free (v : Lattice) (hv : AdmissibleTwist j v) :
    letI := D.action v hv.1
    IsCancelSMul (CyclicGroup j) D.TotalSpace := familyAction_free j v hv

theorem action_free_iff (v : Lattice) (hv : j.matrix *ᵥ v = v) :
    letI := D.action v hv
    IsCancelSMul (CyclicGroup j) D.TotalSpace ↔ AdmissibleTwist j v :=
  familyAction_free_iff j v hv

theorem action_continuous (v : Lattice) (hv : j.matrix *ᵥ v = v) :
    letI := D.action v hv
    ContinuousConstSMul (CyclicGroup j) D.TotalSpace := familyAction_continuous j v hv

theorem action_discPower (v : Lattice) (hv : j.matrix *ᵥ v = v)
    (g : CyclicGroup j) (x : D.TotalSpace) :
    letI := D.action v hv
    discPower j.order j.order_pos (g • x).1 = discPower j.order j.order_pos x.1 :=
  familyAction_discPower j v hv g x

/-- The central period is an actual fixed point of the period action. -/
def centralPeriod : FixedPeriod j :=
  ⟨D.periods.point SpecialPeriods.discZero,
    (D.covariance SpecialPeriods.discZero).symm.trans
      (congrArg D.periods.point (familyRotation_zero j))⟩

end Data

/-- The already constructed explicit local families genuinely instantiate
the generalized input data. -/
def concrete (j : Kind) : Data j where
  periods := familyPeriods j
  covariance z := by
    cases j
    · exact threePeriodMap_rotate z
    · exact fourPeriodMap_rotate z

@[simp] theorem concrete_periods (j : Kind) : (concrete j).periods = familyPeriods j := rfl

end Wikipedia.HopfProblem.Elliptic.Equivariant
