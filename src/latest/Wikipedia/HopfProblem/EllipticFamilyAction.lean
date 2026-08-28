import Wikipedia.HopfProblem.EllipticFamilies
import Wikipedia.HopfProblem.EllipticSurfaces
import Wikipedia.HopfProblem.EllipticDiscPower

/-!
# The finite free action on the actual elliptic torus family

The logarithmic generator acts by the prescribed disc rotation and the
actual affine homeomorphism of the flat torus.  Its finite order and
freeness are proved from these factors.  The whole resulting cyclic
action is holomorphic in the varying-period atlas, and the base power
map is invariant under every group element.
-/

noncomputable section

open scoped Matrix ContDiff

namespace Wikipedia.HopfProblem.Elliptic

open SpecialPeriods

theorem familyPermutation_iterate (j : Kind) (v : Lattice) (r : ℕ) (x : Family j) :
    (familyPermutation j v)^[r] x =
      ((familyRotation j)^[r] x.1, (flatTorusAffine j v)^[r] x.2) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [Function.iterate_succ_apply', ih, familyPermutation_apply]

theorem familyPermutation_pow_apply (j : Kind) (v : Lattice) (r : ℕ) (x : Family j) :
    (familyPermutation j v ^ r) x =
      ((familyRotation j)^[r] x.1, (flatTorusAffine j v)^[r] x.2) := by
  rw [Equiv.Perm.coe_pow]
  exact familyPermutation_iterate j v r x

/-- The `m`-th power is the identity on the actual whole family. -/
theorem familyPermutation_pow_order (j : Kind) (v : Lattice)
    (hv : j.matrix *ᵥ v = v) : familyPermutation j v ^ j.order = 1 := by
  apply Equiv.ext
  intro x
  rw [familyPermutation_pow_apply, familyRotation_iterate_order,
    flatTorusAffine_iterate_order j v hv]
  rfl

/-- The free affine action on the torus factor rules out all fixed points
of nonidentity powers, on every fibre of the family. -/
theorem familyPermutation_pow_ne (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (r : ℕ) (hr : 0 < r) (hrm : r < j.order)
    (x : Family j) : (familyPermutation j v ^ r) x ≠ x := by
  intro hx
  rw [familyPermutation_pow_apply] at hx
  exact flatTorusAffine_iterate_ne j v hv r hr hrm x.2 (congrArg Prod.snd hx)

@[simp] theorem familyRotation_zero (j : Kind) : familyRotation j discZero = discZero := by
  cases j <;> apply Subtype.ext
  · change -rho * (0 : ℂ) = 0
    exact mul_zero _
  · change -Complex.I * (0 : ℂ) = 0
    exact mul_zero _

/-- Every nonidentity power of a base rotation fixes precisely the centre. -/
theorem familyRotation_iterate_fixed_iff (j : Kind) (r : ℕ)
    (hr : 0 < r) (hrm : r < j.order) (z : Disc) :
    (familyRotation j)^[r] z = z ↔ z = discZero := by
  cases j
  · exact discRotateThree_iterate_fixed_iff r hr hrm z
  · exact discRotateFour_iterate_fixed_iff r hr hrm z

/-- Even before imposing admissibility, every nontrivial fixed point lies
over the centre of the disc, as in Proposition 5.6. -/
theorem familyPermutation_fixed_base (j : Kind) (v : Lattice) (r : ℕ)
    (hr : 0 < r) (hrm : r < j.order) (x : Family j)
    (hx : (familyPermutation j v ^ r) x = x) : x.1 = discZero := by
  apply (familyRotation_iterate_fixed_iff j r hr hrm x.1).mp
  rw [familyPermutation_pow_apply] at hx
  exact congrArg Prod.fst hx

/-- The exact admissibility criterion holds on the whole actual family. -/
theorem familyPermutation_free_iff (j : Kind) (v : Lattice)
    (hv : j.matrix *ᵥ v = v) :
    (∀ r : ℕ, 0 < r → r < j.order → ∀ x : Family j,
      (familyPermutation j v ^ r) x ≠ x) ↔ AdmissibleTwist j v := by
  constructor
  · intro hf
    apply (flatTorusPermutation_free_iff j v hv).mp
    intro r hr hrm y hy
    apply hf r hr hrm (discZero, y)
    rw [familyPermutation_pow_apply]
    apply Prod.ext (Function.iterate_fixed (familyRotation_zero j) r)
    simpa only [Equiv.Perm.coe_pow, flatTorusPermutation, Homeomorph.coe_toEquiv] using hy
  · intro ha
    exact familyPermutation_pow_ne j v ha

/-- The generator has order exactly `m` for every invariant twist, including
the nonfree twists: its projection already has that order on the base. -/
theorem familyPermutation_orderOf (j : Kind) (v : Lattice)
    (hv : j.matrix *ᵥ v = v) : orderOf (familyPermutation j v) = j.order := by
  apply (orderOf_eq_iff j.order_pos).mpr
  refine ⟨familyPermutation_pow_order j v hv, ?_⟩
  intro r hrm hr heq
  let z : Disc := ⟨(1 / 2 : ℂ), by norm_num [unitDisc]⟩
  have hz := familyPermutation_fixed_base j v r hr hrm (z, 0) (by rw [heq]; rfl)
  have hval := congrArg Subtype.val hz
  norm_num [z, discZero] at hval

/-- The actual selected action of the cyclic group of the required order. -/
@[instance_reducible] def familyAction (j : Kind) (v : Lattice)
    (hv : j.matrix *ᵥ v = v) : MulAction (CyclicGroup j) (Family j) :=
  CyclicAction.action (familyPermutation j v) (familyPermutation_pow_order j v hv)

theorem familyAction_generator_smul (j : Kind) (v : Lattice)
    (hv : j.matrix *ᵥ v = v) (x : Family j) :
    letI := familyAction j v hv
    CyclicAction.generator j.order • x = familyPermutation j v x :=
  CyclicAction.generator_smul (familyPermutation j v)
    (familyPermutation_pow_order j v hv) x

theorem familyAction_apply (j : Kind) (v : Lattice) (hv : j.matrix *ᵥ v = v)
    (g : CyclicGroup j) (x : Family j) :
    letI := familyAction j v hv
    g • x = ((familyRotation j)^[g.toAdd.val] x.1,
      (flatTorusAffine j v)^[g.toAdd.val] x.2) :=
  (CyclicAction.smul_eq_iterate (familyPermutation j v)
    (familyPermutation_pow_order j v hv) g x).trans
      (familyPermutation_iterate j v g.toAdd.val x)

theorem familyAction_free_iff (j : Kind) (v : Lattice) (hv : j.matrix *ᵥ v = v) :
    letI := familyAction j v hv
    IsCancelSMul (CyclicGroup j) (Family j) ↔ AdmissibleTwist j v := by
  refine (CyclicAction.isCancelSMul_iff (familyPermutation j v)
    (familyPermutation_pow_order j v hv)).trans ?_
  simpa only [Equiv.Perm.coe_pow] using familyPermutation_free_iff j v hv

/-- Freeness is a consequence of the checked arithmetic of the actual twist. -/
theorem familyAction_free (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :
    letI := familyAction j v hv.1
    IsCancelSMul (CyclicGroup j) (Family j) :=
  (familyAction_free_iff j v hv.1).mpr hv

/-- The action is holomorphic for the complex atlas of the actual varying
period family, not for an assumed product complex structure. -/
theorem familyAction_holomorphic (j : Kind) (v : Lattice)
    (hv : j.matrix *ᵥ v = v) (g : CyclicGroup j) :
    letI := (familyPeriods j).totalChartedSpace
    letI := familyAction j v hv
    ContMDiff (modelWithCornersSelf ℂ FamilyModel) (modelWithCornersSelf ℂ FamilyModel) ω
      (fun x : Family j => g • x) := by
  let := (familyPeriods j).totalChartedSpace
  exact CyclicAction.smul_contMDiff (familyPermutation j v)
    (familyPermutation_pow_order j v hv) (familyPermutation_holomorphic j v) g

theorem familyAction_continuous (j : Kind) (v : Lattice)
    (hv : j.matrix *ᵥ v = v) :
    letI := familyAction j v hv
    ContinuousConstSMul (CyclicGroup j) (Family j) := by
  apply CyclicAction.continuousConstSMul (familyPermutation j v)
    (familyPermutation_pow_order j v hv)
  let := (familyPeriods j).totalChartedSpace
  exact (familyPermutation_holomorphic j v).continuous

/-- The source's local base coordinate `s^m` is unchanged by the generator. -/
theorem discPower_familyRotation (j : Kind) (z : Disc) :
    discPower j.order j.order_pos (familyRotation j z) =
      discPower j.order j.order_pos z := by
  cases j <;> apply Subtype.ext
  · change (-rho * (z : ℂ)) ^ 3 = (z : ℂ) ^ 3
    rw [mul_pow, neg_pow, rho_cube]
    norm_num
  · change (-Complex.I * (z : ℂ)) ^ 4 = (z : ℂ) ^ 4
    norm_num [mul_pow]

theorem discPower_familyRotation_iterate (j : Kind) (r : ℕ) (z : Disc) :
    discPower j.order j.order_pos ((familyRotation j)^[r] z) =
      discPower j.order j.order_pos z := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply', discPower_familyRotation, ih]

/-- The positive power of the base coordinate is invariant under every
element of the actual finite action, so it descends to its orbit quotient. -/
theorem familyAction_discPower (j : Kind) (v : Lattice) (hv : j.matrix *ᵥ v = v)
    (g : CyclicGroup j) (x : Family j) :
    letI := familyAction j v hv
    discPower j.order j.order_pos (g • x).1 = discPower j.order j.order_pos x.1 := by
  let := familyAction j v hv
  rw [familyAction_apply]
  exact discPower_familyRotation_iterate j g.toAdd.val x.1

end Wikipedia.HopfProblem.Elliptic
