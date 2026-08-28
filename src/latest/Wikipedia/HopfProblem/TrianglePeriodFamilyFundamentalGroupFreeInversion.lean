import Wikipedia.HopfProblem.TriangleRegularBaseFundamentalGroup

/-!
# Simultaneously reversing the two actual free meridians

Inverting each free generator extends to an involutive group automorphism.
Composing the proved marking of the twice-punctured plane with this
automorphism makes the two inverse meridians into a free basis as well.
The Boolean choice is left explicit; no triangle orientation is assumed.
-/

noncomputable section

namespace Wikipedia.HopfProblem.FreeMeridianMarking

private def inversionHom : FreeGroup Bool →* FreeGroup Bool :=
  FreeGroup.lift (fun b => (FreeGroup.of b)⁻¹)

@[simp] private theorem inversionHom_of (b : Bool) :
    inversionHom (FreeGroup.of b) = (FreeGroup.of b)⁻¹ := FreeGroup.lift_apply_of

private theorem inversionHom_involutive : Function.Involutive inversionHom := by
  have h : inversionHom.comp inversionHom = MonoidHom.id (FreeGroup Bool) := by
    apply FreeGroup.ext_hom
    intro b
    simp only [MonoidHom.comp_apply, inversionHom_of, map_inv, inv_inv, MonoidHom.id_apply]
  exact fun w => DFunLike.congr_fun h w

/-- Simultaneous inversion of the two free generators, extended as a
homomorphism. This is not inversion of arbitrary words. -/
def invertGenerators : FreeGroup Bool ≃* FreeGroup Bool where
  __ := inversionHom
  invFun := inversionHom
  left_inv := inversionHom_involutive
  right_inv := inversionHom_involutive

@[simp] theorem invertGenerators_of (b : Bool) :
    invertGenerators (FreeGroup.of b) = (FreeGroup.of b)⁻¹ := inversionHom_of b

theorem invertGenerators_involutive : Function.Involutive invertGenerators :=
  inversionHom_involutive

@[simp] theorem invertGenerators_apply_apply (w : FreeGroup Bool) :
    invertGenerators (invertGenerators w) = w := invertGenerators_involutive w

@[simp] theorem invertGenerators_symm : invertGenerators.symm = invertGenerators := by
  ext w
  rfl

/-- Either keep both generators or invert both, with the choice explicit. -/
def conditionalInversion : Bool → (FreeGroup Bool ≃* FreeGroup Bool)
  | false => MulEquiv.refl _
  | true => invertGenerators

@[simp] theorem conditionalInversion_false :
    conditionalInversion false = MulEquiv.refl (FreeGroup Bool) := rfl

@[simp] theorem conditionalInversion_true :
    conditionalInversion true = invertGenerators := rfl

@[simp] theorem conditionalInversion_of (reverse b : Bool) :
    conditionalInversion reverse (FreeGroup.of b) =
      if reverse then (FreeGroup.of b)⁻¹ else FreeGroup.of b := by
  cases reverse <;> simp

theorem conditionalInversion_involutive (reverse : Bool) :
    Function.Involutive (conditionalInversion reverse) := by
  cases reverse
  · exact fun _ => rfl
  · exact invertGenerators_involutive

@[simp] theorem conditionalInversion_symm (reverse : Bool) :
    (conditionalInversion reverse).symm = conditionalInversion reverse := by
  cases reverse <;> simp

/-- Reorient any genuine two-generator free marking by the same Boolean choice. -/
def reorient {K : Type*} [Group K] (e : K ≃* FreeGroup Bool) (reverse : Bool) :
    K ≃* FreeGroup Bool :=
  e.trans (conditionalInversion reverse)

@[simp] theorem reorient_apply {K : Type*} [Group K]
    (e : K ≃* FreeGroup Bool) (reverse : Bool) (x : K) :
    reorient e reverse x = conditionalInversion reverse (e x) := rfl

/-- The new free generators are precisely the original marked elements,
or both of their inverses. -/
@[simp] theorem reorient_symm_of {K : Type*} [Group K]
    (e : K ≃* FreeGroup Bool) (reverse b : Bool) :
    (reorient e reverse).symm (FreeGroup.of b) =
      if reverse then (e.symm (FreeGroup.of b))⁻¹ else e.symm (FreeGroup.of b) := by
  cases reverse <;> simp [reorient]

theorem reorient_marked_generator {K : Type*} [Group K]
    (e : K ≃* FreeGroup Bool) (reverse b : Bool) :
    reorient e reverse
      (if reverse then (e.symm (FreeGroup.of b))⁻¹ else e.symm (FreeGroup.of b)) =
      FreeGroup.of b := by
  rw [← reorient_symm_of, MulEquiv.apply_symm_apply]

open SpecialPeriods.Triangle

/-- The two actual meridian classes with a common optional reversal. -/
def orientedClass (reverse b : Bool) :
    FundamentalGroup TwicePuncturedPlane meridianBasepoint :=
  if reverse then (meridianClass b)⁻¹ else meridianClass b

@[simp] theorem orientedClass_false (b : Bool) :
    orientedClass false b = meridianClass b := rfl

@[simp] theorem orientedClass_true (b : Bool) :
    orientedClass true b = (meridianClass b)⁻¹ := rfl

/-- A genuine free marking of the actual twice-punctured-plane fundamental
group, compatible with either common orientation of its meridians. -/
def orientedEquiv (reverse : Bool) :
    FundamentalGroup TwicePuncturedPlane meridianBasepoint ≃* FreeGroup Bool :=
  reorient twicePuncturedFundamentalGroupFreeEquiv reverse

@[simp] theorem orientedEquiv_meridianClass (reverse b : Bool) :
    orientedEquiv reverse (meridianClass b) =
      if reverse then (FreeGroup.of b)⁻¹ else FreeGroup.of b := by
  change conditionalInversion reverse
    (twicePuncturedFundamentalGroupFreeEquiv (meridianClass b)) = _
  rw [twicePuncturedFundamentalGroupFreeEquiv_meridianClass, conditionalInversion_of]

@[simp] theorem orientedEquiv_meridianClass_inv (reverse b : Bool) :
    orientedEquiv reverse (meridianClass b)⁻¹ =
      if reverse then FreeGroup.of b else (FreeGroup.of b)⁻¹ := by
  rw [map_inv, orientedEquiv_meridianClass]
  cases reverse <;> simp

@[simp] theorem orientedEquiv_symm_of (reverse b : Bool) :
    (orientedEquiv reverse).symm (FreeGroup.of b) = orientedClass reverse b := by
  simp only [orientedEquiv, reorient_symm_of,
    twicePuncturedFundamentalGroupFreeEquiv_symm_of, orientedClass]

/-- Both the positive classes and their simultaneous inverses are actual
free generators under the corresponding proved marking. -/
@[simp] theorem orientedEquiv_orientedClass (reverse b : Bool) :
    orientedEquiv reverse (orientedClass reverse b) = FreeGroup.of b := by
  rw [← orientedEquiv_symm_of, MulEquiv.apply_symm_apply]

end Wikipedia.HopfProblem.FreeMeridianMarking
