import Wikipedia.HopfProblem.EllipticFundamentalGroupDeck
import Wikipedia.HopfProblem.EllipticFillingTopologySurface
import Mathlib.Algebra.Group.Equiv.Opposite

/-!
# The affine deck action and the actual elliptic fundamental groups

The affine subgroup acts by evaluation on the real universal covering
space. Its action is free, continuous, and has exactly the fibres of the
constructed covering as its orbits. Mathlib's monodromy construction then
identifies the actual surface and filling fundamental groups with this
group. The inversion needed to remove the opposite-group convention is
recorded explicitly in the lifted-endpoint formula.
-/

noncomputable section

open Set Topology
open scoped Matrix

namespace Wikipedia.HopfProblem.Elliptic

@[simp] theorem deckTranslationHom_coe (j : Kind) (v : Lattice)
    (w : Multiplicative Lattice) :
    (deckTranslationHom j v w : AffineAutomorphism) = integerTranslation w.toAdd := rfl

@[simp] theorem deckGenerator_coe (j : Kind) (v : Lattice) :
    (deckGenerator j v : AffineAutomorphism) = affineGenerator j v := rfl

theorem deckTranslationHom_injective (j : Kind) (v : Lattice) :
    Function.Injective (deckTranslationHom j v) := by
  intro w z h
  apply Multiplicative.toAdd.injective
  exact integerTranslation_injective (congrArg Subtype.val h)

theorem deckGenerator_translation (j : Kind) (v w : Lattice) :
    deckGenerator j v * deckTranslationHom j v (Multiplicative.ofAdd w) =
      deckTranslationHom j v (Multiplicative.ofAdd (latticeMonodromy j w)) *
        deckGenerator j v :=
  Subtype.ext (affineGenerator_translation j v w)

theorem deckGenerator_conj_translation (j : Kind) (v w : Lattice) :
    deckGenerator j v * deckTranslationHom j v (Multiplicative.ofAdd w) *
        (deckGenerator j v)⁻¹ =
      deckTranslationHom j v (Multiplicative.ofAdd (j.matrix *ᵥ w)) :=
  Subtype.ext (affineGenerator_conj_translation j v w)

theorem deckGenerator_pow_order (j : Kind) (v : Lattice) (hv : j.matrix *ᵥ v = v) :
    deckGenerator j v ^ j.order = deckTranslationHom j v (Multiplicative.ofAdd v) :=
  Subtype.ext (affineGenerator_pow_order j v hv)

instance affineDeckGroupMulAction (j : Kind) (v : Lattice) :
    MulAction (AffineDeckGroup j v) RealCoordinates where
  smul g x := (g : AffineAutomorphism) x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[simp] theorem affineDeckGroup_smul (j : Kind) (v : Lattice)
    (g : AffineDeckGroup j v) (x : RealCoordinates) :
    g • x = (g : AffineAutomorphism) x := rfl

instance affineDeckGroupContinuousConstSMul (j : Kind) (v : Lattice) :
    ContinuousConstSMul (AffineDeckGroup j v) RealCoordinates where
  continuous_const_smul g := affineAutomorphism_continuous g.val

/-- Evaluation at any point separates actual deck transformations. -/
theorem affineDeckGroup_eval_injective (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (x : RealCoordinates) :
    Function.Injective (fun g : AffineDeckGroup j v => g • x) := by
  intro g h hgh
  obtain ⟨a, rfl⟩ := deckNormalForm_surjective j v hv.1 g
  obtain ⟨b, rfl⟩ := deckNormalForm_surjective j v hv.1 h
  have he : affineNormalForm j v a.1 a.2.val x =
      affineNormalForm j v b.1 b.2.val x := hgh
  rw [affineNormalForm_apply, affineNormalForm_apply] at he
  have hu := affineTranslate_unique j (exampleFixedPeriod j) v hv x a.2 b.2 a.1 b.1 he
  exact congrArg (deckNormalForm j v) (Prod.ext hu.2 hu.1)

theorem affineDeckGroup_free (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :
    IsCancelSMul (AffineDeckGroup j v) RealCoordinates where
  right_cancel' _ _ x hgh := affineDeckGroup_eval_injective j v hv x hgh

/-- The affine subgroup orbits are exactly the fibres of the actual surface
covering, with both implications proved from affine normal forms. -/
theorem affineCoverProjection_orbit_iff (j : Kind) (p : FixedPeriod j)
    (v : Lattice) (hv : AdmissibleTwist j v) (x y : RealCoordinates) :
    affineCoverProjection j p v hv x = affineCoverProjection j p v hv y ↔
      x ∈ MulAction.orbit (AffineDeckGroup j v) y := by
  rw [affineCoverProjection_eq_iff_translate]
  constructor
  · rintro ⟨r, hr, w, hx⟩
    refine ⟨deckNormalForm j v (w, ⟨r, hr⟩), ?_⟩
    change affineNormalForm j v w r y = x
    rw [affineNormalForm_apply]
    exact hx.symm
  · rintro ⟨g, hg⟩
    obtain ⟨a, rfl⟩ := deckNormalForm_surjective j v hv.1 g
    refine ⟨a.2.val, a.2.isLt, a.1, ?_⟩
    have he : affineNormalForm j v a.1 a.2.val y = x := hg
    exact he.symm.trans (affineNormalForm_apply j v a.1 a.2.val y)

/-- This is the actual quotient covering for the actual affine deck subgroup. -/
theorem affineCoverProjection_isQuotientCoveringMap (j : Kind) (p : FixedPeriod j)
    (v : Lattice) (hv : AdmissibleTwist j v) :
    IsQuotientCoveringMap (affineCoverProjection j p v hv) (AffineDeckGroup j v) := by
  let := affineDeckGroup_free j v hv
  exact quotientCoveringMap_of_localHomeomorph
    (affineCoverProjection_isCoveringMap j p v hv).isLocalHomeomorph
    (affineCoverProjection_surjective j p v hv) (affineCoverProjection_orbit_iff j p v hv)

/-- Monodromy naturally gives the opposite of the left-acting deck group. -/
def surfaceFundamentalGroupDeckOppositeEquiv (j : Kind) (p : FixedPeriod j)
    (v : Lattice) (hv : AdmissibleTwist j v) (y : RealCoordinates) :
    FundamentalGroup (Surface j p v hv) (affineCoverProjection j p v hv y) ≃*
      (AffineDeckGroup j v)ᵐᵒᵖ :=
  (affineCoverProjection_isQuotientCoveringMap j p v hv).fundamentalGroupEquiv ⟨y, rfl⟩

/-- The actual fundamental group is isomorphic to the actual affine subgroup.
Inversion converts the natural opposite-group isomorphism into this one. -/
def surfaceFundamentalGroupDeckEquiv (j : Kind) (p : FixedPeriod j)
    (v : Lattice) (hv : AdmissibleTwist j v) (y : RealCoordinates) :
    FundamentalGroup (Surface j p v hv) (affineCoverProjection j p v hv y) ≃*
      AffineDeckGroup j v :=
  (surfaceFundamentalGroupDeckOppositeEquiv j p v hv y).trans
    (MulEquiv.inv' (AffineDeckGroup j v)).symm

/-- This records the inversion convention: the inverse of the assigned
deck element takes the chosen lift to the endpoint of the lifted loop. -/
theorem surfaceFundamentalGroupDeckEquiv_monodromy (j : Kind) (p : FixedPeriod j)
    (v : Lattice) (hv : AdmissibleTwist j v) (y : RealCoordinates)
    (γ : FundamentalGroup (Surface j p v hv) (affineCoverProjection j p v hv y)) :
    (surfaceFundamentalGroupDeckEquiv j p v hv y γ)⁻¹ • y =
      ((affineCoverProjection_isQuotientCoveringMap j p v hv).isCoveringMap.monodromy γ
        ⟨y, rfl⟩ : RealCoordinates) := by
  let hq := affineCoverProjection_isQuotientCoveringMap j p v hv
  change ((hq.fundamentalGroupToMulOpposite ⟨y, rfl⟩ γ).unop⁻¹)⁻¹ • y = _
  rw [inv_inv]
  exact hq.unop_fundamentalGroupToMulOpposite_smul

/-- The actual elliptic filling has the same affine fundamental group,
through its proved strong deformation retraction onto the central surface. -/
def fillingFundamentalGroupDeckEquiv (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (y : RealCoordinates) :
    FundamentalGroup (Filling j v hv)
        (centralFibreInclusion j v hv (affineCoverProjection j (centralPeriod j) v hv y)) ≃*
      AffineDeckGroup j v :=
  (fillingSurfaceFundamentalGroupEquiv j v hv
    (affineCoverProjection j (centralPeriod j) v hv y)).symm.trans
      (surfaceFundamentalGroupDeckEquiv j (centralPeriod j) v hv y)

end Wikipedia.HopfProblem.Elliptic
