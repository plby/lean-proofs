import Wikipedia.HopfProblem.EllipticFundamentalGroupCoordinates
import Wikipedia.HopfProblem.EllipticFundamentalGroupAction
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The exact lattice extension of the actual affine deck group

The finite exponent in the proved unique affine normal form gives the
residue character. Its kernel is precisely the actual translation
subgroup, and it is onto the cyclic group of order three or four. This
proves the group extension used in §5 of `tex/s6.tex` for the genuine
subgroup of affine automorphisms, not for a postulated presentation.
-/

noncomputable section

namespace Wikipedia.HopfProblem.Elliptic

variable (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v)

/-- The finite affine exponent, reduced modulo the elliptic order. -/
def deckResidue : AffineDeckGroup j v →* CyclicGroup j :=
  MonoidHom.mk'
    (fun g => Multiplicative.ofAdd
      (((deckNormalFormEquiv j v hv).symm g).2.val : ZMod j.order)) (by
      intro g h
      apply Multiplicative.toAdd.injective
      change (((deckNormalFormEquiv j v hv).symm (g * h)).2.val : ZMod j.order) =
        (((deckNormalFormEquiv j v hv).symm g).2.val : ZMod j.order) +
          (((deckNormalFormEquiv j v hv).symm h).2.val : ZMod j.order)
      rw [deckNormalFormEquiv_symm_mul, coordinateProduct_snd_val,
        ZMod.natCast_mod, Nat.cast_add])

@[simp] theorem deckResidue_normalForm (a : Lattice × Fin j.order) :
    deckResidue j v hv (deckNormalForm j v a) =
      Multiplicative.ofAdd (a.2.val : ZMod j.order) := by
  change Multiplicative.ofAdd
    (((deckNormalFormEquiv j v hv).symm ((deckNormalFormEquiv j v hv) a)).2.val :
      ZMod j.order) = _
  rw [Equiv.symm_apply_apply]

/-- Every integral translation has trivial cyclic residue. -/
@[simp] theorem deckResidue_translation (w : Multiplicative Lattice) :
    deckResidue j v hv (deckTranslationHom j v w) = 1 := by
  simpa [deckNormalForm] using deckResidue_normalForm j v hv (w.toAdd, ⟨0, j.order_pos⟩)

/-- The actual affine generator maps to the specified cyclic generator. -/
@[simp] theorem deckResidue_generator :
    deckResidue j v hv (deckGenerator j v) = Multiplicative.ofAdd (1 : ZMod j.order) := by
  have hm : 1 < j.order := by cases j <;> decide
  simpa [deckNormalForm] using deckResidue_normalForm j v hv (0, ⟨1, hm⟩)

theorem deckResidue_surjective : Function.Surjective (deckResidue j v hv) := by
  intro z
  refine ⟨deckNormalForm j v (0, ⟨z.toAdd.val, ZMod.val_lt _⟩), ?_⟩
  rw [deckResidue_normalForm]
  exact congrArg Multiplicative.ofAdd (ZMod.natCast_zmod_val z.toAdd)

/-- Having zero affine residue is equivalent to being an actual integral
translation, with both directions proved from the unique normal forms. -/
theorem deckResidue_eq_one_iff (g : AffineDeckGroup j v) :
    deckResidue j v hv g = 1 ↔ g ∈ (deckTranslationHom j v).range := by
  constructor
  · intro hg
    obtain ⟨a, ha⟩ := deckNormalForm_surjective j v hv.1 g
    rw [← ha, deckResidue_normalForm] at hg
    have hz : (a.2.val : ZMod j.order) = 0 := congrArg Multiplicative.toAdd hg
    have hr := congrArg ZMod.val hz
    rw [ZMod.val_natCast_of_lt a.2.isLt, ZMod.val_zero] at hr
    refine ⟨Multiplicative.ofAdd a.1, ?_⟩
    rw [← ha, deckNormalForm, hr, pow_zero, mul_one]
  · rintro ⟨w, rfl⟩
    exact deckResidue_translation j v hv w

/-- The kernel of the residue character is exactly the lattice subgroup. -/
theorem deckResidue_ker : (deckResidue j v hv).ker = (deckTranslationHom j v).range := by
  ext g
  exact deckResidue_eq_one_iff j v hv g

/-- The actual affine deck group fits into the exact sequence
`1 → Λ → Γ → ℤ/m → 1`. -/
theorem affineDeckGroup_exactSequence :
    Function.Injective (deckTranslationHom j v) ∧
      (deckResidue j v hv).ker = (deckTranslationHom j v).range ∧
      Function.Surjective (deckResidue j v hv) :=
  ⟨deckTranslationHom_injective j v, deckResidue_ker j v hv, deckResidue_surjective j v hv⟩

/-- Normality of the actual translation subgroup follows from the kernel
calculation. -/
theorem deckTranslationRange_normal (hv : AdmissibleTwist j v) :
    (deckTranslationHom j v).range.Normal := by
  rw [← deckResidue_ker j v hv]
  infer_instance

/-- Quotienting the genuine affine deck subgroup by its translations gives
the actual cyclic group of the stated elliptic order. -/
def deckQuotientEquiv :
    letI : (deckTranslationHom j v).range.Normal := deckTranslationRange_normal j v hv
    (AffineDeckGroup j v ⧸ (deckTranslationHom j v).range) ≃* CyclicGroup j := by
  letI : (deckTranslationHom j v).range.Normal := deckTranslationRange_normal j v hv
  exact (QuotientGroup.quotientMulEquivOfEq (deckResidue_ker j v hv).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (deckResidue j v hv)
      (deckResidue_surjective j v hv))

@[simp] theorem deckQuotientEquiv_mk (g : AffineDeckGroup j v) :
    deckQuotientEquiv j v hv (QuotientGroup.mk g) = deckResidue j v hv g := rfl

/-- The translation lattice has exactly three or four cosets. -/
theorem deckTranslation_index (hv : AdmissibleTwist j v) :
    (deckTranslationHom j v).range.index = j.order := by
  let : (deckTranslationHom j v).range.Normal := deckTranslationRange_normal j v hv
  change Nat.card (AffineDeckGroup j v ⧸ (deckTranslationHom j v).range) = j.order
  rw [Nat.card_congr (deckQuotientEquiv j v hv).toEquiv]
  simp [CyclicGroup, Nat.card_eq_fintype_card, ZMod.card]

end Wikipedia.HopfProblem.Elliptic
