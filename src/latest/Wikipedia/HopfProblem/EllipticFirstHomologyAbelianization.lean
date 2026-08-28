import Wikipedia.HopfProblem.EllipticFirstHomologyLattice
import Wikipedia.HopfProblem.EllipticFundamentalGroupPresentation
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.Algebra.Module.Equiv.Basic

/-!
# The abelianization of the actual elliptic affine group

The proof of Theorem 5.4(iii), `tex/s6.tex` lines 17258 onward, uses
`ℤ³ / ⟨(γ(v), ψⱼ(v), -mⱼ)⟩`. This file derives that quotient from the
proved presentation of the genuine affine deck group. It concerns the
group's abelianization; no singular-homology comparison is assumed.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.Elliptic

/-- The additive form of the genuine affine group's abelianization. -/
abbrev DeckAbelianization (j : Kind) (v : Lattice) :=
  Additive (Abelianization (AffineDeckGroup j v))

/-- Append a zero affine-generator coordinate to the two coinvariant coordinates. -/
def abelianCoordinateInclusion : (Fin 2 → ℤ) →ₗ[ℤ] (Fin 3 → ℤ) where
  toFun x := ![x 0, x 1, 0]
  map_add' x y := by ext i; fin_cases i <;> simp
  map_smul' a x := by ext i; fin_cases i <;> simp

/-- Forget the affine-generator coordinate. -/
def abelianCoordinatePair : (Fin 3 → ℤ) →ₗ[ℤ] (Fin 2 → ℤ) where
  toFun x := ![x 0, x 1]
  map_add' x y := by ext i; fin_cases i <;> simp
  map_smul' a x := by ext i; fin_cases i <;> simp

/-- The generator coordinate in the three-generator abelian presentation. -/
def abelianGeneratorVector : Fin 3 → ℤ := ![0, 0, 1]

/-- The relation is the actual affine power relation `h^m = T_v`. -/
def abelianRelation (j : Kind) (v : Lattice) : Fin 3 → ℤ :=
  ![γ v, psi j v, -(j.order : ℤ)]

def abelianRelationSpan (j : Kind) (v : Lattice) : Submodule ℤ (Fin 3 → ℤ) :=
  ℤ ∙ abelianRelation j v

/-- The integral module quotient displayed in Theorem 5.4(iii). -/
abbrev AbelianCoordinateQuotient (j : Kind) (v : Lattice) :=
  (Fin 3 → ℤ) ⧸ abelianRelationSpan j v

def abelianCoordinateTranslation (j : Kind) (v : Lattice) :
    Lattice →ₗ[ℤ] AbelianCoordinateQuotient j v :=
  (abelianRelationSpan j v).mkQ.comp (abelianCoordinateInclusion.comp (coinvariantMap j))

def abelianCoordinateGenerator (j : Kind) (v : Lattice) :
    AbelianCoordinateQuotient j v := Submodule.Quotient.mk abelianGeneratorVector

theorem abelianCoordinateTranslation_monodromy (j : Kind) (v w : Lattice) :
    abelianCoordinateTranslation j v (j.matrix *ᵥ w) = abelianCoordinateTranslation j v w := by
  change (abelianRelationSpan j v).mkQ
      (abelianCoordinateInclusion (coinvariantMap j (j.matrix *ᵥ w))) = _
  rw [coinvariantMap_monodromy]
  rfl

theorem abelianCoordinateGenerator_order (j : Kind) (v : Lattice) :
    j.order • abelianCoordinateGenerator j v = abelianCoordinateTranslation j v v := by
  change (abelianRelationSpan j v).mkQ (j.order • abelianGeneratorVector) =
    (abelianRelationSpan j v).mkQ (abelianCoordinateInclusion (coinvariantMap j v))
  apply (Submodule.Quotient.eq _).mpr
  have he : j.order • abelianGeneratorVector -
      abelianCoordinateInclusion (coinvariantMap j v) = -abelianRelation j v := by
    ext i
    fin_cases i <;>
      simp [abelianGeneratorVector, abelianCoordinateInclusion, abelianRelation, coinvariantMap]
  rw [he]
  exact Submodule.neg_mem _ (Submodule.subset_span (Set.mem_singleton _))

private theorem abelianCoordinate_conjugation (j : Kind) (v w : Lattice) :
    Multiplicative.ofAdd (abelianCoordinateGenerator j v) *
        (abelianCoordinateTranslation j v).toAddMonoidHom.toMultiplicative
          (Multiplicative.ofAdd w) =
      (abelianCoordinateTranslation j v).toAddMonoidHom.toMultiplicative
          (Multiplicative.ofAdd (j.matrix *ᵥ w)) *
        Multiplicative.ofAdd (abelianCoordinateGenerator j v) := by
  change Multiplicative.ofAdd
      (abelianCoordinateGenerator j v + abelianCoordinateTranslation j v w) =
    Multiplicative.ofAdd
      (abelianCoordinateTranslation j v (j.matrix *ᵥ w) + abelianCoordinateGenerator j v)
  rw [abelianCoordinateTranslation_monodromy, add_comm]

private theorem abelianCoordinate_power (j : Kind) (v : Lattice) :
    Multiplicative.ofAdd (abelianCoordinateGenerator j v) ^ j.order =
      (abelianCoordinateTranslation j v).toAddMonoidHom.toMultiplicative
        (Multiplicative.ofAdd v) :=
  congrArg Multiplicative.ofAdd (abelianCoordinateGenerator_order j v)

/-- The actual affine group maps into the displayed abelian presentation. -/
def deckAbelianCharacter (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :
    AffineDeckGroup j v →* Multiplicative (AbelianCoordinateQuotient j v) :=
  Classical.choose (affineDeckGroup_presentation j v hv
    (abelianCoordinateTranslation j v).toAddMonoidHom.toMultiplicative
    (Multiplicative.ofAdd (abelianCoordinateGenerator j v))
    (abelianCoordinate_conjugation j v) (abelianCoordinate_power j v))

theorem deckAbelianCharacter_spec (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :
    (∀ w, deckAbelianCharacter j v hv (deckTranslationHom j v (Multiplicative.ofAdd w)) =
      Multiplicative.ofAdd (abelianCoordinateTranslation j v w)) ∧
    deckAbelianCharacter j v hv (deckGenerator j v) =
      Multiplicative.ofAdd (abelianCoordinateGenerator j v) :=
  (Classical.choose_spec (affineDeckGroup_presentation j v hv
    (abelianCoordinateTranslation j v).toAddMonoidHom.toMultiplicative
    (Multiplicative.ofAdd (abelianCoordinateGenerator j v))
    (abelianCoordinate_conjugation j v) (abelianCoordinate_power j v))).1

/-- Integral translations in the genuine abelianization. -/
def deckAbelianTranslation (j : Kind) (v : Lattice) :
    Lattice →ₗ[ℤ] DeckAbelianization j v :=
  ((Abelianization.of.comp (deckTranslationHom j v)).toAdditiveRight).toIntLinearMap

/-- The class of the affine generator in the genuine abelianization. -/
def deckAbelianGenerator (j : Kind) (v : Lattice) : DeckAbelianization j v :=
  Additive.ofMul (Abelianization.of (deckGenerator j v))

theorem deckAbelianTranslation_monodromy (j : Kind) (v w : Lattice) :
    deckAbelianTranslation j v (j.matrix *ᵥ w) = deckAbelianTranslation j v w := by
  apply Additive.toMul.injective
  change Abelianization.of (deckTranslationHom j v (Multiplicative.ofAdd (j.matrix *ᵥ w))) =
    Abelianization.of (deckTranslationHom j v (Multiplicative.ofAdd w))
  have h := congrArg Abelianization.of (deckGenerator_translation j v w)
  simp only [map_mul, latticeMonodromy_apply] at h
  exact mul_right_cancel (h.symm.trans (mul_comm _ _))

theorem deckAbelianTranslation_difference (j : Kind) (v w : Lattice) :
    deckAbelianTranslation j v (coinvariantDifference j w) = 0 := by
  rw [coinvariantDifference_apply, map_sub, deckAbelianTranslation_monodromy, sub_self]

theorem deckAbelianTranslation_section (j : Kind) (v w : Lattice) :
    deckAbelianTranslation j v (coinvariantSection j (coinvariantMap j w)) =
      deckAbelianTranslation j v w := by
  have hk : coinvariantMap j (w - coinvariantSection j (coinvariantMap j w)) = 0 := by
    rw [map_sub, coinvariantMap_section, sub_self]
  obtain ⟨z, hz⟩ := (coinvariantMap_eq_zero_iff j _).mp hk
  have hzero : deckAbelianTranslation j v
      (w - coinvariantSection j (coinvariantMap j w)) = 0 := by
    rw [← hz]
    exact deckAbelianTranslation_difference j v z
  exact (sub_eq_zero.mp ((map_sub (deckAbelianTranslation j v) _ _).symm.trans hzero)).symm

theorem deckAbelianGenerator_order (j : Kind) (v : Lattice)
    (hv : j.matrix *ᵥ v = v) :
    j.order • deckAbelianGenerator j v = deckAbelianTranslation j v v := by
  apply Additive.toMul.injective
  change Abelianization.of (deckGenerator j v) ^ j.order =
    Abelianization.of (deckTranslationHom j v (Multiplicative.ofAdd v))
  rw [← map_pow, deckGenerator_pow_order j v hv]

/-- The forward homomorphism is the lift of the actual affine-group
character through its abelianization. -/
def deckAbelianCoordinateMap (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :
    DeckAbelianization j v →ₗ[ℤ] AbelianCoordinateQuotient j v :=
  (Abelianization.lift (deckAbelianCharacter j v hv)).toAdditiveLeft.toIntLinearMap

@[simp] theorem deckAbelianCoordinateMap_translation (j : Kind) (v w : Lattice)
    (hv : AdmissibleTwist j v) :
    deckAbelianCoordinateMap j v hv (deckAbelianTranslation j v w) =
      abelianCoordinateTranslation j v w :=
  congrArg Multiplicative.toAdd ((deckAbelianCharacter_spec j v hv).1 w)

@[simp] theorem deckAbelianCoordinateMap_generator (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) :
    deckAbelianCoordinateMap j v hv (deckAbelianGenerator j v) =
      abelianCoordinateGenerator j v :=
  congrArg Multiplicative.toAdd (deckAbelianCharacter_spec j v hv).2

/-- Evaluate the three formal additive generators in the genuine abelianization. -/
def deckAbelianWord (j : Kind) (v : Lattice) :
    (Fin 3 → ℤ) →ₗ[ℤ] DeckAbelianization j v :=
  ((deckAbelianTranslation j v).comp (coinvariantSection j)).comp abelianCoordinatePair +
    (LinearMap.proj 2).smulRight (deckAbelianGenerator j v)

theorem deckAbelianWord_apply (j : Kind) (v : Lattice) (x : Fin 3 → ℤ) :
    deckAbelianWord j v x =
      deckAbelianTranslation j v (coinvariantSection j ![x 0, x 1]) +
        x 2 • deckAbelianGenerator j v := rfl

theorem deckAbelianWord_relation (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :
    deckAbelianWord j v (abelianRelation j v) = 0 := by
  rw [deckAbelianWord_apply]
  change deckAbelianTranslation j v (coinvariantSection j (coinvariantMap j v)) +
    (-(j.order : ℤ)) • deckAbelianGenerator j v = 0
  rw [deckAbelianTranslation_section, neg_smul, natCast_zsmul,
    deckAbelianGenerator_order j v hv.1, add_neg_cancel]

/-- The displayed relation vanishes in the actual abelianization, so
evaluation descends to the actual module quotient. -/
def deckAbelianQuotientLift (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :
    AbelianCoordinateQuotient j v →ₗ[ℤ] DeckAbelianization j v :=
  Submodule.liftQSpanSingleton (abelianRelation j v) (deckAbelianWord j v)
    (deckAbelianWord_relation j v hv)

@[simp] theorem deckAbelianQuotientLift_mk (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (x : Fin 3 → ℤ) :
    deckAbelianQuotientLift j v hv (Submodule.Quotient.mk x) = deckAbelianWord j v x := rfl

@[simp] theorem deckAbelianQuotientLift_translation (j : Kind) (v w : Lattice)
    (hv : AdmissibleTwist j v) :
    deckAbelianQuotientLift j v hv (abelianCoordinateTranslation j v w) =
      deckAbelianTranslation j v w := by
  change deckAbelianWord j v ![γ w, psi j w, 0] = _
  rw [deckAbelianWord_apply]
  change deckAbelianTranslation j v (coinvariantSection j (coinvariantMap j w)) +
    (0 : ℤ) • deckAbelianGenerator j v = _
  rw [zero_smul, add_zero, deckAbelianTranslation_section]

@[simp] theorem deckAbelianQuotientLift_generator (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) :
    deckAbelianQuotientLift j v hv (abelianCoordinateGenerator j v) =
      deckAbelianGenerator j v := by
  change deckAbelianWord j v abelianGeneratorVector = _
  rw [deckAbelianWord_apply]
  change deckAbelianTranslation j v (coinvariantSection j ![0, 0]) +
    (1 : ℤ) • deckAbelianGenerator j v = _
  have hzero : (![0, 0] : Fin 2 → ℤ) = 0 := by ext i; fin_cases i <;> rfl
  rw [hzero, map_zero, map_zero, one_smul, zero_add]

theorem deckAbelianCoordinateMap_word (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (x : Fin 3 → ℤ) :
    deckAbelianCoordinateMap j v hv (deckAbelianWord j v x) =
      Submodule.Quotient.mk x := by
  rw [deckAbelianWord_apply, map_add, map_smul, deckAbelianCoordinateMap_translation,
    deckAbelianCoordinateMap_generator]
  change (abelianRelationSpan j v).mkQ
      (abelianCoordinateInclusion (coinvariantMap j (coinvariantSection j ![x 0, x 1]))) +
      x 2 • (abelianRelationSpan j v).mkQ abelianGeneratorVector =
    (abelianRelationSpan j v).mkQ x
  rw [coinvariantMap_section, ← map_smul, ← map_add]
  congr 1
  ext i
  fin_cases i <;> simp [abelianCoordinateInclusion, abelianGeneratorVector]

theorem deckAbelianQuotientLift_rightInverse (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) :
    Function.RightInverse (deckAbelianQuotientLift j v hv) (deckAbelianCoordinateMap j v hv) := by
  intro x
  refine Submodule.Quotient.induction_on _ x ?_
  intro w
  rw [deckAbelianQuotientLift_mk, deckAbelianCoordinateMap_word]

theorem deckAbelianQuotientLift_leftInverse (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) :
    Function.LeftInverse (deckAbelianQuotientLift j v hv) (deckAbelianCoordinateMap j v hv) := by
  intro x
  obtain ⟨g, hg⟩ := Quotient.exists_rep x.toMul
  have hx : Additive.ofMul (Abelianization.of g) = x := congrArg Additive.ofMul hg
  rw [← hx]
  obtain ⟨a, rfl⟩ := deckNormalForm_surjective j v hv.1 g
  have he : Additive.ofMul (Abelianization.of (deckNormalForm j v a)) =
      deckAbelianTranslation j v a.1 + a.2.val • deckAbelianGenerator j v := by
    change Additive.ofMul (Abelianization.of
      (deckTranslationHom j v (Multiplicative.ofAdd a.1) * deckGenerator j v ^ a.2.val)) = _
    rw [map_mul, map_pow, ofMul_mul, ofMul_pow]
    rfl
  rw [he]
  simp only [map_add, map_nsmul, deckAbelianCoordinateMap_translation,
    deckAbelianCoordinateMap_generator, deckAbelianQuotientLift_translation,
    deckAbelianQuotientLift_generator]

/-- The actual affine deck-group abelianization, with no presentation
assumptions, is the integral quotient in Theorem 5.4(iii). -/
def deckAbelianizationQuotientEquiv (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) :
    DeckAbelianization j v ≃ₗ[ℤ] AbelianCoordinateQuotient j v :=
  LinearEquiv.ofLinearMap (deckAbelianCoordinateMap j v hv) (deckAbelianQuotientLift j v hv)
    (by apply LinearMap.ext; exact deckAbelianQuotientLift_rightInverse j v hv)
    (by apply LinearMap.ext; exact deckAbelianQuotientLift_leftInverse j v hv)

@[simp] theorem deckAbelianizationQuotientEquiv_translation (j : Kind) (v w : Lattice)
    (hv : AdmissibleTwist j v) :
    deckAbelianizationQuotientEquiv j v hv (deckAbelianTranslation j v w) =
      abelianCoordinateTranslation j v w := deckAbelianCoordinateMap_translation j v w hv

@[simp] theorem deckAbelianizationQuotientEquiv_generator (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) :
    deckAbelianizationQuotientEquiv j v hv (deckAbelianGenerator j v) =
      abelianCoordinateGenerator j v := deckAbelianCoordinateMap_generator j v hv

end Wikipedia.HopfProblem.Elliptic
