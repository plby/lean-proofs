import ErdosProblems.Erdos1141.QuadraticFieldClassification
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Quadratic characters on a finite product of unit groups
-/

namespace Pollack17

open scoped BigOperators

noncomputable def pullbackUnitChar {R S : Type*} [CommMonoid R] [CommMonoid S]
    (χ : MulChar R ℂ) (f : Sˣ →* Rˣ) : MulChar S ℂ :=
  MulChar.ofUnitHom (χ.toUnitHom.comp f)

theorem pullbackUnitChar_apply_unit {R S : Type*} [CommMonoid R] [CommMonoid S]
    (χ : MulChar R ℂ) (f : Sˣ →* Rˣ) (x : Sˣ) :
    pullbackUnitChar χ f x = χ (f x : R) := by
  simp only [pullbackUnitChar, MulChar.ofUnitHom_coe, MonoidHom.comp_apply,
    MulChar.coe_toUnitHom]

theorem pullbackUnitChar_isQuadratic {R S : Type*} [CommMonoid R] [CommMonoid S]
    (χ : MulChar R ℂ) (hχ : χ.IsQuadratic) (f : Sˣ →* Rˣ) :
    (pullbackUnitChar χ f).IsQuadratic := by
  intro x
  by_cases hx : IsUnit x
  · have heq : pullbackUnitChar χ f x = χ (f hx.unit : R) :=
      pullbackUnitChar_apply_unit χ f hx.unit
    rw [heq]
    exact hχ _
  · exact Or.inl ((pullbackUnitChar χ f).map_nonunit hx)

noncomputable def productUnitEmbedding {ι : Type*} [DecidableEq ι]
    (R : ι → Type*) [∀ i, CommMonoid (R i)] (i : ι) :
    (R i)ˣ →* (∀ j, R j)ˣ :=
  (MulEquiv.piUnits (M := R)).symm.toMonoidHom.comp
    (MonoidHom.mulSingle (fun j => (R j)ˣ) i)

theorem productUnitEmbedding_val {ι : Type*} [DecidableEq ι]
    (R : ι → Type*) [∀ i, CommMonoid (R i)] (i : ι) (x : (R i)ˣ) :
    (productUnitEmbedding R i x : ∀ j, R j) = Pi.mulSingle i (x : R i) := by
  ext j
  by_cases hji : j = i
  · subst j
    simp [productUnitEmbedding, MulEquiv.piUnits]
  · simp [productUnitEmbedding, MulEquiv.piUnits, hji]

theorem prod_productUnitEmbedding {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : ι → Type*) [∀ i, CommMonoid (R i)] (x : (∀ j, R j)ˣ) :
    (∏ i, productUnitEmbedding R i (MulEquiv.piUnits x i)) = x := by
  apply Units.ext
  ext j
  simp only [Units.coe_prod, Finset.prod_apply, productUnitEmbedding_val]
  exact Fintype.prod_pi_mulSingle j (fun i => (x : ∀ j, R j) i)

noncomputable def productComponentChar {ι : Type*} [DecidableEq ι]
    (R : ι → Type*) [∀ i, CommMonoid (R i)] (χ : MulChar (∀ j, R j) ℂ) (i : ι) :
    MulChar (R i) ℂ := pullbackUnitChar χ (productUnitEmbedding R i)

theorem productComponentChar_isQuadratic {ι : Type*} [DecidableEq ι]
    (R : ι → Type*) [∀ i, CommMonoid (R i)]
    (χ : MulChar (∀ j, R j) ℂ) (hχ : χ.IsQuadratic) (i : ι) :
    (productComponentChar R χ i).IsQuadratic :=
  pullbackUnitChar_isQuadratic χ hχ _

theorem character_eq_prod_components {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R : ι → Type*) [∀ i, CommMonoid (R i)]
    (χ : MulChar (∀ j, R j) ℂ) (x : (∀ j, R j)ˣ) :
    χ (x : ∀ j, R j) = ∏ i, productComponentChar R χ i ((x : ∀ j, R j) i) := by
  calc
    _ = χ ((∏ i, productUnitEmbedding R i (MulEquiv.piUnits x i) : (∀ j, R j)ˣ) : ∀ j, R j) := by
      rw [prod_productUnitEmbedding]
    _ = ∏ i, χ (productUnitEmbedding R i (MulEquiv.piUnits x i) : ∀ j, R j) := by
      rw [Units.coe_prod, map_prod]
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      exact (pullbackUnitChar_apply_unit χ (productUnitEmbedding R i) (MulEquiv.piUnits x i)).symm

end Pollack17
