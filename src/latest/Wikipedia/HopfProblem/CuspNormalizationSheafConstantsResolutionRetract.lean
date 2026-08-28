import Mathlib.Algebra.Homology.ShortComplex.Ab

/-!
# Exactness of actual short complexes descends through retracts

The general statement uses Mathlib's actual homology functor and its
criterion for `ShortComplex.Exact`.  For abelian groups, a stronger
elementwise version only needs the middle retraction and the two chain
squares used to lift a cycle and retract its preimage.  Neither a new
notion of exactness nor an exactness assumption on the smaller complex
is introduced.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace Wikipedia.HopfProblem.CuspNormalization.SheafConstants.ResolutionRetract

section General

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {S T : ShortComplex C} [S.HasHomology] [T.HasHomology]

/-- A retract of an exact actual short complex is exact.  In particular,
the homology hypotheses are automatic in an abelian category. -/
theorem exact_of_retract (i : S ⟶ T) (r : T ⟶ S)
    (hir : i ≫ r = 𝟙 S) (hT : T.Exact) : S.Exact := by
  apply S.exact_iff_isZero_homology.mpr
  rw [IsZero.iff_id_eq_zero]
  have hz := T.exact_iff_isZero_homology.mp hT
  calc
    𝟙 S.homology = ShortComplex.homologyMap (𝟙 S) :=
      (ShortComplex.homologyMap_id S).symm
    _ = ShortComplex.homologyMap (i ≫ r) :=
      congrArg (fun φ : S ⟶ S => ShortComplex.homologyMap φ) hir.symm
    _ = ShortComplex.homologyMap i ≫ ShortComplex.homologyMap r :=
      ShortComplex.homologyMap_comp i r
    _ = 0 := (congrArg (fun k => k ≫ ShortComplex.homologyMap r)
      (hz.eq_of_tgt (ShortComplex.homologyMap i) 0)).trans zero_comp

end General

section AdditiveGroups

variable {S T : ShortComplex AddCommGrpCat.{u}}

/-- Elementwise descent of actual exactness only needs the forward map
on cycles, the backward map on boundaries, and a retraction in the
middle.  No first or last component retraction identity is needed. -/
theorem ab_exact_of_middle_retract_components
    (i₂ : S.X₂ ⟶ T.X₂) (i₃ : S.X₃ ⟶ T.X₃)
    (r₁ : T.X₁ ⟶ S.X₁) (r₂ : T.X₂ ⟶ S.X₂)
    (hi : i₂ ≫ T.g = S.g ≫ i₃) (hr : r₁ ≫ S.f = T.f ≫ r₂)
    (h₂ : i₂ ≫ r₂ = 𝟙 S.X₂) (hT : T.Exact) : S.Exact := by
  apply S.ab_exact_iff.mpr
  intro x hx
  have hix : T.g (i₂ x) = 0 :=
    (ConcreteCategory.congr_hom hi x).trans ((congrArg i₃ hx).trans i₃.hom.map_zero)
  obtain ⟨y, hy⟩ := T.ab_exact_iff.mp hT (i₂ x) hix
  refine ⟨r₁ y, ?_⟩
  exact (ConcreteCategory.congr_hom hr y).trans
    ((congrArg r₂ hy).trans (ConcreteCategory.congr_hom h₂ x))

/-- For morphisms of actual short complexes of abelian groups, only
their middle components need to compose to the identity. -/
theorem ab_exact_of_middle_retract (i : S ⟶ T) (r : T ⟶ S)
    (h₂ : i.τ₂ ≫ r.τ₂ = 𝟙 S.X₂) (hT : T.Exact) : S.Exact :=
  ab_exact_of_middle_retract_components i.τ₂ i.τ₃ r.τ₁ r.τ₂ i.comm₂₃ r.comm₁₂ h₂ hT

end AdditiveGroups

end Wikipedia.HopfProblem.CuspNormalization.SheafConstants.ResolutionRetract
