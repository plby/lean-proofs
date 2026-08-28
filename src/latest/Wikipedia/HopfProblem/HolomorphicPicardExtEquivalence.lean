import Wikipedia.HopfProblem.HolomorphicPicardExtSplit

/-!
# Equality of extension classes gives an actual middle isomorphism

For short exact sequences with the same literal endpoints, equality of the
actual degree-one Ext classes first gives a lift of the quotient map.  Its
left-endpoint discrepancy factors through the genuine kernel and is removed
using the contravariant Ext sequence.  The short five lemma then makes the
corrected middle map an isomorphism.  No enough-injectives hypothesis is used.
-/

universe w v u

open CategoryTheory CategoryTheory.Category CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.HolomorphicPicard.ExtExtensions

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {A B E₁ E₂ : C}
  {i₁ : A ⟶ E₁} {p₁ : E₁ ⟶ B} {w₁ : i₁ ≫ p₁ = 0}
  {i₂ : A ⟶ E₂} {p₂ : E₂ ⟶ B} {w₂ : i₂ ≫ p₂ = 0}

/-- An actual morphism of short exact sequences which fixes the endpoints
preserves their genuine degree-one Ext classes. -/
theorem extClass_eq_of_middle_map
    (h₁ : (ShortComplex.mk i₁ p₁ w₁).ShortExact)
    (h₂ : (ShortComplex.mk i₂ p₂ w₂).ShortExact)
    (m : E₁ ⟶ E₂) (hi : i₁ ≫ m = i₂) (hp : m ≫ p₂ = p₁) :
    (h₁.extClass : Ext.{w} B A 1) = h₂.extClass := by
  let φ : ShortComplex.mk i₁ p₁ w₁ ⟶ ShortComplex.mk i₂ p₂ w₂ :=
    { τ₁ := 𝟙 A
      τ₂ := m
      τ₃ := 𝟙 B
      comm₁₂ := by simpa only [id_comp] using hi.symm
      comm₂₃ := by simpa only [comp_id] using hp }
  have h := h₁.extClass_naturality h₂ φ
  change h₁.extClass.comp (Ext.mk₀ (𝟙 A)) (add_zero 1) =
    (Ext.mk₀ (𝟙 B)).comp h₂.extClass (zero_add 1) at h
  simpa only [Ext.comp_mk₀_id, Ext.mk₀_id_comp] using h

/-- Equal Ext classes give a genuine morphism of the original short exact
sequences which is the identity on both endpoints. -/
theorem exists_middle_map_of_extClass_eq
    (h₁ : (ShortComplex.mk i₁ p₁ w₁).ShortExact)
    (h₂ : (ShortComplex.mk i₂ p₂ w₂).ShortExact)
    (h : (h₁.extClass : Ext.{w} B A 1) = h₂.extClass) :
    ∃ m : E₁ ⟶ E₂, i₁ ≫ m = i₂ ∧ m ≫ p₂ = p₁ := by
  have hboundary : (Ext.mk₀ p₁).comp h₂.extClass (zero_add 1) = 0 := by
    rw [← h]
    exact h₁.comp_extClass
  obtain ⟨μ, hμ⟩ := Ext.covariant_sequence_exact₃ E₁ h₂
    (Ext.mk₀ p₁) (zero_add 1) hboundary
  obtain ⟨m, rfl⟩ := (Ext.mk₀_bijective E₁ E₂).surjective μ
  have hm : m ≫ p₂ = p₁ := by
    apply (Ext.mk₀_bijective E₁ B).injective
    simpa only [Ext.mk₀_comp_mk₀] using hμ
  have : Mono i₂ := h₂.mono_f
  have hk : (i₁ ≫ m) ≫ p₂ = 0 := by rw [assoc, hm, w₁]
  obtain ⟨e, he⟩ : ∃ e : A ⟶ A, e ≫ i₂ = i₁ ≫ m :=
    h₂.exact.lift' (i₁ ≫ m) hk
  let φ : ShortComplex.mk i₁ p₁ w₁ ⟶ ShortComplex.mk i₂ p₂ w₂ :=
    { τ₁ := e
      τ₂ := m
      τ₃ := 𝟙 B
      comm₁₂ := he
      comm₂₃ := by simpa only [comp_id] using hm }
  have hext : h₁.extClass.comp (Ext.mk₀ e) (add_zero 1) = h₁.extClass := by
    have hn := h₁.extClass_naturality h₂ φ
    change h₁.extClass.comp (Ext.mk₀ e) (add_zero 1) =
      (Ext.mk₀ (𝟙 B)).comp h₂.extClass (zero_add 1) at hn
    simpa only [Ext.mk₀_id_comp, ← h] using hn
  have hcorrection : h₁.extClass.comp (Ext.mk₀ (𝟙 A - e)) (add_zero 1) = 0 := by
    rw [sub_eq_add_neg, Ext.mk₀_add, Ext.mk₀_neg, Ext.comp_add,
      Ext.comp_neg, Ext.comp_mk₀_id, hext, add_neg_cancel]
  obtain ⟨ρ, hρ⟩ := Ext.contravariant_sequence_exact₁ h₁ A
    (Ext.mk₀ (𝟙 A - e)) (add_zero 1) hcorrection
  obtain ⟨r, rfl⟩ := (Ext.mk₀_bijective E₁ A).surjective ρ
  have hr : i₁ ≫ r = 𝟙 A - e := by
    apply (Ext.mk₀_bijective A A).injective
    simpa only [Ext.mk₀_comp_mk₀] using hρ
  refine ⟨m + r ≫ i₂, ?_, ?_⟩
  · rw [Preadditive.comp_add, ← assoc, hr, ← he, Preadditive.sub_comp, id_comp]
    abel
  · rw [Preadditive.add_comp, assoc, w₂, Limits.comp_zero, add_zero, hm]

/-- Equal genuine extension classes are realized by an isomorphism of the
middle objects which respects both original arrows. -/
theorem exists_middle_iso_of_extClass_eq
    (h₁ : (ShortComplex.mk i₁ p₁ w₁).ShortExact)
    (h₂ : (ShortComplex.mk i₂ p₂ w₂).ShortExact)
    (h : (h₁.extClass : Ext.{w} B A 1) = h₂.extClass) :
    ∃ e : E₁ ≅ E₂, i₁ ≫ e.hom = i₂ ∧ e.hom ≫ p₂ = p₁ := by
  obtain ⟨m, hi, hp⟩ := exists_middle_map_of_extClass_eq h₁ h₂ h
  let φ : ShortComplex.mk i₁ p₁ w₁ ⟶ ShortComplex.mk i₂ p₂ w₂ :=
    { τ₁ := 𝟙 A
      τ₂ := m
      τ₃ := 𝟙 B
      comm₁₂ := by simpa only [id_comp] using hi.symm
      comm₂₃ := by simpa only [comp_id] using hp }
  have : IsIso m := ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ φ h₁ h₂
  exact ⟨asIso m, hi, hp⟩

theorem extClass_eq_iff_exists_middle_iso
    (h₁ : (ShortComplex.mk i₁ p₁ w₁).ShortExact)
    (h₂ : (ShortComplex.mk i₂ p₂ w₂).ShortExact) :
    (h₁.extClass : Ext.{w} B A 1) = h₂.extClass ↔
      ∃ e : E₁ ≅ E₂, i₁ ≫ e.hom = i₂ ∧ e.hom ≫ p₂ = p₁ := by
  constructor
  · exact exists_middle_iso_of_extClass_eq h₁ h₂
  · rintro ⟨e, hi, hp⟩
    exact extClass_eq_of_middle_map h₁ h₂ e.hom hi hp

end Wikipedia.HopfProblem.HolomorphicPicard.ExtExtensions
