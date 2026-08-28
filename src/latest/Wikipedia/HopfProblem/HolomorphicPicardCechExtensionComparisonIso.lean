import Wikipedia.HopfProblem.HolomorphicPicardCechExtensionComparisonMaps
import Wikipedia.HopfProblem.HolomorphicPicardCechExtensionExact

/-!
# The actual comparison isomorphism of extensions

The glued comparison fixes both original endpoints. Short exactness of
the actual cocycle extension and the given extension therefore makes
this same map an isomorphism by the short five lemma. Both directions
commute with the original inclusions and projections.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.HolomorphicPicard.CechExtension

open HolomorphicFunctionSheaf.SphereH1

variable {X : TopCat.{0}} {F G : TopCat.Sheaf AddCommGrpCat.{0} X}
  {ι : Type} {U : ι → Opens X} (c : CechOneCocycle F U)
  (hU : ∀ x : X, ∃ j : ι, x ∈ U j)
  (i : F ⟶ G) (p : G ⟶ degreeSheaf X) (hz : i ≫ p = 0)
  (t : ∀ j : ι, Section G (U j))
  (hp : ∀ j : ι, p.hom.app (op (U j)) (t j) =
    (degreeUnit X).app (op (U j)) (ULift.up (1 : ℤ)))
  (hdiff : ∀ j k : ι,
    res G inf_le_right (t k) - res G inf_le_left (t j) =
      i.hom.app (op (U j ⊓ U k)) (c.value j k))

include hp in
/-- The actual glued middle map is invertible, since its two endpoint
maps are identities between short exact sequences. -/
theorem comparison_isIso (hS : (ShortComplex.mk i p hz).ShortExact) :
    IsIso (comparison c hU i t hdiff) := by
  let φ := comparisonComplexMap c hU i p hz t hp hdiff
  have h₁ : IsIso φ.τ₁ := by
    change IsIso (𝟙 F)
    infer_instance
  have h₃ : IsIso φ.τ₃ := by
    change IsIso (𝟙 (degreeSheaf X))
    infer_instance
  exact ShortComplex.isIso₂_of_shortExact_of_isIso₁₃'
    φ (complex_shortExact c hU) hS h₁ h₃

/-- The original extension is reconstructed by the cocycle of the actual
local degree-one lifts, using the actual glued comparison as its map. -/
def comparisonIso (hS : (ShortComplex.mk i p hz).ShortExact) :
    extensionSheaf c ≅ G := by
  letI : IsIso (comparison c hU i t hdiff) :=
    comparison_isIso c hU i p hz t hp hdiff hS
  exact asIso (comparison c hU i t hdiff)

variable (hS : (ShortComplex.mk i p hz).ShortExact)

@[simp] theorem comparisonIso_hom :
    (comparisonIso c hU i p hz t hp hdiff hS).hom =
      comparison c hU i t hdiff := rfl

/-- The comparison is the identity on the original kernel endpoint. -/
theorem inclusion_comparisonIso_hom :
    inclusion c ≫ (comparisonIso c hU i p hz t hp hdiff hS).hom = i := by
  have h := (comparisonComplexMap c hU i p hz t hp hdiff).comm₁₂
  change (𝟙 F) ≫ i = inclusion c ≫ comparison c hU i t hdiff at h
  change inclusion c ≫ comparison c hU i t hdiff = i
  simpa only [Category.id_comp] using h.symm

/-- The comparison is the identity on the native integer quotient. -/
theorem comparisonIso_hom_projection :
    (comparisonIso c hU i p hz t hp hdiff hS).hom ≫ p = projection c := by
  have h := (comparisonComplexMap c hU i p hz t hp hdiff).comm₂₃
  change comparison c hU i t hdiff ≫ p = projection c ≫ (𝟙 (degreeSheaf X)) at h
  change comparison c hU i t hdiff ≫ p = projection c
  simpa only [Category.comp_id] using h

/-- The actual inverse respects the original kernel inclusion. -/
theorem inclusion_comparisonIso_inv :
    i ≫ (comparisonIso c hU i p hz t hp hdiff hS).inv = inclusion c := by
  let e := comparisonIso c hU i p hz t hp hdiff hS
  calc
    i ≫ e.inv = (inclusion c ≫ e.hom) ≫ e.inv :=
      congrArg (fun f => f ≫ e.inv)
        (inclusion_comparisonIso_hom c hU i p hz t hp hdiff hS).symm
    _ = inclusion c := by rw [Category.assoc, e.hom_inv_id, Category.comp_id]

/-- The actual inverse respects the original integer projection. -/
theorem comparisonIso_inv_projection :
    (comparisonIso c hU i p hz t hp hdiff hS).inv ≫ projection c = p := by
  let e := comparisonIso c hU i p hz t hp hdiff hS
  calc
    e.inv ≫ projection c = e.inv ≫ (e.hom ≫ p) :=
      congrArg (fun f => e.inv ≫ f)
        (comparisonIso_hom_projection c hU i p hz t hp hdiff hS).symm
    _ = p := by rw [← Category.assoc, e.inv_hom_id, Category.id_comp]

/-- Reconstruction is an actual isomorphism of short complexes with
literal identity maps on both original endpoints. -/
def comparisonComplexIso : complex c ≅ ShortComplex.mk i p hz := by
  refine ShortComplex.isoMk (Iso.refl F)
    (comparisonIso c hU i p hz t hp hdiff hS) (Iso.refl (degreeSheaf X)) ?_ ?_
  · change (𝟙 F) ≫ i =
      inclusion c ≫ (comparisonIso c hU i p hz t hp hdiff hS).hom
    rw [Category.id_comp, inclusion_comparisonIso_hom]
  · change (comparisonIso c hU i p hz t hp hdiff hS).hom ≫ p =
      projection c ≫ (𝟙 (degreeSheaf X))
    rw [Category.comp_id, comparisonIso_hom_projection]

@[simp] theorem comparisonComplexIso_hom :
    (comparisonComplexIso c hU i p hz t hp hdiff hS).hom =
      comparisonComplexMap c hU i p hz t hp hdiff := by
  apply ShortComplex.hom_ext <;> rfl

end Wikipedia.HopfProblem.HolomorphicPicard.CechExtension
