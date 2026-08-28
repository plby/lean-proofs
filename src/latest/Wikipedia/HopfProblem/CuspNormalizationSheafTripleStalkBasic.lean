import Wikipedia.HopfProblem.CuspNormalizationSheafCuspSums
import Wikipedia.HopfProblem.CuspNormalizationSheafBiproduct
import Wikipedia.HopfProblem.CuspNormalizationSheafTripleStalkSkyscraper

/-!
# Actual stalks of the two triple-point skyscrapers

The last term of the resolution is the actual categorical direct sum
of the skyscrapers at the two distinct actual triple points. Its stalk
at either support is canonically the scalar group, through the actual
biproduct projection. Away from both points its actual stalk is zero.
-/

noncomputable section

open Set TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite
open scoped ContDiff AlgebraicGeometry

namespace Wikipedia.HopfProblem.CuspNormalization.SheafResolution

open CuspQuotient ToricCharts ToricSpace

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
  (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

local notation "Base" => TopCat.of (CentralSpace C ε)
local notation "A" => triplePointSheaf C ε hε
local notation "p" => triplePoint C ε hε

include hε1 hC hR in
/-- Each actual point skyscraper has zero stalk away from its support. -/
theorem triplePointSheaf_stalk_isZero (t : Fin 2) (x : CentralSpace C ε)
    (hx : x ≠ p t) : IsZero ((A t).presheaf.stalk x) := by
  let := CuspQuotient.quotient_t2Space C ε hε hε1 hC hR
  exact SheafTripleStalk.skyscraper_stalk_isZero_of_ne (X := Base)
    (p t) x (AddCommGrpCat.of ℂ) hx

/-- The actual projection to the supported summand, followed by the
canonical stalk evaluation of its actual skyscraper. -/
def tripleStalkProjectionHom (t : Fin 2) :
    (tripleSheaf C ε hε).presheaf.stalk (p t) ⟶ AddCommGrpCat.of ℂ :=
  (SheafBiproduct.stalkFunctor Base (p t)).map (biproduct.π A t) ≫
    (SheafEvaluation.skyscraperStalkIso (X := Base) (p t) (AddCommGrpCat.of ℂ)).hom

/-- The actual inclusion of the supported skyscraper stalk in the
stalk of the categorical direct sum. -/
def tripleStalkInclusionHom (t : Fin 2) :
    AddCommGrpCat.of ℂ ⟶ (tripleSheaf C ε hε).presheaf.stalk (p t) :=
  (SheafEvaluation.skyscraperStalkIso (X := Base) (p t) (AddCommGrpCat.of ℂ)).inv ≫
    (SheafBiproduct.stalkFunctor Base (p t)).map (biproduct.ι A t)

/-- The actual supported summand is a retraction of the direct-sum stalk. -/
@[reassoc (attr := simp)] theorem tripleStalkInclusion_projection (t : Fin 2) :
    tripleStalkInclusionHom C ε hε t ≫ tripleStalkProjectionHom C ε hε t =
      𝟙 (AddCommGrpCat.of ℂ) := by
  have h : (SheafBiproduct.stalkFunctor Base (p t)).map (biproduct.ι A t) ≫
      (SheafBiproduct.stalkFunctor Base (p t)).map (biproduct.π A t) =
        𝟙 ((A t).presheaf.stalk (p t)) := by
    rw [← Functor.map_comp, biproduct.ι_π_self]
    exact (SheafBiproduct.stalkFunctor Base (p t)).map_id _
  let q : (A t).presheaf.stalk (p t) ≅ AddCommGrpCat.of ℂ :=
    SheafEvaluation.skyscraperStalkIso (X := Base) (p t) (AddCommGrpCat.of ℂ)
  let i : (A t).presheaf.stalk (p t) ⟶ (tripleSheaf C ε hε).presheaf.stalk (p t) :=
    (SheafBiproduct.stalkFunctor Base (p t)).map (biproduct.ι A t)
  let r : (tripleSheaf C ε hε).presheaf.stalk (p t) ⟶ (A t).presheaf.stalk (p t) :=
    (SheafBiproduct.stalkFunctor Base (p t)).map (biproduct.π A t)
  have hi : i ≫ r = 𝟙 ((A t).presheaf.stalk (p t)) := h
  change (q.inv ≫ i) ≫ r ≫ q.hom = _
  rw [Category.assoc, ← Category.assoc i r q.hom, hi, Category.id_comp, q.inv_hom_id]

theorem tripleStalkProjection_surjective (t : Fin 2) :
    Function.Surjective (tripleStalkProjectionHom C ε hε t) := by
  intro c
  refine ⟨tripleStalkInclusionHom C ε hε t c, ?_⟩
  exact ConcreteCategory.congr_hom (tripleStalkInclusion_projection C ε hε t) c

include hε1 hC hR in
/-- All unsupported coordinates are zero, so the actual projection
also detects equality of stalk elements. -/
theorem tripleStalkProjection_injective (t : Fin 2) :
    Function.Injective (tripleStalkProjectionHom C ε hε t) := by
  intro u v huv
  apply (SheafBiproduct.finiteStalkEquiv Base A (p t)).injective
  funext k
  by_cases hkt : k = t
  · subst k
    apply (SheafEvaluation.skyscraperStalkIso (X := Base) (p t)
      (AddCommGrpCat.of ℂ)).addCommGroupIsoToAddEquiv.injective
    rw [SheafBiproduct.finiteStalkEquiv_apply, SheafBiproduct.finiteStalkEquiv_apply]
    change tripleStalkProjectionHom C ε hε t u = tripleStalkProjectionHom C ε hε t v
    exact huv
  · let := AddCommGrpCat.subsingleton_of_isZero
      (triplePointSheaf_stalk_isZero C ε hε hε1 hC hR k (p t)
        (fun heq => hkt ((triplePoint_injective C ε hε heq).symm)))
    exact Subsingleton.elim _ _

/-- The actual last sheaf's stalk at either triple point is the scalar
group, through the actual categorical projection to that support. -/
def tripleStalkEquiv (t : Fin 2) :
    (tripleSheaf C ε hε).presheaf.stalk (p t) ≃+ ℂ :=
  AddEquiv.ofBijective (tripleStalkProjectionHom C ε hε t).hom
    ⟨tripleStalkProjection_injective C ε hε hε1 hC hR t,
      tripleStalkProjection_surjective C ε hε t⟩

@[simp] theorem tripleStalkEquiv_apply (t : Fin 2)
    (u : (tripleSheaf C ε hε).presheaf.stalk (p t)) :
    tripleStalkEquiv C ε hε hε1 hC hR t u =
      (SheafEvaluation.skyscraperStalkIso (X := Base) (p t) (AddCommGrpCat.of ℂ)).hom
        ((SheafBiproduct.stalkFunctor Base (p t)).map (biproduct.π A t) u) := rfl

/-- The scalar is the actual supported component of a genuine section
germ, under the genuine neighborhood identification of the skyscraper. -/
@[simp] theorem tripleStalkEquiv_germ (t : Fin 2) (U : Opens (CentralSpace C ε))
    (ht : p t ∈ U) (u : (tripleSheaf C ε hε).obj.obj (op U)) :
    tripleStalkEquiv C ε hε hε1 hC hR t
      ((tripleSheaf C ε hε).presheaf.germ U (p t) ht u) =
      (SheafEvaluation.skyscraperSectionIso (X := Base) (p t) (AddCommGrpCat.of ℂ) U ht).hom
        ((biproduct.π A t).hom.app (op U) u) := by
  rw [tripleStalkEquiv_apply]
  change (SheafEvaluation.skyscraperStalkIso (X := Base) (p t) (AddCommGrpCat.of ℂ)).hom
    ((TopCat.Presheaf.stalkFunctor AddCommGrpCat (p t)).map
      (biproduct.π A t).hom ((tripleSheaf C ε hε).presheaf.germ U (p t) ht u)) = _
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  exact ConcreteCategory.congr_hom
    (SheafEvaluation.germ_skyscraperStalkIso_hom
      (X := Base) (p t) (AddCommGrpCat.of ℂ) U ht) _

include hε1 hC hR in
/-- Away from both actual supports, the actual last stalk is zero. -/
theorem tripleSheaf_stalk_isZero (x : CentralSpace C ε) (hx : ∀ t : Fin 2, x ≠ p t) :
    IsZero ((tripleSheaf C ε hε).presheaf.stalk x) := by
  have hs : Subsingleton ((tripleSheaf C ε hε).presheaf.stalk x) := by
    refine ⟨fun u v => (SheafBiproduct.finiteStalkEquiv Base A x).injective ?_⟩
    funext t
    let := AddCommGrpCat.subsingleton_of_isZero
      (triplePointSheaf_stalk_isZero C ε hε hε1 hC hR t x (hx t))
    exact Subsingleton.elim _ _
  let := hs
  exact AddCommGrpCat.isZero_of_subsingleton _

include hε1 hC hR in
/-- Equivalent off-support formulation using the source's names `P,Q`. -/
theorem tripleSheaf_stalk_isZero_of_ne (x : CentralSpace C ε)
    (hxP : x ≠ pointP C ε hε) (hxQ : x ≠ pointQ C ε hε) :
    IsZero ((tripleSheaf C ε hε).presheaf.stalk x) := by
  apply tripleSheaf_stalk_isZero C ε hε hε1 hC hR x
  intro t
  fin_cases t
  · exact hxP
  · exact hxQ

end Wikipedia.HopfProblem.CuspNormalization.SheafResolution
