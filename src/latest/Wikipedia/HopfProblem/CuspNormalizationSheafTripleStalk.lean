import Wikipedia.HopfProblem.CuspNormalizationSheafTripleStalkBasic
import Wikipedia.HopfProblem.CuspNormalizationSheafTripleStalkEvaluation

/-!
# The actual last differential is surjective

At either actual triple point, the scalar identification of the last
stalk turns the actual differential into its actual alternating
evaluation. A germ on the first curve realizes any prescribed value.
Away from both triple points the target stalk is zero. Exactness on
actual sheaf stalks therefore proves exactness at the last term of the
genuine sheaf resolution, and hence the final differential is an epimorphism.
-/

noncomputable section

open Set TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite
open scoped ContDiff AlgebraicGeometry ZeroObject

namespace Wikipedia.HopfProblem.CuspNormalization.SheafResolution

open CuspQuotient ToricCharts ToricSpace

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
  (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

local notation "Base" => TopCat.of (CentralSpace C ε)
local notation "A" => triplePointSheaf C ε hε
local notation "B" => curveSheaf C ε hε hε1 hC hR
local notation "p" => triplePoint C ε hε

/-- Scalar evaluation of an actual curve-pushforward stalk at an actual
triple point, through the actual evaluation sheaf morphism. -/
def curveStalkEvaluationHom (k : Fin 3) (t : Fin 2) :
    (B k).presheaf.stalk (p t) ⟶ AddCommGrpCat.of ℂ :=
  (SheafBiproduct.stalkFunctor Base (p t)).map
      (curveEvaluation C ε hε hε1 hC hR k t) ≫
    (SheafEvaluation.skyscraperStalkIso (X := Base) (p t) (AddCommGrpCat.of ℂ)).hom

/-- Under the actual supported-stalk identification, the last map is
the actual alternating evaluation at that same triple point. -/
theorem tripleStalkEquiv_deltaOne (t : Fin 2)
    (u : (boundarySheaf C ε hε hε1 hC hR).presheaf.stalk (p t)) :
    tripleStalkEquiv C ε hε hε1 hC hR t
      ((SheafBiproduct.stalkFunctor Base (p t)).map
        (deltaOne C ε hε hε1 hC hR) u) =
      (SheafEvaluation.skyscraperStalkIso (X := Base) (p t) (AddCommGrpCat.of ℂ)).hom
        ((SheafBiproduct.stalkFunctor Base (p t)).map
          (deltaOneAt C ε hε hε1 hC hR t) u) := by
  let F := SheafBiproduct.stalkFunctor Base (p t)
  have h : F.map (deltaOne C ε hε hε1 hC hR) ≫ F.map (biproduct.π A t) =
      F.map (deltaOneAt C ε hε hε1 hC hR t) :=
    (F.map_comp (deltaOne C ε hε hε1 hC hR) (biproduct.π A t)).symm.trans
      (congrArg (fun f => F.map f) (deltaOne_component C ε hε hε1 hC hR t))
  exact congrArg
    (SheafEvaluation.skyscraperStalkIso (X := Base) (p t) (AddCommGrpCat.of ℂ)).hom
    (ConcreteCategory.congr_hom h u)

/-- The literal three-coordinate formula has exactly the source's
signs: first curve minus second curve plus third curve. -/
theorem tripleStalkEquiv_deltaOne_signed (t : Fin 2)
    (u : (boundarySheaf C ε hε hε1 hC hR).presheaf.stalk (p t)) :
    tripleStalkEquiv C ε hε hε1 hC hR t
      ((SheafBiproduct.stalkFunctor Base (p t)).map
        (deltaOne C ε hε hε1 hC hR) u) =
      curveStalkEvaluationHom C ε hε hε1 hC hR 0 t
          (SheafBiproduct.finiteStalkEquiv Base B (p t) u 0) -
        curveStalkEvaluationHom C ε hε hε1 hC hR 1 t
          (SheafBiproduct.finiteStalkEquiv Base B (p t) u 1) +
        curveStalkEvaluationHom C ε hε hε1 hC hR 2 t
          (SheafBiproduct.finiteStalkEquiv Base B (p t) u 2) := by
  rw [tripleStalkEquiv_deltaOne]
  simp only [deltaOneAt, Functor.map_add, Functor.map_sub, Functor.map_comp,
    SheafBiproduct.finiteStalkEquiv_apply]
  let F := SheafBiproduct.stalkFunctor Base (p t)
  let q : (A t).presheaf.stalk (p t) →+ ℂ :=
    (SheafEvaluation.skyscraperStalkIso (X := Base) (p t) (AddCommGrpCat.of ℂ)).hom.hom
  let w₀ : (A t).presheaf.stalk (p t) :=
    F.map (curveEvaluation C ε hε hε1 hC hR 0 t) (F.map (biproduct.π B 0) u)
  let w₁ : (A t).presheaf.stalk (p t) :=
    F.map (curveEvaluation C ε hε hε1 hC hR 1 t) (F.map (biproduct.π B 1) u)
  let w₂ : (A t).presheaf.stalk (p t) :=
    F.map (curveEvaluation C ε hε hε1 hC hR 2 t) (F.map (biproduct.π B 2) u)
  change q (w₀ - w₁ + w₂) = q w₀ - q w₁ + q w₂
  rw [map_add, map_sub]

/-- At a support point a germ on the first actual curve realizes any
element of the actual last stalk. -/
theorem deltaOne_stalk_surjective_at (t : Fin 2) :
    Function.Surjective ((SheafBiproduct.stalkFunctor Base (p t)).map
      (deltaOne C ε hε hε1 hC hR)) := by
  let F := SheafBiproduct.stalkFunctor Base (p t)
  intro v
  obtain ⟨w, hw⟩ := curveEvaluation_stalk_surjective C ε hε hε1 hC hR 0 t
    (F.map (biproduct.π A t) v)
  refine ⟨F.map (biproduct.ι B 0) w, ?_⟩
  apply (tripleStalkEquiv C ε hε hε1 hC hR t).injective
  have h : F.map (biproduct.ι B 0) ≫ F.map (deltaOneAt C ε hε hε1 hC hR t) =
      F.map (curveEvaluation C ε hε hε1 hC hR 0 t) :=
    (F.map_comp (biproduct.ι B 0) (deltaOneAt C ε hε hε1 hC hR t)).symm.trans
      (congrArg (fun f => F.map f)
        (boundary_inclusion_zero_deltaOneAt C ε hε hε1 hC hR t))
  refine (tripleStalkEquiv_deltaOne C ε hε hε1 hC hR t
    (F.map (biproduct.ι B 0) w)).trans ?_
  exact congrArg
    (SheafEvaluation.skyscraperStalkIso (X := Base) (p t) (AddCommGrpCat.of ℂ)).hom
    ((ConcreteCategory.congr_hom h w).trans hw)

/-- The genuine last differential is surjective on every actual stalk. -/
theorem deltaOne_stalk_surjective (x : CentralSpace C ε) :
    Function.Surjective ((SheafBiproduct.stalkFunctor Base x).map
      (deltaOne C ε hε hε1 hC hR)) := by
  by_cases hx : ∃ t : Fin 2, x = p t
  · obtain ⟨t, rfl⟩ := hx
    exact deltaOne_stalk_surjective_at C ε hε hε1 hC hR t
  · let : Subsingleton ((SheafBiproduct.stalkFunctor Base x).obj (tripleSheaf C ε hε)) :=
      AddCommGrpCat.subsingleton_of_isZero
      (tripleSheaf_stalk_isZero C ε hε hε1 hC hR x (fun t ht => hx ⟨t, ht⟩))
    intro v
    exact ⟨0, Subsingleton.elim _ _⟩

/-- Exactness at the last term of the actual normalization sequence,
proved by the genuine stalkwise exactness criterion. -/
theorem terminalComplex_exact : (terminalComplex C ε hε hε1 hC hR).Exact := by
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact
    (terminalComplex C ε hε hε1 hC hR)).mpr
  intro x
  let F := SheafBiproduct.stalkFunctor Base x
  have hz : ((terminalComplex C ε hε hε1 hC hR).map F).g = 0 := F.map_zero _ _
  apply (((terminalComplex C ε hε hε1 hC hR).map F).exact_iff_epi hz).mpr
  exact ConcreteCategory.epi_of_surjective _
    (deltaOne_stalk_surjective C ε hε hε1 hC hR x)

/-- The actual last differential of the sheaf resolution is an epimorphism. -/
theorem deltaOne_epi : Epi (deltaOne C ε hε hε1 hC hR) :=
  ((terminalComplex C ε hε hε1 hC hR).exact_iff_epi rfl).mp
    (terminalComplex_exact C ε hε hε1 hC hR)

end Wikipedia.HopfProblem.CuspNormalization.SheafResolution
