import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsResolutionInitial
import Wikipedia.HopfProblem.CuspNormalizationSheafConstantsResolutionComparison

/-!
# The actual constant normalization complex and its full comparison

This is the six-object sequence with both zero endpoints, built from
the actual constant sheaf, the actual normalization and curve direct
images, and the actual two skyscrapers. Both complex identities are
proved. The termwise inclusions form a genuine morphism of the full
sequence to the holomorphic sequence, and every component is injective.
Exactness at the remaining interior terms is treated separately.
-/

noncomputable section

open Set TopologicalSpace CategoryTheory CategoryTheory.Limits
open scoped ContDiff ZeroObject

namespace Wikipedia.HopfProblem.CuspNormalization.SheafResolution

open CuspQuotient ToricCharts ToricSpace

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
  (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

/-- The entire actual constant normalization sequence, including both
zero endpoints and the source's actual signed differentials. -/
def constantResolution : ComposableArrows
    (TopCat.Sheaf AddCommGrpCat (TopCat.of (CentralSpace C ε))) 5 :=
  ComposableArrows.mk₅ (constantInitialComplex C ε hε).f
    (normalizationConstantPullback C ε hε) (constantDeltaZero C ε hε hε1 hC hR)
    (constantDeltaOne C ε hε) (constantTerminalComplex C ε hε).g

/-- Both actual nontrivial consecutive composites vanish. -/
theorem constantResolution_isComplex : (constantResolution C ε hε hε1 hC hR).IsComplex where
  zero i hi := by
    have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases h with rfl | rfl | rfl | rfl
    · exact (constantInitialComplex C ε hε).zero
    · exact (constantNormalizationComplex C ε hε hε1 hC hR).zero
    · exact (constantBoundaryComplex C ε hε hε1 hC hR).zero
    · exact (constantTerminalComplex C ε hε).zero

/-- The actual constants inclusions give a genuine morphism of all five
arrows, with identities on the two skyscrapers and on both zero endpoints. -/
def constantResolutionComparison :
    constantResolution C ε hε hε1 hC hR ⟶ resolution C ε hε hε1 hC hR :=
  ComposableArrows.homMk₅ (𝟙 _)
    (reducedConstantsMap C ε hε hε1 hC hR)
    (normalizationConstantsMap C ε hε)
    (boundaryConstantsMap C ε hε hε1 hC hR) (𝟙 _) (𝟙 _)
    (zero_comp.trans (Category.id_comp _).symm)
    (normalization_constants_naturality C ε hε hε1 hC hR).symm
    (deltaZero_constants_naturality C ε hε hε1 hC hR).symm
    ((Category.comp_id _).trans (deltaOne_constants_naturality C ε hε hε1 hC hR).symm)
    ((Category.comp_id _).trans (Category.id_comp _).symm)

@[simp] theorem constantResolutionComparison_app_zero :
    (constantResolutionComparison C ε hε hε1 hC hR).app 0 =
      𝟙 (0 : TopCat.Sheaf AddCommGrpCat (TopCat.of (CentralSpace C ε))) := rfl

@[simp] theorem constantResolutionComparison_app_one :
    (constantResolutionComparison C ε hε hε1 hC hR).app 1 =
      reducedConstantsMap C ε hε hε1 hC hR := rfl

@[simp] theorem constantResolutionComparison_app_two :
    (constantResolutionComparison C ε hε hε1 hC hR).app 2 =
      normalizationConstantsMap C ε hε := rfl

@[simp] theorem constantResolutionComparison_app_three :
    (constantResolutionComparison C ε hε hε1 hC hR).app 3 =
      boundaryConstantsMap C ε hε hε1 hC hR := rfl

@[simp] theorem constantResolutionComparison_app_four :
    (constantResolutionComparison C ε hε hε1 hC hR).app 4 =
      𝟙 (tripleSheaf C ε hε) := rfl

@[simp] theorem constantResolutionComparison_app_five :
    (constantResolutionComparison C ε hε hε1 hC hR).app 5 =
      𝟙 (0 : TopCat.Sheaf AddCommGrpCat (TopCat.of (CentralSpace C ε))) := rfl

/-- The full actual comparison is a monomorphism: its components are
the proved constants inclusions and the actual endpoint identities. -/
instance constantResolutionComparison_mono :
    Mono (constantResolutionComparison C ε hε hε1 hC hR) := by
  let : ∀ i : Fin 6, Mono ((constantResolutionComparison C ε hε hε1 hC hR).app i) := by
    intro i
    fin_cases i
    · exact inferInstanceAs
        (Mono (𝟙 (0 : TopCat.Sheaf AddCommGrpCat (TopCat.of (CentralSpace C ε)))))
    · exact reducedConstantsMap_mono C ε hε hε1 hC hR
    · exact normalizationConstantsMap_mono C ε hε
    · exact boundaryConstantsMap_mono C ε hε hε1 hC hR
    · exact inferInstanceAs (Mono (𝟙 (tripleSheaf C ε hε)))
    · exact inferInstanceAs
        (Mono (𝟙 (0 : TopCat.Sheaf AddCommGrpCat (TopCat.of (CentralSpace C ε)))))
  exact NatTrans.mono_of_mono_app (constantResolutionComparison C ε hε hε1 hC hR)

end Wikipedia.HopfProblem.CuspNormalization.SheafResolution
