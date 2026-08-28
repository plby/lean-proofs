import Wikipedia.HopfProblem.ConstantSheafSingularComparisonGlobalKernelLocal
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonSmallCochainDetection

/-!
# The actual global-unit kernel detected on small singular chains

The original cochain becomes zero under the native sheafification unit
exactly when it vanishes on all chains small for some genuine open cover.
This connects the actual sheaf map to the original small-chain complex.
-/

noncomputable section

open Set TopologicalSpace CategoryTheory Opposite

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison

open FirstHurewicz

variable (X : TopCat.{0}) (A : AddCommGrpCat.{0}) (n : ℕ)

/-- Restriction to small chains vanishes exactly when the original
cochain restricts to zero on every member of the open family. -/
theorem smallCochainRestriction_eq_zero_iff_restrictions
    {ι : Type} (U : ι → Opens X) (φ : Cochains X A n) :
    (smallCochainRestriction A (fun i => (U i : Set X))).f n φ = 0 ↔
      ∀ i, restrictGlobalCochain A n φ (U i) = 0 := by
  constructor
  · intro h i
    apply cochain_ext (U i) A n
    intro σ
    let τ : SingularSimplex X n :=
      (⟨Subtype.val, continuous_subtype_val⟩ : C(U i, X)).comp σ
    have hτ : ∃ j, range τ ⊆ (U j : Set X) := by
      refine ⟨i, ?_⟩
      rintro _ ⟨z, rfl⟩
      exact (σ z).property
    exact (restrictGlobalCochain_simplex A n φ (U i) σ).trans
      ((smallCochainRestriction_eq_zero_iff A (fun j => (U j : Set X)) n φ).mp h τ hτ)
  · intro h
    apply (smallCochainRestriction_eq_zero_iff A (fun i => (U i : Set X)) n φ).mpr
    intro σ hσ
    obtain ⟨i, hi⟩ := hσ
    let σ' := simplexInOpen n σ (U i) hi
    have hv := congrArg
      (fun ψ : Cochains (U i) A n => ψ (simplexChain (U i) n σ')) (h i)
    exact (restrictGlobalCochain_simplex A n φ (U i) σ').symm.trans hv

/-- Vanishing on the small chains of an actual open cover forces the
native sheafification image of the original cochain to vanish. -/
theorem globalCochainUnit_eq_zero_of_smallRestriction
    {ι : Type} (U : ι → Opens X) (hcover : ∀ x : X, ∃ i, x ∈ U i)
    (φ : Cochains X A n)
    (hφ : (smallCochainRestriction A (fun i => (U i : Set X))).f n φ = 0) :
    globalCochainUnit X A n φ = 0 := by
  apply globalCochainUnit_eq_zero_of_local X A n φ
  intro x
  obtain ⟨i, hi⟩ := hcover x
  exact ⟨U i, hi, (smallCochainRestriction_eq_zero_iff_restrictions X A n U φ).mp hφ i⟩

/-- An actual kernel element vanishes on the small chains for some
genuine point-indexed open cover of the original space. -/
theorem exists_cover_smallRestriction_eq_zero (φ : Cochains X A n)
    (hφ : globalCochainUnit X A n φ = 0) :
    ∃ U : X → Opens X, (∀ x : X, x ∈ U x) ∧
      (smallCochainRestriction A (fun x => (U x : Set X))).f n φ = 0 := by
  classical
  choose U hxU hU using globalCochainUnit_locally_zero X A n φ hφ
  exact ⟨U, hxU, (smallCochainRestriction_eq_zero_iff_restrictions X A n U φ).mpr hU⟩

/-- The exact actual kernel criterion used by the singular comparison. -/
theorem globalCochainUnit_eq_zero_iff_smallCover (φ : Cochains X A n) :
    globalCochainUnit X A n φ = 0 ↔
      ∃ U : X → Opens X, (∀ x : X, x ∈ U x) ∧
        (smallCochainRestriction A (fun x => (U x : Set X))).f n φ = 0 := by
  constructor
  · exact exists_cover_smallRestriction_eq_zero X A n φ
  · rintro ⟨U, hxU, hU⟩
    exact globalCochainUnit_eq_zero_of_smallRestriction X A n U
      (fun x => ⟨x, hxU x⟩) φ hU

end Wikipedia.HopfProblem.ConstantSheafSingularComparison
