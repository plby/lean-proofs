import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalCuspCoordinates

/-!
# Extending an actual punctured scalar by its analytic base germ

This elementary analytic gluing lemma keeps the original manifold atlas.
Agreement is required only in a neighborhood of parameter zero, and is
uniform over the full fibres there.  Away from zero the given holomorphic
function is unchanged; on the zero fibre its forced limiting value is used.
-/

noncomputable section

open Set Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalCuspExtension

section Gluing

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace M] [ChartedSpace E M]

local notation "IM" => modelWithCornersSelf ℂ E
local notation "I₁" => modelWithCornersSelf ℂ ℂ

/-- Fill the zero fibre, without changing the function at any punctured point. -/
def fillAcrossZero (p : M → ℂ) (U : TopologicalSpace.Opens M)
    (hU : ∀ y : M, y ∈ U ↔ p y ≠ 0) (r : U → ℂ) (c : ℂ) (y : M) : ℂ :=
  if hy : p y = 0 then c else r ⟨y, (hU y).mpr hy⟩

theorem fillAcrossZero_of_zero (p : M → ℂ) (U : TopologicalSpace.Opens M)
    (hU : ∀ y : M, y ∈ U ↔ p y ≠ 0) (r : U → ℂ) (c : ℂ)
    {y : M} (hy : p y = 0) : fillAcrossZero p U hU r c y = c := by
  simp [fillAcrossZero, hy]

theorem fillAcrossZero_on_open (p : M → ℂ) (U : TopologicalSpace.Opens M)
    (hU : ∀ y : M, y ∈ U ↔ p y ≠ 0) (r : U → ℂ) (c : ℂ) (y : U) :
    fillAcrossZero p U hU r c y = r y := by
  have hy := (hU y.val).mp y.property
  simp [fillAcrossZero, hy]

/-- The filled scalar agrees with the actual analytic base expression near the zero fibre. -/
theorem fillAcrossZero_eventually_eq (p : M → ℂ) (U : TopologicalSpace.Opens M)
    (hU : ∀ y : M, y ∈ U ↔ p y ≠ 0) (r : U → ℂ) (g : ℂ → ℂ)
    (hp : Continuous p)
    (hagree : ∀ᶠ q : ℂ in 𝓝 0, ∀ y : U, p y.val = q → r y = g q)
    {y : M} (hy : p y = 0) :
    fillAcrossZero p U hU r (g 0) =ᶠ[𝓝 y] g ∘ p := by
  have ht : Tendsto p (𝓝 y) (𝓝 (0 : ℂ)) := by
    rw [← hy]
    exact hp.continuousAt
  filter_upwards [ht.eventually hagree] with z hz
  by_cases hz0 : p z = 0
  · rw [fillAcrossZero_of_zero p U hU r (g 0) hz0]
    simp only [Function.comp_apply, hz0]
  · simp only [fillAcrossZero, dif_neg hz0, Function.comp_apply]
    exact hz ⟨z, (hU z).mpr hz0⟩ rfl

/-- The gluing is holomorphic for the original atlas, using no extension theorem as input. -/
theorem fillAcrossZero_holomorphic (p : M → ℂ) (U : TopologicalSpace.Opens M)
    (hU : ∀ y : M, y ∈ U ↔ p y ≠ 0) (r : U → ℂ) (g : ℂ → ℂ)
    (hp : ContMDiff IM I₁ ω p) (hr : ContMDiff IM I₁ ω r) (hg : AnalyticAt ℂ g 0)
    (hagree : ∀ᶠ q : ℂ in 𝓝 0, ∀ y : U, p y.val = q → r y = g q) :
    ContMDiff IM I₁ ω (fillAcrossZero p U hU r (g 0)) := by
  intro y
  by_cases hy : p y = 0
  · have hgy : ContMDiffAt I₁ I₁ ω g (p y) := by
      rw [hy]
      exact hg.contDiffAt.contMDiffAt
    exact (hgy.comp y (hp y)).congr_of_eventuallyEq
      (fillAcrossZero_eventually_eq p U hU r g hp.continuous hagree hy)
  · have hs : ContMDiffAt IM I₁ ω
        (fun z : U => fillAcrossZero p U hU r (g 0) z.val) ⟨y, (hU y).mpr hy⟩ := by
      apply (hr ⟨y, (hU y).mpr hy⟩).congr_of_eventuallyEq
      exact Filter.Eventually.of_forall (fillAcrossZero_on_open p U hU r (g 0))
    exact contMDiffAt_subtype_iff.mp hs

/-- Nonvanishing on the punctured domain and at the central value gives nonvanishing everywhere. -/
theorem fillAcrossZero_ne_zero (p : M → ℂ) (U : TopologicalSpace.Opens M)
    (hU : ∀ y : M, y ∈ U ↔ p y ≠ 0) (r : U → ℂ) (c : ℂ)
    (hr : ∀ y : U, r y ≠ 0) (hc : c ≠ 0) (y : M) :
    fillAcrossZero p U hU r c y ≠ 0 := by
  by_cases hy : p y = 0
  · rw [fillAcrossZero_of_zero p U hU r c hy]
    exact hc
  · simp only [fillAcrossZero, dif_neg hy]
    exact hr ⟨y, (hU y).mpr hy⟩

end Gluing

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.GlobalCuspExtension
