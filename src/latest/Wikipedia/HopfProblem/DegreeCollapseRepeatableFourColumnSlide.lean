import Wikipedia.HopfProblem.DegreeCollapseSlideWindowInvariants
import Wikipedia.HopfProblem.DegreeCollapseCommonCutFourFamilySlide

/-!
# A prescribed four-handle column slide retains its original cut conditions

Request radii below the old radii. The actual new system keeps the same
common cut, a regular lower band, and separation from every higher label,
as well as the original central map and all protected sphere parameters.
-/

noncomputable section

open Set Function Filter Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

local notation "S₃" => Hemisphere.Sphere 3

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.exists_repeatable_four_column_slide
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : IsMorse E f) (hdim : Module.finrank ℝ E = 7)
    (q : criticalPoints E f) (hq : nativeMorseIndex E f q = 4)
    (hprefix : ∀ j : Fin S.toSurgeryWindows.count, 0 < j.val →
      f (S.toSurgeryWindows.point j) ≤ f q →
      Module.finrank ℝ (S.data (S.toSurgeryWindows.point j)).chart.NegativeCoordinates = 3 ∨
      Module.finrank ℝ (S.data (S.toSurgeryWindows.point j)).chart.NegativeCoordinates = 4)
    {a : ℝ} (ha : ∀ y, f y = a → y ∉ criticalPoints E f)
    (hal : a < S.toSurgeryWindows.lower q)
    (hband : ∀ y, f y ∈ Icc a (S.toSurgeryWindows.lower q) → y ∉ criticalPoints E f)
    {n : ℕ} (p : Fin n → criticalPoints E f) (i : Fin n)
    (hp : ∀ j, nativeMorseIndex E f (p j) = 4)
    (hhigh : ∀ j, S.toSurgeryWindows.upper q < f (p j))
    (αq : C(S₃, {y : M // f y = a})) (α : Fin n → C(S₃, {y : M // f y = a}))
    (hfamily : IsNativeFourBasinFamily S hf ha (Fin.cases q p)
      (Fin.cases αq (fun j => α j)))
    (k : ℤ) (hk : k = 1 ∨ k = -1) :
    ∃ T : AdaptedSurgeryWindows E f,
      (∀ z, (T.data z).chart = (S.data z).chart) ∧
      (∀ z, (T.data z).radius ≤ (S.data z).radius) ∧
      (∀ z ∈ criticalPoints E f, ∀ᶠ y in 𝓝 z, T.field y = S.field y) ∧
      a < T.toSurgeryWindows.lower q ∧
      (∀ y, f y ∈ Icc a (T.toSurgeryWindows.lower q) → y ∉ criticalPoints E f) ∧
      (∀ j, T.toSurgeryWindows.upper q < f (p j)) ∧
      ∃ Γ : Fin n → C(S₃, {y : M // f y = a}),
        IsNativeFourBasinFamily T hf ha (Fin.cases q p) (Fin.cases αq (fun j => Γ j)) ∧
        (∀ j, j ≠ i → Γ j = α j) ∧
        (threeSectionClass (Γ i) = threeSectionClass (α i) + k • threeSectionClass αq) ∧
        ∀ z : M, f z ≤ f q →
          (∀ x, Tendsto (fun t => T.flow t x) atBot (𝓝 z) ↔
            Tendsto (fun t => S.flow t x) atBot (𝓝 z)) ∧
          (∀ x, Tendsto (fun t => S.flow t x) atBot (𝓝 z) →
            range (fun t => T.flow t x) = range (fun t => S.flow t x)) ∧
          ∀ v, Tendsto (fun t => T.flow t z) atTop (𝓝 v) ↔
            Tendsto (fun t => S.flow t z) atTop (𝓝 v) := by
  obtain ⟨T, hcharts, hradii, hgerms, Γ, hΓ, hother, hclass, hkeep⟩ :=
    S.exists_common_cut_four_family_slide hf hm hdim q hq hprefix ha hal hband p i hp hhigh
      αq α hfamily k hk (fun z => (S.data z).radius) (fun z => (S.data z).radius_pos)
  obtain ⟨hcut, hregular⟩ := common_cut_band_of_smaller_radius S.toSurgeryWindows
    T.toSurgeryWindows q hal hband (hradii q).le
  have hseparated : ∀ j, T.toSurgeryWindows.upper q < f (p j) :=
    fun j => higher_window_separation_of_value_order S.toSurgeryWindows T.toSurgeryWindows
      q (p j) (hhigh j)
  exact ⟨T, hcharts, fun z => (hradii z).le, hgerms, hcut, hregular, hseparated,
    Γ, hΓ, hother, hclass, hkeep⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

