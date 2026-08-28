import Wikipedia.HopfProblem.DegreeCollapseRelativeSurgeryCutTransport

/-!
# Realize a relative family move and identify its exact lower endpoint maps

The old and modified complete flows transport the same upper parameter
maps to the original lower cut. The modified endpoint is exactly the old
flow transport after the level diffeomorphism. Every protected parameter
is unchanged at the lower cut, and the whole labelled basin families and
all lower critical basins are retained.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse SupportedDiffeomorph

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open MorseRearrangement

local notation "S₂" => Hemisphere.Sphere 2

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.exists_relative_family_lower_transport
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : IsMorse E f) (q : criticalPoints E f) (hq : nativeMorseIndex E f q = 3)
    {n : ℕ} (p : Fin n → criticalPoints E f) (i : Fin n)
    (hhigh : ∀ j, S.toSurgeryWindows.upper q < f (p j))
    (α : Fin n → C(S₂, (S.data q).UpperLevel))
    (hα : IsNativeMiddleBasinFamily S hf (S.data q).upper_regular p (fun j => α j))
    (havoid : ∀ j, Disjoint (range (α j)) (range (S.data q).surgery.beltSphere))
    (ε : criticalPoints E f → ℝ) (hε : ∀ z, 0 < ε z) :
    let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
    ∀ (D : Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
        (S.data q).UpperLevel (S.data q).UpperLevel ∞)
      (K : Set (S.data q).UpperLevel), IsCompact K →
      SupportedRelativeIsotopy D K (otherSheetImages (fun j => α j) i) →
      (∀ j, Disjoint (range (D ∘ α j)) (range (S.data q).surgery.beltSphere)) →
      ∃ T : AdaptedSurgeryWindows E f,
        (∀ z, (T.data z).chart = (S.data z).chart) ∧
        (∀ z, (T.data z).radius < ε z) ∧
        (∀ z ∈ criticalPoints E f, ∀ᶠ y in 𝓝 z, T.field y = S.field y) ∧
        ∃ β δ : Fin n → C(S₂, (S.data q).LowerLevel),
          IsNativeMiddleBasinFamily S hf (S.data q).lower_regular p (fun j => β j) ∧
          IsNativeMiddleBasinFamily T hf (S.data q).lower_regular p (fun j => δ j) ∧
          (∀ j x, ∃ t : ℝ, S.flow t (α j x).val = (β j x).val) ∧
          (∀ j x, ∃ t : ℝ, T.flow t (α j x).val = (δ j x).val) ∧
          (∀ j x, ∃ t : ℝ, S.flow t (D (α j x)).val = (δ j x).val) ∧
          (∀ j, j ≠ i → δ j = β j) ∧
          (∀ j, j ≠ i → ∀ x,
            range (fun t => T.flow t (α j x).val) = range (fun t => S.flow t (α j x).val)) ∧
          ∀ z : M, f z ≤ f q →
            (∀ x, Tendsto (fun t => T.flow t x) atBot (𝓝 z) ↔
              Tendsto (fun t => S.flow t x) atBot (𝓝 z)) ∧
            (∀ x, Tendsto (fun t => S.flow t x) atBot (𝓝 z) →
              range (fun t => T.flow t x) = range (fun t => S.flow t x)) ∧
            ∀ v, Tendsto (fun t => T.flow t z) atTop (𝓝 v) ↔
              Tendsto (fun t => S.flow t z) atTop (𝓝 v) := by
  let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
  let _ := RegularLevel.chartedSpace hf (S.data q).lower_regular
  let _ : Fact (Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 2 + 1) :=
    ⟨(nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hq⟩
  dsimp only
  intro D K hK I hDavoid
  let x₀ : S₂ := Hemisphere.point true ⟨0, by simp⟩
  let u := SphereCoordinates.standardParametrization (S.data q).chart.NegativeCoordinates 2 x₀
  obtain ⟨T, hcharts, hradii, hgerms, hback, hforward, hprotected, hcut, hkeep⟩ :=
    S.exists_relative_surgery_cut_transport hf hm q (α i x₀) ε hε D K
      (otherSheetImages (fun j => α j) i) hK I
  obtain ⟨hs, he, hi, hpair, hfull⟩ := hα
  have holdreach (j : Fin n) (x : S₂) :=
    S.belt_complement_reaches_lower_level hf q (α j x)
      (fun h => Set.disjoint_left.mp (havoid j) (mem_range_self x) h)
  have hnewreach (j : Fin n) (x : S₂) :=
    S.reaches_old_lower_of_belt_avoidance T hf q D hforward (α j x)
      (fun h => Set.disjoint_left.mp (hDavoid j) (mem_range_self x) h)
  obtain ⟨β₀, hβs, hβe, hβi, hβpair, hβflow⟩ := S.exists_native_family_level_transport hf
    (S.data q).upper_regular (S.data q).lower_regular (α i x₀)
      ((S.data q).surgery.attachingSphere u) (fun j => α j) hs
      (fun j => (he j).injective) hi hpair holdreach
  obtain ⟨δ₀, hδs, hδe, hδi, hδpair, hδflow⟩ := T.exists_native_family_level_transport hf
    (S.data q).upper_regular (S.data q).lower_regular (α i x₀)
      ((S.data q).surgery.attachingSphere u) (fun j => α j) hs
      (fun j => (he j).injective) hi hpair hnewreach
  let β : Fin n → C(S₂, (S.data q).LowerLevel) := fun j => ⟨β₀ j, (hβs j).continuous⟩
  let δ : Fin n → C(S₂, (S.data q).LowerLevel) := fun j => ⟨δ₀ j, (hδs j).continuous⟩
  have hδold (j : Fin n) (x : S₂) : ∃ t : ℝ, S.flow t (D (α j x)).val = (δ j x).val :=
    (hcut (α j x) (S.toSurgeryWindows.lower_lt_value q)
      (S.data q).lower_regular (δ j x)).mp (hδflow j x)
  have hab := (S.toSurgeryWindows.lower_lt_value q).trans (S.toSurgeryWindows.value_lt_upper q)
  refine ⟨T, hcharts, hradii, hgerms, β, δ, ?_, ?_, hβflow, hδflow, hδold, ?_, ?_, hkeep⟩
  · refine ⟨hβs, hβe, hβi, hβpair, ?_⟩
    intro j
    exact S.transported_backward_basin_image hf hab (S.data q).lower_regular
      (p j).val (hhigh j) (α j) (β j) (hfull j) (hβflow j)
  · refine ⟨hδs, hδe, hδi, hδpair, ?_⟩
    intro j
    apply T.transported_backward_basin_image hf hab (S.data q).lower_regular
      (p j).val (hhigh j) (α j) (δ j) ?_ (hδflow j)
    intro x
    exact (hfull j x).trans (hback x (p j).val).symm
  · intro j hji
    apply ContinuousMap.ext
    intro x
    obtain ⟨s, hs⟩ := hδold j x
    have hfix : D (α j x) = α j x :=
      I.endpoint_fixed_on (α j x) (mem_otherSheetImages (fun j => α j) i j hji x)
    rw [hfix] at hs
    obtain ⟨t, ht⟩ := hβflow j x
    change S.flow t (α j x).val = (β j x).val at ht
    have hshared : S.flow 0 (δ j x).val = S.flow (s - t) (β j x).val := by
      rw [S.flow.map_zero_apply, ← hs, ← ht, ← S.flow.map_add, sub_add_cancel]
    apply Subtype.ext
    exact native_same_level_orbit_points hf S.smooth S.flow S.integral
      (fun z hz => S.descent z ((S.data q).lower_regular z hz))
      (δ j x).property (β j x).property hshared
  · intro j hji x
    exact hprotected (α j x) (mem_otherSheetImages (fun j => α j) i j hji x)

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
