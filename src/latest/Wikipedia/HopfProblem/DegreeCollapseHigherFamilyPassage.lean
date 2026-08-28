import Wikipedia.HopfProblem.DegreeCollapseHigherMiddleFamily

/-!
# A higher-family passage starts from the original transported spheres

The exact common-cut orbit formulas imply that every lifted higher sheet
already misses the selected belt. No preparatory isotopy is needed. A belt
point automatically avoids every protected sheet, and native connectedness
supplies its joining path. The passage crosses the actual belt once and
fixes every other original higher sheet throughout the whole isotopy.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open MorseRearrangement

local notation "S₂" => Hemisphere.Sphere 2

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.upper_point_not_on_belt_of_lower_orbit
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (q : criticalPoints E f) {a : ℝ} (ha : a < f q)
    (x : {y : M // f y = a}) (y : (S.data q).UpperLevel)
    (horbit : ∃ t : ℝ, S.flow t x.val = y.val) :
    y ∉ range (S.data q).surgery.beltSphere := by
  intro hy
  have hyforward := (S.belt_basin_iff hf q y).mpr hy
  obtain ⟨t, ht⟩ := horbit
  have hxforward : Tendsto (fun s => S.flow s x.val) atTop (𝓝 q.val) := by
    rw [← ht] at hyforward
    exact (flow_time_atTop_limit_iff S.flow t x.val q.val).mp hyforward
  have hheight : Tendsto (fun s => f (S.flow s x.val)) atTop (𝓝 (f q)) :=
    hf.continuous.continuousAt.tendsto.comp hxforward
  have hh := (FlowConstruction.antitone_flow_height hf S.flow S.integral S.zero S.descent
    x.val).le_of_tendsto hheight 0
  have hqa : f q ≤ a := by simpa only [S.flow.map_zero_apply, x.property] using hh
  exact ha.not_ge hqa

variable [PathConnectedSpace M]

theorem AdaptedSurgeryWindows.exists_higher_family_passage
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6)
    (horder : ∀ p q : criticalPoints E f, f p < f q →
      nativeMorseIndex E f p ≤ nativeMorseIndex E f q)
    (q : criticalPoints E f) (hq : nativeMorseIndex E f q = 3)
    {a : ℝ} (ha : ∀ y, f y = a → y ∉ criticalPoints E f) (haq : a < f q)
    {n : ℕ} (p : Fin n → criticalPoints E f) (i : Fin n)
    (hp : ∀ j, nativeMorseIndex E f (p j) = 3)
    (hhigh : ∀ j, S.toSurgeryWindows.upper q < f (p j))
    (α : Fin n → C(S₂, {y : M // f y = a}))
    (hα : IsNativeMiddleBasinFamily S hf ha p (fun j => α j)) :
    let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
    let _ : Fact (Module.finrank ℝ (S.data q).chart.PositiveCoordinates = 2 + 1) :=
      ⟨by have hsplit := (S.data q).chart.finrank_negative_add_positive
          have hn := (nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hq
          omega⟩
    ∃ β : Fin n → C(S₂, (S.data q).UpperLevel),
      IsNativeMiddleBasinFamily S hf (S.data q).upper_regular p (fun j => β j) ∧
      (∀ j x, ∃ t : ℝ, S.flow t (α j x).val = (β j x).val) ∧
      (∀ j, Disjoint (range (β j)) (range (S.data q).surgery.beltSphere)) ∧
      ∃ (x : S₂) (v : sphere (0 : (S.data q).chart.PositiveCoordinates) 1),
        ∃ τ ∈ Ioo (0 : ℝ) 1,
        ∃ (F : ℝ × (S.data q).UpperLevel → (S.data q).UpperLevel)
          (K : Set (S.data q).UpperLevel),
          IsCompact K ∧ K ⊆ (otherSheetImages (fun j => β j) i)ᶜ ∧
          ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, RegularLevel.Model E))
            𝓘(ℝ, RegularLevel.Model E) ∞ F ∧
          (∀ z, F (0, z) = z) ∧
          (∀ t, ∃ d : Diffeomorph 𝓘(ℝ, RegularLevel.Model E)
              𝓘(ℝ, RegularLevel.Model E) (S.data q).UpperLevel (S.data q).UpperLevel ∞,
            ∀ z, d z = F (t, z)) ∧
          (∀ t z, z ∉ K → F (t, z) = z) ∧
          (∀ t j, j ≠ i → ∀ z, F (t, β j z) = β j z) ∧
          (∀ t ∈ Icc (0 : ℝ) 1, ∀ u : S₂,
            ∀ w : sphere (0 : (S.data q).chart.PositiveCoordinates) 1,
              F (t, β i u) = (S.data q).surgery.beltSphere w ↔
                t = τ ∧ u = x ∧ w = v) ∧
          NativeTransversality.At (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2)
            𝓘(ℝ, RegularLevel.Model E) (fun z : ℝ × S₂ => F (z.1, β i z.2))
            (S.data q).surgery.beltSphere (τ, x) v := by
  let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
  let _ := RegularLevel.isManifold hf (S.data q).upper_regular
  let _ : CompactSpace (S.data q).UpperLevel :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  let _ : Fact (Module.finrank ℝ (S.data q).chart.PositiveCoordinates = 2 + 1) :=
    ⟨by have hsplit := (S.data q).chart.finrank_negative_add_positive
        have hn := (nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hq
        omega⟩
  obtain ⟨β₀, hβ₀, horbit₀⟩ := S.exists_higher_middle_family hf
    (haq.trans (S.toSurgeryWindows.value_lt_upper q)) ha (S.data q).upper_regular p i hp hhigh α hα
  let β : Fin n → C(S₂, (S.data q).UpperLevel) := β₀
  have hβ : IsNativeMiddleBasinFamily S hf (S.data q).upper_regular p (fun j => β j) := hβ₀
  have horbit : ∀ j x, ∃ t : ℝ, S.flow t (α j x).val = (β j x).val := horbit₀
  have hdisj (j : Fin n) : Disjoint (range (β j)) (range (S.data q).surgery.beltSphere) := by
    apply Set.disjoint_left.mpr
    rintro y ⟨x, rfl⟩ hy
    exact S.upper_point_not_on_belt_of_lower_orbit hf q haq (α j x) (β j x) (horbit j x) hy
  let x : S₂ := Hemisphere.point true ⟨0, by simp⟩
  let v := SphereCoordinates.standardParametrization (S.data q).chart.PositiveCoordinates 2 x
  have hv : (S.data q).surgery.beltSphere v ∉ otherSheetImages (fun j => β j) i := by
    intro h
    obtain ⟨j, hj⟩ := mem_iUnion.mp h
    exact Set.disjoint_left.mp (hdisj j.val) hj (mem_range_self v)
  let _ : PathConnectedSpace (S.data q).UpperLevel :=
    S.pathConnectedSpace_index_three_upper_level hf hdim horder q hq (β i x)
  have hleveldim : Module.finrank ℝ (RegularLevel.Model E) = 5 := by
    simp [RegularLevel.Model, hdim]
  obtain ⟨τ, hτ, F, K, hK, hKU, hF, hF0, hFd, hFfix, hfixed, hcount, htrans⟩ :=
    exists_finite_family_single_passage (fun j => β j) hβ.1 hβ.2.2.2.1 i
      ((S.data q).belt_smooth hf 2) (hβ.2.1 i).isEmbedding
      (S.data q).belt_isClosedEmbedding.isEmbedding (hβ.2.2.1 i)
      ((S.data q).belt_derivative_injective hf 2) (hdisj i) hleveldim x v hv
      (PathConnectedSpace.somePath (β i x) ((S.data q).surgery.beltSphere v))
  exact ⟨β, hβ, horbit, hdisj, x, v, τ, hτ, F, K, hK, hKU, hF, hF0,
    hFd, hFfix, hfixed, hcount, htrans⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
