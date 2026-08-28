import Wikipedia.HopfProblem.DegreeCollapseCommonCutClassTransport
import Wikipedia.HopfProblem.DegreeCollapsePrescribedFamilySlide

/-!
# A prescribed-sign slide changes actual sphere classes at the fixed common cut

For a first middle handle, the band from the common cut to its lower
window is regular. Return the realized higher family through that band,
retain the exact central sphere and every protected parameter, and use
injectivity of literal sublevel inclusion to descend the signed relation.
This version retains the given canonical parameter of the central sphere.
-/

noncomputable section

open Set Function Filter Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

local notation "S₂" => Hemisphere.Sphere 2

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.exists_common_cut_prescribed_slide
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : IsMorse E f) (hdim : Module.finrank ℝ E = 6)
    (horder : ∀ p q : criticalPoints E f, f p < f q →
      nativeMorseIndex E f p ≤ nativeMorseIndex E f q)
    (q : criticalPoints E f) (hq : nativeMorseIndex E f q = 3)
    {a : ℝ} (ha : ∀ y, f y = a → y ∉ criticalPoints E f)
    (hal : a < S.toSurgeryWindows.lower q)
    (hband : ∀ y, f y ∈ Icc a (S.toSurgeryWindows.lower q) → y ∉ criticalPoints E f)
    {n : ℕ} (p : Fin n → criticalPoints E f) (i : Fin n)
    (hp : ∀ j, nativeMorseIndex E f (p j) = 3)
    (hhigh : ∀ j, S.toSurgeryWindows.upper q < f (p j))
    (αq : C(S₂, {y : M // f y = a})) (α : Fin n → C(S₂, {y : M // f y = a}))
    (hfamily : IsNativeMiddleBasinFamily S hf ha (Fin.cases q p)
      (Fin.cases αq (fun j => α j)))
    (hαq : ∀ x, ∃ t : ℝ, S.flow t (nativeIndexThreeAttachingSphere S q hq x).val = (αq x).val)
    (k : ℤ) (hk : k = 1 ∨ k = -1)
    (ε : criticalPoints E f → ℝ) (hε : ∀ z, 0 < ε z) :
    ∃ T : AdaptedSurgeryWindows E f,
      (∀ z, (T.data z).chart = (S.data z).chart) ∧
      (∀ z, (T.data z).radius < ε z) ∧
      (∀ z ∈ criticalPoints E f, ∀ᶠ y in 𝓝 z, T.field y = S.field y) ∧
      ∃ Γ : Fin n → C(S₂, {y : M // f y = a}),
        IsNativeMiddleBasinFamily T hf ha (Fin.cases q p) (Fin.cases αq (fun j => Γ j)) ∧
        (∀ j, j ≠ i → Γ j = α j) ∧
        (middleSectionClass (Γ i) = middleSectionClass (α i) + k • middleSectionClass αq) ∧
        ∀ z : M, f z ≤ f q →
          (∀ x, Tendsto (fun t => T.flow t x) atBot (𝓝 z) ↔
            Tendsto (fun t => S.flow t x) atBot (𝓝 z)) ∧
          (∀ x, Tendsto (fun t => S.flow t x) atBot (𝓝 z) →
            range (fun t => T.flow t x) = range (fun t => S.flow t x)) ∧
          ∀ v, Tendsto (fun t => T.flow t z) atTop (𝓝 v) ↔
            Tendsto (fun t => S.flow t z) atTop (𝓝 v) := by
  let _ := RegularLevel.chartedSpace hf ha
  let _ := RegularLevel.chartedSpace hf (S.data q).lower_regular
  obtain ⟨hs, he, hi, hpair, hfull⟩ := hfamily
  have hα : IsNativeMiddleBasinFamily S hf ha p (fun j => α j) := by
    refine ⟨fun j => hs j.succ, fun j => he j.succ, fun j => hi j.succ, ?_, fun j => hfull j.succ⟩
    intro j k hjk
    exact hpair (fun h => hjk (Fin.succ_inj.mp h))
  obtain ⟨T, hcharts, hradii, hgerms, β, δ, hβ, hδ, hαβ, hother, hprotected,
      hmaps, hkeep⟩ :=
    S.exists_prescribed_family_slide hf hm hdim horder q hq ha
      (hal.trans (S.toSurgeryWindows.lower_lt_value q)) p i hp hhigh α hα k hk ε hε
  have hgap : ∀ z ∈ criticalPoints E f, f z ∉ Icc a (S.toSurgeryWindows.lower q) :=
    fun z hz h => hband z h hz
  have hpabove (j : Fin n) : S.toSurgeryWindows.lower q < f (p j) :=
    (S.toSurgeryWindows.lower_lt_value q).trans
      ((S.toSurgeryWindows.value_lt_upper q).trans (hhigh j))
  let x₀ : S₂ := Hemisphere.point true ⟨0, by simp⟩
  obtain ⟨Γ₀, hΓ₀, hδΓ⟩ := T.exists_regular_band_middle_basin_family hf hal
    (S.data q).lower_regular ha hgap (δ i x₀) p hpabove (fun j => δ j) hδ
  let Γ : Fin n → C(S₂, {y : M // f y = a}) := fun j => ⟨Γ₀ j, (hΓ₀.1 j).continuous⟩
  have hΓ : IsNativeMiddleBasinFamily T hf ha p (fun j => Γ j) := hΓ₀
  have hαqfull (y : {z : M // f z = a}) : y ∈ range αq ↔
      Tendsto (fun t => T.flow t y.val) atBot (𝓝 q.val) :=
    (hfull 0 y).trans ((hkeep q.val le_rfl).1 y.val).symm
  have hdisj (j : Fin n) : Disjoint (range αq) (range (Γ j)) := by
    apply Set.disjoint_left.mpr
    intro y hyq hyj
    have heq : q.val = (p j).val := tendsto_nhds_unique
      ((hαqfull y).mp hyq) ((hΓ.2.2.2.2 j y).mp hyj)
    exact ((S.toSurgeryWindows.value_lt_upper q).trans (hhigh j)).ne (congrArg f heq)
  have hΓpair : Pairwise (fun j k => Disjoint
      (range (Fin.cases αq (fun j => Γ j) j)) (range (Fin.cases αq (fun j => Γ j) k))) := by
    intro j k hjk
    cases j using Fin.cases with
    | zero =>
      cases k using Fin.cases with
      | zero => exact (hjk rfl).elim
      | succ k => exact hdisj k
    | succ j =>
      cases k using Fin.cases with
      | zero => exact (hdisj j).symm
      | succ k => exact hΓ.2.2.2.1 (fun h => hjk (congrArg Fin.succ h))
  refine ⟨T, hcharts, hradii, hgerms, Γ, ?_, ?_, ?_, hkeep⟩
  · refine ⟨?_, ?_, ?_, hΓpair, ?_⟩
    · intro j
      cases j using Fin.cases with
      | zero => exact hs 0
      | succ j => exact hΓ.1 j
    · intro j
      cases j using Fin.cases with
      | zero => exact he 0
      | succ j => exact hΓ.2.1 j
    · intro j
      cases j using Fin.cases with
      | zero => exact hi 0
      | succ j => exact hΓ.2.2.1 j
    · intro j
      cases j using Fin.cases with
      | zero => exact hαqfull
      | succ j => exact hΓ.2.2.2.2 j
  · intro j hji
    apply ContinuousMap.ext
    intro x
    obtain ⟨s, hs⟩ := hδΓ j x
    change T.flow s (δ j x).val = (Γ j x).val at hs
    obtain ⟨t, ht⟩ := hprotected j hji x
    have hshared : T.flow 0 (Γ j x).val = T.flow (s - t) (α j x).val := by
      rw [T.flow.map_zero_apply, ← hs, ← ht, ← T.flow.map_add, sub_add_cancel]
    apply Subtype.ext
    exact native_same_level_orbit_points hf T.smooth T.flow T.integral
      (fun z hz => T.descent z (ha z hz)) (Γ j x).property (α j x).property hshared
  · have hβα (x : S₂) : ∃ t : ℝ, S.flow t (β i x).val = (α i x).val := by
      obtain ⟨t, ht⟩ := hαβ i x
      exact ⟨-t, by rw [← ht, ← S.flow.map_add, neg_add_cancel, S.flow.map_zero_apply]⟩
    exact signed_relation_of_regular_cut_transport S T hf hal ha hband
      (β i) (δ i) (nativeIndexThreeAttachingSphere S q hq) (α i) (Γ i) αq k
      hβα (hδΓ i) hαq hmaps

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
