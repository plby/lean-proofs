import Wikipedia.HopfProblem.DegreeCollapseRepeatableColumnSlide

/-!
# Finite iteration of the actual prescribed column slide

Induction composes the constructed descending systems, keeping the same
central sphere, common cut, regular band, and all protected parameters.
The selected class receives any finite multiple of either prescribed unit.
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

theorem AdaptedSurgeryWindows.exists_iterated_column_slide
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
    (k : ℤ) (hk : k = 1 ∨ k = -1) (m : ℕ) :
    ∃ T : AdaptedSurgeryWindows E f,
      (∀ z, (T.data z).chart = (S.data z).chart) ∧
      (∀ z, (T.data z).radius ≤ (S.data z).radius) ∧
      (∀ z ∈ criticalPoints E f, ∀ᶠ y in 𝓝 z, T.field y = S.field y) ∧
      a < T.toSurgeryWindows.lower q ∧
      (∀ y, f y ∈ Icc a (T.toSurgeryWindows.lower q) → y ∉ criticalPoints E f) ∧
      (∀ j, T.toSurgeryWindows.upper q < f (p j)) ∧
      ∃ Γ : Fin n → C(S₂, {y : M // f y = a}),
        IsNativeMiddleBasinFamily T hf ha (Fin.cases q p) (Fin.cases αq (fun j => Γ j)) ∧
        (∀ j, j ≠ i → Γ j = α j) ∧
        (middleSectionClass (Γ i) = middleSectionClass (α i) + ((m : ℤ) * k) • middleSectionClass αq) ∧
        ∀ z : M, f z ≤ f q →
          (∀ x, Tendsto (fun t => T.flow t x) atBot (𝓝 z) ↔
            Tendsto (fun t => S.flow t x) atBot (𝓝 z)) ∧
          (∀ x, Tendsto (fun t => S.flow t x) atBot (𝓝 z) →
            range (fun t => T.flow t x) = range (fun t => S.flow t x)) ∧
          ∀ v, Tendsto (fun t => T.flow t z) atTop (𝓝 v) ↔
            Tendsto (fun t => S.flow t z) atTop (𝓝 v) := by
  induction m with
  | zero =>
    refine ⟨S, fun _ => rfl, fun _ => le_rfl, ?_, hal, hband, hhigh,
      α, hfamily, fun _ _ => rfl, ?_, ?_⟩
    · intro z hz
      exact Filter.Eventually.of_forall (fun _ => rfl)
    · simp only [Nat.cast_zero, zero_mul, zero_smul, add_zero]
    · intro z hz
      exact ⟨fun _ => Iff.rfl, fun _ _ => rfl, fun _ => Iff.rfl⟩
  | succ m ih =>
    obtain ⟨T, hcharts, hradii, hgerms, hcut, hregular, hseparated,
      Γ, hΓ, hother, hclass, hkeep⟩ := ih
    obtain ⟨U, ucharts, uradii, ugerms, ucut, uregular, useparated,
      Δ, hΔ, uother, uclass, ukeep⟩ :=
      T.exists_repeatable_column_slide hf hm hdim horder q hq ha hcut hregular
        p i hp hseparated αq Γ hΓ k hk
    refine ⟨U, fun z => (ucharts z).trans (hcharts z),
      fun z => (uradii z).trans (hradii z), ?_, ucut, uregular, useparated,
      Δ, hΔ, fun j hji => (uother j hji).trans (hother j hji), ?_, ?_⟩
    · intro z hz
      filter_upwards [ugerms z hz, hgerms z hz] with y hy hy'
      exact hy.trans hy'
    · rw [uclass, hclass, add_assoc, ← add_zsmul]
      have hcoef : (m : ℤ) * k + k = ((m + 1 : ℕ) : ℤ) * k := by
        push_cast
        ring
      rw [hcoef]
    · intro z hz
      have hUT := ukeep z hz
      have hTS := hkeep z hz
      exact ⟨fun x => (hUT.1 x).trans (hTS.1 x),
        fun x hx => (hUT.2.1 x ((hTS.1 x).mpr hx)).trans (hTS.2.1 x hx),
        fun v => (hUT.2.2 v).trans (hTS.2.2 v)⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
