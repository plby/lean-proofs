import Wikipedia.HopfProblem.DegreeCollapseIteratedColumnSlide

/-!
# Every integral multiple of the first attaching class is geometrically realized

Choose the sign and finitely iterate the native slide. The resulting actual
family and descending system retain the common-cut conditions and the
original protected maps, including the zero-multiple case.
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

theorem AdaptedSurgeryWindows.exists_integer_column_slide
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
    (k : ℤ) :
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
        (middleSectionClass (Γ i) = middleSectionClass (α i) + k • middleSectionClass αq) ∧
        ∀ z : M, f z ≤ f q →
          (∀ x, Tendsto (fun t => T.flow t x) atBot (𝓝 z) ↔
            Tendsto (fun t => S.flow t x) atBot (𝓝 z)) ∧
          (∀ x, Tendsto (fun t => S.flow t x) atBot (𝓝 z) →
            range (fun t => T.flow t x) = range (fun t => S.flow t x)) ∧
          ∀ v, Tendsto (fun t => T.flow t z) atTop (𝓝 v) ↔
            Tendsto (fun t => S.flow t z) atTop (𝓝 v) := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · simpa only [mul_one] using
      S.exists_iterated_column_slide hf hm hdim horder q hq ha hal hband p i hp hhigh
        αq α hfamily 1 (Or.inl rfl) m
  · simpa only [mul_neg_one] using
      S.exists_iterated_column_slide hf hm hdim horder q hq ha hal hband p i hp hhigh
        αq α hfamily (-1) (Or.inr rfl) m

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
