import Wikipedia.HopfProblem.DegreeCollapseRegularBandFamilyTransport

/-!
# A native middle family records full, labelled backward-basin images

This predicate fixes the original regular-level atlas. Its members are
smooth closed embedded immersive two-spheres, pairwise disjoint, and their
images are exactly the named critical backward basins on the cut. Both
regular-band transport and the constructed one-handle step retain it.
-/

noncomputable section

open Set Function Filter Manifold Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

local notation "S₂" => Hemisphere.Sphere 2

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

def IsNativeMiddleBasinFamily (S : AdaptedSurgeryWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a : ℝ}
    (ha : ∀ y, f y = a → y ∉ criticalPoints E f) {n : ℕ}
    (p : Fin n → criticalPoints E f) (α : Fin n → S₂ → {y : M // f y = a}) : Prop :=
  let _ := RegularLevel.chartedSpace hf ha
  (∀ j, ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) ∞ (α j)) ∧
  (∀ j, IsClosedEmbedding (α j)) ∧
  (∀ j x, Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model E) (α j) x)) ∧
  Pairwise (fun i j => Disjoint (range (α i)) (range (α j))) ∧
  ∀ j y, y ∈ range (α j) ↔ Tendsto (fun t => S.flow t y.val) atBot (𝓝 (p j).val)

theorem AdaptedSurgeryWindows.exists_regular_band_middle_basin_family
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {a b : ℝ} (hab : b < a) (ha : ∀ y, f y = a → y ∉ criticalPoints E f)
    (hb : ∀ y, f y = b → y ∉ criticalPoints E f)
    (hgap : ∀ q ∈ criticalPoints E f, f q ∉ Icc b a)
    (za : {x : M // f x = a}) {n : ℕ} (p : Fin n → criticalPoints E f)
    (hp : ∀ j, a < f (p j)) (α : Fin n → S₂ → {x : M // f x = a})
    (hα : IsNativeMiddleBasinFamily S hf ha p α) :
    ∃ β : Fin n → S₂ → {x : M // f x = b}, IsNativeMiddleBasinFamily S hf hb p β ∧
      ∀ j x, ∃ t : ℝ, S.flow t (α j x).val = (β j x).val := by
  let _ := RegularLevel.chartedSpace hf ha
  let _ := RegularLevel.chartedSpace hf hb
  obtain ⟨hs, he, hi, hpair, hfull⟩ := hα
  obtain ⟨β, hβs, hβe, hβi, hβpair, hflow, hβfull⟩ :=
    S.exists_regular_band_family_transport hf hab ha hb hgap za α hs
      (fun j => (he j).injective) hi hpair
  exact ⟨β, ⟨hβs, hβe, hβi, hβpair, fun j => hβfull j (p j).val (hp j) (hfull j)⟩,
    hflow⟩

theorem AdaptedSurgeryWindows.exists_middle_basin_family_step
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : IsMorse E f) (hdim : Module.finrank ℝ E = 6)
    (q : criticalPoints E f) (hq : nativeMorseIndex E f q = 3)
    {n : ℕ} (p : Fin n → criticalPoints E f)
    (hp : ∀ j, S.toSurgeryWindows.upper q < f (p j))
    (α : Fin n → S₂ → (S.data q).UpperLevel)
    (hα : IsNativeMiddleBasinFamily S hf (S.data q).upper_regular p α)
    (ε : criticalPoints E f → ℝ) (hε : ∀ r, 0 < ε r) :
    ∃ T : AdaptedSurgeryWindows E f,
      (∀ r, (T.data r).chart = (S.data r).chart) ∧
      (∀ r, (T.data r).radius < ε r) ∧
      (∀ r ∈ criticalPoints E f, ∀ᶠ y in 𝓝 r, T.field y = S.field y) ∧
      ∃ Γ : Fin (n + 1) → S₂ → (S.data q).LowerLevel,
        IsNativeMiddleBasinFamily T hf (S.data q).lower_regular (Fin.cases q p) Γ := by
  let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
  let _ := RegularLevel.chartedSpace hf (S.data q).lower_regular
  obtain ⟨hs, he, hi, hpair, hfull⟩ := hα
  obtain ⟨T, hcharts, hradii, hgerms, -, -, Γ, hΓs, hΓe, hΓi, hΓpair,
      -, hΓzero, -, -, hΓfull⟩ :=
    S.exists_middle_family_step hf hm hdim q hq n α isClosed_empty
      (fun j => disjoint_empty _) ε hε hs (fun j => (he j).injective) hi hpair
  refine ⟨T, hcharts, hradii, hgerms, Γ, hΓs, hΓe, hΓi, hΓpair, ?_⟩
  intro j
  cases j using Fin.cases with
  | zero => exact hΓzero
  | succ j => exact hΓfull j (p j).val (hp j) (hfull j)

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
