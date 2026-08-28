import Wikipedia.HopfProblem.DegreeCollapseRegularBandFamilyTransport
import Wikipedia.HopfProblem.DegreeCollapseIndexFourFamilyStep

/-!
# The whole native index-four backward-basin family at a regular cut

Retain the original regular-level atlas, smooth embedded immersive
three-spheres, pairwise disjointness, and exact full backward-basin images.
Actual regular-band transport and the constructed four-handle step both
preserve this data for the original critical labels.
-/

noncomputable section

open Set Function Filter Manifold Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

local notation "S₃" => Hemisphere.Sphere 3

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

def IsNativeFourBasinFamily (S : AdaptedSurgeryWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {a : ℝ}
    (ha : ∀ y, f y = a → y ∉ criticalPoints E f) {n : ℕ}
    (p : Fin n → criticalPoints E f) (α : Fin n → S₃ → {y : M // f y = a}) : Prop :=
  let _ := RegularLevel.chartedSpace hf ha
  (∀ j, ContMDiff (𝓡 3) 𝓘(ℝ, RegularLevel.Model E) ∞ (α j)) ∧
  (∀ j, IsClosedEmbedding (α j)) ∧
  (∀ j x, Injective (mfderiv (𝓡 3) 𝓘(ℝ, RegularLevel.Model E) (α j) x)) ∧
  Pairwise (fun i j => Disjoint (range (α i)) (range (α j))) ∧
  ∀ j y, y ∈ range (α j) ↔ Tendsto (fun t => S.flow t y.val) atBot (𝓝 (p j).val)

theorem AdaptedSurgeryWindows.exists_regular_band_four_basin_family
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {a b : ℝ} (hab : b < a) (ha : ∀ y, f y = a → y ∉ criticalPoints E f)
    (hb : ∀ y, f y = b → y ∉ criticalPoints E f)
    (hgap : ∀ q ∈ criticalPoints E f, f q ∉ Icc b a)
    (za : {x : M // f x = a}) {n : ℕ} (p : Fin n → criticalPoints E f)
    (hp : ∀ j, a < f (p j)) (α : Fin n → S₃ → {x : M // f x = a})
    (hα : IsNativeFourBasinFamily S hf ha p α) :
    ∃ β : Fin n → S₃ → {x : M // f x = b}, IsNativeFourBasinFamily S hf hb p β ∧
      ∀ j x, ∃ t : ℝ, S.flow t (α j x).val = (β j x).val := by
  let _ := RegularLevel.chartedSpace hf ha
  let _ := RegularLevel.chartedSpace hf hb
  obtain ⟨hs, he, hi, hpair, hfull⟩ := hα
  obtain ⟨β, hβs, hβe, hβi, hβpair, hflow, hβfull⟩ :=
    S.exists_regular_band_family_transport hf hab ha hb hgap za α hs
      (fun j => (he j).injective) hi hpair
  exact ⟨β, ⟨hβs, hβe, hβi, hβpair, fun j => hβfull j (p j).val (hp j) (hfull j)⟩,
    hflow⟩

theorem AdaptedSurgeryWindows.exists_four_basin_family_step
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : IsMorse E f) (hdim : Module.finrank ℝ E = 7)
    (q : criticalPoints E f) (hq : nativeMorseIndex E f q = 4)
    {n : ℕ} (p : Fin n → criticalPoints E f)
    (hp : ∀ j, S.toSurgeryWindows.upper q < f (p j))
    (α : Fin n → S₃ → (S.data q).UpperLevel)
    (hα : IsNativeFourBasinFamily S hf (S.data q).upper_regular p α)
    (ε : criticalPoints E f → ℝ) (hε : ∀ r, 0 < ε r) :
    ∃ T : AdaptedSurgeryWindows E f,
      (∀ r, (T.data r).chart = (S.data r).chart) ∧
      (∀ r, (T.data r).radius < ε r) ∧
      (∀ r ∈ criticalPoints E f, ∀ᶠ y in 𝓝 r, T.field y = S.field y) ∧
      ∃ Γ : Fin (n + 1) → S₃ → (S.data q).LowerLevel,
        IsNativeFourBasinFamily T hf (S.data q).lower_regular (Fin.cases q p) Γ := by
  let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
  let _ := RegularLevel.chartedSpace hf (S.data q).lower_regular
  obtain ⟨hs, he, hi, hpair, hfull⟩ := hα
  obtain ⟨T, hcharts, hradii, hgerms, -, -, Γ, hΓs, hΓe, hΓi, hΓpair,
      -, hΓzero, -, -, hΓfull⟩ :=
    S.exists_index_four_family_step hf hm hdim q hq n α isClosed_empty
      (fun j => disjoint_empty _) ε hε hs (fun j => (he j).injective) hi hpair
  refine ⟨T, hcharts, hradii, hgerms, Γ, hΓs, hΓe, hΓi, hΓpair, ?_⟩
  intro j
  cases j using Fin.cases with
  | zero => exact hΓzero
  | succ j => exact hΓfull j (p j).val (hp j) (hfull j)

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
