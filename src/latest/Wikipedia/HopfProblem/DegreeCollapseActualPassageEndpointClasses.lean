import Wikipedia.HopfProblem.DegreeCollapseRelativeFamilyLowerTransport

/-!
# The signed passage formula concerns the actual lower endpoint maps

The constructed belt-complement transport is uniquely determined by its
original-flow orbit formula. Thus any actual lower endpoint maps with
those formulas are exactly the two maps in the proved passage relation.
No separately chosen endpoint representative or orientation is assumed.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open PassageHomology SingularMayerVietoris

local notation "S₂" => Hemisphere.Sphere 2

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.single_passage_actual_endpoint_classes
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (q : criticalPoints E f) (hq : nativeMorseIndex E f q = 3)
    [Fact (Module.finrank ℝ (S.data q).chart.PositiveCoordinates = 2 + 1)]
    (H : C(ℝ × S₂, (S.data q).UpperLevel)) {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1)
    (x₀ : S₂) (v : sphere (0 : (S.data q).chart.PositiveCoordinates) 1)
    (hpoint : (S.data q).surgery.beltSphere v = H (τ, x₀))
    (hcross : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x : S₂,
      H (t, x) ∈ range (S.data q).surgery.beltSphere ↔ t = τ ∧ x = x₀)
    (β δ : C(S₂, (S.data q).LowerLevel))
    (hβ : ∀ x, ∃ t : ℝ, S.flow t (H (0, x)).val = (β x).val)
    (hδ : ∀ x, ∃ t : ℝ, S.flow t (H (1, x)).val = (δ x).val) :
    let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
    ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, RegularLevel.Model E) ∞ H (τ, x₀) →
    NativeTransversality.At (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) 𝓘(ℝ, RegularLevel.Model E)
      H (S.data q).surgery.beltSphere (τ, x₀) v →
    ∃ k : ℤ, (k = 1 ∨ k = -1) ∧
      singularHomologyMap δ 2 = singularHomologyMap β 2 +
        k • singularHomologyMap (nativeIndexThreeAttachingSphere S q hq) 2 := by
  let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
  let _ : Fact (Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 2 + 1) :=
    ⟨(nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hq⟩
  dsimp only
  intro hH htrans
  obtain ⟨D, -, hunique, k, hk, hrelation⟩ :=
    S.exists_single_passage_class_addition hf q H hτ x₀ v hpoint hcross hH htrans
  let G := D.comp (puncturedPassageTrace H (range (S.data q).surgery.beltSphere) hτ x₀ hcross)
  have hmap (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (hsτ : s ≠ τ)
      (σ : C(S₂, (S.data q).LowerLevel))
      (hσ : ∀ x, ∃ t : ℝ, S.flow t (H (s, x)).val = (σ x).val) :
      G.comp (cylinderSlice τ x₀ s hsτ) = σ := by
    apply ContinuousMap.ext
    intro x
    obtain ⟨t, ht⟩ := hσ x
    apply hunique _ (σ x) t
    have heq := puncturedPassageTrace_on_interval H
      (range (S.data q).surgery.beltSphere) hτ x₀ hcross (cylinderSlice τ x₀ s hsτ x) hs
    change S.flow t
      (puncturedPassageTrace H (range (S.data q).surgery.beltSphere) hτ x₀ hcross
        (cylinderSlice τ x₀ s hsτ x)).val.val = (σ x).val
    rw [heq]
    exact ht
  have hzero := hmap 0 ⟨le_rfl, zero_le_one⟩ hτ.1.ne β hβ
  have hone := hmap 1 ⟨zero_le_one, le_rfl⟩ hτ.2.ne' δ hδ
  change singularHomologyMap (G.comp (cylinderSlice τ x₀ 1 hτ.2.ne')) 2 =
    singularHomologyMap (G.comp (cylinderSlice τ x₀ 0 hτ.1.ne)) 2 +
      k • singularHomologyMap (nativeIndexThreeAttachingSphere S q hq) 2 at hrelation
  rw [hone, hzero] at hrelation
  exact ⟨k, hk, hrelation⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
