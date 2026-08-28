import Wikipedia.SmoothSixDPoincare.HeightPreservingCollarIsotopy
import Wikipedia.SmoothSixDPoincare.AmbientIsotopy

/-!
# Ambient extension of isotopies of actual regular levels

The collar is constructed from the original function and the native regular
level atlas. Every slice of the extended isotopy is an actual diffeomorphism
of the original manifold and preserves the function globally. In particular,
its endpoint preserves every original sublevel, not just the chosen level.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare.RegularLevel

/-- A height-preserving bijection preserves every set defined by height. -/
theorem image_preimage_eq_of_preserves {X Y : Type*} (d : X ≃ X) {f : X → Y}
    (hf : ∀ x, f (d x) = f x) (S : Set Y) : d '' (f ⁻¹' S) = f ⁻¹' S := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change f (d x) ∈ S
    rw [hf]
    exact hx
  · intro hy
    obtain ⟨x, rfl⟩ := d.surjective y
    refine ⟨x, ?_, rfl⟩
    change f x ∈ S
    change f (d x) ∈ S at hy
    rwa [hf x] at hy

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] {f : M → ℝ} {b : ℝ}
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
  (hreg : ∀ x, f x = b → x ∉ ManifoldMorse.criticalPoints E f)

/-- An actual regular-level isotopy extends smoothly to M while preserving f at every time. -/
theorem exists_ambient_extension_of_isotopy :
    letI := chartedSpace hf hreg
    ∀ A : ℝ × {x : M // f x = b} → {x : M // f x = b},
      ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, Model E)) 𝓘(ℝ, Model E) ∞ A →
      (∀ x, A (0, x) = x) →
      (∀ t, ∃ d : Diffeomorph 𝓘(ℝ, Model E) 𝓘(ℝ, Model E)
          {x : M // f x = b} {x : M // f x = b} ∞, ∀ x, A (t, x) = d x) →
      ∃ K : Set M, IsCompact K ∧ ∃ B : ℝ × M → M,
        ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ B ∧
        (∀ y, B (0, y) = y) ∧
        (∀ t, ∃ d : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞, ∀ y, B (t, y) = d y) ∧
        (∀ t y, y ∉ K → B (t, y) = y) ∧
        (∀ t (x : {x : M // f x = b}), B (t, (x : M)) = (A (t, x) : M)) ∧
        (∀ t y, f (B (t, y)) = f y) := by
  classical
  let _ := chartedSpace hf hreg
  let _ := isManifold hf hreg
  let _ : CompactSpace {x : M // f x = b} :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  intro A hA hA₀ hAt
  by_cases hb : Nonempty {x : M // f x = b}
  · let _ := hb
    obtain ⟨ε, hε, Ψ, hsource, hzero, hheight⟩ := exists_heightCollar hf hreg
    obtain ⟨K, hK, -, B, hB, hB₀, hBt, hfix, hlevel, hpreserve⟩ :=
      CollarIsotopy.exists_height_preserving_extension Ψ hε hsource hheight hA hA₀ hAt
    refine ⟨K, hK, B, hB, hB₀, hBt, hfix, ?_, hpreserve⟩
    intro t x
    simpa only [hzero] using hlevel t x
  · refine ⟨∅, isCompact_empty, Prod.snd, contMDiff_snd, fun _ => rfl, ?_,
      fun _ _ _ => rfl, ?_, fun _ _ => rfl⟩
    · exact fun _ => ⟨Diffeomorph.refl 𝓘(ℝ, E) M ∞, fun _ => rfl⟩
    · intro _ x
      exact (hb ⟨x⟩).elim

/-- The endpoint extends the given level diffeomorphism and preserves all original sublevels. -/
theorem exists_height_preserving_ambient_extension :
    letI := chartedSpace hf hreg
    ∀ e : Diffeomorph 𝓘(ℝ, Model E) 𝓘(ℝ, Model E)
        {x : M // f x = b} {x : M // f x = b} ∞,
      SupportedDiffeomorph.IsotopicToIdentity e →
      ∃ K : Set M, IsCompact K ∧ ∃ D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞,
        SupportedDiffeomorph.IsotopicToIdentity D ∧
        (∀ y, y ∉ K → D y = y) ∧
        (∀ x : {x : M // f x = b}, D (x : M) = (e x : M)) ∧
        (∀ y, f (D y) = f y) ∧
        (∀ S : Set ℝ, D '' (f ⁻¹' S) = f ⁻¹' S) := by
  let _ := chartedSpace hf hreg
  intro e he
  obtain ⟨A, hA, hA₀, hA₁, hAt⟩ := he
  obtain ⟨K, hK, B, hB, hB₀, hBt, hfix, hlevel, hpreserve⟩ :=
    exists_ambient_extension_of_isotopy hf hreg A hA hA₀ hAt
  obtain ⟨D, hD⟩ := hBt 1
  have hDf (y : M) : f (D y) = f y := by
    rw [← hD y]
    exact hpreserve 1 y
  refine ⟨K, hK, D, ⟨B, hB, hB₀, hD, hBt⟩, ?_, ?_, hDf, ?_⟩
  · intro y hy
    rw [← hD y]
    exact hfix 1 y hy
  · intro x
    rw [← hD (x : M), hlevel, hA₁]
  · exact image_preimage_eq_of_preserves D.toEquiv hDf

end Wikipedia.SmoothSixDPoincare.RegularLevel
