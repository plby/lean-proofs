import Wikipedia.NoExoticSixSphere.CompactRetractionAnnulusInterior
import Wikipedia.NoExoticSixSphere.CompactRetractionProtectedDerivative

/-!
# Generic four-annuli retaining both original collars and strict interior

One small parameter gives generic four-to-seven jets on the active middle
annulus and regular double-point equations whenever at least one point is
active. Both protected end maps and their actual embedded derivatives are
fixed. Every interior point stays in the prescribed open target region.
The compact-image retraction is constructed for the original target atlas;
compactness of the whole target and immersion in the middle are not assumed.
-/

noncomputable section

open Set Function Filter Metric
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.GenericFourAnnulus

open GLOrthonormalization EuclideanEmbedding CompactRetractionAffineFamily SphereAnnulus

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  [IsManifold (𝓡 7) ∞ M] (e : EuclideanEmbedding 7 M)

include e in
theorem exists_relative (f : Vector 4 → M)
    (hf : ∀ x ∈ domain 3, ContMDiffAt (𝓡 4) (𝓡 7) ∞ f x)
    (r₀ r₁ : ℝ) (hr₀ : 1 < r₀) (hr₁ : r₁ < 2) (hrr : r₀ < r₁)
    (V : Set M) (hV : IsOpen V) (hfV : ∀ x, 1 < ‖x‖ → ‖x‖ < 2 → f x ∈ V) :
    ∃ g : Vector 4 → M,
      (∀ x ∈ domain 3, ContMDiffAt (𝓡 4) (𝓡 7) ∞ g x) ∧
      (∀ x ∈ domain 3, ‖x‖ ≤ r₀ ∨ r₁ ≤ ‖x‖ → g x = f x) ∧
      (∀ x ∈ domain 3, ‖x‖ ≤ r₀ ∨ r₁ ≤ ‖x‖ →
        fderiv ℝ (e.toFun ∘ g) x = fderiv ℝ (e.toFun ∘ f) x) ∧
      (∀ x, 1 < ‖x‖ → ‖x‖ < 2 → g x ∈ V) ∧
      ∃ C : Set (PartialDiffeomorph (𝓡 7) (𝓡 7) M (Vector 7) ∞),
        C.Countable ∧ (∀ y : M, ∃ c ∈ C, y ∈ c.source) ∧
        (∀ c ∈ C, OperatorRank.RegularFourSevenOn
          (fun x ↦ fderiv ℝ (c ∘ g) x) {x | (r₀ < ‖x‖ ∧ ‖x‖ < r₁) ∧ g x ∈ c.source}) ∧
        RegularDoublePointsOn g {x | 1 < ‖x‖ ∧ ‖x‖ < 2}
          {x | r₀ < ‖x‖ ∧ ‖x‖ < r₁} C := by
  let : Nonempty M := ⟨f 0⟩
  have hcont : ContinuousOn f (domain 3) :=
    fun x hx ↦ (hf x hx).continuousAt.continuousWithinAt
  obtain ⟨r⟩ := e.nonempty_retractionNear ((isCompact_domain 3).image_of_continuousOn hcont)
  have hb : ∀ x ∈ domain 3, f x ∈ r.base := fun x hx ↦ r.covers ⟨x, hx, rfl⟩
  let χ : Vector 4 → ℝ := perturbationCutoff r₀ r₁
  have hχ : ContDiff ℝ ∞ χ := contDiff_perturbationCutoff 3 r₀ r₁
  have hr₀pos : 0 ≤ r₀ := (zero_lt_one.trans hr₀).le
  have hr₁pos : 0 ≤ r₁ := hr₀pos.trans hrr.le
  have hzero (x : Vector 4) (hx : ‖x‖ ≤ r₀ ∨ r₁ ≤ ‖x‖) : χ x = 0 :=
    perturbationCutoff_zero_of_protected r₀ r₁ hr₀pos hr₁pos x hx
  let U : TopologicalSpace.Opens (Vector 4) :=
    ⟨{x | 1 < ‖x‖ ∧ ‖x‖ < 2},
      (isOpen_lt continuous_const continuous_norm).inter
        (isOpen_lt continuous_norm continuous_const)⟩
  have hUL : (U : Set (Vector 4)) ⊆ domain 3 := fun _ hx ↦ ⟨hx.1.le, hx.2.le⟩
  let A : Set (Parameters 4 e) :=
    {a | ∀ x, 1 < ‖x‖ → ‖x‖ < 2 → map e r f χ a x ∈ V}
  have hA : A ∈ 𝓝 (0 : Parameters 4 e) :=
    eventually_map_annulus_interior e r f χ r₀ r₁ hr₀ hr₁ hf hχ hzero hb V hV hfV
  obtain ⟨C, a, hC, hcov, -, haV, hadom, has, haeq, hgen⟩ :=
    exists_small_regular_on_compact_mem e r f χ (isCompact_domain 3)
      hf hχ hb U hUL rfl rfl A hA (by norm_num : (0 : ℝ) < 1)
  let g := map e r f χ a
  refine ⟨g, has, ?_, ?_, haV, C, hC, hcov, ?_, ?_⟩
  · intro x hx hxends
    exact haeq x hx (hzero x hxends)
  · intro x hx hxends
    exact fderiv_embedded_map_of_zero_cutoff e r f χ a x (hf x hx)
      hχ.contDiffAt (perturbationCutoff_nonneg r₀ r₁) (hzero x hxends) (hb x hx)
  · intro c hc
    have he : {x | (a, x) ∈ activeChartDomain e r f χ U
        (fun x hx ↦ (hf x (hUL hx)).contMDiffWithinAt) hχ c} =
        {x | (r₀ < ‖x‖ ∧ ‖x‖ < r₁) ∧ g x ∈ c.source} := by
      ext x
      constructor
      · rintro ⟨⟨⟨hxU, hxdom⟩, hxc⟩, hχx⟩
        exact ⟨(perturbationCutoff_ne_zero_iff r₀ r₁ hr₀pos hr₁pos x).mp hχx, hxc⟩
      · rintro ⟨hxactive, hxc⟩
        have hxU : x ∈ U := ⟨hr₀.trans hxactive.1, hxactive.2.trans hr₁⟩
        exact ⟨⟨⟨hxU, hadom x (hUL hxU)⟩, hxc⟩,
          (perturbationCutoff_ne_zero_iff r₀ r₁ hr₀pos hr₁pos x).mpr hxactive⟩
    have hg := hgen.1 c hc
    rw [he] at hg
    exact hg
  · have ha : {x : Vector 4 | χ x ≠ 0} = {x | r₀ < ‖x‖ ∧ ‖x‖ < r₁} := by
      ext x
      exact perturbationCutoff_ne_zero_iff r₀ r₁ hr₀pos hr₁pos x
    change RegularDoublePointsOn (map e r f χ a) U {x | r₀ < ‖x‖ ∧ ‖x‖ < r₁} C
    rw [← ha]
    exact hgen.2

end NoExoticSixSphere.GenericFourAnnulus
