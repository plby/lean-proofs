import Wikipedia.NoExoticSixSphere.AnnulusPerturbationCutoff
import Wikipedia.NoExoticSixSphere.CompactRetractionInteriorControl

/-!
# Strict-interior control for the original protected annulus perturbation

Small parameters keep the compact active core in the prescribed open
target. Outside that core, the cutoff vanishes and the original map is
retained exactly. Thus every interior annulus point stays in the open
target without assuming the open annulus is compact.
-/

noncomputable section

open Set Function Filter Metric
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.CompactRetractionAffineFamily

open GLOrthonormalization EuclideanEmbedding SphereAnnulus

variable {p n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (e : EuclideanEmbedding n M) {K : Set M} (r : e.RetractionNear K)
  (f : Vector (p + 1) → M) (χ : Vector (p + 1) → ℝ)

theorem eventually_map_annulus_interior (r₀ r₁ : ℝ) (hr₀ : 1 < r₀) (hr₁ : r₁ < 2)
    (hf : ∀ x ∈ domain p, ContMDiffAt (𝓡 (p + 1)) (𝓡 n) ∞ f x)
    (hχ : ContDiff ℝ ∞ χ) (hzero : ∀ x, ‖x‖ ≤ r₀ ∨ r₁ ≤ ‖x‖ → χ x = 0)
    (hb : ∀ x ∈ domain p, f x ∈ r.base)
    (V : Set M) (hV : IsOpen V) (hfV : ∀ x, 1 < ‖x‖ → ‖x‖ < 2 → f x ∈ V) :
    ∀ᶠ a in 𝓝 (0 : Parameters (p + 1) e),
      ∀ x, 1 < ‖x‖ → ‖x‖ < 2 → map e r f χ a x ∈ V := by
  have hsub := closedCore_subset_domain p hr₀.le hr₁.le
  have hnear := eventually_map_mem_open_on_compact e r f χ
    (isCompact_closedCore p r₀ r₁)
    (fun x hx ↦ hf x (hsub hx)) hχ (fun x hx ↦ hb x (hsub hx)) V hV
    (fun x hx ↦ hfV x (hr₀.trans_le hx.1) (hx.2.trans_lt hr₁))
  apply hnear.mono
  intro a ha x hx₀ hx₁
  by_cases hcore : x ∈ closedCore p r₀ r₁
  · exact ha x hcore
  · have hend : ‖x‖ ≤ r₀ ∨ r₁ ≤ ‖x‖ := by
      by_cases hleft : ‖x‖ ≤ r₀
      · exact Or.inl hleft
      · right
        have hnot : ¬ ‖x‖ ≤ r₁ := fun h ↦ hcore ⟨(lt_of_not_ge hleft).le, h⟩
        exact (lt_of_not_ge hnot).le
    rw [map_eq_of_cutoff_zero e r f χ a x (hb x ⟨hx₀.le, hx₁.le⟩) (hzero x hend)]
    exact hfV x hx₀ hx₁

end NoExoticSixSphere.CompactRetractionAffineFamily
