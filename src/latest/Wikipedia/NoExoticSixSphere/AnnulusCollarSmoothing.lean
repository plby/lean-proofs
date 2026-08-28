import Wikipedia.NoExoticSixSphere.AnnulusCollarAmbientExtension
import Wikipedia.NoExoticSixSphere.CompactRelativeManifoldSmoothing

/-!
# Relative smoothing of the original annulus with both collars fixed

Compact-image tubular retraction works without compactness of the target.
The actual annulus map is smoothed near the entire annulus, with both
prescribed end collars fixed exactly. A compact middle region is kept in
the specified open target set; the remaining interior values stay there
because the original map is unchanged on the protected collars.
-/

noncomputable section

open Set Metric Filter
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization SphereAnnulus

variable {n p : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (Vector n) M] [IsManifold (𝓡 n) ∞ M] [Nonempty M]
  (e : EuclideanEmbedding n M)

theorem exists_smooth_annulus_with_collars (G : C(SphereAnnulus.domain p, M))
    (H₀ H₁ : C(Vector (p + 1), Vector e.ambientDimension))
    (hH₀ : ContDiff ℝ ∞ H₀) (hH₁ : ContDiff ℝ ∞ H₁)
    (h₀ : ∀ x : SphereAnnulus.domain p, ‖x.val‖ ≤ 4 / 3 → H₀ x.val = e.toFun (G x))
    (h₁ : ∀ x : SphereAnnulus.domain p, 7 / 4 ≤ ‖x.val‖ → H₁ x.val = e.toFun (G x))
    (V : Set M) (hV : IsOpen V)
    (hGV : ∀ x : SphereAnnulus.domain p, 1 < ‖x.val‖ → ‖x.val‖ < 2 → G x ∈ V) :
    ∃ g : Vector (p + 1) → M,
      (∀ x ∈ SphereAnnulus.domain p, ContMDiffAt (𝓡 (p + 1)) (𝓡 n) ∞ g x) ∧
      (∀ x : SphereAnnulus.domain p, ‖x.val‖ ≤ 9 / 8 ∨ 15 / 8 ≤ ‖x.val‖ →
        g x.val = G x) ∧
      ∀ x : Vector (p + 1), 1 < ‖x‖ → ‖x‖ < 2 → g x ∈ V := by
  let A : C(SphereAnnulus.domain p, Vector e.ambientDimension) :=
    ⟨e.toFun ∘ G, e.smooth.continuous.comp G.continuous⟩
  obtain ⟨B, hBG, hB₀, hB₁⟩ := SphereAnnulus.exists_ambient_extension A H₀ H₁ h₀ h₁
  let L : Set (Vector (p + 1)) := {x | 9 / 8 ≤ ‖x‖ ∧ ‖x‖ ≤ 15 / 8}
  let S : Set (Vector (p + 1)) := {x | ‖x‖ ≤ 9 / 8 ∨ 15 / 8 ≤ ‖x‖}
  let U : Set (Vector (p + 1)) := {x | ‖x‖ < 5 / 4 ∨ 11 / 6 < ‖x‖}
  have hL : IsCompact L :=
    (isCompact_closedBall (0 : Vector (p + 1)) (15 / 8)).of_isClosed_subset
      ((isClosed_le continuous_const continuous_norm).inter
        (isClosed_le continuous_norm continuous_const))
      (fun _ hx ↦ mem_closedBall_zero_iff.mpr hx.2)
  have hLK : L ⊆ SphereAnnulus.domain p := by
    intro x hx
    change 9 / 8 ≤ ‖x‖ ∧ ‖x‖ ≤ 15 / 8 at hx
    constructor <;> linarith
  have hS : IsClosed S := (isClosed_le continuous_norm continuous_const).union
    (isClosed_le continuous_const continuous_norm)
  have hU : IsOpen U := (isOpen_lt continuous_norm continuous_const).union
    (isOpen_lt continuous_const continuous_norm)
  have hSU : S ⊆ U := by
    intro x hx
    rcases hx with hx | hx
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  have hBs : ContDiffOn ℝ ∞ B U := by
    intro x hx
    rcases hx with hx | hx
    · have he : (B : Vector (p + 1) → Vector e.ambientDimension) =ᶠ[𝓝 x] H₀ := by
        filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hx] with y hy
        exact hB₀ y hy.le
      exact (hH₀.contDiffAt.congr_of_eventuallyEq he).contDiffWithinAt
    · have he : (B : Vector (p + 1) → Vector e.ambientDimension) =ᶠ[𝓝 x] H₁ := by
        filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hx] with y hy
        exact hB₁ y hy.le
      exact (hH₁.contDiffAt.congr_of_eventuallyEq he).contDiffWithinAt
  obtain ⟨g, hgs, hgeq, hgV⟩ := e.exists_smooth_near_compact_relative
    (SphereAnnulus.isCompact_domain p) hL hLK G B hBG hS (hU.mem_nhdsSet.mpr hSU) hBs
    V hV (fun x hx ↦ hGV x (by change 9 / 8 ≤ ‖x.val‖ ∧ _ at hx; linarith)
      (by change _ ∧ ‖x.val‖ ≤ 15 / 8 at hx; linarith))
  refine ⟨g, hgs, hgeq, ?_⟩
  intro x hx₀ hx₁
  have hx : x ∈ SphereAnnulus.domain p := ⟨hx₀.le, hx₁.le⟩
  by_cases hcore : x ∈ L
  · exact hgV x hcore
  · have hprotected : x ∈ S := by
      by_contra hn
      change ¬ (‖x‖ ≤ 9 / 8 ∨ 15 / 8 ≤ ‖x‖) at hn
      push Not at hn
      exact hcore ⟨hn.1.le, hn.2.le⟩
    rw [hgeq ⟨x, hx⟩ hprotected]
    exact hGV ⟨x, hx⟩ hx₀ hx₁

end NoExoticSixSphere.EuclideanEmbedding
