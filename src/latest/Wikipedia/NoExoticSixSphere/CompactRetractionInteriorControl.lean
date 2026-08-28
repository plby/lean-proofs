import Wikipedia.NoExoticSixSphere.CompactRetractionGenericMap

/-!
# Open-target control for the same protected manifold perturbation

Compactness turns continuity near the original parameter into uniform
preservation of an open target region on a compact source subset. Combined
with the exact cutoff-zero equality, this controls the whole disk interior
without assuming it is compact or allowing its boundary into the open region.
-/

noncomputable section

open Set Function Filter Metric
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.CompactRetractionAffineFamily

open GLOrthonormalization EuclideanEmbedding

variable {d n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (e : EuclideanEmbedding n M) {K : Set M} (r : e.RetractionNear K)
  (f : Vector d → M) (χ : Vector d → ℝ)

theorem eventually_map_mem_open_on_compact {L : Set (Vector d)} (hL : IsCompact L)
    (hf : ∀ x ∈ L, ContMDiffAt (𝓡 d) (𝓡 n) ∞ f x) (hχ : ContDiff ℝ ∞ χ)
    (hb : ∀ x ∈ L, f x ∈ r.base) (V : Set M) (hV : IsOpen V)
    (hfV : ∀ x ∈ L, f x ∈ V) :
    ∀ᶠ p in 𝓝 (0 : Parameters d e), ∀ x ∈ L, map e r f χ p x ∈ V := by
  apply hL.eventually_forall_of_forall_eventually
  intro x hx
  have he : ambient e f χ (0 : Parameters d e) x = e.toFun (f x) := by
    simp only [ambient, WeightedAffineComposite.ambient, AffinePerturbation.value,
      Prod.fst_zero, Prod.snd_zero, zero_apply, add_zero, smul_zero, comp_apply]
  have hmem : ambient e f χ (0 : Parameters d e) x ∈ r.domain :=
    he.symm ▸ r.contains ⟨f x, hb x hx, rfl⟩
  have hzero : map e r f χ 0 x ∈ V := by
    rw [map_zero e r f χ x (hb x hx)]
    exact hfV x hx
  exact (contMDiffAt_map e r f χ 0 x (hf x hx) hχ.contDiffAt hmem).continuousAt
    (hV.mem_nhds hzero)

theorem eventually_map_disk_interior (ρ : ℝ) (hρ : ρ < 1)
    (hf : ∀ x ∈ closedBall 0 1, ContMDiffAt (𝓡 d) (𝓡 n) ∞ f x)
    (hχ : ContDiff ℝ ∞ χ) (hzero : ∀ x, ρ ≤ ‖x‖ → χ x = 0)
    (hb : ∀ x ∈ closedBall 0 1, f x ∈ r.base)
    (V : Set M) (hV : IsOpen V) (hfV : ∀ x ∈ ball 0 1, f x ∈ V) :
    ∀ᶠ p in 𝓝 (0 : Parameters d e), ∀ x ∈ ball 0 1, map e r f χ p x ∈ V := by
  have hsub : closedBall (0 : Vector d) ρ ⊆ ball 0 1 :=
    closedBall_subset_ball hρ
  have hnear := eventually_map_mem_open_on_compact e r f χ
    (isCompact_closedBall (0 : Vector d) ρ)
    (fun x hx ↦ hf x (ball_subset_closedBall (hsub hx))) hχ
    (fun x hx ↦ hb x (ball_subset_closedBall (hsub hx))) V hV
    (fun x hx ↦ hfV x (hsub hx))
  apply hnear.mono
  intro p hp x hx
  by_cases hinner : x ∈ closedBall (0 : Vector d) ρ
  · exact hp x hinner
  · rw [map_eq_of_cutoff_zero e r f χ p x (hb x (ball_subset_closedBall hx))
      (hzero x (le_of_lt (not_le.mp (fun h ↦ hinner (mem_closedBall_zero_iff.mpr h)))))]
    exact hfV x hx

end NoExoticSixSphere.CompactRetractionAffineFamily
