import Wikipedia.NoExoticSixSphere.FamilyEmbeddingTrack
import Wikipedia.NoExoticSixSphere.SphereNeighborhoodAnnulus
import Wikipedia.SmoothSixDPoincare.ImmersionLocalInjectivity

/-!
# A uniform embedded immersive collar for a compact parameter family

The actual family track is embedded and immersive on the compact
parameter--sphere locus. Its open embedding neighborhood and the tube lemma
give one radial collar for all parameters. No choice of unrelated slice
collars or parametric embedding theorem is assumed.
-/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff
open Wikipedia.SmoothSixDPoincare.ManifoldImmersion

namespace NoExoticSixSphere.FamilyEmbedding

variable {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

theorem exists_uniform_embedded_immersive_annulus {K : Set P} (hK : IsCompact K)
    (f : P → E → F) (hf : ContDiff ℝ ∞ (uncurry f))
    (hi : ∀ t ∈ K, InjOn (f t) (sphere (0 : E) 1))
    (hd : ∀ t ∈ K, ∀ x ∈ sphere (0 : E) 1, Injective (fderiv ℝ (f t) x))
    {U : Set (P × E)} (hU : IsOpen U) (hSU : K ×ˢ sphere (0 : E) 1 ⊆ U) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      K ×ˢ (closedBall (0 : E) 1 ∩ {x | r ≤ ‖x‖}) ⊆ U ∧
      (∀ t ∈ K, InjOn (f t) (closedBall (0 : E) 1 ∩ {x | r ≤ ‖x‖})) ∧
      ∀ t ∈ K, ∀ x ∈ closedBall (0 : E) 1,
        r ≤ ‖x‖ → Injective (fderiv ℝ (f t) x) := by
  have hmd : ∀ q ∈ K ×ˢ sphere (0 : E) 1,
      Injective (mfderiv 𝓘(ℝ, P × E) 𝓘(ℝ, P × F) (track f) q) := by
    intro q hq
    rw [mfderiv_eq_fderiv]
    exact (injective_fderiv_track_iff f hf q.1 q.2).mpr (hd q.1 hq.1 q.2 hq.2)
  obtain ⟨V, hV, hKV, _, hVi, hVd⟩ :=
    exists_open_embedded_immersive_neighborhood isOpen_univ
      (contDiff_track f hf).contMDiff.contMDiffOn
      (hK.prod (isCompact_sphere (0 : E) 1)) (subset_univ _)
      ((injOn_track_iff f K _).mpr hi) hmd
  obtain ⟨W, T, _, hT, hKW, hST, hWT⟩ :=
    generalized_tube_lemma hK (isCompact_sphere (0 : E) 1) (hV.inter hU)
      (fun q hq ↦ ⟨hKV hq, hSU hq⟩)
  obtain ⟨r, hr, hr1, hRT⟩ := exists_annulus_subset_sphere_neighborhood hT hST
  have hR : K ×ˢ (closedBall (0 : E) 1 ∩ {x | r ≤ ‖x‖}) ⊆ V ∩ U :=
    fun q hq ↦ hWT ⟨hKW hq.1, hRT hq.2⟩
  refine ⟨r, hr, hr1, fun q hq ↦ (hR hq).2,
    (injOn_track_iff f K _).mp (hVi.mono (fun q hq ↦ (hR hq).1)), ?_⟩
  intro t ht x hx hrx
  apply (injective_fderiv_track_iff f hf t x).mp
  have htx : (t, x) ∈ V ∩ U := hR ⟨ht, hx, hrx⟩
  have h := hVd (t, x) htx.1
  rwa [mfderiv_eq_fderiv] at h

end NoExoticSixSphere.FamilyEmbedding
