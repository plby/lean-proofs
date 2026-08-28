import Wikipedia.HopfProblem.OrbitPairSupportedAmbientClock
import Wikipedia.HopfProblem.OrbitPairNativeImmersionStability

/-!
# Compact full-immersion stability for ambient clock perturbations

The small vector parameter, time, and source point are treated jointly.
Thus an ambient clock used to prepare a new point can be chosen small
enough to preserve every previously immersive point of a compact set.
-/

noncomputable section

open Set Function Filter
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.OrbitPair.ClockVelocity

open Wikipedia.SmoothSixDPoincare

variable {V E G H K M N : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {J : ModelWithCorners ℝ G K} [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N]

theorem eventually_clock_preserves_full_immersion
    (Φ : PartialDiffeomorph 𝓘(ℝ, V) J V N ∞)
    {β : V → ℝ} {κ : ℝ → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcompact : HasCompactSupport β)
    (hsupport : tsupport β ⊆ Φ.source)
    (hκ : ContDiff ℝ ∞ κ) (hbound : ∀ t, ‖κ t‖ ≤ 1)
    {F : ℝ × M → N} (hF : ContMDiff (𝓘(ℝ, ℝ).prod I) J ∞ F)
    {C : Set (ℝ × M)} (hC : IsCompact C)
    (hi : ∀ p ∈ C, Injective (mfderiv (𝓘(ℝ, ℝ).prod I) J F p)) :
    ∀ᶠ a : V in 𝓝 0, ∀ p ∈ C,
      Injective (mfderiv (𝓘(ℝ, ℝ).prod I) J
        (NativeFamily.ambientFamily F (clockAmbient Φ β κ a)) p) := by
  obtain ⟨δ, hδ, -, hsmooth, -⟩ :=
    SupportedDiffeomorph.exists_radius_ambient_bumpFamily Φ hβ hcompact hsupport
  let A : V → (ℝ × M) → N := fun a =>
    NativeFamily.ambientFamily F (clockAmbient Φ β κ a)
  let W : Set (V × (ℝ × M)) := {p | ‖p.1‖ < δ}
  have hW : IsOpen W := isOpen_lt continuous_fst.norm continuous_const
  have hin : ContMDiff (𝓘(ℝ, V).prod (𝓘(ℝ, ℝ).prod I)) (𝓘(ℝ, V).prod J) ∞
      (fun p : V × (ℝ × M) => (κ p.2.1 • p.1, F p.2)) :=
    ((hκ.contMDiff.comp (contMDiff_fst.comp contMDiff_snd)).smul contMDiff_fst).prodMk
      (hF.comp contMDiff_snd)
  have hfamily : ContMDiffOn (𝓘(ℝ, V).prod (𝓘(ℝ, ℝ).prod I)) J ∞ (uncurry A) W := by
    intro p hp
    have hnorm : ‖κ p.2.1 • p.1‖ < δ := by
      calc
        ‖κ p.2.1 • p.1‖ = ‖κ p.2.1‖ * ‖p.1‖ := norm_smul _ _
        _ ≤ 1 * ‖p.1‖ := mul_le_mul_of_nonneg_right (hbound p.2.1) (norm_nonneg _)
        _ = ‖p.1‖ := one_mul _
        _ < δ := hp
    exact ((hsmooth (κ p.2.1 • p.1, F p.2) hnorm).comp p (hin p)).contMDiffWithinAt
  have hzero : A 0 = F := by
    funext p
    change SupportedDiffeomorph.bumpFamily Φ β (κ p.1 • (0 : V), F p) = F p
    rw [smul_zero]
    exact SupportedDiffeomorph.bumpFamily_zero Φ β (F p)
  apply NativeImmersion.eventually_injective_derivative hW hfamily hC
  · intro p _
    change ‖(0 : V)‖ < δ
    simpa only [norm_zero] using hδ
  · intro p hp
    rw [hzero]
    exact hi p hp

end Wikipedia.HopfProblem.OrbitPair.ClockVelocity
