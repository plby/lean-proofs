import Wikipedia.NoExoticSixSphere.SmoothAnnulusBoundaryImmersion
import Mathlib.Topology.Order.Compact

/-!+# Protected immersive neighborhoods of both original annulus boundaries

The singular set of a continuous operator field on the closed annulus
is compact. If it misses both boundary spheres, its norm has minimum
strictly above one and maximum strictly below two. This gives two
immersive subcollars inside the regions fixed by relative smoothing.
No immersion is asserted between these subcollars.
-/

noncomputable section

open Set Function Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereAnnulus

open GLOrthonormalization

variable {p : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_injective_boundary_annuli (D : Vector (p + 1) → Vector (p + 1) →L[ℝ] F)
    (hD : ContinuousOn D (domain p))
    (hi : ∀ x, ‖x‖ = 1 ∨ ‖x‖ = 2 → Injective (D x)) :
    ∃ r₀ r₁ : ℝ, 1 < r₀ ∧ r₀ < 9 / 8 ∧ 15 / 8 < r₁ ∧ r₁ < 2 ∧
      ∀ x ∈ domain p, ‖x‖ ≤ r₀ ∨ r₁ ≤ ‖x‖ → Injective (D x) := by
  let S : Set (Vector (p + 1)) := domain p ∩ {x | ¬ Injective (D x)}
  have hSc : IsClosed S :=
    hD.preimage_isClosed_of_isClosed (isClosed_domain p)
      ContinuousLinearMap.isOpen_injective.isClosed_compl
  have hS : IsCompact S := (isCompact_domain p).of_isClosed_subset hSc inter_subset_left
  by_cases hne : S.Nonempty
  · obtain ⟨x, hx, hmin⟩ := hS.exists_isMinOn hne continuous_norm.continuousOn
    obtain ⟨y, hy, hmax⟩ := hS.exists_isMaxOn hne continuous_norm.continuousOn
    have hx1 : 1 < ‖x‖ := lt_of_le_of_ne hx.1.1 (by
      intro he
      exact hx.2 (hi x (Or.inl he.symm)))
    have hy2 : ‖y‖ < 2 := lt_of_le_of_ne hy.1.2 (by
      intro he
      exact hy.2 (hi y (Or.inr he)))
    obtain ⟨r₀, hr₀, hr₀min⟩ := exists_between
      (lt_min (by norm_num : (1 : ℝ) < 9 / 8) hx1)
    obtain ⟨r₁, hr₁max, hr₁⟩ := exists_between
      (max_lt (by norm_num : (15 / 8 : ℝ) < 2) hy2)
    refine ⟨r₀, r₁, hr₀, hr₀min.trans_le (min_le_left _ _),
      (le_max_left _ _).trans_lt hr₁max, hr₁, ?_⟩
    intro z hz hzends
    by_contra hsing
    rcases hzends with hz₀ | hz₁
    · have hle : ‖x‖ ≤ ‖z‖ := hmin ⟨hz, hsing⟩
      exact (not_lt_of_ge (hle.trans hz₀)) (hr₀min.trans_le (min_le_right _ _))
    · have hle : ‖z‖ ≤ ‖y‖ := hmax ⟨hz, hsing⟩
      exact (not_lt_of_ge (hz₁.trans hle)) ((le_max_right _ _).trans_lt hr₁max)
  · refine ⟨17 / 16, 31 / 16, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
    intro x hx _
    by_contra hsing
    exact hne ⟨x, hx, hsing⟩

variable {k : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector k) M]
  (e : EuclideanEmbedding k M)

theorem exists_immersive_boundary_annuli (f : Vector (p + 1) → M)
    (hf : ∀ x ∈ domain p, ContMDiffAt (𝓡 (p + 1)) (𝓡 k) ∞ f x)
    (hi : ∀ q : Sphere p,
      Injective (fderiv ℝ (e.toFun ∘ f) q.val) ∧
      Injective (fderiv ℝ (e.toFun ∘ f) ((2 : ℝ) • q.val))) :
    ∃ r₀ r₁ : ℝ, 1 < r₀ ∧ r₀ < 9 / 8 ∧ 15 / 8 < r₁ ∧ r₁ < 2 ∧
      ∀ x ∈ domain p, ‖x‖ ≤ r₀ ∨ r₁ ≤ ‖x‖ →
        Injective (fderiv ℝ (e.toFun ∘ f) x) := by
  apply exists_injective_boundary_annuli (fderiv ℝ (e.toFun ∘ f))
  · intro x hx
    exact ((e.smooth.contMDiffAt.comp x (hf x hx)).contDiffAt.continuousAt_fderiv
      (by simp)).continuousWithinAt
  · intro x hx
    rcases hx with hx | hx
    · exact (hi ⟨x, mem_sphere_zero_iff_norm.mpr hx⟩).1
    · let q : Sphere p := ⟨(1 / 2 : ℝ) • x, by
        apply mem_sphere_zero_iff_norm.mpr
        rw [norm_smul, hx]
        norm_num⟩
      have hq : (2 : ℝ) • q.val = x := by
        change (2 : ℝ) • ((1 / 2 : ℝ) • x) = x
        rw [smul_smul]
        norm_num
      simpa only [hq] using (hi q).2

end NoExoticSixSphere.SphereAnnulus
