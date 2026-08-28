import Wikipedia.NoExoticSixSphere.CompactCoreImmersion
import Wikipedia.NoExoticSixSphere.AnnulusDoublePointCompactness
import Mathlib.Topology.Order.Compact

/-!
# One embedded immersive neighborhood of both annulus boundary spheres

An injective immersive map on the union of the two boundary spheres has
one injective immersive neighborhood of that compact union. Compactness
of the complement in the actual annulus supplies two uniform subcollars.
Injectivity is joint across the two collars, not just separate on each.
-/

noncomputable section

open Function Set Metric
open scoped ContDiff

namespace NoExoticSixSphere.SphereAnnulus

open GLOrthonormalization

theorem exists_boundary_annuli_subset {p : ℕ} {U : Set (Vector (p + 1))} (hU : IsOpen U)
    (hB : ∀ x : Vector (p + 1), ‖x‖ = 1 ∨ ‖x‖ = 2 → x ∈ U) :
    ∃ r₀ r₁ : ℝ, 1 < r₀ ∧ r₀ < 9 / 8 ∧ 15 / 8 < r₁ ∧ r₁ < 2 ∧
      {x | x ∈ domain p ∧ (‖x‖ ≤ r₀ ∨ r₁ ≤ ‖x‖)} ⊆ U := by
  let K := domain p \ U
  have hK : IsCompact K := (isCompact_domain p).diff hU
  by_cases hne : K.Nonempty
  · obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn hne continuous_norm.continuousOn
    obtain ⟨y, hy, hmax⟩ := hK.exists_isMaxOn hne continuous_norm.continuousOn
    have hx1 : 1 < ‖x‖ := lt_of_le_of_ne hx.1.1
      (fun he ↦ hx.2 (hB x (Or.inl he.symm)))
    have hy2 : ‖y‖ < 2 := lt_of_le_of_ne hy.1.2
      (fun he ↦ hy.2 (hB y (Or.inr he)))
    obtain ⟨r₀, hr₀, hr₀min⟩ := exists_between (lt_min (by norm_num : (1 : ℝ) < 9 / 8) hx1)
    obtain ⟨r₁, hr₁max, hr₁⟩ := exists_between (max_lt (by norm_num : (15 / 8 : ℝ) < 2) hy2)
    refine ⟨r₀, r₁, hr₀, hr₀min.trans_le (min_le_left _ _),
      (le_max_left _ _).trans_lt hr₁max, hr₁, ?_⟩
    intro z hz
    by_contra hzU
    rcases hz.2 with hl | hr
    · exact (not_lt_of_ge ((hmin ⟨hz.1, hzU⟩).trans hl))
        (hr₀min.trans_le (min_le_right _ _))
    · exact (not_lt_of_ge (hr.trans (hmax ⟨hz.1, hzU⟩)))
        ((le_max_right _ _).trans_lt hr₁max)
  · refine ⟨17 / 16, 31 / 16, by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
    intro x hx
    by_contra hxU
    exact hne ⟨x, hx.1, hxU⟩

theorem exists_embedded_boundary_annuli {p : ℕ} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] (f : Vector (p + 1) → F)
    (hf : ∀ x, ‖x‖ = 1 ∨ ‖x‖ = 2 → ContDiffAt ℝ ∞ f x)
    (hi : InjOn f {x | ‖x‖ = 1 ∨ ‖x‖ = 2})
    (hd : ∀ x, ‖x‖ = 1 ∨ ‖x‖ = 2 → Injective (fderiv ℝ f x)) :
    ∃ r₀ r₁ : ℝ, 1 < r₀ ∧ r₀ < 9 / 8 ∧ 15 / 8 < r₁ ∧ r₁ < 2 ∧
      InjOn f {x | x ∈ domain p ∧ (‖x‖ ≤ r₀ ∨ r₁ ≤ ‖x‖)} ∧
      ∀ x ∈ domain p, ‖x‖ ≤ r₀ ∨ r₁ ≤ ‖x‖ → Injective (fderiv ℝ f x) := by
  have hK : IsCompact {x : Vector (p + 1) | ‖x‖ = 1 ∨ ‖x‖ = 2} := by
    have he : {x : Vector (p + 1) | ‖x‖ = 1 ∨ ‖x‖ = 2} =
        sphere 0 1 ∪ sphere 0 2 := by
      ext x
      simp only [mem_setOf_eq, mem_union, mem_sphere, dist_zero_right]
    rw [he]
    exact (isCompact_sphere (0 : Vector (p + 1)) 1).union
      (isCompact_sphere (0 : Vector (p + 1)) 2)
  obtain ⟨U, hU, hKU, hUi, hUd⟩ :=
    CompactCoreImmersion.exists_open_injOn_near_compact hK hf hi hd
  obtain ⟨r₀, r₁, hr₀, hr₀small, hr₁large, hr₁, hsub⟩ :=
    exists_boundary_annuli_subset hU (fun x hx ↦ hKU hx)
  exact ⟨r₀, r₁, hr₀, hr₀small, hr₁large, hr₁, hUi.mono hsub,
    fun x hx he ↦ hUd x (hsub ⟨hx, he⟩)⟩

end NoExoticSixSphere.SphereAnnulus
