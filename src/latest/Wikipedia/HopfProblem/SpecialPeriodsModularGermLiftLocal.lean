import Wikipedia.HopfProblem.SpecialPeriodsModularLocalLift
import Wikipedia.HopfProblem.SpecialPeriodsModularSurjective

/-!
# Local modular lifts of arbitrary analytic germs

An analytic germ lifts through the actual modular function provided its order
over zero is divisible by three and its order over `1728` is even.  At the
critical values the lift is supplied by the proved cubic or quadratic modular
chart.  At regular values, surjectivity of the actual modular function and its
analytic local inverse supply the lift.  Every branch is defined on a genuine
positive-radius ball and takes values in the upper half-plane.
-/

noncomputable section

open Filter Metric Set UpperHalfPlane
open scoped Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.ModularGermLift

/-- At a regular value, the local lift may be centered at any specified
point of its actual modular fibre. -/
theorem exists_regular_local_lift_at {F : ℂ → ℂ} {a : ℂ}
    (hF : AnalyticAt ℂ F a) (b : ℍ) (hb : modularJ b = F a)
    (h₀ : F a ≠ 0) (h₁ : F a ≠ 1728) :
    ∃ r : ℝ, 0 < r ∧ ∃ τ : ℂ → ℂ,
      AnalyticOnNhd ℂ τ (ball a r) ∧ τ a = (b : ℂ) ∧
      MapsTo τ (ball a r) upperHalfPlaneSet ∧
      ∀ z ∈ ball a r, modularJ (ofComplex (τ z)) = F z := by
  have hb₀ : modularJ b ≠ 0 := hb ▸ h₀
  have hb₁ : modularJ b ≠ 1728 := hb ▸ h₁
  let g : ℂ → ℂ := modularLocalInverse b hb₀ hb₁
  let τ : ℂ → ℂ := fun z => g (F z)
  have hg : AnalyticAt ℂ g (F a) := by
    rw [← hb]
    exact modularLocalInverse_analyticAt b hb₀ hb₁
  have hτ : AnalyticAt ℂ τ a := hg.comp hF
  have hτa : τ a = (b : ℂ) := by
    dsimp only [τ]
    rw [← hb]
    simpa only [ofComplex_apply] using
      (modularLocalInverse_eventually_left_inverse b hb₀ hb₁).self_of_nhds
  have hU : ∀ᶠ z in 𝓝 a, τ z ∈ upperHalfPlaneSet := by
    apply hτ.continuousAt.preimage_mem_nhds
    rw [hτa]
    exact isOpen_upperHalfPlaneSet.mem_nhds b.im_pos
  have hinv : ∀ᶠ w in 𝓝 (F a), modularJ (ofComplex (g w)) = w := by
    rw [← hb]
    exact modularLocalInverse_eventually_right_inverse b hb₀ hb₁
  have hj : ∀ᶠ z in 𝓝 a, modularJ (ofComplex (τ z)) = F z :=
    hF.continuousAt.tendsto.eventually hinv
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (hτ.eventually_analyticAt.and (hU.and hj))
  exact ⟨r, hr, τ, fun z hz => (hball hz).1, hτa,
    fun z hz => (hball hz).2.1, fun z hz => (hball hz).2.2⟩

/-- **Local modular lifting.** The critical-order conditions are required
only when the central value is the corresponding critical value.  All local
branches, including the regular branch, are constructed from the actual `j`. -/
theorem exists_local_lift {F : ℂ → ℂ} {a : ℂ} (hF : AnalyticAt ℂ F a)
    (h₃ : F a = 0 → ∃ k : ℕ, analyticOrderAt F a = (3 * k : ℕ))
    (h₂ : F a = 1728 →
      ∃ k : ℕ, analyticOrderAt (fun z => F z - 1728) a = (2 * k : ℕ)) :
    ∃ r : ℝ, 0 < r ∧ ∃ τ : ℂ → ℂ,
      AnalyticOnNhd ℂ τ (ball a r) ∧ MapsTo τ (ball a r) upperHalfPlaneSet ∧
      ∀ z ∈ ball a r, modularJ (ofComplex (τ z)) = F z := by
  by_cases ha₀ : F a = 0
  · obtain ⟨k, hk⟩ := h₃ ha₀
    have hkpos : 0 < k := by
      apply Nat.pos_of_ne_zero
      intro hk₀
      exact (hF.analyticOrderAt_ne_zero.mpr ha₀) (by simpa only [hk₀, mul_zero,
        Nat.cast_zero] using hk)
    obtain ⟨r, hr, τ, hτ, -, hU, hj, -⟩ :=
      exists_modularJ_lift_of_order_multiple_three hF hk hkpos
    exact ⟨r, hr, τ, hτ, hU, hj⟩
  · by_cases ha₁ : F a = 1728
    · obtain ⟨k, hk⟩ := h₂ ha₁
      have hkpos : 0 < k := by
        apply Nat.pos_of_ne_zero
        intro hk₀
        have hshift : AnalyticAt ℂ (fun z => F z - 1728) a := hF.sub analyticAt_const
        have hn : analyticOrderAt (fun z => F z - 1728) a ≠ 0 :=
          hshift.analyticOrderAt_ne_zero.mpr (sub_eq_zero.mpr ha₁)
        exact hn (by simpa only [hk₀, mul_zero, Nat.cast_zero] using hk)
      obtain ⟨r, hr, τ, hτ, -, hU, hj, -⟩ :=
        exists_modularJ_lift_of_order_multiple_two hF hk hkpos
      exact ⟨r, hr, τ, hτ, hU, hj⟩
    · obtain ⟨b, hb⟩ := modularJ_surjective (F a)
      obtain ⟨r, hr, τ, hτ, -, hU, hj⟩ :=
        exists_regular_local_lift_at hF b hb ha₀ ha₁
      exact ⟨r, hr, τ, hτ, hU, hj⟩

/-- The local lift can be chosen inside any prescribed open neighborhood
of the source point. -/
theorem exists_local_lift_ball_subset {F : ℂ → ℂ} {a : ℂ} {S : Set ℂ}
    (hS : IsOpen S) (ha : a ∈ S) (hF : AnalyticAt ℂ F a)
    (h₃ : F a = 0 → ∃ k : ℕ, analyticOrderAt F a = (3 * k : ℕ))
    (h₂ : F a = 1728 →
      ∃ k : ℕ, analyticOrderAt (fun z => F z - 1728) a = (2 * k : ℕ)) :
    ∃ r : ℝ, 0 < r ∧ ball a r ⊆ S ∧ ∃ τ : ℂ → ℂ,
      AnalyticOnNhd ℂ τ (ball a r) ∧ MapsTo τ (ball a r) upperHalfPlaneSet ∧
      ∀ z ∈ ball a r, modularJ (ofComplex (τ z)) = F z := by
  obtain ⟨r, hr, τ, hτ, hU, hj⟩ := exists_local_lift hF h₃ h₂
  obtain ⟨s, hs, hsS⟩ := Metric.mem_nhds_iff.mp (hS.mem_nhds ha)
  have hsub : ball a (min r s) ⊆ ball a r := ball_subset_ball (min_le_left _ _)
  refine ⟨min r s, lt_min hr hs, (ball_subset_ball (min_le_right _ _)).trans hsS,
    τ, hτ.mono hsub, ?_, ?_⟩
  · exact hU.mono_left hsub
  · exact fun z hz => hj z (hsub hz)

end Wikipedia.HopfProblem.SpecialPeriods.ModularGermLift
