import Wikipedia.HopfProblem.DegreeCollapseNativeWholeLevelHolonomy

/-!
# Exact exterior half-orbits after native whole-level insertion

The stationary lower and upper suspension collars give equality with
the original flow on the entire exterior half-lines, including their
section endpoints. This follows from the actual cylinder formulas.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension

variable {Z N M : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [FiniteDimensional ℝ Z] [TopologicalSpace N] [ChartedSpace Z N]
  [IsManifold 𝓘(ℝ, Z) ∞ N] [TopologicalSpace M]

theorem native_whole_level_exterior_tails
    (A : N × ℝ → M) (ι : N → M) (H G : Flow ℝ M)
    (hformula : ∀ p, A p = H p.2 (ι p.1))
    (D : Diffeomorph 𝓘(ℝ, Z) 𝓘(ℝ, Z) N N ∞)
    (Ψ : Diffeomorph (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ))
      (N × ℝ) (N × ℝ) ∞)
    (hleft : ∀ p, p.2 ≤ 1 / 3 → Ψ p = p)
    (hright : ∀ p, 2 / 3 ≤ p.2 → Ψ p = (D p.1, p.2))
    (hfull : ∀ p t, G t (A p) = A (nativeSuspensionFlow Ψ t p)) :
    (∀ x, ∀ t : ℝ, t ≤ 0 → G t (A (x, 0)) = H t (A (x, 0))) ∧
    ∀ x, ∀ t : ℝ, 0 ≤ t → G t (A (x, 1)) = H t (A (x, 1)) := by
  constructor
  · intro x t ht
    have h0 : Ψ (x, (0 : ℝ)) = (x, 0) := hleft (x, 0) (by norm_num)
    have hf : nativeSuspensionFlow Ψ t (x, 0) = (x, t) := by
      rw [← h0, nativeSuspensionFlow_chart, zero_add]
      exact hleft (x, t) (by linarith)
    rw [hfull, hf, hformula, hformula, H.map_zero_apply]
  · intro x t ht
    have h1 : Ψ (D.symm x, (1 : ℝ)) = (x, 1) := by
      rw [hright (D.symm x, 1) (by norm_num), D.apply_symm_apply]
    have hf : nativeSuspensionFlow Ψ t (x, 1) = (x, 1 + t) := by
      rw [← h1, nativeSuspensionFlow_chart]
      rw [hright (D.symm x, 1 + t) (by linarith), D.apply_symm_apply]
    rw [hfull, hf, hformula, hformula, ← H.map_add]
    congr 1
    ring

end Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension
