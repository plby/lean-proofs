import Wikipedia.HopfProblem.DegreeCollapseNativeSuspensionCurves

/-!
# Positive native height speed of a manifold-based suspension field

The actual retained-time identity is differentiated in the native
product atlas. The generator has time component exactly one and is
therefore nowhere zero, independently of the level's topology.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension

variable {Z N : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [FiniteDimensional ℝ Z] [TopologicalSpace N] [ChartedSpace Z N]
  [IsManifold 𝓘(ℝ, Z) ∞ N]

theorem nativeSuspensionField_height
    (Ψ : Diffeomorph (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ))
      (N × ℝ) (N × ℝ) ∞)
    (hheight : ∀ p, (Ψ p).2 = p.2) (p : N × ℝ) :
    (nativeSuspensionField Ψ p).2 = 1 := by
  let q := Ψ.symm p
  have hproj : (Prod.snd : N × ℝ → ℝ) ∘ Ψ = Prod.snd := funext hheight
  have hc := mfderiv_comp q
    (show MDifferentiableAt (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
      (Prod.snd : N × ℝ → ℝ) (Ψ q) from mdifferentiableAt_snd)
    (Ψ.contMDiff.mdifferentiableAt (by simp))
  rw [hproj, mfderiv_snd, mfderiv_snd] at hc
  have hv := congrArg (fun L : (Z × ℝ) →L[ℝ] ℝ => L (0, 1)) hc
  change (1 : ℝ) = (nativeSuspensionField Ψ p).2 at hv
  exact hv.symm

theorem nativeSuspensionField_ne_zero
    (Ψ : Diffeomorph (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, Z).prod 𝓘(ℝ, ℝ))
      (N × ℝ) (N × ℝ) ∞)
    (hheight : ∀ p, (Ψ p).2 = p.2) (p : N × ℝ) : nativeSuspensionField Ψ p ≠ 0 := by
  intro hz
  have hh := congrArg (fun v : Z × ℝ => v.2) hz
  rw [nativeSuspensionField_height Ψ hheight p] at hh
  exact one_ne_zero hh

end Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension
