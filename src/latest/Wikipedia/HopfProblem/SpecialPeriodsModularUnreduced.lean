import Wikipedia.HopfProblem.SpecialPeriodsModularUnreducedAnalytic
import Wikipedia.HopfProblem.SpecialPeriodsModularUnreducedCoverTools

/-!
# The unreduced modular covering and its holomorphic lifts

The source here is the actual upper half-plane with the elliptic fibres
removed, not the modular orbit quotient. Proper discontinuity and local
injectivity construct an evenly covered neighbourhood even though the
`SL₂(ℤ)` action has the ineffective elements `±1`. This proves the regular
modular map is a covering and is locally biholomorphic. Its continuous
covering lifts are holomorphic by the checked analytic inverse-function
argument.
-/

noncomputable section

open Set Topology UpperHalfPlane
open scoped ContDiff Manifold MatrixGroups

namespace Wikipedia.HopfProblem.SpecialPeriods

/-- The actual Eisenstein-series modular function is a covering on the
regular finite values, with its unreduced upper-half-plane source. -/
theorem modularJ_regular_isCoveringMapOn : IsCoveringMapOn modularJ modularRegularValues := by
  intro c hc
  obtain ⟨z, rfl⟩ := modularJ_surjective c
  obtain ⟨h₀, h₁⟩ := (mem_modularRegularValues _).mp hc
  obtain ⟨U, hUo, hz, hinj⟩ := modularJ_regular_injOn_neighbourhood z h₀ h₁
  exact ModularCoverTools.isEvenlyCovered_of_injective_open_neighborhood
    (G := SL(2, ℤ)) modularJ_isOpenQuotientMap
    (fun {a b} => modularJ_eq_iff_mem_orbit a b) z U hUo hz hinj

theorem modularUnreducedJ_isCoveringMap : IsCoveringMap modularUnreducedJ :=
  modularJ_regular_isCoveringMapOn.isCoveringMap_restrictPreimage

theorem modularUnreducedJ_isLocalHomeomorph : IsLocalHomeomorph modularUnreducedJ :=
  modularUnreducedJ_isCoveringMap.isLocalHomeomorph

/-- The local homeomorphisms are analytic in both directions for the
inherited complex structures on the unreduced source and regular target. -/
theorem modularUnreducedJ_isLocalDiffeomorph :
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω modularUnreducedJ := by
  intro x
  obtain ⟨e, hx, he⟩ := modularUnreducedJ_isLocalHomeomorph x
  let d : PartialDiffeomorph 𝓘(ℂ) 𝓘(ℂ) modularRegularUpper modularRegularPlane ω :=
    { toPartialEquiv := e.toPartialEquiv
      open_source := e.open_source
      open_target := e.open_target
      contMDiffOn_toFun := by
        change ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω e e.source
        simpa only [he] using (modularUnreducedJ_holomorphic.contMDiffOn (s := e.source))
      contMDiffOn_invFun := by
        change ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω e.symm e.target
        intro y hy
        apply ContMDiffAt.contMDiffWithinAt
        apply modularUnreducedJ_contMDiffAt_lift 𝓘(ℂ) (e.symm.continuousAt hy)
        have hinv : modularUnreducedJ ∘ e.symm =ᶠ[𝓝 y] id := by
          filter_upwards [e.open_target.mem_nhds hy] with w hw
          change modularUnreducedJ (e.symm w) = w
          rw [he]
          exact e.right_inv hw
        exact contMDiffAt_id.congr_of_eventuallyEq hinv }
  exact ⟨d, hx, fun y _ => congrFun he y⟩

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  (I : ModelWithCorners ℂ E H)

/-- Over a simply connected locally path-connected source, a holomorphic
map into the regular j-plane has a unique holomorphic lift after a value
of the lift at one point is specified. The covering and analyticity of
the lift are both proved for the actual modular function. -/
theorem modularUnreducedJ_existsUnique_holomorphic_lift
    [SimplyConnectedSpace M] [LocallyPathConnectedSpace M]
    (f : M → modularRegularPlane) (hf : ContMDiff I 𝓘(ℂ) ω f)
    (x₀ : M) (z₀ : modularRegularUpper) (hz₀ : modularUnreducedJ z₀ = f x₀) :
    ∃! F : M → modularRegularUpper,
      ContMDiff I 𝓘(ℂ) ω F ∧ F x₀ = z₀ ∧ modularUnreducedJ ∘ F = f := by
  let fc : C(M, modularRegularPlane) := ⟨f, hf.continuous⟩
  obtain ⟨F, ⟨hF₀, hFj⟩, hFu⟩ :=
    modularUnreducedJ_isCoveringMap.existsUnique_continuousMap_lifts fc x₀ z₀ hz₀
  have hFholo : ContMDiff I 𝓘(ℂ) ω F := by
    apply modularUnreducedJ_contMDiff_lift I F.continuous
    rw [hFj]
    exact hf
  refine ⟨F, ⟨hFholo, hF₀, hFj⟩, ?_⟩
  intro G hG
  have hGe : (⟨G, hG.1.continuous⟩ : C(M, modularRegularUpper)) = F :=
    hFu ⟨G, hG.1.continuous⟩ ⟨hG.2.1, hG.2.2⟩
  exact congrArg (fun u : C(M, modularRegularUpper) => (u : M → modularRegularUpper)) hGe

end Wikipedia.HopfProblem.SpecialPeriods
