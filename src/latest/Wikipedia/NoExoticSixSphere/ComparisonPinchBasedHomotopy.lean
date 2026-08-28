import Wikipedia.NoExoticSixSphere.SphereResolutionPinchComparison
import Wikipedia.NoExoticSixSphere.SpherePinchHomotopy

/-!
# Comparison-pinch homotopies from the original based homotopies

Precomposition with the actual cap comparison and southern reflection carries
the based homotopies to the pinching pole. The existing genuine pinch homotopy
then compares the two comparison pinches, without changing their source maps.
-/

noncomputable section

open Set Function

namespace NoExoticSixSphere

theorem homotopicRel_precomp_at_base {X Y M : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace M]
    (f g : C(X, M)) (b : X) (H : f.HomotopicRel g {b})
    (p : C(Y, X)) (a : Y) (hp : p a = b) :
    (f.comp p).HomotopicRel (g.comp p) {a} := by
  obtain ⟨K⟩ := H
  refine ⟨{ toHomotopy := K.toHomotopy.compContinuousMap p, prop' := ?_ }⟩
  intro t y hy
  have hy' : y = a := mem_singleton_iff.mp hy
  have hpy : p y = b := (congrArg p hy').trans hp
  change K (t, p y) = f (p y)
  rw [hpy]
  exact K.eq_fst t (mem_singleton b)

namespace SphereSumNeck

variable {M : Type*} [TopologicalSpace M]

theorem comparisonPinch_homotopic_of_based (f₀ g₀ f₁ g₁ : C(Sphere 3, M))
    (ε : ℝ) (hε : ε ≠ 0)
    (hzero₀ : f₀ (sourceChart 0) = g₀ (sourceChart 0))
    (hzero₁ : f₁ (sourceChart 0) = g₁ (sourceChart 0))
    (Hf : f₀.HomotopicRel f₁ {sourceChart 0}) (Hg : g₀.HomotopicRel g₁ {sourceChart 0}) :
    (comparisonPinch f₀ g₀ ε hε hzero₀).Homotopic (comparisonPinch f₁ g₁ ε hε hzero₁) := by
  have Hn : (northPinchInput f₀ ε hε).HomotopicRel (northPinchInput f₁ ε hε)
      {antipode pinchPole} :=
    homotopicRel_precomp_at_base f₀ f₁ (sourceChart 0) Hf
      ⟨capPinchComparison ε hε, (capPinchComparison ε hε).continuous⟩
      (antipode pinchPole) (capPinchComparison_base ε hε)
  have Hs : (southPinchInput g₀ ε hε).HomotopicRel (southPinchInput g₁ ε hε)
      {antipode pinchPole} := by
    apply homotopicRel_precomp_at_base g₀ g₁ (sourceChart 0) Hg
      ⟨fun x ↦ capPinchComparison ε hε (tailReflection x),
        (capPinchComparison ε hε).continuous.comp contMDiff_tailReflection.continuous⟩
      (antipode pinchPole)
    change capPinchComparison ε hε (tailReflection (antipode pinchPole)) = sourceChart 0
    rw [tailReflection_base, capPinchComparison_base]
  exact SphereFold.pinch_homotopic pinchPole
    (northPinchInput f₀ ε hε) (southPinchInput g₀ ε hε)
    (northPinchInput f₁ ε hε) (southPinchInput g₁ ε hε)
    (pinchInput_base f₀ g₀ ε hε hzero₀) (pinchInput_base f₁ g₁ ε hε hzero₁) Hn Hs

end SphereSumNeck
end NoExoticSixSphere
