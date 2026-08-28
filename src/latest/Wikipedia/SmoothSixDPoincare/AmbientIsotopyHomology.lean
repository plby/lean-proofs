import Wikipedia.SmoothSixDPoincare.AmbientIsotopy
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleHomotopy

/-!
# Native ambient isotopies preserve the actual singular homology maps

Restrict the recorded jointly smooth isotopy to the unit time interval.
The resulting genuine continuous homotopy proves invariance for every
continuous map acted upon by its endpoint diffeomorphism.
-/

noncomputable section

open ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.SupportedDiffeomorph

open Wikipedia.HopfProblem.SingularMayerVietoris
  Wikipedia.HopfProblem.PeriodTorusHigherHomology

variable {F H M : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] {J : ModelWithCorners ℝ F H}
  [TopologicalSpace M] [ChartedSpace H M]
  {e : Diffeomorph J J M M ∞}

theorem IsotopicToIdentity.homotopic (he : IsotopicToIdentity e) :
    (ContinuousMap.id M).Homotopic e.toHomeomorph.toHomotopyEquiv.toFun := by
  obtain ⟨A, hA, hA₀, hA₁, _⟩ := he
  exact ⟨{
    toFun := fun p => A (p.1.val, p.2)
    continuous_toFun := hA.continuous.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
    map_zero_left := hA₀
    map_one_left := hA₁ }⟩

theorem IsotopicToIdentity.comp_homotopic {X : Type*} [TopologicalSpace X]
    (he : IsotopicToIdentity e) (g : C(X, M)) :
    g.Homotopic (e.toHomeomorph.toHomotopyEquiv.toFun.comp g) := by
  simpa using he.homotopic.comp (ContinuousMap.Homotopic.refl g)

theorem IsotopicToIdentity.comp_homologyMap {X : Type} [TopologicalSpace X]
    (he : IsotopicToIdentity e) (g : C(X, M)) (k : ℕ) :
    singularHomologyMap (e.toHomeomorph.toHomotopyEquiv.toFun.comp g) k =
      singularHomologyMap g k :=
  (homotopic_homologyMap (he.comp_homotopic g) k).symm

end Wikipedia.SmoothSixDPoincare.SupportedDiffeomorph
