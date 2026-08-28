import Wikipedia.SmoothSixDPoincare.FramedSurgerySmoothOverlap
import Wikipedia.NoExoticSixSphere.ModelInteriorCoordinates

/-!
# Construct the common model chart for the new surgery patch

The dimension equality is obtained from the differential of the given full
face chart. Thus the smooth model chart used to rechart the new patch is
constructed from the actual framed face, not postulated separately.
-/

noncomputable section

open Set Function Topology Metric
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.FramedSurgery

open PuncturedHandle

variable {E F G H X : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
  [TopologicalSpace X] [ChartedSpace H X]
  {m : ℕ} [Fact (Module.finrank ℝ E = m + 1)]
  (A : SmoothClosedFace (𝓡 m) J (UnitSphere E) F X)
  (n : ℕ) [Fact (Module.finrank ℝ F = n + 1)]

include A in
theorem model_finrank :
    Module.finrank ℝ (E × EuclideanSpace ℝ (Fin n)) = Module.finrank ℝ G := by
  obtain ⟨z⟩ := nonempty_overlap (E := E) (F := F) m n
  let x : UnitSphere E × F := (z.1, 0)
  have hx : x ∈ A.chart.source := A.source ⟨mem_univ _, by simp [x]⟩
  let d := mfderiv ((𝓡 m).prod 𝓘(ℝ, F)) J A.chart x
  have hd : Bijective d := PartialChart.bijective_mfderiv A.chart hx
  have hdim := (LinearEquiv.ofBijective d.toLinearMap hd).finrank_eq
  change Module.finrank ℝ (EuclideanSpace ℝ (Fin m) × F) = Module.finrank ℝ G at hdim
  simp only [Module.finrank_prod, finrank_euclideanSpace_fin] at hdim ⊢
  have hE := Fact.out (p := Module.finrank ℝ E = m + 1)
  have hF := Fact.out (p := Module.finrank ℝ F = n + 1)
  omega

include A in
theorem exists_modelChart [FiniteDimensional ℝ G] [J.Boundaryless] :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, E × EuclideanSpace ℝ (Fin n)) J
        (E × EuclideanSpace ℝ (Fin n)) H ∞,
      Φ.source = univ ∧ ∀ y ∈ Φ.target, J y ∈ interior (range J) := by
  let L : (E × EuclideanSpace ℝ (Fin n)) ≃L[ℝ] G :=
    ContinuousLinearEquiv.ofFinrankEq (model_finrank A n)
  let C := NoExoticSixSphere.modelInteriorPartialDiffeomorph J univ isOpen_univ
    (by rw [ModelWithCorners.range_eq_univ])
  refine ⟨L.toDiffeomorph.toPartialDiffeomorph.trans C.symm, ?_, ?_⟩
  · exact eq_univ_of_forall fun _ => ⟨mem_univ _, mem_univ _⟩
  · intro y _
    simp only [ModelWithCorners.range_eq_univ, interior_univ, mem_univ]

end Wikipedia.SmoothSixDPoincare.FramedSurgery
