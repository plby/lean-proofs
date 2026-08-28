import Wikipedia.HopfProblem.DegreeCollapseNativeTransversePostcomposition

/-!
# Pulling a transverse target sheet back through the actual circle placement

The endpoint identifies the circle pointwise. Its inverse transports the
other sheet and preserves the native tangent-sum condition, retaining an
exact global postcomposition formula for the required basin germs.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {A B E HA HB H X Y N : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A] [TopologicalSpace HA]
  {I : ModelWithCorners ℝ A HA} [TopologicalSpace X] [ChartedSpace HA X]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace HB]
  {I' : ModelWithCorners ℝ B HB} [TopologicalSpace Y] [ChartedSpace HB Y]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {J : ModelWithCorners ℝ E H} [TopologicalSpace N] [ChartedSpace H N]

theorem exists_transverse_sheet_of_circle_placement (P : Diffeomorph J J N N ∞)
    {γ δ : X → N} {β : Y → N} {x : X} {y : Y}
    (hγ : MDifferentiableAt I J γ x) (hβ : MDifferentiableAt I' J β y)
    (hplace : ∀ z, P (γ z) = δ z) (hcross : β y = δ x)
    (htrans : NativeTransversality.At I I' J δ β x y) :
    ∃ β' : Y → N, MDifferentiableAt I' J β' y ∧ β' y = γ x ∧
      NativeTransversality.At I I' J γ β' x y ∧ ∀ z, P (β' z) = β z := by
  let β' := P.symm ∘ β
  have hβ' : MDifferentiableAt I' J β' y :=
    (P.symm.contMDiff.mdifferentiableAt (by simp)).comp y hβ
  have hcross' : β' y = γ x := by
    apply P.injective
    change P (P.symm (β y)) = P (γ x)
    rw [P.apply_symm_apply, hcross, hplace]
  have hforward (z : Y) : P (β' z) = β z := P.apply_symm_apply (β z)
  refine ⟨β', hβ', hcross', ?_, hforward⟩
  apply (TransverseGerms.native_transversality_partial_diffeomorph_iff
    P.toPartialDiffeomorph hγ hβ' hcross' (mem_univ _)).mpr
  have hγeq : P.toPartialDiffeomorph ∘ γ = δ := funext hplace
  have hβeq : P.toPartialDiffeomorph ∘ β' = β := funext hforward
  rw [hγeq, hβeq]
  exact htrans

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
