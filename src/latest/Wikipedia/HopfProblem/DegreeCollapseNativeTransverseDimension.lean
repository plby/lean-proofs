import Wikipedia.SmoothSixDPoincare.NativeTransversalityStability
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
# Dimension obstruction and removal of an ignored source factor

Native transversality at an actual crossing forces the sum of the source
dimensions to be at least the target dimension. A dummy manifold factor
ignored by one sheet does not change its tangent image, so transversality
of the enlarged source implies transversality of the original sheets.
-/

noncomputable section

open Set Function Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseRearrangement

variable {D Z G H H' K X Y N : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace K]
  {I : ModelWithCorners ℝ D H} {I' : ModelWithCorners ℝ Z H'}
  {J : ModelWithCorners ℝ G K}
  [TopologicalSpace X] [ChartedSpace H X]
  [TopologicalSpace Y] [ChartedSpace H' Y]
  [TopologicalSpace N] [ChartedSpace K N]

theorem native_transverse_dimension_bound [FiniteDimensional ℝ D] [FiniteDimensional ℝ Z]
    {f : X → N} {g : Y → N} {x : X} {y : Y}
    (ht : NativeTransversality.At I I' J f g x y) (hxy : g y = f x) :
    Module.finrank ℝ G ≤ Module.finrank ℝ D + Module.finrank ℝ Z := by
  let L : (D × Z) →L[ℝ] G := by
    exact (mfderiv I J f x : D →L[ℝ] G).coprod (mfderiv I' J g y : Z →L[ℝ] G)
  have hL : Surjective L := ht hxy
  have hh := LinearMap.finrank_le_finrank_of_surjective (f := L.toLinearMap) hL
  simpa only [Module.finrank_prod] using hh

theorem disjoint_ranges_of_native_transverse_dimension
    [FiniteDimensional ℝ D] [FiniteDimensional ℝ Z]
    {f : X → N} {g : Y → N}
    (ht : ∀ x y, NativeTransversality.At I I' J f g x y)
    (hdim : Module.finrank ℝ D + Module.finrank ℝ Z < Module.finrank ℝ G) :
    Disjoint (range f) (range g) := by
  apply disjoint_left.mpr
  rintro z ⟨x, hx⟩ ⟨y, hy⟩
  exact (not_le_of_gt hdim) (native_transverse_dimension_bound (ht x y) (hy.trans hx.symm))

theorem native_transverse_of_ignored_factor
    {R H'' W : Type*} [NormedAddCommGroup R] [NormedSpace ℝ R]
    [TopologicalSpace H''] {I'' : ModelWithCorners ℝ R H''}
    [TopologicalSpace W] [ChartedSpace H'' W]
    {f : X → N} {g : Y → N} {x : X} {y : Y} (w : W)
    (hf : MDifferentiableAt I J f x)
    (ht : NativeTransversality.At (I.prod I'') I' J (f ∘ Prod.fst) g (x, w) y) :
    NativeTransversality.At I I' J f g x y := by
  intro hxy
  have hsurj := ht hxy
  have hd : (mfderiv (I.prod I'') J (f ∘ Prod.fst) (x, w) : (D × R) →L[ℝ] G) =
      (mfderiv I J f x : D →L[ℝ] G).comp (ContinuousLinearMap.fst ℝ D R) := by
    rw [mfderiv_comp (x, w) hf mdifferentiableAt_fst, mfderiv_fst]
    rfl
  change Surjective ((mfderiv (I.prod I'') J (f ∘ Prod.fst) (x, w) : (D × R) →L[ℝ] G).coprod
    (mfderiv I' J g y : Z →L[ℝ] G)) at hsurj
  rw [hd] at hsurj
  intro v
  obtain ⟨⟨⟨a, b⟩, c⟩, hh⟩ := hsurj v
  exact ⟨(a, c), hh⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseRearrangement
