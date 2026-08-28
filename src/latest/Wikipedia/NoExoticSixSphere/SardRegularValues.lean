import Wikipedia.NoExoticSixSphere.SardManifoldSource

/-!
# Density of regular values between smooth manifolds

Apply the proved vector-valued Sard theorem inside a genuine target chart.
Only the preimage of that chart's source is used. The invertible chart
differential transfers regularity back to the original target manifold.
-/

open scoped Manifold ContDiff
open Set MeasureTheory MeasureTheory.Measure

namespace NoExoticSixSphere.Sard

variable {B F : Type} {H K M N : Type*}
  [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ B H} {J : ModelWithCorners ℝ F K}
  [I.Boundaryless] [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N]
  [SecondCountableTopology M]

theorem dense_regularValues {f : M → N} (hf : ContMDiff I J ∞ f) :
    Dense {b | ∀ x, f x = b → Function.Surjective (mfderiv I J f x)} := by
  let : MeasurableSpace F := borel F
  let : BorelSpace F := ⟨rfl⟩
  let μ : Measure F := addHaar
  rw [dense_iff_inter_open]
  rintro V hV ⟨b, hb⟩
  let c := modelChartPartialDiffeomorph (I := J) b
  let U := f ⁻¹' c.source
  let g : M → F := c ∘ f
  let W := c.target ∩ c.symm ⁻¹' V
  have hU : IsOpen U := c.open_source.preimage hf.continuous
  have hg : ContMDiffOn I 𝓘(ℝ, F) ∞ g U :=
    c.contMDiffOn.comp hf.contMDiffOn (fun _ hx ↦ hx)
  have hnull := measure_manifoldCriticalValues_eq_zero μ hU hg
  have hdense : Dense
      (g '' {x | x ∈ U ∧ ¬ Function.Surjective (mfderiv I 𝓘(ℝ, F) g x)})ᶜ :=
    interior_eq_empty_iff_dense_compl.mp (μ.interior_eq_empty_of_null hnull)
  have hW : IsOpen W := c.toOpenPartialHomeomorph.isOpen_inter_preimage_symm hV
  have hbsource : b ∈ c.source := mem_extChartAt_source b
  have hWne : W.Nonempty := ⟨c b, c.map_source' hbsource, by
    change c.symm (c b) ∈ V
    have heq : c.symm (c b) = b := c.left_inv' hbsource
    rwa [heq]⟩
  obtain ⟨v, hvnot, hvW⟩ := hdense.exists_mem_open hW hWne
  refine ⟨c.symm v, hvW.2, ?_⟩
  intro x hx
  have hxU : x ∈ U := by
    change f x ∈ c.source
    rw [hx]
    exact c.map_target' hvW.1
  have hgx : g x = v := by
    change c (f x) = v
    exact (congrArg c hx).trans (c.right_inv' hvW.1)
  have hreg : Function.Surjective (mfderiv I 𝓘(ℝ, F) g x) := by
    by_contra h
    exact hvnot ⟨x, ⟨hxU, h⟩, hgx⟩
  have hc : IsLocalDiffeomorphAt J 𝓘(ℝ, F) ∞ c (f x) :=
    ⟨c, hxU, fun _ _ ↦ rfl⟩
  have hci := (hc.mfderivToContinuousLinearEquiv (by simp)).injective
  have hcomp := mfderiv_comp x (hc.mdifferentiableAt (by simp))
    ((hf x).mdifferentiableAt (by simp))
  intro w
  obtain ⟨u, hu⟩ := hreg (mfderiv J 𝓘(ℝ, F) c (f x) w)
  refine ⟨u, hci ?_⟩
  change mfderiv I 𝓘(ℝ, F) g x = _ at hcomp
  rw [hcomp] at hu
  exact hu

end NoExoticSixSphere.Sard
