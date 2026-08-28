import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicCayleyAtlas

/-! # Smoothness of symplectic families in their original real operator coordinates -/

noncomputable section

open scoped Manifold ContDiff
open Set

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns

open NoExoticSixSphere.GLOrthonormalization NoExoticSixSphere.CayleyTransform CayleyAtlas

namespace Smoothness

variable {n : ℕ}

theorem contMDiff_operator :
    ContMDiff 𝓘(ℝ, SkewSpace n) 𝓘(ℝ, Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)) ∞
      (fun a : symplecticSubgroup n => a.val.val.val) := by
  intro a
  rw [contMDiffAt_iff_source]
  have hs : ContDiff ℝ ∞ (fun K : SkewSpace n =>
      a.val.val.val.comp (operator (toOrthogonalSkew n K))) :=
    contDiff_const.clm_comp contDiff_cayleyOperator
  change ContMDiffWithinAt 𝓘(ℝ, SkewSpace n)
    𝓘(ℝ, Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)) ∞
    (fun K => a.val.val.val.comp (operator (toOrthogonalSkew n K))) (range id) _
  rw [range_id, contMDiffWithinAt_univ, contMDiffAt_iff_contDiffAt]
  exact hs.contDiffAt

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {f : M → symplecticSubgroup n} {x : M}

theorem contMDiffAt_iff_chart :
    ContMDiffAt I 𝓘(ℝ, SkewSpace n) ∞ f x ↔
      ContinuousAt f x ∧ ContMDiffAt I 𝓘(ℝ, SkewSpace n) ∞
        (fun y => atOperator (f x) (f y)) x :=
  contMDiffAt_iff_target_of_mem_source
    (I' := 𝓘(ℝ, SkewSpace n)) (n := ∞) (f := f) (mem_atOperator_source (f x))

theorem mul_operator (a b : symplecticSubgroup n) :
    (a * b).val.val.val = a.val.val.val.comp b.val.val.val := rfl

theorem contMDiffAt_coordinateExpression (a : symplecticSubgroup n)
    (h : ContMDiffAt I 𝓘(ℝ, Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)) ∞
      (fun y => (f y).val.val.val) x)
    (hdom : a⁻¹ * f x ∈ cayleyDomain n) :
    ContMDiffAt I 𝓘(ℝ, SkewSpace n) ∞
      (fun y => skewProjection n (fraction ((a⁻¹).val.val.val.comp (f y).val.val.val))) x := by
  have hA : ContMDiffAt I 𝓘(ℝ, Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)) ∞
      (fun y => (a⁻¹).val.val.val.comp (f y).val.val.val) x := contMDiffAt_const.clm_comp h
  have hden : (1 + (a⁻¹).val.val.val.comp (f x).val.val.val).IsInvertible := hdom
  have hfrac : ContMDiffAt I 𝓘(ℝ, Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)) ∞
      (fun y => fraction ((a⁻¹).val.val.val.comp (f y).val.val.val)) x :=
    ContMDiffAt.comp (f := fun y => (a⁻¹).val.val.val.comp (f y).val.val.val)
      (g := fraction (n := 4 * n + 4)) x
      (contDiffAt_fraction _ hden).contMDiffAt hA
  exact ContMDiffAt.comp (f := fun y => fraction ((a⁻¹).val.val.val.comp (f y).val.val.val))
    (g := skewProjection n) x contDiff_skewProjection.contMDiff.contMDiffAt hfrac

theorem chart_eventuallyEq_coordinateExpression (hf : ContinuousAt f x) :
    (fun y => atOperator (f x) (f y)) =ᶠ[nhds x]
      (fun y => skewProjection n
        (fraction (((f x)⁻¹).val.val.val.comp (f y).val.val.val))) := by
  filter_upwards [hf.eventually
    ((atOperator (f x)).open_source.mem_nhds (mem_atOperator_source (f x)))] with y hy
  have hymem : (f x)⁻¹ * f y ∈ cayleyDomain n := by
    change f y ∈ (atOperator (f x)).source at hy
    rw [atOperator_source] at hy
    exact hy
  rw [atOperator_apply, cayleyCoordinates_of_mem n _ hymem, ← mul_operator]
  exact (skewProjection_fraction ((f x)⁻¹ * f y) hymem).symm

/-- Smoothness in the actual ambient operator space implies smoothness in the Cayley atlas. -/
theorem contMDiffAt_of_operator
    (h : ContMDiffAt I 𝓘(ℝ, Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)) ∞
      (fun y => (f y).val.val.val) x) :
    ContMDiffAt I 𝓘(ℝ, SkewSpace n) ∞ f x := by
  have hf : ContinuousAt f x := tendsto_subtype_rng.mpr
    (tendsto_subtype_rng.mpr (tendsto_subtype_rng.mpr h.continuousAt))
  apply contMDiffAt_iff_chart.mpr
  refine ⟨hf, ?_⟩
  have hdom : (f x)⁻¹ * f x ∈ cayleyDomain n := by
    rw [inv_mul_cancel]
    exact one_mem_cayleyDomain n
  exact (contMDiffAt_coordinateExpression (f x) h hdom).congr_of_eventuallyEq
    (chart_eventuallyEq_coordinateExpression hf)

theorem contMDiffAt_iff_operator :
    ContMDiffAt I 𝓘(ℝ, SkewSpace n) ∞ f x ↔
      ContMDiffAt I 𝓘(ℝ, Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)) ∞
        (fun y => (f y).val.val.val) x :=
  ⟨fun h => contMDiff_operator.contMDiffAt.comp x h, contMDiffAt_of_operator⟩

theorem contMDiff_iff_operator :
    ContMDiff I 𝓘(ℝ, SkewSpace n) ∞ f ↔
      ContMDiff I 𝓘(ℝ, Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)) ∞
        (fun y => (f y).val.val.val) := by
  simp only [ContMDiff, contMDiffAt_iff_operator]

end Smoothness

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns
