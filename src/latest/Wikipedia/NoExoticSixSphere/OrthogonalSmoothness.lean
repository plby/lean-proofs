import Wikipedia.NoExoticSixSphere.CayleyAtlas

/-!
# Smoothness in the actual orthogonal operator space

For the verified Cayley atlas, a map is smooth exactly when its underlying
continuous-linear operator is smooth. This compares the manifold structure
with ambient operator calculus, rather than with a transported topology.
-/

open scoped Manifold ContDiff
open Set

namespace NoExoticSixSphere

open GLOrthonormalization OrthogonalPaths CayleyTransform CayleyAtlas

namespace OrthogonalSmoothness

variable {n : ℕ}

/-- The inclusion into the ambient space of operators is smooth. -/
theorem contMDiff_operator :
    ContMDiff 𝓘(ℝ, SkewOperators n) 𝓘(ℝ, Vector n →L[ℝ] Vector n) ∞
      (fun a : OrthogonalOperators n ↦ a.1.1) := by
  intro a
  rw [contMDiffAt_iff_source]
  have hs : ContDiff ℝ ∞ (fun K : SkewOperators n ↦ a.1.1.comp (operator K)) :=
    contDiff_const.clm_comp CayleyTransform.contDiff_operator
  change ContMDiffWithinAt 𝓘(ℝ, SkewOperators n) 𝓘(ℝ, Vector n →L[ℝ] Vector n) ∞
    (fun K ↦ a.1.1.comp (operator K)) (range id) _
  rw [range_id, contMDiffWithinAt_univ, contMDiffAt_iff_contDiffAt]
  exact hs.contDiffAt

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {f : M → OrthogonalOperators n} {x : M}

theorem contMDiffAt_iff_chart :
    ContMDiffAt I 𝓘(ℝ, SkewOperators n) ∞ f x ↔
      ContinuousAt f x ∧ ContMDiffAt I 𝓘(ℝ, SkewOperators n) ∞
        (fun y ↦ atOperator (f x) (f y)) x := by
  exact contMDiffAt_iff_target_of_mem_source
    (I' := 𝓘(ℝ, SkewOperators n)) (n := ∞) (f := f)
    (mem_atOperator_source (f x))

theorem mul_operator (a b : OrthogonalOperators n) :
    (mul a b).1.1 = a.1.1.comp b.1.1 := rfl

theorem contMDiffAt_coordinateExpression (a : OrthogonalOperators n)
    (h : ContMDiffAt I 𝓘(ℝ, Vector n →L[ℝ] Vector n) ∞ (fun y ↦ (f y).1.1) x)
    (hdom : mul (inverse a) (f x) ∈ domain) :
    ContMDiffAt I 𝓘(ℝ, SkewOperators n) ∞
      (fun y ↦ skewProjection (fraction ((inverse a).1.1.comp (f y).1.1))) x := by
  have hA : ContMDiffAt I 𝓘(ℝ, Vector n →L[ℝ] Vector n) ∞
      (fun y ↦ (inverse a).1.1.comp (f y).1.1) x := contMDiffAt_const.clm_comp h
  have hden : (1 + (inverse a).1.1.comp (f x).1.1).IsInvertible := hdom
  have hfrac : ContMDiffAt I 𝓘(ℝ, Vector n →L[ℝ] Vector n) ∞
      (fun y ↦ fraction ((inverse a).1.1.comp (f y).1.1)) x :=
    ContMDiffAt.comp (f := fun y ↦ (inverse a).1.1.comp (f y).1.1)
      (g := fraction (n := n)) x
      (contDiffAt_fraction (n := n) _ hden).contMDiffAt hA
  exact ContMDiffAt.comp (f := fun y ↦ fraction ((inverse a).1.1.comp (f y).1.1))
    (g := skewProjection (n := n)) x skewProjection.contMDiff.contMDiffAt hfrac

theorem chart_eventuallyEq_coordinateExpression (hf : ContinuousAt f x) :
    (fun y ↦ atOperator (f x) (f y)) =ᶠ[nhds x]
      (fun y ↦ skewProjection (fraction ((inverse (f x)).1.1.comp (f y).1.1))) := by
  filter_upwards [hf.eventually
    ((atOperator (f x)).open_source.mem_nhds (mem_atOperator_source (f x)))] with y hy
  have hymem : mul (inverse (f x)) (f y) ∈ domain := by
    change f y ∈ (atOperator (f x)).source at hy
    rw [atOperator_source] at hy
    exact hy
  rw [atOperator_apply]
  rw [coordinates_of_mem _ hymem]
  rw [← mul_operator]
  exact (skewProjection_fraction (n := n) (mul (inverse (f x)) (f y)) hymem).symm

/-- Smooth ambient families are smooth as maps into the orthogonal manifold. -/
theorem contMDiffAt_of_operator
    (h : ContMDiffAt I 𝓘(ℝ, Vector n →L[ℝ] Vector n) ∞ (fun y ↦ (f y).1.1) x) :
    ContMDiffAt I 𝓘(ℝ, SkewOperators n) ∞ f x := by
  have hf : ContinuousAt f x :=
    tendsto_subtype_rng.mpr (tendsto_subtype_rng.mpr h.continuousAt)
  apply contMDiffAt_iff_chart.mpr
  refine ⟨hf, ?_⟩
  have hdom : mul (inverse (f x)) (f x) ∈ domain := by
    rw [inverse_mul]
    exact identity_mem_domain
  exact (contMDiffAt_coordinateExpression (f x) h hdom).congr_of_eventuallyEq
    (chart_eventuallyEq_coordinateExpression hf)

theorem contMDiffAt_iff_operator :
    ContMDiffAt I 𝓘(ℝ, SkewOperators n) ∞ f x ↔
      ContMDiffAt I 𝓘(ℝ, Vector n →L[ℝ] Vector n) ∞ (fun y ↦ (f y).1.1) x :=
  ⟨fun h ↦ contMDiff_operator.contMDiffAt.comp x h, contMDiffAt_of_operator⟩

theorem contMDiff_iff_operator :
    ContMDiff I 𝓘(ℝ, SkewOperators n) ∞ f ↔
      ContMDiff I 𝓘(ℝ, Vector n →L[ℝ] Vector n) ∞ (fun y ↦ (f y).1.1) := by
  simp only [ContMDiff, contMDiffAt_iff_operator]

end OrthogonalSmoothness

end NoExoticSixSphere
