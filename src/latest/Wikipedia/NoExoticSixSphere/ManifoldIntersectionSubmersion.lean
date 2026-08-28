import Wikipedia.NoExoticSixSphere.ManifoldIntersectionPerturbation
import Wikipedia.NoExoticSixSphere.ParametricRegularOpen

/-!
# Parametric regularity for two actual manifold-valued sphere families

The derivative of the moving sheet with respect to its affine parameter is
surjective. Composing with the valid target chart preserves surjectivity;
the fixed second sheet contributes no parameter derivative. Parametric Sard
therefore applies to the genuine coupled coincidence equation.
-/

noncomputable section

open Set Function
open MeasureTheory MeasureTheory.Measure
open scoped Manifold ContDiff

namespace NoExoticSixSphere.ManifoldIntersectionFamily

open GLOrthonormalization EuclideanEmbedding ManifoldAffineSphereFamily

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (e : EuclideanEmbedding n M) (r : TubularRetraction e) (f g : ℝ → Sphere 3 → M)
  (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry f))
  (hg : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry g))
  (s z : SourceChart) (c : TargetChart n M)

theorem surjective_fderiv_difference_parameter
    (q : Parameters e × (ℝ × (Vector 3 × Vector 3)))
    (hq : q ∈ domain e r f g hf hg s z c) :
    Surjective (fderiv ℝ (fun p : Parameters e ↦ difference e r f g s z c (p, q.2)) q.1) := by
  let u : Parameters e → M := fun p ↦ ManifoldAffineSphereFamily.map e r f p q.2.1
    (s.symm q.2.2.1)
  have hu := (contMDiffAt_map_parameter e r f q.1 q.2.1
    (s.symm q.2.2.1) hq.1.1.2).mdifferentiableAt (by simp)
  have hcu : IsLocalDiffeomorphAt (𝓡 n) (𝓡 n) ∞ c (u q.1) :=
    ⟨c, hq.1.2, fun _ _ ↦ rfl⟩
  have heq : (fun p : Parameters e ↦ difference e r f g s z c (p, q.2)) =
      fun p ↦ (c ∘ u) p - c (g q.2.1 (z.symm q.2.2.2)) := by
    funext p
    exact difference_apply e r f g s z c (p, q.2)
  rw [heq, fderiv_sub_const, ← mfderiv_eq_fderiv,
    mfderiv_comp q.1 (hcu.mdifferentiableAt (by simp)) hu]
  exact (hcu.mfderivToContinuousLinearEquiv (by simp)).surjective.comp
    (surjective_mfderiv_map_parameter e r f q.1 q.2.1
      (s.symm q.2.2.1) hq.1.1.1.2 hq.1.1.2)

theorem surjective_fderiv_difference
    (q : Parameters e × (ℝ × (Vector 3 × Vector 3)))
    (hq : q ∈ domain e r f g hf hg s z c) :
    Surjective (fderiv ℝ (difference e r f g s z c) q) := by
  have hp := surjective_fderiv_difference_parameter e r f g hf hg s z c q hq
  have hD := ((contDiffOn_difference e r f g hf hg s z c).contDiffAt
    ((domain e r f g hf hg s z c).isOpen.mem_nhds hq)).differentiableAt (by simp)
  have ht : HasFDerivAt (fun p : Parameters e ↦ (p, q.2))
      (ContinuousLinearMap.inl ℝ (Parameters e) (ℝ × (Vector 3 × Vector 3))) q.1 :=
    (hasFDerivAt_id q.1).prodMk (hasFDerivAt_const q.2 q.1)
  have he := (hD.hasFDerivAt.comp q.1 ht).fderiv
  change fderiv ℝ (fun p : Parameters e ↦ difference e r f g s z c (p, q.2)) q.1 = _ at he
  rw [he] at hp
  intro w
  obtain ⟨v, hv⟩ := hp w
  exact ⟨(v, 0), hv⟩

theorem ae_regular_intersections [MeasurableSpace (Parameters e)] [BorelSpace (Parameters e)]
    (μ : Measure (Parameters e)) [IsAddHaarMeasure μ] :
    ∀ᵐ p ∂μ, ∀ x : ℝ × (Vector 3 × Vector 3),
      (p, x) ∈ domain e r f g hf hg s z c → difference e r f g s z c (p, x) = 0 →
      Surjective (fderiv ℝ (fun y ↦ difference e r f g s z c (p, y)) x) :=
  ParametricRegular.ae_parameters_on μ (difference e r f g s z c)
    (domain e r f g hf hg s z c) (contDiffOn_difference e r f g hf hg s z c)
    (fun q hq _ ↦ surjective_fderiv_difference e r f g hf hg s z c q hq)

end NoExoticSixSphere.ManifoldIntersectionFamily
