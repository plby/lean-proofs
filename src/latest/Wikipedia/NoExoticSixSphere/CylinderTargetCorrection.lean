import Wikipedia.NoExoticSixSphere.CylinderSliceRegularity

/-!
# Correcting a regular target value while preserving constant ends

Apply a smooth time-dependent family of actual target diffeomorphisms. On
the open middle interval the family is constant, so regularity comes from
the cylinder's supplied regular value. On the closed ends, regularity comes
from the spatial endpoint maps at the moving value. No Sard or genericity
assertion is included in these lemmas.
-/

open scoped Manifold ContDiff Topology
open Set

namespace NoExoticSixSphere

variable {B H M C H' N : Type*}
  [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H]
  {I : ModelWithCorners ℝ B H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup C] [NormedSpace ℝ C] [TopologicalSpace H']
  {J : ModelWithCorners ℝ C H'}
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

omit [IsManifold J ∞ N] in
theorem contMDiff_cylinderTargetCorrection (e : ℝ → N ≃ₘ⟮J, J⟯ N)
    (he : ContMDiff ((𝓘(ℝ, ℝ)).prod J) J ∞ (fun p : ℝ × N ↦ e p.1 p.2))
    {F : ℝ × M → N} (hF : ContMDiff ((𝓘(ℝ, ℝ)).prod I) J ∞ F) :
    ContMDiff ((𝓘(ℝ, ℝ)).prod I) J ∞ (fun p : ℝ × M ↦ e p.1 (F p)) :=
  he.comp (contMDiff_fst.prodMk hF)

omit [IsManifold J ∞ N] in
theorem regular_cylinderTargetCorrection
    (e : ℝ → N ≃ₘ⟮J, J⟯ N)
    (he : ContMDiff ((𝓘(ℝ, ℝ)).prod J) J ∞ (fun p : ℝ × N ↦ e p.1 p.2))
    {F : ℝ × M → N} (hF : ContMDiff ((𝓘(ℝ, ℝ)).prod I) J ∞ F)
    {f₀ f₁ : M → N} (h₀ : ContMDiff I J ∞ f₀) (h₁ : ContMDiff I J ∞ f₁)
    (l r : ℝ) (hleft : ∀ t ≤ l, ∀ x, F (t, x) = f₀ x)
    (hright : ∀ t, r ≤ t → ∀ x, F (t, x) = f₁ x)
    (a : ℝ → N) (b c : N) (hroot : ∀ t, e t (a t) = b)
    (hreg₀ : ∀ t x, f₀ x = a t → Function.Surjective (mfderiv I J f₀ x))
    (hreg₁ : ∀ t x, f₁ x = a t → Function.Surjective (mfderiv I J f₁ x))
    (e₀ : N ≃ₘ⟮J, J⟯ N) (hmiddle : ∀ t ∈ Ioo l r, e t = e₀) (hc : e₀ c = b)
    (hreg : ∀ p, F p = c → Function.Surjective (mfderiv ((𝓘(ℝ, ℝ)).prod I) J F p)) :
    ∀ p, e p.1 (F p) = b → Function.Surjective
      (mfderiv ((𝓘(ℝ, ℝ)).prod I) J (fun q : ℝ × M ↦ e q.1 (F q)) p) := by
  let G := fun q : ℝ × M ↦ e q.1 (F q)
  have hG : ContMDiff ((𝓘(ℝ, ℝ)).prod I) J ∞ G :=
    contMDiff_cylinderTargetCorrection e he hF
  rintro ⟨t, x⟩ hx
  have hFx : F (t, x) = a t := (e t).injective (hx.trans (hroot t).symm)
  by_cases ht : t ≤ l
  · have hfx : f₀ x = a t := (hleft t ht x).symm.trans hFx
    have hs : Function.Surjective (mfderiv I J (e t ∘ f₀) x) := by
      rw [mfderiv_comp x ((e t).contMDiff.mdifferentiable (by simp) (f₀ x))
        (h₀.mdifferentiable (by simp) x)]
      exact ((e t).mfderivToContinuousLinearEquiv (by simp) (f₀ x)).surjective.comp
        (hreg₀ t x hfx)
    exact mfderiv_cylinder_surjective_of_slice G (e t ∘ f₀) hG t
      (fun y ↦ congrArg (e t) (hleft t ht y)) x hs
  by_cases ht' : r ≤ t
  · have hfx : f₁ x = a t := (hright t ht' x).symm.trans hFx
    have hs : Function.Surjective (mfderiv I J (e t ∘ f₁) x) := by
      rw [mfderiv_comp x ((e t).contMDiff.mdifferentiable (by simp) (f₁ x))
        (h₁.mdifferentiable (by simp) x)]
      exact ((e t).mfderivToContinuousLinearEquiv (by simp) (f₁ x)).surjective.comp
        (hreg₁ t x hfx)
    exact mfderiv_cylinder_surjective_of_slice G (e t ∘ f₁) hG t
      (fun y ↦ congrArg (e t) (hright t ht' y)) x hs
  have htm : t ∈ Ioo l r := ⟨lt_of_not_ge ht, lt_of_not_ge ht'⟩
  have heq : G =ᶠ[𝓝 (t, x)] (e₀ ∘ F) := by
    filter_upwards [(isOpen_Ioo.preimage continuous_fst).mem_nhds htm] with q hq
    change e q.1 (F q) = e₀ (F q)
    rw [hmiddle q.1 hq]
  have hFc : F (t, x) = c := by
    apply e₀.injective
    have hx' : e₀ (F (t, x)) = b := by simpa only [hmiddle t htm] using hx
    exact hx'.trans hc.symm
  change Function.Surjective (mfderiv ((𝓘(ℝ, ℝ)).prod I) J G (t, x))
  rw [heq.mfderiv_eq, mfderiv_comp (t, x)
    (e₀.contMDiff.mdifferentiable (by simp) (F (t, x))) (hF.mdifferentiable (by simp) (t, x))]
  exact (e₀.mfderivToContinuousLinearEquiv (by simp) (F (t, x))).surjective.comp
    (hreg (t, x) hFc)

end NoExoticSixSphere
