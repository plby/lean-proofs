import Wikipedia.HopfProblem.DegreeCollapseRelativeTwoSphereGenericParameter
import Wikipedia.HopfProblem.DegreeCollapseRelativeTwoSphereProtectedDerivative

/-!
# Global embedding of a relative two-sphere slice

Active pairs are excluded by the actual chart tests, including mixed
protected/unprotected pairs. Pairs wholly in the protected set retain the
original injectivity. Native immersion follows from the active jets and
the exact derivative preservation on the cutoff zero set.
-/

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.RelativeTwoSphere

open NoExoticSixSphere GLOrthonormalization EuclideanEmbedding
open TwoSpherePerturbation (Parameters SourceChart TargetChart)

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (e : EuclideanEmbedding n M) (r : TubularRetraction e)
  (f : ℝ → Sphere 2 → M) (χ : Sphere 2 → ℝ)

theorem injective_slice_of_embedding_charts
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 n) ∞ (uncurry f))
    (hχ : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ χ)
    {S : Set SourceChart} {C : Set (TargetChart n M)}
    (hS : ∀ x : Sphere 2, ∃ s ∈ S, x ∈ s.source)
    (hC : ∀ x : M, ∃ c ∈ C, x ∈ c.source)
    (p : Parameters e) (hgen : EmbeddingInCharts e r f χ hf hχ S C p)
    (hmem : ∀ t x, ambient e f χ p t x ∈ r.domain)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hfixed : InjOn (f t) {x | χ x = 0}) : Injective (map e r f χ p t) := by
  intro x y hxy
  by_cases hactive : χ x ≠ 0 ∨ χ y ≠ 0
  · by_contra hne
    obtain ⟨s, hs, hsx⟩ := hS x
    obtain ⟨z, hz, hzy⟩ := hS y
    obtain ⟨c, hc, hcx⟩ := hC (map e r f χ p t x)
    have hsInv : s.symm (s x) = x := s.left_inv' hsx
    have hzInv : z.symm (z y) = y := z.left_inv' hzy
    have hleft : (p, t, s x) ∈ chartDomain e r f χ hf hχ s c :=
      ⟨⟨⟨s.map_source' hsx, ht⟩, hmem t _⟩, by
        change map e r f χ p t (s.symm (s x)) ∈ c.source
        rwa [hsInv]⟩
    have hright : (p, t, z y) ∈ chartDomain e r f χ hf hχ z c :=
      ⟨⟨⟨z.map_source' hzy, ht⟩, hmem t _⟩, by
        change map e r f χ p t (z.symm (z y)) ∈ c.source
        rwa [hzInv, ← hxy]⟩
    have hdistinct : s.symm (s x) ≠ z.symm (z y) := by
      simpa only [hsInv, hzInv] using hne
    have hpair : (p, t, s x, z y) ∈ pairDomain e r f χ hf hχ s z c :=
      ⟨⟨hleft, hright⟩, hdistinct⟩
    have hactivePair : (p, t, s x, z y) ∈ activePairDomain e r f χ hf hχ s z c :=
      ⟨hpair, by
        change χ (s.symm (s x)) ≠ 0 ∨ χ (z.symm (z y)) ≠ 0
        simpa only [hsInv, hzInv] using hactive⟩
    apply hgen.2 s hs z hz c hc (t, s x, z y) hactivePair
    apply (chartDifference_zero_iff e r f χ hf hχ s z c (p, t, s x, z y) hpair).mpr
    simpa only [hsInv, hzInv] using hxy
  · have hx : χ x = 0 := by by_contra h; exact hactive (Or.inl h)
    have hy : χ y = 0 := by by_contra h; exact hactive (Or.inr h)
    exact hfixed hx hy ((map_eq_zero_cutoff e r f χ p t x hx).symm.trans
      (hxy.trans (map_eq_zero_cutoff e r f χ p t y hy)))

theorem immersive_slice_of_embedding_charts [IsManifold (𝓡 n) ∞ M]
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 n) ∞ (uncurry f))
    (hχ : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ χ) (hnonneg : ∀ x, 0 ≤ χ x)
    {S : Set SourceChart} {C : Set (TargetChart n M)}
    (hS : ∀ x : Sphere 2, ∃ s ∈ S, x ∈ s.source)
    (hC : ∀ x : M, ∃ c ∈ C, x ∈ c.source)
    (p : Parameters e) (hgen : EmbeddingInCharts e r f χ hf hχ S C p)
    (hmem : ∀ t x, ambient e f χ p t x ∈ r.domain)
    (hg : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 n) ∞ (uncurry (map e r f χ p)))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hfixed : ∀ x, χ x = 0 → Injective (mfderiv (𝓡 2) (𝓡 n) (f t) x)) (x : Sphere 2) :
    Injective (mfderiv (𝓡 2) (𝓡 n) (map e r f χ p t) x) := by
  by_cases hxχ : χ x = 0
  · rw [mfderiv_map_of_zero_cutoff e r f χ hf hχ hnonneg p t x hxχ]
    exact hfixed x hxχ
  let g := map e r f χ p t
  have hgs : ContMDiff (𝓡 2) (𝓡 n) ∞ g := hg.comp (contMDiff_const.prodMk contMDiff_id)
  obtain ⟨s, hs, hsx⟩ := hS x
  obtain ⟨c, hc, hcx⟩ := hC (g x)
  have hsInv : s.symm (s x) = x := s.left_inv' hsx
  have hdom : (p, t, s x) ∈ chartDomain e r f χ hf hχ s c :=
    ⟨⟨⟨s.map_source' hsx, ht⟩, hmem t _⟩, by
      change g (s.symm (s x)) ∈ c.source
      rwa [hsInv]⟩
  have hactive : (p, t, s x) ∈ activeChartDomain e r f χ hf hχ s c :=
    ⟨hdom, by simpa only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff,
      hsInv] using hxχ⟩
  have hjet := hgen.1 s hs c hc (t, s x) hactive
  have hsd := s.symm.mdifferentiableAt (by simp) (s.map_source' hsx)
  have hgd := hgs.mdifferentiableAt (x := s.symm (s x)) (by simp)
  have hcd := c.mdifferentiableAt (by simp)
    (show g (s.symm (s x)) ∈ c.source by rwa [hsInv])
  change Injective (fderiv ℝ (c ∘ (g ∘ s.symm)) (s x)) at hjet
  rw [← mfderiv_eq_fderiv, mfderiv_comp (s x) hcd (hgd.comp (s x) hsd),
    mfderiv_comp (s x) hgd hsd] at hjet
  change Injective (fun v : Vector 2 => mfderiv (𝓡 n) (𝓡 n) c (g (s.symm (s x)))
    (mfderiv (𝓡 2) (𝓡 n) g (s.symm (s x))
      (mfderiv (𝓡 2) (𝓡 2) s.symm (s x) v))) at hjet
  rw [hsInv] at hjet
  have hsLocal : IsLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ s.symm (s x) :=
    ⟨s.symm, s.map_source' hsx, fun _ _ => rfl⟩
  have hsurj := (hsLocal.mfderivToContinuousLinearEquiv (by simp)).surjective
  change Surjective (mfderiv (𝓡 2) (𝓡 2) s.symm (s x)) at hsurj
  intro v w hvw
  obtain ⟨u, hu⟩ := hsurj v
  obtain ⟨z, hz⟩ := hsurj w
  have he : u = z := hjet (by
    change mfderiv (𝓡 n) (𝓡 n) c (g x)
        (mfderiv (𝓡 2) (𝓡 n) g x (mfderiv (𝓡 2) (𝓡 2) s.symm (s x) u)) =
      mfderiv (𝓡 n) (𝓡 n) c (g x)
        (mfderiv (𝓡 2) (𝓡 n) g x (mfderiv (𝓡 2) (𝓡 2) s.symm (s x) z))
    rw [hu, hz, hvw])
  exact hu.symm.trans ((congrArg (mfderiv (𝓡 2) (𝓡 2) s.symm (s x)) he).trans hz)

end Wikipedia.HopfProblem.DegreeCollapse.RelativeTwoSphere
