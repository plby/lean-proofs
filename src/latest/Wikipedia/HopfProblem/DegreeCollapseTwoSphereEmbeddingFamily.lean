import Wikipedia.HopfProblem.DegreeCollapseTwoSphereGenericParameter

/-!
# Actual embedded two-sphere families in the original target atlas

The finite chart covers turn the constructed collision and kernel
avoidance into global injectivity and native immersion of every interior
slice. The same single parameter supplies the jointly smooth family.
All exterior-time slices are exactly the original slices, so original
embedding and immersion hypotheses there are retained pointwise.
-/

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.TwoSpherePerturbation

open NoExoticSixSphere GLOrthonormalization EuclideanEmbedding

variable {n : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (e : EuclideanEmbedding n M) (r : TubularRetraction e) (f : ℝ → Sphere 2 → M)

theorem injective_slice_of_embedding_charts
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 n) ∞ (uncurry f))
    {S : Set SourceChart} {C : Set (TargetChart n M)}
    (hS : ∀ x : Sphere 2, ∃ s ∈ S, x ∈ s.source)
    (hC : ∀ x : M, ∃ c ∈ C, x ∈ c.source)
    (p : Parameters e) (hgen : EmbeddingInCharts e r f hf S C p)
    (hmem : ∀ t s, ambient e f p t s ∈ r.domain)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : Injective (map e r f p t) := by
  intro x y hxy
  by_contra hne
  obtain ⟨s, hs, hsx⟩ := hS x
  obtain ⟨z, hz, hzy⟩ := hS y
  obtain ⟨c, hc, hcx⟩ := hC (map e r f p t x)
  have hsInv : s.symm (s x) = x := s.left_inv' hsx
  have hzInv : z.symm (z y) = y := z.left_inv' hzy
  have hleft : (p, t, s x) ∈ chartDomain e r f hf s c :=
    ⟨⟨⟨s.map_source' hsx, ht⟩, hmem t _⟩, by
      change map e r f p t (s.symm (s x)) ∈ c.source
      rwa [hsInv]⟩
  have hright : (p, t, z y) ∈ chartDomain e r f hf z c :=
    ⟨⟨⟨z.map_source' hzy, ht⟩, hmem t _⟩, by
      change map e r f p t (z.symm (z y)) ∈ c.source
      rwa [hzInv, ← hxy]⟩
  have hdistinct : s.symm (s x) ≠ z.symm (z y) := by
    simpa only [hsInv, hzInv] using hne
  have hpair : (p, t, s x, z y) ∈ pairDomain e r f hf s z c :=
    ⟨⟨hleft, hright⟩, hdistinct⟩
  apply hgen.2 s hs z hz c hc (t, s x, z y) hpair
  apply (chartDifference_zero_iff e r f hf s z c (p, t, s x, z y) hpair).mpr
  simpa only [hsInv, hzInv] using hxy

theorem immersive_slice_of_embedding_charts
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 n) ∞ (uncurry f))
    {S : Set SourceChart} {C : Set (TargetChart n M)}
    (hS : ∀ x : Sphere 2, ∃ s ∈ S, x ∈ s.source)
    (hC : ∀ x : M, ∃ c ∈ C, x ∈ c.source)
    (p : Parameters e) (hgen : EmbeddingInCharts e r f hf S C p)
    (hmem : ∀ t s, ambient e f p t s ∈ r.domain)
    (hg : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 n) ∞ (uncurry (map e r f p)))
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (x : Sphere 2) :
    Injective (mfderiv (𝓡 2) (𝓡 n) (map e r f p t) x) := by
  let g := map e r f p t
  have hgs : ContMDiff (𝓡 2) (𝓡 n) ∞ g :=
    hg.comp (contMDiff_const.prodMk contMDiff_id)
  obtain ⟨s, hs, hsx⟩ := hS x
  obtain ⟨c, hc, hcx⟩ := hC (g x)
  have hsInv : s.symm (s x) = x := s.left_inv' hsx
  have hdom : (p, t, s x) ∈ chartDomain e r f hf s c :=
    ⟨⟨⟨s.map_source' hsx, ht⟩, hmem t _⟩, by
      change g (s.symm (s x)) ∈ c.source
      rwa [hsInv]⟩
  have hjet := hgen.1 s hs c hc (t, s x) hdom
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

include e r in
theorem exists_smooth_embedding_family [IsManifold (𝓡 n) ∞ M] [CompactSpace M]
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 n) ∞ (uncurry f)) (hdim : 5 < n)
    (hi : ∀ t, t ≤ 0 ∨ 1 ≤ t → Injective (f t))
    (hd : ∀ t, t ≤ 0 ∨ 1 ≤ t → ∀ x, Injective (mfderiv (𝓡 2) (𝓡 n) (f t) x)) :
    ∃ g : ℝ → Sphere 2 → M,
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 n) ∞ (uncurry g) ∧
      (∀ t, Injective (g t)) ∧
      (∀ t x, Injective (mfderiv (𝓡 2) (𝓡 n) (g t) x)) ∧
      ∀ t, t ≤ 0 ∨ 1 ≤ t → ∀ x, g t x = f t x := by
  obtain ⟨S, C, p, _, hS, _, hC, _, hgen, hmem, hg, hfix⟩ :=
    exists_small_manifold_family_with_embedding_charts e r f hf hdim (by norm_num : (0 : ℝ) < 1)
  refine ⟨map e r f p, hg, ?_, ?_, hfix⟩
  · intro t
    by_cases ht : t ∈ Ioo (0 : ℝ) 1
    · exact injective_slice_of_embedding_charts e r f hf hS hC p hgen hmem t ht
    · have ho : t ≤ 0 ∨ 1 ≤ t := by simp only [mem_Ioo, not_and_or, not_lt] at ht; exact ht
      rw [funext (hfix t ho)]
      exact hi t ho
  · intro t x
    by_cases ht : t ∈ Ioo (0 : ℝ) 1
    · exact immersive_slice_of_embedding_charts e r f hf hS hC p hgen hmem hg t ht x
    · have ho : t ≤ 0 ∨ 1 ≤ t := by simp only [mem_Ioo, not_and_or, not_lt] at ht; exact ht
      rw [funext (hfix t ho)]
      exact hd t ho x

end Wikipedia.HopfProblem.DegreeCollapse.TwoSpherePerturbation
