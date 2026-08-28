import Wikipedia.HopfProblem.DegreeCollapseTripleChartGenericity
import Wikipedia.HopfProblem.DegreeCollapseDoublePointCounting
import Wikipedia.NoExoticSixSphere.ManifoldAffineGenericParameter

/-!
# One actual manifold family with no interior triple fibers

The common parameter simultaneously satisfies the existing jet and pair
genericity conditions and the new triple exclusion. Compactness supplies
genuine finite chart covers and one uniform tubular parameter ball. Every
interior slice has only simple double fibers; both endpoint maps are fixed.
-/

noncomputable section

open Set Function
open MeasureTheory MeasureTheory.Measure
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.TripleParameters

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization
open EuclideanEmbedding ManifoldAffineSphereFamily DoublePointCounting

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M) (r : TubularRetraction e) (f : ℝ → Sphere 3 → M)

theorem mem_pairDomain_at_points
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry f))
    (p : Parameters e) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1)
    (x y : Sphere 3) (hne : x ≠ y) (a b : SourceChart) (d : TargetChart 6 M)
    (hxa : x ∈ a.source) (hyb : y ∈ b.source)
    (hx : ambient e f p t x ∈ r.domain) (hy : ambient e f p t y ∈ r.domain)
    (hxd : map e r f p t x ∈ d.source) (hyd : map e r f p t y ∈ d.source) :
    (p, (t, (a x, b y))) ∈ pairDomain e r f hf a b d := by
  have hx' : a.symm (a x) = x := a.left_inv hxa
  have hy' : b.symm (b y) = y := b.left_inv hyb
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · change ((a x ∈ a.target ∧ t ∈ Ioo (0 : ℝ) 1) ∧
      ambient e f p t (a.symm (a x)) ∈ r.domain) ∧ map e r f p t (a.symm (a x)) ∈ d.source
    rw [hx']
    exact ⟨⟨⟨a.map_source hxa, ht⟩, hx⟩, hxd⟩
  · change ((b y ∈ b.target ∧ t ∈ Ioo (0 : ℝ) 1) ∧
      ambient e f p t (b.symm (b y)) ∈ r.domain) ∧ map e r f p t (b.symm (b y)) ∈ d.source
    rw [hy']
    exact ⟨⟨⟨b.map_source hyb, ht⟩, hy⟩, hyd⟩
  · change a.symm (a x) ≠ b.symm (b y)
    rwa [hx', hy']

theorem onlyDoubleFibers_of_tripleFreeInCharts
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry f))
    (S : Set SourceChart) (C : Set (TargetChart 6 M))
    (hS : ∀ x : Sphere 3, ∃ a ∈ S, x ∈ a.source)
    (hC : ∀ x : M, ∃ d ∈ C, x ∈ d.source)
    (p : Parameters e) (hfree : TripleFreeInCharts e r f hf S C p)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hmem : ∀ x, ambient e f p t x ∈ r.domain) :
    HasOnlyDoubleFibers (map e r f p t) := by
  intro x y hxy heq z hzx
  by_cases hz₁ : z = x
  · exact Or.inl hz₁
  by_cases hz₂ : z = y
  · exact Or.inr hz₂
  obtain ⟨a, ha, hxa⟩ := hS x
  obtain ⟨b, hb, hyb⟩ := hS y
  obtain ⟨c, hc, hzc⟩ := hS z
  obtain ⟨d, hd, hxd⟩ := hC (map e r f p t x)
  have hyd : map e r f p t y ∈ d.source := heq ▸ hxd
  have hzd : map e r f p t z ∈ d.source := hzx.symm ▸ hxd
  have hq : (p, (t, (a x, b y, c z))) ∈ tripleDomain e r f hf a b c d :=
    ⟨mem_pairDomain_at_points e r f hf p t ht x y hxy a b d hxa hyb
        (hmem x) (hmem y) hxd hyd,
      mem_pairDomain_at_points e r f hf p t ht x z (Ne.symm hz₁) a c d hxa hzc
        (hmem x) (hmem z) hxd hzd,
      mem_pairDomain_at_points e r f hf p t ht y z (Ne.symm hz₂) b c d hyb hzc
        (hmem y) (hmem z) hyd hzd⟩
  have hz : tripleChartDifference e r f a b c d (p, (t, (a x, b y, c z))) = 0 := by
    apply (tripleChartDifference_zero_iff e r f hf a b c d _ hq).mpr
    have hx' : a.symm (a x) = x := a.left_inv hxa
    have hy' : b.symm (b y) = y := b.left_inv hyb
    have hz' : c.symm (c z) = z := c.left_inv hzc
    change map e r f p t (a.symm (a x)) = map e r f p t (b.symm (b y)) ∧
      map e r f p t (a.symm (a x)) = map e r f p t (c.symm (c z))
    rw [hx', hy', hz']
    exact ⟨heq, hzx.symm⟩
  exact (hfree a ha b hb c hc d hd _ hq hz).elim

theorem exists_small_tripleFree_generic_in_charts
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry f))
    (S : Set SourceChart) (hS : S.Countable) (C : Set (TargetChart 6 M)) (hC : C.Countable)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p : Parameters e, ‖p‖ < ε ∧ GenericInCharts e r f hf S C p ∧
      TripleFreeInCharts e r f hf S C p := by
  let : MeasurableSpace (Parameters e) := borel (Parameters e)
  let : BorelSpace (Parameters e) := ⟨rfl⟩
  have hgen := ae_generic_in_charts e r f addHaar hf rfl S hS C hC
  have hfree := ae_tripleFree_in_charts e r f addHaar hf S hS C hC
  have hdense := Measure.dense_of_ae (hgen.and hfree)
  obtain ⟨p, hp, hsmall⟩ := hdense.exists_dist_lt 0 hε
  exact ⟨p, by simpa only [dist_zero_left] using hsmall, hp⟩

theorem exists_small_tripleFree_generic_manifold_family [IsManifold (𝓡 6) ∞ M] [CompactSpace M]
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry f))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Set SourceChart, ∃ C : Set (TargetChart 6 M), ∃ p : Parameters e,
      S.Finite ∧ (∀ x : Sphere 3, ∃ a ∈ S, x ∈ a.source) ∧
      C.Finite ∧ (∀ x : M, ∃ d ∈ C, x ∈ d.source) ∧ ‖p‖ < ε ∧
      GenericInCharts e r f hf S C p ∧
      (∀ t ∈ Ioo (0 : ℝ) 1, HasOnlyDoubleFibers (map e r f p t)) ∧
      (∀ t x, ambient e f p t x ∈ r.domain) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry (map e r f p)) ∧
      ∀ t, t ≤ 0 ∨ 1 ≤ t → ∀ x, map e r f p t x = f t x := by
  obtain ⟨S, hS, hScov⟩ := exists_finite_chart_cover 3 (Sphere 3)
  obtain ⟨C, hC, hCcov⟩ := exists_finite_chart_cover 6 M
  obtain ⟨δ, hδ, hmem, hsmooth⟩ := exists_smooth_parameter_ball e r f hf
  obtain ⟨p, hp, hgen, hfree⟩ := exists_small_tripleFree_generic_in_charts e r f hf
    S hS.countable C hC.countable (lt_min hε hδ)
  have hpε : ‖p‖ < ε := hp.trans_le (min_le_left _ _)
  have hpδ : ‖p‖ < δ := hp.trans_le (min_le_right _ _)
  refine ⟨S, C, p, hS, hScov, hC, hCcov, hpε, hgen, ?_, hmem p hpδ, ?_, ?_⟩
  · exact fun t ht ↦ onlyDoubleFibers_of_tripleFreeInCharts e r f hf S C hScov hCcov
      p hfree t ht (hmem p hpδ t)
  · exact hsmooth.comp_contMDiff (contMDiff_const.prodMk contMDiff_id) (fun _ ↦ hpδ)
  · exact fun _ ht x ↦ map_eq_outside e r f p ht x

end Wikipedia.HopfProblem.DegreeCollapse.TripleParameters
