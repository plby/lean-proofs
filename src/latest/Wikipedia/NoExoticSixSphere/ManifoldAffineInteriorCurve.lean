import Wikipedia.NoExoticSixSphere.ManifoldAffineGenericParameter
import Wikipedia.NoExoticSixSphere.CompactSphereDoublePoints
import Wikipedia.NoExoticSixSphere.PartialHomeomorphSubsets
import Wikipedia.NoExoticSixSphere.RegularLevelNormalForm
import Wikipedia.NoExoticSixSphere.RegularLevelChart
import Wikipedia.NoExoticSixSphere.InvolutionFreeChart
import Wikipedia.NoExoticSixSphere.EuclideanTailSplitting

/-!
# Interior charts on the actual unordered manifold double-point space

Two genuine source charts are allowed at distinct sphere points. The regular
coordinate difference has a one-dimensional zero chart. Its source stays in
the actual pair domain, so the chart transfers to the original double-point
closure and then descends through the free swap quotient.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.ManifoldAffineSphereFamily

open GLOrthonormalization EuclideanEmbedding FamilyEmbedding InvolutionQuotient

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (e : EuclideanEmbedding n M) (r : TubularRetraction e) (f : ℝ → Sphere 3 → M)
  (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry f))
  (p : Parameters e)
  (hg : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 n) ∞ (uncurry (map e r f p)))
  (S : Set SourceChart) (C : Set (TargetChart n M))
  (hS : ∀ x : Sphere 3, ∃ s ∈ S, x ∈ s.source)
  (hC : ∀ x : M, ∃ c ∈ C, x ∈ c.source)
  (hp : ∀ t x, ambient e f p t x ∈ r.domain)
  (hgen : GenericInCharts e r f hf S C p)
  (hinj : ∀ t, t ≤ 0 ∨ 1 ≤ t → Injective (f t))

include hg hS hC hp hgen

theorem exists_ordered_interior_chart_at_time (hn : n = 6)
    (a : closure (doublePoints (map e r f p))) (hne : a.val.2.1 ≠ a.val.2.2)
    (hta : a.val.1 ∈ Ioo (0 : ℝ) 1) :
    ∃ d : OpenPartialHomeomorph (closure (doublePoints (map e r f p))) ℝ,
      a ∈ d.source := by
  let : T2Space M := e.closedEmbedding.isEmbedding.t2Space
  have heq := closure_doublePoints_equal_image_of_continuous (map e r f p) hg.continuous
    a.property
  obtain ⟨s, hs, hxs⟩ := hS a.val.2.1
  obtain ⟨z, hz, hyz⟩ := hS a.val.2.2
  obtain ⟨c, hc, hxc⟩ := hC (map e r f p a.val.1 a.val.2.1)
  have hyc : map e r f p a.val.1 a.val.2.2 ∈ c.source := heq ▸ hxc
  let T₀ := (OpenPartialHomeomorph.refl ℝ).prod
    (s.toOpenPartialHomeomorph.prod z.toOpenPartialHomeomorph)
  let U : Set (ℝ × (Vector 3 × Vector 3)) := {q | (p, q) ∈ pairDomain e r f hf s z c}
  let D : ℝ × (Vector 3 × Vector 3) → Vector n := fun q ↦ chartDifference e r f s z c (p, q)
  have hU : IsOpen U :=
    (pairDomain e r f hf s z c).isOpen.preimage (continuous_const.prodMk continuous_id)
  have hD : ContDiffOn ℝ ∞ D U := (contDiffOn_chartDifference e r f hf s z c).comp
    (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ hq ↦ hq)
  have haT : a.val ∈ T₀.source := ⟨mem_univ _, hxs, hyz⟩
  have hxleft : s.symm (s a.val.2.1) = a.val.2.1 := s.left_inv hxs
  have hyleft : z.symm (z a.val.2.2) = a.val.2.2 := z.left_inv hyz
  have haU : T₀ a.val ∈ U := by
    change ((((s a.val.2.1 ∈ s.target ∧ a.val.1 ∈ Ioo (0 : ℝ) 1) ∧
      ambient e f p a.val.1 (s.symm (s a.val.2.1)) ∈ r.domain) ∧
      map e r f p a.val.1 (s.symm (s a.val.2.1)) ∈ c.source) ∧
      (((z a.val.2.2 ∈ z.target ∧ a.val.1 ∈ Ioo (0 : ℝ) 1) ∧
      ambient e f p a.val.1 (z.symm (z a.val.2.2)) ∈ r.domain) ∧
      map e r f p a.val.1 (z.symm (z a.val.2.2)) ∈ c.source)) ∧
      s.symm (s a.val.2.1) ≠ z.symm (z a.val.2.2)
    rw [hxleft, hyleft]
    exact ⟨⟨⟨⟨⟨s.map_source hxs, hta⟩, hp _ _⟩, hxc⟩,
      ⟨⟨⟨z.map_source hyz, hta⟩, hp _ _⟩, hyc⟩⟩, hne⟩
  have hcompare (b : ℝ × (Sphere 3 × Sphere 3)) (hbT : b ∈ T₀.source)
      (hbU : T₀ b ∈ U) : D (T₀ b) = 0 ↔ map e r f p b.1 b.2.1 = map e r f p b.1 b.2.2 := by
    have h := chartDifference_zero_iff e r f hf s z c (p, T₀ b) hbU
    change D (T₀ b) = 0 ↔ map e r f p b.1 (s.symm (s b.2.1)) =
      map e r f p b.1 (z.symm (z b.2.2)) at h
    have hx : s.symm (s b.2.1) = b.2.1 := s.left_inv hbT.2.1
    have hy : z.symm (z b.2.2) = b.2.2 := z.left_inv hbT.2.2
    rwa [hx, hy] at h
  have haD : D (T₀ a.val) = 0 := (hcompare a.val haT haU).mpr heq
  have hsurj : Surjective (fderiv ℝ D (T₀ a.val)) :=
    hgen.2 s hs z hz c hc (T₀ a.val) haU haD
  obtain ⟨Φ, hΦa, hΦU, hΦfirst, _⟩ := exists_euclideanLevelNormalForm hU haU hD hsurj 1
    (by simp [GLOrthonormalization.Vector, hn])
  let T := T₀.trans (OpenPartialHomeomorph.ofSet Φ.source Φ.open_source)
  have haT' : a.val ∈ T.source := ⟨haT, hΦa⟩
  have hImage : T.IsImage (closure (doublePoints (map e r f p))) {q | D q = 0} := by
    intro b hb
    have hbU : T₀ b ∈ U := hΦU hb.2
    have hx : s.symm (s b.2.1) = b.2.1 := s.left_inv hb.1.2.1
    have hy : z.symm (z b.2.2) = b.2.2 := z.left_inv hb.1.2.2
    have hbne : b.2.1 ≠ b.2.2 := by
      have h : s.symm (s b.2.1) ≠ z.symm (z b.2.2) := hbU.2
      rwa [hx, hy] at h
    change D (T₀ b) = 0 ↔ b ∈ closure (doublePoints (map e r f p))
    constructor
    · intro hd
      exact subset_closure ⟨hbne, (hcompare b hb.1 hbU).mp hd⟩
    · intro hcl
      exact (hcompare b hb.1 hbU).mpr
        (closure_doublePoints_equal_image_of_continuous (map e r f p) hg.continuous hcl)
  let a₀ : {q | D q = 0} := ⟨T₀ a.val, haD⟩
  let E := SubsetCoordinates.coordinates T hImage a a₀
  let k := RegularLevelChart.chart Φ.toOpenPartialHomeomorph (fun x _ ↦ hΦfirst x) a₀
  let d := E.trans
    (k.trans EuclideanTailCoordinates.scalar.symm.toHomeomorph.toOpenPartialHomeomorph)
  refine ⟨d, haT', ?_, mem_univ _⟩
  change (E a).val ∈ Φ.source
  rw [SubsetCoordinates.coordinates_val T hImage a a₀ haT']
  exact hΦa

include hinj in
theorem exists_ordered_interior_chart (hn : n = 6)
    (a : closure (doublePoints (map e r f p))) (hne : a.val.2.1 ≠ a.val.2.2) :
    ∃ d : OpenPartialHomeomorph (closure (doublePoints (map e r f p))) ℝ,
      a ∈ d.source := by
  let : T2Space M := e.closedEmbedding.isEmbedding.t2Space
  have heq := closure_doublePoints_equal_image_of_continuous (map e r f p) hg.continuous
    a.property
  have hta := doublePoints_time_mem_Ioo (map e r f p)
    (fun t ht ↦ injective_map_outside e r f p hinj ht) ⟨hne, heq⟩
  exact exists_ordered_interior_chart_at_time e r f hf p hg S C hS hC hp hgen hn a hne hta

theorem exists_unordered_interior_chart_at_time (hn : n = 6)
    (a : closure (doublePoints (map e r f p))) (hne : a.val.2.1 ≠ a.val.2.2)
    (hta : a.val.1 ∈ Ioo (0 : ℝ) 1) :
    ∃ d : OpenPartialHomeomorph (UnorderedClosedDoublePoints (map e r f p)) ℝ,
      unorderedProj (map e r f p) a ∈ d.source ∧
      Disjoint d.source (diagonalOrbits (map e r f p)) := by
  obtain ⟨c, hca⟩ :=
    exists_ordered_interior_chart_at_time e r f hf p hg S C hS hC hp hgen hn a hne hta
  have hfree : swapClosure (map e r f p) a ≠ a :=
    fun he ↦ hne ((swapClosure_fixed_iff (map e r f p) a).mp he)
  obtain ⟨d, hda, _, hdis⟩ := exists_free_chart (swapClosure (map e r f p))
    (swapClosure_involutive (map e r f p)) (swapClosure (map e r f p)).continuous a hfree c hca
  refine ⟨d, hda, ?_⟩
  rw [diagonalOrbits_eq_fixed]
  exact hdis

include hinj in
theorem exists_unordered_interior_chart (hn : n = 6)
    (a : closure (doublePoints (map e r f p))) (hne : a.val.2.1 ≠ a.val.2.2) :
    ∃ d : OpenPartialHomeomorph (UnorderedClosedDoublePoints (map e r f p)) ℝ,
      unorderedProj (map e r f p) a ∈ d.source ∧
      Disjoint d.source (diagonalOrbits (map e r f p)) := by
  let : T2Space M := e.closedEmbedding.isEmbedding.t2Space
  have heq := closure_doublePoints_equal_image_of_continuous (map e r f p) hg.continuous
    a.property
  have hta := doublePoints_time_mem_Ioo (map e r f p)
    (fun t ht ↦ injective_map_outside e r f p hinj ht) ⟨hne, heq⟩
  exact exists_unordered_interior_chart_at_time e r f hf p hg S C hS hC hp hgen hn a hne hta

end NoExoticSixSphere.ManifoldAffineSphereFamily
