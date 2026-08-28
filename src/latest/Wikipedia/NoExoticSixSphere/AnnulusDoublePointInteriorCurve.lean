import Wikipedia.NoExoticSixSphere.AnnulusDoublePointTopology
import Wikipedia.NoExoticSixSphere.CompactRetractionGenericDoublePoints
import Wikipedia.NoExoticSixSphere.PartialHomeomorphSubsets
import Wikipedia.NoExoticSixSphere.RegularLevelNormalForm
import Wikipedia.NoExoticSixSphere.RegularLevelChart
import Wikipedia.NoExoticSixSphere.InvolutionFreeChart
import Wikipedia.NoExoticSixSphere.EuclideanTailSplitting

/-!
# Real curve charts off the diagonal of the actual annulus double points

The original target-chart difference has a one-dimensional regular zero
fiber. Inverse-function coordinates identify it locally with the actual
annulus double-point closure at every distinct pair. Passing through the
free swap quotient gives a real chart disjoint from the diagonal orbits.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.AnnulusDoublePoints

open GLOrthonormalization CompactRetractionAffineFamily InvolutionQuotient SphereAnnulus

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace (Vector 7) M]
  (g : Vector 4 → M)
  (hg : ∀ x ∈ domain 3, ContMDiffAt (𝓡 4) (𝓡 7) ∞ g x)
  (hinside : closure (points g) ⊆ openDomain 3 ×ˢ openDomain 3)
  (C : Set (PartialDiffeomorph (𝓡 7) (𝓡 7) M (Vector 7) ∞))
  (hC : ∀ y : M, ∃ c ∈ C, y ∈ c.source)
  (hreg : RegularDoublePointsOn g (openDomain 3) (openDomain 3) C)

include hg hinside hC hreg

theorem exists_ordered_interior_chart (a : ClosedPoints g) (hne : a.val.1 ≠ a.val.2) :
    ∃ d : OpenPartialHomeomorph (ClosedPoints g) ℝ, a ∈ d.source := by
  have hcont : ContinuousOn g (domain 3) :=
    fun x hx ↦ (hg x hx).continuousAt.continuousWithinAt
  have heq := closure_equal_image g hcont a.property
  have ha := hinside a.property
  obtain ⟨c, hc, hxc⟩ := hC (g a.val.1)
  have hyc : g a.val.2 ∈ c.source := heq ▸ hxc
  let N := openDomain 3 ∩ g ⁻¹' c.source
  have hN : IsOpen N :=
    (hcont.mono (openDomain_subset_domain 3)).isOpen_inter_preimage
      (isOpen_openDomain 3) c.open_source
  have hcg : ContDiffOn ℝ ∞ (c ∘ g) N := by
    intro x hx
    have hcs := c.contMDiffOn_toFun.contMDiffAt (c.open_source.mem_nhds hx.2)
    exact (hcs.comp x (hg x (openDomain_subset_domain 3 hx.1))).contDiffAt.contDiffWithinAt
  let U := (N ×ˢ N) ∩ {q : Vector 4 × Vector 4 | q.1 ≠ q.2}
  have hU : IsOpen U :=
    (hN.prod hN).inter (isClosed_eq continuous_fst continuous_snd).isOpen_compl
  let D : Vector 4 × Vector 4 → Vector 7 := fun q ↦ c (g q.1) - c (g q.2)
  have hD : ContDiffOn ℝ ∞ D U :=
    (hcg.comp contDiff_fst.contDiffOn (fun _ hq ↦ hq.1.1)).sub
      (hcg.comp contDiff_snd.contDiffOn (fun _ hq ↦ hq.1.2))
  have haU : a.val ∈ U := ⟨⟨⟨ha.1, hxc⟩, ⟨ha.2, hyc⟩⟩, hne⟩
  have haD : D a.val = 0 := by
    change c (g a.val.1) - c (g a.val.2) = 0
    rw [heq, sub_self]
  have hsurj : Surjective (fderiv ℝ D a.val) :=
    hreg c hc a.val.1 ha.1 a.val.2 ha.2 hne (Or.inl ha.1) hxc hyc heq
  obtain ⟨Φ, hΦa, hΦU, hΦfirst, _⟩ := exists_euclideanLevelNormalForm hU haU hD hsurj 1
    (by simp [GLOrthonormalization.Vector])
  let T := OpenPartialHomeomorph.ofSet Φ.source Φ.open_source
  have hImage : T.IsImage (closure (points g)) {q | D q = 0} := by
    intro b hb
    have hbU : b ∈ U := hΦU hb
    change D b = 0 ↔ b ∈ closure (points g)
    constructor
    · intro hd
      have he : g b.1 = g b.2 := c.injOn hbU.1.1.2 hbU.1.2.2 (sub_eq_zero.mp hd)
      exact subset_closure ⟨hbU.1.1.1, hbU.1.2.1, hbU.2, he⟩
    · intro hcl
      change c (g b.1) - c (g b.2) = 0
      rw [closure_equal_image g hcont hcl, sub_self]
  let a₀ : {q | D q = 0} := ⟨a.val, haD⟩
  let E := SubsetCoordinates.coordinates T hImage a a₀
  let k := RegularLevelChart.chart Φ.toOpenPartialHomeomorph (fun x _ ↦ hΦfirst x) a₀
  let d := E.trans
    (k.trans EuclideanTailCoordinates.scalar.symm.toHomeomorph.toOpenPartialHomeomorph)
  refine ⟨d, hΦa, ?_, mem_univ _⟩
  change (E a).val ∈ Φ.source
  rw [SubsetCoordinates.coordinates_val T hImage a a₀ hΦa]
  exact hΦa

theorem exists_unordered_interior_chart (a : ClosedPoints g) (hne : a.val.1 ≠ a.val.2) :
    ∃ d : OpenPartialHomeomorph (Unordered g) ℝ,
      unorderedProj g a ∈ d.source ∧ Disjoint d.source (diagonalOrbits g) := by
  obtain ⟨c, hca⟩ := exists_ordered_interior_chart g hg hinside C hC hreg a hne
  have hfree : swapClosure g a ≠ a := fun he ↦ hne ((swapClosure_fixed_iff g a).mp he)
  obtain ⟨d, hda, _, hdis⟩ := exists_free_chart (swapClosure g) (swapClosure_involutive g)
    (swapClosure g).continuous a hfree c hca
  refine ⟨d, hda, ?_⟩
  rw [diagonalOrbits_eq_fixed]
  exact hdis

theorem exists_unordered_chart_of_not_mem_diagonal (q : Unordered g)
    (hq : q ∉ diagonalOrbits g) :
    ∃ d : OpenPartialHomeomorph (Unordered g) ℝ,
      q ∈ d.source ∧ Disjoint d.source (diagonalOrbits g) := by
  obtain ⟨a, rfl⟩ := (isOpenQuotientMap_unorderedProj g).surjective q
  apply exists_unordered_interior_chart g hg hinside C hC hreg a
  intro he
  exact hq ⟨a, he, rfl⟩

end NoExoticSixSphere.AnnulusDoublePoints
