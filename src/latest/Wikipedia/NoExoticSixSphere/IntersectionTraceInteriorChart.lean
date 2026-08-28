import Wikipedia.NoExoticSixSphere.IntersectionTraceCoordinates
import Wikipedia.NoExoticSixSphere.HalfLineInteriorChart

/-!
# Interior curve charts on the actual coincidence trace

A surjective derivative of the valid native chart difference gives a
one-dimensional regular-level chart. Restricting the actual product chart
identifies that zero fiber with the original coincidence locus. The chart
source stays strictly between the time ends.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.IntersectionTrace

open GLOrthonormalization InvolutionQuotient

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (f g : ℝ → Sphere 3 → M)
  (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry f))
  (hg : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry g))

include hf hg in
theorem exists_interior_line_chart (a : space f g) (hta : a.val.1 ∈ Ioo 0 1)
    (s z : SphereChart) (c : ManifoldChart M)
    (hxs : a.val.2.1 ∈ s.source) (hyz : a.val.2.2 ∈ z.source)
    (hxc : f a.val.1 a.val.2.1 ∈ c.source)
    (hreg : Surjective (fderiv ℝ (coordinateDifference f g s z c)
      (a.val.1, (s a.val.2.1, z a.val.2.2)))) :
    ∃ d : OpenPartialHomeomorph (space f g) ℝ,
      a ∈ d.source ∧ ∀ b ∈ d.source, b.val.1 ∈ Ioo 0 1 := by
  let T₀ := (OpenPartialHomeomorph.refl ℝ).prod
    (s.toOpenPartialHomeomorph.prod z.toOpenPartialHomeomorph)
  let U := coordinateDomain f g s z c
  let D := coordinateDifference f g s z c
  have hU : IsOpen U := isOpen_coordinateDomain f g hf hg s z c
  have hD : ContDiffOn ℝ ∞ D U := contDiffOn_coordinateDifference f g hf hg s z c
  have haT : a.val ∈ T₀.source := ⟨mem_univ _, hxs, hyz⟩
  have hx : s.symm (s a.val.2.1) = a.val.2.1 := s.left_inv hxs
  have hy : z.symm (z a.val.2.2) = a.val.2.2 := z.left_inv hyz
  have hyc : g a.val.1 a.val.2.2 ∈ c.source := a.property.2 ▸ hxc
  have haU : T₀ a.val ∈ U := by
    change (a.val.1 ∈ Ioo 0 1 ∧ s a.val.2.1 ∈ s.target ∧ z a.val.2.2 ∈ z.target) ∧
      (f a.val.1 (s.symm (s a.val.2.1)) ∈ c.source ∧
        g a.val.1 (z.symm (z a.val.2.2)) ∈ c.source)
    rw [hx, hy]
    exact ⟨⟨hta, s.map_source hxs, z.map_source hyz⟩, hxc, hyc⟩
  have hcompare (b : ℝ × (Sphere 3 × Sphere 3))
      (hbT : b ∈ T₀.source) (hbU : T₀ b ∈ U) :
      D (T₀ b) = 0 ↔ f b.1 b.2.1 = g b.1 b.2.2 := by
    have h := coordinateDifference_zero_iff f g s z c (T₀ b) hbU
    change D (T₀ b) = 0 ↔
      f b.1 (s.symm (s b.2.1)) = g b.1 (z.symm (z b.2.2)) at h
    have hx' : s.symm (s b.2.1) = b.2.1 := s.left_inv hbT.2.1
    have hy' : z.symm (z b.2.2) = b.2.2 := z.left_inv hbT.2.2
    rwa [hx', hy'] at h
  have haD : D (T₀ a.val) = 0 := (hcompare a.val haT haU).mpr a.property.2
  obtain ⟨Φ, hΦa, hΦU, hΦfirst, _⟩ := exists_euclideanLevelNormalForm hU haU hD hreg 1
    (by simp [GLOrthonormalization.Vector, PairModel])
  let T := T₀.trans (OpenPartialHomeomorph.ofSet Φ.source Φ.open_source)
  have haT' : a.val ∈ T.source := ⟨haT, hΦa⟩
  have hImage : T.IsImage (space f g) {q | D q = 0} := by
    intro b hb
    have hbU : T₀ b ∈ U := hΦU hb.2
    change D (T₀ b) = 0 ↔ b ∈ space f g
    constructor
    · intro hd
      exact ⟨⟨hbU.1.1.1.le, hbU.1.1.2.le⟩, (hcompare b hb.1 hbU).mp hd⟩
    · intro hbspace
      exact (hcompare b hb.1 hbU).mpr hbspace.2
  let a₀ : {q | D q = 0} := ⟨T₀ a.val, haD⟩
  let E := SubsetCoordinates.coordinates T hImage a a₀
  let k := RegularLevelChart.chart Φ.toOpenPartialHomeomorph (fun x _ ↦ hΦfirst x) a₀
  let d := E.trans
    (k.trans EuclideanTailCoordinates.scalar.symm.toHomeomorph.toOpenPartialHomeomorph)
  have had : a ∈ d.source := by
    refine ⟨haT', ?_, mem_univ _⟩
    change (E a).val ∈ Φ.source
    rw [SubsetCoordinates.coordinates_val T hImage a a₀ haT']
    exact hΦa
  refine ⟨d, had, ?_⟩
  intro b hb
  have hbT : b.val ∈ T.source := hb.1
  exact (hΦU hbT.2).1.1

/-- Regularity refers to the derivative of the original coincidence equation
in actual source and target charts, not to a chart on the trace. -/
def ChartRegular : Prop :=
  ∀ a : space f g, a.val.1 ∈ Ioo 0 1 →
    ∃ (s z : SphereChart) (c : ManifoldChart M),
      a.val.2.1 ∈ s.source ∧ a.val.2.2 ∈ z.source ∧
      f a.val.1 a.val.2.1 ∈ c.source ∧
      Surjective (fderiv ℝ (coordinateDifference f g s z c)
        (a.val.1, (s a.val.2.1, z a.val.2.2)))

include hf hg in
theorem exists_interior_halfLine_chart (hreg : ChartRegular f g)
    (a : space f g) (ha : a ∉ ends f g) :
    ∃ d : OpenPartialHomeomorph (space f g) HalfLine,
      a ∈ d.source ∧ ∀ b ∈ d.source, (d b).val = 0 ↔ b ∈ ends f g := by
  have hta : a.val.1 ∈ Ioo 0 1 :=
    ⟨lt_of_le_of_ne a.property.1.1 (fun h ↦ ha (Or.inl h.symm)),
      lt_of_le_of_ne a.property.1.2 (fun h ↦ ha (Or.inr h))⟩
  obtain ⟨s, z, c, hxs, hyz, hxc, hs⟩ := hreg a hta
  obtain ⟨d, hda, hdt⟩ := exists_interior_line_chart f g hf hg a hta s z c hxs hyz hxc hs
  refine ⟨d.trans positiveHalfLine, ⟨hda, mem_univ _⟩, ?_⟩
  intro b hb
  have htb := hdt b hb.1
  have hnot : b ∉ ends f g := by
    rintro (h | h)
    · exact htb.1.ne' h
    · exact htb.2.ne h
  exact iff_of_false (Real.exp_ne_zero _) hnot

end NoExoticSixSphere.IntersectionTrace
