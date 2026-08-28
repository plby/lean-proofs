import Wikipedia.NoExoticSixSphere.ManifoldAffineBoundaryCurve
import Wikipedia.NoExoticSixSphere.ManifoldAffineInteriorCurve
import Wikipedia.NoExoticSixSphere.SphereFamilyTransverseTimeChart
import Wikipedia.NoExoticSixSphere.ClosedTimeWindowCharts
import Wikipedia.NoExoticSixSphere.HalfLineInteriorChart
import Wikipedia.NoExoticSixSphere.SphereFamilyDiagonalClosure

/-!
# Finite even boundary for a generic unordered family cut at immersed endpoints

The original generic interior charts and singular reflection charts combine
with actual time charts at self-transverse immersed endpoints. Restricting
to the closed unit-time window makes the quotient compact without imposing
global injectivity on exterior slices. Its boundary consists exactly of
diagonal orbits and endpoint double-point orbits in that window.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.ManifoldAffineSphereFamily

open GLOrthonormalization EuclideanEmbedding FamilyEmbedding InvolutionQuotient SphereFamily

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M]
  (e : EuclideanEmbedding 6 M) (r : TubularRetraction e) (f : ℝ → Sphere 3 → M)
  (hf : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry f)) (p : Parameters e)
  (hg : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry (map e r f p)))
  (S : Set SourceChart) (C : Set (TargetChart 6 M))
  (hS : ∀ x : Sphere 3, ∃ s ∈ S, x ∈ s.source)
  (hC : ∀ x : M, ∃ c ∈ C, x ∈ c.source)
  (hp : ∀ t x, ambient e f p t x ∈ r.domain)
  (hgen : GenericInCharts e r f hf S C p)

include hg hS hC hp hgen in
theorem exists_unordered_halfLine_chart_at_time
    (q : UnorderedClosedDoublePoints (map e r f p))
    (htime : unorderedTime (map e r f p) q ∈ Ioo (0 : ℝ) 1) :
    ∃ d : OpenPartialHomeomorph (UnorderedClosedDoublePoints (map e r f p)) HalfLine,
      q ∈ d.source ∧ ∀ y ∈ d.source, (d y).val = 0 ↔ y ∈ diagonalOrbits (map e r f p) := by
  obtain ⟨a, rfl⟩ := (isOpenQuotientMap_unorderedProj (map e r f p)).surjective q
  by_cases he : a.val.2.1 = a.val.2.2
  · have ha : (a.val.1, (a.val.2.1, a.val.2.1)) ∈
        closure (doublePoints (map e r f p)) := by
      have ha' : (a.val.1, (a.val.2.1, a.val.2.2)) ∈
          closure (doublePoints (map e r f p)) := a.property
      rwa [← he] at ha'
    have hsing := singular_of_diagonal_mem_closure (map e r f p) hg (a.val.1, a.val.2.1) ha
    obtain ⟨hb, d, hd, _, hiff⟩ := exists_unordered_chart_at_singular
      e r f hf p hg S C hS hC hp hgen (a.val.1, a.val.2.1) htime hsing
    have hab : (⟨(a.val.1, (a.val.2.1, a.val.2.1)), hb⟩ :
        closure (doublePoints (map e r f p))) = a :=
      Subtype.ext (Prod.ext rfl (Prod.ext rfl he))
    rw [hab] at hd
    exact ⟨d, hd, hiff⟩
  · obtain ⟨c, hc, hdis⟩ :=
      exists_unordered_interior_chart_at_time e r f hf p hg S C hS hC hp hgen rfl a he htime
    refine ⟨c.trans positiveHalfLine, ⟨hc, mem_univ _⟩, ?_⟩
    intro y hy
    change Real.exp (c y) = 0 ↔ y ∈ diagonalOrbits (map e r f p)
    exact iff_of_false (Real.exp_ne_zero _) ((disjoint_left.mp hdis) hy.1)

include hg hS hC hp hgen in
theorem finite_even_unordered_window_boundary
    (hd : ∀ t, t = 0 ∨ t = 1 → ∀ x,
      Injective (mfderiv (𝓡 3) (𝓡 6) (map e r f p t) x))
    (ht : ∀ t, t = 0 ∨ t = 1 → ∀ x y, x ≠ y →
      map e r f p t x = map e r f p t y → Surjective
        ((mfderiv (𝓡 3) (𝓡 6) (map e r f p t) x).coprod
          (mfderiv (𝓡 3) (𝓡 6) (map e r f p t) y))) :
    (ClosedTimeWindow.boundary (unorderedTime (map e r f p))
      (diagonalOrbits (map e r f p))).Finite ∧
    Even (ClosedTimeWindow.boundary (unorderedTime (map e r f p))
      (diagonalOrbits (map e r f p))).ncard := by
  let : T2Space M := e.closedEmbedding.isEmbedding.t2Space
  let := t2Space_unordered (map e r f p)
  apply ClosedTimeWindow.finite_even_boundary (unorderedTime (map e r f p))
    (diagonalOrbits (map e r f p)) (isCompact_unorderedWindow (map e r f p) 0 1)
  · exact exists_unordered_halfLine_chart_at_time e r f hf p hg S C hS hC hp hgen
  · intro q hq
    obtain ⟨a, rfl⟩ := (isOpenQuotientMap_unorderedProj (map e r f p)).surjective q
    have hne : a.val.2.1 ≠ a.val.2.2 := by
      intro he
      have ha : (a.val.1, (a.val.2.1, a.val.2.1)) ∈
          closure (doublePoints (map e r f p)) := by
        have ha' : (a.val.1, (a.val.2.1, a.val.2.2)) ∈
            closure (doublePoints (map e r f p)) := a.property
        rwa [← he] at ha'
      exact diagonal_not_mem_closure (map e r f p) hg (a.val.1, a.val.2.1)
        (hd a.val.1 hq a.val.2.1) ha
    have heq := closure_doublePoints_equal_image_of_continuous (map e r f p) hg.continuous
      a.property
    obtain ⟨c, hc, hdis, htime⟩ := exists_unordered_transverse_time_chart (map e r f p) hg
      a hne (ht a.val.1 hq a.val.2.1 a.val.2.2 hne heq)
    exact ⟨c, hc, htime, hdis⟩

end NoExoticSixSphere.ManifoldAffineSphereFamily
