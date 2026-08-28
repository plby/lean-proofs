import Wikipedia.NoExoticSixSphere.CompactSphereCoincidenceChart
import Wikipedia.NoExoticSixSphere.UnorderedFamilyTime
import Wikipedia.NoExoticSixSphere.InvolutionFreeChart
import Wikipedia.NoExoticSixSphere.FamilyDoublePointOpenLocus

/-!
# Genuine time charts at self-transverse family double points

At a distinct pair with transverse native spatial derivatives, the actual
coincidence coordinates restrict to a time chart on the ordered closure.
The free quotient chart preserves this time on its entire source. These
charts apply at endpoint times without an exterior-injectivity assumption.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereFamily

open GLOrthonormalization FamilyEmbedding InvolutionQuotient CompactPairTrace

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] (g : ℝ → Sphere 3 → M)
  (hg : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 6) ∞ (uncurry g))

include hg in
theorem exists_ordered_transverse_time_chart (a : closure (doublePoints g))
    (hne : a.val.2.1 ≠ a.val.2.2)
    (ht : Surjective ((mfderiv (𝓡 3) (𝓡 6) (g a.val.1) a.val.2.1).coprod
      (mfderiv (𝓡 3) (𝓡 6) (g a.val.1) a.val.2.2))) :
    ∃ d : OpenPartialHomeomorph (closure (doublePoints g)) ℝ,
      a ∈ d.source ∧ ∀ q ∈ d.source, d q = q.val.1 := by
  have heq := closure_doublePoints_equal_image_of_continuous g hg.continuous a.property
  obtain ⟨Tbase, haBase, htime, hzero⟩ :=
    exists_ambient_time_coordinates g g hg hg a.val heq ht
  let W : Set (ℝ × (Sphere 3 × Sphere 3)) := {b | b.2.1 ≠ b.2.2}
  have hW : IsOpen W :=
    (isClosed_eq continuous_snd.fst continuous_snd.snd).isOpen_compl
  let T := Tbase.restrOpen W hW
  have hImage : T.IsImage (closure (doublePoints g)) (zeroLine (Vector 6)) := by
    intro b hb
    change (Tbase b).1 = 0 ↔ b ∈ closure (doublePoints g)
    rw [hzero b hb.1]
    exact ⟨fun h ↦ subset_closure ⟨hb.2, h⟩,
      fun h ↦ closure_doublePoints_equal_image_of_continuous g hg.continuous h⟩
  let a₀ : zeroLine (Vector 6) := ⟨(0, a.val.1), rfl⟩
  let E := SubsetCoordinates.coordinates T hImage a a₀
  let d := E.trans (zeroLineTimeHomeomorph (Vector 6)).toOpenPartialHomeomorph
  refine ⟨d, ⟨⟨haBase, hne⟩, mem_univ _⟩, ?_⟩
  intro q hq
  change (E q).val.2 = q.val.1
  rw [SubsetCoordinates.coordinates_val T hImage a a₀ hq.1]
  exact htime q.val

include hg in
theorem exists_unordered_transverse_time_chart (a : closure (doublePoints g))
    (hne : a.val.2.1 ≠ a.val.2.2)
    (ht : Surjective ((mfderiv (𝓡 3) (𝓡 6) (g a.val.1) a.val.2.1).coprod
      (mfderiv (𝓡 3) (𝓡 6) (g a.val.1) a.val.2.2))) :
    ∃ d : OpenPartialHomeomorph (UnorderedClosedDoublePoints g) ℝ,
      unorderedProj g a ∈ d.source ∧ Disjoint d.source (diagonalOrbits g) ∧
      ∀ q ∈ d.source, d q = unorderedTime g q := by
  obtain ⟨c, hca, hctime⟩ := exists_ordered_transverse_time_chart g hg a hne ht
  have hfree : swapClosure g a ≠ a :=
    fun he ↦ hne ((swapClosure_fixed_iff g a).mp he)
  obtain ⟨d, hd, _, hdis, hlift⟩ := exists_free_chart_with_lifts
    (swapClosure g) (swapClosure_involutive g) (swapClosure g).continuous a hfree c hca
  refine ⟨d, hd, ?_, ?_⟩
  · rw [diagonalOrbits_eq_fixed]
    exact hdis
  · intro q hq
    obtain ⟨b, hb, hbq, hdb⟩ := hlift q hq
    rw [hdb, hctime b hb, ← hbq]
    rfl

end NoExoticSixSphere.SphereFamily
