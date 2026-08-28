import Wikipedia.NoExoticSixSphere.ManifoldAffineChartDomain
import Wikipedia.NoExoticSixSphere.PartialHomeomorphSubsets
import Wikipedia.NoExoticSixSphere.UnorderedFamilyDoublePoints

/-!
# Genuine sphere-chart coordinates on the actual double-point closure

The pair chart retains time and applies one source chart to both sphere
points. Its source is restricted to where both images lie in the chosen
target chart. On this actual open region, the same-image and distinct-point
conditions are equivalent in coordinates. The local image relation therefore
also transports the original closures and respects the swap involution.
-/

noncomputable section

open Set Function TopologicalSpace
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereFamily

open GLOrthonormalization ManifoldAffineSphereFamily FamilyEmbedding

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (g : ℝ → Sphere 3 → M) (hg : Continuous (uncurry g))
  (s : SourceChart) (c : TargetChart n M)

def coordinateFamily (t : ℝ) (x : Vector 3) : Vector n := c (g t (s.symm x))

def pairTargetRegion : Opens (ℝ × (Sphere 3 × Sphere 3)) :=
  ⟨{q | g q.1 q.2.1 ∈ c.source ∧ g q.1 q.2.2 ∈ c.source},
    (c.open_source.preimage
      (hg.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd)))).inter
    (c.open_source.preimage
      (hg.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd))))⟩

def pairCoordinates : OpenPartialHomeomorph (ℝ × (Sphere 3 × Sphere 3))
    (ℝ × (Vector 3 × Vector 3)) :=
  ((OpenPartialHomeomorph.refl ℝ).prod
    (s.toOpenPartialHomeomorph.prod s.toOpenPartialHomeomorph)).restrOpen
      (pairTargetRegion g hg c) (pairTargetRegion g hg c).isOpen

theorem pairCoordinates_apply (q : ℝ × (Sphere 3 × Sphere 3)) :
    pairCoordinates g hg s c q = (q.1, (s q.2.1, s q.2.2)) := rfl

theorem mem_pairCoordinates_source (q : ℝ × (Sphere 3 × Sphere 3)) :
    q ∈ (pairCoordinates g hg s c).source ↔
      q.2.1 ∈ s.source ∧ q.2.2 ∈ s.source ∧
        g q.1 q.2.1 ∈ c.source ∧ g q.1 q.2.2 ∈ c.source := by
  change ((q.1 ∈ (univ : Set ℝ) ∧ q.2.1 ∈ s.source ∧ q.2.2 ∈ s.source) ∧
    g q.1 q.2.1 ∈ c.source ∧ g q.1 q.2.2 ∈ c.source) ↔ _
  simp only [mem_univ, true_and, and_assoc]

theorem pairCoordinates_source_swap {q : ℝ × (Sphere 3 × Sphere 3)}
    (hq : q ∈ (pairCoordinates g hg s c).source) :
    swapPair q ∈ (pairCoordinates g hg s c).source := by
  rw [mem_pairCoordinates_source] at hq ⊢
  exact ⟨hq.2.1, hq.1, hq.2.2.2, hq.2.2.1⟩

theorem pairCoordinates_swap (q : ℝ × (Sphere 3 × Sphere 3)) :
    pairCoordinates g hg s c (swapPair q) = swapPair (pairCoordinates g hg s c q) := rfl

theorem isImage_doublePoints :
    (pairCoordinates g hg s c).IsImage (doublePoints g)
      (doublePoints (coordinateFamily g s c)) := by
  intro q hq
  obtain ⟨hx, hy, hcx, hcy⟩ := (mem_pairCoordinates_source g hg s c q).mp hq
  have hsx : s.symm (s q.2.1) = q.2.1 := s.left_inv hx
  have hsy : s.symm (s q.2.2) = q.2.2 := s.left_inv hy
  change (s q.2.1 ≠ s q.2.2 ∧
    c (g q.1 (s.symm (s q.2.1))) = c (g q.1 (s.symm (s q.2.2)))) ↔
      (q.2.1 ≠ q.2.2 ∧ g q.1 q.2.1 = g q.1 q.2.2)
  rw [hsx, hsy]
  constructor
  · rintro ⟨hne, he⟩
    exact ⟨fun h ↦ hne (congrArg s h), c.injOn hcx hcy he⟩
  · rintro ⟨hne, he⟩
    exact ⟨fun h ↦ hne (s.injOn hx hy h), congrArg c he⟩

theorem isImage_closedDoublePoints :
    (pairCoordinates g hg s c).IsImage (closure (doublePoints g))
      (closure (doublePoints (coordinateFamily g s c))) :=
  (isImage_doublePoints g hg s c).closure

end NoExoticSixSphere.SphereFamily
