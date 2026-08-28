import Wikipedia.NoExoticSixSphere.RegularPointNeighborhood

/-!
# Nearby values remain regular for a compact source

Openness of the regular-point locus passes through a closed map to openness
of its regular-value locus. In particular this applies to smooth maps with
compact source and Hausdorff target. The result protects whole endpoint
fibers when the target value moves slightly; it does not assert density of
regular values.
-/

open scoped Manifold ContDiff Topology
open Set

namespace NoExoticSixSphere

variable {B H M C H' N : Type*}
  [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B] [TopologicalSpace H]
  {I : ModelWithCorners ℝ B H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup C] [NormedSpace ℝ C] [FiniteDimensional ℝ C] [TopologicalSpace H']
  {J : ModelWithCorners ℝ C H'} [J.Boundaryless]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

theorem eventually_regularValue_of_isClosedMap {f : M → N}
    (hf : ContMDiff I J ∞ f) (hclosed : IsClosedMap f) {b : N}
    (hreg : ∀ x, f x = b → Function.Surjective (mfderiv I J f x)) :
    ∀ᶠ c in 𝓝 b, ∀ x, f x = c → Function.Surjective (mfderiv I J f x) := by
  apply hclosed.eventually_nhds_fiber b
  intro x hx
  exact (isOpen_regularPoints hf).mem_nhds (hreg x hx)

theorem isOpen_regularValues_of_isClosedMap {f : M → N}
    (hf : ContMDiff I J ∞ f) (hclosed : IsClosedMap f) :
    IsOpen {b | ∀ x, f x = b → Function.Surjective (mfderiv I J f x)} := by
  rw [isOpen_iff_mem_nhds]
  exact fun _ hb ↦ eventually_regularValue_of_isClosedMap hf hclosed hb

theorem exists_regularValueNeighborhood [CompactSpace M] [T2Space N]
    {f : M → N} (hf : ContMDiff I J ∞ f) {b : N}
    (hreg : ∀ x, f x = b → Function.Surjective (mfderiv I J f x)) :
    ∃ V : Set N, IsOpen V ∧ b ∈ V ∧
      ∀ c ∈ V, ∀ x, f x = c → Function.Surjective (mfderiv I J f x) := by
  exact ⟨{c | ∀ x, f x = c → Function.Surjective (mfderiv I J f x)},
    isOpen_regularValues_of_isClosedMap hf hf.continuous.isClosedMap,
    hreg, fun _ hc ↦ hc⟩

theorem exists_commonRegularValueNeighborhood [CompactSpace M] [T2Space N]
    {f₀ f₁ : M → N} (h₀ : ContMDiff I J ∞ f₀) (h₁ : ContMDiff I J ∞ f₁) {b : N}
    (hreg₀ : ∀ x, f₀ x = b → Function.Surjective (mfderiv I J f₀ x))
    (hreg₁ : ∀ x, f₁ x = b → Function.Surjective (mfderiv I J f₁ x)) :
    ∃ V : Set N, IsOpen V ∧ b ∈ V ∧
      (∀ c ∈ V, ∀ x, f₀ x = c → Function.Surjective (mfderiv I J f₀ x)) ∧
      (∀ c ∈ V, ∀ x, f₁ x = c → Function.Surjective (mfderiv I J f₁ x)) := by
  obtain ⟨V₀, hV₀, hb₀, hr₀⟩ := exists_regularValueNeighborhood h₀ hreg₀
  obtain ⟨V₁, hV₁, hb₁, hr₁⟩ := exists_regularValueNeighborhood h₁ hreg₁
  exact ⟨V₀ ∩ V₁, hV₀.inter hV₁, ⟨hb₀, hb₁⟩,
    fun c hc ↦ hr₀ c hc.1, fun c hc ↦ hr₁ c hc.2⟩

end NoExoticSixSphere
