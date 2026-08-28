import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Smooth partitions normalized near a distinguished closed set

An open cover of a finite-dimensional Hausdorff sigma-compact smooth manifold
admits a subordinate smooth partition which is identically one in a prescribed
cover member near a closed subset of that member.  All other partition functions
have topological support disjoint from the closure of the chosen neighborhood.

The partition is obtained from an actual adapted open cover, rather than assumed
as extra data.  The index type need not be finite.
-/

noncomputable section

open Function Set
open scoped Manifold Topology ContDiff

namespace Wikipedia.HopfProblem.HolomorphicCousin

variable {ι E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

/-- A smooth partition subordinate to an arbitrary open cover can be normalized
on the closure of an open neighborhood of a closed set in one cover member.
The topological supports of all other partition functions miss that closure. -/
theorem exists_smoothPartitionOfUnity_normalized_near_closed
    (U : ι → Set M) (hUo : ∀ i, IsOpen (U i))
    (hUc : univ ⊆ ⋃ i, U i) (i₀ : ι) {K : Set M}
    (hK : IsClosed K) (hKU : K ⊆ U i₀) :
    ∃ V : Set M, IsOpen V ∧ K ⊆ V ∧ closure V ⊆ U i₀ ∧
      ∃ ρ : SmoothPartitionOfUnity ι I M univ,
        ρ.IsSubordinate U ∧
        EqOn (ρ i₀) (fun _ => 1) (closure V) ∧
        ∀ i, i ≠ i₀ → Disjoint (tsupport (ρ i)) (closure V) := by
  classical
  let : LocallyCompactSpace H := I.locallyCompactSpace
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  obtain ⟨V, hVo, hKV, hVU⟩ := normal_exists_closure_subset hK (hUo i₀) hKU
  let W : ι → Set M := fun i => if i = i₀ then U i else U i \ closure V
  have hWo (i : ι) : IsOpen (W i) := by
    by_cases hi : i = i₀
    · simpa only [W, if_pos hi] using hUo i
    · simpa only [W, if_neg hi] using (hUo i).sdiff isClosed_closure
  have hWc : univ ⊆ ⋃ i, W i := by
    intro x hx
    by_cases hxV : x ∈ closure V
    · apply mem_iUnion_of_mem i₀
      simpa only [W, if_pos rfl] using hVU hxV
    · obtain ⟨i, hxi⟩ := mem_iUnion.mp (hUc hx)
      apply mem_iUnion_of_mem i
      by_cases hi : i = i₀
      · simpa only [W, if_pos hi] using hxi
      · simpa only [W, if_neg hi, mem_sdiff] using And.intro hxi hxV
  obtain ⟨ρ, hρW⟩ := SmoothPartitionOfUnity.exists_isSubordinate I
    isClosed_univ W hWo hWc
  have hρU : ρ.IsSubordinate U := by
    intro i x hx
    have hxi := hρW i hx
    by_cases hi : i = i₀
    · simpa only [W, if_pos hi] using hxi
    · exact (show x ∈ U i \ closure V by simpa only [W, if_neg hi] using hxi).1
  have hdisjoint (i : ι) (hi : i ≠ i₀) :
      Disjoint (tsupport (ρ i)) (closure V) := by
    apply Set.disjoint_left.mpr
    intro x hx hxV
    have hxi : x ∈ U i \ closure V := by
      simpa only [W, if_neg hi] using hρW i hx
    exact hxi.2 hxV
  have hzero (x : M) (hx : x ∈ closure V) (i : ι) (hi : i ≠ i₀) : ρ i x = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    exact fun hs => Set.disjoint_left.mp (hdisjoint i hi) hs hx
  refine ⟨V, hVo, hKV, hVU, ρ, hρU, ?_, hdisjoint⟩
  intro x hx
  exact (finsum_eq_single (fun i => ρ i x) i₀ (hzero x hx)).symm.trans
    (ρ.sum_eq_one (mem_univ x))

/-- Pointwise form of the relative partition construction: one distinguished
function equals one, and every other function equals zero, on an actual open
neighborhood of the prescribed closed set. -/
theorem exists_smoothPartitionOfUnity_eq_one_near_closed
    (U : ι → Set M) (hUo : ∀ i, IsOpen (U i))
    (hUc : univ ⊆ ⋃ i, U i) (i₀ : ι) {K : Set M}
    (hK : IsClosed K) (hKU : K ⊆ U i₀) :
    ∃ V : Set M, IsOpen V ∧ K ⊆ V ∧ V ⊆ U i₀ ∧
      ∃ ρ : SmoothPartitionOfUnity ι I M univ,
        ρ.IsSubordinate U ∧
        (∀ x ∈ V, ρ i₀ x = 1) ∧
        (∀ i, i ≠ i₀ → ∀ x ∈ V, ρ i x = 0) ∧
        ∀ i, i ≠ i₀ → Disjoint (tsupport (ρ i)) V := by
  obtain ⟨V, hVo, hKV, hVU, ρ, hρU, hρone, hρdisjoint⟩ :=
    exists_smoothPartitionOfUnity_normalized_near_closed I U hUo hUc i₀ hK hKU
  refine ⟨V, hVo, hKV, subset_closure.trans hVU, ρ, hρU, ?_, ?_, ?_⟩
  · intro x hx
    exact hρone (subset_closure hx)
  · intro i hi x hx
    apply image_eq_zero_of_notMem_tsupport
    exact fun hs => Set.disjoint_left.mp (hρdisjoint i hi) hs (subset_closure hx)
  · intro i hi
    exact (hρdisjoint i hi).mono_right subset_closure

end Wikipedia.HopfProblem.HolomorphicCousin
