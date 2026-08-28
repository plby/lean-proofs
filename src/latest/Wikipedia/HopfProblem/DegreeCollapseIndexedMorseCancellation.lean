import Wikipedia.HopfProblem.DegreeCollapseIntrinsicMorseIndex

/-!
# Exact critical-point counts in each native Morse index after pair removal

Surviving function germs preserve the intrinsic index. Hence cancellation
subtracts precisely the selected two points from every indexed critical set.
For an adjacent-index pair, each of its two counts falls by one and all
other index counts remain unchanged.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ} {p q : M}

def nativeMorseCount (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] (f : M → ℝ) (k : ℕ) : ℕ :=
  {z : M | z ∈ criticalPoints E f ∧ nativeMorseIndex E f z = k}.ncard

theorem indexed_criticalPoints_after_pair_removal
    (hcrit : ∀ z, z ∈ criticalPoints E g ↔ z ∈ criticalPoints E f ∧ z ≠ p ∧ z ≠ q)
    (hkeep : ∀ z ∈ criticalPoints E g, g =ᶠ[𝓝 z] f) (k : ℕ) :
    {z : M | z ∈ criticalPoints E g ∧ nativeMorseIndex E g z = k} =
      {z : M | z ∈ criticalPoints E f ∧ nativeMorseIndex E f z = k} \ {p, q} := by
  ext z
  simp only [mem_setOf_eq, Set.mem_sdiff, mem_insert_iff, mem_singleton_iff, not_or]
  constructor
  · rintro ⟨hzg, hindex⟩
    obtain ⟨hzf, hzp, hzq⟩ := (hcrit z).mp hzg
    rw [nativeMorseIndex_congr_germ (hkeep z hzg)] at hindex
    exact ⟨⟨hzf, hindex⟩, hzp, hzq⟩
  · rintro ⟨⟨hzf, hindex⟩, hzp, hzq⟩
    have hzg := (hcrit z).mpr ⟨hzf, hzp, hzq⟩
    exact ⟨hzg, (nativeMorseIndex_congr_germ (hkeep z hzg)).trans hindex⟩

open Classical in
theorem nativeMorseCount_after_pair_removal
    (hfinite : (criticalPoints E f).Finite)
    (hp : p ∈ criticalPoints E f) (hq : q ∈ criticalPoints E f) (hpq : p ≠ q)
    (hcrit : ∀ z, z ∈ criticalPoints E g ↔ z ∈ criticalPoints E f ∧ z ≠ p ∧ z ≠ q)
    (hkeep : ∀ z ∈ criticalPoints E g, g =ᶠ[𝓝 z] f) (k : ℕ) :
    nativeMorseCount E g k + (if nativeMorseIndex E f p = k then 1 else 0) +
      (if nativeMorseIndex E f q = k then 1 else 0) = nativeMorseCount E f k := by
  let K := {z : M | z ∈ criticalPoints E f ∧ nativeMorseIndex E f z = k}
  have hK : K.Finite := hfinite.subset (fun _ hz => hz.1)
  have hdiff : K \ (K ∩ {p, q}) = K \ {p, q} := by
    ext z
    simp only [Set.mem_sdiff, mem_inter_iff]
    tauto
  have hrem : (K ∩ {p, q}).ncard =
      (if nativeMorseIndex E f p = k then 1 else 0) +
        (if nativeMorseIndex E f q = k then 1 else 0) := by
    by_cases hip : nativeMorseIndex E f p = k
    · have hpK : p ∈ K := ⟨hp, hip⟩
      rw [inter_insert_of_mem hpK, if_pos hip]
      by_cases hiq : nativeMorseIndex E f q = k
      · rw [inter_singleton_of_mem (show q ∈ K from ⟨hq, hiq⟩), if_pos hiq, ncard_pair hpq]
      · rw [inter_singleton_of_notMem (show q ∉ K from fun h => hiq h.2), if_neg hiq]
        simp
    · have hpK : p ∉ K := fun h => hip h.2
      rw [inter_insert_of_notMem hpK, if_neg hip]
      by_cases hiq : nativeMorseIndex E f q = k
      · rw [inter_singleton_of_mem (show q ∈ K from ⟨hq, hiq⟩), if_pos hiq]
        simp
      · rw [inter_singleton_of_notMem (show q ∉ K from fun h => hiq h.2), if_neg hiq]
        simp
  have hc := ncard_sdiff_add_ncard_of_subset (inter_subset_left : K ∩ {p, q} ⊆ K) hK
  rw [hdiff, hrem] at hc
  unfold nativeMorseCount
  rw [indexed_criticalPoints_after_pair_removal hcrit hkeep k]
  exact (Nat.add_assoc _ _ _).trans hc

open Classical in
theorem nativeMorseCount_adjacent_pair
    (hfinite : (criticalPoints E f).Finite)
    (hp : p ∈ criticalPoints E f) (hq : q ∈ criticalPoints E f) (hpq : p ≠ q)
    (hcrit : ∀ z, z ∈ criticalPoints E g ↔ z ∈ criticalPoints E f ∧ z ≠ p ∧ z ≠ q)
    (hkeep : ∀ z ∈ criticalPoints E g, g =ᶠ[𝓝 z] f) {k : ℕ}
    (hip : nativeMorseIndex E f p = k) (hiq : nativeMorseIndex E f q = k + 1) :
    nativeMorseCount E g k + 1 = nativeMorseCount E f k ∧
      nativeMorseCount E g (k + 1) + 1 = nativeMorseCount E f (k + 1) ∧
      ∀ j, j ≠ k → j ≠ k + 1 → nativeMorseCount E g j = nativeMorseCount E f j := by
  have hc := nativeMorseCount_after_pair_removal hfinite hp hq hpq hcrit hkeep
  refine ⟨?_, ?_, ?_⟩
  · simpa [hip, hiq] using hc k
  · simpa [hip, hiq, show k ≠ k + 1 by omega] using hc (k + 1)
  · intro j hj hj'
    simpa only [hip, hiq, if_neg (Ne.symm hj), if_neg (Ne.symm hj'), Nat.add_zero] using hc j

theorem native_index_order_of_critical_germs
    (horder : ∀ x ∈ criticalPoints E f, ∀ y ∈ criticalPoints E f,
      f x ≤ f y → nativeMorseIndex E f x ≤ nativeMorseIndex E f y)
    (hsub : criticalPoints E g ⊆ criticalPoints E f)
    (hkeep : ∀ z ∈ criticalPoints E g, g =ᶠ[𝓝 z] f) :
    ∀ x ∈ criticalPoints E g, ∀ y ∈ criticalPoints E g,
      g x ≤ g y → nativeMorseIndex E g x ≤ nativeMorseIndex E g y := by
  intro x hx y hy hxy
  rw [nativeMorseIndex_congr_germ (hkeep x hx), nativeMorseIndex_congr_germ (hkeep y hy)]
  apply horder x (hsub hx) y (hsub hy)
  rwa [(hkeep x hx).self_of_nhds, (hkeep y hy).self_of_nhds] at hxy

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
