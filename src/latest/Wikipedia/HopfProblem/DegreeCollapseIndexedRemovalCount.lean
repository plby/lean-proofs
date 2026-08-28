import Wikipedia.HopfProblem.DegreeCollapseIndexedMorseCancellation

/-!
# Exact indexed removal counts from preserved intrinsic indices

Value rearrangement need not preserve surviving function germs relative to
the original function, but it does preserve their intrinsic indices. These
weaker data suffice for exact indexed counts after the two selected points
are removed.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f g : M → ℝ} {p q : M}

theorem indexed_criticalPoints_removed_of_index_eq
    (hcrit : ∀ z, z ∈ criticalPoints E g ↔ z ∈ criticalPoints E f ∧ z ≠ p ∧ z ≠ q)
    (hindex : ∀ z ∈ criticalPoints E g, nativeMorseIndex E g z = nativeMorseIndex E f z)
    (k : ℕ) :
    {z : M | z ∈ criticalPoints E g ∧ nativeMorseIndex E g z = k} =
      {z : M | z ∈ criticalPoints E f ∧ nativeMorseIndex E f z = k} \ {p, q} := by
  ext z
  simp only [mem_setOf_eq, mem_sdiff, mem_insert_iff, mem_singleton_iff, not_or]
  constructor
  · rintro ⟨hz, hi⟩
    obtain ⟨hzf, hzp, hzq⟩ := (hcrit z).mp hz
    exact ⟨⟨hzf, (hindex z hz).symm.trans hi⟩, hzp, hzq⟩
  · rintro ⟨⟨hzf, hi⟩, hzp, hzq⟩
    have hz := (hcrit z).mpr ⟨hzf, hzp, hzq⟩
    exact ⟨hz, (hindex z hz).trans hi⟩

open Classical in
theorem nativeMorseCount_removed_of_index_eq
    (hfinite : (criticalPoints E f).Finite)
    (hp : p ∈ criticalPoints E f) (hq : q ∈ criticalPoints E f) (hpq : p ≠ q)
    (hcrit : ∀ z, z ∈ criticalPoints E g ↔ z ∈ criticalPoints E f ∧ z ≠ p ∧ z ≠ q)
    (hindex : ∀ z ∈ criticalPoints E g, nativeMorseIndex E g z = nativeMorseIndex E f z)
    (k : ℕ) :
    nativeMorseCount E g k + (if nativeMorseIndex E f p = k then 1 else 0) +
      (if nativeMorseIndex E f q = k then 1 else 0) = nativeMorseCount E f k := by
  let K := {z : M | z ∈ criticalPoints E f ∧ nativeMorseIndex E f z = k}
  have hK : K.Finite := hfinite.subset (fun _ hz => hz.1)
  have hdiff : K \ (K ∩ {p, q}) = K \ {p, q} := by
    ext z
    simp only [mem_sdiff, mem_inter_iff]
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
  rw [indexed_criticalPoints_removed_of_index_eq hcrit hindex k]
  exact (Nat.add_assoc _ _ _).trans hc

theorem nativeMorseCount_adjacent_removed_of_index_eq
    (hfinite : (criticalPoints E f).Finite)
    (hp : p ∈ criticalPoints E f) (hq : q ∈ criticalPoints E f) (hpq : p ≠ q)
    (hcrit : ∀ z, z ∈ criticalPoints E g ↔ z ∈ criticalPoints E f ∧ z ≠ p ∧ z ≠ q)
    (hindex : ∀ z ∈ criticalPoints E g, nativeMorseIndex E g z = nativeMorseIndex E f z)
    {k : ℕ} (hip : nativeMorseIndex E f p = k) (hiq : nativeMorseIndex E f q = k + 1) :
    nativeMorseCount E g k + 1 = nativeMorseCount E f k ∧
      nativeMorseCount E g (k + 1) + 1 = nativeMorseCount E f (k + 1) ∧
      ∀ j, j ≠ k → j ≠ k + 1 → nativeMorseCount E g j = nativeMorseCount E f j := by
  have hc := nativeMorseCount_removed_of_index_eq hfinite hp hq hpq hcrit hindex
  refine ⟨?_, ?_, ?_⟩
  · simpa [hip, hiq] using hc k
  · simpa [hip, hiq, show k ≠ k + 1 by omega] using hc (k + 1)
  · intro j hj hj'
    simpa only [hip, hiq, if_neg (Ne.symm hj), if_neg (Ne.symm hj'), Nat.add_zero] using hc j

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
