import Wikipedia.HopfProblem.DegreeCollapseMinimalMiddleIndices
import Wikipedia.SmoothSixDPoincare.OrderedMiddleUnimodular

/-!
# The remaining index-three block is empty

Once indices four and five are absent, the tail of the ordered middle
blocks consists only of maxima. The unique maximum makes these blocks
exhaust the interior. The actual homology presentation then has equally
many index-two and index-three handles, so absence of index two implies
absence of index three and exactly two critical values in total.
-/

noncomputable section

open Set Function Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [Nonempty M] {f : M → ℝ}

theorem native_index_excluded_of_count_zero (S : SurgeryWindows E f) {k : ℕ}
    (hcount : nativeMorseCount E f k = 0) :
    ∀ z ∈ criticalPoints E f, nativeMorseIndex E f z ≠ k := by
  have hfinite : {z : M | z ∈ criticalPoints E f ∧ nativeMorseIndex E f z = k}.Finite :=
    S.finite.subset (fun _ hz => hz.1)
  have hempty : {z : M | z ∈ criticalPoints E f ∧ nativeMorseIndex E f z = k} = ∅ :=
    (Set.ncard_eq_zero hfinite).mp hcount
  intro z hz hi
  have hmem : z ∈ {z : M | z ∈ criticalPoints E f ∧ nativeMorseIndex E f z = k} := ⟨hz, hi⟩
  rw [hempty] at hmem
  exact hmem

theorem middle_blocks_complete_of_no_four_five
    (S : SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (r n : ℕ)
    (htwo : S.HasIndexTwoPrefix r) (hrc : r + n < S.count)
    (hthree : S.HasIndexThreeBlock r n)
    (hafter : ∀ i : Fin S.count, r + n < i.val →
      4 ≤ Module.finrank ℝ (S.data (S.point i)).chart.NegativeCoordinates)
    (hsix : nativeMorseCount E f 6 = 1) (hfour : nativeMorseCount E f 4 = 0)
    (hfive : nativeMorseCount E f 5 = 0) : r + n + 2 = S.count := by
  have hpos := S.count_pos hf
  have hidx (i : Fin S.count) : nativeMorseIndex E f (S.point i) = 6 ↔
      r + n + 1 ≤ i.val ∧ i.val < S.count := by
    have hle : nativeMorseIndex E f (S.point i) ≤ 6 := by
      simpa only [hdim] using (nativeMorseIndex_le (E := E) (f := f) (p := (S.point i).val))
    have hne4 := native_index_excluded_of_count_zero S hfour _ (S.point i).property
    have hne5 := native_index_excluded_of_count_zero S hfive _ (S.point i).property
    by_cases ha : r + n < i.val
    · have hh := hafter i ha
      rw [← nativeMorseIndex_eq_chart (S.data (S.point i)).chart] at hh
      have hi := i.isLt
      omega
    · have hh : nativeMorseIndex E f (S.point i) ≤ 3 := by
        by_cases hz : i.val = 0
        · have he : i = ⟨0, hpos⟩ := Fin.ext hz
          have hzidx : nativeMorseIndex E f (S.point i) = 0 := by
            rw [he]
            exact (nativeMorseIndex_eq_chart (S.data (S.first hpos)).chart).trans
              (S.first_index_zero hf hpos)
          omega
        · by_cases hr : i.val ≤ r
          · rw [nativeMorseIndex_eq_chart (S.data (S.point i)).chart, htwo i (by omega) hr]
            omega
          · rw [nativeMorseIndex_eq_chart (S.data (S.point i)).chart,
              hthree i (by omega) (by omega)]
      omega
  have hcount := nativeMorseCount_eq_interval_length S 6 (r + n + 1) S.count
    (by omega) le_rfl hidx
  omega

theorem ordered_no_middle_indices_count_two
    (S : SurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (e : M ≃ₕ SixSphere)
    (horder : ∀ x y : criticalPoints E f, f x < f y →
      nativeMorseIndex E f x ≤ nativeMorseIndex E f y)
    (hzero : nativeMorseCount E f 0 = 1) (hsix : nativeMorseCount E f 6 = 1)
    (hone : nativeMorseCount E f 1 = 0) (htwo : nativeMorseCount E f 2 = 0)
    (hfour : nativeMorseCount E f 4 = 0) (hfive : nativeMorseCount E f 5 = 0) :
    nativeMorseCount E f 3 = 0 ∧ S.count = 2 := by
  obtain ⟨r, n, hprefix, hrc, hblock, -, hafter⟩ :=
    exists_middle_index_blocks S hf hdim horder hzero hone
  obtain ⟨hr, hn⟩ := native_middle_block_counts S hf r n hprefix hrc hblock hafter
  have hcount := middle_blocks_complete_of_no_four_five S hf hdim r n hprefix hrc hblock
    hafter hsix hfour hfive
  have heq := S.middle_counts_equal hf hdim e r n hprefix hrc hblock hcount
  omega

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
