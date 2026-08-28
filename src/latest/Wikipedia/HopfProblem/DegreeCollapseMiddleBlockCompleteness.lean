import Wikipedia.HopfProblem.DegreeCollapseArbitraryColumnSequence

/-!
# The original chronological middle block is complete and has the required cut

Intrinsic index counts identify the constructed consecutive blocks. Thus
every index-three critical point has an original block label, and every
lower-index critical value is below the actual common base cut.
-/

noncomputable section

open Set Function Manifold
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [Nonempty M] {f : M → ℝ}

theorem native_middle_block_complete_and_cut
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6)
    (horder : ∀ x y : criticalPoints E f, f x < f y →
      nativeMorseIndex E f x ≤ nativeMorseIndex E f y)
    (hzero : nativeMorseCount E f 0 = 1) (hone : nativeMorseCount E f 1 = 0)
    (r n : ℕ) (hr : nativeMorseCount E f 2 = r) (hn : nativeMorseCount E f 3 = n)
    (hrc : r + n < S.toSurgeryWindows.count) :
    (∀ z : criticalPoints E f, nativeMorseIndex E f z = 3 →
      ∃ j, nativeMiddleBlockPoint S r n hrc j = z) ∧
    (∀ z : criticalPoints E f, nativeMorseIndex E f z < 3 →
      f z < nativeMiddleBaseCut S r n hrc) := by
  obtain ⟨r', n', htwo, hrc', hthree, -, hafter⟩ :=
    exists_middle_index_blocks S.toSurgeryWindows hf hdim horder hzero hone
  obtain ⟨hr', hn'⟩ :=
    native_middle_block_counts S.toSurgeryWindows hf r' n' htwo hrc' hthree hafter
  have hrr : r' = r := hr'.symm.trans hr
  have hnn : n' = n := hn'.symm.trans hn
  rw [hrr] at htwo
  rw [hrr, hnn] at hthree hafter
  let W := S.toSurgeryWindows
  have hrcW : r + n < W.count := hrc
  have hpos := W.count_pos hf
  have hi0 (i : Fin W.count) (hi : i.val = 0) : nativeMorseIndex E f (W.point i) = 0 := by
    have he : i = ⟨0, hpos⟩ := Fin.ext hi
    rw [he]
    exact (nativeMorseIndex_eq_chart (S.data (W.first hpos)).chart).trans
      (W.first_index_zero hf hpos)
  have hi2 (i : Fin W.count) (hi : 0 < i.val) (hir : i.val ≤ r) :
      nativeMorseIndex E f (W.point i) = 2 :=
    (nativeMorseIndex_eq_chart (S.data (W.point i)).chart).trans (htwo i hi hir)
  have hi3 (i : Fin W.count) (hri : r < i.val) (hin : i.val ≤ r + n) :
      nativeMorseIndex E f (W.point i) = 3 :=
    (nativeMorseIndex_eq_chart (S.data (W.point i)).chart).trans (hthree i hri hin)
  have hi4 (i : Fin W.count) (hin : r + n < i.val) :
      4 ≤ nativeMorseIndex E f (W.point i) := by
    rw [nativeMorseIndex_eq_chart (S.data (W.point i)).chart]
    exact hafter i hin
  constructor
  · intro z hz
    obtain ⟨i, rfl⟩ := W.point.surjective z
    have hiz : i.val ≠ 0 := by
      intro hi
      have hh := hi0 i hi
      omega
    have hri : r < i.val := by
      by_contra hnot
      have hh := hi2 i (by omega) (le_of_not_gt hnot)
      omega
    have hin : i.val ≤ r + n := by
      by_contra hnot
      have hh := hi4 i (lt_of_not_ge hnot)
      omega
    refine ⟨⟨i.val - (r + 1), by omega⟩, ?_⟩
    apply congrArg W.point
    apply Fin.ext
    change r + (i.val - (r + 1)) + 1 = i.val
    omega
  · intro z hz
    obtain ⟨i, rfl⟩ := W.point.surjective z
    have hir : i.val ≤ r := by
      by_contra hnot
      by_cases hin : i.val ≤ r + n
      · have hh := hi3 i (lt_of_not_ge hnot) hin
        omega
      · have hh := hi4 i (lt_of_not_ge hin)
        omega
    exact (W.point_strictMono.monotone (show i ≤ ⟨r, by omega⟩ from hir)).trans_lt
      (W.value_lt_upper _)

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
