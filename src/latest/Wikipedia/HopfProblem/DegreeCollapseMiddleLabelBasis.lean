import Wikipedia.HopfProblem.DegreeCollapseSmoothMiddleFamilies
import Wikipedia.HopfProblem.DegreeCollapseMiddleHomologyFree

/-!
# The number of actual middle labels is the integral H3 rank

Use the same separated native Morse system, not another independently chosen
function. Its ordered middle block labels every actual index-three critical
point exactly once. The proved native collapse-coordinate basis therefore
has exactly as many coordinates as this actual label type.
-/

noncomputable section

open Set Function Metric Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.MiddleDuality.SeparatedSystem

open SingularMayerVietoris

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [Nonempty M] (D : SeparatedSystem E M)

theorem count_zero_of_other_index (k : ℕ) (hk0 : k ≠ 0) (hk3 : k ≠ 3) (hk6 : k ≠ 6) :
    nativeMorseCount E D.function k = 0 := by
  have he : {z : M | z ∈ criticalPoints E D.function ∧ nativeMorseIndex E D.function z = k} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro z ⟨hz, hi⟩
    rcases D.indices ⟨z, hz⟩ with h | h | h
    · exact hk0 (hi.symm.trans h)
    · exact hk3 (hi.symm.trans h)
    · exact hk6 (hi.symm.trans h)
  change {z : M | z ∈ criticalPoints E D.function ∧ nativeMorseIndex E D.function z = k}.ncard = 0
  rw [he, Set.ncard_empty]

theorem exists_middle_label_basis :
    ∃ n : ℕ, Nonempty (Fin n ≃ D.MiddleLabel) ∧
      Nonempty ((Fin n → ℤ) ≃ₗ[ℤ] SingularHomology M 3) := by
  let S := D.windows
  have hone := D.count_zero_of_other_index 1 (by decide) (by decide) (by decide)
  have htwo := D.count_zero_of_other_index 2 (by decide) (by decide) (by decide)
  have hfour := D.count_zero_of_other_index 4 (by decide) (by decide) (by decide)
  have hfive := D.count_zero_of_other_index 5 (by decide) (by decide) (by decide)
  obtain ⟨r, n, hprefix, hn, hthree, -, hafter⟩ :=
    exists_middle_index_blocks S.toSurgeryWindows D.smooth D.dimension D.ordered D.minimum_count hone
  obtain ⟨hr, -⟩ := native_middle_block_counts S.toSurgeryWindows D.smooth r n hprefix hn hthree hafter
  have hr0 : r = 0 := hr.symm.trans htwo
  clear hr
  subst r
  have hcount : n + 2 = S.toSurgeryWindows.count := by
    simpa only [Nat.zero_add] using middle_blocks_complete_of_no_four_five
      S.toSurgeryWindows D.smooth D.dimension 0 n hprefix hn hthree hafter D.maximum_count hfour hfive
  let p := nativeMiddleBlockPoint S 0 n hn
  have hp (j : Fin n) : nativeMorseIndex E D.function (p j) = 3 :=
    (nativeMorseIndex_eq_chart (S.data (p j)).chart).trans
      (hthree ⟨0 + j.val + 1, by omega⟩ (by simp) (by dsimp; omega))
  let label : Fin n → D.MiddleLabel := fun j => ⟨p j, hp j⟩
  have hlabel : Bijective label := by
    constructor
    · intro i j hij
      have he := S.toSurgeryWindows.point.injective (congrArg Subtype.val hij)
      have hv := congrArg Fin.val he
      apply Fin.ext
      change 0 + i.val + 1 = 0 + j.val + 1 at hv
      omega
    · intro q
      obtain ⟨j, hj⟩ := middle_label_surjective S D.smooth D.dimension n hn hcount q.val q.property
      exact ⟨j, Subtype.ext hj⟩
  exact ⟨n, ⟨Equiv.ofBijective label hlabel⟩,
    ⟨MiddleBasis.wholeBasis S.toSurgeryWindows D.smooth D.dimension n (by omega) hthree hcount⟩⟩

theorem middle_homology_finrank :
    Module.finrank ℤ (SingularHomology M 3) = Nat.card D.MiddleLabel := by
  obtain ⟨n, ⟨e⟩, ⟨b⟩⟩ := D.exists_middle_label_basis
  calc
    Module.finrank ℤ (SingularHomology M 3) = n := by
      simpa only [Module.finrank_fin_fun] using b.finrank_eq.symm
    _ = Nat.card D.MiddleLabel := by simpa only [Nat.card_fin] using Nat.card_congr e

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.MiddleDuality.SeparatedSystem
