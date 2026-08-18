/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.GreedyDyadicRange
import ErdosProblems.Erdos186.CFP.GreedySourceIntervalLowPrefix
import ErdosProblems.Erdos186.CFP.RandomGreedyDenseWitness

/-!
# Uniform terminal crossings for populated random colours

Each colour keeps its own approximation rank, but the interval estimate for
the low prefix and the stable dyadic ratio are uniform.  Hence one numerical
inequality forces every populated colour to reach the same terminal
threshold strictly before the common cap.  No first-crossing or
H-approximation callback remains in the conclusion.
-/

namespace Erdos186.CFP.RandomPartition

noncomputable section

/-- Reaching a threshold one step before the permitted endpoint makes the
canonical first crossing strict at that endpoint. -/
theorem firstCrossing_lt_of_reached_before_endpoint
    {f : ℕ → ℕ} {cap threshold : ℕ}
    (hcap : 0 < cap) (hreached : threshold ≤ f (cap - 1)) :
    Greedy.firstCrossing f cap threshold < cap := by
  have hle : Greedy.firstCrossing f cap threshold ≤ cap - 1 := by
    apply Nat.find_min'
    exact Or.inr hreached
  omega

/-- Strict terminal crossing in every nonzero colour.  The colour-dependent
approximation rank is chosen internally from the exact dyadic source range.
The common terminal level is allowed but not assumed to be a first-crossing
level; only the canonical crossing inequality is concluded. -/
theorem dyadicBinStart_lt_cap_of_populated_dyadicRange
    {source W A : Finset ℤ}
    {q cap D n low terminal propernessDenominator : ℕ}
    (c : {a // a ∈ A} → Fin (q + 1))
    (hfamily : PreprocessingBilu.DyadicRangeSourceHApproximationFamily
      source low terminal D 1
        (PreprocessingBilu.preprocessingScaleDen propernessDenominator))
    (hzeroA : 0 ∉ A) (hsource : insert 0 A ⊆ source)
    (hAW : insert 0 A ⊆ W)
    (hpopulated : ∀ i, cap < (integerColorClass A c i).card)
    (hstable : ∀ i, Stability.WeaklyStableFor
      (anchoredColorClass A c i) (Stability.minimalBoxFamily W)
        cap D (n ^ 2))
    (hn : 0 < n) (hlowTerminal : low < terminal)
    (hfoldn : ∀ h, low ≤ h → h ≤ terminal → 2 ^ h ≤ n)
    (hinterval : ∀ z ∈ W, 0 ≤ z ∧ z < (n : ℤ))
    (hlarge : ∀ h, low ≤ h → h ≤ terminal →
      PreprocessingBilu.preprocessingIndexBound D propernessDenominator ≤
        2 ^ h)
    (hcrossNumeric :
      2 ^ (low + 1) * (Nat.log 2 (2 ^ low * n + 1) + 1) +
          16 * Greedy.stableDyadicRatio D
            (PreprocessingBilu.preprocessingScaleDen propernessDenominator) *
            2 ^ terminal + 1 < cap) :
    ∀ i, Greedy.dyadicBinStart (integerColorClass A c i) cap cap terminal <
      cap := by
  intro i
  let S := integerColorClass A c i
  let steps := cap - 1
  have hzeroS : 0 ∉ S := by
    intro hzero
    exact hzeroA (integerColorClass_subset A c i hzero)
  have hSW : insert 0 S ⊆ W := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hAW (by simp)
    · exact hAW (Finset.mem_insert_of_mem
        (integerColorClass_subset A c i hz))
  have hSSource : insert 0 S ⊆ source := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hsource (by simp)
    · exact hsource (Finset.mem_insert_of_mem
        (integerColorClass_subset A c i hz))
  have hstepsCard : steps ≤ S.card := by
    exact (Nat.sub_le cap 1).trans (hpopulated i).le
  have hstepsBudget : steps ≤ cap := Nat.sub_le _ _
  have hSnonempty : S.Nonempty := Finset.card_pos.mp (by
    have := hpopulated i
    omega)
  have hstableMinimal : Stability.WeaklyStableMinimalFor
      (insert 0 S) cap D n := by
    apply Greedy.weaklyStableMinimalFor_of_fixed_minimalBox hSW
    simpa only [S, anchoredColorClass, integerColorClass] using
      (hstable i)
  have hratio : ∀ h, low ≤ h → h < terminal →
      Greedy.positiveDyadicThreshold S cap (h + 1) ≤
        Greedy.stableDyadicRatio D
            (PreprocessingBilu.preprocessingScaleDen propernessDenominator) *
          Greedy.positiveDyadicThreshold S cap h := by
    intro h hlow hhigh
    have hrange := Greedy.positiveDyadicThreshold_succ_le_of_dyadicRange
      hfamily hlow hhigh.le hSSource hzeroS hSnonempty (hpopulated i)
      hstableMinimal (fun z hz ↦ hinterval z (hSW hz))
      (hfoldn h hlow hhigh.le) (hlarge h hlow hhigh.le)
    simpa only [Greedy.stableDyadicRatio] using hrange
  have hprefix : Greedy.dyadicBinStart S cap steps low ≤
      2 ^ (low + 1) * (Nat.log 2 (2 ^ low * n + 1) + 1) := by
    apply Greedy.dyadicBinStart_le_sourceIntervalLog hn
      (fun z hz ↦ ?_) hstepsCard hstepsBudget
    exact Finset.mem_Icc.mpr ⟨(hinterval z (hSW hz)).1, by
      have := (hinterval z (hSW hz)).2
      omega⟩
  have hactive : Greedy.dyadicBinStart S cap steps low +
      16 * Greedy.stableDyadicRatio D
          (PreprocessingBilu.preprocessingScaleDen propernessDenominator) *
        2 ^ terminal < steps := by
    let active := 16 * Greedy.stableDyadicRatio D
      (PreprocessingBilu.preprocessingScaleDen propernessDenominator) *
        2 ^ terminal
    have hbound : Greedy.dyadicBinStart S cap steps low + active ≤
        2 ^ (low + 1) * (Nat.log 2 (2 ^ low * n + 1) + 1) + active :=
      Nat.add_le_add_right hprefix active
    have hstrict :
        2 ^ (low + 1) * (Nat.log 2 (2 ^ low * n + 1) + 1) + active <
          cap - 1 := by
      dsimp only [active]
      omega
    exact hbound.trans_lt hstrict
  have hreached : Greedy.positiveDyadicThreshold S cap terminal ≤
      (Greedy.sums S steps).card :=
    Greedy.positiveDyadicThreshold_le_card_sums_of_shiftedPrefix_lt
      hlowTerminal hstepsCard hstepsBudget hratio hactive
  exact firstCrossing_lt_of_reached_before_endpoint (by omega) hreached

end

end Erdos186.CFP.RandomPartition

#print axioms
  Erdos186.CFP.RandomPartition.dyadicBinStart_lt_cap_of_populated_dyadicRange
