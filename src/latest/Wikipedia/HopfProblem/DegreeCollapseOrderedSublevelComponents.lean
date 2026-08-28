import Wikipedia.HopfProblem.DegreeCollapseNativeMorseHomologyZero
import Wikipedia.SmoothSixDPoincare.MorseSurgeryEndpoints
import Wikipedia.SmoothSixDPoincare.RegularSublevelDeformation

/-!
# Connectedness descends through the actual higher-index surgery tail

Starting with the whole connected manifold, reverse induction through the
actual ordered surgery windows proves connectedness after the last handle
of index at most one. Regular bands and every index-at-least-two attachment
are constructed on the original sublevels.
-/

noncomputable section

open Set Function ContinuousMap
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open Wikipedia.SmoothSixDPoincare ManifoldMorse

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PathConnectedSpace M]
  {f : M → ℝ} (S : SurgeryWindows E f)

theorem ordered_upper_pathConnected_of_later_transfers
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (i : Fin S.count)
    (htransfer : ∀ j : Fin S.count, i.val < j.val →
      PathConnectedSpace {x : M // f x ≤ S.upper (S.point j)} →
        PathConnectedSpace {x : M // f x ≤ S.lower (S.point j)}) :
    PathConnectedSpace {x : M // f x ≤ S.upper (S.point i)} := by
  have hall : ∀ k : ℕ, ∀ i : Fin S.count, S.count - 1 - i.val = k →
      (∀ j : Fin S.count, i.val < j.val →
        PathConnectedSpace {x : M // f x ≤ S.upper (S.point j)} →
          PathConnectedSpace {x : M // f x ≤ S.lower (S.point j)}) →
      PathConnectedSpace {x : M // f x ≤ S.upper (S.point i)} := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro i hki hindices
      have hpos : 0 < S.count := (Nat.zero_le i.val).trans_lt i.isLt
      by_cases hlast : i.val = S.count - 1
      · have hi : S.point i = S.last hpos := congrArg S.point (Fin.ext hlast)
        have hset : {x : M | f x ≤ S.upper (S.point i)} = univ := by
          rw [hi]
          exact S.last_upper_univ hf hpos
        have hp : IsPathConnected {x : M | f x ≤ S.upper (S.point i)} :=
          hset.symm ▸ isPathConnected_univ
        exact isPathConnected_iff_pathConnectedSpace.mp hp
      · have hjlt : i.val + 1 < S.count := by omega
        let j : Fin S.count := ⟨i.val + 1, hjlt⟩
        have hjmeasure : S.count - 1 - j.val < k := by
          dsimp [j]
          omega
        have hupper : PathConnectedSpace {x : M // f x ≤ S.upper (S.point j)} :=
          ih _ hjmeasure j rfl (fun q hq => hindices q (by dsimp [j] at hq; omega))
        let : PathConnectedSpace {x : M // f x ≤ S.lower (S.point j)} :=
          hindices j (by dsimp [j]; omega) hupper
        have hij : i < j := by change i.val < i.val + 1; omega
        obtain ⟨e, -⟩ := FlowConstruction.exists_regularSublevelHomotopyEquiv hf
          (S.ordered_windows i j hij).le (S.consecutive_regular i j rfl)
        exact pathConnectedSpace_of_homotopyEquiv e
  exact hall _ i rfl htransfer

theorem ordered_upper_pathConnected_of_later_indices
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (i : Fin S.count)
    (hindex : ∀ j : Fin S.count, i.val < j.val →
      2 ≤ Module.finrank ℝ (S.data (S.point j)).chart.NegativeCoordinates) :
    PathConnectedSpace {x : M // f x ≤ S.upper (S.point i)} := by
  apply ordered_upper_pathConnected_of_later_transfers S hf i
  intro j hij hupper
  let : PathConnectedSpace
      {x : M // f x ≤ f (S.point j) + (S.data (S.point j)).radius ^ 2} := hupper
  exact native_lower_pathConnected_of_upper (S.data (S.point j)) hf.continuous (hindex j hij)

theorem ordered_lower_pathConnected_of_later_indices
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (i : Fin S.count)
    (hindex : ∀ j : Fin S.count, i.val ≤ j.val →
      2 ≤ Module.finrank ℝ (S.data (S.point j)).chart.NegativeCoordinates) :
    PathConnectedSpace {x : M // f x ≤ S.lower (S.point i)} := by
  let : PathConnectedSpace
      {x : M // f x ≤ f (S.point i) + (S.data (S.point i)).radius ^ 2} :=
    ordered_upper_pathConnected_of_later_indices S hf i
    (fun j hij => hindex j hij.le)
  exact native_lower_pathConnected_of_upper (S.data (S.point i)) hf.continuous
    (hindex i le_rfl)

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
