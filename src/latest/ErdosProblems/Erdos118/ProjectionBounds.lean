import ErdosProblems.Erdos118.LabelOrigins

/-! The actual annotation projections inherit the proved command bounds. -/

namespace Erdos118.ProjectionBounds

open Negative Negative.Exact LabelledExtensions LabelledFrames LabelCoarsening

theorem body_label_pairwise (S : Stem) (i : ℕ) (hi : i < S.bodyLabels.length) :
    S.bodyLabels[i].Pairwise (· < ·) := by
  have hi' : i < S.done.length := by simpa [Stem.bodyLabels] using hi
  have hflat := (List.pairwise_cons.mp (List.pairwise_append.mp S.increasing).2.1).2
  have hb := (List.pairwise_flatMap.mp hflat).1 S.done[i] (List.getElem_mem hi')
  simpa only [Stem.bodyLabels, List.getElem_map] using (List.pairwise_append.mp hb).1

theorem projection_root_sublist {S U : Stem} {hS : S.done.length = S.root}
    {hU : U.done.length = U.root} {ys : List ℕ} (A : Projection S hS ys U hU) :
    U.rootLabel.Sublist S.rootLabel := by
  apply List.sublist_of_subperm_of_pairwise _ U.label_pairwise S.label_pairwise
  apply List.subperm_of_subset U.label_pairwise.nodup
  intro x hx
  obtain ⟨P, y, hy, hp, hcut, he⟩ := A.rootUsed x hx
  simpa only [he] using selected_root_mem P S hS hcut.labels

theorem projection_body_sublist {S U : Stem} {hS : S.done.length = S.root}
    {hU : U.done.length = U.root} {ys : List ℕ} (A : Projection S hS ys U hU)
    (i : ℕ) (hiU : i < U.bodyLabels.length) (hiS : i < S.bodyLabels.length) :
    U.bodyLabels[i].Sublist S.bodyLabels[i] := by
  have hUinc := body_label_pairwise U i hiU
  apply List.sublist_of_subperm_of_pairwise _ hUinc (body_label_pairwise S i hiS)
  apply List.subperm_of_subset hUinc.nodup
  intro x hx
  obtain ⟨P, y, hy, hp, hcut, hi, hxP⟩ := A.bodyUsed i hiU x hx
  obtain ⟨_, hmem⟩ := selected_body_mem P S hS hcut.labels
  simpa only [hi, hxP] using hmem

theorem projection_root_command {K L : Set ℕ} (hL : L.Infinite) (hLK : L ⊆ K)
    (b : ℕ) (hb : b ∈ K) (hpos : 1 ≤ b) (htail : ∀ x ∈ L, b < x)
    (s : G2) {U : Stem} {hU : U.done.length = U.root} {ys : List ℕ}
    (A : Projection (LabelledRealization.output hL s).stem
      (LabelledRealization.output hL s).full ys U hU) :
    ∃ q ∈ K, U.rootLabel.length ≤ q ∧ ∀ x ∈ U.rootLabel, q < x :=
  LabelOrigins.output_root_projected_command hL hLK b hb hpos htail s U.rootLabel
    (projection_root_sublist A)

theorem projection_body_command {L : Set ℕ} (hL : L.Infinite) (s : G2)
    {U : Stem} {hU : U.done.length = U.root} {ys : List ℕ}
    (A : Projection (LabelledRealization.output hL s).stem
      (LabelledRealization.output hL s).full ys U hU)
    (i : ℕ) (hiU : i < U.bodyLabels.length) (hne : U.bodyLabels[i] ≠ []) :
    U.bodyLabels[i].length - 1 = 0 ∨
      ∃ q ∈ L, U.bodyLabels[i].length - 1 ≤ q ∧ ∀ x ∈ U.bodyLabels[i], q < x := by
  have hiS : i < (LabelledRealization.output hL s).stem.bodyLabels.length := by
    simpa only [Stem.bodyLabels, List.length_map, hU,
      (LabelledRealization.output hL s).full, A.root] using hiU
  exact LabelOrigins.output_body_projected_command hL s _ _ (List.getElem_mem hiS)
    (projection_body_sublist A i hiU hiS) hne

end Erdos118.ProjectionBounds
