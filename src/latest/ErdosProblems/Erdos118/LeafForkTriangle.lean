import ErdosProblems.Erdos118.ReversedForks
import ErdosProblems.Erdos118.OverlapFinish
import ErdosProblems.Erdos118.CurrentBody

/-!
The reversed inside forks yield a triangle when the fine S word's final
selected leaf is the coarse S word's next selected leaf. Both old bounds
are fixed before the new SU continuation. The initial S overlap is explicit.
-/

namespace Erdos118.LeafForkTriangle

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns

theorem triangle {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (S₀ S₁ : Pending) (F : ReversedForks.Forks H B .inside S₀ S₁)
    (hS : S₀.position.ordinary = S₁.position.ordinary)
    (hS₁ : ExactSlots.Exact (.leaf S₁)) (hSR : S₁.roots = [])
    (j : ℕ) (rest : List ℕ) (hnext : S₀.leaves = j :: rest)
    (hlast : S₁.position.label.getLastD 0 = j) :
    ∃ s t u : G, B.Adj s t ∧ B.Adj s u ∧ B.Adj t u := by
  have hTUright := InsideEndgame.last_left_rightBlue hH B F.T F.U
    F.tLast.1 F.tLast.2 F.blueTU
  obtain ⟨bU, hbU⟩ := OverlapFinish.right_extension_triangle hH B F.T F.U F.uLast hTUright
  obtain ⟨bS, hbS⟩ := JointMoves.leaf_bound hH Set.Subset.rfl B .inside false
    S₀ (.leaf F.T₀) j rest hnext F.leftST
  have hready : S₁.leaves = [] → PreparedRelays.OtherBlue H B .inside false
      (.leaf S₁) (.leaf F.U₀) := by
    intro hL
    exact InsideEndgame.last_left_rightBlue hH B S₁ F.U₀ hSR hL F.blueSU
  obtain ⟨S', Y, hsame, hSL, hrun, hblue, hhand, v, w, hSword, hYword, hv, hw⟩ :=
    CurrentBody.last_on hH Set.Subset.rfl B .inside false S₁ (.leaf F.U₀)
      (max bS bU) F.blueSU hready
  have hS'R : S'.roots = [] := hsame.roots.trans hSR
  have hYne : Y ≠ .initial := by
    have hmem : F.U₀.position.stem.root ∈ Y.ordinary := by
      rw [hYword]
      exact List.mem_append_left _ (by simp [State.ordinary, Position.ordinary, Stem.ordinary])
    intro he
    simp [he, State.ordinary] at hmem
  obtain ⟨U', hY, hUR, hUL⟩ := InsideEndgame.last_left_right_command hH B S' Y hS'R hSL hYne hhand
  subst Y
  have hS'exact : ExactSlots.Exact (.leaf S') := ExactSlots.run_exact_left hrun hS₁
  have hS'len : S'.position.entries.length = j := by
    have he := ExactSlots.pending_last_leaf S' hS'exact hSL
    rw [hsame.label, hlast] at he
    exact he.symm
  have hcomp := JointMoves.ordinary_components S₀.position S₁.position hS
  have hstem : S'.position.stem.ordinary = S₀.position.stem.ordinary :=
    (congrArg Stem.ordinary hsame.stem).trans hcomp.2.1.symm
  have hsize : S'.position.size = S₀.position.size := hsame.size.trans hcomp.2.2.2.1.symm
  have hSword₀ : S'.position.ordinary = S₀.position.ordinary ++ v := by
    rw [hSword, ← hS]
  have hentries : S'.position.entries = S₀.position.entries ++ v := by
    have he : S₀.position.size :: S'.position.entries =
        S₀.position.size :: (S₀.position.entries ++ v) := by
      apply List.append_cancel_left (as := S₀.position.stem.ordinary)
      simpa only [Position.ordinary, hstem, hsize, List.cons_append, List.append_assoc]
        using hSword₀
    exact (List.cons.inj he).2
  obtain ⟨A, hAv, hAword⟩ := LeafReplay.setup_of_position S₀.position S'.position j
    hstem hsize hS'len v hentries
  obtain ⟨_, hST, _⟩ := hbS A (by
    rw [hAv]
    exact fun x hx ↦ ⟨(hv x hx).1, (le_max_left _ _).trans_lt (hv x hx).2⟩)
  let S₀' := LeafResponses.toPending S₀ j rest hnext A
  have hslot := S₀.leafSlots.bounded j (hnext ▸ List.mem_cons_self ..)
  have hS'ord : S₀'.position.ordinary = S'.position.ordinary :=
    (LeafResponses.position_ordinary A hslot.1 hslot.2.1).trans hAword
  have hUword : U'.position.ordinary = F.U.position.ordinary ++ w := by
    change U'.position.ordinary = F.U₀.position.ordinary ++ w at hYword
    rwa [F.uOrdinary] at hYword
  exact hbU S₀' S' F.T₀ U' w hS'R hSL hS'ord F.tOrdinary hUword
    (fun x hx ↦ ⟨(hw x hx).1, (le_max_right _ _).trans_lt (hw x hx).2⟩) hST hblue

end Erdos118.LeafForkTriangle
