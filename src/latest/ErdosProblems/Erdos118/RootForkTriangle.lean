import ErdosProblems.Erdos118.ReversedForks
import ErdosProblems.Erdos118.OverlapFinish
import ErdosProblems.Erdos118.FreshBodyCheckpoint
import ErdosProblems.Erdos118.CurrentBody

/-!
The reversed inside forks yield a triangle when the fine S word's last
selected body is the coarse S word's next selected body. The coarse target
may retain further root slots. Its body response is prepared before the
fine last-body marker, and the old U bound precedes both continuation runs.
-/

namespace Erdos118.RootForkTriangle

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns

theorem triangle {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (S₀ S₁ : Pending) (F : ReversedForks.Forks H B .inside S₀ S₁)
    (hS : S₀.position.ordinary = S₁.position.ordinary)
    (hS₁ : ExactSlots.Exact (.leaf S₁)) (hSL : S₀.leaves = [])
    (c : ℕ) (rest : List ℕ) (hnext : S₀.roots = c :: rest)
    (hlast : S₁.position.stem.rootLabel.getLastD 0 = c) :
    ∃ s t u : G, B.Adj s t ∧ B.Adj s u ∧ B.Adj t u := by
  have hcomp := JointMoves.ordinary_components S₀.position S₁.position hS
  have hslot := S₀.rootSlots.bounded c (hnext ▸ List.mem_cons_self ..)
  have hS₁R : S₁.roots ≠ [] := by
    intro he
    have h := ExactSlots.pending_last_root S₁ hS₁ he
    rw [hlast] at h
    have hc := hcomp.2.2.1
    omega
  have hTUright := InsideEndgame.last_left_rightBlue hH B F.T F.U
    F.tLast.1 F.tLast.2 F.blueTU
  obtain ⟨bU, hbU⟩ := OverlapFinish.right_extension_triangle hH B F.T F.U F.uLast hTUright
  obtain ⟨bS, hbS⟩ := JointMoves.stem_bound Set.Subset.rfl B .inside false
    S₀ (.leaf F.T₀) c rest hnext hSL F.leftST
  obtain ⟨D, Y, hDR, hrun, _, hcmdD, v, w, hSword, hYword, hv, hw⟩ :=
    FreshBodyCheckpoint.left_last hH Set.Subset.rfl B .inside (.leaf S₁) (.leaf F.U₀)
      hS₁R (max bS bU) F.blueSU
  have hD : ExactSlots.Exact (.body D) := ExactSlots.run_exact_left hrun hS₁
  have hDlabel : D.stem.rootLabel = S₁.position.stem.rootLabel :=
    Option.some.inj ((SkippedCuts.run_extensions hrun).1.labels.root
      S₁.position.stem.rootLabel rfl)
  have hDcount : D.stem.done.length = c - 1 := by
    have h := BoundaryRelays.body_last_root D hD hDR
    rw [hDlabel, hlast] at h
    omega
  have hDword : D.stem.ordinary = S₀.position.ordinary ++ v := by
    change D.stem.ordinary = S₁.position.ordinary ++ v at hSword
    rwa [← hS] at hSword
  have hDroot : D.stem.root = S₀.position.stem.root := by
    have he := congrArg (fun l : List ℕ ↦ l.headD 0) hDword
    simpa only [Stem.ordinary, Position.ordinary, List.cons_append, List.headD_cons] using he
  have hmore := (next_body_bounds S₀ c rest hnext).1
  obtain ⟨A, hAv, hAord⟩ := CompletionReplay.setup_of_literal_stem S₀.position D.stem (c - 1)
    hDroot hDcount hmore v hDword
  obtain ⟨_, _, hcmdE⟩ := hbS A (by
    rw [hAv]
    exact fun x hx ↦ ⟨(hv x hx).1, (le_max_left _ _).trans_lt (hv x hx).2⟩)
  let E := ofStem S₀ c rest hnext A
  obtain ⟨k, C, Z, _, hb₂, hh₂, _⟩ := BodyReplay.prepare hH Set.Subset.rfl B .inside
    false false D E Y (.leaf F.T₀) hD hDR hAord hcmdD hcmdE bU
  let S₂ := applyBody D C
  obtain ⟨S₃, Y₃, hsame, hS₃L, hr₂, hb₃, hh₃, _, w₂, _, hY₃word, _, hw₂⟩ :=
    CurrentBody.last_on hH Set.Subset.rfl B .inside false S₂ Y bU hb₂ (fun _ ↦ hh₂)
  have hS₃R : S₃.roots = [] := hsame.roots.trans hDR
  have hUfull : Y₃.ordinary = F.U.position.ordinary ++ (w ++ w₂) := by
    rw [hY₃word, hYword]
    change (F.U₀.position.ordinary ++ w) ++ w₂ = _
    rw [F.uOrdinary, List.append_assoc]
  have hY₃ne : Y₃ ≠ .initial := by
    have hmem : F.U.position.stem.root ∈ Y₃.ordinary := by
      rw [hUfull]
      exact List.mem_append_left _ (by simp [Position.ordinary, Stem.ordinary])
    intro he
    simp [he, State.ordinary] at hmem
  obtain ⟨U', hY₃, _, _⟩ := InsideEndgame.last_left_right_command hH B S₃ Y₃
    hS₃R hS₃L hY₃ne hh₃
  subst Y₃
  obtain ⟨Z₃, _, _⟩ := BodyReplay.carry_of_run Z false S₃ Y (.leaf U') Set.Subset.rfl
    (GraphPayoff.payoff B .inside) hr₂
  obtain ⟨hSord, hST, _⟩ := BodyReplay.fire hH Z₃ hS₃L
  have huf : ∀ x ∈ w ++ w₂, x ∈ H ∧ bU < x := by
    intro x hx
    exact (List.mem_append.mp hx).elim
      (fun hx ↦ ⟨(hw x hx).1, (le_max_right _ _).trans_lt (hw x hx).2⟩) (hw₂ x)
  exact hbU (applyBody E (Z₃.setup hS₃L)) S₃ F.T₀ U' (w ++ w₂)
    hS₃R hS₃L hSord F.tOrdinary hUfull huf hST hb₃

end Erdos118.RootForkTriangle
