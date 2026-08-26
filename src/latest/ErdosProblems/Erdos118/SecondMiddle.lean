import ErdosProblems.Erdos118.FineBody

/-! The common two last source games, with the entire right ordinary
suffix above an arbitrary previously saved third-game bound. -/

namespace Erdos118.SecondMiddle

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns PreparedRelays BoundaryRelays FreshCheckpoints

structure LastPair {H : Set ℕ} {B : SimpleGraph G} {O : LateOpening.Opening H B}
    (D : FirstMiddle.Diagram O) (d : ℕ) where
  oldLeft : Pending
  fineLeft : Pending
  right : Pending
  oldLast : oldLeft.roots = [] ∧ oldLeft.leaves = []
  fineLast : fineLeft.roots = [] ∧ fineLeft.leaves = []
  rightLast : right.roots = [] ∧ right.leaves = []
  rightBody : SameBody O.insertedRight right
  rightExact : ExactSlots.Exact (.leaf right)
  sameOrdinary : oldLeft.position.ordinary = fineLeft.position.ordinary
  suffix : List ℕ
  ordinary : right.position.ordinary = O.insertedRight.position.ordinary ++ suffix
  fresh : ∀ x ∈ suffix, x ∈ H ∧ d < x
  oldBlue : RamseyGame.Outcome H
    (GraphPayoff.game B .inside (.leaf oldLeft, .leaf D.right)) true
  fineBlue : RamseyGame.Outcome H
    (GraphPayoff.game B .inside (.leaf fineLeft, .leaf right)) true

theorem exists_last_pair {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    {O : LateOpening.Opening H B} (D : FirstMiddle.Diagram O) (d : ℕ) :
    Nonempty (LastPair D d) := by
  obtain ⟨CS⟩ := SelectedLeafReplay.exists_certificate hH B .inside false
    D.left (.leaf D.right) D.lastIndex [] D.leftLeaf D.handoff
  let e := max CS.bound d
  obtain ⟨F⟩ := FineBody.exists_response hH B D e
  let P := applyBody O.insertedBody F.setup
  obtain ⟨P₂, U₂, k, hPP, hUU, hPL, hUL, hP₂, hU₂, _, _, hh₂, hf₂⟩ :=
    MiddleRun.endpoint hH Set.Subset.rfl B e P O.insertedRight F.roots
      O.insertedRightLast F.leaves F.exactSlots O.insertedManaged.exact F.blue
      (fun _ ↦ F.handoff)
  obtain ⟨vS, vU, hvS, hvU, hfS, hfU⟩ := hf₂
  have hk : k = D.lastIndex := by
    calc
      k = P₂.position.label.getLastD 0 := (ExactSlots.pending_next_last P₂ hP₂ hPL).symm
      _ = F.setup.position.label.getLastD 0 := congrArg (fun L ↦ L.getLastD 0) hPP.2.2.2.1
      _ = D.reserve.label.getLastD 0 := congrArg (fun L ↦ L.getLastD 0) F.label
      _ = D.left.position.label.getLastD 0 := D.reserve.sameLast
      _ = D.lastIndex := ExactSlots.pending_next_last D.left D.leftExact D.leftLeaf
  obtain ⟨A, _, hb₃, _, hf₃⟩ := SelectedLeafResponses.respond hH Set.Subset.rfl
    B .inside false P₂ (.leaf U₂) k [] hPL hh₂ CS.bound
  let S₁ := LeafResponses.toPending P₂ k [] hPL A
  have hslots := P₂.leafSlots.bounded k (hPL ▸ List.mem_singleton_self _)
  have hSord : S₁.position.ordinary = D.left.position.ordinary ++
      (F.suffix ++ vS ++ A.newWord) := by
    change (LeafResponses.position A hslots.1 hslots.2.1).ordinary = _
    rw [LeafResponses.position_ordinary]
    change P₂.position.ordinary = P.position.ordinary ++ vS at hvS
    rw [hvS]
    change (F.setup.position.ordinary ++ vS) ++ A.newWord = _
    simp only [F.ordinary, List.append_assoc]
  have hstem : S₁.position.stem.ordinary = D.left.position.stem.ordinary := by
    change P₂.position.stem.ordinary = D.left.position.stem.ordinary
    rw [hPP.2.1]
    change F.setup.position.stem.ordinary = D.left.position.stem.ordinary
    rw [F.setup.stem_eq, D.leftStem]
    exact O.sameOrdinary.symm
  have hmarker : S₁.position.size = D.left.position.size := hPP.2.2.1.trans F.marker
  have hcount : S₁.position.entries.length = D.lastIndex :=
    (LeafResponses.position_length A hslots.1 hslots.2.1).trans hk
  have hentries : S₁.position.entries = D.left.position.entries ++
      (F.suffix ++ vS ++ A.newWord) := by
    simp only [Position.ordinary, hstem, hmarker, List.append_assoc] at hSord
    have ht := List.append_cancel_left hSord
    have ht' : D.left.position.size :: S₁.position.entries = D.left.position.size ::
        (D.left.position.entries ++ (F.suffix ++ vS ++ A.newWord)) := by
      simpa only [List.cons_append, List.append_assoc] using ht
    exact (List.cons.inj ht').2
  have hfull : ∀ x ∈ F.suffix ++ vS ++ A.newWord, x ∈ H ∧ CS.bound < x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · rcases List.mem_append.mp hx with hx | hx
      · exact ⟨(F.fresh x hx).1, (le_max_left _ _).trans_lt (F.fresh x hx).2⟩
      · exact ⟨(hfS x hx).1, (le_max_left _ _).trans_lt (hfS x hx).2⟩
    · exact hf₃ x hx
  obtain ⟨RS⟩ := CS.fire D.leftExact S₁.position hstem hmarker hcount
    (F.suffix ++ vS ++ A.newWord) hentries
    (fun x hx ↦ (hfull x hx).1) (fun x hx ↦ (hfull x hx).2)
  exact ⟨{
    oldLeft := RS.target, fineLeft := S₁, right := U₂
    oldLast := ⟨RS.roots.trans D.leftRoot, RS.leaves⟩, fineLast := ⟨hPP.1, rfl⟩
    rightLast := ⟨hUU.1, hUL⟩, rightBody := hUU, rightExact := hU₂
    sameOrdinary := RS.ordinary, suffix := vU, ordinary := hvU
    fresh := fun x hx ↦ ⟨(hfU x hx).1, (le_max_right _ _).trans_lt (hfU x hx).2⟩
    oldBlue := RS.blue, fineBlue := hb₃ }⟩

end Erdos118.SecondMiddle
