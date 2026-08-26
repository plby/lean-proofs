import ErdosProblems.Erdos118.AlignedAllBodies
import ErdosProblems.Erdos118.MiddleRun
import ErdosProblems.Erdos118.SelectedLeafReplay
import ErdosProblems.Erdos118.InsideCompletion

/-! The two actual middle runs for the positive aligned parameters.
All reused prefixes meet their original bounds, while new suffixes
meet bounds saved only after the first middle run. -/

namespace Erdos118.AlignedPositiveEnding

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns PreparedRelays BoundaryRelays AlignedLastOpening AlignedFirstBodies
open AlignedBridgeDiagram AlignedAllBodies

private theorem entries_of_ordinary (P Q : Position) (v : List ℕ)
    (hs : Q.stem.ordinary = P.stem.ordinary) (hm : Q.size = P.size)
    (hv : Q.ordinary = P.ordinary ++ v) : Q.entries = P.entries ++ v := by
  have he : P.size :: Q.entries = P.size :: (P.entries ++ v) := by
    apply List.append_cancel_left (as := P.stem.ordinary)
    simpa only [Position.ordinary, hs, hm, List.cons_append, List.append_assoc] using hv
  exact (List.cons.inj he).2

theorem triangle {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    {O : Opening H B} {F : Pair O} {D : Diagram O F} {T : TPair D}
    (C : UCertificates D T) (U : UPair C) (ht : 0 < D.lowerCertificate.size) :
    ∃ s t u : G, B.Adj s t ∧ B.Adj s u ∧ B.Adj t u := by
  have hd : 0 < C.lowerCertificate.size := Nat.pos_of_ne_zero
    (fun he ↦ (Nat.ne_of_gt ht) (C.lowerZero.mpr he))
  have hTupper := (T.exactSlots D.lowerExact D.upperExact).2
  have hUupper := (U.exactSlots C.lowerExact C.upperExact).2
  obtain ⟨tr, hTnext⟩ := T.next_upper D.upperExact ht
  obtain ⟨CT⟩ := SelectedLeafReplay.exists_certificate hH B .inside false T.upper (.leaf U.upper)
    (T.lower.position.label.getLastD 0) tr hTnext U.upperHandoff
  obtain ⟨j, sr, hSnext⟩ := List.exists_cons_of_ne_nil F.leaves_nonempty.2
  obtain ⟨CS₁⟩ := SelectedLeafReplay.exists_certificate hH B .inside false F.insertedLeft
    (.leaf U.lower) j sr hSnext U.lowerHandoff
  have hS₀len : 1 < F.oldLeft.leaves.length := by
    change 1 < F.oldSetup.position.label.tail.length
    rw [List.length_tail, F.oldSetup.label_length, D.lowerSize]
    omega
  have hS₁len : 1 < F.insertedLeft.leaves.length := by
    change 1 < F.insertedSetup.position.label.tail.length
    rw [List.length_tail, F.insertedSetup.label_length, C.lowerSize]
    omega
  have hsr : sr ≠ [] := by intro he; rw [hSnext, he] at hS₁len; simp at hS₁len
  obtain ⟨S₀, T₀, a, hSS, hTT, hSL, hTL, hS₀, hT₀, _, _, hh₀, vS, vT,
      hvS, hvT, hfS, hfT⟩ := MiddleRun.endpoint hH Set.Subset.rfl B (max CT.bound CS₁.bound)
    F.oldLeft T.lower F.roots_nil.1 D.lowerLast F.leaves_nonempty.1 F.exactSlots.1
    (T.exactSlots D.lowerExact D.upperExact).1 T.lowerBlue (by
      rintro ⟨k, hk⟩
      rw [hk] at hS₀len
      simp at hS₀len)
  obtain ⟨RT⟩ := CT.fire_last T.lower T₀ hTupper T.sameOrdinary.symm
    (congrArg List.length T.sameEntries.symm) hTT hT₀ hTL vT hvT
    (fun x hx ↦ (hfT x hx).1) (fun x hx ↦ (le_max_left _ _).trans_lt (hfT x hx).2)
  obtain ⟨ur, hUnext⟩ := U.next_upper C.upperExact hd
  obtain ⟨CU⟩ := SelectedLeafReplay.exists_certificate hH B .inside true U.upper (.leaf RT.target)
    (U.lower.position.label.getLastD 0) ur hUnext RT.handoff
  obtain ⟨CS₀⟩ := SelectedLeafReplay.exists_certificate hH B .inside false S₀ (.leaf T₀)
    a [] hSL hh₀
  let M := max CS₀.bound CU.bound
  have ha : a = F.oldLeft.position.label.getLastD 0 :=
    (ExactSlots.pending_next_last S₀ hS₀ hSL).symm.trans
      (congrArg (fun L ↦ L.getLastD 0) hSS.2.2.2.1)
  have hSsel : S₀.position.entries.length ∈ F.oldSetup.position.label :=
    hSS.2.2.2.1 ▸ S₀.leafSelected
  have hSlt : S₀.position.entries.length < F.oldSetup.position.label.getLastD 0 :=
    ha ▸ (S₀.leafSlots.bounded a (hSL ▸ List.mem_singleton_self _)).1
  have hbefore := F.separated _ hSsel hSlt
  change S₀.position.entries.length < F.insertedLeft.leaves.headD 0 at hbefore
  rw [hSnext, List.headD_cons] at hbefore
  obtain ⟨hs, hm, _⟩ := NextSelectedLeaf.ordinary_parts F.insertedLeft.position F.oldLeft.position
    F.sameOrdinary (congrArg List.length F.sameEntries)
  have hstem : S₀.position.stem.ordinary = F.insertedLeft.position.stem.ordinary :=
    (congrArg Stem.ordinary hSS.2.1).trans hs
  have hmarker : S₀.position.size = F.insertedLeft.position.size := hSS.2.2.1.trans hm
  have hword : S₀.position.ordinary = F.insertedLeft.position.ordinary ++ vS := by
    change S₀.position.ordinary = F.oldLeft.position.ordinary ++ vS at hvS
    exact hvS.trans (congrArg (fun v : List ℕ ↦ v ++ vS) F.sameOrdinary)
  have hentries := entries_of_ordinary F.insertedLeft.position S₀.position vS hstem hmarker hword
  obtain ⟨Z, RS, w, hRSword, _, hw⟩ := CS₁.buffer hH F.exactSlots.2 S₀.position hstem hmarker
    vS hentries (fun x hx ↦ ⟨(hfS x hx).1, (le_max_right _ _).trans_lt (hfS x hx).2⟩)
    hbefore M
  have hRSR : RS.target.roots = [] := RS.roots.trans F.roots_nil.2
  have hRSL : RS.target.leaves ≠ [] := fun he ↦ hsr (RS.leaves.symm.trans he)
  obtain ⟨S₁, U₀, a₁, hS₁body, hUU, hS₁L, hUL, hS₁, hU₀, _, _, hh₁,
      wS, wU, hwS, hwU, hfS₁, hfU⟩ := MiddleRun.endpoint hH Set.Subset.rfl B M
    RS.target U.lower hRSR C.lowerLast hRSL RS.exactSlots
    (U.exactSlots C.lowerExact C.upperExact).1 RS.blue (fun _ ↦ RS.handoff)
  have ha₁ : a₁ = a := by
    calc
      a₁ = S₁.position.label.getLastD 0 := (ExactSlots.pending_next_last S₁ hS₁ hS₁L).symm
      _ = RS.target.position.label.getLastD 0 := congrArg (fun L ↦ L.getLastD 0) hS₁body.2.2.2.1
      _ = F.insertedLeft.position.label.getLastD 0 := congrArg (fun L ↦ L.getLastD 0) RS.label
      _ = F.oldLeft.position.label.getLastD 0 := F.sameLast.symm
      _ = a := ha.symm
  obtain ⟨A, _, hbA, _, hfA⟩ := SelectedLeafResponses.respond hH Set.Subset.rfl
    B .inside false S₁ (.leaf U₀) a₁ [] hS₁L hh₁ CS₀.bound
  let S₂ := LeafResponses.toPending S₁ a₁ [] hS₁L A
  have hslot := S₁.leafSlots.bounded a₁ (hS₁L ▸ List.mem_singleton_self _)
  have hfinalWord : S₂.position.ordinary = S₀.position.ordinary ++ (w ++ wS ++ A.newWord) := by
    change (LeafResponses.position A hslot.1 hslot.2.1).ordinary = _
    rw [LeafResponses.position_ordinary]
    change S₁.position.ordinary = RS.target.position.ordinary ++ wS at hwS
    rw [hwS, hRSword]
    simp only [List.append_assoc]
  have hfinalStem : S₂.position.stem.ordinary = S₀.position.stem.ordinary :=
    ((congrArg Stem.ordinary hS₁body.2.1).trans (congrArg Stem.ordinary RS.stem)).trans hstem.symm
  have hfinalMarker : S₂.position.size = S₀.position.size :=
    (hS₁body.2.2.1.trans RS.marker).trans hmarker.symm
  have hfinalCount : S₂.position.entries.length = a :=
    (LeafResponses.position_length A hslot.1 hslot.2.1).trans ha₁
  have hfinalEntries := entries_of_ordinary S₀.position S₂.position
    (w ++ wS ++ A.newWord) hfinalStem hfinalMarker hfinalWord
  have hfull : ∀ x ∈ w ++ wS ++ A.newWord, x ∈ H ∧ CS₀.bound < x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · rcases List.mem_append.mp hx with hx | hx
      · exact ⟨(hw x hx).1, (le_max_left _ _).trans_lt (hw x hx).2⟩
      · exact ⟨(hfS₁ x hx).1, (le_max_left _ _).trans_lt (hfS₁ x hx).2⟩
    · exact hfA x hx
  obtain ⟨R₀⟩ := CS₀.fire hS₀ S₂.position hfinalStem hfinalMarker hfinalCount
    (w ++ wS ++ A.newWord) hfinalEntries (fun x hx ↦ (hfull x hx).1)
    (fun x hx ↦ (hfull x hx).2)
  obtain ⟨RU⟩ := CU.fire_last U.lower U₀ hUupper U.sameOrdinary.symm
    (congrArg List.length U.sameEntries.symm) hUU hU₀ hUL wU hwU
    (fun x hx ↦ (hfU x hx).1) (fun x hx ↦ (le_max_right _ _).trans_lt (hfU x hx).2)
  exact InsideCompletion.triangle hH B R₀.target S₂ T₀ U₀ RT.target RU.target
    ⟨R₀.roots.trans hSS.1, R₀.leaves⟩ ⟨hS₁body.1, rfl⟩ ⟨hTT.1, hTL⟩ ⟨hUU.1, hUL⟩
    R₀.ordinary RT.ordinary RU.ordinary R₀.blue hbA RU.blue

end Erdos118.AlignedPositiveEnding
