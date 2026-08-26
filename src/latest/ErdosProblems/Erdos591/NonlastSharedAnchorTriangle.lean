import ErdosProblems.Erdos591.NonlastPreparedAnchor
import ErdosProblems.Erdos591.NonlastPreparedCheckpointTriangle

/-! # Both shared U-anchor requests through the complete nonlast triangle -/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact
open Relay

theorem nonlast_shared_anchor_triangle {N H0 H HU : Set ℕ}
    (hH0N : H0 ⊆ N) (hHH0 : H ⊆ H0) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (origin p oldT oldU : Concrete.Hist N) {a d c BU e g j k i : ℕ}
    (U : SplicedRootLabels HU BU e g j k) (ha : 2 ≤ a) (hAfterU : k < g)
    (hop : origin.position.pending = some ⟨false, .advance a⟩)
    (hboard : origin.position.board = Board.initial) (hmode : origin.position.mode = some true)
    (hwin : (exactGame N blue).ArchitectWins H0 b σ origin)
    (hfrom : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H0 b) origin p)
    (hwinOldT : (exactGame N blue).ArchitectWins H b σ oldT)
    (hwinOldU : (exactGame N blue).ArchitectWins H b σ oldU)
    (hp : p.position.pending = some ⟨true, .advance d⟩)
    (hpU : oldU.position.pending = some ⟨true, .advance c⟩)
    (hm : p.position.board.right.markerEvent = true)
    (hmU : oldU.position.board.right.markerEvent = true)
    (hUshape : LabeledWord.SameStructure p.position.board.right oldU.position.board.right)
    (hbeforeT : p.position.board.left.bodyLabels.length < p.position.board.left.lastSelectedBody)
    (hposT : 0 < p.position.board.left.coordinates.length)
    (hrootU : p.position.board.right.rootLabel = U.upper)
    (hbodyU : p.position.board.right.bodyLabels.length + 1 = U.anchor)
    (hLowerRoot : oldU.position.board.right.rootLabel = U.lower)
    (hModeSU : oldU.position.mode = some true)
    (hfixed : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p z →
      (exactGame N blue).kind z = .terminal w →
        z.position.board.right.criticalBodyRank z.position.board.left.lastSelectedLabel.card = k)
    (hlast : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p z →
      (exactGame N blue).kind z = .terminal w → criticalLastColor z = false)
    (hpOld : oldT.position.pending = some ⟨true, .advance 0⟩)
    (hrelOld : oldT.position.board.right.relaxed = true)
    (hnoOld : oldT.position.board.right.NoLeafPending)
    (hbeforeOld : LabeledWord.BeforeBody i oldT.position.board.right)
    (hnextOld : ∀ m ∈ oldT.position.board.right.rootLabel,
      oldT.position.board.right.bodyLabels.length < m → i ≤ m)
    {anchor : LabeledWord} {front : List (Finset ℕ × ℕ)}
    (hshape : LabeledWord.SameStructure oldT.position.board.right anchor)
    (hfront : LabeledWord.LegalRun anchor front p.position.board.left)
    (hpool : ∀ atom ∈ front, atom.2 ∈ H ∧ max oldT.position.bound (b oldT) < atom.2)
    (hFresh : ∀ x ∈ H, max oldT.position.bound (b oldT) < x)
    (hlastT : p.position.board.left.lastSelectedBody = i)
    (hall : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H0 b) origin z →
      (exactGame N blue).kind z = .terminal w →
        z.position.board.left.beforeLastLeafCount < z.position.board.right.beforeLastLeafCount)
    (hSrel : oldU.position.board.left.relaxed = true)
    (hS : LabeledWord.SameStructure oldT.position.board.left oldU.position.board.left)
    {gamma : ℕ} (hSUp : LabeledWord.UpToLeaf gamma oldT.position.board.left)
    (hSstrict : oldT.position.board.left.leafIndex < gamma)
    (hSnext : ∀ m ∈ oldT.position.board.left.currentLabel,
      oldT.position.board.left.leafIndex < m → gamma ≤ m)
    (hSroot : ∀ m ∈ oldU.position.board.left.rootLabel,
      m ≤ oldU.position.board.left.bodyLabels.length)
    (hgamma : gamma ∈ oldU.position.board.left.currentLabel)
    (hSlast : ∀ m ∈ oldU.position.board.left.currentLabel, m ≤ gamma) :
    ¬ blue.CliqueFree 3 := by
  have hHN := hHH0.trans hH0N
  have hwinP := (hwin.of_reachable (exactGame N blue) hfrom).mono
    (exactGame N blue) hHH0 (fun _ => le_rfl)
  have hd := winning_pending_marker_size_pos hHN hH blue hwinP hp hm
  have hc := winning_pending_marker_size_pos hHN hH blue hwinOldU hpU hmU
  let B := max (max p.position.bound (b p)) (max oldU.position.bound (b oldU))
  obtain ⟨E⟩ := LastFirstLabels.exists_of_infinite hH B d c hd hc
  obtain ⟨q, hpq, _hqn, hq, hqroot, hqbody, hqcurrent, hqbefore,
      PU, hPUtarget, hPUside, _hPUstem, _hPUlower, hPUpivot, _hPUupper⟩ :=
    nonlast_prepared_anchor_checkpoint hHN hH blue p oldU U E hwinP hwinOldU hp hpU hm hmU
      hUshape (le_max_left _ _) (le_max_right _ _) hbeforeT hposT hrootU hbodyU
      (follow_mode_some hfrom hmode) hfixed hlast
  have hpq0 : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H0 b) p q :=
    Relation.ReflTransGen.mono (fun _ _ hs =>
      FiniteResponseGame.FollowStep.mono (exactGame N blue) hHH0 (fun _ => le_rfl) hs) _ _ hpq
  obtain ⟨as, has, hAsPool⟩ := follow_word_inputs_above_bound hpq false
  have hfull := hfront.append has
  have hfullPool : ∀ atom ∈ front ++ as,
      atom.2 ∈ H ∧ max oldT.position.bound (b oldT) < atom.2 := by
    intro atom ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hpool atom ha
    · exact ⟨(hAsPool atom ha).1, hFresh atom.2 (hAsPool atom ha).1⟩
  have hstartOld := LabeledWord.relaxed_ne_start
    ((Position.history_dataInvariant oldT).2.1 true).1 hrelOld
  have hstartAnchor : anchor.parser ≠ .start := fun he => hstartOld (hshape.parser_eq.trans he)
  have hstartP := hfront.parser_ne_start hstartAnchor
  have hlastQ : q.position.board.left.lastSelectedBody = i :=
    (congrArg (fun C : Finset ℕ => C.sup id) (has.rootLabel_eq hstartP)).trans hlastT
  have hsup : E.lower.sup id = E.pivot :=
    le_antisymm (Finset.sup_le E.lower_le) (Finset.le_sup (f := id) E.pivot_lower)
  have hqSup : q.position.board.right.currentLabel.sup id = E.pivot := by
    rw [hqcurrent, hsup]
  exact nonlast_prepared_checkpoint_triangle hH0N hHH0 hH blue origin q oldT U PU
    ha hAfterU hop hboard hmode hwin (hfrom.trans hpq0) hq hwinOldT
    (by simpa only [hPUtarget] using hModeSU) hPUside hpOld hrelOld hnoOld
    hbeforeOld hnextOld hshape hfull hfullPool hFresh hlastQ
    (by simpa only [hqSup] using hqbefore) (hPUpivot.trans hqSup.symm) hqroot hqbody
    (by simpa only [hPUtarget] using hLowerRoot) hall
    (by simpa only [hPUtarget] using hSrel) (by simpa only [hPUtarget] using hS)
    hSUp hSstrict hSnext (by simpa only [hPUtarget] using hSroot)
    (by simpa only [hPUtarget] using hgamma) (by simpa only [hPUtarget] using hSlast)

#print axioms nonlast_shared_anchor_triangle

end Erdos591.Positive.Game.Payoff
