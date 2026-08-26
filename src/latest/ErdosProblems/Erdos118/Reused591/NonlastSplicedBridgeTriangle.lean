import ErdosProblems.Erdos118.Reused591.SplicedAnchorMarkerStart
import ErdosProblems.Erdos118.Reused591.AnchorMarkerReplay
import ErdosProblems.Erdos118.Reused591.NonlastSharedAnchorTriangle

namespace Erdos118.Reused591

/-!
# The higher-rank nonlast upper bridge through the strict triangle

Start after the actual upper preliminary U response. It is either
a fresh selected leaf or a selected marker at or before the anchor.
Reach the actual anchor request, replay it in the lower U play,
and retain the T prefix for the complete shared-anchor construction.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem nonlast_spliced_bridge_triangle {N H0 H HU : Set ℕ}
    (hH0N : H0 ⊆ N) (hHH0 : H ⊆ H0) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (origin p oldT oldU : Concrete.Hist N) {a BU e g j k i : ℕ}
    (U : SplicedRootLabels HU BU e g j k) (ha : 2 ≤ a) (hAfterU : k < g)
    (hop : origin.position.pending = some ⟨false, .advance a⟩)
    (hboard : origin.position.board = Board.initial) (hmode : origin.position.mode = some true)
    (hwin : (exactGame N blue).ArchitectWins H0 b σ origin)
    (hfrom : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H0 b) origin p)
    (hwinOldT : (exactGame N blue).ArchitectWins H b σ oldT)
    (hwinOldU : (exactGame N blue).ArchitectWins H b σ oldU)
    (hn : p.position.pending = none) (hTrel : p.position.board.left.relaxed = true)
    (hbeforeT : p.position.board.left.bodyLabels.length < p.position.board.left.lastSelectedBody)
    (hlastT : p.position.board.left.lastSelectedBody = i)
    (hrootU : p.position.board.right.rootLabel = U.upper)
    (hstart : (p.position.board.right.relaxed = true ∧
      p.position.board.right.bodyLabels.length < U.anchor ∧
      ∀ x ∈ p.position.board.left.coordinates,
        x ≤ p.position.board.right.coordinates.getLastD 0) ∨
      (p.position.board.right.markerEvent = true ∧
        p.position.board.right.bodyLabels.length + 1 ≤ U.anchor))
    (hfixed : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p z →
      (exactGame N blue).kind z = .terminal w →
        z.position.board.right.criticalBodyRank z.position.board.left.lastSelectedLabel.card = k)
    (hlast : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p z →
      (exactGame N blue).kind z = .terminal w → criticalLastColor z = false)
    (hpOldT : oldT.position.pending = some ⟨true, .advance 0⟩)
    (hrelOldT : oldT.position.board.right.relaxed = true)
    (hnoOldT : oldT.position.board.right.NoLeafPending)
    (hbeforeOldT : LabeledWord.BeforeBody i oldT.position.board.right)
    (hnextOldT : ∀ m ∈ oldT.position.board.right.rootLabel,
      oldT.position.board.right.bodyLabels.length < m → i ≤ m)
    (hpOldU : oldU.position.pending = some ⟨true, .advance 0⟩)
    (hrelOldU : oldU.position.board.right.relaxed = true)
    (hnoOldU : oldU.position.board.right.NoLeafPending)
    (hbeforeOldU : LabeledWord.BeforeBody U.anchor oldU.position.board.right)
    (hnextOldU : ∀ m ∈ oldU.position.board.right.rootLabel,
      oldU.position.board.right.bodyLabels.length < m → U.anchor ≤ m)
    (hLowerRoot : oldU.position.board.right.rootLabel = U.lower)
    (hModeSU : oldU.position.mode = some true)
    {anchorT anchorU : LabeledWord} {frontT frontU : List (Finset ℕ × ℕ)}
    (hshapeT : LabeledWord.SameStructure oldT.position.board.right anchorT)
    (hfrontT : LabeledWord.LegalRun anchorT frontT p.position.board.left)
    (hpoolT : ∀ atom ∈ frontT, atom.2 ∈ H ∧ max oldT.position.bound (b oldT) < atom.2)
    (hshapeU : LabeledWord.SameStructure oldU.position.board.right anchorU)
    (hfrontU : LabeledWord.LegalRun anchorU frontU p.position.board.right)
    (hpoolU : ∀ atom ∈ frontU, atom.2 ∈ H ∧ max oldU.position.bound (b oldU) < atom.2)
    (hFreshT : ∀ x ∈ H, max oldT.position.bound (b oldT) < x)
    (hFreshU : ∀ x ∈ H, max oldU.position.bound (b oldU) < x)
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
  have hmodeP := follow_mode_some hfrom hmode
  obtain ⟨q, d, hpq, hpqPending, hd, hqm, hqi, hqUroot, hqTroot, hqBefore⟩ :
      ∃ q d, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q ∧
        q.position.pending = some ⟨true, .advance d⟩ ∧ 0 < d ∧
        q.position.board.right.markerEvent = true ∧
        q.position.board.right.bodyLabels.length + 1 = U.anchor ∧
        q.position.board.right.rootLabel = U.upper ∧
        q.position.board.left.rootLabel = p.position.board.left.rootLabel ∧
        q.position.board.left.bodyLabels.length < q.position.board.left.lastSelectedBody := by
    rcases hstart with ⟨hr, hb, hs⟩ | ⟨hm, hi⟩
    · exact winning_spliced_anchor_marker hHN hH blue U hwinP hn hTrel hr
        hbeforeT hb hrootU hs hmodeP hfixed hlast
    · exact winning_spliced_anchor_from_marker hHN hH blue U hwinP hn hTrel hm
        hbeforeT hi hrootU hmodeP hfixed hlast
  have hpq0 : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H0 b) p q :=
    Relation.ReflTransGen.mono (fun _ _ hs =>
      FiniteResponseGame.FollowStep.mono (exactGame N blue) hHH0 (fun _ => le_rfl) hs) _ _ hpq
  obtain ⟨as, has, hAsPool⟩ := follow_word_inputs_above_bound hpq false
  obtain ⟨bs, hbs, hBsPool⟩ := follow_word_inputs_above_bound hpq true
  have hfullT := hfrontT.append has
  have hfullU := hfrontU.append hbs
  have hfullTPool : ∀ atom ∈ frontT ++ as,
      atom.2 ∈ H ∧ max oldT.position.bound (b oldT) < atom.2 := by
    intro atom ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hpoolT atom ha
    · exact ⟨(hAsPool atom ha).1, hFreshT atom.2 (hAsPool atom ha).1⟩
  have hfullUPool : ∀ atom ∈ frontU ++ bs,
      atom.2 ∈ H ∧ max oldU.position.bound (b oldU) < atom.2 := by
    intro atom ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hpoolU atom ha
    · exact ⟨(hBsPool atom ha).1, hFreshU atom.2 (hBsPool atom ha).1⟩
  obtain ⟨su, c, hOldSU, hpSU, _hc, hSUshape, hmSU, _hiSU, hrootSU, hSUother⟩ :=
    next_marker_request_at_endpoint hHN hH blue oldU q true true hwinOldU hpOldU hrelOldU
      hnoOldU hbeforeOldU hnextOldU hshapeU hfullU hfullUPool hqm hqi
  simp only [Board.get, Bool.not_true] at hSUshape hmSU hrootSU hSUother
  obtain ⟨initialAtoms, hinit⟩ := History.word_run p false
  have hqPos : 0 < q.position.board.left.coordinates.length :=
    (hinit.relaxed_coordinates_pos hTrel).trans_le has.coordinates_prefix.length_le
  have hqLast : q.position.board.left.lastSelectedBody = i :=
    (congrArg (fun C : Finset ℕ => C.sup id) hqTroot).trans hlastT
  exact nonlast_shared_anchor_triangle hH0N hHH0 hH blue origin q oldT su U ha hAfterU
    hop hboard hmode hwin (hfrom.trans hpq0) hwinOldT
    (hwinOldU.of_reachable (exactGame N blue) hOldSU) hpqPending hpSU hqm hmSU hSUshape.symm
    hqBefore hqPos hqUroot hqi (hrootSU.trans hLowerRoot) (follow_mode_some hOldSU hModeSU)
    (fun z w hqz hz => hfixed z w (hpq.trans hqz) hz)
    (fun z w hqz hz => hlast z w (hpq.trans hqz) hz)
    hpOldT hrelOldT hnoOldT hbeforeOldT hnextOldT hshapeT hfullT hfullTPool hFreshT hqLast hall
    (by simpa only [hSUother] using hSrel) (by simpa only [hSUother] using hS)
    hSUp hSstrict hSnext (by simpa only [hSUother] using hSroot)
    (by simpa only [hSUother] using hgamma) (by simpa only [hSUother] using hSlast)

#print axioms nonlast_spliced_bridge_triangle

end Erdos591.Positive.Game.Payoff

end Erdos118.Reused591
