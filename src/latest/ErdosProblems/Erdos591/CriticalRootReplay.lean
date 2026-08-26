import ErdosProblems.Erdos591.CriticalRootLabels
import ErdosProblems.Erdos591.RootGluingHistory

/-!
# Actual upper root response at a prescribed lower critical body

The upper root label first selects the shared body. Its initial response
therefore contains exactly the retained lower coordinates through that
marker, even though the lower root may have several later selected bodies.
-/

namespace Erdos591.Positive.Game

namespace CriticalRootLabels

theorem root_reply {H : Set ℕ} {B e d j : ℕ} (L : CriticalRootLabels H B e d j)
    (board : Board) (side : Bool) (hinit : board.get side = LabeledWord.initial)
    {v : LabeledWord} {xs : List (Finset ℕ × ℕ)}
    (hr : (LabeledCode.rootCursor L.lower L.marker).runAtoms xs = some v)
    (hm : v.markerEvent = true) (hindex : v.bodyLabels.length + 1 = L.shared)
    (hinc : (L.marker :: xs.map Prod.snd).Pairwise (· < ·))
    (hpool : ∀ x ∈ xs.map Prod.snd, x ∈ H) :
    ∃ u, Reply board ⟨side, .advance d⟩ u (board.update side (LabeledWord.rootRelabel L.upper v)) ∧
      u.sort (· ≤ ·) = L.upper.sort (· ≤ ·) ++ L.marker :: xs.map Prod.snd ∧
      (↑u : Set ℕ) ⊆ H ∧ ∀ x ∈ u, B < x := by
  have hrest := LabeledWord.rootRelabel_first_marker hr
    (fun i hi => ⟨(Nat.zero_le B).trans_lt (L.upper_fresh i hi).2.1,
      (L.upper_fresh i hi).2.2⟩) hm (hindex ▸ L.shared_upper)
    (fun i hi => hindex ▸ (L.upper_bounds i hi).1)
  let input := L.upper.sort (· ≤ ·) ++ L.marker :: xs.map Prod.snd
  have hinput : input.Pairwise (· < ·) := by
    refine List.pairwise_append.mpr ⟨(Finset.sortedLT_sort L.upper).pairwise, hinc, ?_⟩
    intro x hx y hy
    have hxm := (L.upper_fresh x ((Finset.mem_sort (· ≤ ·)).mp hx)).2.2
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hxm
    · exact hxm.trans ((List.pairwise_cons.mp hinc).1 y hy)
  have hlegal : (board.get side).AllowedSize L.upper.card := by
    simp [hinit, LabeledWord.AllowedSize, LabeledWord.terminal, LabeledWord.initial]
  have hreply := Reply.advance_of_list board side L.upper L.marker (xs.map Prod.snd)
    (LabeledCode.rootCursor L.upper L.marker) (LabeledWord.rootRelabel L.upper v)
    hlegal (by rw [hinit]; exact LabeledCode.read_root _ _) hrest hinput
  rw [L.upper_card] at hreply
  have hvalues : ∀ x ∈ input, x ∈ H ∧ B < x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · have hf := L.upper_fresh x ((Finset.mem_sort (· ≤ ·)).mp hx)
      exact ⟨hf.1, hf.2.1⟩
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact L.marker_fresh
      · exact ⟨hpool x hx, L.marker_fresh.2.trans ((List.pairwise_cons.mp hinc).1 x hx)⟩
  exact ⟨input.toFinset, hreply, Erdos590.Larson.sort_toFinset_eq_self_of_pairwise hinput,
    fun x hx => (hvalues x (List.mem_toFinset.mp hx)).1,
    fun x hx => (hvalues x (List.mem_toFinset.mp hx)).2⟩

end CriticalRootLabels

namespace Payoff

open Erdos591.Negative.Exact

theorem winning_critical_root_request {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} (p : Concrete.Hist N)
    (hwin : (exactGame N blue).ArchitectWins H b σ p) (side : Bool)
    {B e d j : ℕ} (L : CriticalRootLabels H B e d j)
    (hp : p.position.pending = some ⟨side, .advance d⟩)
    (hinit : p.position.board.get side = LabeledWord.initial)
    (hB : max p.position.bound (b p) ≤ B)
    {v : LabeledWord} {xs : List (Finset ℕ × ℕ)}
    (hr : (LabeledCode.rootCursor L.lower L.marker).runAtoms xs = some v)
    (hm : v.markerEvent = true) (hindex : v.bodyLabels.length + 1 = L.shared)
    (hinc : (L.marker :: xs.map Prod.snd).Pairwise (· < ·))
    (hpool : ∀ x ∈ xs.map Prod.snd, x ∈ H) :
    ∃ q a, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q ∧
      q.position.pending = some ⟨side, .advance a⟩ ∧ 0 < a ∧
      q.position.board.get side = LabeledWord.rootRelabel L.upper v ∧
      (q.position.board.get side).markerEvent = true ∧
      (q.position.board.get side).NoRootPassed ∧
      q.position.board.get (!side) = p.position.board.get (!side) := by
  obtain ⟨u, hreply, _hsort, huH, huB⟩ := L.root_reply p.position.board side hinit
    hr hm hindex hinc hpool
  obtain ⟨q₀, hstep, hboard, hnone⟩ := Concrete.follow_reply hHN (payoff blue) σ p hp
    hreply huH (fun x hx =>
      ⟨((le_max_left _ _).trans hB).trans_lt (huB x hx),
        ((le_max_right _ _).trans hB).trans_lt (huB x hx)⟩)
  have hword : q₀.position.board.get side = LabeledWord.rootRelabel L.upper v := by
    simp [hboard]
  have hmarker : (q₀.position.board.get side).markerEvent = true := by
    obtain ⟨r, hparse⟩ := LabeledWord.marker_blocks hm
    simp [hword, LabeledWord.rootRelabel, LabeledWord.markerEvent, hparse, hindex, L.shared_upper]
  obtain ⟨q, a, hrequest, hboard', hpend, ha⟩ := winning_request_at_marker hHN hH blue
    (hwin.of_reachable (exactGame N blue) (.single hstep)) side hnone hmarker
  refine ⟨q, a, (Relation.ReflTransGen.single hstep).tail hrequest, hpend, ha,
    by simpa only [hboard'] using hword, by simpa only [hboard'] using hmarker, ?_,
    by simpa [hboard', hboard] using hreply.other_eq⟩
  intro i hi
  have himem : i ∈ L.upper := by simpa [hboard', hword, LabeledWord.rootRelabel] using hi
  have hlen : (q.position.board.get side).bodyLabels.length = v.bodyLabels.length := by
    simp [hboard', hword, LabeledWord.rootRelabel]
  have hiBound := (L.upper_bounds i himem).1
  rw [hlen]
  omega

#print axioms CriticalRootLabels.root_reply
#print axioms winning_critical_root_request

end Payoff

end Erdos591.Positive.Game
