import ErdosProblems.Erdos591.RootGluingHistory
import ErdosProblems.Erdos591.ArchitectBudget

/-!
# Replaying a fixed root prefix and bounding its next body request

The lower prefix and both root labels are already fixed. The upper
response is appended without changing any lower data. If its shared
coordinates are at most `K`, all used upper inputs are in `[0,K]`, so
the actual next strategy request satisfies the proved finite-history
bound. This is the bound needed when allocating its later body label.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem winning_replay_root_bounded {N H : Set ℕ} (hHN : H ⊆ N) (hH : H.Infinite)
    (blue : SimpleGraph G) {b : Concrete.Hist N → ℕ}
    {σ : (exactGame N blue).ArchitectStrategy} {p : Concrete.Hist N}
    (hwin : (exactGame N blue).ArchitectWins H b σ p) (side : Bool)
    {B a c : ℕ} (L : LastFirstLabels H B a c)
    (hp : p.position.pending = some ⟨side, .advance c⟩)
    (hinit : p.position.board.get side = LabeledWord.initial)
    (hB : max p.position.bound (b p) ≤ B)
    {w : LabeledWord} {as : List (Finset ℕ × ℕ)}
    (hraw : (LabeledCode.rootCursor L.lower L.marker).runAtoms as = some w)
    (hm : w.markerEvent = true) (hindex : w.bodyLabels.length + 1 = L.pivot)
    (hinc : (L.marker :: as.map Prod.snd).Pairwise (· < ·))
    (hpool : ∀ x ∈ as.map Prod.snd, x ∈ H) (K : ℕ)
    (hK : ∀ x ∈ L.marker :: as.map Prod.snd, x ≤ K) :
    ∃ q d, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q ∧
      q.position.pending = some ⟨side, .advance d⟩ ∧ 0 < d ∧
      q.position.board.get side = LabeledWord.rootRelabel L.upper w ∧
      q.position.board.get (!side) = p.position.board.get (!side) ∧
      b q < ArchitectBudget.bound σ b (Finset.range (K + 1)) ∧
      d < ArchitectBudget.bound σ b (Finset.range (K + 1)) := by
  obtain ⟨u, hreply, hsort, huH, huB⟩ := L.root_reply p.position.board side hinit
    hraw hm hindex hinc hpool
  obtain ⟨q₀, hstep, hboard, hnone, hused⟩ :=
    Concrete.follow_reply_with_used hHN (payoff blue) σ p hp hreply huH
      (fun x hx => ⟨((le_max_left _ _).trans hB).trans_lt (huB x hx),
        ((le_max_right _ _).trans hB).trans_lt (huB x hx)⟩)
  have hword : q₀.position.board.get side = LabeledWord.rootRelabel L.upper w := by
    simp [hboard]
  have hmarker : (q₀.position.board.get side).markerEvent = true := by
    obtain ⟨r, hparse⟩ := LabeledWord.marker_blocks hm
    simp [hword, LabeledWord.rootRelabel, LabeledWord.markerEvent, hparse, hindex, L.pivot_upper]
  have hmk : L.marker ≤ K := hK _ (by simp)
  have hpK : p.position.bound ≤ K :=
    (((le_max_left _ _).trans hB).trans_lt L.marker_fresh.2).le.trans hmk
  have huK : ∀ x ∈ u, x ≤ K := by
    intro x hx
    have hs : x ∈ L.upper.sort (· ≤ ·) ++ L.marker :: as.map Prod.snd := by
      rw [← hsort]
      exact (Finset.mem_sort (· ≤ ·)).mpr hx
    rcases List.mem_append.mp hs with hs | hs
    · exact (L.upper_fresh x ((Finset.mem_sort (· ≤ ·)).mp hs)).2.2.le.trans hmk
    · exact hK x hs
  have hF : ReplayBudget.used q₀ ⊆ Finset.range (K + 1) := by
    intro x hx
    rw [hused] at hx
    apply Finset.mem_range.mpr
    rcases Finset.mem_union.mp hx with hx | hx
    · exact Nat.lt_succ_of_le ((ReplayBudget.used_bound p x hx).trans hpK)
    · exact Nat.lt_succ_of_le (huK x hx)
  have hwin₀ := hwin.of_reachable (exactGame N blue) (Relation.ReflTransGen.single hstep)
  obtain ⟨q, d, hrequest, hboard', hpend, hd⟩ := winning_request_at_marker hHN hH blue
    hwin₀ side hnone hmarker
  have hk : (exactGame N blue).kind q₀ = .architect :=
    (Concrete.kind_architect_iff (payoff blue) q₀).mpr
      ⟨hnone, Board.not_done_of_live (LabeledWord.marker_not_terminal hmarker)⟩
  have hbound := ArchitectBudget.follow_request_lt_bound σ b (Finset.range (K + 1)) hF hk hrequest
  have hsize : d < ArchitectBudget.bound σ b (Finset.range (K + 1)) := by
    simpa [Position.pendingSize, hpend, Request.size] using hbound.2
  exact ⟨q, d, (Relation.ReflTransGen.single hstep).tail hrequest, hpend, hd,
    by simpa only [hboard'] using hword,
    by simpa [hboard', hboard] using hreply.other_eq, hbound.1, hsize⟩

#print axioms winning_replay_root_bounded

end Erdos591.Positive.Game.Payoff
