import ErdosProblems.Erdos591.CriticalObservables

/-!
# Finite bounds for the strict critical-body observable

Every winning strict terminal has an actual critical selected pair.
Its body rank lies strictly between zero and the root cardinality.
If the critical leaf exhausts its body, at least two later selected
bodies remain. These bounds hold before any local color is chosen.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem ClearSide.criticalPair_spec_of_range {w : LabeledWord} {s t : G}
    (hc : ClearSide w s t) {n : ℕ} (hn : 0 < n) (hbound : n ≤ w.selectedLeafCount) :
    w.CriticalPairSpec n (w.criticalPair n) := by
  apply w.criticalPair_spec _ hn hbound
  intro p hp
  obtain ⟨hi, hj⟩ := Finset.mem_sigma.mp hp
  have hcut := hc.selected_pair_cut hi hj
  exact ⟨(hc.root_bounds p.1 hi).1, (hc.body_bounds _ hcut.1 p.2 hj).1⟩

theorem Clear.strict_critical_data {board : Board} {s t : G} (hc : Clear board s t)
    (hfirst : board.left.coordinates.headD 0 < board.right.coordinates.headD 0)
    (hmax : MaxOrder true board) (hcard : 2 ≤ board.left.rootLabel.card)
    (hstrict : board.left.beforeLastLeafCount < board.right.beforeLastLeafCount) :
    3 ≤ board.left.lastSelectedLabel.card ∧
      board.right.CriticalPairSpec board.left.lastSelectedLabel.card
        (board.right.criticalPair board.left.lastSelectedLabel.card) ∧
      (board.right.criticalPair board.left.lastSelectedLabel.card).1 <
        board.right.lastSelectedBody ∧
      0 < board.right.criticalBodyRank board.left.lastSelectedLabel.card ∧
      board.right.criticalBodyRank board.left.lastSelectedLabel.card < board.right.rootLabel.card ∧
      (board.right.criticalLast board.left.lastSelectedLabel.card = true →
        board.right.criticalBodyRank board.left.lastSelectedLabel.card + 1 <
          board.right.rootLabel.card) := by
  classical
  obtain ⟨hl, hr, hpre⟩ := hc.inside_roots_nonempty hfirst hmax hcard
  have hlastL : board.left.lastSelectedBody ∈ board.left.rootLabel := by
    simpa [LabeledWord.lastSelectedBody] using Finset.sup_mem_of_nonempty (f := id) hl
  have hlastR : board.right.lastSelectedBody ∈ board.right.rootLabel := by
    simpa [LabeledWord.lastSelectedBody] using Finset.sup_mem_of_nonempty (f := id) hr
  have hposL : 0 < board.left.lastSelectedLabel.card := hc.1.selected_body_card_pos hlastL
  have hposR : 0 < board.right.lastSelectedLabel.card := hc.2.1.selected_body_card_pos hlastR
  have hcount := hc.inside_last_body_count hfirst hmax hl hr
  have htotalR := LabeledWord.selectedLeafCount_decomposition hr
  have hgap := hc.strict_last_body_count hfirst hmax hl hr hstrict
  let p := board.right.criticalPair board.left.lastSelectedLabel.card
  have hp : board.right.CriticalPairSpec board.left.lastSelectedLabel.card p :=
    hc.2.1.criticalPair_spec_of_range hposL (by omega)
  obtain ⟨hi, hj⟩ := Finset.mem_sigma.mp hp.1
  have hbefore : p.1 < board.right.lastSelectedBody := by
    have hle : p.1 ≤ board.right.lastSelectedBody := Finset.le_sup (f := id) hi
    by_contra hn
    have hindex : p.1 - 1 + 1 = board.right.lastSelectedBody := by have := hp.2.1; omega
    have hbound := LabeledWord.selectedLeafPairsFrom_last_body_card_le (j := p.2 - 1) hindex
    rw [hp.2.2.2] at hbound
    omega
  let F := board.right.rootLabel.filter (fun i => i ≤ p.1)
  have hmemF : p.1 ∈ F := Finset.mem_filter.mpr ⟨hi, le_rfl⟩
  have hlastNotF : board.right.lastSelectedBody ∉ F := by
    intro h
    exact not_le_of_gt hbefore (Finset.mem_filter.mp h).2
  have hsub : F ⊆ board.right.rootLabel := Finset.filter_subset _ _
  have hlt : F.card < board.right.rootLabel.card := Finset.card_lt_card
    (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun heq => hlastNotF (heq ▸ hlastR)⟩)
  refine ⟨by omega, hp, hbefore, Finset.card_pos.mpr ⟨_, hmemF⟩, hlt, ?_⟩
  intro hlast
  have hno : ∀ j ∈ board.right.bodyLabels.getD (p.1 - 1) ∅, j ≤ p.2 := by
    simpa only [LabeledWord.criticalLast, decide_eq_true_eq] using hlast
  have hmiddle : ∃ k ∈ board.right.rootLabel, p.1 < k ∧ k < board.right.lastSelectedBody := by
    by_contra hn
    have hpen : ∀ k ∈ board.right.rootLabel, k < board.right.lastSelectedBody → k ≤ p.1 := by
      intro k hk hklast
      by_contra hknot
      exact hn ⟨k, hk, lt_of_not_ge hknot, hklast⟩
    have hbodyIndex : p.1 - 1 + 1 = p.1 := by have := hp.2.1; omega
    have hleafIndex : p.2 - 1 + 1 = p.2 := by have := hp.2.2.1; omega
    have hbound := (hc.2.1.penultimate_endpoint_iff_suffix_card
      (i := p.1 - 1) (j := p.2 - 1)
      (by simpa only [hbodyIndex] using hi) (by simpa only [hleafIndex] using hj)).mpr
      ⟨by simpa only [hbodyIndex] using hbefore,
        by simpa only [hbodyIndex] using hpen, by simpa only [hleafIndex] using hno⟩
    rw [hp.2.2.2] at hbound
    omega
  obtain ⟨k, hk, hpk, hklast⟩ := hmiddle
  have hknot : k ∉ F := fun h => not_le_of_gt hpk (Finset.mem_filter.mp h).2
  have hinsert : insert k F ⊆ board.right.rootLabel := Finset.insert_subset hk hsub
  have hlastNot : board.right.lastSelectedBody ∉ insert k F := by
    intro h
    rcases Finset.mem_insert.mp h with h | h
    · exact hklast.ne h.symm
    · exact hlastNotF h
  have hlt' := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
    ⟨hinsert, fun heq => hlastNot (heq ▸ hlastR)⟩)
  rw [Finset.card_insert_of_notMem hknot] at hlt'
  exact hlt'

theorem terminal_strict_critical_data {N H : Set ℕ} (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (origin q : Concrete.Hist N) {a : ℕ} (ha : 2 ≤ a)
    (hop : origin.position.pending = some ⟨false, .advance a⟩)
    (hboard : origin.position.board = Board.initial) (hmode : origin.position.mode = some true)
    (hwin : (exactGame N blue).ArchitectWins H b σ origin)
    (hpath : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin q)
    {value : Bool} (hq : (exactGame N blue).kind q = .terminal value)
    (hstrict : q.position.board.left.beforeLastLeafCount <
      q.position.board.right.beforeLastLeafCount) :
    3 ≤ q.position.board.left.lastSelectedLabel.card ∧
      0 < q.position.board.right.criticalBodyRank q.position.board.left.lastSelectedLabel.card ∧
      q.position.board.right.criticalBodyRank q.position.board.left.lastSelectedLabel.card <
        q.position.board.right.rootLabel.card ∧
      (criticalLastColor q = true →
        q.position.board.right.criticalBodyRank q.position.board.left.lastSelectedLabel.card + 1 <
          q.position.board.right.rootLabel.card) := by
  obtain ⟨s, t, hc, hmax, hfirst, hcard⟩ :=
    terminal_inside_clear_data blue origin q (by omega) hop hboard hmode hwin hpath hq
  obtain ⟨hsize, _hspec, _hbefore, hpos, hlt, hlast⟩ :=
    hc.strict_critical_data hfirst hmax (by simpa only [hcard] using ha) hstrict
  exact ⟨hsize, hpos, hlt, hlast⟩

#print axioms Clear.strict_critical_data
#print axioms terminal_strict_critical_data

end Erdos591.Positive.Game.Payoff
