import ErdosProblems.Erdos591.PreliminaryRun

/-!
# The actual first preliminary lower run ends immediately before beta

Starting in the issued last S body, follow the old opposite critical
body to its largest selected leaf. The actual endpoint has S rank r,
so beta is its next selection. Both full body labels and the literal
input runs are retained; every new input lies in the chosen future
pool and exceeds its externally recorded bound.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

theorem preliminary_lower_run {N H K HL : Set ℕ}
    (hHN : H ⊆ N) (hKH : K ⊆ H) (hK : K.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (origin old p : Concrete.Hist N) {a B P Q r t F : ℕ}
    (L : PreliminaryPivotLabels HL B P Q r t) (ha : 2 ≤ a)
    (hop : origin.position.pending = some ⟨false, .advance a⟩)
    (hboard : origin.position.board = Board.initial) (hmode : origin.position.mode = some true)
    (hwin : (exactGame N blue).ArchitectWins H b σ origin)
    (hfrom : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin old)
    (holdp : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) old p)
    (hOld : CriticalCheckpoint old)
    (hl : p.position.board.left.relaxed = true) (hr : p.position.board.right.relaxed = true)
    (hSroot : ∀ i ∈ p.position.board.left.rootLabel, i ≤ p.position.board.left.bodyLabels.length)
    (hSlabel : p.position.board.left.currentLabel = L.lower)
    (hTbody : p.position.board.right.bodyLabels = old.position.board.right.bodyLabels)
    (hTlt : p.position.board.right.leafIndex < p.position.board.right.currentLabel.sup id)
    (hrank : old.position.board.right.currentLabel.card -
      (old.position.board.right.currentLabel.filter
        (fun x => x ≤ old.position.board.right.leafIndex)).card = r)
    (hfresh : ∀ x ∈ K, F < x)
    (hall : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin z →
      (exactGame N blue).kind z = .terminal w →
        z.position.board.left.beforeLastLeafCount < z.position.board.right.beforeLastLeafCount) :
    ∃ q, Relation.ReflTransGen ((exactGame N blue).FollowStep σ K b) p q ∧
      q.position.pending = none ∧ q.position.board.left.relaxed = true ∧
      q.position.board.right.relaxed = true ∧ q.position.board.right.NoLeafPending ∧
      q.position.board.left.bodyLabels = p.position.board.left.bodyLabels ∧
      q.position.board.left.bodyMarker = p.position.board.left.bodyMarker ∧
      q.position.board.left.currentLabel = L.lower ∧
      q.position.board.right.bodyLabels = old.position.board.right.bodyLabels ∧
      q.position.board.right.bodyMarker = p.position.board.right.bodyMarker ∧
      q.position.board.right.leafIndex = p.position.board.right.currentLabel.sup id ∧
      (q.position.board.left.currentLabel.filter
        (fun x => x ≤ q.position.board.left.leafIndex)).card = r ∧
      q.position.board.left.leafIndex < L.beta ∧
      (∀ x ∈ L.lower, q.position.board.left.leafIndex < x → L.beta ≤ x) ∧
      (∀ x ∈ q.position.board.left.coordinates,
        x ≤ q.position.board.right.coordinates.getLastD 0) ∧
      ∃ as bs, LabeledWord.LegalRun p.position.board.left as q.position.board.left ∧
        LabeledWord.LegalRun p.position.board.right bs q.position.board.right ∧
        (∀ atom ∈ as, atom.2 ∈ K ∧ F < atom.2) ∧
        (∀ atom ∈ bs, atom.2 ∈ K ∧ F < atom.2) := by
  exact preliminary_run hHN hKH hK blue origin old p L.lower L.beta_lower
    (by rw [finite_rank_eq_strict_rank_add_one L.lower L.beta_lower, L.lower_before]) ha
    hop hboard hmode hwin hfrom holdp hOld hl hr hSroot hSlabel hTbody hTlt hrank hfresh hall

#print axioms preliminary_lower_run

end Erdos591.Positive.Game.Payoff
