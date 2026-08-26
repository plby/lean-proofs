import ErdosProblems.Erdos591.PreparedBodyTransport

/-!
# Retaining a root overlap until its last selected body

An upper initial root request and its label are fixed in advance. The
lower word retains its exact legal root-prefix execution, while future
body labels remain free. At the last selected body this prefix is a
genuine upper root response; the next upper body request is obtained
before the common body marker or either body label is chosen.
-/

namespace Erdos591.Positive.Game.Relay

open Erdos591.Negative.Exact
open Payoff

structure RootPlan (N H : Set ℕ) (blue : SimpleGraph G)
    (b : Concrete.Hist N → ℕ) (σ : (exactGame N blue).ArchitectStrategy) (w : LabeledWord) where
  target : Concrete.Hist N
  side : Bool
  budget : ℕ
  lowerSize : ℕ
  upperSize : ℕ
  labels : LastFirstLabels H budget lowerSize upperSize
  targetPending : target.position.pending = some ⟨side, .advance upperSize⟩
  targetInitial : target.position.board.get side = LabeledWord.initial
  targetBound : max target.position.bound (b target) ≤ budget
  targetWinning : (exactGame N blue).ArchitectWins H b σ target
  atoms : List (Finset ℕ × ℕ)
  run : LabeledWord.LegalRun (LabeledCode.rootCursor labels.lower labels.marker) atoms w
  pool : ∀ a ∈ atoms, a.2 ∈ H ∧ budget < a.2
  before : w.bodyLabels.length < labels.pivot

namespace RootPlan

variable {N H : Set ℕ} {blue : SimpleGraph G} {b : Concrete.Hist N → ℕ}
  {σ : (exactGame N blue).ArchitectStrategy} {w v : LabeledWord}

theorem not_start (R : RootPlan N H blue b σ w) : w.parser ≠ .start :=
  R.run.parser_ne_start (by simp [LabeledCode.rootCursor])

theorem rootLabel (R : RootPlan N H blue b σ w) : w.rootLabel = R.labels.lower := by
  simpa [LabeledCode.rootCursor] using
    R.run.rootLabel_eq (by simp [LabeledCode.rootCursor])

theorem before_body (R : RootPlan N H blue b σ w) :
    LabeledWord.BeforeBody R.labels.pivot w := ⟨R.rootLabel ▸ R.labels.pivot_lower, R.before⟩

theorem pending (R : RootPlan N H blue b σ w) : Macro.Pending w :=
  Or.inl ⟨R.labels.pivot, R.before_body⟩

theorem coordinates (R : RootPlan N H blue b σ w) :
    w.coordinates = R.labels.marker :: R.atoms.map Prod.snd := by
  simpa [LabeledCode.rootCursor] using LabeledWord.runAtoms_coordinates R.run.run

theorem budget_lt_bound {p : Concrete.Hist N} {s : Bool}
    (R : RootPlan N H blue b σ (p.position.board.get s)) : R.budget < p.position.bound := by
  have hm : R.labels.marker ∈ (p.position.board.get s).coordinates := by
    rw [R.coordinates]
    simp
  exact R.labels.marker_fresh.2.trans_le ((Position.history_dataInvariant p).1 _
    (p.position.board.get_support_subset s (LabeledWord.coordinate_mem_support hm))).2.2

def move (R : RootPlan N H blue b σ w) {ys : List (Finset ℕ × ℕ)}
    (h : LabeledWord.LegalRun w ys v)
    (hpool : ∀ a ∈ ys, a.2 ∈ H ∧ R.budget < a.2)
    (hbefore : v.bodyLabels.length < R.labels.pivot) : RootPlan N H blue b σ v where
  target := R.target
  side := R.side
  budget := R.budget
  lowerSize := R.lowerSize
  upperSize := R.upperSize
  labels := R.labels
  targetPending := R.targetPending
  targetInitial := R.targetInitial
  targetBound := R.targetBound
  targetWinning := R.targetWinning
  atoms := R.atoms ++ ys
  run := R.run.append h
  pool := by
    intro a ha
    exact (List.mem_append.mp ha).elim (R.pool a) (hpool a)
  before := hbefore

theorem fire_first (R : RootPlan N H blue b σ w) (hHN : H ⊆ N) (hH : H.Infinite)
    (hm : w.markerEvent = true) (hindex : w.bodyLabels.length + 1 = R.labels.pivot)
    (hinc : w.coordinates.Pairwise (· < ·)) :
    ∃ q d, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) R.target q ∧
      q.position.pending = some ⟨R.side, .advance d⟩ ∧ 0 < d ∧
      LabeledWord.SameStructure w (q.position.board.get R.side) ∧
      (q.position.board.get R.side).markerEvent = true ∧
      q.position.board.get (!R.side) = R.target.position.board.get (!R.side) ∧
      (q.position.board.get R.side).NoRootPassed := by
  have htailInc : (R.labels.marker :: R.atoms.map Prod.snd).Pairwise (· < ·) := by
    simpa only [R.coordinates] using hinc
  have hpool : ∀ x ∈ R.atoms.map Prod.snd, x ∈ H := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    exact (R.pool a ha).1
  obtain ⟨u, hr, _hsort, huH, huB⟩ := R.labels.root_reply R.target.position.board R.side
    R.targetInitial R.run.run hm hindex htailInc hpool
  obtain ⟨q₀, hstep, hboard, hnone⟩ := Concrete.follow_reply hHN (payoff blue) σ R.target
    R.targetPending hr huH (fun x hx =>
      ⟨((le_max_left _ _).trans R.targetBound).trans_lt (huB x hx),
        ((le_max_right _ _).trans R.targetBound).trans_lt (huB x hx)⟩)
  have hword : q₀.position.board.get R.side = LabeledWord.rootRelabel R.labels.upper w := by
    simp [hboard]
  have hmarker : (q₀.position.board.get R.side).markerEvent = true := by
    obtain ⟨r, hp⟩ := LabeledWord.marker_blocks hm
    simp [hword, LabeledWord.rootRelabel, LabeledWord.markerEvent, hp, hindex,
      R.labels.pivot_upper]
  have hwin := R.targetWinning.of_reachable (exactGame N blue)
    (Relation.ReflTransGen.single hstep)
  obtain ⟨q, d, hrequest, hboard', hp, hd⟩ :=
    winning_request_at_marker hHN hH blue hwin R.side hnone hmarker
  refine ⟨q, d, (Relation.ReflTransGen.single hstep).tail hrequest, hp, hd, ?_, ?_, ?_, ?_⟩
  · rw [hboard', hword]
    exact (LabeledWord.rootRelabel_sameStructure R.labels.upper w).symm
  · simpa only [hboard'] using hmarker
  · simpa [hboard', hboard] using hr.other_eq
  · intro i hi
    have hi' : i ∈ R.labels.upper := by
      simpa [hboard', hword, LabeledWord.rootRelabel] using hi
    have hlen : (q.position.board.get R.side).bodyLabels.length = w.bodyLabels.length := by
      simp [hboard', hword, LabeledWord.rootRelabel]
    rw [hlen]
    have hge := R.labels.upper_ge i hi'
    omega

theorem fire (R : RootPlan N H blue b σ w) (hHN : H ⊆ N) (hH : H.Infinite)
    (hm : w.markerEvent = true) (hindex : w.bodyLabels.length + 1 = R.labels.pivot)
    (hinc : w.coordinates.Pairwise (· < ·)) :
    ∃ q d, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) R.target q ∧
      q.position.pending = some ⟨R.side, .advance d⟩ ∧ 0 < d ∧
      LabeledWord.SameStructure w (q.position.board.get R.side) ∧
      (q.position.board.get R.side).markerEvent = true ∧
      q.position.board.get (!R.side) = R.target.position.board.get (!R.side) := by
  obtain ⟨q, d, hpath, hp, hd, hshape, hmark, hother, _hfirst⟩ :=
    R.fire_first hHN hH hm hindex hinc
  exact ⟨q, d, hpath, hp, hd, hshape, hmark, hother⟩

#print axioms fire_first
#print axioms fire

end RootPlan

end Erdos591.Positive.Game.Relay
