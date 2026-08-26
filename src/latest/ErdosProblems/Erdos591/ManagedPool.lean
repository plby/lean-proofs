import ErdosProblems.Erdos591.ManagedWord

/-!
# Widen a managed record using a genuinely original-pool winning target

Pool enlargement preserves finite labels and recorded inputs, but does
not by itself preserve winning. The caller supplies winning at an
actual original-pool origin; its recorded path recovers winning at the
unchanged saved target before either managed constructor is rebuilt.
-/

namespace Erdos591.Positive.Game

open Erdos591.Negative.Exact
open Payoff

def LastFirstLabels.widen {J H : Set ℕ} (hJH : J ⊆ H) {B a c : ℕ}
    (L : LastFirstLabels J B a c) : LastFirstLabels H B a c where
  lower := L.lower
  upper := L.upper
  pivot := L.pivot
  marker := L.marker
  lower_card := L.lower_card
  upper_card := L.upper_card
  pivot_lower := L.pivot_lower
  pivot_upper := L.pivot_upper
  lower_le := L.lower_le
  upper_ge := L.upper_ge
  lower_fresh := fun x hx => ⟨hJH (L.lower_fresh x hx).1, (L.lower_fresh x hx).2⟩
  upper_fresh := fun x hx => ⟨hJH (L.upper_fresh x hx).1, (L.upper_fresh x hx).2⟩
  marker_fresh := ⟨hJH L.marker_fresh.1, L.marker_fresh.2⟩

namespace Relay

variable {N H J : Set ℕ} {blue : SimpleGraph G} {b : Concrete.Hist N → ℕ}
  {σ : (exactGame N blue).ArchitectStrategy} {w : LabeledWord}

def RootPlan.widen (R : RootPlan N J blue b σ w) (hJH : J ⊆ H)
    (hwin : (exactGame N blue).ArchitectWins H b σ R.target) : RootPlan N H blue b σ w where
  target := R.target
  side := R.side
  budget := R.budget
  lowerSize := R.lowerSize
  upperSize := R.upperSize
  labels := R.labels.widen hJH
  targetPending := R.targetPending
  targetInitial := R.targetInitial
  targetBound := R.targetBound
  targetWinning := hwin
  atoms := R.atoms
  run := R.run
  pool := fun a ha => ⟨hJH (R.pool a ha).1, (R.pool a ha).2⟩
  before := R.before

def PreparedBody.widen (P : PreparedBody N J blue b σ w) (hJH : J ⊆ H)
    (hwin : (exactGame N blue).ArchitectWins H b σ P.target) : PreparedBody N H blue b σ w where
  target := P.target
  side := P.side
  stem := P.stem
  remainingBodies := P.remainingBodies
  budget := P.budget
  lowerSize := P.lowerSize
  upperSize := P.upperSize
  labels := P.labels.widen hJH
  targetPending := P.targetPending
  targetMarker := P.targetMarker
  targetBound := P.targetBound
  targetWinning := hwin
  stemSame := P.stemSame
  stemParser := P.stemParser
  first := P.first
  firstRead := P.firstRead
  atoms := P.atoms
  run := P.run
  bodyLabels_eq := P.bodyLabels_eq
  pool := fun a ha => ⟨hJH (P.pool a ha).1, (P.pool a ha).2⟩
  rootLast := P.rootLast
  upto := P.upto

namespace Managed

def widen {t mode : Bool} {other : LabeledWord}
    (M : Managed N J blue b σ t mode other w) (hJH : J ⊆ H)
    (hwin : (exactGame N blue).ArchitectWins H b σ M.target) :
    Managed N H blue b σ t mode other w := by
  cases M with
  | root R hs ho hm => exact .root (R.widen hJH hwin) hs ho hm
  | prepared P hs ho hm hf => exact .prepared (P.widen hJH hwin) hs ho hm hf

theorem widen_target {t mode : Bool} {other : LabeledWord}
    (M : Managed N J blue b σ t mode other w) (hJH : J ⊆ H)
    (hwin : (exactGame N blue).ArchitectWins H b σ M.target) :
    (M.widen hJH hwin).target = M.target := by cases M <;> rfl

theorem widen_from {t mode : Bool} {other : LabeledWord}
    (M : Managed N J blue b σ t mode other w) (hJH : J ⊆ H)
    (origin : Concrete.Hist N) (hwin : (exactGame N blue).ArchitectWins H b σ origin)
    (hfrom : Relation.ReflTransGen ((exactGame N blue).FollowStep σ J b) origin M.target) :
    ∃ M' : Managed N H blue b σ t mode other w, M'.target = M.target ∧
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin M'.target := by
  have hpath : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) origin M.target :=
    Relation.ReflTransGen.mono (fun _ _ hs =>
      FiniteResponseGame.FollowStep.mono (exactGame N blue) hJH (fun _ => le_rfl) hs) _ _ hfrom
  have htarget := hwin.of_reachable (exactGame N blue) hpath
  exact ⟨M.widen hJH htarget, M.widen_target hJH htarget,
    (M.widen_target hJH htarget).symm ▸ hpath⟩

#print axioms widen_from

end Managed
end Relay
end Erdos591.Positive.Game
