import ErdosProblems.Erdos591.FixedBoundThinning
import ErdosProblems.Erdos591.ReachableBodyCard

/-!
# Localize a bounded future body size before reading either body label

The finite color is a truncated terminal body cardinality. A proved
bound makes the truncation inactive. Every later actual request for
that body then has the localized size, by taking a real winning
continuation and recovering the cardinality of its first response.
-/

namespace Erdos591.Positive.Game.Payoff

open Erdos591.Negative.Exact

noncomputable def futureBodyColor {N : Set ℕ} (side : Bool) (i R : ℕ)
    (q : Concrete.Hist N) : Fin (R + 1) :=
  ⟨min ((q.position.board.get side).bodyLabels.getD (i - 1) ∅).card R,
    Nat.lt_succ_of_le (min_le_right _ _)⟩

theorem bounded_future_body_localization {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (p : Concrete.Hist N) (side : Bool) (i R : ℕ)
    (hbound : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p z →
      (exactGame N blue).kind z = .terminal w →
        0 < ((z.position.board.get side).bodyLabels.getD (i - 1) ∅).card ∧
          ((z.position.board.get side).bodyLabels.getD (i - 1) ∅).card + 2 ≤ R) :
    ∃ L, L ⊆ H ∧ L.Infinite ∧ ∃ K, 0 < K ∧ K + 2 ≤ R ∧ ∀ z w,
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ L b) p z →
      (exactGame N blue).kind z = .terminal w →
        ((z.position.board.get side).bodyLabels.getD (i - 1) ∅).card = K := by
  obtain ⟨L, hLH, hL, value, hvalue⟩ :=
    Concrete.terminal_finite_uniformization_fixed_bound hHN hH b σ
      (futureBodyColor side i R) p
  have pathH {z : Concrete.Hist N}
      (hpz : Relation.ReflTransGen ((exactGame N blue).FollowStep σ L b) p z) :
      Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p z :=
    Relation.ReflTransGen.mono (fun _ _ hs =>
      FiniteResponseGame.FollowStep.mono (exactGame N blue) hLH (fun _ => le_rfl) hs) _ _ hpz
  have fixed (z : Concrete.Hist N) (w : Bool)
      (hpz : Relation.ReflTransGen ((exactGame N blue).FollowStep σ L b) p z)
      (hz : (exactGame N blue).kind z = .terminal w) :
      ((z.position.board.get side).bodyLabels.getD (i - 1) ∅).card = value.val := by
    have hb := (hbound z w (pathH hpz) hz).2
    have hle : ((z.position.board.get side).bodyLabels.getD (i - 1) ∅).card ≤ R := by omega
    have hc := congrArg Fin.val (hvalue z w hpz hz)
    simpa only [futureBodyColor, min_eq_left hle] using hc
  obtain ⟨z, w, hpz, hz⟩ := (exactGame N blue).terminal_reachable_of_infinite
    (hLH.trans hHN) hL b σ p
  have hb := hbound z w (pathH hpz) hz
  rw [fixed z w hpz hz] at hb
  exact ⟨L, hLH, hL, value.val, hb.1, hb.2, fixed⟩

theorem localized_body_request_size {N H : Set ℕ}
    (hHN : H ⊆ N) (hH : H.Infinite) (blue : SimpleGraph G)
    {b : Concrete.Hist N → ℕ} {σ : (exactGame N blue).ArchitectStrategy}
    (p q : Concrete.Hist N) (side : Bool) {i K d : ℕ}
    (hwin : (exactGame N blue).ArchitectWins H b σ p)
    (hfixed : ∀ z w, Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p z →
      (exactGame N blue).kind z = .terminal w →
        ((z.position.board.get side).bodyLabels.getD (i - 1) ∅).card = K)
    (hpq : Relation.ReflTransGen ((exactGame N blue).FollowStep σ H b) p q)
    (hp : q.position.pending = some ⟨side, .advance d⟩)
    (hm : (q.position.board.get side).markerEvent = true)
    (hi : (q.position.board.get side).bodyLabels.length + 1 = i) : d = K := by
  obtain ⟨z, hqz, hz⟩ := (hwin.of_reachable (exactGame N blue) hpq).exists_terminal
    (exactGame N blue) hHN hH
  have hc := reachable_body_label_card blue q z side hp hm hqz hz
  have hf := hfixed z true (hpq.trans hqz) hz
  rw [← hi, Nat.add_sub_cancel] at hf
  exact hc.symm.trans hf

#print axioms bounded_future_body_localization
#print axioms localized_body_request_size

end Erdos591.Positive.Game.Payoff
