import ErdosProblems.Erdos118.JointFinish

/-!
Exact aligned frames have comparable remaining lists. Matching response
kinds yield actual paired moves and strictly decrease a primary frame's
lexicographic number of unused roots and leaves. Mismatches are not excluded.
-/

namespace Erdos118.JointAlignment

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns PreparedRelays

def Comparable (C D : List ℕ) : Prop := C <+: D ∨ D <+: C

structure Aligned (P Q : Pending) : Prop where
  ordinary : P.position.ordinary = Q.position.ordinary
  exactLeft : ExactSlots.Exact (.leaf P)
  exactRight : ExactSlots.Exact (.leaf Q)
  roots : Comparable P.position.stem.rootLabel Q.position.stem.rootLabel
  leaves : Comparable P.position.label Q.position.label

inductive Kind
  | leaf | body | finish
  deriving DecidableEq

def kind (P : Pending) : Kind :=
  match P.leaves, P.roots with
  | _ :: _, _ => .leaf
  | [], _ :: _ => .body
  | [], [] => .finish

def Last (P : Pending) : Prop := P.roots = [] ∧ P.leaves = []

theorem kind_eq_finish_iff (P : Pending) : kind P = .finish ↔ Last P := by
  cases hL : P.leaves <;> cases hR : P.roots <;> simp [kind, Last, hL, hR]

theorem Aligned.remaining {P Q : Pending} (h : Aligned P Q) :
    Comparable P.roots Q.roots ∧ Comparable P.leaves Q.leaves := by
  have hc := JointMoves.ordinary_components P.position Q.position h.ordinary
  constructor
  · rw [h.exactLeft.1, h.exactRight.1, hc.2.2.1]
    rcases h.roots with hl | hr
    · exact Or.inl (hl.filter _)
    · exact Or.inr (hr.filter _)
  · rw [h.exactLeft.2, h.exactRight.2, hc.2.2.2.2]
    rcases h.leaves with hl | hr
    · exact Or.inl (hl.filter _)
    · exact Or.inr (hr.filter _)

private theorem comparable_head {a b : ℕ} {C D : List ℕ}
    (h : Comparable (a :: C) (b :: D)) : a = b := by
  rcases h with h | h
  · exact (List.cons_prefix_cons.mp h).1
  · exact (List.cons_prefix_cons.mp h).1.symm

theorem Aligned.next_cases {P Q : Pending} (h : Aligned P Q) (hk : kind P = kind Q) :
    (∃ j : ℕ, ∃ p q : List ℕ, P.leaves = j :: p ∧ Q.leaves = j :: q) ∨
      (P.leaves = [] ∧ Q.leaves = [] ∧
        ∃ c : ℕ, ∃ p q : List ℕ, P.roots = c :: p ∧ Q.roots = c :: q) ∨
      (Last P ∧ Last Q) := by
  have hr := h.remaining
  cases hPL : P.leaves with
  | cons j p =>
    cases hQL : Q.leaves with
    | nil => cases hQR : Q.roots <;> simp [kind, hPL, hQL, hQR] at hk
    | cons i q =>
      have he : j = i := comparable_head (by simpa only [hPL, hQL] using hr.2)
      subst i
      exact Or.inl ⟨j, p, q, rfl, rfl⟩
  | nil =>
    cases hQL : Q.leaves with
    | cons i q => cases hPR : P.roots <;> simp [kind, hPL, hQL, hPR] at hk
    | nil =>
      cases hPR : P.roots with
      | nil =>
        cases hQR : Q.roots with
        | nil => exact Or.inr (Or.inr ⟨⟨hPR, hPL⟩, ⟨hQR, hQL⟩⟩)
        | cons c q => simp [kind, hPL, hQL, hPR, hQR] at hk
      | cons c p =>
        cases hQR : Q.roots with
        | nil => simp [kind, hPL, hQL, hPR, hQR] at hk
        | cons d q =>
          have he : c = d := comparable_head (by simpa only [hPR, hQR] using hr.1)
          subst d
          exact Or.inr (Or.inl ⟨rfl, rfl, c, p, q, rfl, rfl⟩)

def size (P : Pending) : ℕ × ℕ := (P.roots.length, P.leaves.length)

def Decreases (P' P : Pending) : Prop := Prod.Lex (· < ·) (· < ·) (size P') (size P)

private theorem run_exact_side {K : Set ℕ} (B : SimpleGraph G)
    (o : GraphPayoff.Orientation) (right : Bool) (P Q : Pending) (X : State)
    (h : ConservativeRuns.Run K (GraphPayoff.payoff B o)
      (pair right (.leaf P) X) (pair right (.leaf Q) X))
    (hP : ExactSlots.Exact (.leaf P)) : ExactSlots.Exact (.leaf Q) := by
  cases right with
  | false => exact ExactSlots.run_exact_left h hP
  | true => exact ExactSlots.run_exact_right h hP

private theorem run_root_side {K : Set ℕ} (B : SimpleGraph G)
    (o : GraphPayoff.Orientation) (right : Bool) (P Q : Pending) (X : State)
    (h : ConservativeRuns.Run K (GraphPayoff.payoff B o)
      (pair right (.leaf P) X) (pair right (.leaf Q) X)) :
    Q.position.stem.rootLabel = P.position.stem.rootLabel := by
  have hl : DecisionStates.LabelsExtend (.leaf P) (.leaf Q) := by
    cases right with
    | false => exact (SkippedCuts.run_extensions h).1.labels
    | true => exact (SkippedCuts.run_extensions h).2.labels
  exact Option.some.inj (hl.root P.position.stem.rootLabel rfl)

theorem Aligned.advance {H K : Set ℕ} (hK : K.Infinite) (hKH : K ⊆ H)
    (B : SimpleGraph G) (o : GraphPayoff.Orientation) (r s : Bool)
    (P Q : Pending) (X Y : State) (h : Aligned P Q) (hk : kind P = kind Q)
    (hn : ¬ Last P) (hp : CommandBlue H B o r (.leaf P) X)
    (hq : CommandBlue H B o s (.leaf Q) Y) (d : ℕ) :
    ∃ P' Q' : Pending, Aligned P' Q' ∧
      ConservativeRuns.Run K (GraphPayoff.payoff B o) (pair r (.leaf P) X) (pair r (.leaf P') X) ∧
      ConservativeRuns.Run K (GraphPayoff.payoff B o) (pair s (.leaf Q) Y) (pair s (.leaf Q') Y) ∧
      Blue H B o r (.leaf P') X ∧ Blue H B o s (.leaf Q') Y ∧
      OtherBlue H B o r (.leaf P') X ∧ OtherBlue H B o s (.leaf Q') Y ∧ Decreases P' P := by
  rcases h.next_cases hk with ⟨j, p, q, hP, hQ⟩ | ⟨hPL, hQL, c, p, q, hP, hQ⟩ | hlast
  · obtain ⟨A, C, _, hord, hsP, hsQ, hbP, hbQ, hhP, hhQ, _⟩ :=
      JointMoves.respond_leaves hK hKH B o r s P Q X Y h.ordinary j p q hP hQ hp hq d
    let P' := LeafResponses.toPending P j p hP A
    let Q' := LeafResponses.toPending Q j q hQ C
    have haligned : Aligned P' Q' :=
      { ordinary := hord
        exactLeft := ExactSlots.step_exact (DecisionStates.Step.leaf P j p hP A) h.exactLeft
        exactRight := ExactSlots.step_exact (DecisionStates.Step.leaf Q j q hQ C) h.exactRight
        roots := h.roots, leaves := h.leaves }
    refine ⟨P', Q', haligned, Relation.ReflTransGen.single hsP,
      Relation.ReflTransGen.single hsQ, hbP, hbQ, hhP, hhQ, ?_⟩
    apply Prod.Lex.right
    change p.length < P.leaves.length
    simp [hP]
  · obtain ⟨P', Q', hPR, _, hord, hlabels, hrP, hrQ, hbP, hbQ, hhP, hhQ, _⟩ :=
      JointMoves.respond_next_bodies hK hKH B o r s P Q X Y h.ordinary c p q hP hQ hPL hQL hp hq d
    have hrootP := run_root_side B o r P P' X hrP
    have hrootQ := run_root_side B o s Q Q' Y hrQ
    have haligned : Aligned P' Q' :=
      { ordinary := hord
        exactLeft := run_exact_side B o r P P' X hrP h.exactLeft
        exactRight := run_exact_side B o s Q Q' Y hrQ h.exactRight
        roots := by rw [hrootP, hrootQ]; exact h.roots
        leaves := hlabels }
    refine ⟨P', Q', haligned, hrP, hrQ, hbP, hbQ, hhP, hhQ, ?_⟩
    apply Prod.Lex.left
    simp [hPR, hP]
  · exact (hn hlast.1).elim

end Erdos118.JointAlignment
