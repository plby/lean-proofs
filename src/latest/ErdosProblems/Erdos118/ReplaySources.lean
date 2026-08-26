import ErdosProblems.Erdos118.BodyReplay
import ErdosProblems.Erdos118.StemReplay

/-!
Two concrete sources of the target body certificate: an actual uniform
root front, or an actual uniform next-body front with an old fixed prefix.
Both resolve through the existing exact response decoders.
-/

namespace Erdos118.ReplaySources

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns ReservedResponses BoundaryRelays PreparedRelays

inductive Source (H : Set ℕ) (B : SimpleGraph G) (o : GraphPayoff.Orientation)
    (right : Bool) (T : Pending) where
  | root (k b : ℕ)
      (certificate : ∀ A : RootResponses.Setup k,
        (∀ x ∈ A.stem.decorated, x ∈ H) → (∀ x ∈ A.stem.decorated, b < x) →
        Blue H B o right (.body (ofRoot A)) (.leaf T)) : Source H B o right T
  | stem (P : Pending) (c : ℕ) (hR : P.roots = [c]) (hL : P.leaves = []) (b : ℕ)
      (certificate : ∀ Q : Stem, ∀ v : List ℕ,
        Q.root = P.position.stem.root → Q.done.length = c - 1 →
        Q.ordinary = P.position.ordinary ++ v →
        (∀ x ∈ v, x ∈ H) → (∀ x ∈ v, b < x) →
        ∃ A : StemResponses.Setup P.position (c - 1), A.newWord = v ∧
          A.stem.ordinary = Q.ordinary ∧
          Blue H B o right (.body (ofStem P c [] hR A)) (.leaf T)) : Source H B o right T

def Source.bound {H : Set ℕ} {B : SimpleGraph G} {o : GraphPayoff.Orientation}
    {right : Bool} {T : Pending} : Source H B o right T → ℕ
  | .root _ b _ => b
  | .stem _ _ _ _ b _ => b

structure RootData (H : Set ℕ) (b k : ℕ) (S : Stem) where
  reserve : Reserve S.rootLabel S.root k
  reserveFresh : ∀ x ∈ reserve.label, x ∈ H ∧ b < x
  ordinaryFresh : ∀ x ∈ S.ordinary, x ∈ H ∧ b < x

structure StemData (H : Set ℕ) (b : ℕ) (P : Pending) (c : ℕ) (S : Stem) : Type where
  root : S.root = P.position.stem.root
  last : S.rootLabel.getLastD 0 = c
  suffix : ∃ v, S.ordinary = P.position.ordinary ++ v ∧ ∀ x ∈ v, x ∈ H ∧ b < x

def Source.Data {H : Set ℕ} {B : SimpleGraph G} {o : GraphPayoff.Orientation}
    {right : Bool} {T : Pending} : Source H B o right T → Stem → Type
  | .root k b _, S => RootData H b k S
  | .stem P c _ _ b _, S => StemData H b P c S

def Source.Data.transport {H : Set ℕ} {B : SimpleGraph G} {o : GraphPayoff.Orientation}
    {right : Bool} {T : Pending} {I : Source H B o right T} {S : Stem}
    (M : I.Data S) (U : Stem) (hr : U.root = S.root) (hC : U.rootLabel = S.rootLabel)
    (v : List ℕ) (hv : U.ordinary = S.ordinary ++ v)
    (hf : ∀ x ∈ v, x ∈ H ∧ I.bound < x) : I.Data U := by
  cases I with
  | root k b certificate =>
    exact
      { reserve :=
          { label := M.reserve.label, card := M.reserve.card, increasing := M.reserve.increasing
            first := by rw [hC]; exact M.reserve.first
            below := by rw [hr]; exact M.reserve.below
            shared := by intro x; rw [hC]; exact M.reserve.shared x }
        reserveFresh := M.reserveFresh
        ordinaryFresh := by
          rw [hv]
          intro x hx
          exact (List.mem_append.mp hx).elim (M.ordinaryFresh x) (hf x) }
  | stem P c hR hL b certificate =>
    exact
      { root := hr.trans M.root
        last := by rw [hC]; exact M.last
        suffix := by
          obtain ⟨w, hw, hwf⟩ := M.suffix
          exact ⟨w ++ v, by rw [hv, hw, List.append_assoc],
            fun x hx ↦ (List.mem_append.mp hx).elim (hwf x) (hf x)⟩ }

theorem body_command {H : Set ℕ} (B : SimpleGraph G) (o : GraphPayoff.Orientation)
    (right : Bool) (E : BodyDecision) (T : Pending)
    (hblue : Blue H B o right (.body E) (.leaf T)) :
    CommandBlue H B o right (.body E) (.leaf T) := by
  cases right with
  | false =>
    rcases blue_command (GraphPayoff.payoff B o) (.body E, .leaf T) rfl hblue with hl | hr
    · exact hl
    · obtain ⟨n, R, hs, _⟩ := hr
      simp [allowedSide] at hs
  | true =>
    rcases blue_command (GraphPayoff.payoff B o) (.leaf T, .body E) rfl hblue with hl | hr
    · obtain ⟨n, R, hs, _⟩ := hl
      simp [allowedSide] at hs
    · exact hr

theorem Source.resolve {H : Set ℕ} {B : SimpleGraph G} {o : GraphPayoff.Orientation}
    {right : Bool} {T : Pending} (I : Source H B o right T)
    (D : BodyDecision) (M : I.Data D.stem) (hD : ExactSlots.Exact (.body D)) (hR : D.roots = []) :
    ∃ E : BodyDecision, E.stem.ordinary = D.stem.ordinary ∧
      CommandBlue H B o right (.body E) (.leaf T) := by
  cases I with
  | root k b certificate =>
    let A := rootAtLastBody D hD hR M.reserve
    have hf := rootAtLastBody_supported D hD hR M.reserve M.reserveFresh M.ordinaryFresh
    have hb := certificate A (fun x hx ↦ (hf x hx).1) (fun x hx ↦ (hf x hx).2)
    exact ⟨ofRoot A, rootAtLastBody_ordinary D hD hR M.reserve,
      body_command B o right (ofRoot A) T hb⟩
  | stem P c hPR hPL b certificate =>
    have hcount : D.stem.done.length = c - 1 := by
      have h := body_last_root D hD hR
      rw [M.last] at h
      omega
    obtain ⟨v, hv, hvf⟩ := M.suffix
    obtain ⟨A, _, hord, hb⟩ := certificate D.stem v M.root hcount hv
      (fun x hx ↦ (hvf x hx).1) (fun x hx ↦ (hvf x hx).2)
    exact ⟨ofStem P c [] hPR A, hord, body_command B o right (ofStem P c [] hPR A) T hb⟩

def Source.Exact {H : Set ℕ} {B : SimpleGraph G} {o : GraphPayoff.Orientation}
    {right : Bool} {T : Pending} : Source H B o right T → Prop
  | .root _ _ _ => True
  | .stem P _ _ _ _ _ => ExactSlots.Exact (.leaf P)

theorem Source.resolve_exact {H : Set ℕ} {B : SimpleGraph G} {o : GraphPayoff.Orientation}
    {right : Bool} {T : Pending} (I : Source H B o right T) (hI : I.Exact)
    (D : BodyDecision) (M : I.Data D.stem) (hD : ExactSlots.Exact (.body D)) (hR : D.roots = []) :
    ∃ E : BodyDecision, E.stem.ordinary = D.stem.ordinary ∧
      ExactSlots.Exact (.body E) ∧ CommandBlue H B o right (.body E) (.leaf T) := by
  cases I with
  | root k b certificate =>
    let A := rootAtLastBody D hD hR M.reserve
    have hf := rootAtLastBody_supported D hD hR M.reserve M.reserveFresh M.ordinaryFresh
    have hb := certificate A (fun x hx ↦ (hf x hx).1) (fun x hx ↦ (hf x hx).2)
    exact ⟨ofRoot A, rootAtLastBody_ordinary D hD hR M.reserve,
      ExactSlots.step_exact (DecisionStates.Step.root A) trivial,
      body_command B o right (ofRoot A) T hb⟩
  | stem P c hPR hPL b certificate =>
    have hcount : D.stem.done.length = c - 1 := by
      have h := body_last_root D hD hR
      rw [M.last] at h
      omega
    obtain ⟨v, hv, hvf⟩ := M.suffix
    obtain ⟨A, _, hord, hb⟩ := certificate D.stem v M.root hcount hv
      (fun x hx ↦ (hvf x hx).1) (fun x hx ↦ (hvf x hx).2)
    exact ⟨ofStem P c [] hPR A, hord,
      ExactSlots.step_exact (DecisionStates.Step.nextBody P c [] hPR hPL A) hI,
      body_command B o right (ofStem P c [] hPR A) T hb⟩

end Erdos118.ReplaySources
