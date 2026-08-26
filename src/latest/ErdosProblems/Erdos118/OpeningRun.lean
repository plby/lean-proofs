import ErdosProblems.Erdos118.OpeningFronts
import ErdosProblems.Erdos118.NextBodyRun

/-!
An actual guarded root/body opening on either side opposite an old state.
Both command anchors come from the target's actual annotation projection.
-/

namespace Erdos118.OpeningRun

open Negative Negative.Exact LabelledExtensions LabelledFrames LabelCoarsening
open CutIndices DecisionStates AdaptiveGame ReservedResponses
open PrefixRealization (below)

private theorem after_nonempty_prefix (C v : List ℕ) (hinc : (C ++ v).Pairwise (· < ·))
    (hne : C ≠ []) (q : ℕ) (hq : ∀ x ∈ C, q < x) : ∀ x ∈ C ++ v, q < x := by
  obtain ⟨c, C, rfl⟩ := List.exists_cons_of_ne_nil hne
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact hq x hx
  · exact (hq c (List.mem_cons_self ..)).trans
      ((List.pairwise_append.mp hinc).2.2 c (List.mem_cons_self ..) x hx)

theorem initial {H K L : Set ℕ} (hL : L.Infinite) (hLK : L ⊆ K) (hKH : K ⊆ H)
    (B : SimpleGraph G) (o : GraphPayoff.Orientation)
    (hguard : FiniteGuards.Sparse H K (GraphPayoff.payoff B o))
    (b : ℕ) (hb : b ∈ K) (hpos : 1 ≤ b) (htail : ∀ x ∈ L, b < x)
    (s : G2) (S T : Stem) (hS : S.done.length = S.root) {ys : List ℕ}
    (J : Projection (LabelledRealization.output hL s).stem
      (LabelledRealization.output hL s).full ys S hS)
    (P : Pending) {z : ℕ} (hP : JointCut P S hS z) (hexact : ExactAnnotations S T)
    (hmin : ∀ i j, Cut S T i j → P.position.stem.done.length ≤ i ∧
      (P.position.stem.done.length = i → P.position.entries.length ≤ j))
    (right : Bool) (W : State)
    (hallowed : allowedSide (PreparedRelays.pair right .initial W) right = true)
    (hWK : ∀ x ∈ W.decorated, x ∈ K)
    (hbefore : ∀ y ∈ W.decorated, ∀ x ∈ S.decorated, y < x) :
    ∃ F : Pending, F.position = P.position ∧ ExactSlots.Exact (.leaf F) ∧
      ConservativeRuns.Run H (GraphPayoff.payoff B o)
        (PreparedRelays.pair right .initial W) (PreparedRelays.pair right (.leaf F) W) := by
  obtain ⟨k, n, A, Q, hA, hQ, hExact⟩ := OpeningFronts.fronts_of_minimal S T hS P hP hexact hmin
  let D := ofRoot A
  let F := applyBody D Q
  have hFcut : JointCut F S hS z := InitialSplit.jointCut_of_position_eq hQ hP
  have hSL : ∀ x ∈ S.decorated, x ∈ L :=
    fun x hx ↦ LabelledRealization.output_supported hL s x (J.decorated.subset hx)
  have hPS : ∀ x ∈ P.position.decorated, x ∈ S.decorated := by
    intro x hx
    apply (List.takeWhile_sublist (fun a ↦ decide (a < z))).subset
    change x ∈ below z S.decorated
    exact hP.decorated ▸ hx
  have hAS : ∀ x ∈ A.stem.decorated, x ∈ S.decorated := by
    intro x hx
    rw [hA] at hx
    exact hPS x (List.mem_append_left _ hx)
  have hQS : ∀ x ∈ BodyResponses.newWord Q.position, x ∈ S.decorated := by
    intro x hx
    rw [hQ] at hx
    exact hPS x (List.mem_append_right _ hx)
  have hAL : ∀ x ∈ A.stem.decorated, x ∈ L := fun x hx ↦ hSL x (hAS x hx)
  have hQL : ∀ x ∈ BodyResponses.newWord Q.position, x ∈ L := fun x hx ↦ hSL x (hQS x hx)
  have hC : S.rootLabel = P.position.stem.rootLabel :=
    Option.some.inj (hP.labels.root _ rfl)
  have hAC : A.stem.rootLabel = S.rootLabel := (congrArg Stem.rootLabel hA).trans hC.symm
  obtain ⟨qr, hqr, hkr, hqrC⟩ := ProjectionBounds.projection_root_command
    hL hLK b hb hpos htail s J
  have hnqr : k + 1 ≤ qr := by rw [← A.label_length, hAC]; exact hkr
  have hCne : A.stem.rootLabel ≠ [] := by
    intro he
    have hl := A.label_length
    simp [he] at hl
  have hqrA : ∀ x ∈ A.stem.decorated, qr < x :=
    after_nonempty_prefix _ _ A.stem.increasing hCne qr (by rwa [hAC])
  let R := PreparedRelays.pair right .initial W
  have hRK : (∀ x ∈ R.1.decorated, x ∈ K) ∧ (∀ x ∈ R.2.decorated, x ∈ K) := by
    cases right <;> simp_all [R, PreparedRelays.pair, State.decorated]
  have hrootBounds : ∀ x ∈ A.stem.decorated,
      pairBound R < x ∧ ConservativeRuns.leftGuard H (GraphPayoff.payoff B o) R (k + 1) < x ∧
        ConservativeRuns.rightGuard H (GraphPayoff.payoff B o) R (k + 1) < x := by
    intro x hx
    apply hguard R hRK.1 hRK.2 (k + 1) qr hqr hnqr x (hLK (hAL x hx)) (hqrA x hx)
    · cases right <;> simp_all [R, PreparedRelays.pair, State.decorated]
    · cases right <;> simp_all [R, PreparedRelays.pair, State.decorated]
  have hrootStep : ConservativeRuns.Step H (GraphPayoff.payoff B o)
      R (PreparedRelays.pair right (.body D) W) := by
    have hc : ∀ x ∈ A.stem.decorated, pairBound R < x := fun x hx ↦ (hrootBounds x hx).1
    let a := rootMember (pairBound R) A hc
    have haH : (↑a.1 : Set ℕ) ⊆ H :=
      fun x hx ↦ hKH (hLK (hAL x (List.mem_toFinset.mp hx)))
    have ha : (rootResponse k (pairBound R)).result a = .body D := rootMember_result ..
    cases right with
    | false =>
      have hs := ConservativeRuns.Step.left R (k + 1) (rootResponse k (pairBound R))
        hallowed rfl a haH (fun x hx ↦ (hrootBounds x (List.mem_toFinset.mp hx)).2.1)
      rw [ha] at hs
      exact hs
    | true =>
      have hs := ConservativeRuns.Step.right R (k + 1) (rootResponse k (pairBound R))
        hallowed rfl a haH (fun x hx ↦ (hrootBounds x (List.mem_toFinset.mp hx)).2.2)
      rw [ha] at hs
      exact hs
  obtain ⟨qb, hqb, hnqb, hqbQ⟩ := NextBodyRun.projection_body_anchor hL hLK b hb htail s J F hFcut
  have hn : n ≤ qb := by
    change Q.position.label.length - 1 ≤ qb at hnqb
    have hl := Q.label_length
    omega
  have hown : ∀ y ∈ A.stem.decorated, ∀ x ∈ BodyResponses.newWord Q.position, y < x :=
    (List.pairwise_append.mp ((BodyResponses.setup_decorated Q) ▸ Q.position.increasing)).2.2
  let R' := PreparedRelays.pair right (.body D) W
  have hR'K : (∀ x ∈ R'.1.decorated, x ∈ K) ∧ (∀ x ∈ R'.2.decorated, x ∈ K) := by
    have hAK : ∀ x ∈ A.stem.decorated, x ∈ K := fun x hx ↦ hLK (hAL x hx)
    cases right <;> simp_all [R', D, PreparedRelays.pair, State.decorated, ofRoot]
  have hbodyBounds : ∀ x ∈ BodyResponses.newWord Q.position,
      pairBound R' < x ∧ ConservativeRuns.leftGuard H (GraphPayoff.payoff B o) R' n < x ∧
        ConservativeRuns.rightGuard H (GraphPayoff.payoff B o) R' n < x := by
    intro x hx
    apply hguard R' hR'K.1 hR'K.2 n qb hqb hn x (hLK (hQL x hx)) (hqbQ x hx)
    · cases right <;> simp_all [R', D, PreparedRelays.pair, State.decorated, ofRoot]
    · cases right <;> simp_all [R', D, PreparedRelays.pair, State.decorated, ofRoot]
  have hbodyAllowed : allowedSide R' right = true := by
    cases right <;> cases W <;> simp_all [R', PreparedRelays.pair, allowedSide]
  have hg : ∀ x ∈ BodyResponses.newWord Q.position,
      PreparedRelays.guard H B o right D W n < x := by
    intro x hx
    cases right with
    | false => exact (hbodyBounds x hx).2.1
    | true => exact (hbodyBounds x hx).2.2
  have hbodyStep := PreparedRelays.body_step B o right D W Q hbodyAllowed
    (fun x hx ↦ hKH (hLK (hQL x hx))) (fun x hx ↦ (hbodyBounds x hx).1) hg
  exact ⟨F, hQ, hExact, (Relation.ReflTransGen.single hrootStep).tail hbodyStep⟩

end Erdos118.OpeningRun
