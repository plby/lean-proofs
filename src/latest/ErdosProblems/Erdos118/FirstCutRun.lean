import ErdosProblems.Erdos118.FirstCutFronts
import ErdosProblems.Erdos118.ProjectionBounds
import ErdosProblems.Erdos118.PreparedRelays

/-!
Execute a decoded first joint cut using actual response members and the
original guard alphabet. This is the initial two-step part of the still
unconstructed complete pair play.
-/

namespace Erdos118.FirstCutRun

open Negative Negative.Exact LabelledExtensions LabelledFrames LabelCoarsening
open CutIndices DecisionStates AdaptiveGame ReservedResponses

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
    (s : G2) (U T : Stem) (hU : U.done.length = U.root) {ys : List ℕ}
    (J : Projection (LabelledRealization.output hL s).stem
      (LabelledRealization.output hL s).full ys U hU)
    (P : Pending) (hcut : JointCut P U hU T.root) (hexact : ExactAnnotations U T) :
    ∃ F : Pending, F.position = P.position ∧ ExactSlots.Exact (.leaf F) ∧
      ConservativeRuns.Run H (GraphPayoff.payoff B o)
        (.initial, .initial) (.leaf F, .initial) := by
  obtain ⟨k, n, A, Q, hA, hQ, hExact⟩ := FirstCutFronts.first_fronts P U T hU hcut hexact
  let D := ofRoot A
  have hUL : ∀ x ∈ U.decorated, x ∈ L :=
    fun x hx ↦ LabelledRealization.output_supported hL s x (J.decorated.subset hx)
  have hPL : ∀ x ∈ P.position.decorated, x ∈ L := by
    intro x hx
    apply hUL x
    apply (List.takeWhile_sublist (fun z ↦ decide (z < T.root))).subset
    change x ∈ PrefixRealization.below T.root U.decorated
    exact hcut.decorated ▸ hx
  have hAL : ∀ x ∈ A.stem.decorated, x ∈ L := by
    intro x hx
    rw [hA] at hx
    exact hPL x (List.mem_append_left _ hx)
  have hQL : ∀ x ∈ BodyResponses.newWord Q.position, x ∈ L := by
    intro x hx
    rw [hQ] at hx
    exact hPL x (List.mem_append_right _ hx)
  have hC : U.rootLabel = P.position.stem.rootLabel :=
    Option.some.inj (hcut.labels.root _ rfl)
  have hAC : A.stem.rootLabel = U.rootLabel := (congrArg Stem.rootLabel hA).trans hC.symm
  obtain ⟨qr, hqr, hkr, hqrC⟩ := ProjectionBounds.projection_root_command
    hL hLK b hb hpos htail s J
  have hnqr : k + 1 ≤ qr := by rw [← A.label_length, hAC]; exact hkr
  have hCne : A.stem.rootLabel ≠ [] := by
    intro he
    have hl := A.label_length
    simp [he] at hl
  have hqrA : ∀ x ∈ A.stem.decorated, qr < x :=
    after_nonempty_prefix _ _ A.stem.increasing hCne qr (by rwa [hAC])
  have rootBounds : ∀ x ∈ A.stem.decorated,
      pairBound (.initial, .initial) < x ∧
        ConservativeRuns.leftGuard H (GraphPayoff.payoff B o) (.initial, .initial) (k + 1) < x ∧
        ConservativeRuns.rightGuard H (GraphPayoff.payoff B o)
          (.initial, .initial) (k + 1) < x := by
    intro x hx
    exact hguard (.initial, .initial) (by simp [State.decorated]) (by simp [State.decorated])
      (k + 1) qr hqr hnqr x (hLK (hAL x hx)) (hqrA x hx)
      (by simp [State.decorated]) (by simp [State.decorated])
  have hrootStep : ConservativeRuns.Step H (GraphPayoff.payoff B o)
      (.initial, .initial) (.body D, .initial) := by
    let c := pairBound (.initial, .initial)
    have hc : ∀ x ∈ A.stem.decorated, c < x := fun x hx ↦ (rootBounds x hx).1
    let a := rootMember c A hc
    have haH : (↑a.1 : Set ℕ) ⊆ H :=
      fun x hx ↦ hKH (hLK (hAL x (List.mem_toFinset.mp hx)))
    have hag : ∀ x ∈ a.1,
        ConservativeRuns.leftGuard H (GraphPayoff.payoff B o) (.initial, .initial) (k + 1) < x :=
      fun x hx ↦ (rootBounds x (List.mem_toFinset.mp hx)).2.1
    have hs := ConservativeRuns.Step.left (.initial, .initial) (k + 1)
      (rootResponse k c) rfl rfl a haH hag
    simpa only [a, rootMember_result] using hs
  have hlabels : P.position.bodyLabels <+: U.bodyLabels := hcut.labels.bodies
  have hiP : P.position.stem.done.length < P.position.bodyLabels.length := by
    simp [Position.bodyLabels, Stem.bodyLabels]
  have hiU := hiP.trans_le hlabels.length_le
  have hE : U.bodyLabels[P.position.stem.done.length] = P.position.label := by
    rw [← hlabels.getElem hiP]
    simp [Position.bodyLabels, Stem.bodyLabels]
  have hEne : U.bodyLabels[P.position.stem.done.length] ≠ [] := by
    rw [hE]
    exact List.ne_nil_of_mem P.leafSelected
  have hn : n = U.bodyLabels[P.position.stem.done.length].length - 1 := by
    have hl := Q.label_length
    rw [hQ] at hl
    rw [hE]
    omega
  have hbodyCommand := ProjectionBounds.projection_body_command hL s J
    P.position.stem.done.length hiU hEne
  have hanchor : ∃ q ∈ K, n ≤ q ∧ ∀ x ∈ Q.position.label, q < x := by
    rcases hbodyCommand with hz | ⟨q, hq, hnq, hqE⟩
    · refine ⟨b, hb, ?_, ?_⟩
      · rw [hn, hz]
        exact Nat.zero_le _
      · intro x hx
        exact htail x (hQL x (List.mem_append_left _ hx))
    · refine ⟨q, hLK hq, ?_, ?_⟩
      · rw [hn]
        exact hnq
      · intro x hx
        apply hqE x
        rw [hE, ← hQ]
        exact hx
  obtain ⟨qb, hqb, hnqb, hqbE⟩ := hanchor
  have hQne : Q.position.label ≠ [] := by
    intro he
    have hl := Q.label_length
    simp [he] at hl
  have hqbQ : ∀ x ∈ BodyResponses.newWord Q.position, qb < x :=
    after_nonempty_prefix _ _ (BodyResponses.newWord_pairwise Q.position) hQne qb hqbE
  have hbefore : ∀ z ∈ A.stem.decorated,
      ∀ x ∈ BodyResponses.newWord Q.position, z < x := by
    intro z hz x hx
    rw [hA] at hz
    rw [hQ] at hx
    exact (List.pairwise_append.mp P.position.increasing).2.2 z hz x hx
  have bodyBounds : ∀ x ∈ BodyResponses.newWord Q.position,
      pairBound (.body D, .initial) < x ∧
        ConservativeRuns.leftGuard H (GraphPayoff.payoff B o) (.body D, .initial) n < x ∧
        ConservativeRuns.rightGuard H (GraphPayoff.payoff B o) (.body D, .initial) n < x := by
    intro x hx
    exact hguard (.body D, .initial) (fun z hz ↦ hLK (hAL z hz))
      (by simp [State.decorated]) n qb hqb hnqb x (hLK (hQL x hx)) (hqbQ x hx)
      (fun z hz ↦ hbefore z hz x hx) (by simp [State.decorated])
  have hbodyStep := PreparedRelays.body_step B o false D .initial Q rfl
    (fun x hx ↦ hKH (hLK (hQL x hx))) (fun x hx ↦ (bodyBounds x hx).1)
    (fun x hx ↦ (bodyBounds x hx).2.1)
  exact ⟨applyBody D Q, hQ, hExact, (Relation.ReflTransGen.single hrootStep).tail hbodyStep⟩

end Erdos118.FirstCutRun
