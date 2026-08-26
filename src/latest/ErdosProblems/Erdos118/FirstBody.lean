import ErdosProblems.Erdos118.RootOverlap
import ErdosProblems.Erdos118.RootForkTriangle
import ErdosProblems.Erdos118.InsideSingleton

/-!
Uniformly singleton first-body certificates give an actual initial root
overlap and a triangle. Nash--Williams then leaves positive first-body
parameters on an infinite root pool, retaining blue certificates on H.
The remaining positive-parameter case is not excluded here.
-/

namespace Erdos118.FirstBody

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns

def Certificate (H : Set ℕ) (B : SimpleGraph G) (D : BodyDecision) (k : ℕ) : Prop :=
  ∃ b : ℕ, ∀ A : BodyResponses.Setup D.stem k,
    (∀ x ∈ BodyResponses.newWord A.position, x ∈ H) →
    (∀ x ∈ BodyResponses.newWord A.position, b < x) →
    RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf (applyBody D A), .initial)) true

theorem certificate_exists {H : Set ℕ} (B : SimpleGraph G) (D : BodyDecision)
    (hb : RamseyGame.Outcome H (GraphPayoff.game B .inside (.body D, .initial)) true) :
    ∃ k : ℕ, Certificate H B D k := by
  rcases blue_command (GraphPayoff.payoff B .inside) (.body D, .initial) rfl hb with hl | hr
  · exact BlueReservations.left_body_setups (GraphPayoff.payoff B .inside) D .initial hl
  · obtain ⟨n, R, hs, _⟩ := hr
    simp [allowedSide] at hs

theorem no_uniform_singleton {H L : Set ℕ} (hH : H.Infinite) (hL : L.Infinite)
    (B : SimpleGraph G) (hB : B.CliqueFree 3)
    (hinit : RamseyGame.Outcome H (GraphPayoff.game B .inside (.initial, .initial)) true)
    (k b : ℕ) (hk : 0 < k)
    (hzero : ∀ A : RootResponses.Setup k, (∀ x ∈ A.stem.decorated, x ∈ L ∧ b < x) →
      Certificate H B (ofRoot A) 0) : False := by
  obtain ⟨A, C, c, rest, hord, hnext, hlast, hA, hC⟩ := RootOverlap.root_setups hL b k hk
  obtain ⟨bA, hbA⟩ := hzero A hA
  obtain ⟨bC, hbC⟩ := hzero C hC
  let D := ofRoot A
  let E := ofRoot C
  let dA := pairBound (.body D, .initial)
  let dC := pairBound (.body E, .initial)
  let bound := max bA (max bC (max dA dC))
  have hbAb : bA ≤ bound := by dsimp [bound]; omega
  have hbCb : bC ≤ bound := by dsimp [bound]; omega
  have hdAb : dA ≤ bound := by dsimp [bound]; omega
  have hdCb : dC ≤ bound := by dsimp [bound]; omega
  obtain ⟨P, Q, hPQ, _, hP, hQ⟩ := CommonFirst.body_setups hH bound 0 0 A.stem C.stem
    D.room E.room hord
  have hbP := hbA P (fun x hx ↦ (hP x hx).1) (fun x hx ↦ hbAb.trans_lt (hP x hx).2)
  have hbQ := hbC Q (fun x hx ↦ (hQ x hx).1) (fun x hx ↦ hbCb.trans_lt (hQ x hx).2)
  let S₀ := applyBody D P
  let S₁ := applyBody E Q
  have hhP : RightBlue H (GraphPayoff.payoff B .inside) (.leaf S₀, .initial) :=
    PreparedRelays.body_handoff hH B .inside false D .initial P
      (fun x hx ↦ hdAb.trans_lt (hP x hx).2) hbP
  have hhQ : RightBlue H (GraphPayoff.payoff B .inside) (.leaf S₁, .initial) :=
    PreparedRelays.body_handoff hH B .inside false E .initial Q
      (fun x hx ↦ hdCb.trans_lt (hQ x hx).2) hbQ
  obtain ⟨F⟩ := ReversedForks.exists_forks hH B hB .inside hinit S₀ S₁ hhP hhQ
  have hS₁ : ExactSlots.Exact (.leaf S₁) :=
    ExactSlots.step_exact (DecisionStates.Step.body E Q)
      (ExactSlots.step_exact (DecisionStates.Step.root C) trivial)
  have hS₀L : S₀.leaves = [] := by
    apply List.eq_nil_of_length_eq_zero
    change P.position.label.tail.length = 0
    rw [List.length_tail, P.label_length]
  have hS₀R : S₀.roots = c :: rest := hnext
  have hS₁last : S₁.position.stem.rootLabel.getLastD 0 = c := by
    change Q.position.stem.rootLabel.getLastD 0 = c
    rw [Q.stem_eq]
    exact hlast
  obtain ⟨s, t, u, hst, hsu, htu⟩ := RootForkTriangle.triangle hH B S₀ S₁ F hPQ hS₁
    hS₀L c rest hS₀R hS₁last
  exact hB {s, t, u} (SimpleGraph.is3Clique_triple_iff.mpr ⟨hst, hsu, htu⟩)

theorem positive_parameters {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (hB : B.CliqueFree 3)
    (hinit : RamseyGame.Outcome H (GraphPayoff.game B .inside (.initial, .initial)) true) :
    ∃ k b : ℕ, 0 < k ∧
      (∀ A : RootResponses.Setup k,
        (∀ x ∈ A.stem.decorated, x ∈ H) → (∀ x ∈ A.stem.decorated, b < x) →
        RamseyGame.Outcome H (GraphPayoff.game B .inside (.body (ofRoot A), .initial)) true) ∧
      ∃ L : Set ℕ, L ⊆ H ∧ L.Infinite ∧
        ∀ A : RootResponses.Setup k, (∀ x ∈ A.stem.decorated, x ∈ L ∧ b < x) →
          (¬ Certificate H B (ofRoot A) 0) ∧
            ∃ m : ℕ, 0 < m ∧ Certificate H B (ofRoot A) m := by
  classical
  obtain ⟨k, b, hk, hroot⟩ := InsideSingleton.initial_root_setups_at_least_two hH B hB hinit
  let F := RootResponses.responseFamily k
  let f : F.members → Bool := fun a ↦
    decide (Certificate H B (ofRoot ((RootResponses.supportEquiv k).symm a)) 0)
  let color : Finset ℕ → Bool := fun s ↦ if hs : s ∈ F.members then f ⟨s, hs⟩ else false
  obtain ⟨L, hLH, hL, value, hcolor⟩ :=
    Erdos590.Larson.NashWilliams.nashWilliams_two F.members F.thin color hH
  have hmono : ∀ A : RootResponses.Setup k, (∀ x ∈ A.stem.decorated, x ∈ L) →
      (Certificate H B (ofRoot A) 0 ↔ value = true) := by
    intro A hAL
    let a := RootResponses.supportEquiv k A
    have haL : (↑a.1 : Set ℕ) ⊆ L := by
      intro x hx
      change x ∈ a.1 at hx
      exact hAL x (by
        simpa only [a, RootResponses.supportEquiv_apply, RootResponses.support, List.mem_toFinset]
          using hx)
    have ha : a.1 ∈ F.members := a.2
    have hc : color a.1 = f a := by
      simp only [color, dif_pos ha]
      rfl
    have hf : f a = decide (Certificate H B (ofRoot A) 0) := by
      dsimp only [f, a]
      rw [Equiv.symm_apply_apply]
    have hm := hcolor a.1 a.2 haL
    rw [hc, hf] at hm
    rw [← hm]
    simp
  have hv : value ≠ true := by
    intro he
    exact no_uniform_singleton hH hL B hB hinit k b hk
      (fun A hA ↦ (hmono A (fun x hx ↦ (hA x hx).1)).mpr he)
  refine ⟨k, b, hk, hroot, L, hLH, hL, ?_⟩
  intro A hA
  have hnzero : ¬ Certificate H B (ofRoot A) 0 :=
    fun hz ↦ hv ((hmono A (fun x hx ↦ (hA x hx).1)).mp hz)
  have hbA := hroot A (fun x hx ↦ hLH (hA x hx).1) (fun x hx ↦ (hA x hx).2)
  obtain ⟨m, hm⟩ := certificate_exists B (ofRoot A) hbA
  have hmne : m ≠ 0 := by
    intro he
    subst m
    exact hnzero hm
  exact ⟨hnzero, m, Nat.pos_of_ne_zero hmne, hm⟩

end Erdos118.FirstBody
