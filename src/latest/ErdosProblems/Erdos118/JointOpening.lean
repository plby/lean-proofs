import ErdosProblems.Erdos118.CommonFirst
import ErdosProblems.Erdos118.PreparedRelays

/-!
Joint actual body responses, followed by three compatible first pending
blue pairs. Every front is submitted to its own extracted certificate.
This is an opening, not a continuation to three terminal blue edges.
-/

namespace Erdos118.JointOpening

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns PreparedRelays

theorem respond_bodies {H K : Set ℕ} (hK : K.Infinite) (hKH : K ⊆ H)
    (B : SimpleGraph G) (o : GraphPayoff.Orientation) (r s : Bool)
    (D E : BodyDecision) (X Y : State) (hDE : D.stem.ordinary = E.stem.ordinary)
    (hD : CommandBlue H B o r (.body D) X) (hE : CommandBlue H B o s (.body E) Y)
    (d : ℕ) :
    ∃ k l : ℕ, ∃ A : BodyResponses.Setup D.stem k, ∃ C : BodyResponses.Setup E.stem l,
      A.position.ordinary = C.position.ordinary ∧
      (A.position.label <+: C.position.label ∨ C.position.label <+: A.position.label) ∧
      ConservativeRuns.Step K (GraphPayoff.payoff B o)
        (pair r (.body D) X) (pair r (.leaf (applyBody D A)) X) ∧
      ConservativeRuns.Step K (GraphPayoff.payoff B o)
        (pair s (.body E) Y) (pair s (.leaf (applyBody E C)) Y) ∧
      Blue H B o r (.leaf (applyBody D A)) X ∧
      Blue H B o s (.leaf (applyBody E C)) Y ∧
      OtherBlue H B o r (.leaf (applyBody D A)) X ∧
      OtherBlue H B o s (.leaf (applyBody E C)) Y ∧
      (∀ x ∈ BodyResponses.newWord A.position, x ∈ K ∧ d < x) ∧
      (∀ x ∈ BodyResponses.newWord C.position, x ∈ K ∧ d < x) := by
  obtain ⟨k, bD, hbD⟩ := body_setups B o r D X hD
  obtain ⟨l, bE, hbE⟩ := body_setups B o s E Y hE
  let cD := pairBound (pair r (.body D) X)
  let cE := pairBound (pair s (.body E) Y)
  let gD := guard K B o r D X k
  let gE := guard K B o s E Y l
  let bound := max bD (max bE (max cD (max cE (max gD (max gE d)))))
  have hbDb : bD ≤ bound := by dsimp [bound]; omega
  have hbEb : bE ≤ bound := by dsimp [bound]; omega
  have hcDb : cD ≤ bound := by dsimp [bound]; omega
  have hcEb : cE ≤ bound := by dsimp [bound]; omega
  have hgDb : gD ≤ bound := by dsimp [bound]; omega
  have hgEb : gE ≤ bound := by dsimp [bound]; omega
  have hdb : d ≤ bound := by dsimp [bound]; omega
  obtain ⟨A, C, hord, hlabels, hA, hC⟩ :=
    CommonFirst.body_setups hK bound k l D.stem E.stem D.room E.room hDE
  have hAc : ∀ x ∈ BodyResponses.newWord A.position, cD < x :=
    fun x hx ↦ hcDb.trans_lt (hA x hx).2
  have hCc : ∀ x ∈ BodyResponses.newWord C.position, cE < x :=
    fun x hx ↦ hcEb.trans_lt (hC x hx).2
  have hblueD := hbD A (fun x hx ↦ hKH (hA x hx).1)
    (fun x hx ↦ hbDb.trans_lt (hA x hx).2)
  have hblueE := hbE C (fun x hx ↦ hKH (hC x hx).1)
    (fun x hx ↦ hbEb.trans_lt (hC x hx).2)
  exact ⟨k, l, A, C, hord, hlabels,
    body_step B o r D X A (command_allowed B o r D X hD)
      (fun x hx ↦ (hA x hx).1) hAc (fun x hx ↦ hgDb.trans_lt (hA x hx).2),
    body_step B o s E Y C (command_allowed B o s E Y hE)
      (fun x hx ↦ (hC x hx).1) hCc (fun x hx ↦ hgEb.trans_lt (hC x hx).2),
    hblueD, hblueE,
    body_handoff (hK.mono hKH) B o r D X A hAc hblueD,
    body_handoff (hK.mono hKH) B o s E Y C hCc hblueE,
    fun x hx ↦ ⟨(hA x hx).1, hdb.trans_lt (hA x hx).2⟩,
    fun x hx ↦ ⟨(hC x hx).1, hdb.trans_lt (hC x hx).2⟩⟩

structure Opening (H : Set ℕ) (B : SimpleGraph G) (o : GraphPayoff.Orientation) where
  initialSize : ℕ
  initialBound : ℕ
  initialCertificate : ∀ A : RootResponses.Setup initialSize,
    (∀ x ∈ A.stem.decorated, x ∈ H) → (∀ x ∈ A.stem.decorated, initialBound < x) →
    RamseyGame.Outcome H (GraphPayoff.game B o (.body (ofRoot A), .initial)) true
  S : Pending
  T₀ : Pending
  T₁ : Pending
  U₀ : Pending
  U₁ : Pending
  sFresh : ∀ x ∈ S.position.decorated, x ∈ H ∧ initialBound < x
  t₀Fresh : ∀ x ∈ T₀.position.decorated, x ∈ H ∧ initialBound < x
  t₁Fresh : ∀ x ∈ T₁.position.decorated, x ∈ H ∧ initialBound < x
  u₀Fresh : ∀ x ∈ U₀.position.decorated, x ∈ H ∧ initialBound < x
  u₁Fresh : ∀ x ∈ U₁.position.decorated, x ∈ H ∧ initialBound < x
  tOrdinary : T₀.position.ordinary = T₁.position.ordinary
  uOrdinary : U₀.position.ordinary = U₁.position.ordinary
  sExact : ExactSlots.Exact (.leaf S)
  t₀Exact : ExactSlots.Exact (.leaf T₀)
  t₁Exact : ExactSlots.Exact (.leaf T₁)
  u₀Exact : ExactSlots.Exact (.leaf U₀)
  u₁Exact : ExactSlots.Exact (.leaf U₁)
  tRoots : T₀.position.stem.rootLabel <+: T₁.position.stem.rootLabel ∨
    T₁.position.stem.rootLabel <+: T₀.position.stem.rootLabel
  uRoots : U₀.position.stem.rootLabel <+: U₁.position.stem.rootLabel ∨
    U₁.position.stem.rootLabel <+: U₀.position.stem.rootLabel
  tLeaves : T₀.position.label <+: T₁.position.label ∨ T₁.position.label <+: T₀.position.label
  uLeaves : U₀.position.label <+: U₁.position.label ∨ U₁.position.label <+: U₀.position.label
  blueST : RamseyGame.Outcome H (GraphPayoff.game B o (.leaf S, .leaf T₀)) true
  blueSU : RamseyGame.Outcome H (GraphPayoff.game B o (.leaf S, .leaf U₀)) true
  blueTU : RamseyGame.Outcome H (GraphPayoff.game B o (.leaf T₁, .leaf U₁)) true
  leftST : LeftBlue H (GraphPayoff.payoff B o) (.leaf S, .leaf T₀)
  leftSU : LeftBlue H (GraphPayoff.payoff B o) (.leaf S, .leaf U₀)
  leftTU : LeftBlue H (GraphPayoff.payoff B o) (.leaf T₁, .leaf U₁)

private theorem left_body_command {H : Set ℕ} (B : SimpleGraph G)
    (o : GraphPayoff.Orientation) (D : BodyDecision) (X : State)
    (hb : RamseyGame.Outcome H (GraphPayoff.game B o (.body D, X)) true) :
    LeftBlue H (GraphPayoff.payoff B o) (.body D, X) := by
  rcases blue_command (GraphPayoff.payoff B o) (.body D, X) rfl hb with hl | hr
  · exact hl
  · obtain ⟨n, R, hs, _⟩ := hr
    simp [allowedSide] at hs

private theorem right_body_command {H : Set ℕ} (B : SimpleGraph G)
    (o : GraphPayoff.Orientation) (P : Pending) (D : BodyDecision)
    (hb : RamseyGame.Outcome H (GraphPayoff.game B o (.leaf P, .body D)) true) :
    RightBlue H (GraphPayoff.payoff B o) (.leaf P, .body D) := by
  rcases blue_command (GraphPayoff.payoff B o) (.leaf P, .body D) rfl hb with hl | hr
  · obtain ⟨n, R, hs, _⟩ := hl
    simp [allowedSide] at hs
  · exact hr

private theorem body_fresh {H : Set ℕ} {b k : ℕ} (D : BodyDecision)
    (A : BodyResponses.Setup D.stem k)
    (hD : ∀ x ∈ D.stem.decorated, x ∈ H ∧ b < x)
    (hA : ∀ x ∈ BodyResponses.newWord A.position, x ∈ H ∧ b < x) :
    ∀ x ∈ (applyBody D A).position.decorated, x ∈ H ∧ b < x := by
  change ∀ x ∈ A.position.decorated, x ∈ H ∧ b < x
  rw [BodyResponses.setup_decorated]
  intro x hx
  exact (List.mem_append.mp hx).elim (hD x) (hA x)

theorem initial_opening {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (hB : B.CliqueFree 3) (o : GraphPayoff.Orientation)
    (hinit : RamseyGame.Outcome H (GraphPayoff.game B o (.initial, .initial)) true) :
    Nonempty (Opening H B o) := by
  obtain ⟨k, b₀, hroot⟩ := BlueReservations.initial_root_setups hH B hB o hinit
  obtain ⟨Aₛ, hAₛ⟩ := RootResponses.setup_above k hH b₀
  let Dₛ := ofRoot Aₛ
  have hDₛ : ExactSlots.Exact (.body Dₛ) :=
    ExactSlots.step_exact (DecisionStates.Step.root Aₛ) trivial
  have hblueD := hroot Aₛ (fun x hx ↦ (hAₛ x hx).1) (fun x hx ↦ (hAₛ x hx).2)
  obtain ⟨m, A, _, _, hrightS, hAfresh⟩ := respond_body_on hH Set.Subset.rfl B o false Dₛ .initial
    (left_body_command B o Dₛ .initial hblueD) b₀
  let S := applyBody Dₛ A
  obtain ⟨l, bS, hrootS⟩ := BlueReservations.second_root_setups hH B hB o hinit S hrightS
  obtain ⟨At₀, At₁, htOrd, htRoots, ht₀, ht₁⟩ := CommonFirst.root_setups hH (max bS b₀) l k
  let Dt₀ := ofRoot At₀
  let Dt₁ := ofRoot At₁
  have hSTbody := hrootS At₀ (fun x hx ↦ (ht₀ x hx).1)
    (fun x hx ↦ (le_max_left _ _).trans_lt (ht₀ x hx).2)
  have hTbody := hroot At₁ (fun x hx ↦ (ht₁ x hx).1)
    (fun x hx ↦ (le_max_right _ _).trans_lt (ht₁ x hx).2)
  obtain ⟨mt₀, mt₁, Bt₀, Bt₁, ht, htLeaves, _, _, hbST, hbT, hleftST, hrightT, hBt₀, hBt₁⟩ :=
    respond_bodies hH Set.Subset.rfl B o true false Dt₀ Dt₁ (.leaf S) .initial htOrd
      (right_body_command B o S Dt₀ hSTbody) (left_body_command B o Dt₁ .initial hTbody) b₀
  let T₀ := applyBody Dt₀ Bt₀
  let T₁ := applyBody Dt₁ Bt₁
  obtain ⟨p, bT, hrootT⟩ := BlueReservations.second_root_setups hH B hB o hinit T₁ hrightT
  let bU := max b₀ (max bS bT)
  have hbSU : bS ≤ bU := by dsimp [bU]; omega
  have hbTU : bT ≤ bU := by dsimp [bU]; omega
  have hb₀U : b₀ ≤ bU := le_max_left _ _
  obtain ⟨Au₀, Au₁, huOrd, huRoots, hu₀, hu₁⟩ := CommonFirst.root_setups hH bU l p
  let Du₀ := ofRoot Au₀
  let Du₁ := ofRoot Au₁
  have hSUbody := hrootS Au₀ (fun x hx ↦ (hu₀ x hx).1)
    (fun x hx ↦ hbSU.trans_lt (hu₀ x hx).2)
  have hTUbody := hrootT Au₁ (fun x hx ↦ (hu₁ x hx).1)
    (fun x hx ↦ hbTU.trans_lt (hu₁ x hx).2)
  obtain ⟨mu₀, mu₁, Bu₀, Bu₁, hu, huLeaves, _, _, hbSU, hbTU, hleftSU, hleftTU, hBu₀, hBu₁⟩ :=
    respond_bodies hH Set.Subset.rfl B o true true Du₀ Du₁ (.leaf S) (.leaf T₁) huOrd
      (right_body_command B o S Du₀ hSUbody) (right_body_command B o T₁ Du₁ hTUbody) b₀
  refine ⟨{
    initialSize := k, initialBound := b₀, initialCertificate := hroot
    S := S, T₀ := T₀, T₁ := T₁, U₀ := applyBody Du₀ Bu₀, U₁ := applyBody Du₁ Bu₁
    sFresh := body_fresh Dₛ A hAₛ hAfresh
    t₀Fresh := body_fresh Dt₀ Bt₀
      (fun x hx ↦ ⟨(ht₀ x hx).1, (le_max_right _ _).trans_lt (ht₀ x hx).2⟩) hBt₀
    t₁Fresh := body_fresh Dt₁ Bt₁
      (fun x hx ↦ ⟨(ht₁ x hx).1, (le_max_right _ _).trans_lt (ht₁ x hx).2⟩) hBt₁
    u₀Fresh := body_fresh Du₀ Bu₀
      (fun x hx ↦ ⟨(hu₀ x hx).1, hb₀U.trans_lt (hu₀ x hx).2⟩) hBu₀
    u₁Fresh := body_fresh Du₁ Bu₁
      (fun x hx ↦ ⟨(hu₁ x hx).1, hb₀U.trans_lt (hu₁ x hx).2⟩) hBu₁
    tOrdinary := ht, uOrdinary := hu
    sExact := ExactSlots.step_exact (DecisionStates.Step.body Dₛ A) hDₛ
    t₀Exact := ExactSlots.step_exact (DecisionStates.Step.body Dt₀ Bt₀)
      (ExactSlots.step_exact (DecisionStates.Step.root At₀) trivial)
    t₁Exact := ExactSlots.step_exact (DecisionStates.Step.body Dt₁ Bt₁)
      (ExactSlots.step_exact (DecisionStates.Step.root At₁) trivial)
    u₀Exact := ExactSlots.step_exact (DecisionStates.Step.body Du₀ Bu₀)
      (ExactSlots.step_exact (DecisionStates.Step.root Au₀) trivial)
    u₁Exact := ExactSlots.step_exact (DecisionStates.Step.body Du₁ Bu₁)
      (ExactSlots.step_exact (DecisionStates.Step.root Au₁) trivial)
    tRoots := ?_, uRoots := ?_, tLeaves := htLeaves, uLeaves := huLeaves
    blueST := hbST, blueSU := hbSU, blueTU := hbTU
    leftST := hleftST, leftSU := hleftSU, leftTU := hleftTU }⟩
  · change Bt₀.position.stem.rootLabel <+: Bt₁.position.stem.rootLabel ∨
      Bt₁.position.stem.rootLabel <+: Bt₀.position.stem.rootLabel
    rw [Bt₀.stem_eq, Bt₁.stem_eq]
    exact htRoots
  · change Bu₀.position.stem.rootLabel <+: Bu₁.position.stem.rootLabel ∨
      Bu₁.position.stem.rootLabel <+: Bu₀.position.stem.rootLabel
    rw [Bu₀.stem_eq, Bu₁.stem_eq]
    exact huRoots

end Erdos118.JointOpening
