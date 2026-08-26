import ErdosProblems.Erdos118.InsideSingleton
import ErdosProblems.Erdos118.InsideRootBody

/-!
An initial inside blue certificate in a triangle-free graph yields the
reserved remaining-leaf checkpoint. The actual right entry excludes a
left body decision, and the proved remaining-body triangle excludes the
other pending alternative. The remaining-leaf triangle is not assumed.
-/

namespace Erdos118.InsideRootLeaf

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns

theorem initial_remaining_leaf {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (hB : B.CliqueFree 3)
    (hinit : RamseyGame.Outcome H (GraphPayoff.game B .inside (.initial, .initial)) true) :
    ∃ k b₀ : ℕ, 0 < k ∧
      (∀ A : RootResponses.Setup k,
        (∀ x ∈ A.stem.decorated, x ∈ H) → (∀ x ∈ A.stem.decorated, b₀ < x) →
        RamseyGame.Outcome H (GraphPayoff.game B .inside (.body (ofRoot A), .initial)) true) ∧
      ∃ P T T₁ : Pending, ∃ j : ℕ, ∃ _Z : RootBuffer.Reserve H b₀ k P.position.stem,
        P.roots = [] ∧ P.leaves = [j] ∧ ExactSlots.Exact (.leaf P) ∧
        (T.roots = [] ∧ T.leaves = []) ∧
        (∀ x ∈ P.position.ordinary, x ∈ H ∧ b₀ < x) ∧
        RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf P, .leaf T)) true ∧
        LeftBlue H (GraphPayoff.payoff B .inside) (.leaf P, .leaf T) ∧
        T₁.position.ordinary = T.position.ordinary ∧
        RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf T₁, .initial)) true ∧
        RightBlue H (GraphPayoff.payoff B .inside) (.leaf T₁, .initial) := by
  obtain ⟨k, b₀, hk, hroot⟩ := InsideSingleton.initial_root_setups_at_least_two hH B hB hinit
  obtain ⟨A₀, Z, hA₀⟩ := RootBuffer.root_reserved hH b₀ k
  let E := ofRoot A₀
  have hE : ExactSlots.Exact (.body E) :=
    ExactSlots.step_exact (DecisionStates.Step.root A₀) trivial
  have hblueE := hroot A₀ (fun x hx ↦ (hA₀ x hx).1) (fun x hx ↦ (hA₀ x hx).2)
  have hleftE : LeftBlue H (GraphPayoff.payoff B .inside) (.body E, .initial) := by
    rcases blue_command (GraphPayoff.payoff B .inside) (.body E, .initial) rfl hblueE with hl | hr
    · exact hl
    · obtain ⟨n, R, hs, _⟩ := hr
      simp [allowedSide] at hs
  obtain ⟨m, A₁, _, _, hhand, hA₁⟩ :=
    PreparedRelays.respond_body_on hH Set.Subset.rfl B .inside false E .initial hleftE b₀
  let S := applyBody E A₁
  have hS : ExactSlots.Exact (.leaf S) :=
    ExactSlots.step_exact (DecisionStates.Step.body E A₁) hE
  have hSfresh : ∀ x ∈ S.position.decorated, x ∈ H ∧ b₀ < x := by
    change ∀ x ∈ A₁.position.decorated, x ∈ H ∧ b₀ < x
    rw [BodyResponses.setup_decorated]
    intro x hx
    exact (List.mem_append.mp hx).elim (hA₀ x) (hA₁ x)
  have hSroot : S.position.stem.root = A₀.stem.root := by
    change A₁.position.stem.root = A₀.stem.root
    rw [A₁.stem_eq]
    rfl
  have hSlabel : S.position.stem.rootLabel = A₀.stem.rootLabel := by
    change A₁.position.stem.rootLabel = A₀.stem.rootLabel
    rw [A₁.stem_eq]
    rfl
  obtain ⟨l, At, Ct, hAt, hCt, hstart⟩ :=
    BlueReservations.second_root_reserved hH B hB .inside hinit S hhand k b₀
  let K := H \ Set.Iic b₀
  have hK : K.Infinite := hH.sdiff (Set.finite_Iic b₀)
  have hKH : K ⊆ H := fun _ hx ↦ hx.1
  have hKb : ∀ x ∈ K, b₀ < x := fun x hx ↦ Nat.lt_of_not_ge hx.2
  obtain ⟨T, V, T₁, hTR, hTL, hrun, hb, hleft, hTord, hTblue, hTright, hnonbody⟩ :=
    InitialRelays.root_to_last_first_nonbody hK hKH b₀ hKb B .inside hroot
      At hAt Ct hCt (.leaf S) hS hstart
  have hV : ∃ P : Pending, V = .leaf P := by
    cases V with
    | initial =>
      have hp := (SkippedCuts.run_extensions hrun).1.ordinary
      have hmem := hp.subset (show S.position.stem.root ∈ S.position.ordinary by
        simp [Position.ordinary, Stem.ordinary])
      exact (List.not_mem_nil hmem).elim
    | body D => exact (hnonbody D rfl).elim
    | complete C =>
      exact (InsideEndgame.complete_incomplete_not_blue hH B C (.leaf T) (by simp) hb).elim
    | leaf P => exact ⟨P, rfl⟩
  obtain ⟨P, rfl⟩ := hV
  have hP := ExactSlots.run_exact_left hrun hS
  have hext := (SkippedCuts.run_extensions hrun).1
  have hPlabel : P.position.stem.rootLabel = S.position.stem.rootLabel :=
    Option.some.inj (hext.labels.root S.position.stem.rootLabel rfl)
  have hProot : P.position.stem.root = S.position.stem.root :=
    (List.cons_prefix_cons.mp hext.ordinary).1.symm
  let ZP := Z.move P.position.stem (hProot.trans hSroot) (hPlabel.trans hSlabel)
  obtain ⟨v, w, hv, _, hvK, _⟩ := CompletionReplay.run_supported_suffixes hrun
  have hOrd : ∀ x ∈ P.position.ordinary, x ∈ H ∧ b₀ < x := by
    change P.position.ordinary = S.position.ordinary ++ v at hv
    rw [hv]
    intro x hx
    exact (List.mem_append.mp hx).elim
      (fun hx ↦ hSfresh x (S.position.ordinary_sublist.subset hx))
      (fun hx ↦ ⟨hKH (hvK x hx), hKb x (hvK x hx)⟩)
  rcases InsideEndgame.last_right_pending_cases hH B P T hTR hTL hleft with
    ⟨hPR, j, hPL⟩ | ⟨hPL, c, hPR⟩
  · exact ⟨k, b₀, hk, hroot, P, T, T₁, j, ZP, hPR, hPL, hP, ⟨hTR, hTL⟩,
      hOrd, hb, hleft, hTord, hTblue, hTright⟩
  · obtain ⟨s, t, u, hst, hsu, htu⟩ := InsideRootBody.triangle_of_reserve
      hH B hB hinit P T T₁ c hPR hPL hP ⟨hTR, hTL⟩ hleft k b₀ ZP hOrd hroot hTord hTright
    exact (hB {s, t, u} (SimpleGraph.is3Clique_triple_iff.mpr ⟨hst, hsu, htu⟩)).elim

end Erdos118.InsideRootLeaf
