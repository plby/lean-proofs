import ErdosProblems.Erdos118.JointAlignment
import ErdosProblems.Erdos118.InsideEndgame

/-!
An actual finite three-game synchronization to unequal response kinds.
Matching moves preserve all three blue certificates, and the common final
rightmost branch gives a triangle. The unequal-kind endpoint is not excluded.
-/

namespace Erdos118.JointController

open Negative Negative.Exact LabelledExtensions LabelledFrames DecisionStates AdaptiveGame
open BlueRuns PreparedRelays JointAlignment

structure Config (H : Set ℕ) (B : SimpleGraph G) where
  S₀ : Pending
  S₁ : Pending
  T₀ : Pending
  T₁ : Pending
  U₀ : Pending
  U₁ : Pending
  sAligned : Aligned S₀ S₁
  tAligned : Aligned T₀ T₁
  uAligned : Aligned U₀ U₁
  blueST : RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf S₀, .leaf T₀)) true
  blueSU : RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf S₁, .leaf U₀)) true
  blueTU : RamseyGame.Outcome H (GraphPayoff.game B .inside (.leaf T₁, .leaf U₁)) true

inductive Turn
  | first | middle | last
  deriving DecidableEq

def Turn.next : Turn → Turn
  | .first => .middle
  | .middle => .last
  | .last => .first

def Config.primary {H : Set ℕ} {B : SimpleGraph G} (C : Config H B) : Turn → Pending
  | .first => C.S₀
  | .middle => C.T₀
  | .last => C.U₀

def Config.secondary {H : Set ℕ} {B : SimpleGraph G} (C : Config H B) : Turn → Pending
  | .first => C.S₁
  | .middle => C.T₁
  | .last => C.U₁

def Ready {H : Set ℕ} {B : SimpleGraph G} (C : Config H B) : Turn → Prop
  | .first =>
      LeftBlue H (GraphPayoff.payoff B .inside) (.leaf C.S₀, .leaf C.T₀) ∧
      LeftBlue H (GraphPayoff.payoff B .inside) (.leaf C.S₁, .leaf C.U₀) ∧
      LeftBlue H (GraphPayoff.payoff B .inside) (.leaf C.T₁, .leaf C.U₁)
  | .middle =>
      RightBlue H (GraphPayoff.payoff B .inside) (.leaf C.S₀, .leaf C.T₀) ∧
      RightBlue H (GraphPayoff.payoff B .inside) (.leaf C.S₁, .leaf C.U₀) ∧
      LeftBlue H (GraphPayoff.payoff B .inside) (.leaf C.T₁, .leaf C.U₁)
  | .last =>
      LeftBlue H (GraphPayoff.payoff B .inside) (.leaf C.S₀, .leaf C.T₀) ∧
      RightBlue H (GraphPayoff.payoff B .inside) (.leaf C.S₁, .leaf C.U₀) ∧
      RightBlue H (GraphPayoff.payoff B .inside) (.leaf C.T₁, .leaf C.U₁)

def Mismatch {H : Set ℕ} {B : SimpleGraph G} (C : Config H B) (t : Turn) : Prop :=
  kind (C.primary t) ≠ kind (C.secondary t)

structure Reach {H : Set ℕ} {B : SimpleGraph G} (K : Set ℕ) (C D : Config H B) : Prop where
  st : ConservativeRuns.Run K (GraphPayoff.payoff B .inside)
    (.leaf C.S₀, .leaf C.T₀) (.leaf D.S₀, .leaf D.T₀)
  su : ConservativeRuns.Run K (GraphPayoff.payoff B .inside)
    (.leaf C.S₁, .leaf C.U₀) (.leaf D.S₁, .leaf D.U₀)
  tu : ConservativeRuns.Run K (GraphPayoff.payoff B .inside)
    (.leaf C.T₁, .leaf C.U₁) (.leaf D.T₁, .leaf D.U₁)

theorem Reach.refl {H : Set ℕ} {B : SimpleGraph G} (K : Set ℕ) (C : Config H B) : Reach K C C :=
  ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩

theorem Reach.trans {H K : Set ℕ} {B : SimpleGraph G} {C D E : Config H B}
    (h : Reach K C D) (h' : Reach K D E) : Reach K C E :=
  ⟨h.st.trans h'.st, h.su.trans h'.su, h.tu.trans h'.tu⟩

def measure {H : Set ℕ} {B : SimpleGraph G} (C : Config H B) : ℕ × ℕ :=
  (C.S₀.roots.length + C.T₀.roots.length + C.U₀.roots.length,
    C.S₀.leaves.length + C.T₀.leaves.length + C.U₀.leaves.length)

def Less {H : Set ℕ} {B : SimpleGraph G} (D C : Config H B) : Prop :=
  Prod.Lex (· < ·) (· < ·) (measure D) (measure C)

theorem less_wellFounded (H : Set ℕ) (B : SimpleGraph G) : WellFounded (Less (H := H) (B := B)) :=
  InvImage.wf measure (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf

private theorem not_last_of_matching {H : Set ℕ} (hH : H.Infinite) (B : SimpleGraph G)
    (hB : B.CliqueFree 3) (C : Config H B) (t : Turn) (hready : Ready C t)
    (hk : kind (C.primary t) = kind (C.secondary t)) : ¬ Last (C.primary t) := by
  intro hlast
  have hother : Last (C.secondary t) := (kind_eq_finish_iff _).mp
    (hk.symm.trans ((kind_eq_finish_iff _).mpr hlast))
  cases t with
  | first =>
    exact InsideEndgame.last_left_not_leftBlue hH B C.S₀ (.leaf C.T₀)
      hlast.1 hlast.2 (by simp) hready.1
  | middle =>
    exact InsideEndgame.last_left_not_leftBlue hH B C.T₁ (.leaf C.U₁)
      hother.1 hother.2 (by simp) hready.2.2
  | last =>
    obtain ⟨s, t, u, hst, hsu, htu⟩ := JointFinish.triangle_of_last_right hH B .inside
      C.S₀ C.S₁ C.T₀ C.T₁ C.U₀ C.U₁ C.sAligned.ordinary C.tAligned.ordinary C.uAligned.ordinary
      hlast hother C.blueST hready.2.1 hready.2.2
    exact hB {s, t, u} (SimpleGraph.is3Clique_triple_iff.mpr ⟨hst, hsu, htu⟩)

theorem matching_step {H K : Set ℕ} (hK : K.Infinite) (hKH : K ⊆ H)
    (B : SimpleGraph G) (hB : B.CliqueFree 3) (C : Config H B) (t : Turn)
    (hready : Ready C t) (hk : kind (C.primary t) = kind (C.secondary t)) :
    ∃ D : Config H B, Reach K C D ∧ Ready D t.next ∧ Less D C := by
  have hn := not_last_of_matching (hK.mono hKH) B hB C t hready hk
  cases t with
  | first =>
    obtain ⟨P, Q, hA, hrP, hrQ, hbP, hbQ, hhP, hhQ, hdec⟩ := Aligned.advance
      hK hKH B .inside false false C.S₀ C.S₁ (.leaf C.T₀) (.leaf C.U₀) C.sAligned hk hn
      hready.1 hready.2.1 0
    let D : Config H B :=
      { C with S₀ := P, S₁ := Q, sAligned := hA, blueST := hbP, blueSU := hbQ }
    refine ⟨D, ⟨hrP, hrQ, Relation.ReflTransGen.refl⟩, ⟨hhP, hhQ, hready.2.2⟩, ?_⟩
    simp only [Decreases, size, Prod.lex_def] at hdec
    dsimp only [Less, measure, D]
    simp only [Prod.lex_def]
    omega
  | middle =>
    obtain ⟨P, Q, hA, hrP, hrQ, hbP, hbQ, hhP, hhQ, hdec⟩ := Aligned.advance
      hK hKH B .inside true false C.T₀ C.T₁ (.leaf C.S₀) (.leaf C.U₁) C.tAligned hk hn
      hready.1 hready.2.2 0
    let D : Config H B :=
      { C with T₀ := P, T₁ := Q, tAligned := hA, blueST := hbP, blueTU := hbQ }
    refine ⟨D, ⟨hrP, Relation.ReflTransGen.refl, hrQ⟩, ⟨hhP, hready.2.1, hhQ⟩, ?_⟩
    simp only [Decreases, size, Prod.lex_def] at hdec
    dsimp only [Less, measure, D]
    simp only [Prod.lex_def]
    omega
  | last =>
    obtain ⟨P, Q, hA, hrP, hrQ, hbP, hbQ, hhP, hhQ, hdec⟩ := Aligned.advance
      hK hKH B .inside true true C.U₀ C.U₁ (.leaf C.S₁) (.leaf C.T₁) C.uAligned hk hn
      hready.2.1 hready.2.2 0
    let D : Config H B :=
      { C with U₀ := P, U₁ := Q, uAligned := hA, blueSU := hbP, blueTU := hbQ }
    refine ⟨D, ⟨Relation.ReflTransGen.refl, hrP, hrQ⟩, ⟨hready.1, hhP, hhQ⟩, ?_⟩
    simp only [Decreases, size, Prod.lex_def] at hdec
    dsimp only [Less, measure, D]
    simp only [Prod.lex_def]
    omega

theorem checkpoint {H K : Set ℕ} (hK : K.Infinite) (hKH : K ⊆ H)
    (B : SimpleGraph G) (hB : B.CliqueFree 3) (C : Config H B) (t : Turn)
    (hready : Ready C t) :
    ∃ D : Config H B, ∃ u : Turn, Reach K C D ∧ Ready D u ∧ Mismatch D u := by
  classical
  induction C using (less_wellFounded H B).induction generalizing t with
  | h C ih =>
    by_cases hm : Mismatch C t
    · exact ⟨C, t, Reach.refl K C, hready, hm⟩
    · have hk : kind (C.primary t) = kind (C.secondary t) := not_ne_iff.mp hm
      obtain ⟨D, hr, hd, hlt⟩ := matching_step hK hKH B hB C t hready hk
      obtain ⟨E, u, hr', he, hm'⟩ := ih D hlt t.next hd
      exact ⟨E, u, hr.trans hr', he, hm'⟩

def ofOpening {H : Set ℕ} {B : SimpleGraph G} (F : JointOpening.Opening H B .inside) : Config H B where
  S₀ := F.S
  S₁ := F.S
  T₀ := F.T₀
  T₁ := F.T₁
  U₀ := F.U₀
  U₁ := F.U₁
  sAligned := ⟨rfl, F.sExact, F.sExact, Or.inl List.prefix_rfl, Or.inl List.prefix_rfl⟩
  tAligned := ⟨F.tOrdinary, F.t₀Exact, F.t₁Exact, F.tRoots, F.tLeaves⟩
  uAligned := ⟨F.uOrdinary, F.u₀Exact, F.u₁Exact, F.uRoots, F.uLeaves⟩
  blueST := F.blueST
  blueSU := F.blueSU
  blueTU := F.blueTU

theorem initial_checkpoint {H K : Set ℕ} (hK : K.Infinite) (hKH : K ⊆ H)
    (B : SimpleGraph G) (hB : B.CliqueFree 3)
    (hinit : RamseyGame.Outcome H (GraphPayoff.game B .inside (.initial, .initial)) true) :
    ∃ F : JointOpening.Opening H B .inside, ∃ D : Config H B, ∃ t : Turn,
      Reach K (ofOpening F) D ∧ Ready D t ∧ Mismatch D t := by
  obtain ⟨F⟩ := JointOpening.initial_opening (hK.mono hKH) B hB .inside hinit
  have hready : Ready (ofOpening F) .first := ⟨F.leftST, F.leftSU, F.leftTU⟩
  obtain ⟨D, t, hr, hd, hm⟩ := checkpoint hK hKH B hB (ofOpening F) .first hready
  exact ⟨F, D, t, hr, hd, hm⟩

end Erdos118.JointController
