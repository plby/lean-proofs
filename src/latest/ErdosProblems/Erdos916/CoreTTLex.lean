/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos916.CoreMaxCycle

/-!
# Lexicographic maximum cycles for the terminal TT exchange

The bridge-endblock cases of Thomassen--Toft use a second finite maximum:
after maximizing the cardinality of the rooted component, maximize the number
of ambient edges with both ends in that component.  This file supplies that
selector and packages its connected-complement output as a
`MaxCycleCertificate`.
-/

namespace Erdos916

open SimpleGraph
open Erdos751.BV

attribute [local instance] Classical.propDecidable

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

namespace Nonseparating

/-- The ambient edges whose two endpoints lie in the rooted component.  This
ambient-finset presentation avoids changing vertex types and gives the
required finite bound immediately. -/
noncomputable def targetEdgeFinset (C : Cycle (G := G)) (x : V) :
    Finset (Sym2 V) :=
  G.edgeFinset.filter fun e => (↑e.toFinset : Set V) ⊆ targetSet G C x

noncomputable def targetEdgeCard (C : Cycle (G := G)) (x : V) : Nat :=
  (targetEdgeFinset G C x).card

theorem targetEdgeCard_le_card_edgeFinset (C : Cycle (G := G)) (x : V) :
    targetEdgeCard G C x ≤ G.edgeFinset.card := by
  exact Finset.card_le_card (Finset.filter_subset _ _)

/-- The edge value `m` occurs among admissible cycles whose rooted component
already has maximum cardinality. -/
def TargetLexEdgeOccurs (S : Set V) (x : V) (m : Nat) : Prop :=
  ∃ C : Cycle (G := G), IsAdmissibleCycle G S C ∧
    targetCard G C x = maxTargetCard G S x ∧ targetEdgeCard G C x = m

/-- The secondary edge maximum among primary-cardinality maximizers. -/
noncomputable def maxTargetEdgeCard (S : Set V) (x : V) : Nat :=
  Nat.findGreatest (TargetLexEdgeOccurs G S x) G.edgeFinset.card

theorem targetLexEdgeOccurs_max {S : Set V} {x : V}
    (hseed : ∃ C : Cycle (G := G), IsAdmissibleCycle G S C) :
    TargetLexEdgeOccurs G S x (maxTargetEdgeCard G S x) := by
  obtain ⟨C, hCadm, hCcard⟩ := targetCardOccurs_max (x := x) G hseed
  have hocc : TargetLexEdgeOccurs G S x (targetEdgeCard G C x) :=
    ⟨C, hCadm, hCcard, rfl⟩
  have hle := targetEdgeCard_le_card_edgeFinset G C x
  simpa only [maxTargetEdgeCard] using
    Nat.findGreatest_spec (P := TargetLexEdgeOccurs G S x) hle hocc

/-- A cycle selected by the two successive finite maxima. -/
noncomputable def lexMaximizingCycle {S : Set V} (x : V)
    (hseed : ∃ C : Cycle (G := G), IsAdmissibleCycle G S C) :
    Cycle (G := G) :=
  Classical.choose (targetLexEdgeOccurs_max (x := x) G hseed)

theorem lexMaximizingCycle_admissible {S : Set V} {x : V}
    (hseed : ∃ C : Cycle (G := G), IsAdmissibleCycle G S C) :
    IsAdmissibleCycle G S (lexMaximizingCycle G x hseed) :=
  (Classical.choose_spec (targetLexEdgeOccurs_max (x := x) G hseed)).1

theorem targetCard_lexMaximizingCycle {S : Set V} {x : V}
    (hseed : ∃ C : Cycle (G := G), IsAdmissibleCycle G S C) :
    targetCard G (lexMaximizingCycle G x hseed) x = maxTargetCard G S x :=
  (Classical.choose_spec (targetLexEdgeOccurs_max (x := x) G hseed)).2.1

theorem targetEdgeCard_lexMaximizingCycle {S : Set V} {x : V}
    (hseed : ∃ C : Cycle (G := G), IsAdmissibleCycle G S C) :
    targetEdgeCard G (lexMaximizingCycle G x hseed) x =
      maxTargetEdgeCard G S x :=
  (Classical.choose_spec (targetLexEdgeOccurs_max (x := x) G hseed)).2.2

theorem targetEdgeCard_le_lexMax {S : Set V} {x : V}
    (C : Cycle (G := G)) (hC : IsAdmissibleCycle G S C)
    (hcard : targetCard G C x = maxTargetCard G S x) :
    targetEdgeCard G C x ≤ maxTargetEdgeCard G S x := by
  by_contra hnot
  have hlt : maxTargetEdgeCard G S x < targetEdgeCard G C x :=
    Nat.lt_of_not_ge hnot
  have hbound := targetEdgeCard_le_card_edgeFinset G C x
  have hnotOcc : ¬TargetLexEdgeOccurs G S x (targetEdgeCard G C x) := by
    apply Nat.findGreatest_is_greatest (P := TargetLexEdgeOccurs G S x)
      (n := G.edgeFinset.card)
    · simpa only [maxTargetEdgeCard] using hlt
    · exact hbound
  exact hnotOcc ⟨C, hC, hcard, rfl⟩

/-- The primary maximum still forces connected complement; the secondary
choice does not disturb the TT target-augmentation argument. -/
theorem lexMaximizingCycle_complement_connected_of_augmentation
    {S : Set V} {x : V} (hxS : x ∈ S)
    (hseed : ∃ C : Cycle (G := G), IsAdmissibleCycle G S C)
    (haug : TargetAugmentationProperty G S x) :
    (G.induce ((lexMaximizingCycle G x hseed).vSet (G := G))ᶜ).Connected := by
  let C := lexMaximizingCycle G x hseed
  have hC : IsAdmissibleCycle G S C := lexMaximizingCycle_admissible G hseed
  have hxout : x ∉ C.vSet (G := G) :=
    IsAdmissibleCycle.not_mem_cycle (G := G) hC hxS
  rw [complement_connected_iff_target_eq G hxout]
  by_contra hne
  obtain ⟨D, hD, hlt⟩ := haug C hC hne
  have hle := targetCard_le_max (x := x) G D hD
  have heq := targetCard_lexMaximizingCycle (x := x) G hseed
  change targetCard G C x = maxTargetCard G S x at heq
  omega

end Nonseparating

/-- A maximum-cycle certificate carrying both finite source invariants. -/
structure LexMaxCycleCertificate (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Set V) (x : V) extends MaxCycleCertificate G where
  admissible : Nonseparating.IsAdmissibleCycle G S cycle
  target_max : ∀ D : Cycle (G := G),
    Nonseparating.IsAdmissibleCycle G S D →
      Nonseparating.targetCard G D x ≤
        Nonseparating.targetCard G cycle x
  edge_max_at_target : ∀ D : Cycle (G := G),
    Nonseparating.IsAdmissibleCycle G S D →
      Nonseparating.targetCard G D x =
        Nonseparating.targetCard G cycle x →
      Nonseparating.targetEdgeCard G D x ≤
        Nonseparating.targetEdgeCard G cycle x

/-- Under the specialized TT hypotheses, the connected-complement
certificate can be selected with both the cardinality and edge tie-breaker
maximality used by the terminal exchange. -/
theorem exists_lexMaxCycleCertificate_of_specialized_TT_minDegreeExcept
    (h2 : VertexTwoConnected (G := G)) {x₀ : V}
    (hdeg : ∀ v : V, v ≠ x₀ → 3 ≤ G.degree v)
    {S : Set V} (hS : (G.induce S).Connected) (hx₀S : x₀ ∈ S)
    (hseed : ∃ C : Cycle (G := G),
      Nonseparating.IsAdmissibleCycle G S C) :
    Nonempty (LexMaxCycleCertificate G S x₀) := by
  let C := Nonseparating.lexMaximizingCycle G x₀ hseed
  have hC : Nonseparating.IsAdmissibleCycle G S C :=
    Nonseparating.lexMaximizingCycle_admissible G hseed
  have haug : Nonseparating.TargetAugmentationProperty G S x₀ :=
    Nonseparating.targetAugmentationProperty_of_vertexTwoConnected_minDegreeExcept
      G h2 hdeg hS hx₀S hseed
  have hconn : (G.induce (C.vSet (G := G))ᶜ).Connected :=
    Nonseparating.lexMaximizingCycle_complement_connected_of_augmentation
      G hx₀S hseed haug
  have hx₀out : x₀ ∉ C.vSet (G := G) :=
    Nonseparating.IsAdmissibleCycle.not_mem_cycle (G := G) hC hx₀S
  have hrimdeg : ∀ c : V, c ∈ C.vSet (G := G) → 3 ≤ G.degree c := by
    intro c hcC
    apply hdeg c
    intro hcx
    exact hx₀out (hcx ▸ hcC)
  let M := maxCycleCertificate_of_complement_connected
    G C hC.1 hconn hx₀out hrimdeg
  refine ⟨{
    toMaxCycleCertificate := M
    admissible := by
      simpa only [M, maxCycleCertificate_of_complement_connected] using hC
    target_max := ?_
    edge_max_at_target := ?_ }⟩
  · intro D hD
    have hle := Nonseparating.targetCard_le_max (x := x₀) G D hD
    have heq := Nonseparating.targetCard_lexMaximizingCycle
      (x := x₀) G hseed
    change Nonseparating.targetCard G D x₀ ≤
      Nonseparating.targetCard G C x₀
    exact hle.trans_eq heq.symm
  · intro D hD hcard
    have heq := Nonseparating.targetCard_lexMaximizingCycle
      (x := x₀) G hseed
    have hcardMax : Nonseparating.targetCard G D x₀ =
        Nonseparating.maxTargetCard G S x₀ := by
      exact hcard.trans heq
    have hle := Nonseparating.targetEdgeCard_le_lexMax
      (x := x₀) G D hD hcardMax
    have hedgeEq := Nonseparating.targetEdgeCard_lexMaximizingCycle
      (x := x₀) G hseed
    change Nonseparating.targetEdgeCard G D x₀ ≤
      Nonseparating.targetEdgeCard G C x₀
    exact hle.trans_eq hedgeEq.symm

/-- Pointed, assumption-minimal entry point for the lexicographic terminal
certificate. -/
theorem exists_lexMaxCycleCertificate_of_pointed_hypotheses
    {x₀ : V} (hcard : 2 ≤ Fintype.card V)
    (h2 : VertexTwoConnected (G := G))
    (hdeg : ∀ v : V, v ≠ x₀ → 3 ≤ G.degree v) :
    Nonempty (LexMaxCycleCertificate G ({x₀} : Set V) x₀) := by
  have hsingleton : (G.induce ({x₀} : Set V)).Connected :=
    ⟨SimpleGraph.Preconnected.of_subsingleton⟩
  have hx₀singleton : x₀ ∈ ({x₀} : Set V) := Set.mem_singleton x₀
  have hseed :=
    Nonseparating.exists_admissible_cycle_singleton_of_vertexTwoConnected_minDegreeExcept
      G hcard h2 hdeg
  exact exists_lexMaxCycleCertificate_of_specialized_TT_minDegreeExcept
    G h2 hdeg hsingleton hx₀singleton hseed

end Erdos916
