/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.IterationChosenLink
import ErdosProblems.Erdos207.PreliminaryInternalResidualLinks
import ErdosProblems.Erdos207.LinkSideDensityScalar

/-!
# Rechoosing typical residual links on support

The internal stage supplies an arbitrary balanced residual bipartition.  Its
two sides certify both parity and containment in the next vortex layer.  We
may therefore apply the paired-bisection theorem again, independently at
each outside center, to obtain degree/codegree-typical links.  Because the
underlying residual-neighbor set is unchanged, reserve-spoke support
transfers from the original links to the rechosen ones.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

lemma IsResidualBipartition.residualNeighbors_even
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {R : TripleSystemOn V} {v : V} {K : BipartiteLink V}
    (hK : IsResidualBipartition G R v K) :
    Even (residualNeighbors G R v).card := by
  rw [← hK.2.1, card_union_of_disjoint K.disjoint_sides, hK.2.2]
  exact ⟨K.right.card, by omega⟩

/-- A new bipartition of the same residual-neighbor set inherits containment
in `U` and reserve-spoke support from an old bipartition. -/
lemma IsResidualBipartition.transfer_side_and_spoke_support
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {U : Finset V} {reserve : Finset (Sym2 V)}
    {R : TripleSystemOn V} {v : V} {Kold Knew : BipartiteLink V}
    (hold : IsResidualBipartition G R v Kold)
    (hnew : IsResidualBipartition G R v Knew)
    (hleft : Kold.left ⊆ U) (hright : Kold.right ⊆ U)
    (hspokes : Kold.SpokesIn reserve) :
    Knew.left ⊆ U ∧ Knew.right ⊆ U ∧ Knew.SpokesIn reserve := by
  have hresU : residualNeighbors G R v ⊆ U := by
    intro x hx
    rw [← hold.2.1] at hx
    rcases mem_union.mp hx with hx | hx
    · exact hleft hx
    · exact hright hx
  have hleftRes : Knew.left ⊆ residualNeighbors G R v := by
    intro x hx
    rw [← hnew.2.1]
    exact mem_union_left Knew.right hx
  have hrightRes : Knew.right ⊆ residualNeighbors G R v := by
    intro x hx
    rw [← hnew.2.1]
    exact mem_union_right Knew.left hx
  refine ⟨hleftRes.trans hresU, hrightRes.trans hresU, ?_⟩
  constructor
  · intro x hx
    rw [hnew.1]
    have hxRes := hleftRes hx
    rw [← hold.2.1] at hxRes
    rcases mem_union.mp hxRes with hxOld | hxOld
    · have hs := hspokes.1 x hxOld
      rwa [hold.1] at hs
    · have hs := hspokes.2 x hxOld
      rwa [hold.1] at hs
  · intro x hx
    rw [hnew.1]
    have hxRes := hrightRes hx
    rw [← hold.2.1] at hxRes
    rcases mem_union.mp hxRes with hxOld | hxOld
    · have hs := hspokes.1 x hxOld
      rwa [hold.1] at hs
    · have hs := hspokes.2 x hxOld
      rwa [hold.1] at hs

/-- Rechoose every residual link from estimates proved directly on its
actual residual-neighbor set.  This is the sparse-reserve counterpart of the
iteration-typical constructor below: the old links are used only for parity,
side containment, and spoke support. -/
theorem exists_reserveSupportedTypicalResidualLinks_of_bounds
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {U : Finset V}
    {reserve : Finset (Sym2 V)} {A I D R : TripleSystemOn V}
    (Kold : {x : V // x ∉ U} → BipartiteLink V)
    (hstate : IsIntermediateLinkState G U A I D R Kold)
    (hleftOld : ∀ o, (Kold o).left ⊆ U)
    (hrightOld : ∀ o, (Kold o).right ⊆ U)
    (hspokesOld : ∀ o, (Kold o).SpokesIn reserve)
    (m d degreeMax codegree : ℕ)
    (hdegreeLower : ∀ o : {x : V // x ∉ U},
      ∀ x ∈ @residualNeighbors V _ _ G (Classical.decRel G.Adj) R o.1,
        m ≤ (ambientLinkNeighborsIn o.1 A
          (@residualNeighbors V _ _ G (Classical.decRel G.Adj) R o.1) x).card)
    (hdegreeUpper : ∀ o : {x : V // x ∉ U},
      ∀ x ∈ @residualNeighbors V _ _ G (Classical.decRel G.Adj) R o.1,
        (ambientLinkNeighborsIn o.1 A
          (@residualNeighbors V _ _ G (Classical.decRel G.Adj) R o.1) x).card ≤ degreeMax)
    (hcodegreeUpper : ∀ o : {x : V // x ∉ U},
      ∀ x ∈ @residualNeighbors V _ _ G (Classical.decRel G.Adj) R o.1,
      ∀ y ∈ @residualNeighbors V _ _ G (Classical.decRel G.Adj) R o.1,
        x ≠ y →
        (ambientLinkCommonNeighborsIn o.1 A
          (@residualNeighbors V _ _ G (Classical.decRel G.Adj) R o.1)
          x y).card ≤ codegree)
    (hbisection : ∀ o : {x : V // x ∉ U},
      ((@residualNeighbors V _ _ G (Classical.decRel G.Adj) R o.1).card :
          ℝ≥0) *
        (2 * (2 : ℝ≥0) ^ d * (3 / 4 : ℝ≥0) ^
          (m - 2 * d)) < 1) :
    ∃ Knew : {x : V // x ∉ U} → BipartiteLink V,
      IsIntermediateLinkState G U A I D R Knew ∧
      (∀ o, (Knew o).center = outsideVertexEmbedding U o) ∧
      (∀ o, outsideVertexEmbedding U o ∉ U) ∧
      (∀ o, (Knew o).left ⊆ U) ∧
      (∀ o, (Knew o).right ⊆ U) ∧
      (∀ o, (Knew o).SpokesIn reserve) ∧
      (∀ o, HasLinkDegreeCodegreeBounds A (Knew o)
        d degreeMax codegree) := by
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  have hchoice : ∀ o : {x : V // x ∉ U},
      ∃ K : BipartiteLink V,
        IsResidualBipartition G R o.1 K ∧
          HasLinkDegreeCodegreeBounds A K d degreeMax codegree := by
    intro o
    exact exists_chosenResidualLink_of_bounds
      (hstate.1 o).residualNeighbors_even m d degreeMax codegree
      (hdegreeLower o) (hdegreeUpper o) (hcodegreeUpper o)
      (hbisection o)
  let Knew : {x : V // x ∉ U} → BipartiteLink V :=
    fun o ↦ Classical.choose (hchoice o)
  have hKnew : ∀ o, IsResidualBipartition G R o.1 (Knew o) :=
    fun o ↦ (Classical.choose_spec (hchoice o)).1
  have hbounds : ∀ o, HasLinkDegreeCodegreeBounds A (Knew o)
      d degreeMax codegree :=
    fun o ↦ (Classical.choose_spec (hchoice o)).2
  have htransfer : ∀ o,
      (Knew o).left ⊆ U ∧ (Knew o).right ⊆ U ∧
        (Knew o).SpokesIn reserve := by
    intro o
    exact (hstate.1 o).transfer_side_and_spoke_support (hKnew o)
      (hleftOld o) (hrightOld o) (hspokesOld o)
  refine ⟨Knew, ⟨hKnew, hstate.2.1, hstate.2.2⟩,
    ?_, ?_, ?_, ?_, ?_, hbounds⟩
  · intro o
    exact (hKnew o).1
  · intro o
    exact o.2
  · intro o
    exact (htransfer o).1
  · intro o
    exact (htransfer o).2.1
  · intro o
    exact (htransfer o).2.2

/-- Rechoose all residual links so that every center has the prescribed
degree/codegree bounds, without losing any intermediate-state or reserve
certificate. -/
theorem IsIterationTypical.exists_reserveSupportedTypicalResidualLinks_localized
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {k : Fin (ell + 1)}
    {G : SimpleGraph V}
    {A I D R : TripleSystemOn V}
    {p eta xi : ℝ≥0} {h : ℕ}
    (htyp : IsIterationTypical W k G A p eta xi h)
    (htri : ConsistsOfTriangles G A)
    (i : Fin ell) (hki : k.val ≤ i.val)
    (hGsupp : GraphSupportedOn G (W.U i.castSucc : Set V))
    (U : Finset V) (hU : U = W.U i.succ)
    (reserve : Finset (Sym2 V))
    (Kold : {x : V // x ∉ U} → BipartiteLink V)
    (hstate : IsIntermediateLinkState G U A I D R Kold)
    (hleftOld : ∀ o, (Kold o).left ⊆ U)
    (hrightOld : ∀ o, (Kold o).right ⊆ U)
    (hspokesOld : ∀ o, (Kold o).SpokesIn reserve)
    (m d degreeMax codegree loss : ℕ)
    (hcovered : ∀ o : {x : V // x ∉ U},
      ((coveredGraph R).neighborFinset o.1 ∩ U).card ≤ loss)
    (hh : 3 ≤ h)
    (hlower : (m + loss + 1 : ℝ≥0) ≤
      (1 - xi) * (p ^ 2 * eta * (W.U i.succ).card))
    (hupper : (1 + xi) * (p ^ 2 * eta * (W.U i.succ).card) ≤
      (degreeMax : ℝ≥0))
    (hcodegree : (1 + xi) *
      (p ^ 3 * eta ^ 2 * (W.U i.succ).card) ≤ (codegree : ℝ≥0))
    (hbisection : ∀ o : {x : V // x ∉ U},
      ((@residualNeighbors V _ _ G (Classical.decRel G.Adj) R o.1).card : ℝ≥0) *
        (2 * (2 : ℝ≥0) ^ d * (3 / 4 : ℝ≥0) ^ (m - 2 * d)) < 1) :
    ∃ Knew : {x : V // x ∉ U} → BipartiteLink V,
      IsIntermediateLinkState G U A I D R Knew ∧
      (∀ o, (Knew o).center = outsideVertexEmbedding U o) ∧
      (∀ o, outsideVertexEmbedding U o ∉ U) ∧
      (∀ o, (Knew o).left ⊆ U) ∧
      (∀ o, (Knew o).right ⊆ U) ∧
      (∀ o, (Knew o).SpokesIn reserve) ∧
      (∀ o, HasLinkDegreeCodegreeBounds A (Knew o)
        d degreeMax codegree) := by
  subst U
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  have hchoice : ∀ o : {x : V // x ∉ W.U i.succ},
      ∃ K : BipartiteLink V,
        IsResidualBipartition G R o.1 K ∧
          HasLinkDegreeCodegreeBounds A K d degreeMax codegree := by
    intro o
    have hold := hstate.1 o
    have hresInner : residualNeighbors G R o.1 ⊆ W.U i.succ := by
      intro x hx
      rw [← hold.2.1] at hx
      rcases mem_union.mp hx with hx | hx
      · exact hleftOld o hx
      · exact hrightOld o hx
    exact htyp.exists_chosenResidualLink_of_supported_localized htri i hki hGsupp
      o.1 o.2 hresInner hold.residualNeighbors_even
      m d degreeMax codegree loss (hcovered o) hh hlower hupper hcodegree
      (hbisection o)
  let Knew : {x : V // x ∉ W.U i.succ} → BipartiteLink V :=
    fun o ↦ Classical.choose (hchoice o)
  have hKnew : ∀ o, IsResidualBipartition G R o.1 (Knew o) :=
    fun o ↦ (Classical.choose_spec (hchoice o)).1
  have hbounds : ∀ o, HasLinkDegreeCodegreeBounds A (Knew o)
      d degreeMax codegree :=
    fun o ↦ (Classical.choose_spec (hchoice o)).2
  have htransfer : ∀ o,
      (Knew o).left ⊆ W.U i.succ ∧
        (Knew o).right ⊆ W.U i.succ ∧
        (Knew o).SpokesIn reserve := by
    intro o
    exact (hstate.1 o).transfer_side_and_spoke_support (hKnew o)
      (hleftOld o) (hrightOld o) (hspokesOld o)
  refine ⟨Knew, ⟨hKnew, hstate.2.1, hstate.2.2⟩,
    ?_, ?_, ?_, ?_, ?_, hbounds⟩
  · intro o
    exact hKnew o |>.1
  · intro o
    exact o.2
  · intro o
    exact (htransfer o).1
  · intro o
    exact (htransfer o).2.1
  · intro o
    exact (htransfer o).2.2

/-- Coarser residual-link rechoice using the full covered degree. -/
theorem IsIterationTypical.exists_reserveSupportedTypicalResidualLinks
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {k : Fin (ell + 1)}
    {G : SimpleGraph V}
    {A I D R : TripleSystemOn V}
    {p eta xi : ℝ≥0} {h : ℕ}
    (htyp : IsIterationTypical W k G A p eta xi h)
    (htri : ConsistsOfTriangles G A)
    (i : Fin ell) (hki : k.val ≤ i.val)
    (hGsupp : GraphSupportedOn G (W.U i.castSucc : Set V))
    (U : Finset V) (hU : U = W.U i.succ)
    (reserve : Finset (Sym2 V))
    (Kold : {x : V // x ∉ U} → BipartiteLink V)
    (hstate : IsIntermediateLinkState G U A I D R Kold)
    (hleftOld : ∀ o, (Kold o).left ⊆ U)
    (hrightOld : ∀ o, (Kold o).right ⊆ U)
    (hspokesOld : ∀ o, (Kold o).SpokesIn reserve)
    (m d degreeMax codegree loss : ℕ)
    (hcovered : ∀ o : {x : V // x ∉ U},
      (coveredGraph R).degree o.1 ≤ loss)
    (hh : 3 ≤ h)
    (hlower : (m + loss + 1 : ℝ≥0) ≤
      (1 - xi) * (p ^ 2 * eta * (W.U i.succ).card))
    (hupper : (1 + xi) * (p ^ 2 * eta * (W.U i.succ).card) ≤
      (degreeMax : ℝ≥0))
    (hcodegree : (1 + xi) *
      (p ^ 3 * eta ^ 2 * (W.U i.succ).card) ≤ (codegree : ℝ≥0))
    (hbisection : ∀ o : {x : V // x ∉ U},
      ((@residualNeighbors V _ _ G (Classical.decRel G.Adj) R o.1).card : ℝ≥0) *
        (2 * (2 : ℝ≥0) ^ d * (3 / 4 : ℝ≥0) ^ (m - 2 * d)) < 1) :
    ∃ Knew : {x : V // x ∉ U} → BipartiteLink V,
      IsIntermediateLinkState G U A I D R Knew ∧
      (∀ o, (Knew o).center = outsideVertexEmbedding U o) ∧
      (∀ o, outsideVertexEmbedding U o ∉ U) ∧
      (∀ o, (Knew o).left ⊆ U) ∧
      (∀ o, (Knew o).right ⊆ U) ∧
      (∀ o, (Knew o).SpokesIn reserve) ∧
      (∀ o, HasLinkDegreeCodegreeBounds A (Knew o)
        d degreeMax codegree) := by
  apply htyp.exists_reserveSupportedTypicalResidualLinks_localized htri i hki
    hGsupp U hU reserve Kold hstate hleftOld hrightOld hspokesOld m d
      degreeMax codegree loss _ hh hlower hupper hcodegree hbisection
  intro o
  calc
    ((coveredGraph R).neighborFinset o.1 ∩ U).card ≤
        ((coveredGraph R).neighborFinset o.1).card :=
      card_le_card inter_subset_left
    _ = (coveredGraph R).degree o.1 := by
      rw [SimpleGraph.card_neighborFinset_eq_degree]
    _ ≤ loss := hcovered o

/-- Exact output of the typical residual-link rechoice at one state. -/
def HasReserveSupportedTypicalResidualLinks
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (reserve : Finset (Sym2 V))
    (A I D R : TripleSystemOn V)
    (d degreeMax codegree : ℕ) : Prop :=
  ∃ K : {x : V // x ∉ U} → BipartiteLink V,
    IsIntermediateLinkState G U A I D R K ∧
      (∀ o, (K o).center = outsideVertexEmbedding U o) ∧
      (∀ o, outsideVertexEmbedding U o ∉ U) ∧
      (∀ o, (K o).left ⊆ U) ∧
      (∀ o, (K o).right ⊆ U) ∧
      (∀ o, (K o).SpokesIn reserve) ∧
      (∀ o, HasLinkDegreeCodegreeBounds A (K o)
        d degreeMax codegree)

/-- Choose the typical residual-link family at ready states and empty links
elsewhere.  The fallback is used only to make the function total. -/
def supportedReserveTypicalResidualLinks
    {Omega V : Type*} [Fintype V] [DecidableEq V]
    (G : Omega → SimpleGraph V) (U : Finset V)
    (reserve : Omega → Finset (Sym2 V))
    (A I D R : Omega → TripleSystemOn V)
    (d degreeMax codegree : ℕ) (omega : Omega) :
    {x : V // x ∉ U} → BipartiteLink V := by
  classical
  if h : HasReserveSupportedTypicalResidualLinks (G omega) U
      (reserve omega) (A omega) (I omega) (D omega) (R omega)
      d degreeMax codegree then
    exact Classical.choose h
  else
    exact fun o ↦ emptyBipartiteLink (outsideVertexEmbedding U o)

/-- All properties not requiring the residual-state identity hold even in
the empty fallback branch.  This makes them available on every fiber of the
subsequent state-dependent link kernel. -/
theorem supportedReserveTypicalResidualLinks_global
    {Omega V : Type*} [Fintype V] [DecidableEq V]
    (G : Omega → SimpleGraph V) (U : Finset V)
    (reserve : Omega → Finset (Sym2 V))
    (A I D R : Omega → TripleSystemOn V)
    (d degreeMax codegree : ℕ) (omega : Omega) :
    let K := supportedReserveTypicalResidualLinks G U reserve A I D R
      d degreeMax codegree omega
    (∀ o, (K o).center = outsideVertexEmbedding U o) ∧
      (∀ o, outsideVertexEmbedding U o ∉ U) ∧
      (∀ o, (K o).left ⊆ U) ∧
      (∀ o, (K o).right ⊆ U) ∧
      (∀ o, (K o).SpokesIn (reserve omega)) ∧
      (∀ o, HasLinkDegreeCodegreeBounds (A omega) (K o)
        d degreeMax codegree) := by
  classical
  dsimp only
  by_cases hready : HasReserveSupportedTypicalResidualLinks (G omega) U
      (reserve omega) (A omega) (I omega) (D omega) (R omega)
      d degreeMax codegree
  · rw [supportedReserveTypicalResidualLinks, dif_pos hready]
    exact (Classical.choose_spec hready).2
  · rw [supportedReserveTypicalResidualLinks, dif_neg hready]
    refine ⟨fun _ ↦ rfl, fun o ↦ o.2, ?_, ?_, ?_, ?_⟩
    · intro o
      simp
    · intro o
      simp
    · intro o
      constructor <;> intro x hx <;> simp at hx
    · intro o
      exact emptyBipartiteLink_hasBounds
        (outsideVertexEmbedding U o) (A omega) d degreeMax codegree

theorem supportedReserveTypicalResidualLinks_ready
    {Omega V : Type*} [Fintype V] [DecidableEq V]
    (G : Omega → SimpleGraph V) (U : Finset V)
    (reserve : Omega → Finset (Sym2 V))
    (A I D R : Omega → TripleSystemOn V)
    (d degreeMax codegree : ℕ) (omega : Omega)
    (hready : HasReserveSupportedTypicalResidualLinks (G omega) U
      (reserve omega) (A omega) (I omega) (D omega) (R omega)
      d degreeMax codegree) :
    let K := supportedReserveTypicalResidualLinks G U reserve A I D R
      d degreeMax codegree omega
    IsIntermediateLinkState (G omega) U (A omega) (I omega) (D omega)
        (R omega) K ∧
      (∀ o, (K o).center = outsideVertexEmbedding U o) ∧
      (∀ o, outsideVertexEmbedding U o ∉ U) ∧
      (∀ o, (K o).left ⊆ U) ∧
      (∀ o, (K o).right ⊆ U) ∧
      (∀ o, (K o).SpokesIn (reserve omega)) ∧
      (∀ o, HasLinkDegreeCodegreeBounds (A omega) (K o)
        d degreeMax codegree) := by
  dsimp only
  rw [supportedReserveTypicalResidualLinks, dif_pos hready]
  exact Classical.choose_spec hready

/-- Supportwise readiness gives every structural and quantitative property
for the totalized rechosen links on the old law's support. -/
theorem FiniteLaw.SupportedOn.supportedReserveTypicalResidualLinks
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V]
    {law : FiniteLaw Omega}
    (G : Omega → SimpleGraph V) (U : Finset V)
    (reserve : Omega → Finset (Sym2 V))
    (A I D R : Omega → TripleSystemOn V)
    (d degreeMax codegree : ℕ)
    (hready : law.SupportedOn fun omega ↦
      HasReserveSupportedTypicalResidualLinks (G omega) U
        (reserve omega) (A omega) (I omega) (D omega) (R omega)
        d degreeMax codegree) :
    let K := supportedReserveTypicalResidualLinks G U reserve A I D R
      d degreeMax codegree
    law.SupportedOn fun omega ↦
      IsIntermediateLinkState (G omega) U (A omega) (I omega) (D omega)
          (R omega) (K omega) ∧
        (∀ o, (K omega o).center = outsideVertexEmbedding U o) ∧
        (∀ o, outsideVertexEmbedding U o ∉ U) ∧
        (∀ o, (K omega o).left ⊆ U) ∧
        (∀ o, (K omega o).right ⊆ U) ∧
        (∀ o, (K omega o).SpokesIn (reserve omega)) ∧
        (∀ o, HasLinkDegreeCodegreeBounds (A omega) (K omega o)
          d degreeMax codegree) := by
  dsimp only
  intro omega hmass
  exact supportedReserveTypicalResidualLinks_ready G U reserve A I D R
    d degreeMax codegree omega (hready omega hmass)

/-- Uniform pointwise typicality and loss estimates rechoose the residual
links at every positive-mass state.  This is the support-level bridge from
the preliminary/internal stage to the totalized typical-link function. -/
theorem FiniteLaw.SupportedOn.reserveSupportedTypicalResidualLinks_of_typical_localized
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V] {ell : ℕ}
    {law : FiniteLaw Omega} {W : Vortex V ell}
    {k : Fin (ell + 1)}
    {G : Omega → SimpleGraph V}
    {A I D R : Omega → TripleSystemOn V}
    {p eta xi : ℝ≥0} {h : ℕ}
    (i : Fin ell) (hki : k.val ≤ i.val)
    (U : Finset V) (hU : U = W.U i.succ)
    (reserve : Omega → Finset (Sym2 V))
    (Kold : (omega : Omega) → {x : V // x ∉ U} → BipartiteLink V)
    (htyp : law.SupportedOn fun omega ↦
      IsIterationTypical W k (G omega) (A omega) p eta xi h)
    (htri : law.SupportedOn fun omega ↦
      ConsistsOfTriangles (G omega) (A omega))
    (hGsupp : law.SupportedOn fun omega ↦
      GraphSupportedOn (G omega) (W.U i.castSucc : Set V))
    (hstate : law.SupportedOn fun omega ↦
      IsIntermediateLinkState (G omega) U (A omega) (I omega) (D omega)
          (R omega) (Kold omega) ∧
        (∀ o, (Kold omega o).center = outsideVertexEmbedding U o) ∧
        (∀ o, outsideVertexEmbedding U o ∉ U) ∧
        (∀ o, (Kold omega o).left ⊆ U) ∧
        (∀ o, (Kold omega o).right ⊆ U) ∧
        (∀ o, (Kold omega o).SpokesIn (reserve omega)))
    (m d degreeMax codegree loss : ℕ)
    (hcovered : law.SupportedOn fun omega ↦
      ∀ o : {x : V // x ∉ U},
        ((coveredGraph (R omega)).neighborFinset o.1 ∩ U).card ≤ loss)
    (hh : 3 ≤ h)
    (hlower : (m + loss + 1 : ℝ≥0) ≤
      (1 - xi) * (p ^ 2 * eta * (W.U i.succ).card))
    (hupper : (1 + xi) *
      (p ^ 2 * eta * (W.U i.succ).card) ≤ (degreeMax : ℝ≥0))
    (hcodegree : (1 + xi) *
      (p ^ 3 * eta ^ 2 * (W.U i.succ).card) ≤ (codegree : ℝ≥0))
    (hbisection : ∀ omega, 0 < law.mass omega →
      ∀ o : {x : V // x ∉ U},
      ((@residualNeighbors V _ _ (G omega)
          (Classical.decRel (G omega).Adj) (R omega) o.1).card : ℝ≥0) *
        (2 * (2 : ℝ≥0) ^ d * (3 / 4 : ℝ≥0) ^ (m - 2 * d)) < 1) :
    law.SupportedOn fun omega ↦
      HasReserveSupportedTypicalResidualLinks
        (G omega) U (reserve omega) (A omega) (I omega) (D omega)
        (R omega) d degreeMax codegree := by
  intro omega hmass
  have hs := hstate omega hmass
  obtain ⟨Knew, hKnew⟩ :=
    (htyp omega hmass).exists_reserveSupportedTypicalResidualLinks_localized
      (htri omega hmass) i hki (hGsupp omega hmass) U hU
      (reserve omega) (Kold omega) hs.1 hs.2.2.2.1 hs.2.2.2.2.1
      hs.2.2.2.2.2 m d degreeMax codegree loss
      (hcovered omega hmass) hh hlower hupper hcodegree
      (hbisection omega hmass)
  exact ⟨Knew, hKnew⟩

/-- Coarser support-level bridge using full covered degrees. -/
theorem FiniteLaw.SupportedOn.reserveSupportedTypicalResidualLinks_of_typical
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V] {ell : ℕ}
    {law : FiniteLaw Omega} {W : Vortex V ell}
    {k : Fin (ell + 1)}
    {G : Omega → SimpleGraph V}
    {A I D R : Omega → TripleSystemOn V}
    {p eta xi : ℝ≥0} {h : ℕ}
    (i : Fin ell) (hki : k.val ≤ i.val)
    (U : Finset V) (hU : U = W.U i.succ)
    (reserve : Omega → Finset (Sym2 V))
    (Kold : (omega : Omega) → {x : V // x ∉ U} → BipartiteLink V)
    (htyp : law.SupportedOn fun omega ↦
      IsIterationTypical W k (G omega) (A omega) p eta xi h)
    (htri : law.SupportedOn fun omega ↦
      ConsistsOfTriangles (G omega) (A omega))
    (hGsupp : law.SupportedOn fun omega ↦
      GraphSupportedOn (G omega) (W.U i.castSucc : Set V))
    (hstate : law.SupportedOn fun omega ↦
      IsIntermediateLinkState (G omega) U (A omega) (I omega) (D omega)
          (R omega) (Kold omega) ∧
        (∀ o, (Kold omega o).center = outsideVertexEmbedding U o) ∧
        (∀ o, outsideVertexEmbedding U o ∉ U) ∧
        (∀ o, (Kold omega o).left ⊆ U) ∧
        (∀ o, (Kold omega o).right ⊆ U) ∧
        (∀ o, (Kold omega o).SpokesIn (reserve omega)))
    (m d degreeMax codegree loss : ℕ)
    (hcovered : law.SupportedOn fun omega ↦
      ∀ o : {x : V // x ∉ U},
        (coveredGraph (R omega)).degree o.1 ≤ loss)
    (hh : 3 ≤ h)
    (hlower : (m + loss + 1 : ℝ≥0) ≤
      (1 - xi) * (p ^ 2 * eta * (W.U i.succ).card))
    (hupper : (1 + xi) *
      (p ^ 2 * eta * (W.U i.succ).card) ≤ (degreeMax : ℝ≥0))
    (hcodegree : (1 + xi) *
      (p ^ 3 * eta ^ 2 * (W.U i.succ).card) ≤ (codegree : ℝ≥0))
    (hbisection : ∀ omega, 0 < law.mass omega →
      ∀ o : {x : V // x ∉ U},
      ((@residualNeighbors V _ _ (G omega)
          (Classical.decRel (G omega).Adj) (R omega) o.1).card : ℝ≥0) *
        (2 * (2 : ℝ≥0) ^ d * (3 / 4 : ℝ≥0) ^ (m - 2 * d)) < 1) :
    law.SupportedOn fun omega ↦
      HasReserveSupportedTypicalResidualLinks
        (G omega) U (reserve omega) (A omega) (I omega) (D omega)
        (R omega) d degreeMax codegree := by
  apply FiniteLaw.SupportedOn.reserveSupportedTypicalResidualLinks_of_typical_localized
    i hki U hU reserve Kold htyp htri hGsupp hstate m d degreeMax codegree
      loss _ hh hlower hupper hcodegree hbisection
  intro omega hmass o
  calc
    ((coveredGraph (R omega)).neighborFinset o.1 ∩ U).card ≤
        ((coveredGraph (R omega)).neighborFinset o.1).card :=
      card_le_card inter_subset_left
    _ = (coveredGraph (R omega)).degree o.1 := by
      rw [SimpleGraph.card_neighborFinset_eq_degree]
    _ ≤ loss := hcovered omega hmass o

/-- Uniform scalar mixing gives the exact robust-Hall candidate count on a
typical balanced link.  The zero-side case has no Hall obstruction. -/
theorem HasLinkDegreeCodegreeBounds.orientedSmallHallCandidateBound_of_uniform
    {V : Type*} [Fintype V] [DecidableEq V]
    {available : TripleSystemOn V} {K : BipartiteLink V}
    {d degreeMax codegree : ℕ}
    (htyp : HasLinkDegreeCodegreeBounds available K d degreeMax codegree)
    (Delta groupSize density candidate cutoff : ℕ)
    (hbalanced : K.left.card = K.right.card)
    (hdensityLe : density ≤ d)
    (hmixing : 0 < K.right.card → ∀ s : ℕ,
      cutoff < s → s ≤ K.right.card →
        K.right.card * (degreeMax + codegree * s) <
          s * (d - density) ^ 2)
    (hdegreeScalar : Delta * groupSize + groupSize ≤ d - cutoff)
    (hd : 2 ≤ d) (hdensityScalar : 3 * candidate ≤ density)
    (hcandidateScalar : Delta * groupSize + groupSize ≤ candidate) :
    ∀ o : OrientedSmallHallObstruction ↑K.left ↑K.right,
      (Delta * orientedSmallHallSize o + 1) * groupSize ≤
        (orientedSmallHallCandidates
          (linkAvailableRelation K available) o).card := by
  by_cases hpositive : 0 < K.right.card
  · have hmoments := balancedLink_secondMomentScalars_of_uniform K d
      degreeMax codegree density cutoff hbalanced hpositive hdensityLe
      (hmixing hpositive)
    exact htyp.orientedSmallHallCandidateBound Delta groupSize density
      candidate cutoff hbalanced hpositive hmoments.1 hmoments.2
      hdegreeScalar
      (htyp.candidate_density_scalar_of_three hbalanced hpositive hd
        hdensityScalar)
      hcandidateScalar
  · have hright : K.right.card = 0 := by omega
    have hleft : K.left.card = 0 := by omega
    intro o
    exfalso
    rcases o with o | o
    · have hSle : o.1.1.1.card ≤ K.left.card := by
        simpa using o.1.1.1.card_le_univ
      have hT := o.1.2
      omega
    · have hSle : o.1.1.1.card ≤ K.right.card := by
        simpa using o.1.1.1.card_le_univ
      have hT := o.1.2
      omega

end

end Erdos207
