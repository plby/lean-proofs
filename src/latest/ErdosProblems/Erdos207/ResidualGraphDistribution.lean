/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.GraphDistributionConditioning
import ErdosProblems.Erdos207.StrongWellDistributedAdjoin

/-! # Compatible graph prescriptions: edges uncovered by the entire selected union

An edge of a later selected triangle is already known to be uncovered by
the initial family. Requiring residual edges after both selected families
removes that redundant density charge. The older interfaces are unchanged.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem IsPackingOn.disjoint_family_edges
    {V : Type*} [Fintype V] [DecidableEq V]
    {I D : TripleSystemOn V} (hpack : IsPackingOn (I ∪ D)) (hdis : Disjoint I D) :
    Disjoint (I.biUnion tripleEdgeFinset) (D.biUnion tripleEdgeFinset) := by
  apply disjoint_left.mpr
  intro e heI heD
  obtain ⟨T, hT, heT⟩ := mem_biUnion.mp heI
  obtain ⟨U, hU, heU⟩ := mem_biUnion.mp heD
  have hne : T ≠ U := by
    intro heq
    exact disjoint_left.mp hdis hT (heq.symm ▸ hU)
  have hpair := hpack.isTriangleDecomposition.pairwiseDisjoint_tripleEdgeFinset
    (mem_union_left D hT) (mem_union_right I hU) hne
  exact disjoint_left.mp hpair heT heU

def ResidualDistributionEvent
    {Ω V : Type*} [Fintype V] [DecidableEq V]
    (initial later : Ω → TripleSystemOn V) (Ifix Dfix : TripleSystemOn V)
    (Efix : Finset (Sym2 V)) (ω : Ω) : Prop :=
  Ifix ⊆ initial ω ∧ Dfix ⊆ later ω ∧
    ∀ e ∈ Efix, e ∉ (coveredGraph (initial ω ∪ later ω)).edgeSet

def IsResidualGraphStronglyWellDistributed
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] {ell : ℕ}
    (L : FiniteLaw Ω) (W : Vortex V ell) (k : Fin (ell + 1)) (G : SimpleGraph V)
    (initial later : Ω → TripleSystemOn V) (p C b : ℝ≥0) : Prop :=
  ∀ (Ifix Dfix : TripleSystemOn V) (Efix : Finset (Sym2 V)),
    Disjoint Ifix Dfix → Efix ⊆ graphEdges G →
    L.probability (ResidualDistributionEvent initial later Ifix Dfix Efix) ≤
      C ^ (Ifix.card + Dfix.card + Efix.card) *
        (p ^ Efix.card * (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card * laterTriangleScale W k p Dfix + b)

theorem ResidualDistributionEvent.toStrong
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V]
    {initial later : Ω → TripleSystemOn V} {Ifix Dfix : TripleSystemOn V}
    {Efix : Finset (Sym2 V)} {ω : Ω}
    (h : ResidualDistributionEvent initial later Ifix Dfix Efix ω) :
    StrongDistributionEvent initial later Ifix Dfix Efix ω := by
  refine ⟨h.1, h.2.1, ?_⟩
  intro e he hcovered
  apply h.2.2 e he
  rw [coveredGraph_edgeSet_eq_biUnion] at hcovered ⊢
  obtain ⟨T, hT, heT⟩ := mem_biUnion.mp hcovered
  exact mem_biUnion.mpr ⟨T, mem_union_left _ hT, heT⟩

theorem IsGraphStronglyWellDistributed.toResidual
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Ω} {W : Vortex V ell} {k : Fin (ell + 1)} {G : SimpleGraph V}
    {initial later : Ω → TripleSystemOn V} {p C b : ℝ≥0}
    (h : IsGraphStronglyWellDistributed L W k G initial later p C b) :
    IsResidualGraphStronglyWellDistributed L W k G initial later p C b := by
  intro Ifix Dfix Efix hdis hE
  exact (L.probability_mono (fun _ hω ↦ hω.toStrong)).trans (h Ifix Dfix Efix hdis hE)

theorem IsInitialGraphProductBound.toResidualGraphStronglyWellDistributed
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Ω} {selected : Ω → TripleSystemOn V} {G : SimpleGraph V} {p C b : ℝ≥0}
    (h : IsInitialGraphProductBound L selected G p C b) (W : Vortex V ell) (k : Fin (ell + 1)) :
    IsResidualGraphStronglyWellDistributed L W k G selected (fun _ ↦ ∅) p C b :=
  (h.toGraphStronglyWellDistributed W k).toResidual

theorem IsResidualGraphStronglyWellDistributed.mono
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Ω} {W : Vortex V ell} {k : Fin (ell + 1)} {G : SimpleGraph V}
    {initial later : Ω → TripleSystemOn V} {p C C' b b' : ℝ≥0}
    (h : IsResidualGraphStronglyWellDistributed L W k G initial later p C b)
    (hC : C ≤ C') (hb : b ≤ b') :
    IsResidualGraphStronglyWellDistributed L W k G initial later p C' b' := by
  intro Ifix Dfix Efix hdis hE
  exact (h Ifix Dfix Efix hdis hE).trans (by gcongr)

/-- The empty test graph retains exactly the selected-only part of the old
interface, allowing all previously checked selected-only tails to be reused. -/
theorem IsResidualGraphStronglyWellDistributed.toGraphStrongEmpty
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Ω} {W : Vortex V ell} {k : Fin (ell + 1)} {G : SimpleGraph V}
    {initial later : Ω → TripleSystemOn V} {p C b : ℝ≥0}
    (h : IsResidualGraphStronglyWellDistributed L W k G initial later p C b) :
    IsGraphStronglyWellDistributed L W k ⊥ initial later p C b := by
  intro Ifix Dfix Efix hdis hE
  have hEempty : Efix = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro e he
    have hempty := mem_graphEdges_iff.mp (hE he)
    simp at hempty
  subst Efix
  have hevent : ResidualDistributionEvent initial later Ifix Dfix ∅ =
      StrongDistributionEvent initial later Ifix Dfix ∅ := by
    funext ω
    simp [ResidualDistributionEvent, StrongDistributionEvent]
  rw [← hevent]
  exact h Ifix Dfix ∅ hdis (empty_subset _)

theorem IsResidualGraphStronglyWellDistributed.map
    {Ω Ξ V : Type*} [Fintype Ω] [Fintype Ξ] [DecidableEq Ξ] [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Ω} (f : Ω → Ξ) {W : Vortex V ell} {k : Fin (ell + 1)} {G : SimpleGraph V}
    {initial later : Ξ → TripleSystemOn V} {p C b : ℝ≥0}
    (h : IsResidualGraphStronglyWellDistributed L W k G
      (fun ω ↦ initial (f ω)) (fun ω ↦ later (f ω)) p C b) :
    IsResidualGraphStronglyWellDistributed (L.map f) W k G initial later p C b := by
  intro Ifix Dfix Efix hdis hE
  rw [FiniteLaw.probability_map]
  have hevent : (fun ω ↦ ResidualDistributionEvent initial later Ifix Dfix Efix (f ω)) =
      ResidualDistributionEvent (fun ω ↦ initial (f ω)) (fun ω ↦ later (f ω)) Ifix Dfix Efix := by
    funext ω
    rfl
  rw [hevent]
  exact h Ifix Dfix Efix hdis hE

theorem IsResidualGraphStronglyWellDistributed.conditionOn
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Ω} {W : Vortex V ell} {k : Fin (ell + 1)} {G : SimpleGraph V}
    {initial later : Ω → TripleSystemOn V} {p C b : ℝ≥0}
    (h : IsResidualGraphStronglyWellDistributed L W k G initial later p C b)
    (Good : Ω → Prop) (hGood : 0 < L.probability Good) :
    IsResidualGraphStronglyWellDistributed (L.conditionOn Good hGood) W k G
      initial later p (C / L.probability Good) b := by
  intro Ifix Dfix Efix hdis hE
  let m := Ifix.card + Dfix.card + Efix.card
  let X := p ^ Efix.card * (Fintype.card V : ℝ≥0)⁻¹ ^ Ifix.card * laterTriangleScale W k p Dfix + b
  by_cases hm : m = 0
  · have hI : Ifix = ∅ := card_eq_zero.mp (by dsimp only [m] at hm; omega)
    have hD : Dfix = ∅ := card_eq_zero.mp (by dsimp only [m] at hm; omega)
    have hE' : Efix = ∅ := card_eq_zero.mp (by dsimp only [m] at hm; omega)
    subst Ifix
    subst Dfix
    subst Efix
    exact ((L.conditionOn Good hGood).probability_le_one _).trans (by simp)
  · have hzpow : L.probability Good ^ m ≤ L.probability Good :=
      pow_le_of_le_one zero_le (L.probability_le_one Good) hm
    have hscale : C ^ m / L.probability Good ≤ (C / L.probability Good) ^ m := by
      rw [div_pow]
      gcongr
    calc
      _ ≤ L.probability (ResidualDistributionEvent initial later Ifix Dfix Efix) / L.probability Good :=
        L.conditionOn_probability_le Good _ hGood
      _ ≤ (C ^ m * X) / L.probability Good := div_le_div_of_nonneg_right (h Ifix Dfix Efix hdis hE) zero_le
      _ = (C ^ m / L.probability Good) * X := by ring
      _ ≤ (C / L.probability Good) ^ m * X := mul_le_mul_of_nonneg_right hscale zero_le

end

end Erdos207
