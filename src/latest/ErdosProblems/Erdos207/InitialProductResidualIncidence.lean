/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InitialProductReserveOne
import ErdosProblems.Erdos207.PreliminaryResidualInternal

/-!
# Residual-incidence conditioning for the initial product law

The long initial sparsification produces an `IsInitialProductBound`, rather
than the pure preliminary product law used by later master stages.  For an
`r`-edge residual witness the former gives the exact bound
`(C * p)^r + C^r * b`.  A finite witness union therefore supplies the
bounded residual-incidence event needed by the raw internal cover.  After
conditioning, the initial-family strong law is retained by the ordinary
finite conditioning lemma.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- The explicit witness-union tail for residual incidence under an initial
product law.  The second summand is the amplified uniform stopping error. -/
def initialProductResidualOuterIncidenceTail
    (V : Type*) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V)
    (p C b : ℝ≥0) (r : ℕ) : ℝ≥0 :=
  ∑ v : V, ((outerIncidentEdges G U v).powersetCard r).card *
    ((C * p) ^ r + C ^ r * b)

/-- Inclusion in the residual outer graph implies that every prescribed
pair is uncovered by the selected family. -/
lemma subset_uncovered_of_subset_preliminaryResidualOuterEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {U : Finset V}
    {P : TripleSystemOn V} {E : Finset (Sym2 V)}
    (hE : E ⊆ preliminaryResidualOuterEdges G U P) :
    ∀ e ∈ E, e ∉ (coveredGraph P).edgeSet := by
  intro e heE heCovered
  have heResidual := hE heE
  exact (mem_sdiff.mp heResidual).2 (mem_graphEdges_iff.mpr heCovered)

/-- At a fixed witness cardinality, an initial product law gives the mixed
edge-only estimate required by the residual-incidence union bound. -/
theorem IsInitialProductBound.probability_residualOuterWitness_le
    {Omega V : Type*} [Fintype Omega] [Fintype V]
    [DecidableEq V]
    {L : FiniteLaw Omega} {selected : Omega → TripleSystemOn V}
    {p C b : ℝ≥0}
    (hproduct : IsInitialProductBound L selected p C b)
    (G : SimpleGraph V) (U : Finset V)
    (E : Finset (Sym2 V)) :
    L.probability (fun omega ↦
        E ⊆ preliminaryResidualOuterEdges G U (selected omega)) ≤
      (C * p) ^ E.card + C ^ E.card * b := by
  have hmono : L.probability (fun omega ↦
        E ⊆ preliminaryResidualOuterEdges G U (selected omega)) ≤
      L.probability (fun omega ↦
        (∅ : TripleSystemOn V) ⊆ selected omega ∧
          ∀ e ∈ E,
            e ∉ (coveredGraph (selected omega)).edgeSet) := by
    apply L.probability_mono
    intro omega hE
    exact ⟨empty_subset _,
      subset_uncovered_of_subset_preliminaryResidualOuterEdges hE⟩
  calc
    L.probability (fun omega ↦
        E ⊆ preliminaryResidualOuterEdges G U (selected omega)) ≤
      L.probability (fun omega ↦
        (∅ : TripleSystemOn V) ⊆ selected omega ∧
          ∀ e ∈ E,
            e ∉ (coveredGraph (selected omega)).edgeSet) := hmono
    _ ≤ C ^ E.card * (p ^ E.card + b) := by
      simpa using hproduct (∅ : TripleSystemOn V) E
    _ = (C * p) ^ E.card + C ^ E.card * b := by
      rw [mul_add, mul_pow]

/-- The probability that some residual outer star has at least `r` edges is
bounded by the explicit initial-product tail. -/
theorem IsInitialProductBound.probability_exists_large_residualOuter_incidence_le
    {Omega V : Type*} [Fintype Omega] [Fintype V]
    [DecidableEq V]
    {L : FiniteLaw Omega} {selected : Omega → TripleSystemOn V}
    {p C b : ℝ≥0}
    (hproduct : IsInitialProductBound L selected p C b)
    (G : SimpleGraph V) (U : Finset V) (r : ℕ) :
    L.probability (fun omega ↦ ∃ v : V,
        r ≤ (outerIncidentEdges G U v ∩
          preliminaryResidualOuterEdges G U (selected omega)).card) ≤
      initialProductResidualOuterIncidenceTail V G U p C b r := by
  classical
  calc
    L.probability (fun omega ↦ ∃ v : V,
        r ≤ (outerIncidentEdges G U v ∩
          preliminaryResidualOuterEdges G U (selected omega)).card) ≤
      ∑ v ∈ (univ : Finset V), L.probability (fun omega ↦
        r ≤ (outerIncidentEdges G U v ∩
          preliminaryResidualOuterEdges G U (selected omega)).card) := by
      simpa using L.probability_exists_le (univ : Finset V)
        (fun v omega ↦ r ≤ (outerIncidentEdges G U v ∩
          preliminaryResidualOuterEdges G U (selected omega)).card)
    _ ≤ ∑ v ∈ (univ : Finset V),
        ((outerIncidentEdges G U v).powersetCard r).card *
          ((C * p) ^ r + C ^ r * b) := by
      apply sum_le_sum
      intro v _hv
      let event : Finset (Sym2 V) → Omega → Prop := fun E omega ↦
        E ⊆ preliminaryResidualOuterEdges G U (selected omega)
      calc
        L.probability (fun omega ↦
            r ≤ (outerIncidentEdges G U v ∩
              preliminaryResidualOuterEdges G U (selected omega)).card) ≤
          L.probability (fun omega ↦ ∃ E ∈
            (outerIncidentEdges G U v).powersetCard r, event E omega) := by
            apply L.probability_mono
            intro omega hlarge
            obtain ⟨E, hEsub, hEcard⟩ := exists_subset_card_eq hlarge
            exact ⟨E, mem_powersetCard.mpr
              ⟨hEsub.trans inter_subset_left, hEcard⟩,
              hEsub.trans inter_subset_right⟩
        _ ≤ ∑ E ∈ (outerIncidentEdges G U v).powersetCard r,
            L.probability (event E) :=
          L.probability_exists_le
            ((outerIncidentEdges G U v).powersetCard r) event
        _ ≤ ∑ _E ∈ (outerIncidentEdges G U v).powersetCard r,
            ((C * p) ^ r + C ^ r * b) := by
          apply sum_le_sum
          intro E hE
          have hcard : E.card = r := (mem_powersetCard.mp hE).2
          simpa only [event, hcard] using
            hproduct.probability_residualOuterWitness_le G U E
        _ = ((outerIncidentEdges G U v).powersetCard r).card *
            ((C * p) ^ r + C ^ r * b) := by
          simp only [sum_const, nsmul_eq_mul, mul_add, mul_pow]
    _ = initialProductResidualOuterIncidenceTail V G U p C b r := by
      simp [initialProductResidualOuterIncidenceTail]

/-- Condition the initial sparsification on uniformly bounded residual outer
incidence.  Its probability has the stated positive lower bound, and its
reserve-aware strong law survives with only the standard reciprocal loss in
the multiplicative constant. -/
theorem IsInitialProductBound.exists_conditionedOn_residualOuterIncidence
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Omega} {W : Vortex V ell} {k : Fin (ell + 1)}
    {selected : Omega → TripleSystemOn V}
    {reserve : Omega → Finset (Sym2 V)}
    {p C b : ℝ≥0}
    (hproduct : IsInitialProductBound L selected p C b)
    (hC : 1 ≤ C) (G : SimpleGraph V) (U : Finset V) (r : ℕ)
    (htail : initialProductResidualOuterIncidenceTail V G U p C b r < 1) :
    let Good : Omega → Prop := fun omega ↦ ∀ v : V,
      (outerIncidentEdges G U v ∩
        preliminaryResidualOuterEdges G U (selected omega)).card < r
    ∃ hGood : 0 < L.probability Good,
      (L.conditionOn Good hGood).SupportedOn Good ∧
      1 - initialProductResidualOuterIncidenceTail V G U p C b r ≤
        L.probability Good ∧
      IsReserveStronglyWellDistributed (L.conditionOn Good hGood) W k
        selected (fun _ ↦ (∅ : TripleSystemOn V)) reserve p 1
        (C / L.probability Good) b := by
  classical
  dsimp only
  let Bad : Omega → Prop := fun omega ↦ ∃ v : V,
    r ≤ (outerIncidentEdges G U v ∩
      preliminaryResidualOuterEdges G U (selected omega)).card
  let Good : Omega → Prop := fun omega ↦ ∀ v : V,
    (outerIncidentEdges G U v ∩
      preliminaryResidualOuterEdges G U (selected omega)).card < r
  have hbad : L.probability Bad ≤
      initialProductResidualOuterIncidenceTail V G U p C b r := by
    simpa only [Bad] using
      hproduct.probability_exists_large_residualOuter_incidence_le G U r
  have hbadlt : L.probability Bad < 1 := hbad.trans_lt htail
  have hGoodEq : L.probability Good = 1 - L.probability Bad := by
    rw [← L.probability_not Bad]
    congr 1
    funext omega
    simp only [Good, Bad]
    push_neg
    rfl
  have hlower :
      1 - initialProductResidualOuterIncidenceTail V G U p C b r ≤
        L.probability Good := by
    rw [hGoodEq]
    exact tsub_le_tsub_left hbad 1
  have hGood : 0 < L.probability Good := by
    rw [hGoodEq]
    exact tsub_pos_iff_lt.mpr hbadlt
  refine ⟨hGood, L.conditionOn_supported Good hGood, hlower, ?_⟩
  exact (hproduct.toReserveStronglyWellDistributed_one
    (W := W) (k := k) (reserve := reserve) hC).conditionOn Good hGood

end

end Erdos207
