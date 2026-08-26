import Mathlib
import ErdosProblems.Erdos550.RegularityRetention
import ErdosProblems.Erdos550.RegularityAlphaQ

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Exact regularity-partition data for the direct off-Turán proof

The older density-transfer wrappers retained only one-way information about
the reduced graph.  The independence argument needs the converse as well:
nonedges are precisely irregular pairs or regular pairs below the density
threshold.  This module therefore keeps the actual Szemerédi partition and
defines its reduced graph by an exact adjacency predicate.
-/

open SimpleGraph Finset Finpartition SzemerediRegularity

namespace Erdos550

open Classical

/-- The forbidden complete `(q+1)`-partite red graph has its canonical
`(q+1)`-colouring. -/
lemma Kmult_colorable (q : ℕ) (m : Fin (q + 1) → ℕ) :
    (Kmult (q + 1) m).Colorable (q + 1) := by
  simpa [Kmult] using!
    completeMultipartiteGraph.colorable
      (fun i : Fin (q + 1) => Fin (m i))

/-- The exact cluster graph: distinct parts are adjacent exactly when their
pair is `ε`-uniform and has density at least `d`. -/
def offTuranReducedGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (Finset.univ : Finset V))
    (ε d : ℝ) : SimpleGraph {C // C ∈ P.parts} where
  Adj C D :=
    C ≠ D ∧ G.IsUniform ε C.1 D.1 ∧
      d ≤ (G.edgeDensity C.1 D.1 : ℝ)
  symm := ⟨fun C D h =>
    ⟨h.1.symm, h.2.1.symm, by
      simpa only [SimpleGraph.edgeDensity_comm] using! h.2.2⟩⟩
  loopless := ⟨fun C h => h.1 rfl⟩

noncomputable instance offTuranReducedGraph.instDecidableRel
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (Finset.univ : Finset V))
    (ε d : ℝ) :
    DecidableRel (offTuranReducedGraph G P ε d).Adj :=
  Classical.decRel _

@[simp] lemma offTuranReducedGraph_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : Finpartition (Finset.univ : Finset V))
    (ε d : ℝ) (C D : {C // C ∈ P.parts}) :
    (offTuranReducedGraph G P ε d).Adj C D ↔
      C ≠ D ∧ G.IsUniform ε C.1 D.1 ∧
        d ≤ (G.edgeDensity C.1 D.1 : ℝ) :=
  Iff.rfl

/-- Keep the complete output of Mathlib's regularity theorem, in particular
the partition itself rather than only an opaque cluster family. -/
theorem exists_offTuran_regular_partition
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (ε : ℝ) (hε : 0 < ε)
    (hcard : ⌈4 / ε⌉₊ ≤ Fintype.card V) :
    ∃ P : Finpartition (Finset.univ : Finset V),
      P.IsEquipartition ∧
      ⌈4 / ε⌉₊ ≤ P.parts.card ∧
      P.parts.card ≤ SzemerediRegularity.bound ε ⌈4 / ε⌉₊ ∧
      P.IsUniform G ε := by
  obtain ⟨P, heq, hlo, hhi, huni⟩ :=
    szemeredi_regularity G hε hcard
  exact ⟨P, heq, hlo, hhi, huni⟩

/-- Exact `α(Q)` edge form for the reduced graph just defined. -/
theorem offTuran_reduced_family_has_edge
    {W : Type} [Fintype W] (F : SimpleGraph W)
    (q : ℕ) (hcol : F.Colorable (q + 1)) (hq : 1 ≤ q)
    (d : ℝ) (hd1 : d < 1)
    (ε₀ : ℝ) (m₀ : ℕ)
    (hcap : ∀ {V : Type} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj], ¬ (F ⊑ Gᶜ) →
      ∀ (ε : ℝ), 0 ≤ ε → ε ≤ ε₀ →
      ∀ (P : Finpartition (univ : Finset V)), P.IsUniform G ε →
      ∀ (A : Finset {C // C ∈ P.parts}),
        4 * q ^ 2 ≤ A.card →
        ((P.parts.card : ℝ) ^ 2 * ε <
          (A.card : ℝ) ^ 2 / (4 * q)) →
        (∀ C ∈ A, m₀ ≤ C.1.card) →
        ∃ C ∈ A, ∃ D ∈ A, C ≠ D ∧ G.IsUniform ε C.1 D.1 ∧
          d ≤ (G.edgeDensity C.1 D.1 : ℝ))
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hF : ¬ (F ⊑ Gᶜ))
    (ε : ℝ) (hε0 : 0 ≤ ε) (hεcap : ε ≤ ε₀)
    (P : Finpartition (univ : Finset V)) (hP : P.IsUniform G ε)
    (A : Finset {C // C ∈ P.parts})
    (hbig : 4 * q ^ 2 ≤ A.card)
    (hirr : (P.parts.card : ℝ) ^ 2 * ε <
      (A.card : ℝ) ^ 2 / (4 * q))
    (hsize : ∀ C ∈ A, m₀ ≤ C.1.card) :
    ∃ C ∈ A, ∃ D ∈ A,
      (offTuranReducedGraph G P ε d).Adj C D := by
  obtain ⟨C, hCA, D, hDA, hCD, huni, hdens⟩ :=
    hcap G hF ε hε0 hεcap P hP A hbig hirr hsize
  exact ⟨C, hCA, D, hDA, hCD, huni, hdens⟩

/-- Packaged source of the cap used by
`offTuran_reduced_family_has_edge`. -/
theorem exists_offTuran_reduced_family_edge_cap
    {W : Type} [Fintype W] (F : SimpleGraph W)
    (q : ℕ) (hcol : F.Colorable (q + 1)) (hq : 1 ≤ q)
    (d : ℝ) (hd1 : d < 1) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ m₀ : ℕ,
      ∀ {V : Type} [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj], ¬ (F ⊑ Gᶜ) →
        ∀ (ε : ℝ), 0 ≤ ε → ε ≤ ε₀ →
        ∀ (P : Finpartition (univ : Finset V)), P.IsUniform G ε →
        ∀ (A : Finset {C // C ∈ P.parts}),
          4 * q ^ 2 ≤ A.card →
          ((P.parts.card : ℝ) ^ 2 * ε <
            (A.card : ℝ) ^ 2 / (4 * q)) →
          (∀ C ∈ A, m₀ ≤ C.1.card) →
          ∃ C ∈ A, ∃ D ∈ A,
            (offTuranReducedGraph G P ε d).Adj C D := by
  obtain ⟨ε₀, hε₀, m₀, hcap⟩ :=
    regularity_dense_regular_pair F q hcol hq d hd1
  exact ⟨ε₀, hε₀, m₀, fun G _ hF ε hε0 hεcap P hP A hbig hirr hsize =>
    offTuran_reduced_family_has_edge F q hcol hq d hd1 ε₀ m₀ hcap
      G hF ε hε0 hεcap P hP A hbig hirr hsize⟩

end Erdos550
