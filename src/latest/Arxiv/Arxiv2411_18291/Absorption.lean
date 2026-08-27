import Arxiv.Arxiv2411_18291.Decomposition

/-!
# The deterministic completion step of the absorption argument

This module proves the algebraic last step in Section 2. It does not assume
or assert the existence of the sparse absorber: constructing that absorber
is a separate part of the paper's proof.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {q r : ℕ}

/-- An absorber is disjoint from its reserve and absorbs every divisible
subgraph of that reserve. -/
def IsAbsorber (q : ℕ) (A R : Hypergraph V r) : Prop :=
  Disjoint A R ∧
    ∀ L : Hypergraph V r, L ⊆ R → Divisible q L → HasDecomposition q (A ∪ L)

theorem IsAbsorber.hasDecomposition {A R : Hypergraph V r} (h : IsAbsorber q A R) :
    HasDecomposition q A := by
  simpa only [union_empty] using h.2 ∅ (empty_subset R) Divisible.empty

theorem IsAbsorber.divisible {A R : Hypergraph V r} (h : IsAbsorber q A R) :
    Divisible q A := h.hasDecomposition.divisible

/-- Once a decomposition leaves only reserve edges outside an absorber, the
absorber completes it. Divisibility of the leave is proved by subtraction. -/
theorem absorption_completion (hqr : r ≤ q) {C A R B : Hypergraph V r}
    (hC : Divisible q C) (hA : A ⊆ C) (habs : IsAbsorber q A R)
    (hB : HasDecomposition q B) (hBA : B ⊆ C \ A)
    (hleave : (C \ A) \ B ⊆ R) : HasDecomposition q C := by
  have hL : Divisible q ((C \ A) \ B) :=
    (hC.sdiff habs.divisible hA).sdiff hB.divisible hBA
  have hAL := habs.2 ((C \ A) \ B) hleave hL
  have hdis : Disjoint B (A ∪ ((C \ A) \ B)) := by
    apply Finset.disjoint_left.mpr
    intro e heB heAL
    rcases mem_union.mp heAL with heA | heL
    · exact (mem_sdiff.mp (hBA heB)).2 heA
    · exact (mem_sdiff.mp heL).2 heB
  have hcover : B ∪ (A ∪ ((C \ A) \ B)) = C := by
    rw [union_left_comm, union_sdiff_of_subset hBA, union_sdiff_of_subset hA]
  simpa only [hcover] using hB.union hqr hAL hdis

/-- Specialization to the complete hypergraph used in Theorem 1.1. -/
theorem complete_of_absorber (hqr : r ≤ q) {A R B : Hypergraph V r}
    (hC : Divisible q (complete V r)) (habs : IsAbsorber q A R)
    (hB : HasDecomposition q B) (hBA : B ⊆ complete V r \ A)
    (hleave : (complete V r \ A) \ B ⊆ R) : HasDecomposition q (complete V r) :=
  absorption_completion hqr hC (subset_univ _) habs hB hBA hleave

end Arxiv2411_18291
