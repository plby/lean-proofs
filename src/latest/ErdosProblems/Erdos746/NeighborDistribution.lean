import ErdosProblems.Erdos746.Posa
import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs
import Mathlib.Probability.Distributions.Binomial

/-!
# Fixed-set external-neighbour estimates in the binomial random graph

The basic probabilistic input is the exact probability that a prescribed
finite family of (non-diagonal) edges is absent.  Applied to all edges between
`S` and the complement of `S ∪ T`, this computes the probability that the
external neighbourhood of `S` is contained in `T`.
-/

open MeasureTheory ProbabilityTheory unitInterval
open scoped BigOperators ENNReal SimpleGraph Sym2

namespace Erdos746

noncomputable section

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The external neighbourhood used by the fixed-set probability calculation.
This is definitionally the same construction used in the deterministic Pósa
development, but this file is deliberately independent of that development. -/
def fixedOuterNeighborFinset (G : _root_.SimpleGraph V) (S : Finset V) : Finset V :=
  by
    classical
    exact (S.biUnion fun u ↦ Finset.univ.filter (G.Adj u)) \ S

@[simp] theorem mem_fixedOuterNeighborFinset {G : _root_.SimpleGraph V}
    {S : Finset V} {v : V} :
    v ∈ fixedOuterNeighborFinset G S ↔
      v ∉ S ∧ ∃ u ∈ S, G.Adj u v := by
  simp [fixedOuterNeighborFinset, _root_.SimpleGraph.adj_comm, and_comm]

theorem fixedOuterNeighborFinset_subset_compl (G : _root_.SimpleGraph V)
    (S : Finset V) :
    fixedOuterNeighborFinset G S ⊆ Finset.univ \ S := by
  intro v hv
  rw [mem_fixedOuterNeighborFinset] at hv
  simp [hv.1]

/-- The independent probability-layer definition agrees definitionally with
the canonical Pósa external neighbourhood. -/
theorem fixedOuterNeighborFinset_eq_outerNeighborFinset
    (G : _root_.SimpleGraph V) (S : Finset V) :
    fixedOuterNeighborFinset G S = G.outerNeighborFinset S := by
  rfl

/-- All unordered pairs with one endpoint in `A` and the other in `B`. -/
def crossEdgeFinset (A B : Finset V) : Finset (Sym2 V) :=
  (A ×ˢ B).image fun x ↦ s(x.1, x.2)

@[simp] theorem mem_crossEdgeFinset {A B : Finset V} {e : Sym2 V} :
    e ∈ crossEdgeFinset A B ↔
      ∃ a ∈ A, ∃ b ∈ B, s(a, b) = e := by
  constructor
  · rw [crossEdgeFinset, Finset.mem_image]
    rintro ⟨⟨a, b⟩, hab, rfl⟩
    exact ⟨a, (Finset.mem_product.mp hab).1, b, (Finset.mem_product.mp hab).2, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    rw [crossEdgeFinset, Finset.mem_image]
    exact ⟨⟨a, b⟩, Finset.mem_product.mpr ⟨ha, hb⟩, rfl⟩

theorem crossEdgeFinset_subset_compl_diagSet {A B : Finset V}
    (hAB : Disjoint A B) :
    (↑(crossEdgeFinset A B) : Set (Sym2 V)) ⊆ Sym2.diagSetᶜ := by
  rintro e he hdiag
  change e ∈ crossEdgeFinset A B at he
  rw [mem_crossEdgeFinset] at he
  obtain ⟨a, ha, b, hb, rfl⟩ := he
  have hab : a ≠ b := by
    intro hab
    subst b
    exact Finset.disjoint_left.mp hAB ha hb
  exact hab (Sym2.mk_isDiag_iff.mp hdiag)

theorem card_crossEdgeFinset {A B : Finset V} (hAB : Disjoint A B) :
    (crossEdgeFinset A B).card = A.card * B.card := by
  rw [crossEdgeFinset, Finset.card_image_iff.mpr]
  · exact Finset.card_product A B
  rintro ⟨a, b⟩ hab ⟨a', b'⟩ hab' he
  have hab := Finset.mem_product.mp hab
  have hab' := Finset.mem_product.mp hab'
  simp only [Sym2.eq_iff] at he
  rcases he with he | he
  · exact Prod.ext he.1 he.2
  · exfalso
    exact Finset.disjoint_left.mp hAB hab.1 (he.1.symm ▸ hab'.2)

end SimpleGraph

/-- The probability that a finite prescribed family of available Bernoulli
coordinates is entirely absent. -/
theorem setBernoulli_disjoint_finset {ι : Type*} [Finite ι]
    (u : Set ι) (p : I) (t : Finset ι) (ht : (↑t : Set ι) ⊆ u) :
    setBer(u, p) {s : Set ι | Disjoint (↑t : Set ι) s} =
      toNNReal (σ p) ^ t.card := by
  classical
  let := Fintype.ofFinite ι
  rw [setBernoulli_apply', Measure.infinitePi_eq_pi]
  have hpre :
      ((fun q : ι → Prop ↦ {i | q i}) ⁻¹' {s : Set ι |
        Disjoint (↑t : Set ι) s}) =
        ((↑t : Set ι).pi fun _ ↦ ({False} : Set Prop)) := by
    ext q
    simp [Set.disjoint_left]
  rw [hpre, Measure.pi_pi_finset, Finset.prod_eq_pow_card]
  intro i hi
  have hiu : i ∈ u := ht hi
  simp only [hiu, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply,
    Set.mem_singleton_iff, Set.indicator_of_mem, Pi.one_apply]
  rw [Set.indicator_of_notMem]
  · simp
  · simp

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Exact `G(V,p)` probability that none of the prescribed non-loop edges is
present. -/
theorem binomialRandom_disjoint_edgeFinset (p : I) (t : Finset (Sym2 V))
    (ht : (↑t : Set (Sym2 V)) ⊆ Sym2.diagSetᶜ) :
    G(V, p) {G | Disjoint (↑t : Set (Sym2 V)) G.edgeSet} =
      toNNReal (σ p) ^ t.card := by
  rw [_root_.SimpleGraph.binomialRandom_apply', setBernoulli_apply_eq_apply_subsets]
  have himage :
      {s ∈ (fun G : _root_.SimpleGraph V ↦ G.edgeSet) '' {G : _root_.SimpleGraph V |
          Disjoint (↑t : Set (Sym2 V)) G.edgeSet} | s ⊆ Sym2.diagSetᶜ} =
        {s ∈ {s : Set (Sym2 V) | Disjoint (↑t : Set (Sym2 V)) s} |
          s ⊆ Sym2.diagSetᶜ} := by
    ext s
    constructor
    · rintro ⟨⟨G, hG, rfl⟩, hs⟩
      exact ⟨hG, hs⟩
    · rintro ⟨hdis, hs⟩
      have hsdiag : Disjoint s Sym2.diagSet :=
        Set.disjoint_left.mpr fun e he hes ↦ hs he hes
      have hedge : (_root_.SimpleGraph.fromEdgeSet s).edgeSet = s := by
        rw [_root_.SimpleGraph.edgeSet_fromEdgeSet, sdiff_eq_left.mpr hsdiag]
      change Disjoint (↑t : Set (Sym2 V)) s at hdis
      exact ⟨⟨_root_.SimpleGraph.fromEdgeSet s, by simpa [hedge] using hdis, hedge⟩, hs⟩
  rw [himage, ← setBernoulli_apply_eq_apply_subsets]
  exact Erdos746.setBernoulli_disjoint_finset _ _ _ ht

/-- Real-valued form of `binomialRandom_disjoint_edgeFinset`. -/
theorem binomialRandom_real_disjoint_edgeFinset (p : I) (t : Finset (Sym2 V))
    (ht : (↑t : Set (Sym2 V)) ⊆ Sym2.diagSetᶜ) :
    G(V, p).real {G | Disjoint (↑t : Set (Sym2 V)) G.edgeSet} =
      (1 - (p : ℝ)) ^ t.card := by
  rw [MeasureTheory.measureReal_def, binomialRandom_disjoint_edgeFinset p t ht,
    ENNReal.toReal_pow]
  simp

/-- Containment of the external neighbourhood is exactly the absence of all
edges from `S` to the complement of `S ∪ T`. -/
theorem fixedOuterNeighborFinset_subset_iff_disjoint_crossEdges
    (G : _root_.SimpleGraph V) (S T : Finset V) :
    fixedOuterNeighborFinset G S ⊆ T ↔
      Disjoint
        (↑(crossEdgeFinset S (Finset.univ \ (S ∪ T))) : Set (Sym2 V))
        G.edgeSet := by
  constructor
  · intro hN
    rw [Set.disjoint_left]
    intro e heCross heG
    change e ∈ crossEdgeFinset S (Finset.univ \ (S ∪ T)) at heCross
    rw [mem_crossEdgeFinset] at heCross
    obtain ⟨u, hu, v, hv, rfl⟩ := heCross
    have hvN : v ∈ fixedOuterNeighborFinset G S := by
      rw [mem_fixedOuterNeighborFinset]
      refine ⟨?_, u, hu, heG⟩
      intro hvS
      exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_union_left T hvS)
    have hvT := hN hvN
    exact (by simpa using hv : v ∉ S ∪ T) (Finset.mem_union_right S hvT)
  · intro hdis v hvN
    rw [Set.disjoint_left] at hdis
    by_contra hvT
    rw [mem_fixedOuterNeighborFinset] at hvN
    have hvB : v ∈ Finset.univ \ (S ∪ T) := by
      simp [hvN.1, hvT]
    exact hdis
      (show s(hvN.2.choose, v) ∈
          (↑(crossEdgeFinset S (Finset.univ \ (S ∪ T))) : Set (Sym2 V)) by
        change s(hvN.2.choose, v) ∈ crossEdgeFinset S (Finset.univ \ (S ∪ T))
        rw [mem_crossEdgeFinset]
        exact ⟨hvN.2.choose, hvN.2.choose_spec.1, v, hvB, rfl⟩)
      hvN.2.choose_spec.2

/-- Exact fixed-set containment probability.  No disjointness hypothesis on
`S` and `T` is needed because the complement removes both. -/
theorem binomialRandom_real_fixedOuterNeighborFinset_subset
    (p : I) (S T : Finset V) :
    G(V, p).real {G | fixedOuterNeighborFinset G S ⊆ T} =
      (1 - (p : ℝ)) ^
        (S.card * (Finset.univ \ (S ∪ T)).card) := by
  let B := Finset.univ \ (S ∪ T)
  have hSB : Disjoint S B := by
    refine Finset.disjoint_left.mpr ?_
    intro v hvS hvB
    exact (by simpa [B, hvS] using hvB)
  have hevent :
      {G : _root_.SimpleGraph V | fixedOuterNeighborFinset G S ⊆ T} =
        {G | Disjoint (↑(crossEdgeFinset S B) : Set (Sym2 V)) G.edgeSet} := by
    ext G
    exact fixedOuterNeighborFinset_subset_iff_disjoint_crossEdges G S T
  rw [hevent,
    binomialRandom_real_disjoint_edgeFinset p (crossEdgeFinset S B)
      (crossEdgeFinset_subset_compl_diagSet hSB),
    card_crossEdgeFinset hSB]

/-- The finite collection of possible external-neighbour sets having cardinal
strictly less than `r`. -/
def smallNeighborCandidateFinset (S : Finset V) (r : ℕ) : Finset (Finset V) :=
  ((Finset.univ \ S).powerset).filter fun T ↦ T.card < r

@[simp] theorem mem_smallNeighborCandidateFinset {S T : Finset V} {r : ℕ} :
    T ∈ smallNeighborCandidateFinset S r ↔
      T ⊆ Finset.univ \ S ∧ T.card < r := by
  simp [smallNeighborCandidateFinset]

/-- A fixed-set union bound for an undersized external neighbourhood.  This is
the form used in the expansion calculation: each summand is an exact
probability, indexed by the possible external-neighbour set `T`. -/
theorem binomialRandom_real_fixedOuterNeighborFinset_card_lt_le
    (p : I) (S : Finset V) (r : ℕ) :
    G(V, p).real {G | (fixedOuterNeighborFinset G S).card < r} ≤
      ∑ T ∈ smallNeighborCandidateFinset S r,
        (1 - (p : ℝ)) ^
          (S.card * (Finset.univ \ (S ∪ T)).card) := by
  let C := smallNeighborCandidateFinset S r
  let E : Finset V → Set (_root_.SimpleGraph V) :=
    fun T ↦ {G | fixedOuterNeighborFinset G S ⊆ T}
  have hsubset :
      {G : _root_.SimpleGraph V | (fixedOuterNeighborFinset G S).card < r} ⊆
        ⋃ T ∈ C, E T := by
    intro G hG
    let N := fixedOuterNeighborFinset G S
    have hNC : N ∈ C := by
      rw [show C = smallNeighborCandidateFinset S r by rfl,
        mem_smallNeighborCandidateFinset]
      exact ⟨fixedOuterNeighborFinset_subset_compl G S, hG⟩
    exact Set.mem_iUnion_of_mem N
      (Set.mem_iUnion_of_mem hNC (show fixedOuterNeighborFinset G S ⊆ N from by rfl))
  calc
    G(V, p).real {G | (fixedOuterNeighborFinset G S).card < r}
        ≤ G(V, p).real (⋃ T ∈ C, E T) :=
      measureReal_mono hsubset (MeasureTheory.measure_ne_top G(V, p) _)
    _ ≤ ∑ T ∈ C, G(V, p).real (E T) :=
      measureReal_biUnion_finset_le C E
    _ = ∑ T ∈ smallNeighborCandidateFinset S r,
          (1 - (p : ℝ)) ^
            (S.card * (Finset.univ \ (S ∪ T)).card) := by
      rw [show C = smallNeighborCandidateFinset S r by rfl]
      apply Finset.sum_congr rfl
      intro T hT
      exact binomialRandom_real_fixedOuterNeighborFinset_subset p S T

/-- The expansion-failure specialization: fewer than twice as many external
neighbours as vertices in `S`. -/
theorem binomialRandom_real_fixedOuterNeighborFinset_card_lt_two_mul_le
    (p : I) (S : Finset V) :
    G(V, p).real
        {G | (fixedOuterNeighborFinset G S).card < 2 * S.card} ≤
      ∑ T ∈ smallNeighborCandidateFinset S (2 * S.card),
        (1 - (p : ℝ)) ^
          (S.card * (Finset.univ \ (S ∪ T)).card) := by
  exact binomialRandom_real_fixedOuterNeighborFinset_card_lt_le p S (2 * S.card)

/-- Exact containment probability for the canonical external neighbourhood. -/
theorem binomialRandom_real_outerNeighborFinset_subset
    (p : I) (S T : Finset V) :
    G(V, p).real {G | G.outerNeighborFinset S ⊆ T} =
      (1 - (p : ℝ)) ^
        (S.card * (Finset.univ \ (S ∪ T)).card) := by
  simpa only [← fixedOuterNeighborFinset_eq_outerNeighborFinset] using
    binomialRandom_real_fixedOuterNeighborFinset_subset p S T

/-- General lower-tail union bound for the canonical external neighbourhood. -/
theorem binomialRandom_real_outerNeighborFinset_card_lt_le
    (p : I) (S : Finset V) (r : ℕ) :
    G(V, p).real {G | (G.outerNeighborFinset S).card < r} ≤
      ∑ T ∈ smallNeighborCandidateFinset S r,
        (1 - (p : ℝ)) ^
          (S.card * (Finset.univ \ (S ∪ T)).card) := by
  simpa only [← fixedOuterNeighborFinset_eq_outerNeighborFinset] using
    binomialRandom_real_fixedOuterNeighborFinset_card_lt_le p S r

/-- Fixed-set undersized-neighbourhood bound for the canonical Pósa
definition. -/
theorem binomialRandom_real_outerNeighborFinset_card_lt_two_mul_le
    (p : I) (S : Finset V) :
    G(V, p).real {G | (G.outerNeighborFinset S).card < 2 * S.card} ≤
      ∑ T ∈ smallNeighborCandidateFinset S (2 * S.card),
        (1 - (p : ℝ)) ^
          (S.card * (Finset.univ \ (S ∪ T)).card) := by
  exact binomialRandom_real_outerNeighborFinset_card_lt_le p S (2 * S.card)

end SimpleGraph

end

end Erdos746
