import ErdosProblems.Erdos814.Basic
import ErdosProblems.Erdos814.Arithmetic
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

/-!
# Erdős 814: the elementary core threshold

This file records the standard degeneracy argument used at the beginning of the
Sauermann proof.  If no nonempty induced subgraph has minimum degree at least
`k`, repeatedly deleting a vertex of degree at most `k - 1` gives the usual
sharp edge bound for a `(k - 1)`-degenerate graph.

All statements use the fixed-ambient `Finset` API from `Basic.lean`.  The signed
version at the end is the form used by the outer induction: integer subtraction
is essential because the shortage in Problem 814 is negative when `k = 2`.
-/

open Finset SimpleGraph

namespace Erdos814

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The extremal number of edges in a `(k - 1)`-degenerate graph on `n`
vertices, in a subtraction-free form valid when `k - 1 ≤ n`. -/
def coreFreeEdgeBound (k n : ℕ) : ℕ :=
  (k - 1).choose 2 + (k - 1) * (n - (k - 1))

/-- Removing `v` after inducing on `A` is isomorphic to inducing after removing
the corresponding vertex of the first induced graph. -/
private def induceEraseIso (A : Finset V) {v : V} (hv : v ∈ A) :
    G.induce (A.erase v : Set V) ≃g
      (G.induce (A : Set V)).induce ({(⟨v, hv⟩ : (A : Set V))}ᶜ) where
  toFun x := ⟨⟨x.1, Finset.mem_of_mem_erase x.2⟩, by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, Subtype.ext_iff,
      ne_eq] using (Finset.ne_of_mem_erase x.2)⟩
  invFun x := ⟨x.1.1, Finset.mem_erase.mpr ⟨by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, Subtype.ext_iff,
      ne_eq] using x.2, x.1.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := by simp

/-- Exact edge bookkeeping when one vertex is erased. -/
lemma edgeCount_erase_add_degreeOn {A : Finset V} {v : V} (hv : v ∈ A) :
    edgeCount G (A.erase v) + degreeOn G A v = edgeCount G A := by
  have herase :
      #((G.induce (A.erase v : Set V)).edgeFinset) =
        #((G.induce (A : Set V)).edgeFinset) -
          (G.induce (A : Set V)).degree ⟨v, hv⟩ := by
    rw [(induceEraseIso G A hv).card_edgeFinset_eq]
    rw [(G.induce (A : Set V)).card_edgeFinset_induce_compl_singleton ⟨v, hv⟩]
    exact (G.induce (A : Set V)).card_edgeFinset_deleteIncidenceSet ⟨v, hv⟩
  have hdeg :
      (G.induce (A : Set V)).degree ⟨v, hv⟩ ≤
        #((G.induce (A : Set V)).edgeFinset) :=
    (G.induce (A : Set V)).degree_le_card_edgeFinset ⟨v, hv⟩
  simp only [edgeCount_eq_card_edgeFinset_induce,
    degreeOn_eq_degree_induce G hv]
  rw [herase, Nat.sub_add_cancel hdeg]

/-- A core-free nonempty set contains a vertex of restricted degree below `k`. -/
lemma exists_degreeOn_lt_of_no_core {A : Finset V} (hA : A.Nonempty)
    (hno : ∀ U ⊆ A, ¬ HasMinDegreeOn G U k) :
    ∃ v ∈ A, degreeOn G A v < k := by
  have hnot := hno A Subset.rfl
  rw [HasMinDegreeOn, not_and_or] at hnot
  rcases hnot with hfalse | hdeg
  · exact (hfalse hA).elim
  · push_neg at hdeg
    exact hdeg

/-- The sharp natural-number edge bound for a graph with no induced `k`-core.

The lower bound on `|A|` is exactly what makes the subtraction-free expression
`coreFreeEdgeBound` agree with `(k-1)|A| - binom(k,2)`. -/
theorem edgeCount_le_coreFreeEdgeBound_of_no_core (k : ℕ) {A : Finset V}
    (hcard : k - 1 ≤ A.card)
    (hno : ∀ U ⊆ A, ¬ HasMinDegreeOn G U k) :
    edgeCount G A ≤ coreFreeEdgeBound k A.card := by
  revert hcard hno
  refine Finset.strongInductionOn A ?_
  intro A ih hcard hno
  by_cases hbase : A.card = k - 1
  · have hedge : edgeCount G A ≤ A.card.choose 2 := by
      rw [edgeCount_eq_card_edgeFinset_induce]
      simpa using (G.induce (A : Set V)).card_edgeFinset_le_card_choose_two
    simpa [coreFreeEdgeBound, hbase] using hedge
  · have hpos : 0 < A.card := by omega
    obtain ⟨v, hvA, hvdeg⟩ :=
      exists_degreeOn_lt_of_no_core (G := G) (k := k) (card_pos.mp hpos) hno
    have herasecard : (A.erase v).card = A.card - 1 := card_erase_of_mem hvA
    have heraselower : k - 1 ≤ (A.erase v).card := by omega
    have herasesub : A.erase v ⊂ A := erase_ssubset hvA
    have heraseno : ∀ U ⊆ A.erase v, ¬ HasMinDegreeOn G U k := by
      intro U hU
      exact hno U (hU.trans herasesub.subset)
    have hih := ih (A.erase v) herasesub heraselower heraseno
    have hvdeg' : degreeOn G A v ≤ k - 1 := by omega
    have hsubstep :
        (A.erase v).card - (k - 1) + 1 = A.card - (k - 1) := by
      omega
    rw [← edgeCount_erase_add_degreeOn G hvA]
    calc
      edgeCount G (A.erase v) + degreeOn G A v ≤
          coreFreeEdgeBound k (A.erase v).card + (k - 1) :=
        Nat.add_le_add hih hvdeg'
      _ = coreFreeEdgeBound k A.card := by
        simp only [coreFreeEdgeBound]
        rw [← hsubstep]
        simp only [Nat.mul_add, Nat.mul_one]
        omega

/-- The extremal bound in the usual signed form. -/
lemma coreFreeEdgeBound_cast_eq (k n : ℕ) (hk : 2 ≤ k) (hn : k - 1 ≤ n) :
    (coreFreeEdgeBound k n : ℤ) =
      (((k - 1) * n : ℕ) : ℤ) - (k.choose 2 : ℤ) := by
  have hkpred : k - 1 = (k - 2) + 1 := by omega
  have hksucc : k = (k - 1) + 1 := by omega
  have hnsub : n = (k - 1) + (n - (k - 1)) := by omega
  have hchoose : k.choose 2 = (k - 1) + (k - 1).choose 2 := by
    conv_lhs => rw [hksucc]
    rw [Nat.choose_succ_succ']
    simp
  simp only [coreFreeEdgeBound, Nat.cast_add, Nat.cast_mul]
  rw [Nat.cast_sub hn, hchoose]
  push_cast
  have hnsubZ : (n : ℤ) = (k - 1 : ℕ) + (n - (k - 1) : ℕ) := by
    exact_mod_cast hnsub
  rw [hnsubZ]
  have hchooseSquare : ∀ p : ℕ,
      (2 : ℤ) * (p.choose 2 : ℤ) + (p : ℤ) = (p : ℤ) ^ 2 := by
    intro p
    induction p with
    | zero => norm_num
    | succ p ih =>
        rw [show 2 = 1 + 1 by norm_num, Nat.choose_succ_succ']
        simp only [Nat.choose_one_right, Nat.cast_add, Nat.cast_succ]
        push_cast
        calc
          (2 : ℤ) * ((p : ℤ) + (p.choose 2 : ℤ)) + ((p : ℤ) + 1) =
              ((2 : ℤ) * (p.choose 2 : ℤ) + (p : ℤ)) + 2 * p + 1 := by ring
          _ = (p : ℤ) ^ 2 + 2 * p + 1 := by rw [ih]
          _ = ((p : ℤ) + 1) ^ 2 := by ring
  have hsq := hchooseSquare (k - 1)
  linear_combination hsq

/-- Signed no-core edge upper bound.  This statement contains no truncated
subtraction and is consequently the convenient form for shortage arithmetic. -/
theorem edgeCount_cast_le_of_no_core (k : ℕ) {A : Finset V}
    (hk : 2 ≤ k) (hcard : k - 1 ≤ A.card)
    (hno : ∀ U ⊆ A, ¬ HasMinDegreeOn G U k) :
    (edgeCount G A : ℤ) ≤
      (((k - 1) * A.card : ℕ) : ℤ) - (k.choose 2 : ℤ) := by
  rw [← coreFreeEdgeBound_cast_eq k A.card hk hcard]
  exact_mod_cast edgeCount_le_coreFreeEdgeBound_of_no_core G k hcard hno

/-- The exact Erdős--Faudree--Rousseau--Schelp base threshold used in
Sauermann's Claim 2.5.  Notice that this is the expression in Problem 814
*before* its final `+ 1`; it is already one edge above the sharp core-free
degeneracy bound. -/
theorem exists_core_of_efrsThreshold_le (k : ℕ) {A : Finset V}
    (hk : 2 ≤ k) (hcard : k - 1 ≤ A.card)
    (hedge :
      (k - 1) * (A.card + 2 - k) + (k - 2).choose 2 ≤ edgeCount G A) :
    ∃ U ⊆ A, HasMinDegreeOn G U k := by
  by_contra h
  push_neg at h
  have hbound := edgeCount_le_coreFreeEdgeBound_of_no_core G k hcard h
  have hpred : k - 1 = (k - 2) + 1 := by omega
  have hcardstep : A.card + 2 - k = A.card - (k - 1) + 1 := by omega
  have hchoose : (k - 1).choose 2 = (k - 2) + (k - 2).choose 2 := by
    conv_lhs => rw [hpred]
    rw [Nat.choose_succ_succ']
    simp
  have hefrs :
      (k - 1) * (A.card + 2 - k) + (k - 2).choose 2 =
        coreFreeEdgeBound k A.card + 1 := by
    simp only [coreFreeEdgeBound]
    rw [hcardstep, hchoose]
    simp only [Nat.mul_add, Nat.mul_one]
    omega
  rw [hefrs] at hedge
  omega

/-- At the Problem 814 density there is a nonempty induced subgraph of minimum
degree at least `k`.  This is the elementary Erdős--Faudree--Rousseau--Schelp
threshold lemma used before the quantitative shrinking argument. -/
theorem exists_core_of_edgeThreshold_le (k : ℕ) {A : Finset V}
    (hk : 2 ≤ k) (hcard : k - 1 ≤ A.card)
    (hedge : edgeThreshold k A.card ≤ edgeCount G A) :
    ∃ U ⊆ A, HasMinDegreeOn G U k := by
  apply exists_core_of_efrsThreshold_le G k hk hcard
  have hbase :
      (k - 1) * (A.card + 2 - k) + (k - 2).choose 2 ≤
        edgeThreshold k A.card := by
    simp [edgeThreshold]
  exact hbase.trans hedge

/-- A nonempty set of minimum degree at least `k` has at least `k+1` vertices. -/
lemma card_ge_succ_of_hasMinDegreeOn {A : Finset V}
    (hcore : HasMinDegreeOn G A k) : k + 1 ≤ A.card := by
  obtain ⟨v, hv⟩ := hcore.1
  have hdeg := hcore.2 v hv
  have hlt := degreeOn_lt_card G hv
  omega

/-- Feasibility consequence needed by the outer induction: whenever the
Problem 814 edge hypothesis is satisfiable, the ambient set has at least
`k+1` vertices. -/
theorem card_ge_succ_of_edgeThreshold_le (k : ℕ) {A : Finset V}
    (hk : 2 ≤ k) (hcard : k - 1 ≤ A.card)
    (hedge : edgeThreshold k A.card ≤ edgeCount G A) :
    k + 1 ≤ A.card := by
  obtain ⟨U, hUA, hcore⟩ := exists_core_of_edgeThreshold_le G k hk hcard hedge
  exact (card_ge_succ_of_hasMinDegreeOn (G := G) (A := U) (k := k) hcore).trans
    (card_le_card hUA)

end Erdos814
