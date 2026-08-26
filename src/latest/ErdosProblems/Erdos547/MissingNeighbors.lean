import ErdosProblems.Erdos547.HighDegreeCore

/-!
# Counting missing adjacencies, including diagonal pairs

Unlike complementary graph degree, these counts include a vertex itself when
it belongs to the target set. Thus they can be used for overlapping dense pairs.
-/

namespace Erdos547

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]

def missingIn (S : Finset V) (v : V) : ℕ := (S.filter fun w ↦ ¬ G.Adj v w).card

theorem degreeIn_add_missingIn (S : Finset V) (v : V) :
    degreeIn G S v + missingIn G S v = S.card :=
  Finset.card_filter_add_card_filter_not (s := S) (G.Adj v)

theorem missingIn_cast_eq_sum (S : Finset V) (v : V) :
    (missingIn G S v : ℝ) = ∑ w ∈ S, if G.Adj v w then (0 : ℝ) else 1 := by
  have h := Finset.sum_boole (s := S) (p := fun w ↦ ¬ G.Adj v w) (R := ℝ)
  simpa only [missingIn, ite_not] using h.symm

theorem sum_missingIn_swap (A B : Finset V) :
    (∑ a ∈ A, (missingIn G B a : ℝ)) = ∑ b ∈ B, (missingIn G A b : ℝ) := by
  simp_rw [missingIn_cast_eq_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  simp only [G.adj_comm]

open scoped Classical in
/-- Delete at most `t` vertices from the second side of a dense pair so that
every retained vertex misses at most `t` vertices on the first side. -/
theorem prune_dense_pair (A B : Finset V) (d t : ℕ)
    (hmissing : ∀ a ∈ A, missingIn G B a ≤ d) (hbudget : A.card * d ≤ t ^ 2) :
    ∃ Q ⊆ B, B.card ≤ Q.card + t ∧
      (∀ b ∈ Q, missingIn G A b ≤ t) ∧
      ∀ a, degreeIn G B a ≤ degreeIn G Q a + t := by
  classical
  let Z := B.filter fun b ↦ t < missingIn G A b
  have hZB : Z ⊆ B := Finset.filter_subset _ _
  have hmass : (∑ b ∈ B, (missingIn G A b : ℝ)) ≤ (A.card : ℝ) * d := by
    rw [sum_missingIn_swap G B A]
    calc
      _ ≤ ∑ _a ∈ A, (d : ℝ) := by
        apply Finset.sum_le_sum
        intro a ha
        exact_mod_cast hmissing a ha
      _ = _ := by simp
  have hZmass : ((t : ℝ) + 1) * Z.card ≤ ∑ b ∈ B, (missingIn G A b : ℝ) := by
    calc
      _ = ∑ _b ∈ Z, ((t : ℝ) + 1) := by simp [mul_comm]; ring
      _ ≤ ∑ b ∈ Z, (missingIn G A b : ℝ) := by
        apply Finset.sum_le_sum
        intro b hb
        have h := (Finset.mem_filter.mp hb).2
        exact_mod_cast (show t + 1 ≤ missingIn G A b from h)
      _ ≤ _ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hZB
        intro b _ _
        positivity
  have hZcard : Z.card ≤ t := by
    have hb : (A.card : ℝ) * d ≤ (t : ℝ) ^ 2 := by exact_mod_cast hbudget
    have hreal : (Z.card : ℝ) ≤ t := by
      by_contra h
      have hn : t + 1 ≤ Z.card := by
        have hlt : t < Z.card := by exact_mod_cast lt_of_not_ge h
        omega
      have hn' : (t : ℝ) + 1 ≤ Z.card := by exact_mod_cast hn
      nlinarith only [hZmass, hmass, hb, hn', (Nat.cast_nonneg t : (0 : ℝ) ≤ t)]
    exact_mod_cast hreal
  let Q := B \ Z
  have hQB : Q ⊆ B := Finset.sdiff_subset
  have hremoved : B \ Q = Z := Finset.sdiff_sdiff_eq_self hZB
  refine ⟨Q, hQB, ?_, ?_, ?_⟩
  · have hcard := Finset.card_sdiff_add_card_inter B Z
    rw [Finset.inter_eq_right.mpr hZB] at hcard
    change Q.card + Z.card = B.card at hcard
    omega
  · intro b hb
    obtain ⟨hbB, hbZ⟩ := Finset.mem_sdiff.mp hb
    by_contra h
    exact hbZ (Finset.mem_filter.mpr ⟨hbB, by omega⟩)
  · intro a
    have h := degreeIn_le_add_removed G B Q a
    rw [hremoved] at h
    omega

open scoped Classical in
/-- Split the whole neighbourhood into its part in `B` and its part outside
`B`, with no disjointness or self-membership restriction on `B`. -/
theorem degreeIn_add_outside [Fintype V] [DecidableEq V] (B : Finset V) (v : V) :
    degreeIn G B v + (G.neighborFinset v \ B).card = G.degree v := by
  classical
  have heq : B.filter (G.Adj v) = G.neighborFinset v ∩ B := by
    ext w
    simp [and_comm]
  have h := Finset.card_sdiff_add_card_inter (G.neighborFinset v) B
  rw [← heq, G.card_neighborFinset_eq_degree] at h
  change (G.neighborFinset v \ B).card + degreeIn G B v = G.degree v at h
  omega

open scoped Classical in
/-- Two neighbourhood counts can overlap only on the intersection of the two
target sets. -/
theorem degreeIn_add_le_degree_add_inter [Fintype V] [DecidableEq V] (A B : Finset V) (v : V) :
    degreeIn G A v + degreeIn G B v ≤ G.degree v + (A ∩ B).card := by
  classical
  have hsplit : degreeIn G (A ∪ B) v + degreeIn G (A ∩ B) v =
      degreeIn G A v + degreeIn G B v := by
    unfold degreeIn
    rw [Finset.filter_union, Finset.filter_inter_distrib]
    exact Finset.card_union_add_card_inter _ _
  have hu := degreeIn_mono G (Finset.subset_univ (A ∪ B)) v
  rw [degreeIn_univ] at hu
  have hi := degreeIn_le_card G (A ∩ B) v
  omega

open scoped Classical in
/-- If two dense sides overlap and a vertex of their intersection has a
controlled global degree, the intersection itself has high minimum degree. -/
theorem dense_intersection_core [Fintype V] [DecidableEq V] (A B : Finset V) (m D k : ℕ)
    (hA : A.card ≤ m) (hI : (A ∩ B).Nonempty)
    (hAB : ∀ a ∈ A, m ≤ degreeIn G B a + D)
    (hBA : ∀ b ∈ B, m ≤ degreeIn G A b + D)
    (hcap : ∀ a ∈ A, G.degree a ≤ m + k) :
    ∀ v ∈ A ∩ B, m ≤ degreeIn G (A ∩ B) v + 3 * D + k := by
  classical
  have hIlower : m ≤ (A ∩ B).card + 2 * D + k := by
    obtain ⟨z, hz⟩ := hI
    obtain ⟨hzA, hzB⟩ := Finset.mem_inter.mp hz
    have h₁ := hAB z hzA
    have h₂ := hBA z hzB
    have h₃ := degreeIn_add_le_degree_add_inter G A B z
    have h₄ := hcap z hzA
    omega
  intro v hv
  have hvB : v ∈ B := (Finset.mem_inter.mp hv).2
  have hdeg := hBA v hvB
  have hdrop := degreeIn_le_add_removed G A (A ∩ B) v
  have hcard := Finset.card_sdiff_add_card_inter A (A ∩ B)
  rw [Finset.inter_eq_right.mpr Finset.inter_subset_left] at hcard
  omega

end Erdos547

#print axioms Erdos547.prune_dense_pair
#print axioms Erdos547.dense_intersection_core
