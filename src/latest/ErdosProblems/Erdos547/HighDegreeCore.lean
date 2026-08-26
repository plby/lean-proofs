import ErdosProblems.Erdos547.DegreeExtraction

/-!
# A core whose vertices have large global colour degree

Partition the vertices according to which colour has degree at least half the
ambient order. The two corresponding internal degree masses have sum at least
the square of half the order. Peeling one of these two sets produces a nonempty
core while retaining the global degree condition needed for restoring leaves.
-/

namespace Erdos547

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]

theorem degreeIn_cast_eq_sum (S : Finset V) (v : V) :
    (degreeIn G S v : ℝ) = ∑ w ∈ S, if G.Adj v w then (1 : ℝ) else 0 := by
  rw [Finset.sum_boole]
  rfl

theorem sum_degreeIn_swap (S Q : Finset V) :
    (∑ v ∈ S, (degreeIn G Q v : ℝ)) = ∑ w ∈ Q, (degreeIn G S w : ℝ) := by
  simp_rw [degreeIn_cast_eq_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  apply Finset.sum_congr rfl
  intro v _
  simp only [G.adj_comm]

theorem degreeIn_union [DecidableEq V] {S Q : Finset V} (hdis : Disjoint S Q) (v : V) :
    degreeIn G (S ∪ Q) v = degreeIn G S v + degreeIn G Q v := by
  unfold degreeIn
  rw [Finset.filter_union]
  exact Finset.card_union_of_disjoint
    (hdis.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))

/-- Across disjoint sets, the two colours together account for every pair
exactly once. -/
theorem cross_degreeIn_add_compl [DecidableRel Gᶜ.Adj] {S Q : Finset V}
    (hdis : Disjoint S Q) :
    (∑ v ∈ S, (degreeIn G Q v : ℝ)) +
      (∑ w ∈ Q, (degreeIn Gᶜ S w : ℝ)) = (S.card : ℝ) * Q.card := by
  rw [sum_degreeIn_swap Gᶜ Q S, ← Finset.sum_add_distrib]
  calc
    _ = ∑ v ∈ S, (Q.card : ℝ) := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [degreeIn_cast_eq_sum, degreeIn_cast_eq_sum, ← Finset.sum_add_distrib]
      calc
        _ = ∑ _w ∈ Q, (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro w hw
          have hvw : v ≠ w := by
            intro heq
            exact Finset.disjoint_left.mp hdis hv (heq.symm ▸ hw)
          by_cases hadj : G.Adj v w <;> simp [SimpleGraph.compl_adj, hvw, hadj]
        _ = _ := by simp
    _ = _ := by simp

/-- The sum of the red degrees on one side and the blue degrees on the other
is exactly the two internal degree masses plus the number of cross pairs. -/
theorem partition_global_degree_sum [Fintype V] [DecidableRel Gᶜ.Adj]
    [DecidableEq V] {S Q : Finset V} (hdis : Disjoint S Q)
    (hcover : S ∪ Q = Finset.univ) :
    (∑ v ∈ S, (G.degree v : ℝ)) + (∑ w ∈ Q, (Gᶜ.degree w : ℝ)) =
      degreeMass G S + degreeMass Gᶜ Q + (S.card : ℝ) * Q.card := by
  have hsplit (H : SimpleGraph V) [DecidableRel H.Adj] (v : V) :
      (H.degree v : ℝ) = degreeIn H S v + degreeIn H Q v := by
    rw [← degreeIn_univ, ← hcover, degreeIn_union H hdis]
    push_cast
    rfl
  simp_rw [hsplit, Finset.sum_add_distrib]
  have hcross := cross_degreeIn_add_compl G hdis
  dsimp [degreeMass]
  linarith only [hcross]

/-- A positive degree excess cannot be completely removed by peeling. -/
theorem exists_core_of_positive_excess (S₀ : Finset V) (d : ℝ)
    (hpositive : 2 * d * S₀.card < degreeMass G S₀) :
    ∃ S ⊆ S₀, S.Nonempty ∧ ∀ v ∈ S, d < (degreeIn G S v : ℝ) := by
  obtain ⟨S, hsub, hpos, _, hmin⟩ := exists_peeling_core G S₀ 0 (Nat.zero_le _) d (by
    intro S _ hS
    have heq : S = ∅ := Finset.card_eq_zero.mp hS
    subst S
    simpa [degreeExcess, degreeMass] using sub_pos.mpr hpositive)
  exact ⟨S, hsub, Finset.card_pos.mp hpos, hmin⟩

open scoped Classical in
/-- Every colouring of `K_(2*m)` has a nonempty core of one colour with
minimum degree greater than `m/5`, all of whose vertices have global degree
at least `m` in that same colour. -/
theorem exists_high_degree_colour_core {m : ℕ} (hm : 0 < m)
    (R : SimpleGraph (Fin (2 * m))) :
    (∃ Q : Finset (Fin (2 * m)), Q.Nonempty ∧
      (∀ v ∈ Q, m ≤ R.degree v) ∧
      ∀ v ∈ Q, (m : ℝ) / 5 < (degreeIn R Q v : ℝ)) ∨
    (∃ Q : Finset (Fin (2 * m)), Q.Nonempty ∧
      (∀ v ∈ Q, m ≤ Rᶜ.degree v) ∧
      ∀ v ∈ Q, (m : ℝ) / 5 < (degreeIn Rᶜ Q v : ℝ)) := by
  classical
  let S := Finset.univ.filter fun v ↦ m ≤ R.degree v
  let Q := Finset.univ \ S
  have hdis : Disjoint S Q := by
    apply Finset.disjoint_left.mpr
    intro v hv hvQ
    exact (Finset.mem_sdiff.mp hvQ).2 hv
  have hcover : S ∪ Q = Finset.univ := Finset.union_sdiff_of_subset (Finset.subset_univ _)
  have hS (v) (hv : v ∈ S) : m ≤ R.degree v := (Finset.mem_filter.mp hv).2
  have hQ (v) (hv : v ∈ Q) : m ≤ Rᶜ.degree v := by
    have hvS : v ∉ S := (Finset.mem_sdiff.mp hv).2
    have hred : ¬ m ≤ R.degree v := by simpa [S] using hvS
    have hsum := degree_add_compl R v
    simp only [Fintype.card_fin] at hsum
    omega
  have hsum := partition_global_degree_sum R hdis hcover
  have hSsum : (m : ℝ) * S.card ≤ ∑ v ∈ S, (R.degree v : ℝ) := by
    calc
      _ = ∑ _v ∈ S, (m : ℝ) := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun v hv ↦ by exact_mod_cast hS v hv
  have hQsum : (m : ℝ) * Q.card ≤ ∑ v ∈ Q, (Rᶜ.degree v : ℝ) := by
    calc
      _ = ∑ _v ∈ Q, (m : ℝ) := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun v hv ↦ by exact_mod_cast hQ v hv
  have hcard : (S.card : ℝ) + Q.card = 2 * m := by
    have hc := Finset.card_union_of_disjoint hdis
    rw [hcover, Finset.card_univ, Fintype.card_fin] at hc
    exact_mod_cast hc.symm
  have hprod : (S.card : ℝ) * Q.card ≤ (m : ℝ) ^ 2 := by
    nlinarith only [sq_nonneg ((S.card : ℝ) - Q.card), hcard]
  have hmass : (m : ℝ) ^ 2 ≤ degreeMass R S + degreeMass Rᶜ Q := by
    nlinarith only [hsum, hSsum, hQsum, hcard, hprod]
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hchoice : 2 * ((m : ℝ) / 5) * S.card < degreeMass R S ∨
      2 * ((m : ℝ) / 5) * Q.card < degreeMass Rᶜ Q := by
    by_contra h
    push Not at h
    nlinarith [sq_pos_of_pos hmpos]
  rcases hchoice with hred | hblue
  · obtain ⟨A, hAS, hA, hdeg⟩ := exists_core_of_positive_excess R S ((m : ℝ) / 5) hred
    exact Or.inl ⟨A, hA, fun v hv ↦ hS v (hAS hv), hdeg⟩
  · obtain ⟨A, hAQ, hA, hdeg⟩ := exists_core_of_positive_excess Rᶜ Q ((m : ℝ) / 5) hblue
    exact Or.inr ⟨A, hA, fun v hv ↦ hQ v (hAQ hv), hdeg⟩

end Erdos547

#print axioms Erdos547.exists_high_degree_colour_core
