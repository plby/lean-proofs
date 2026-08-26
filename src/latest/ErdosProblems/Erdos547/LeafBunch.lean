import ErdosProblems.Erdos547.HighDegreeCore
import ErdosProblems.Erdos547.LeafExtension

/-!
# A large bunch of leaves in the near-core case

If every vertex of a red near-core has red degree below `m`, it has blue degree
at least `m`. Deleting a small exceptional set outside the core leaves a blue
host for the tree with a large leaf bunch removed. Its root can be placed in
the original core, after which the bunch is restored using its global degree.
-/

namespace Erdos547

open Finset SimpleGraph
open scoped SimpleGraph BigOperators

variable {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A vertex outside `A` has exactly one edge colour to every vertex of `A`. -/
theorem degreeIn_add_compl_of_not_mem [DecidableRel Gᶜ.Adj]
    (A : Finset V) {v : V} (hv : v ∉ A) :
    degreeIn G A v + degreeIn Gᶜ A v = A.card := by
  have hr : (degreeIn G A v : ℝ) + degreeIn Gᶜ A v = A.card := by
    rw [degreeIn_cast_eq_sum, degreeIn_cast_eq_sum, ← Finset.sum_add_distrib]
    calc
      _ = ∑ _w ∈ A, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro w hw
        have hvw : v ≠ w := by intro h; exact hv (h.symm ▸ hw)
        by_cases hadj : G.Adj v w <;> simp [SimpleGraph.compl_adj, hvw, hadj]
      _ = _ := by simp
  exact_mod_cast hr

open scoped Classical in
/-- A red near-core with no globally high red vertex supplies a blue core
large enough for every tree with at least a quarter of its leaves at one root.
The explicit constant is intentionally coarse. -/
theorem blue_core_of_no_global_red {m d : ℕ} (hm : 0 < m) (hd : 128 * d ≤ m)
    (R : SimpleGraph (Fin (2 * m))) (A : Finset (Fin (2 * m))) (hA : A.Nonempty)
    (hnear : ∀ v ∈ A, m ≤ degreeIn R A v + d)
    (hglobal : ∀ v ∈ A, R.degree v < m) :
    ∃ K : Finset (Fin (2 * m)), A ⊆ K ∧
      ∀ v ∈ K, 3 * (m : ℝ) / 4 ≤ (degreeIn Rᶜ K v : ℝ) := by
  classical
  let W := Finset.univ \ A
  have hdis : Disjoint A W := by
    apply Finset.disjoint_left.mpr
    intro v hv hvW
    exact (Finset.mem_sdiff.mp hvW).2 hv
  have hcover : A ∪ W = Finset.univ := Finset.union_sdiff_of_subset (Finset.subset_univ _)
  have hredout (v) (hv : v ∈ A) : degreeIn R W v ≤ d := by
    have hsplit := degreeIn_union R hdis v
    rw [hcover, degreeIn_univ] at hsplit
    have h₁ := hnear v hv
    have h₂ := hglobal v hv
    omega
  have hblue (v) (hv : v ∈ A) : m ≤ Rᶜ.degree v := by
    have hsum := degree_add_compl R v
    simp only [Fintype.card_fin] at hsum
    have h := hglobal v hv
    omega
  have hAsize : m + 1 ≤ A.card + d := by
    obtain ⟨v, hv⟩ := hA
    have h := hnear v hv
    have hcard := degreeIn_add_one_le_card R A hv
    omega
  have hAupper : A.card ≤ 2 * m := by simpa using Finset.card_le_univ A
  let B := W.filter fun v ↦ m ≤ 8 * degreeIn R A v
  have hBW : B ⊆ W := Finset.filter_subset _ _
  have hcross : (∑ v ∈ W, (degreeIn R A v : ℝ)) ≤ (d : ℝ) * A.card := by
    rw [sum_degreeIn_swap]
    calc
      _ ≤ ∑ _v ∈ A, (d : ℝ) := by
        apply Finset.sum_le_sum
        intro v hv
        exact_mod_cast hredout v hv
      _ = _ := by simp [mul_comm]
  have hBsum : (m : ℝ) * B.card ≤ 8 * ∑ v ∈ B, (degreeIn R A v : ℝ) := by
    calc
      _ = ∑ _v ∈ B, (m : ℝ) := by simp [mul_comm]
      _ ≤ ∑ v ∈ B, 8 * (degreeIn R A v : ℝ) := by
        apply Finset.sum_le_sum
        intro v hv
        exact_mod_cast (Finset.mem_filter.mp hv).2
      _ = _ := by rw [Finset.mul_sum]
  have hsumle : (∑ v ∈ B, (degreeIn R A v : ℝ)) ≤
      ∑ v ∈ W, (degreeIn R A v : ℝ) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hBW
    intro v _ _
    positivity
  have hBcard : B.card ≤ 16 * d := by
    have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
    have hAupper' : (A.card : ℝ) ≤ 2 * m := by exact_mod_cast hAupper
    have hprod := mul_le_mul_of_nonneg_left hAupper' (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
    have hmul : (m : ℝ) * B.card ≤ m * (16 * (d : ℝ)) := by
      nlinarith only [hBsum, hsumle, hcross, hprod]
    have hbound := le_of_mul_le_mul_left hmul hmpos
    exact_mod_cast hbound
  let K := Finset.univ \ B
  have hAK : A ⊆ K := by
    intro v hv
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hvB
    exact Finset.disjoint_left.mp hdis hv (hBW hvB)
  refine ⟨K, hAK, ?_⟩
  intro v hv
  by_cases hvA : v ∈ A
  · have hdrop := degreeIn_le_add_removed Rᶜ Finset.univ K v
    have hremoved : Finset.univ \ K = B :=
      Finset.sdiff_sdiff_eq_self (Finset.subset_univ B)
    rw [hremoved, degreeIn_univ] at hdrop
    have hglobalblue := hblue v hvA
    have hbound : m ≤ degreeIn Rᶜ K v + 16 * d := by omega
    have hbound' : (m : ℝ) ≤ degreeIn Rᶜ K v + 16 * d := by exact_mod_cast hbound
    have hd' : 128 * (d : ℝ) ≤ m := by exact_mod_cast hd
    linarith
  · have hvW : v ∈ W := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hvA⟩
    have hvB : v ∉ B := (Finset.mem_sdiff.mp hv).2
    have hsmall : 8 * degreeIn R A v < m := by
      have hn : ¬ m ≤ 8 * degreeIn R A v := by
        intro h
        exact hvB (Finset.mem_filter.mpr ⟨hvW, h⟩)
      omega
    have hcompl := degreeIn_add_compl_of_not_mem R A hvA
    have hmono := degreeIn_mono Rᶜ hAK v
    have hnat : 3 * m ≤ 4 * degreeIn Rᶜ K v := by omega
    have hreal : 3 * (m : ℝ) ≤ 4 * degreeIn Rᶜ K v := by exact_mod_cast hnat
    linarith

open scoped Classical in
/-- Deleting any collection of leaves attached to a retained root preserves
the tree property. -/
theorem isTree_induce_of_leaf_bunch {U : Type*} (T : SimpleGraph U) (hT : T.IsTree)
    (S : Set U) (r : S)
    (hp : ∀ x : (Sᶜ : Set U), ∀ y, T.Adj x.val y → y = r.val) :
    (T.induce S).IsTree := by
  let : Nonempty S := ⟨r⟩
  refine ⟨⟨hT.connected.preconnected.induce_of_degree_eq_one ?_⟩, hT.isAcyclic.induce _⟩
  intro v hv x hx y hy
  exact (hp ⟨v, hv⟩ x hx).trans (hp ⟨v, hv⟩ y hy).symm

open scoped Classical in
/-- The near-core Ramsey conclusion when at least a quarter of the tree's
edge count consists of leaves at one vertex. -/
theorem ramsey_of_near_core_of_leaf_bunch {m d : ℕ} (hm : 0 < m) (hd : 128 * d ≤ m)
    (T : SimpleGraph (Fin (m + 1))) (hT : T.IsTree)
    (S : Set (Fin (m + 1))) (r : S)
    (hp : ∀ x : (Sᶜ : Set (Fin (m + 1))), ∀ y, T.Adj x.val y → y = r.val)
    (hbunch : m ≤ 4 * Fintype.card (Sᶜ : Set (Fin (m + 1))))
    (R : SimpleGraph (Fin (2 * m))) (A : Finset (Fin (2 * m))) (hA : A.Nonempty)
    (hnear : ∀ v ∈ A, m ≤ degreeIn R A v + d) : T ⊑ R ∨ T ⊑ Rᶜ := by
  classical
  have hST := isTree_induce_of_leaf_bunch T hT S r hp
  have hcards := Fintype.card_compl_set S
  simp only [Fintype.card_fin] at hcards
  have hSpos : 0 < Fintype.card S := Fintype.card_pos_iff.mpr ⟨r⟩
  have hScard : Fintype.card S ≤ m + 1 := by
    simpa only [Fintype.card_fin] using Fintype.card_subtype_le (Membership.mem S)
  have hsmall : Fintype.card S - 1 + d ≤ m := by omega
  have hsmallReal : (Fintype.card S - 1 : ℕ) ≤ 3 * (m : ℝ) / 4 := by
    have hn : 4 * (Fintype.card S - 1) ≤ 3 * m := by omega
    have hr : 4 * ((Fintype.card S - 1 : ℕ) : ℝ) ≤ 3 * m := by exact_mod_cast hn
    linarith
  by_cases hhigh : ∃ z ∈ A, m ≤ R.degree z
  · obtain ⟨z, hz, hglobal⟩ := hhigh
    left
    let : Nonempty (A : Set (Fin (2 * m))) := ⟨⟨z, hz⟩⟩
    apply isContained_of_leaf_bunch S (A : Set (Fin (2 * m))) r ⟨z, hz⟩ hST hp
    · apply SimpleGraph.le_minDegree_of_forall_le_degree
      intro v
      rw [← degreeIn_eq_induce_degree R A v]
      have hv := hnear v.val v.property
      omega
    · simpa only [Fintype.card_fin, Nat.add_sub_cancel] using hglobal
  · have hglobal : ∀ v ∈ A, R.degree v < m := by
      intro v hv
      by_contra h
      exact hhigh ⟨v, hv, by omega⟩
    obtain ⟨K, hAK, hKmin⟩ := blue_core_of_no_global_red hm hd R A hA hnear hglobal
    obtain ⟨z, hz⟩ := hA
    have hzK := hAK hz
    let : Nonempty (K : Set (Fin (2 * m))) := ⟨⟨z, hzK⟩⟩
    right
    apply isContained_of_leaf_bunch S (K : Set (Fin (2 * m))) r ⟨z, hzK⟩ hST hp
    · apply SimpleGraph.le_minDegree_of_forall_le_degree
      intro v
      rw [← degreeIn_eq_induce_degree Rᶜ K v]
      have h := hsmallReal.trans (hKmin v.val v.property)
      exact_mod_cast h
    · have hsum := degree_add_compl R z
      simp only [Fintype.card_fin] at hsum ⊢
      have h := hglobal z hz
      omega

end Erdos547

#print axioms Erdos547.blue_core_of_no_global_red
#print axioms Erdos547.ramsey_of_near_core_of_leaf_bunch
