import ErdosProblems.Erdos577.JointLossTriangle

/-! The two opposite-pair insertions and exact degree splitting on a labeled quadrilateral. -/

namespace Erdos577.JointFinal

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

lemma opposite_replace (q : Quadrilateral G) (z : V) (hz : z ∉ q.support)
    (h0 : G.Adj z (q 0)) (h2 : G.Adj z (q 2)) (i : Fin 4) (hi : i = 1 ∨ i = 3) :
    QuadOn G (insert z (q.support.erase (q i))) := by
  rcases hi with rfl | rfl
  · exact q.replace_using_path z hz 1 0 3 2 (by decide) (by decide)
      h0 (q.adjacent 3).symm (q.adjacent 2).symm h2
  · exact q.replace_using_path z hz 3 0 1 2 (by decide) (by decide)
      h0 (q.adjacent 0) (q.adjacent 1) h2

lemma low_pair_replace (q : Quadrilateral G) (z : V) (hz : z ∉ q.support)
    (h1 : G.Adj z (q 1)) (h3 : G.Adj z (q 3)) (i : Fin 4) (hi : i = 0 ∨ i = 2) :
    QuadOn G (insert z (q.support.erase (q i))) := by
  rcases hi with rfl | rfl
  · exact q.replace_using_path z hz 0 1 2 3 (by decide) (by decide)
      h1 (q.adjacent 1) (q.adjacent 2) h3
  · exact q.replace_using_path z hz 2 1 0 3 (by decide) (by decide)
      h1 (q.adjacent 0).symm (q.adjacent 3).symm h3

lemma three_row_universal (q : Quadrilateral G) (z : V) (hz : z ∉ q.support)
    (hrow : ∀ i : Fin 4, i ≠ 3 → G.Adj z (q i)) (hdiag : G.Adj (q 1) (q 3)) :
    ∀ u ∈ q.support, QuadOn G (insert z (q.support.erase u)) := by
  intro u hu
  obtain ⟨i, rfl⟩ := (q.mem_support u).mp hu
  fin_cases i
  · exact q.replace_using_path z hz 0 1 3 2 (by decide) (by decide)
      (hrow 1 (by decide)) hdiag (q.adjacent 2).symm (hrow 2 (by decide))
  · exact opposite_replace q z hz (hrow 0 (by decide)) (hrow 2 (by decide)) 1 (Or.inl rfl)
  · exact q.replace_using_path z hz 2 0 3 1 (by decide) (by decide)
      (hrow 0 (by decide)) (q.adjacent 3).symm hdiag.symm (hrow 1 (by decide))
  · exact opposite_replace q z hz (hrow 0 (by decide)) (hrow 2 (by decide)) 3 (Or.inr rfl)

variable [DecidableRel G.Adj]

lemma degree_pair_eq (z a b : V) (hab : a ≠ b) :
    degreeIn G z {a, b} = (if G.Adj z a then 1 else 0) + (if G.Adj z b then 1 else 0) := by
  rw [degreeIn_insert G z a (by simpa only [mem_singleton] using hab)]
  have hs : degreeIn G z {b} = if G.Adj z b then 1 else 0 := by
    unfold degreeIn
    rw [filter_singleton]
    split_ifs <;> rfl
  rw [hs]

lemma degree_pair_le_one_iff (z a b : V) (hab : a ≠ b) :
    degreeIn G z {a, b} ≤ 1 ↔ ¬(G.Adj z a ∧ G.Adj z b) := by
  rw [degree_pair_eq z a b hab]
  by_cases ha : G.Adj z a <;> by_cases hb : G.Adj z b <;> simp [ha, hb]

lemma opposite_degree_split (q : Quadrilateral G) (z : V) :
    degreeIn G z q.support = degreeIn G z {q 0, q 2} + degreeIn G z {q 1, q 3} := by
  have he : ({q 0, q 2} : Finset V) ∪ {q 1, q 3} = q.support := by
    ext u
    constructor
    · intro hu
      simp only [mem_union, mem_insert, mem_singleton] at hu
      rcases hu with (rfl | rfl) | (rfl | rfl)
      · exact (q.mem_support _).mpr ⟨0, rfl⟩
      · exact (q.mem_support _).mpr ⟨2, rfl⟩
      · exact (q.mem_support _).mpr ⟨1, rfl⟩
      · exact (q.mem_support _).mpr ⟨3, rfl⟩
    · intro hu
      obtain ⟨i, rfl⟩ := (q.mem_support u).mp hu
      fin_cases i <;> simp
  have hd : Disjoint ({q 0, q 2} : Finset V) {q 1, q 3} := by
    apply disjoint_left.mpr
    intro u hu hv
    simp only [mem_insert, mem_singleton] at hu
    rcases hu with rfl | rfl <;>
      simp only [mem_insert, mem_singleton] at hv <;> rcases hv with hh | hh
    · exact q.injective.ne (by decide : (0 : Fin 4) ≠ 1) hh
    · exact q.injective.ne (by decide : (0 : Fin 4) ≠ 3) hh
    · exact q.injective.ne (by decide : (2 : Fin 4) ≠ 1) hh
    · exact q.injective.ne (by decide : (2 : Fin 4) ≠ 3) hh
  rw [← he, degreeIn_union G z hd]

end Erdos577.JointFinal
