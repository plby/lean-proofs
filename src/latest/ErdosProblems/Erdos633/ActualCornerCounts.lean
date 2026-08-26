import ErdosProblems.Erdos633.LabelledTiling

/-!
# Corner counts extracted from congruent tilings

Every label occurs exactly once per tile. The finite counts and their global
conservation identities are proved from the labelled geometric tiles. Local
angle sums around a vertex are not assumed or asserted in this file.
-/

namespace Erdos633

open scoped BigOperators

noncomputable def CongruentTiling.cornerCount {P R : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) (z : ℂ) (k : Fin 3) : ℕ := by
  classical
  exact (Finset.univ.filter fun i : Fin N => (T.labelledTile i).vertex k = z).card

theorem CongruentTiling.cornerCount_pos_iff {P R : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) (z : ℂ) (k : Fin 3) :
    0 < T.cornerCount z k ↔ ∃ i : Fin N, (T.labelledTile i).vertex k = z := by
  classical
  simp only [CongruentTiling.cornerCount, Finset.card_pos, Finset.Nonempty,
    Finset.mem_filter, Finset.mem_univ, true_and]

theorem CongruentTiling.sum_cornerCount {P R : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) (k : Fin 3) :
    ∑ z ∈ T.labelledDissection.vertexFinset, T.cornerCount z k = N := by
  classical
  have hmap : Set.MapsTo (fun i : Fin N => (T.labelledTile i).vertex k)
      (↑(Finset.univ : Finset (Fin N))) (↑T.labelledDissection.vertexFinset) := by
    intro i _
    exact T.labelledDissection.vertex_mem_vertexFinset i k
  have h := Finset.card_eq_sum_card_fiberwise hmap
  simpa only [CongruentTiling.cornerCount, Finset.card_univ, Fintype.card_fin] using h.symm

theorem CongruentTiling.sum_cornerCount_mul {P R : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) (z : ℂ) (f : Fin 3 → ℝ) :
    ∑ k : Fin 3, (T.cornerCount z k : ℝ) * f k =
      ∑ i : Fin N, ∑ k : Fin 3, if (T.labelledTile i).vertex k = z then f k else 0 := by
  classical
  calc
    _ = ∑ k : Fin 3, ∑ i : Fin N,
        if (T.labelledTile i).vertex k = z then f k else 0 := by
      apply Finset.sum_congr rfl
      intro k _
      rw [← Finset.sum_filter]
      simp [CongruentTiling.cornerCount]
    _ = _ := Finset.sum_comm

theorem CongruentTiling.outer_cornerCount_pos {P R : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) (j : Fin 3) : ∃ k : Fin 3, 0 < T.cornerCount (P.vertex j) k := by
  obtain ⟨i, k, hk⟩ := T.labelledDissection.outer_vertex_incidence j
  exact ⟨k, (T.cornerCount_pos_iff _ k).mpr ⟨i, hk⟩⟩

noncomputable def CongruentTiling.angleSumAt {P R : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) (z : ℂ) : ℝ :=
  ∑ k : Fin 3, (T.cornerCount z k : ℝ) * R.cornerAngle k

theorem CongruentTiling.sum_angleSumAt {P R : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) :
    ∑ z ∈ T.labelledDissection.vertexFinset, T.angleSumAt z = N * Real.pi := by
  classical
  unfold CongruentTiling.angleSumAt
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, ← Nat.cast_sum, T.sum_cornerCount]
  rw [← Finset.mul_sum, R.sum_cornerAngle]

theorem CongruentTiling.outer_angleSumAt_pos {P R : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) (j : Fin 3) : 0 < T.angleSumAt (P.vertex j) := by
  obtain ⟨k, hk⟩ := T.outer_cornerCount_pos j
  apply Finset.sum_pos'
  · intro i _
    exact mul_nonneg (Nat.cast_nonneg _) (R.cornerAngle_pos i).le
  · exact ⟨k, Finset.mem_univ _, mul_pos (by exact_mod_cast hk) (R.cornerAngle_pos k)⟩

theorem CongruentTiling.angleSumAt_pos_of_vertex {P R : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) (z : ℂ) (hz : z ∈ T.labelledDissection.vertexFinset) :
    0 < T.angleSumAt z := by
  obtain ⟨i, k, hk⟩ := (T.labelledDissection.mem_vertexFinset z).mp hz
  have hcount : 0 < T.cornerCount z k := (T.cornerCount_pos_iff z k).mpr ⟨i, hk⟩
  apply Finset.sum_pos'
  · intro j _
    exact mul_nonneg (Nat.cast_nonneg _) (R.cornerAngle_pos j).le
  · exact ⟨k, Finset.mem_univ _, mul_pos (by exact_mod_cast hcount) (R.cornerAngle_pos k)⟩

noncomputable def Triangle.outerVertexFinset (P : Triangle) : Finset ℂ := by
  classical
  exact Finset.univ.image P.vertex

theorem TriangleDissection.outerVertexFinset_subset {P : Triangle} {N : ℕ}
    (T : TriangleDissection P N) : P.outerVertexFinset ⊆ T.vertexFinset := by
  classical
  intro z hz
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
  exact T.outer_vertex_mem_vertexFinset i

noncomputable def CongruentTiling.outerCornerCount {P R : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) (k : Fin 3) : ℕ := ∑ j : Fin 3, T.cornerCount (P.vertex j) k

theorem CongruentTiling.cornerCount_le_outerCornerCount {P R : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) (j k : Fin 3) :
    T.cornerCount (P.vertex j) k ≤ T.outerCornerCount k := by
  exact Finset.single_le_sum (fun i _ => Nat.zero_le (T.cornerCount (P.vertex i) k))
    (Finset.mem_univ j)

theorem CongruentTiling.cornerCount_eq_zero_of_outer_eq_zero {P R : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) (j k : Fin 3) (hk : T.outerCornerCount k = 0) :
    T.cornerCount (P.vertex j) k = 0 := by
  have h := T.cornerCount_le_outerCornerCount j k
  omega

theorem CongruentTiling.nonouter_cornerCount_total {P R : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) (k : Fin 3) :
    (∑ z ∈ T.labelledDissection.vertexFinset \ P.outerVertexFinset, T.cornerCount z k) +
      T.outerCornerCount k = N := by
  classical
  have houter : ∑ z ∈ P.outerVertexFinset, T.cornerCount z k = T.outerCornerCount k := by
    unfold Triangle.outerVertexFinset CongruentTiling.outerCornerCount
    apply Finset.sum_image
    intro i _ j _ hij
    exact P.vertex_injective hij
  rw [← houter, Finset.sum_sdiff T.labelledDissection.outerVertexFinset_subset]
  exact T.sum_cornerCount k

end Erdos633
