import ErdosProblems.Erdos633.ActualFieldConjugation
import ErdosProblems.Erdos633.VertexSectorAngle

/-!
# Corner equations for explicitly labelled dissections

The labels here are the actual ordered vertices of each dissection triangle,
not newly chosen congruence witnesses. This permits the original labels to be
retained under field conjugation. Sector additivity proves the corner-angle
equations whenever the three labelled angles are uniform across the tiles.
-/

namespace Erdos633

open scoped BigOperators

noncomputable def TriangleDissection.cornerCount {P : Triangle} {N : ℕ}
    (T : TriangleDissection P N) (z : ℂ) (k : Fin 3) : ℕ := by
  classical
  exact (Finset.univ.filter fun i : Fin N => (T.tile i).vertex k = z).card

noncomputable def TriangleDissection.outerCornerCount {P : Triangle} {N : ℕ}
    (T : TriangleDissection P N) (k : Fin 3) : ℕ :=
  ∑ j : Fin 3, T.cornerCount (P.vertex j) k

theorem TriangleDissection.sum_cornerCount_mul {P : Triangle} {N : ℕ}
    (T : TriangleDissection P N) (z : ℂ) (g : Fin 3 → ℝ) :
    (∑ k : Fin 3, (T.cornerCount z k : ℝ) * g k) =
      ∑ i : Fin N, ∑ k : Fin 3, if (T.tile i).vertex k = z then g k else 0 := by
  classical
  calc
    _ = ∑ k : Fin 3, ∑ i : Fin N, if (T.tile i).vertex k = z then g k else 0 := by
      apply Finset.sum_congr rfl
      intro k _
      rw [← Finset.sum_filter]
      simp [TriangleDissection.cornerCount]
    _ = _ := Finset.sum_comm

open Classical in
theorem TriangleDissection.outer_sector_contribution {P : Triangle} {N : ℕ}
    (T : TriangleDissection P N) (θ : Fin 3 → ℝ)
    (hθ : ∀ i : Fin N, ∀ k : Fin 3, (T.tile i).cornerAngle k = θ k)
    (j : Fin 3) (i : Fin N) :
    (∑ k : Fin 3, if (T.tile i).vertex k = P.vertex j then θ k / 2 else 0) =
      if P.vertex j ∈ (T.tile i).carrier then (T.tile i).localSectorArea (P.vertex j) else 0 := by
  classical
  by_cases hi : P.vertex j ∈ (T.tile i).carrier
  · rw [if_pos hi]
    obtain ⟨k, hk⟩ := (T.mem_tile_at_outer_vertex_iff j i).mp hi
    rw [← hk]
    simp only [(T.tile i).vertex_injective.eq_iff, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    rw [(T.tile i).localSectorArea_vertex, hθ]
  · rw [if_neg hi]
    apply Finset.sum_eq_zero
    intro k _
    apply if_neg
    intro hk
    exact hi (hk ▸ (T.tile i).vertex_mem_carrier k)

theorem TriangleDissection.outer_angle_count_identity {P : Triangle} {N : ℕ}
    (T : TriangleDissection P N) (θ : Fin 3 → ℝ)
    (hθ : ∀ i : Fin N, ∀ k : Fin 3, (T.tile i).cornerAngle k = θ k) (j : Fin 3) :
    (∑ k : Fin 3, (T.cornerCount (P.vertex j) k : ℝ) * θ k) = P.cornerAngle j := by
  classical
  let s := Finset.univ.filter (fun i : Fin N => P.vertex j ∈ (T.tile i).carrier)
  have hs (i : Fin N) : i ∈ s ↔ P.vertex j ∈ (T.tile i).carrier := by simp [s]
  have h : P.localSectorArea (P.vertex j) =
      ∑ k : Fin 3, (T.cornerCount (P.vertex j) k : ℝ) * (θ k / 2) := by
    calc
      _ = ∑ i : {i : Fin N // P.vertex j ∈ (T.tile i).carrier},
          (T.tile i).localSectorArea (P.vertex j) :=
        T.localSectorArea_eq_sum (P.vertex j) (P.vertex_mem_carrier j)
      _ = ∑ i ∈ s, (T.tile i).localSectorArea (P.vertex j) :=
        (Finset.sum_subtype s hs
          (fun i : Fin N => (T.tile i).localSectorArea (P.vertex j))).symm
      _ = ∑ i : Fin N, if P.vertex j ∈ (T.tile i).carrier then
          (T.tile i).localSectorArea (P.vertex j) else 0 := Finset.sum_filter _ _
      _ = ∑ i : Fin N, ∑ k : Fin 3,
          if (T.tile i).vertex k = P.vertex j then θ k / 2 else 0 :=
        Finset.sum_congr rfl (fun i _ => (T.outer_sector_contribution θ hθ j i).symm)
      _ = _ := (T.sum_cornerCount_mul (P.vertex j) (fun k => θ k / 2)).symm
  rw [P.localSectorArea_vertex] at h
  simp only [← mul_div_assoc, ← Finset.sum_div] at h
  linarith

theorem TriangleDissection.outer_angle_total {P : Triangle} {N : ℕ}
    (T : TriangleDissection P N) (θ : Fin 3 → ℝ)
    (hθ : ∀ i : Fin N, ∀ k : Fin 3, (T.tile i).cornerAngle k = θ k) :
    (∑ k : Fin 3, (T.outerCornerCount k : ℝ) * θ k) = Real.pi := by
  simp only [TriangleDissection.outerCornerCount, Nat.cast_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [T.outer_angle_count_identity θ hθ, P.sum_cornerAngle]

theorem TriangleDissection.cornerCount_vertexImage {P P' : Triangle} {N : ℕ}
    (T : TriangleDissection P N) (U : TriangleDissection P' N) (f : ℂ → ℂ)
    (hf : Set.InjOn f T.vertexFinset) (hP : P.VertexImage P' f)
    (hQ : ∀ i : Fin N, (T.tile i).VertexImage (U.tile i) f) (j k : Fin 3) :
    U.cornerCount (P'.vertex j) k = T.cornerCount (P.vertex j) k := by
  classical
  unfold TriangleDissection.cornerCount
  congr 1
  apply Finset.filter_congr
  intro i _
  rw [hQ i k, hP j]
  exact hf.eq_iff (T.vertex_mem_vertexFinset i k) (T.outer_vertex_mem_vertexFinset j)

theorem TriangleDissection.outerCornerCount_vertexImage {P P' : Triangle} {N : ℕ}
    (T : TriangleDissection P N) (U : TriangleDissection P' N) (f : ℂ → ℂ)
    (hf : Set.InjOn f T.vertexFinset) (hP : P.VertexImage P' f)
    (hQ : ∀ i : Fin N, (T.tile i).VertexImage (U.tile i) f) (k : Fin 3) :
    U.outerCornerCount k = T.outerCornerCount k := by
  unfold TriangleDissection.outerCornerCount
  exact Finset.sum_congr rfl (fun j _ => T.cornerCount_vertexImage U f hf hP hQ j k)

theorem TriangleDissection.transported_outer_angle_total {P P' : Triangle} {N : ℕ}
    (T : TriangleDissection P N) (U : TriangleDissection P' N) (f : ℂ → ℂ)
    (hf : Set.InjOn f T.vertexFinset) (hP : P.VertexImage P' f)
    (hQ : ∀ i : Fin N, (T.tile i).VertexImage (U.tile i) f)
    (θ : Fin 3 → ℝ) (hθ : ∀ i : Fin N, ∀ k : Fin 3, (U.tile i).cornerAngle k = θ k) :
    (∑ k : Fin 3, (T.outerCornerCount k : ℝ) * θ k) = Real.pi := by
  have h := U.outer_angle_total θ hθ
  simpa only [T.outerCornerCount_vertexImage U f hf hP hQ] using h

theorem CongruentTiling.labelledDissection_cornerCount
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N) (z : ℂ) (k : Fin 3) :
    T.labelledDissection.cornerCount z k = T.cornerCount z k := rfl

theorem CongruentTiling.labelledDissection_outerCornerCount
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N) (k : Fin 3) :
    T.labelledDissection.outerCornerCount k = T.outerCornerCount k := rfl

end Erdos633
