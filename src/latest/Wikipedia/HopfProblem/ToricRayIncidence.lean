import Wikipedia.HopfProblem.ToricDivisors

/-!
# Incidence of the central components

Two distinct ray components meet exactly when their lattice vertices are
neighbours in the A₂ triangulation. Thus each central component meets exactly
its six lattice neighbours. In affine charts the intersections are the
corresponding coordinate axes.
-/

noncomputable section

open Set Topology
open scoped Matrix

namespace Wikipedia.HopfProblem.ToricFan

/-- The three unoriented edge directions of the triangular lattice. -/
def edgeDirection : Fin 3 → (Fin 2 → ℤ) := ![![1, 0], ![0, 1], ![1, -1]]

def AreAdjacent (v w : Fin 2 → ℤ) : Prop :=
  ∃ i : Fin 3, w - v = edgeDirection i ∨ w - v = -edgeDirection i

theorem edgeDirection_ne_zero (i : Fin 3) : edgeDirection i ≠ 0 := by
  fin_cases i <;> simp [edgeDirection, funext_iff]

theorem AreAdjacent.ne {v w : Fin 2 → ℤ} (h : AreAdjacent v w) : v ≠ w := by
  rintro rfl
  obtain ⟨i, h | h⟩ := h
  · exact edgeDirection_ne_zero i (by simpa only [sub_self] using h.symm)
  · exact edgeDirection_ne_zero i (by simpa only [sub_self, neg_eq_zero] using h.symm)

namespace Triangle

theorem vertices_adjacent (s : Triangle) {j k : Fin 3} (hjk : j ≠ k) :
    AreAdjacent (s.vertex j) (s.vertex k) := by
  cases hs : s.upper <;> fin_cases j <;> fin_cases k <;>
    simp_all [AreAdjacent, vertex, rays, edgeDirection, funext_iff,
      Fin.exists_fin_succ, Fin.forall_fin_succ]

theorem triangle_for_edge (v : Fin 2 → ℤ) (i : Fin 3) :
    ∃ s : Triangle, ∃ j k : Fin 3, s.vertex j = v ∧ s.vertex k = v + edgeDirection i := by
  fin_cases i
  · refine ⟨⟨v 0, v 1, false⟩, 0, 1, ?_, ?_⟩
    all_goals ext a; fin_cases a <;> simp [vertex, rays, edgeDirection]
  · refine ⟨⟨v 0, v 1, false⟩, 0, 2, ?_, ?_⟩
    all_goals ext a; fin_cases a <;> simp [vertex, rays, edgeDirection]
  · refine ⟨⟨v 0, v 1 - 1, false⟩, 2, 1, ?_, ?_⟩
    all_goals ext a; fin_cases a <;> simp [vertex, rays, edgeDirection, sub_eq_add_neg]

theorem exists_triangle_of_adjacent {v w : Fin 2 → ℤ} (h : AreAdjacent v w) :
    ∃ s : Triangle, ∃ j k : Fin 3, s.vertex j = v ∧ s.vertex k = w := by
  obtain ⟨i, hi | hi⟩ := h
  · have hw : w = v + edgeDirection i := by
      exact (sub_eq_iff_eq_add.mp hi).trans (add_comm _ _)
    obtain ⟨s, j, k, hj, hk⟩ := triangle_for_edge v i
    exact ⟨s, j, k, hj, hk.trans hw.symm⟩
  · have hv : v = w + edgeDirection i := by
      ext a
      have h := congrFun hi a
      change w a - v a = -edgeDirection i a at h
      change v a = w a + edgeDirection i a
      omega
    obtain ⟨s, j, k, hj, hk⟩ := triangle_for_edge w i
    exact ⟨s, k, j, hk.trans hv.symm, hj⟩

end Triangle

end Wikipedia.HopfProblem.ToricFan

namespace Wikipedia.HopfProblem.ToricSpace

open ToricCharts ToricFan Triangle

theorem rayDivisor_nonempty (v : Fin 2 → ℤ) : (rayDivisor v).Nonempty := by
  let s : Triangle := ⟨v 0, v 1, false⟩
  have hv : s.vertex 0 = v := by ext i; fin_cases i <;> rfl
  refine ⟨inclusion s 0, ?_⟩
  rw [← hv, mem_rayDivisor_vertex]
  rfl

theorem rayDivisor_inter_nonempty_iff_vertices (v w : Fin 2 → ℤ) :
    (rayDivisor v ∩ rayDivisor w).Nonempty ↔
      ∃ s : Triangle, ∃ j k : Fin 3, s.vertex j = v ∧ s.vertex k = w := by
  constructor
  · rintro ⟨x, hxv, hxw⟩
    obtain ⟨s, z, rfl⟩ := inclusion_jointly_surjective x
    obtain ⟨j, _, hj⟩ := (mem_rayDivisor_inclusion v s z).mp hxv
    obtain ⟨k, _, hk⟩ := (mem_rayDivisor_inclusion w s z).mp hxw
    exact ⟨s, j, k, hj, hk⟩
  · rintro ⟨s, j, k, rfl, rfl⟩
    exact ⟨inclusion s 0, (mem_rayDivisor_vertex s j 0).mpr rfl,
      (mem_rayDivisor_vertex s k 0).mpr rfl⟩

theorem rayDivisor_inter_nonempty_iff (v w : Fin 2 → ℤ) (hvw : v ≠ w) :
    (rayDivisor v ∩ rayDivisor w).Nonempty ↔ AreAdjacent v w := by
  rw [rayDivisor_inter_nonempty_iff_vertices]
  constructor
  · rintro ⟨s, j, k, rfl, rfl⟩
    exact vertices_adjacent s (fun h => hvw (congrArg s.vertex h))
  · exact exists_triangle_of_adjacent

theorem rayDivisor_inter_empty_of_not_adjacent (v w : Fin 2 → ℤ) (hvw : v ≠ w)
    (h : ¬AreAdjacent v w) : rayDivisor v ∩ rayDivisor w = ∅ := by
  rw [← Set.not_nonempty_iff_eq_empty, rayDivisor_inter_nonempty_iff v w hvw]
  exact h

theorem rayDivisor_inter_preimage (s : Triangle) (j k : Fin 3) :
    inclusion s ⁻¹' (rayDivisor (s.vertex j) ∩ rayDivisor (s.vertex k)) =
      {z | z j = 0 ∧ z k = 0} := by
  ext z
  simp only [Set.mem_preimage, Set.mem_inter_iff, mem_rayDivisor_vertex, Set.mem_ofPred_eq]

theorem branchCount_ge_two_iff (x : Space) : 2 ≤ branchCount x ↔
    ∃ v w : Fin 2 → ℤ, v ≠ w ∧ x ∈ rayDivisor v ∩ rayDivisor w := by
  have h := Set.one_lt_ncard (branchVertices_finite x)
  rw [branchVertices_ncard] at h
  rw [show (2 ≤ branchCount x) ↔ 1 < branchCount x by omega, h]
  constructor
  · rintro ⟨v, hv, w, hw, hne⟩
    exact ⟨v, w, hne, hv, hw⟩
  · rintro ⟨v, w, hne, hv, hw⟩
    exact ⟨v, hv, w, hw, hne⟩

end Wikipedia.HopfProblem.ToricSpace
