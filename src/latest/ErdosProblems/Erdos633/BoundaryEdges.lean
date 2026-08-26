import ErdosProblems.Erdos633.AngleSimilarity

/-!
# Labelled triangle edges and supporting faces

The edge with label `k` is opposite the corner with label `k`. Barycentric
coordinates identify each closed edge with the corresponding supporting face.
An open tile-edge point on an outer edge forces the whole tile edge onto it.
-/

namespace Erdos633

open scoped BigOperators

def Triangle.edgeStart (P : Triangle) : Fin 3 → ℂ := ![P.b, P.c, P.a]
def Triangle.edgeEnd (P : Triangle) : Fin 3 → ℂ := ![P.c, P.a, P.b]

def Triangle.edge (P : Triangle) (k : Fin 3) : Set ℂ :=
  segment ℝ (P.edgeStart k) (P.edgeEnd k)

def Triangle.openEdge (P : Triangle) (k : Fin 3) : Set ℂ :=
  openSegment ℝ (P.edgeStart k) (P.edgeEnd k)

noncomputable def Triangle.sideLength (P : Triangle) (k : Fin 3) : ℝ :=
  dist (P.edgeStart k) (P.edgeEnd k)

theorem Triangle.edgeStart_mem_carrier (P : Triangle) (k : Fin 3) :
    P.edgeStart k ∈ P.carrier := by
  fin_cases k
  · exact P.vertex_mem_carrier 1
  · exact P.vertex_mem_carrier 2
  · exact P.vertex_mem_carrier 0

theorem Triangle.edgeEnd_mem_carrier (P : Triangle) (k : Fin 3) :
    P.edgeEnd k ∈ P.carrier := by
  fin_cases k
  · exact P.vertex_mem_carrier 2
  · exact P.vertex_mem_carrier 0
  · exact P.vertex_mem_carrier 1

theorem Triangle.edgeStart_ne_edgeEnd (P : Triangle) (k : Fin 3) :
    P.edgeStart k ≠ P.edgeEnd k := by
  fin_cases k
  · exact P.b_ne_c
  · exact P.swapBC.a_ne_b.symm
  · exact P.a_ne_b

theorem Triangle.sideLength_pos (P : Triangle) (k : Fin 3) : 0 < P.sideLength k :=
  dist_pos.mpr (P.edgeStart_ne_edgeEnd k)

theorem Triangle.edge_subset_carrier (P : Triangle) (k : Fin 3) : P.edge k ⊆ P.carrier :=
  P.convex_carrier.segment_subset (P.edgeStart_mem_carrier k) (P.edgeEnd_mem_carrier k)

theorem Triangle.openEdge_subset_edge (P : Triangle) (k : Fin 3) : P.openEdge k ⊆ P.edge k :=
  openSegment_subset_segment ℝ _ _

theorem Triangle.barycentric_vertex (P : Triangle) (i j : Fin 3) :
    P.barycentric (P.vertex i) j = if i = j then 1 else 0 := by
  have ha : P.coordinateEquiv.symm P.a = 0 := by
    rw [← P.coordinateEquiv_zero, P.coordinateEquiv.symm_apply_apply]
  have hb : P.coordinateEquiv.symm P.b = 1 := by
    rw [← P.coordinateEquiv_one, P.coordinateEquiv.symm_apply_apply]
  have hc : P.coordinateEquiv.symm P.c = Complex.I := by
    rw [← P.coordinateEquiv_I, P.coordinateEquiv.symm_apply_apply]
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;>
    norm_num [Triangle.vertex, Triangle.barycentric, ha, hb, hc, Matrix.cons_val_two] <;> decide

theorem Triangle.barycentric_edgeStart_self (P : Triangle) (k : Fin 3) :
    P.barycentric (P.edgeStart k) k = 0 := by
  have hk : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hk with rfl | rfl | rfl
  · exact (P.barycentric_vertex 1 0).trans (by norm_num)
  · exact (P.barycentric_vertex 2 1).trans (by norm_num; decide)
  · exact (P.barycentric_vertex 0 2).trans (by norm_num; decide)

theorem Triangle.barycentric_edgeEnd_self (P : Triangle) (k : Fin 3) :
    P.barycentric (P.edgeEnd k) k = 0 := by
  have hk : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hk with rfl | rfl | rfl
  · exact (P.barycentric_vertex 2 0).trans (by norm_num; decide)
  · exact (P.barycentric_vertex 0 1).trans (by norm_num)
  · exact (P.barycentric_vertex 1 2).trans (by norm_num; decide)

theorem Triangle.barycentric_repr (P : Triangle) (z : ℂ) :
    P.barycentric z 0 • P.a + P.barycentric z 1 • P.b + P.barycentric z 2 • P.c = z := by
  have h : P.barycentric z 0 • P.a + P.barycentric z 1 • P.b + P.barycentric z 2 • P.c =
      P.coordinateEquiv (P.coordinateEquiv.symm z) := by
    rw [P.coordinateEquiv_apply]
    change (1 - (P.coordinateEquiv.symm z).re - (P.coordinateEquiv.symm z).im) • P.a +
      (P.coordinateEquiv.symm z).re • P.b + (P.coordinateEquiv.symm z).im • P.c = _
    simp only [sub_smul, one_smul, smul_sub]
    abel
  exact h.trans (P.coordinateEquiv.apply_symm_apply z)

theorem Triangle.mem_edge_iff (P : Triangle) (k : Fin 3) (z : ℂ) :
    z ∈ P.edge k ↔ z ∈ P.carrier ∧ P.barycentric z k = 0 := by
  constructor
  · intro hz
    refine ⟨P.edge_subset_carrier k hz, ?_⟩
    obtain ⟨a, b, _, _, hab, rfl⟩ := hz
    rw [P.barycentric_combo _ _ a b hab, P.barycentric_edgeStart_self,
      P.barycentric_edgeEnd_self]
    simp
  · rintro ⟨hz, hk⟩
    have hn := (P.mem_carrier_iff_barycentric z).mp hz
    have hs := P.sum_barycentric z
    norm_num [Fin.sum_univ_succ] at hs
    have hr := P.barycentric_repr z
    have hk' : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk' with rfl | rfl | rfl
    · refine ⟨P.barycentric z 1, P.barycentric z 2, hn 1, hn 2, by linarith, ?_⟩
      change P.barycentric z 1 • P.b + P.barycentric z 2 • P.c = z
      simpa only [hk, zero_smul, zero_add] using hr
    · refine ⟨P.barycentric z 2, P.barycentric z 0, hn 2, hn 0, by linarith, ?_⟩
      change P.barycentric z 2 • P.c + P.barycentric z 0 • P.a = z
      simpa only [hk, zero_smul, add_zero, zero_add, add_comm] using hr
    · refine ⟨P.barycentric z 0, P.barycentric z 1, hn 0, hn 1, by linarith, ?_⟩
      change P.barycentric z 0 • P.a + P.barycentric z 1 • P.b = z
      simpa only [hk, zero_smul, add_zero] using hr

theorem Triangle.edge_not_mem_interior (P : Triangle) (k : Fin 3) {z : ℂ}
    (hz : z ∈ P.edge k) : z ∉ interior P.carrier := by
  intro hi
  have hp := (P.mem_interior_iff_barycentric z).mp hi k
  rw [(P.mem_edge_iff k z).mp hz |>.2] at hp
  exact (lt_irrefl 0) hp

theorem Triangle.barycentric_edge_endpoints_sum (P : Triangle) (k j : Fin 3) (hjk : j ≠ k) :
    P.barycentric (P.edgeStart k) j + P.barycentric (P.edgeEnd k) j = 1 := by
  have hk : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hk with rfl | rfl | rfl
  · change P.barycentric (P.vertex 1) j + P.barycentric (P.vertex 2) j = 1
    rw [P.barycentric_vertex, P.barycentric_vertex]
    have hj : j = 1 ∨ j = 2 := by omega
    rcases hj with rfl | rfl <;> norm_num <;> decide
  · change P.barycentric (P.vertex 2) j + P.barycentric (P.vertex 0) j = 1
    rw [P.barycentric_vertex, P.barycentric_vertex]
    have hj : j = 0 ∨ j = 2 := by omega
    rcases hj with rfl | rfl <;> norm_num <;> decide
  · change P.barycentric (P.vertex 0) j + P.barycentric (P.vertex 1) j = 1
    rw [P.barycentric_vertex, P.barycentric_vertex]
    have hj : j = 0 ∨ j = 1 := by omega
    rcases hj with rfl | rfl <;> norm_num

theorem Triangle.barycentric_pos_of_mem_openEdge (P : Triangle) (k j : Fin 3)
    (hjk : j ≠ k) {z : ℂ} (hz : z ∈ P.openEdge k) : 0 < P.barycentric z j := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
  rw [P.barycentric_combo _ _ a b hab]
  have hx := (P.mem_carrier_iff_barycentric _).mp (P.edgeStart_mem_carrier k) j
  have hy := (P.mem_carrier_iff_barycentric _).mp (P.edgeEnd_mem_carrier k) j
  have hs := P.barycentric_edge_endpoints_sum k j hjk
  rcases eq_or_lt_of_le hx with hx | hx
  · have he : P.barycentric (P.edgeEnd k) j = 1 := by linarith
    rw [← hx, he]
    simpa using hb
  · exact add_pos_of_pos_of_nonneg (mul_pos ha hx) (mul_nonneg hb.le hy)

theorem Triangle.openEdges_disjoint (P : Triangle) {k l : Fin 3} (hkl : k ≠ l) :
    Disjoint (P.openEdge k) (P.openEdge l) := by
  apply Set.disjoint_left.mpr
  intro z hk hl
  have hp := P.barycentric_pos_of_mem_openEdge k l hkl.symm hk
  have hz := ((P.mem_edge_iff l z).mp (P.openEdge_subset_edge l hl)).2
  rw [hz] at hp
  exact (lt_irrefl 0) hp

theorem Triangle.boundary_nonvertex_mem_openEdge (P : Triangle) (z : ℂ)
    (hz : z ∈ P.carrier) (hint : z ∉ interior P.carrier)
    (hvertex : z ∉ Set.range P.vertex) : ∃ k : Fin 3, z ∈ P.openEdge k := by
  rcases P.boundary_nonvertex_mem_open_edges z hz hint hvertex with h | h | h
  · exact ⟨2, h⟩
  · refine ⟨1, ?_⟩
    change z ∈ openSegment ℝ P.c P.a
    rw [openSegment_symm]
    exact h
  · exact ⟨0, h⟩

/-- A supporting affine coordinate cannot vanish at an interior point of a
segment in the triangle without vanishing at both endpoints. -/
theorem Triangle.edge_contains_segment_of_open_point (P : Triangle) (k : Fin 3)
    {x y z : ℂ} (hx : x ∈ P.carrier) (hy : y ∈ P.carrier)
    (hz : z ∈ P.edge k) (hseg : z ∈ openSegment ℝ x y) :
    segment ℝ x y ⊆ P.edge k := by
  have hx0 := (P.mem_carrier_iff_barycentric x).mp hx k
  have hy0 := (P.mem_carrier_iff_barycentric y).mp hy k
  have hz0 := ((P.mem_edge_iff k z).mp hz).2
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hseg
  rw [P.barycentric_combo x y a b hab] at hz0
  have hax : a * P.barycentric x k = 0 := by
    nlinarith only [hz0, mul_nonneg ha.le hx0, mul_nonneg hb.le hy0]
  have hby : b * P.barycentric y k = 0 := by
    nlinarith only [hz0, mul_nonneg ha.le hx0, mul_nonneg hb.le hy0]
  have hxz := (mul_eq_zero.mp hax).resolve_left (ne_of_gt ha)
  have hyz := (mul_eq_zero.mp hby).resolve_left (ne_of_gt hb)
  intro w hw
  refine (P.mem_edge_iff k w).mpr ⟨P.convex_carrier.segment_subset hx hy hw, ?_⟩
  obtain ⟨c, d, _, _, hcd, rfl⟩ := hw
  rw [P.barycentric_combo x y c d hcd, hxz, hyz]
  simp

theorem Triangle.edgeStart_mem_vertices (P : Triangle) (k : Fin 3) :
    P.edgeStart k ∈ Set.range P.vertex := by
  fin_cases k
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨0, rfl⟩

theorem Triangle.edgeEnd_mem_vertices (P : Triangle) (k : Fin 3) :
    P.edgeEnd k ∈ Set.range P.vertex := by
  fin_cases k
  · exact ⟨2, rfl⟩
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩

theorem Triangle.mem_openEdge_of_not_vertex (P : Triangle) (k : Fin 3) {z : ℂ}
    (hz : z ∈ P.edge k) (hv : z ∉ Set.range P.vertex) : z ∈ P.openEdge k := by
  apply mem_openSegment_of_ne_left_right _ _ hz
  · intro h
    exact hv (h ▸ P.edgeStart_mem_vertices k)
  · intro h
    exact hv (h ▸ P.edgeEnd_mem_vertices k)

theorem Triangle.cornerAngle_lt_pi (P : Triangle) (k : Fin 3) : P.cornerAngle k < Real.pi := by
  fin_cases k
  · exact P.angleA_lt_pi
  · exact P.angleB_lt_pi
  · exact P.angleC_lt_pi

theorem Triangle.localSectorArea_boundary_le_half_pi (P : Triangle) {z : ℂ}
    (hz : z ∈ P.carrier) (hint : z ∉ interior P.carrier) : P.localSectorArea z ≤ Real.pi / 2 := by
  by_cases hv : z ∈ Set.range P.vertex
  · obtain ⟨j, rfl⟩ := hv
    rw [P.localSectorArea_vertex]
    linarith [P.cornerAngle_lt_pi j]
  · rw [P.localSectorArea_boundary_nonvertex z hz hint hv]

/-- Away from the finite vertex set, an outer boundary point belongs to only
one tile. The proof uses the already established local-sector area ledger. -/
theorem TriangleDissection.boundary_nonvertex_tile_unique {P : Triangle} {N : ℕ}
    (T : TriangleDissection P N) {z : ℂ} (hz : z ∈ P.carrier)
    (hint : z ∉ interior P.carrier) (hv : z ∉ T.vertexFinset)
    {i j : Fin N} (hi : z ∈ (T.tile i).carrier) (hj : z ∈ (T.tile j).carrier) : i = j := by
  classical
  by_contra hij
  have ha (l : Fin N) (hl : z ∈ (T.tile l).carrier) :
      (T.tile l).localSectorArea z = Real.pi / 2 := by
    apply (T.tile l).localSectorArea_boundary_nonvertex z hl
    · exact fun h => hint (interior_mono (T.tile_subset l) h)
    · rintro ⟨k, hk⟩
      exact hv ((T.mem_vertexFinset z).mpr ⟨l, k, hk⟩)
  let f (l : Fin N) := if z ∈ (T.tile l).carrier then (T.tile l).localSectorArea z else 0
  have hf (l : Fin N) : 0 ≤ f l := by
    dsimp [f]
    split_ifs
    · exact (T.tile l).localSectorArea_nonneg z
    · exact le_rfl
  have hsum : f i + f j ≤ ∑ l : Fin N, f l :=
    Finset.add_le_sum (fun l _ => hf l) (Finset.mem_univ i) (Finset.mem_univ j) hij
  have hi' : f i = Real.pi / 2 := by simp only [f, if_pos hi, ha i hi]
  have hj' : f j = Real.pi / 2 := by simp only [f, if_pos hj, ha j hj]
  have ht : P.localSectorArea z = ∑ l, f l := T.localSectorArea_eq_sum_ite z hz
  rw [hi', hj', ← ht] at hsum
  have hbound := P.localSectorArea_boundary_le_half_pi hz hint
  linarith [Real.pi_pos]

end Erdos633
