import ErdosProblems.Erdos633.SegmentPartitions

/-!
# A longest tile edge on every outer side

If a tile angle exceeds pi/2 and never occurs at an outer corner, then every
outer side contains a whole tile edge opposite that angle. The conclusion is
proved for actual congruent tilings, allowing arbitrary partial edge contacts.
-/

namespace Erdos633

open scoped BigOperators

theorem Triangle.vertex_eq_edge_endpoint_of_ne (P : Triangle) (k j : Fin 3)
    (hjk : j ≠ k) : P.vertex j = P.edgeStart k ∨ P.vertex j = P.edgeEnd k := by
  fin_cases k <;> fin_cases j <;>
    simp_all [Triangle.vertex, Triangle.edgeStart, Triangle.edgeEnd]

theorem Triangle.collinear_edge (P : Triangle) (k : Fin 3) : Collinear ℝ (P.edge k) := by
  rw [collinear_iff_exists_forall_eq_smul_vadd]
  refine ⟨P.edgeStart k, P.edgeEnd k - P.edgeStart k, ?_⟩
  intro z hz
  rw [Triangle.edge, segment_eq_image_lineMap] at hz
  obtain ⟨t, _, rfl⟩ := hz
  exact ⟨t, AffineMap.lineMap_apply_module' _ _ _⟩

theorem Triangle.edge_labels_eq_of_subsets (P Q : Triangle) (k i j : Fin 3)
    (hi : P.edge i ⊆ Q.edge k) (hj : P.edge j ⊆ Q.edge k) : i = j := by
  by_contra hij
  have hm (l n : Fin 3) (hl : P.edge l ⊆ Q.edge k) (hn : n ≠ l) :
      P.vertex n ∈ Q.edge k := by
    rcases P.vertex_eq_edge_endpoint_of_ne l n hn with h | h
    · rw [h]
      exact hl (left_mem_segment ℝ _ _)
    · rw [h]
      exact hl (right_mem_segment ℝ _ _)
  have hv (n : Fin 3) : P.vertex n ∈ Q.edge k := by
    by_cases hn : n = i
    · subst n
      exact hm j i hj hij
    · exact hm i n hi hn
  apply P.not_collinear
  apply (Q.collinear_edge k).subset
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl
  · exact hv 0
  · exact hv 1
  · exact hv 2

theorem CongruentTiling.boundary_cornerCount_le_one {P R : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) {z : ℂ} (hz : z ∈ P.carrier)
    (hint : z ∉ interior P.carrier) (g : Fin 3) (hg : Real.pi / 2 < R.cornerAngle g) :
    T.cornerCount z g ≤ 1 := by
  by_contra h
  have htwo : 2 ≤ T.cornerCount z g := by omega
  have htwoR : (2 : ℝ) ≤ T.cornerCount z g := by exact_mod_cast htwo
  obtain ⟨i, hi⟩ := (T.cornerCount_pos_iff z g).mp (by omega)
  have hv : z ∈ T.labelledDissection.vertexFinset :=
    (T.labelledDissection.mem_vertexFinset z).mpr ⟨i, g, hi⟩
  have hterm : (T.cornerCount z g : ℝ) * R.cornerAngle g ≤ T.angleSumAt z :=
    Finset.single_le_sum
      (fun j _ => mul_nonneg (Nat.cast_nonneg _) (R.cornerAngle_pos j).le)
      (Finset.mem_univ g)
  have hmul := mul_le_mul_of_nonneg_right htwoR (R.cornerAngle_pos g).le
  have hbal := T.local_angle_balance z hv
  have harea := P.localSectorArea_boundary_le_half_pi hz hint
  have hstraight : 0 ≤ (T.straightCount z : ℝ) * Real.pi :=
    mul_nonneg (Nat.cast_nonneg _) Real.pi_pos.le
  linarith

theorem CongruentTiling.boundary_obtuse_corner_unique {P R : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) {z : ℂ} (hz : z ∈ P.carrier)
    (hint : z ∉ interior P.carrier) (g : Fin 3) (hg : Real.pi / 2 < R.cornerAngle g)
    {i j : Fin N} (hi : (T.labelledTile i).vertex g = z)
    (hj : (T.labelledTile j).vertex g = z) : i = j := by
  classical
  have hcard := T.boundary_cornerCount_le_one hz hint g hg
  unfold CongruentTiling.cornerCount at hcard
  exact Finset.card_le_one.mp hcard i
    (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩) j
    (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩)

theorem CongruentTiling.labelled_vertex_ne_outer_of_count_zero
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N) (i : Fin N) (g j : Fin 3)
    (hg : T.outerCornerCount g = 0) : (T.labelledTile i).vertex g ≠ P.vertex j := by
  intro h
  have hp := (T.cornerCount_pos_iff (P.vertex j) g).mpr ⟨i, h⟩
  rw [T.cornerCount_eq_zero_of_outer_eq_zero j g hg] at hp
  omega

theorem CongruentTiling.boundarySideCount_pos_of_obtuse_of_outer_eq_zero
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N) (k g : Fin 3)
    (hg : Real.pi / 2 < R.cornerAngle g) (houter : T.outerCornerCount g = 0) :
    0 < T.boundarySideCount k g := by
  classical
  by_contra hpos
  let I := T.labelledDissection.boundaryEdgeIndices k
  have hnolabel (p : I) : p.val.2 ≠ g := by
    intro h
    apply hpos
    apply Finset.card_pos.mpr
    exact ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ p, h⟩⟩
  let mark (p : I) := (T.labelledTile p.val.1).vertex g
  have hsub (p : I) : (T.labelledTile p.val.1).edge p.val.2 ⊆ P.edge k :=
    (T.labelledDissection.mem_boundaryEdgeIndices k p.val).mp p.property
  have hmark (p : I) :
      mark p = (T.labelledTile p.val.1).edgeStart p.val.2 ∨
      mark p = (T.labelledTile p.val.1).edgeEnd p.val.2 :=
    (T.labelledTile p.val.1).vertex_eq_edge_endpoint_of_ne p.val.2 g (hnolabel p).symm
  have hmarkedge (p : I) : mark p ∈ P.edge k := by
    rcases hmark p with h | h
    · rw [h]
      exact hsub p (left_mem_segment ℝ _ _)
    · rw [h]
      exact hsub p (right_mem_segment ℝ _ _)
  have hends (p : I) : mark p ≠ P.edgeStart k ∧ mark p ≠ P.edgeEnd k := by
    obtain ⟨j, hj⟩ := P.edgeStart_mem_vertices k
    obtain ⟨l, hl⟩ := P.edgeEnd_mem_vertices k
    constructor
    · rw [← hj]
      exact T.labelled_vertex_ne_outer_of_count_zero p.val.1 g j houter
    · rw [← hl]
      exact T.labelled_vertex_ne_outer_of_count_zero p.val.1 g l houter
  have hinj : Function.Injective mark := by
    intro p q hpq
    have hpedge := hmarkedge p
    have hij : p.val.1 = q.val.1 := T.boundary_obtuse_corner_unique
      (P.edge_subset_carrier k hpedge) (P.edge_not_mem_interior k hpedge) g hg rfl hpq.symm
    have hqsub := hsub q
    rw [← hij] at hqsub
    have hlabel := (T.labelledTile p.val.1).edge_labels_eq_of_subsets P k
      p.val.2 q.val.2 (hsub p) hqsub
    exact Subtype.ext (Prod.ext hij hlabel)
  apply no_injective_segment_endpoint_marks (P.edgeStart k) (P.edgeEnd k)
    (P.edgeStart_ne_edgeEnd k)
    (fun p : I => (T.labelledTile p.val.1).edgeStart p.val.2)
    (fun p : I => (T.labelledTile p.val.1).edgeEnd p.val.2) mark
    (fun p => (T.labelledTile p.val.1).edgeStart_ne_edgeEnd p.val.2) hsub
    (T.labelledDissection.vertexFinset : Set ℂ) T.labelledDissection.vertexFinset.finite_toSet
    ?_ ?_ hmark hends hinj
  · intro z hz hv
    exact Set.mem_iUnion.mp
      ((T.labelledDissection.boundaryEdges_cover_away_from_vertices k hv).mp hz)
  · intro p q hpq
    exact T.labelledDissection.vertexFinset.finite_toSet.subset
      (T.labelledDissection.boundaryEdges_inter_subset_vertices k hpq)

/-- An angle larger than every outer angle cannot occur at an outer corner. -/
theorem CongruentTiling.outerCornerCount_eq_zero_of_angle_gt
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N) (g : Fin 3)
    (hgt : ∀ j, P.cornerAngle j < R.cornerAngle g) : T.outerCornerCount g = 0 := by
  unfold CongruentTiling.outerCornerCount
  apply Finset.sum_eq_zero
  intro j _
  by_contra h
  have hp : 0 < T.cornerCount (P.vertex j) g := Nat.pos_of_ne_zero h
  have hcount : (1 : ℝ) ≤ T.cornerCount (P.vertex j) g := by exact_mod_cast hp
  have hterm : (T.cornerCount (P.vertex j) g : ℝ) * R.cornerAngle g ≤
      ∑ l : Fin 3, (T.cornerCount (P.vertex j) l : ℝ) * R.cornerAngle l :=
    Finset.single_le_sum
      (fun l _ => mul_nonneg (Nat.cast_nonneg _) (R.cornerAngle_pos l).le)
      (Finset.mem_univ g)
  rw [T.outer_angle_count_identity j] at hterm
  have hmul := mul_le_mul_of_nonneg_right hcount (R.cornerAngle_pos g).le
  linarith [hgt j]

theorem CongruentTiling.boundarySideCount_pos_of_obtuse_of_angle_gt
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N) (k g : Fin 3)
    (hg : Real.pi / 2 < R.cornerAngle g)
    (hgt : ∀ j, P.cornerAngle j < R.cornerAngle g) :
    0 < T.boundarySideCount k g :=
  T.boundarySideCount_pos_of_obtuse_of_outer_eq_zero k g hg
    (T.outerCornerCount_eq_zero_of_angle_gt g hgt)

theorem CongruentTiling.exists_positive_boundary_side_counts
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N) (k : Fin 3)
    (hg : Real.pi / 2 < R.angleC) (houter : T.outerCornerCount 2 = 0) :
    ∃ p q r : ℕ, 0 < r ∧
      P.sideLength k = p * R.sideLength 0 + q * R.sideLength 1 + r * R.sideLength 2 :=
  ⟨T.boundarySideCount k 0, T.boundarySideCount k 1, T.boundarySideCount k 2,
    T.boundarySideCount_pos_of_obtuse_of_outer_eq_zero k 2 hg houter,
    T.boundary_side_count_equation_three k⟩

/-- The V angle pattern supplies its positive longest-edge counts without an
assumed boundary equation or an assumed missing-corner count. -/
theorem CongruentTiling.groupOne_V_boundarySideCount_pos
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N) (k : Fin 3)
    (hrel : 3 * R.angleA + 2 * R.angleB = Real.pi)
    (hshape : PermutedTriple P.cornerAngle
      ![2 * R.angleA, R.angleB, R.angleA + R.angleB]) :
    0 < T.boundarySideCount k 2 := by
  have hC : R.angleC = 2 * R.angleA + R.angleB := by linarith [R.angle_sum]
  have hlt (i : Fin 3) :
      ![2 * R.angleA, R.angleB, R.angleA + R.angleB] i < R.angleC := by
    fin_cases i
    · change 2 * R.angleA < R.angleC
      linarith [R.angleB_pos]
    · change R.angleB < R.angleC
      linarith [R.angleA_pos]
    · change R.angleA + R.angleB < R.angleC
      linarith [R.angleA_pos]
  apply T.boundarySideCount_pos_of_obtuse_of_angle_gt k 2
  · change Real.pi / 2 < R.angleC
    linarith [R.angleA_pos]
  · obtain ⟨e, he⟩ := hshape.symm
    intro j
    change P.cornerAngle j < R.angleC
    rw [← he j]
    exact hlt (e j)

/-- The W angle pattern supplies its positive longest-edge counts directly. -/
theorem CongruentTiling.oneTwenty_W_boundarySideCount_pos
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N) (k : Fin 3)
    (hrel : 3 * R.angleA + 3 * R.angleB = Real.pi)
    (hshape : PermutedTriple P.cornerAngle
      ![R.angleA, R.angleA + R.angleB, R.angleA + 2 * R.angleB]) :
    0 < T.boundarySideCount k 2 := by
  have hC : R.angleC = 2 * R.angleA + 2 * R.angleB := by linarith [R.angle_sum]
  have hlt (i : Fin 3) :
      ![R.angleA, R.angleA + R.angleB, R.angleA + 2 * R.angleB] i < R.angleC := by
    fin_cases i
    · change R.angleA < R.angleC
      linarith [R.angleA_pos, R.angleB_pos]
    · change R.angleA + R.angleB < R.angleC
      linarith [R.angleA_pos, R.angleB_pos]
    · change R.angleA + 2 * R.angleB < R.angleC
      linarith [R.angleA_pos]
  apply T.boundarySideCount_pos_of_obtuse_of_angle_gt k 2
  · change Real.pi / 2 < R.angleC
    linarith [Real.pi_pos]
  · obtain ⟨e, he⟩ := hshape.symm
    intro j
    change P.cornerAngle j < R.angleC
    rw [← he j]
    exact hlt (e j)

end Erdos633
