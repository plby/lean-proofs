import ErdosProblems.Erdos633.AreaBoundary

/-!
# Boundary propagation through an actual dissection

Tile weights that agree across shared open edges have a weighted boundary
identity. Integrating the determinant density gives a weighted area identity.
Nonnegative weights vanish if their boundary values vanish. Consequently a
property holding at all boundary tiles and propagating across shared open
edges holds at every tile, without an assumed adjacency-connectivity theorem.
-/

namespace Erdos633

open MeasureTheory
open scoped BigOperators ENNReal

theorem TriangleDissection.sum_weighted_boundaryDensity_eq_incident
    {P : Triangle} {N : ℕ} (T : TriangleDissection P N)
    (w : Fin N → ℝ) (φ : ℂ → ℝ) (z : ℂ) :
    (∑ i : Fin N, w i * (T.tile i).boundaryDensity φ z) =
      ∑ i ∈ T.incidentTiles z, w i * (T.tile i).boundaryDensity φ z := by
  classical
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _ hi
  rw [(T.tile i).boundaryDensity_zero_of_not_carrier φ
    (fun h => hi ((T.mem_incidentTiles z i).mpr h)), mul_zero]

theorem TriangleDissection.weighted_boundaryDensity_eq_sum_of_not_vertex
    {P : Triangle} {N : ℕ} (T : TriangleDissection P N)
    (w : Fin N → ℝ) (wP : ℝ)
    (houter : ∀ i k l, (T.tile i).edge l ⊆ P.edge k → w i = wP)
    (hshared : ∀ i j : Fin N, i ≠ j → ∀ k l z,
      z ∈ (T.tile i).openEdge k → z ∈ (T.tile j).openEdge l → w i = w j)
    (φ : ℂ → ℝ) (hodd : ∀ u, φ (-u) = -φ u) {z : ℂ}
    (hv : z ∉ T.vertexFinset) :
    wP * P.boundaryDensity φ z = ∑ i : Fin N, w i * (T.tile i).boundaryDensity φ z := by
  classical
  by_cases hzP : z ∈ P.carrier
  · rw [T.sum_weighted_boundaryDensity_eq_incident]
    by_cases hint : z ∈ interior P.carrier
    · rw [P.boundaryDensity_zero_of_interior φ hint, mul_zero]
      symm
      by_cases he : ∃ i : Fin N, ∃ k : Fin 3, z ∈ (T.tile i).edge k
      · obtain ⟨i₀, k₀, hz⟩ := he
        obtain ⟨i, j, hij, hset⟩ := Finset.card_eq_two.mp
          (T.incidentTiles_card_eq_two_of_interior_edge hv hint i₀ k₀ hz)
        have hi : i ∈ T.incidentTiles z := by rw [hset]; simp
        have hj : j ∈ T.incidentTiles z := by rw [hset]; simp
        obtain ⟨k, hk, _⟩ := T.incident_tile_has_open_edge hv i₀ k₀ hz hi
        obtain ⟨l, hl, _⟩ := T.incident_tile_has_open_edge hv i₀ k₀ hz hj
        rw [hset, Finset.sum_pair hij,
          (T.tile i).boundaryDensity_openEdge φ k hk,
          (T.tile j).boundaryDensity_openEdge φ l hl,
          hshared i j hij k l z hk hl,
          T.shared_open_edges_unitVector_neg hij k l hk hl, hodd]
        ring
      · apply Finset.sum_eq_zero
        intro i _
        rw [(T.tile i).boundaryDensity_zero_of_no_edges φ
          (fun k hk => he ⟨i, k, hk⟩), mul_zero]
    · obtain ⟨k, hk⟩ := P.boundary_nonvertex_mem_openEdge z hzP hint
        (T.not_outer_vertex_of_not_vertexFinset hv)
      obtain ⟨i, hset⟩ := Finset.card_eq_one.mp
        (T.incidentTiles_card_eq_one_of_boundary hv hzP hint)
      have hi : z ∈ (T.tile i).carrier := (T.mem_incidentTiles z i).mp (by rw [hset]; simp)
      have hni : z ∉ interior (T.tile i).carrier :=
        fun h => hint (interior_mono (T.tile_subset i) h)
      obtain ⟨l, hl⟩ := (T.tile i).boundary_nonvertex_mem_openEdge z hi hni
        (T.not_tile_vertex_of_not_vertexFinset hv i)
      have hsub : (T.tile i).edge l ⊆ P.edge k :=
        P.edge_contains_segment_of_open_point k
          (T.tile_subset i ((T.tile i).edgeStart_mem_carrier l))
          (T.tile_subset i ((T.tile i).edgeEnd_mem_carrier l))
          (P.openEdge_subset_edge k hk) hl
      rw [hset, Finset.sum_singleton, P.boundaryDensity_openEdge φ k hk,
        (T.tile i).boundaryDensity_openEdge φ l hl, houter i k l hsub,
        P.unitEdgeVector_eq_of_edge_subset (T.tile i) k l (T.tile_subset i) hsub]
  · rw [P.boundaryDensity_zero_of_not_carrier φ hzP, mul_zero]
    symm
    apply Finset.sum_eq_zero
    intro i _
    rw [(T.tile i).boundaryDensity_zero_of_not_carrier φ
      (fun h => hzP (T.tile_subset i h)), mul_zero]

theorem TriangleDissection.weighted_area_identity
    {P : Triangle} {N : ℕ} (T : TriangleDissection P N)
    (w : Fin N → ℝ) (wP : ℝ)
    (houter : ∀ i k l, (T.tile i).edge l ⊆ P.edge k → w i = wP)
    (hshared : ∀ i j : Fin N, i ≠ j → ∀ k l z,
      z ∈ (T.tile i).openEdge k → z ∈ (T.tile j).openEdge l → w i = w j) :
    wP * (P.orientationSign * orientedDoubleArea P.a P.b P.c) =
      ∑ i : Fin N, w i * ((T.tile i).orientationSign *
        orientedDoubleArea (T.tile i).a (T.tile i).b (T.tile i).c) := by
  have hae : (fun z => wP * P.areaBoundaryDensity z) =ᵐ[(μH[1] : Measure ℂ)]
      fun z => ∑ i : Fin N, w i * (T.tile i).areaBoundaryDensity z := by
    let : NullSingletonClass (μH[1] : Measure ℂ) :=
      Measure.nullSingletonClass_hausdorff ℂ (by norm_num)
    have hv := T.vertexFinset.finite_toSet.countable.ae_notMem (μH[1] : Measure ℂ)
    filter_upwards [hv] with z hz
    simp_rw [Triangle.areaBoundaryDensity_eq]
    exact T.weighted_boundaryDensity_eq_sum_of_not_vertex w wP houter hshared
      (planeDet z) (planeDet_neg_right z) hz
  have h := integral_congr_ae hae
  rw [integral_const_mul,
    integral_finsetSum Finset.univ
      (fun i _ => (T.tile i).integrable_areaBoundaryDensity.const_mul (w i))] at h
  simp_rw [integral_const_mul, Triangle.integral_areaBoundaryDensity] at h
  exact h

theorem TriangleDissection.nonnegative_weights_zero_of_boundary
    {P : Triangle} {N : ℕ} (T : TriangleDissection P N)
    (w : Fin N → ℝ) (hw : ∀ i, 0 ≤ w i)
    (houter : ∀ i k l, (T.tile i).edge l ⊆ P.edge k → w i = 0)
    (hshared : ∀ i j : Fin N, i ≠ j → ∀ k l z,
      z ∈ (T.tile i).openEdge k → z ∈ (T.tile j).openEdge l → w i = w j) :
    ∀ i, w i = 0 := by
  have hsum := (T.weighted_area_identity w 0 houter hshared).symm
  rw [zero_mul] at hsum
  intro i
  have hle : w i * ((T.tile i).orientationSign *
      orientedDoubleArea (T.tile i).a (T.tile i).b (T.tile i).c) ≤ 0 := by
    calc
      _ ≤ ∑ j : Fin N, w j * ((T.tile j).orientationSign *
          orientedDoubleArea (T.tile j).a (T.tile j).b (T.tile j).c) :=
        Finset.single_le_sum (fun j _ => mul_nonneg (hw j) (T.tile j).orientationSign_area_pos.le)
          (Finset.mem_univ i)
      _ = 0 := hsum
  have harea := (T.tile i).orientationSign_area_pos
  have hwi := hw i
  nlinarith

theorem TriangleDissection.property_of_boundary_and_shared
    {P : Triangle} {N : ℕ} (T : TriangleDissection P N) (p : Fin N → Prop)
    (houter : ∀ i k l, (T.tile i).edge l ⊆ P.edge k → p i)
    (hshared : ∀ i j : Fin N, i ≠ j → ∀ k l z,
      z ∈ (T.tile i).openEdge k → z ∈ (T.tile j).openEdge l → p i → p j) :
    ∀ i, p i := by
  classical
  let w : Fin N → ℝ := fun i => if p i then 0 else 1
  have hw : ∀ i, 0 ≤ w i := by intro i; dsimp [w]; split_ifs <;> norm_num
  have hb : ∀ i k l, (T.tile i).edge l ⊆ P.edge k → w i = 0 := by
    intro i k l hi
    simp only [w, if_pos (houter i k l hi)]
  have hs : ∀ i j : Fin N, i ≠ j → ∀ k l z,
      z ∈ (T.tile i).openEdge k → z ∈ (T.tile j).openEdge l → w i = w j := by
    intro i j hij k l z hi hj
    have hp : p i ↔ p j := ⟨hshared i j hij k l z hi hj,
      hshared j i hij.symm l k z hj hi⟩
    simp only [w, hp]
  have hz := T.nonnegative_weights_zero_of_boundary w hw hb hs
  intro i
  by_contra hi
  have h := hz i
  simp only [w, if_neg hi] at h
  norm_num at h

end Erdos633
