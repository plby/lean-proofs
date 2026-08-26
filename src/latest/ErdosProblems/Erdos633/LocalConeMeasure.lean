import ErdosProblems.Erdos633.LocalConePartition

/-!
# Area additivity for the local sectors of a dissection

The active half-plane model has the expected interior and null boundary.
Intersecting it with a unit ball therefore gives finite local sectors whose
areas add over the incident tiles. Identifying a vertex-sector area with
half its Euclidean angle remains a separate geometric step.
-/

namespace Erdos633

open MeasureTheory
open scoped BigOperators ENNReal

theorem Triangle.barycentric_combo (P : Triangle) (x y : ℂ) (a b : ℝ) (hab : a + b = 1)
    (i : Fin 3) : P.barycentric (a • x + b • y) i =
      a * P.barycentric x i + b * P.barycentric y i := by
  have ha : a = 1 - b := by linarith
  have hp : a • x + b • y = AffineMap.lineMap x y b := by
    rw [ha, AffineMap.lineMap_apply]
    simp only [vsub_eq_sub, vadd_eq_add, sub_smul, one_smul, smul_sub]
    abel
  rw [hp, P.barycentric_lineMap, ← ha]

theorem Triangle.localConeAt_convex (P : Triangle) (z : ℂ) : Convex ℝ (P.localConeAt z) := by
  intro x hx y hy a b ha hb hab i hi
  rw [P.barycentric_combo x y a b hab]
  exact add_nonneg (mul_nonneg ha (hx i hi)) (mul_nonneg hb (hy i hi))

theorem Triangle.localConeAt_isClosed (P : Triangle) (z : ℂ) : IsClosed (P.localConeAt z) := by
  simp only [Triangle.localConeAt, Set.ofPred_forall]
  apply isClosed_iInter
  intro i
  apply isClosed_iInter
  intro _
  exact isClosed_le continuous_const (P.barycentric_continuous i)

theorem Triangle.interior_barycentric_halfspace (P : Triangle) (i : Fin 3) :
    interior {x : ℂ | 0 ≤ P.barycentric x i} = {x : ℂ | 0 < P.barycentric x i} := by
  let H := P.coordinateEquiv.symm.toContinuousAffineEquiv.toHomeomorph
  fin_cases i
  · change interior {x : ℂ | 0 ≤ P.barycentric x 0} = {x : ℂ | 0 < P.barycentric x 0}
    have hc : {x : ℂ | 0 ≤ P.barycentric x 0} = H ⁻¹' {w : ℂ | w.re + w.im ≤ 1} := by
      ext x
      change (0 ≤ 1 - (H x).re - (H x).im) ↔ (H x).re + (H x).im ≤ 1
      constructor <;> intro h <;> linarith
    have ho : {x : ℂ | 0 < P.barycentric x 0} = H ⁻¹' {w : ℂ | w.re + w.im < 1} := by
      ext x
      change (0 < 1 - (H x).re - (H x).im) ↔ (H x).re + (H x).im < 1
      constructor <;> intro h <;> linarith
    rw [hc, ho, ← H.preimage_interior, interior_re_add_im_le]
  · change interior (H ⁻¹' {w : ℂ | 0 ≤ w.re}) = H ⁻¹' {w : ℂ | 0 < w.re}
    rw [← H.preimage_interior, Complex.interior_setOfPred_le_re]
  · change interior (H ⁻¹' {w : ℂ | 0 ≤ w.im}) = H ⁻¹' {w : ℂ | 0 < w.im}
    rw [← H.preimage_interior, Complex.interior_setOfPred_le_im]

theorem Triangle.interior_localConeAt (P : Triangle) (z : ℂ) :
    interior (P.localConeAt z) = P.localOpenConeAt z := by
  simp only [Triangle.localConeAt, Triangle.localOpenConeAt, Set.ofPred_forall,
    interior_iInter_of_finite, P.interior_barycentric_halfspace]

theorem Triangle.volume_frontier_localConeAt (P : Triangle) (z : ℂ) :
    volume (frontier (P.localConeAt z)) = 0 := (P.localConeAt_convex z).addHaar_frontier volume

noncomputable def Triangle.localSector (P : Triangle) (z : ℂ) : Set ℂ :=
  P.localConeAt z ∩ Metric.ball z 1

theorem Triangle.measurableSet_localSector (P : Triangle) (z : ℂ) :
    MeasurableSet (P.localSector z) :=
  (P.localConeAt_isClosed z).measurableSet.inter measurableSet_ball

theorem Triangle.volume_localSector_lt_top (P : Triangle) (z : ℂ) :
    volume (P.localSector z) < ⊤ := by
  apply lt_of_le_of_lt (measure_mono (Set.inter_subset_right.trans Metric.ball_subset_closedBall))
  exact (isCompact_closedBall z (1 : ℝ)).measure_lt_top

theorem TriangleDissection.localSector_aedisjoint {P : Triangle} {N : ℕ}
    (T : TriangleDissection P N) (z : ℂ) {i j : Fin N} (hij : i ≠ j)
    (hi : z ∈ (T.tile i).carrier) (hj : z ∈ (T.tile j).carrier) :
    AEDisjoint volume ((T.tile i).localSector z) ((T.tile j).localSector z) := by
  have hd := T.localOpenConeAt_disjoint z hij hi hj
  rw [← Triangle.interior_localConeAt, ← Triangle.interior_localConeAt] at hd
  have hs : (T.tile i).localSector z ∩ (T.tile j).localSector z ⊆
      frontier ((T.tile i).localConeAt z) ∪ frontier ((T.tile j).localConeAt z) := by
    intro x hx
    by_cases hxi : x ∈ interior ((T.tile i).localConeAt z)
    · right
      exact ⟨subset_closure hx.2.1, fun hxj => Set.disjoint_left.mp hd hxi hxj⟩
    · left
      exact ⟨subset_closure hx.1.1, hxi⟩
  exact measure_mono_null hs (measure_union_null
    ((T.tile i).volume_frontier_localConeAt z) ((T.tile j).volume_frontier_localConeAt z))

theorem TriangleDissection.localSector_eq_union {P : Triangle} {N : ℕ}
    (T : TriangleDissection P N) (z : ℂ) (hz : z ∈ P.carrier) :
    P.localSector z = ⋃ i : {i : Fin N // z ∈ (T.tile i).carrier}, (T.tile i).localSector z := by
  ext x
  constructor
  · rintro ⟨hx, hball⟩
    rw [T.localConeAt_eq_union z hz] at hx
    obtain ⟨i, hx⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hi, hx⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hx, hball⟩
  · intro hx
    obtain ⟨i, hx⟩ := Set.mem_iUnion.mp hx
    refine ⟨?_, hx.2⟩
    rw [T.localConeAt_eq_union z hz]
    exact Set.mem_iUnion.mpr ⟨i.val, Set.mem_iUnion.mpr ⟨i.property, hx.1⟩⟩

open Classical in
theorem TriangleDissection.volume_localSector_eq_sum {P : Triangle} {N : ℕ}
    (T : TriangleDissection P N) (z : ℂ) (hz : z ∈ P.carrier) :
    volume (P.localSector z) =
      ∑ i : {i : Fin N // z ∈ (T.tile i).carrier}, volume ((T.tile i).localSector z) := by
  classical
  have hd : Pairwise fun i j : {i : Fin N // z ∈ (T.tile i).carrier} =>
      AEDisjoint volume ((T.tile i).localSector z) ((T.tile j).localSector z) := by
    intro i j hij
    exact T.localSector_aedisjoint z (fun h => hij (Subtype.ext h)) i.property j.property
  rw [T.localSector_eq_union z hz, measure_iUnion₀ hd]
  · exact tsum_fintype _
  · intro i
    exact ((T.tile i).measurableSet_localSector z).nullMeasurableSet

noncomputable def Triangle.localSectorArea (P : Triangle) (z : ℂ) : ℝ :=
  (volume (P.localSector z)).toReal

open Classical in
theorem TriangleDissection.localSectorArea_eq_sum {P : Triangle} {N : ℕ}
    (T : TriangleDissection P N) (z : ℂ) (hz : z ∈ P.carrier) :
    P.localSectorArea z =
      ∑ i : {i : Fin N // z ∈ (T.tile i).carrier}, (T.tile i).localSectorArea z := by
  classical
  unfold Triangle.localSectorArea
  rw [T.volume_localSector_eq_sum z hz, ENNReal.toReal_sum]
  intro i _
  exact ne_of_lt ((T.tile i).volume_localSector_lt_top z)

theorem TriangleDissection.localSectorArea_eq_sum_of_mem_all {P : Triangle} {N : ℕ}
    (T : TriangleDissection P N) (z : ℂ) (hz : z ∈ P.carrier)
    (hmem : ∀ i : Fin N, z ∈ (T.tile i).carrier) :
    P.localSectorArea z = ∑ i : Fin N, (T.tile i).localSectorArea z := by
  classical
  rw [T.localSectorArea_eq_sum z hz]
  exact (Finset.sum_subtype Finset.univ (fun i => by simp [hmem i])
    (fun i : Fin N => (T.tile i).localSectorArea z)).symm

open Classical in
theorem TriangleDissection.localSectorArea_eq_sum_ite {P : Triangle} {N : ℕ}
    (T : TriangleDissection P N) (z : ℂ) (hz : z ∈ P.carrier) :
    P.localSectorArea z =
      ∑ i : Fin N, if z ∈ (T.tile i).carrier then (T.tile i).localSectorArea z else 0 := by
  classical
  let s := Finset.univ.filter (fun i : Fin N => z ∈ (T.tile i).carrier)
  have hs (i : Fin N) : i ∈ s ↔ z ∈ (T.tile i).carrier := by simp [s]
  rw [T.localSectorArea_eq_sum z hz]
  calc
    _ = ∑ i ∈ s, (T.tile i).localSectorArea z :=
      (Finset.sum_subtype s hs (fun i : Fin N => (T.tile i).localSectorArea z)).symm
    _ = _ := Finset.sum_filter _ _

end Erdos633
