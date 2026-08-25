import Util.IncidenceGeometry.PolygonalArcAdjacentOutwardDirectionsNotSameRay
import Util.IncidenceGeometry.PolygonalArcInteriorRayPair

open Classical
noncomputable section

lemma PolygonalArcInteriorRayPairExists
    (gamma : PolygonalArc) (p : EuclideanSpace ℝ (Fin 2))
    (hp : p ∈ gamma.relativeInterior) :
    Nonempty (PolygonalArcInteriorRayPair gamma p) := by
  rw [gamma.relativeInterior_eq] at hp
  rcases hp with ⟨hpCarrier, hpEnds⟩
  have hpBoth : p ≠ gamma.source ∧ p ≠ gamma.target := by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using hpEnds
  have hpSource : p ≠ gamma.source := by
    exact hpBoth.1
  have hpTarget : p ≠ gamma.target := by
    exact hpBoth.2
  by_cases hpListed : p ∈ gamma.vertices
  · rcases List.getElem_of_mem hpListed with ⟨k, hk, hkp⟩
    have hsource0 : gamma.vertices[0] = gamma.source := by
      have hhead := gamma.source_eq_head
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hhead
      exact Option.some.inj hhead
    have hkpos : 0 < k := by
      by_contra h
      have hk0 : k = 0 := by omega
      apply hpSource
      have hksource : gamma.vertices[k] = gamma.source := by
        simpa [hk0] using hsource0
      exact hkp.symm.trans hksource
    have htargetLast :
        gamma.vertices[gamma.vertices.length - 1] = gamma.target := by
      have hlast := gamma.target_eq_last
      rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hlast
      exact Option.some.inj hlast
    have hknext : k + 1 < gamma.vertices.length := by
      by_contra h
      have hklast : k = gamma.vertices.length - 1 := by omega
      apply hpTarget
      have hktarget : gamma.vertices[k] = gamma.target := by
        simpa [hklast] using htargetLast
      exact hkp.symm.trans hktarget
    have hprev : (k - 1) + 1 < gamma.vertices.length := by
      simpa [Nat.sub_add_cancel (Nat.succ_le_of_lt hkpos)] using
        (Nat.lt_of_succ_lt hknext)
    let d1 := gamma.vertices[k + 1] - gamma.vertices[k]
    let d2 := gamma.vertices[k - 1] - gamma.vertices[k]
    have hd1 : d1 ≠ 0 := by
      dsimp [d1]
      exact sub_ne_zero.mpr (by
        intro h
        have hidx := (gamma.simple_vertices.getElem_inj_iff
          (i := k + 1) (j := k) (hi := hknext)
          (hj := Nat.lt_of_succ_lt hknext)).1 h
        omega)
    have hd2 : d2 ≠ 0 := by
      dsimp [d2]
      exact sub_ne_zero.mpr (by
        intro h
        have hidx := (gamma.simple_vertices.getElem_inj_iff
          (i := k - 1) (j := k) (hi := Nat.lt_of_succ_lt hprev)
          (hj := Nat.lt_of_succ_lt hknext)).1 h
        omega)
    refine ⟨{
      firstIndex := k
      secondIndex := k - 1
      firstIndex_valid := hknext
      secondIndex_valid := hprev
      firstVector := d1
      secondVector := d2
      firstVector_ne_zero := hd1
      secondVector_ne_zero := hd2
      firstScale := 1
      secondScale := -1
      firstScale_ne_zero := one_ne_zero
      secondScale_ne_zero := neg_ne_zero.mpr one_ne_zero
      firstVector_eq := by simp [d1]
      secondVector_eq := by
        dsimp [d2]
        have hkprev : k - 1 + 1 = k :=
          Nat.sub_add_cancel (Nat.succ_le_of_lt hkpos)
        simp [hkprev, neg_sub]
      firstRay_subset := by
        intro z hz
        simpa [d1, hkp, add_sub_cancel_left] using hz
      secondRay_subset := by
        intro z hz
        have hz' : z ∈ segment ℝ gamma.vertices[k] gamma.vertices[k - 1] := by
          simpa [d2, hkp, add_sub_cancel_left] using hz
        have hkprev : k - 1 + 1 = k :=
          Nat.sub_add_cancel (Nat.succ_le_of_lt hkpos)
        simpa [hkprev, segment_symm] using hz'
      rays_not_same_positive := by
        simpa [d1, d2] using
          (PolygonalArcAdjacentOutwardDirectionsNotSameRay gamma hkpos hknext).1 }⟩
  · rw [gamma.carrier_eq] at hpCarrier
    rcases hpCarrier with ⟨i, hi, hpseg⟩
    have hleft : gamma.vertices[i] ≠ p := by
      intro h
      apply hpListed
      rw [← h]
      exact List.getElem_mem (by omega)
    have hright : gamma.vertices[i + 1] ≠ p := by
      intro h
      apply hpListed
      rw [← h]
      exact List.getElem_mem hi
    have hpOpen :
        p ∈ openSegment ℝ gamma.vertices[i] gamma.vertices[i + 1] :=
      mem_openSegment_of_ne_left_right hleft hright hpseg
    rw [openSegment_eq_image_lineMap] at hpOpen
    rcases hpOpen with ⟨t, ht, hpt⟩
    let dir := gamma.vertices[i + 1] - gamma.vertices[i]
    let d1 := gamma.vertices[i + 1] - p
    let d2 := gamma.vertices[i] - p
    have hdir : dir ≠ 0 := by
      dsimp [dir]
      exact sub_ne_zero.mpr (by
        intro h
        have hidx := (gamma.simple_vertices.getElem_inj_iff
          (i := i + 1) (j := i) (hi := hi)
          (hj := Nat.lt_of_succ_lt hi)).1 h
        omega)
    have hd1eq : d1 = (1 - t) • dir := by
      dsimp [d1, dir]
      rw [← hpt]
      simp only [AffineMap.lineMap_apply_module]
      module
    have hd2eq : d2 = (-t) • dir := by
      dsimp [d2, dir]
      rw [← hpt]
      simp only [AffineMap.lineMap_apply_module]
      module
    have hd1 : d1 ≠ 0 := by
      rw [hd1eq]
      exact smul_ne_zero (by linarith [ht.2]) hdir
    have hd2 : d2 ≠ 0 := by
      rw [hd2eq]
      exact smul_ne_zero (by linarith [ht.1]) hdir
    refine ⟨{
      firstIndex := i
      secondIndex := i
      firstIndex_valid := hi
      secondIndex_valid := hi
      firstVector := d1
      secondVector := d2
      firstVector_ne_zero := hd1
      secondVector_ne_zero := hd2
      firstScale := 1 - t
      secondScale := -t
      firstScale_ne_zero := by linarith [ht.2]
      secondScale_ne_zero := by linarith [ht.1]
      firstVector_eq := hd1eq
      secondVector_eq := hd2eq
      firstRay_subset := by
        intro z hz
        have hpseg' : p ∈ segment ℝ gamma.vertices[i] gamma.vertices[i + 1] :=
          openSegment_subset_segment ℝ _ _ (by
            rw [openSegment_eq_image_lineMap]
            exact ⟨t, ht, hpt⟩)
        have hrightmem := right_mem_segment ℝ gamma.vertices[i] gamma.vertices[i + 1]
        have hz' : z ∈ segment ℝ p gamma.vertices[i + 1] := by
          simpa [d1, add_sub_cancel_left] using hz
        exact (convex_segment _ _).segment_subset hpseg' hrightmem hz'
      secondRay_subset := by
        intro z hz
        have hpseg' : p ∈ segment ℝ gamma.vertices[i] gamma.vertices[i + 1] :=
          openSegment_subset_segment ℝ _ _ (by
            rw [openSegment_eq_image_lineMap]
            exact ⟨t, ht, hpt⟩)
        have hleftmem := left_mem_segment ℝ gamma.vertices[i] gamma.vertices[i + 1]
        have hz' : z ∈ segment ℝ p gamma.vertices[i] := by
          simpa [d2, add_sub_cancel_left] using hz
        exact (convex_segment _ _).segment_subset hpseg' hleftmem hz'
      rays_not_same_positive := by
        rintro ⟨a, ha, hsame⟩
        have hcoeff : -t = a * (1 - t) := by
          apply smul_left_injective ℝ hdir
          calc
            (-t) • dir = d2 := hd2eq.symm
            _ = a • d1 := hsame
            _ = (a * (1 - t)) • dir := by rw [hd1eq, smul_smul]
        nlinarith [ht.1, ht.2] }⟩
