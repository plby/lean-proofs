import Mathlib.Tactic
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Util.IncidenceGeometry.ArcCrossingEarlierPrefix
import Util.IncidenceGeometry.PolygonalArc

open Classical
noncomputable section

lemma ArcCrossingOldPrefixDisjointTail
    (δ τ : PolygonalArc) (j : ℕ) (c d : EuclideanSpace ℝ (Fin 2))
    (hj : j + 1 < δ.vertices.length)
    (hcOpen : c ∈ openSegment ℝ δ.vertices[j] δ.vertices[j + 1])
    (hdOpen : d ∈ openSegment ℝ δ.vertices[j] c)
    (hτvertices : τ.vertices = c :: δ.vertices.drop (j + 1)) :
    Disjoint
      (ArcCrossingEarlierPrefix δ j hj ∪ segment ℝ δ.vertices[j] d)
      τ.carrier := by
  have left_piece_disjoint_right_piece :
      ∀ (u c v d : EuclideanSpace ℝ (Fin 2)),
        u ≠ v →
          c ∈ openSegment ℝ u v →
            d ∈ openSegment ℝ u c →
              Disjoint (segment ℝ u d) (segment ℝ c v) := by
    intro u c v d huv hcOpen hdOpen
    rw [Set.disjoint_left]
    intro z hzud hzcv
    have hcseg : c ∈ segment ℝ u v :=
      openSegment_subset_segment ℝ u v hcOpen
    have hdseg : d ∈ segment ℝ u c :=
      openSegment_subset_segment ℝ u c hdOpen
    have hzuc : z ∈ segment ℝ u c :=
      (convex_segment u c).segment_subset (left_mem_segment ℝ u c) hdseg hzud
    have hzuv : z ∈ segment ℝ u v :=
      (convex_segment u v).segment_subset
        (left_mem_segment ℝ u v) hcseg hzuc
    have hzc_v : dist c z + dist z v = dist c v :=
      dist_add_dist_of_mem_segment hzcv
    have huz_c : dist u z + dist z c = dist u c :=
      dist_add_dist_of_mem_segment hzuc
    have huc_v : dist u c + dist c v = dist u v :=
      dist_add_dist_of_mem_segment hcseg
    have huz_v : dist u z + dist z v = dist u v :=
      dist_add_dist_of_mem_segment hzuv
    have hzc_eq_zero : dist z c = 0 := by
      have hcz : dist c z = dist z c := dist_comm c z
      nlinarith
    have hzc : z = c := by
      exact dist_eq_zero.mp hzc_eq_zero
    subst z
    have hdu_c : dist u d + dist d c = dist u c :=
      dist_add_dist_of_mem_segment hdseg
    have hdc_pos : 0 < dist d c := by
      have hd_ne_c : d ≠ c := by
        intro h
        have hc_mem : c ∈ openSegment ℝ u c := by simpa [h] using hdOpen
        have huc : u = c :=
          (right_mem_openSegment_iff (𝕜 := ℝ) (x := u) (y := c)).1 hc_mem
        have hu_mem : u ∈ openSegment ℝ u v := by simpa [huc] using hcOpen
        have huv_eq : u = v :=
          (left_mem_openSegment_iff (𝕜 := ℝ) (x := u) (y := v)).1 hu_mem
        exact huv huv_eq
      exact dist_pos.2 hd_ne_c
    have hcu_d : dist u c + dist c d = dist u d :=
      dist_add_dist_of_mem_segment hzud
    have hcd_pos : 0 < dist c d := by simpa [dist_comm] using hdc_pos
    nlinarith
  have left_endpoint_not_right_piece :
      ∀ (u c v : EuclideanSpace ℝ (Fin 2)),
        u ≠ v → c ∈ openSegment ℝ u v → u ∉ segment ℝ c v := by
    intro u c v huv hcOpen hu
    have hcseg : c ∈ segment ℝ u v :=
      openSegment_subset_segment ℝ u v hcOpen
    have huc_v : dist u c + dist c v = dist u v :=
      dist_add_dist_of_mem_segment hcseg
    have hcu_v : dist c u + dist u v = dist c v :=
      dist_add_dist_of_mem_segment hu
    have huc_pos : 0 < dist u c := by
      have huc_ne : u ≠ c := by
        intro h
        have hu_mem : u ∈ openSegment ℝ u v := by simpa [h] using hcOpen
        have huv_eq : u = v :=
          (left_mem_openSegment_iff (𝕜 := ℝ) (x := u) (y := v)).1 hu_mem
        exact huv huv_eq
      exact dist_pos.2 huc_ne
    have hcu : dist c u = dist u c := dist_comm c u
    nlinarith
  have right_endpoint_not_left_piece :
      ∀ (u c v d : EuclideanSpace ℝ (Fin 2)),
        u ≠ v →
          c ∈ openSegment ℝ u v →
            d ∈ openSegment ℝ u c →
              v ∉ segment ℝ u d := by
    intro u c v d huv hcOpen hdOpen hv
    have hcseg : c ∈ segment ℝ u v :=
      openSegment_subset_segment ℝ u v hcOpen
    have hdseg : d ∈ segment ℝ u c :=
      openSegment_subset_segment ℝ u c hdOpen
    have hvuc : v ∈ segment ℝ u c :=
      (convex_segment u c).segment_subset (left_mem_segment ℝ u c) hdseg hv
    have huc_v : dist u c + dist c v = dist u v :=
      dist_add_dist_of_mem_segment hcseg
    have huv_c : dist u v + dist v c = dist u c :=
      dist_add_dist_of_mem_segment hvuc
    have hcv_pos : 0 < dist c v := by
      have hcv_ne : c ≠ v := by
        intro h
        have hv_mem : v ∈ openSegment ℝ u v := by simpa [h] using hcOpen
        have huv_eq : u = v :=
          (right_mem_openSegment_iff (𝕜 := ℝ) (x := u) (y := v)).1 hv_mem
        exact huv huv_eq
      exact dist_pos.2 hcv_ne
    have hvc : dist v c = dist c v := dist_comm v c
    nlinarith
  rw [Set.disjoint_left]
  intro z hzprefix hzτ
  have huv : δ.vertices[j] ≠ δ.vertices[j + 1] := by
    intro hEq
    have hidx : j = j + 1 :=
      (δ.simple_vertices.getElem_inj_iff
        (i := j) (j := j + 1)
        (hi := Nat.lt_of_succ_lt hj) (hj := hj)).1 hEq
    omega
  have hcseg : c ∈ segment ℝ δ.vertices[j] δ.vertices[j + 1] :=
    openSegment_subset_segment ℝ δ.vertices[j] δ.vertices[j + 1] hcOpen
  have hdseg : d ∈ segment ℝ δ.vertices[j] c :=
    openSegment_subset_segment ℝ δ.vertices[j] c hdOpen
  have hτ_get_succ :
      ∀ n (hn : n + 1 < τ.vertices.length),
        τ.vertices[n + 1] = δ.vertices[j + 1 + n]'(by
          have hdrop : n < (δ.vertices.drop (j + 1)).length := by
            have hn' : n + 1 < (c :: δ.vertices.drop (j + 1)).length := by
              simpa [hτvertices] using hn
            simpa using hn'
          simp [List.length_drop] at hdrop
          omega) := by
    intro n hn
    have hdrop : n < (δ.vertices.drop (j + 1)).length := by
      have hn' : n + 1 < (c :: δ.vertices.drop (j + 1)).length := by
        simpa [hτvertices] using hn
      simpa using hn'
    simpa [hτvertices] using (List.getElem_drop (xs := δ.vertices) (i := j + 1)
      (j := n) (h := hdrop))
  have hτ_get_pos :
      ∀ n (hnpos : 0 < n) (hn : n < τ.vertices.length),
        τ.vertices[n] = δ.vertices[j + n]'(by
          cases n with
          | zero => omega
          | succ q =>
              have hq : q + 1 < τ.vertices.length := by simpa using hn
              have hdrop : q < (δ.vertices.drop (j + 1)).length := by
                have hq' : q + 1 < (c :: δ.vertices.drop (j + 1)).length := by
                  simpa [hτvertices] using hq
                simpa using hq'
              simp [List.length_drop] at hdrop
              omega) := by
    intro n hnpos hn
    cases n with
    | zero => omega
    | succ q =>
        have hq : q + 1 < τ.vertices.length := by simpa using hn
        have hidx : j + 1 + q = j + (q + 1) := by omega
        simpa [hidx] using hτ_get_succ q hq
  rw [τ.carrier_eq] at hzτ
  rcases hzτ with ⟨n, hn, hzsegτ⟩
  rcases hzprefix with hprev | hlast
  · rw [ArcCrossingEarlierPrefix] at hprev
    rcases Set.mem_iUnion.mp hprev with ⟨i, hzi⟩
    have hi_len : i.1 + 1 < δ.vertices.length := by
      have hij := i.2
      omega
    by_cases hn0 : n = 0
    · subst n
      have hτ0 : τ.vertices[0] = c := by
        simpa [hτvertices]
      have hτ1 : τ.vertices[0 + 1] = δ.vertices[j + 1] := by
        simpa using hτ_get_succ 0 hn
      have hzj_tail : z ∈ segment ℝ c δ.vertices[j + 1] := by
        simpa [hτ0, hτ1] using hzsegτ
      have hzj : z ∈ segment ℝ δ.vertices[j] δ.vertices[j + 1] :=
        (convex_segment δ.vertices[j] δ.vertices[j + 1]).segment_subset
          hcseg (right_mem_segment ℝ δ.vertices[j] δ.vertices[j + 1])
          hzj_tail
      have hinter :=
        δ.segment_intersections (i := i.1) (j := j) hi_len hj i.2
      have hzint :
          z ∈ segment ℝ δ.vertices[i.1] δ.vertices[i.1 + 1] ∩
              segment ℝ δ.vertices[j] δ.vertices[j + 1] := ⟨hzi, hzj⟩
      have hzint' := hzint
      rw [hinter] at hzint'
      by_cases hadj : j = i.1 + 1
      · have hzu_i : z = δ.vertices[i.1 + 1] := by
          simpa [hadj] using hzint'
        have hzu : z = δ.vertices[j] := by
          simpa [hadj] using hzu_i
        have hzj_tail_u : δ.vertices[j] ∈ segment ℝ c δ.vertices[j + 1] := by
          simpa [hzu] using hzj_tail
        exact left_endpoint_not_right_piece
          δ.vertices[j] c δ.vertices[j + 1] huv hcOpen hzj_tail_u
      · have hzempty : z ∈ (∅ : Set (EuclideanSpace ℝ (Fin 2))) := by
          simpa [hadj] using hzint'
        exact hzempty
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
      have hτn := hτ_get_pos n hnpos (Nat.lt_of_succ_lt hn)
      have hτn1 := hτ_get_pos (n + 1) (by omega) hn
      have hm_len : j + n + 1 < δ.vertices.length := by
        rw [hτvertices] at hn
        simp [List.length_drop] at hn
        omega
      have hz_m :
          z ∈ segment ℝ δ.vertices[j + n] δ.vertices[j + n + 1] := by
        simpa [hτn, hτn1, Nat.add_assoc] using hzsegτ
      have hlt : i.1 < j + n := by omega
      have hinter :=
        δ.segment_intersections (i := i.1) (j := j + n)
          hi_len hm_len hlt
      have hzint :
          z ∈ segment ℝ δ.vertices[i.1] δ.vertices[i.1 + 1] ∩
              segment ℝ δ.vertices[j + n] δ.vertices[j + n + 1] :=
        ⟨hzi, hz_m⟩
      have hzint' := hzint
      rw [hinter] at hzint'
      have hnot_adj : j + n ≠ i.1 + 1 := by omega
      have hzempty : z ∈ (∅ : Set (EuclideanSpace ℝ (Fin 2))) := by
        simpa [hnot_adj] using hzint'
      exact hzempty
  · by_cases hn0 : n = 0
    · subst n
      have hτ0 : τ.vertices[0] = c := by
        simpa [hτvertices]
      have hτ1 : τ.vertices[0 + 1] = δ.vertices[j + 1] := by
        simpa using hτ_get_succ 0 hn
      have hz_tail : z ∈ segment ℝ c δ.vertices[j + 1] := by
        simpa [hτ0, hτ1] using hzsegτ
      exact Set.disjoint_left.mp
        (left_piece_disjoint_right_piece
          δ.vertices[j] c δ.vertices[j + 1] d huv hcOpen hdOpen) hlast hz_tail
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
      have hτn := hτ_get_pos n hnpos (Nat.lt_of_succ_lt hn)
      have hτn1 := hτ_get_pos (n + 1) (by omega) hn
      have hm_len : j + n + 1 < δ.vertices.length := by
        rw [hτvertices] at hn
        simp [List.length_drop] at hn
        omega
      have hz_m :
          z ∈ segment ℝ δ.vertices[j + n] δ.vertices[j + n + 1] := by
        simpa [hτn, hτn1, Nat.add_assoc] using hzsegτ
      have hz_j : z ∈ segment ℝ δ.vertices[j] δ.vertices[j + 1] := by
        have hz_uc : z ∈ segment ℝ δ.vertices[j] c :=
          (convex_segment δ.vertices[j] c).segment_subset
            (left_mem_segment ℝ δ.vertices[j] c) hdseg hlast
        exact
          (convex_segment δ.vertices[j] δ.vertices[j + 1]).segment_subset
            (left_mem_segment ℝ δ.vertices[j] δ.vertices[j + 1]) hcseg hz_uc
      have hlt : j < j + n := by omega
      have hinter :=
        δ.segment_intersections (i := j) (j := j + n) hj hm_len hlt
      have hzint :
          z ∈ segment ℝ δ.vertices[j] δ.vertices[j + 1] ∩
              segment ℝ δ.vertices[j + n] δ.vertices[j + n + 1] :=
        ⟨hz_j, hz_m⟩
      have hzint' := hzint
      rw [hinter] at hzint'
      by_cases hadj : j + n = j + 1
      · have hz_m_eq : z = δ.vertices[j + n] := by
          simpa [hadj] using hzint'
        have hzv : z = δ.vertices[j + 1] := by
          have hn_eq : n = 1 := by omega
          simpa [hn_eq] using hz_m_eq
        have hlast_v : δ.vertices[j + 1] ∈ segment ℝ δ.vertices[j] d := by
          simpa [hzv] using hlast
        exact right_endpoint_not_left_piece
          δ.vertices[j] c δ.vertices[j + 1] d huv hcOpen hdOpen hlast_v
      · have hzempty : z ∈ (∅ : Set (EuclideanSpace ℝ (Fin 2))) := by
          have hn_ne_one : n ≠ 1 := by omega
          simpa [hn_ne_one] using hzint'
        exact hzempty

