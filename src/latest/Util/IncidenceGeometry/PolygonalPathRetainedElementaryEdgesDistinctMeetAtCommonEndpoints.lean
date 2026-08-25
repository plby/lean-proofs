import Util.IncidenceGeometry.PolygonalPathRetainedElementaryEdges
import Mathlib.Tactic

open Classical
noncomputable section


lemma PolygonalPathRetainedElementaryEdgesDistinctMeetAtCommonEndpoints
    (γ : PolygonalPath)
    (cutVertices : Finset (EuclideanSpace ℝ (Fin 2)))
    (hcut_finite_pair :
      ∀ i j : ℕ,
        (hi : i + 1 < γ.vertices.length) →
          (hj : j + 1 < γ.vertices.length) →
            Set.Finite
              (segment ℝ γ.vertices[i] γ.vertices[i + 1] ∩
                segment ℝ γ.vertices[j] γ.vertices[j + 1]) →
              ∀ p : EuclideanSpace ℝ (Fin 2),
                p ∈ segment ℝ γ.vertices[i] γ.vertices[i + 1] →
                  p ∈ segment ℝ γ.vertices[j] γ.vertices[j + 1] →
                    p ∈ cutVertices)
    (retainedEdgesData : PolygonalPathRetainedElementaryEdges γ cutVertices) :
    ∀ e f : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
      e ∈ retainedEdgesData.retainedEdges →
        f ∈ retainedEdgesData.retainedEdges →
          e ≠ f →
            segment ℝ e.1 e.2 ∩ segment ℝ f.1 f.2 =
              ({e.1, e.2} : Set (EuclideanSpace ℝ (Fin 2))) ∩
                ({f.1, f.2} : Set (EuclideanSpace ℝ (Fin 2))) := by
  classical
  have retained_no_cut_open :
      ∀ e : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
        e ∈ retainedEdgesData.retainedEdges →
          ∀ v : EuclideanSpace ℝ (Fin 2),
            v ∈ cutVertices → v ∉ openSegment ℝ e.1 e.2 :=
    by
      intro e he v hv
      rcases retainedEdgesData.retained_edge_data e he with
        ⟨_hsrc, _htgt, _hne, i, hseg, k, hk, horient, _hsub, _hcarrier⟩
      rcases horient with hdir | hrev
      · subst e
        exact retainedEdgesData.elementary_no_cut_open i hseg k hk v hv
      · subst e
        simpa [openSegment_symm] using
          (retainedEdgesData.elementary_no_cut_open i hseg k hk v hv)
  have exact_of_open_disjoint :
      ∀ e f : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
        Disjoint (openSegment ℝ e.1 e.2) (openSegment ℝ f.1 f.2) →
        e.1 ∉ openSegment ℝ f.1 f.2 →
        e.2 ∉ openSegment ℝ f.1 f.2 →
        f.1 ∉ openSegment ℝ e.1 e.2 →
        f.2 ∉ openSegment ℝ e.1 e.2 →
          segment ℝ e.1 e.2 ∩ segment ℝ f.1 f.2 =
            ({e.1, e.2} : Set (EuclideanSpace ℝ (Fin 2))) ∩
              ({f.1, f.2} : Set (EuclideanSpace ℝ (Fin 2))) := by
    intro e f hopen he1_not he2_not hf1_not hf2_not
    ext x
    constructor
    · intro hx
      constructor
      · by_contra hxend
        have hxne1 : e.1 ≠ x := by
          intro h
          exact hxend (by simp [h])
        have hxne2 : e.2 ≠ x := by
          intro h
          exact hxend (by simp [h])
        have hxopen_e : x ∈ openSegment ℝ e.1 e.2 :=
          mem_openSegment_of_ne_left_right hxne1 hxne2 hx.1
        by_cases hxf1 : f.1 = x
        · exact hf1_not (by simpa [hxf1] using hxopen_e)
        by_cases hxf2 : f.2 = x
        · exact hf2_not (by simpa [hxf2] using hxopen_e)
        have hxopen_f : x ∈ openSegment ℝ f.1 f.2 :=
          mem_openSegment_of_ne_left_right hxf1 hxf2 hx.2
        exact (Set.disjoint_left.mp hopen) hxopen_e hxopen_f
      · by_contra hxend
        have hxne1 : f.1 ≠ x := by
          intro h
          exact hxend (by simp [h])
        have hxne2 : f.2 ≠ x := by
          intro h
          exact hxend (by simp [h])
        have hxopen_f : x ∈ openSegment ℝ f.1 f.2 :=
          mem_openSegment_of_ne_left_right hxne1 hxne2 hx.2
        by_cases hxe1 : e.1 = x
        · exact he1_not (by simpa [hxe1] using hxopen_f)
        by_cases hxe2 : e.2 = x
        · exact he2_not (by simpa [hxe2] using hxopen_f)
        have hxopen_e : x ∈ openSegment ℝ e.1 e.2 :=
          mem_openSegment_of_ne_left_right hxe1 hxe2 hx.1
        exact (Set.disjoint_left.mp hopen) hxopen_e hxopen_f
    · intro hx
      constructor
      · rcases hx.1 with hx1 | hx2
        · subst x
          exact left_mem_segment ℝ e.1 e.2
        · subst x
          exact right_mem_segment ℝ e.1 e.2
      · rcases hx.2 with hx1 | hx2
        · subst x
          exact left_mem_segment ℝ f.1 f.2
        · subst x
          exact right_mem_segment ℝ f.1 f.2
  have real_sym2_of_open_overlap_no_endpoints :
      ∀ {a b c d x : ℝ}, a ≠ b → c ≠ d →
        x ∈ openSegment ℝ a b →
        x ∈ openSegment ℝ c d →
        c ∉ openSegment ℝ a b →
        d ∉ openSegment ℝ a b →
        a ∉ openSegment ℝ c d →
        b ∉ openSegment ℝ c d →
          Sym2.mk a b = Sym2.mk c d := by
    intro a b c d x hab hcd hxab hxcd hc_not hd_not ha_not hb_not
    rw [openSegment_eq_Ioo' hab] at hxab hc_not hd_not
    rw [openSegment_eq_Ioo' hcd] at hxcd ha_not hb_not
    have hmin_cd_le_min_ab : min c d ≤ min a b := by
      by_contra hnot
      have hlt : min a b < min c d := lt_of_not_ge hnot
      have hmem : min c d ∈ Set.Ioo (min a b) (max a b) :=
        ⟨hlt, lt_trans hxcd.1 hxab.2⟩
      by_cases hcd_le : c ≤ d
      · have hcmin : min c d = c := min_eq_left hcd_le
        exact hc_not (by simpa [hcmin] using hmem)
      · have hdmin : min c d = d := min_eq_right (le_of_lt (lt_of_not_ge hcd_le))
        exact hd_not (by simpa [hdmin] using hmem)
    have hmin_ab_le_min_cd : min a b ≤ min c d := by
      by_contra hnot
      have hlt : min c d < min a b := lt_of_not_ge hnot
      have hmem : min a b ∈ Set.Ioo (min c d) (max c d) :=
        ⟨hlt, lt_trans hxab.1 hxcd.2⟩
      by_cases hab_le : a ≤ b
      · have hamin : min a b = a := min_eq_left hab_le
        exact ha_not (by simpa [hamin] using hmem)
      · have hbmin : min a b = b := min_eq_right (le_of_lt (lt_of_not_ge hab_le))
        exact hb_not (by simpa [hbmin] using hmem)
    have hmax_ab_le_max_cd : max a b ≤ max c d := by
      by_contra hnot
      have hlt : max c d < max a b := lt_of_not_ge hnot
      have hmem : max c d ∈ Set.Ioo (min a b) (max a b) :=
        ⟨lt_trans hxab.1 hxcd.2, hlt⟩
      by_cases hcd_le : c ≤ d
      · have hdmax : max c d = d := max_eq_right hcd_le
        exact hd_not (by simpa [hdmax] using hmem)
      · have hcmax : max c d = c := max_eq_left (le_of_lt (lt_of_not_ge hcd_le))
        exact hc_not (by simpa [hcmax] using hmem)
    have hmax_cd_le_max_ab : max c d ≤ max a b := by
      by_contra hnot
      have hlt : max a b < max c d := lt_of_not_ge hnot
      have hmem : max a b ∈ Set.Ioo (min c d) (max c d) :=
        ⟨lt_trans hxcd.1 hxab.2, hlt⟩
      by_cases hab_le : a ≤ b
      · have hbmax : max a b = b := max_eq_right hab_le
        exact hb_not (by simpa [hbmax] using hmem)
      · have hamax : max a b = a := max_eq_left (le_of_lt (lt_of_not_ge hab_le))
        exact ha_not (by simpa [hamax] using hmem)
    have hmin : min a b = min c d := le_antisymm hmin_ab_le_min_cd hmin_cd_le_min_ab
    have hmax : max a b = max c d := le_antisymm hmax_ab_le_max_cd hmax_cd_le_max_ab
    have hab_cases :
        (a = min a b ∧ b = max a b) ∨ (a = max a b ∧ b = min a b) := by
      by_cases hle : a ≤ b
      · exact Or.inl ⟨(min_eq_left hle).symm, (max_eq_right hle).symm⟩
      · have hle' : b ≤ a := le_of_lt (lt_of_not_ge hle)
        exact Or.inr ⟨(max_eq_left hle').symm, (min_eq_right hle').symm⟩
    have hcd_cases :
        (c = min c d ∧ d = max c d) ∨ (c = max c d ∧ d = min c d) := by
      by_cases hle : c ≤ d
      · exact Or.inl ⟨(min_eq_left hle).symm, (max_eq_right hle).symm⟩
      · have hle' : d ≤ c := le_of_lt (lt_of_not_ge hle)
        exact Or.inr ⟨(max_eq_left hle').symm, (min_eq_right hle').symm⟩
    apply (Sym2.eq_iff).mpr
    rcases hab_cases with hab_order | hab_order <;>
      rcases hcd_cases with hcd_order | hcd_order
    · left
      constructor <;> linarith
    · right
      constructor <;> linarith
    · right
      constructor <;> linarith
    · left
      constructor <;> linarith
  have line_sym2_of_open_overlap_no_endpoints :
      ∀ (A B : EuclideanSpace ℝ (Fin 2)) (hAB : A ≠ B)
        (u v r s : ℝ),
          AffineMap.lineMap A B u ≠ AffineMap.lineMap A B v →
          AffineMap.lineMap A B r ≠ AffineMap.lineMap A B s →
          ∀ {x : EuclideanSpace ℝ (Fin 2)},
            x ∈ openSegment ℝ
              (AffineMap.lineMap A B u) (AffineMap.lineMap A B v) →
            x ∈ openSegment ℝ
              (AffineMap.lineMap A B r) (AffineMap.lineMap A B s) →
            AffineMap.lineMap A B r ∉ openSegment ℝ
              (AffineMap.lineMap A B u) (AffineMap.lineMap A B v) →
            AffineMap.lineMap A B s ∉ openSegment ℝ
              (AffineMap.lineMap A B u) (AffineMap.lineMap A B v) →
            AffineMap.lineMap A B u ∉ openSegment ℝ
              (AffineMap.lineMap A B r) (AffineMap.lineMap A B s) →
            AffineMap.lineMap A B v ∉ openSegment ℝ
              (AffineMap.lineMap A B r) (AffineMap.lineMap A B s) →
              Sym2.mk (AffineMap.lineMap A B u) (AffineMap.lineMap A B v) =
                Sym2.mk (AffineMap.lineMap A B r) (AffineMap.lineMap A B s) := by
    intro A B hAB u v r s hne_uv hne_rs x hxuv hxrs hr_not hs_not hu_not hv_not
    let F : ℝ →ᵃ[ℝ] EuclideanSpace ℝ (Fin 2) := AffineMap.lineMap A B
    have hF : Function.Injective F := AffineMap.lineMap_injective (k := ℝ) hAB
    have huv : u ≠ v := by
      intro huv
      exact hne_uv (by simp [huv])
    have hrs : r ≠ s := by
      intro hrs
      exact hne_rs (by simp [hrs])
    have hxuv' : x ∈ F '' openSegment ℝ u v := by
      rw [image_openSegment ℝ F u v]
      simpa [F] using hxuv
    have hxrs' : x ∈ F '' openSegment ℝ r s := by
      rw [image_openSegment ℝ F r s]
      simpa [F] using hxrs
    rcases hxuv' with ⟨t, htuv, rfl⟩
    rcases hxrs' with ⟨w, htrs, htw⟩
    have htw_eq : w = t := hF htw
    subst w
    have hr_not_real : r ∉ openSegment ℝ u v := by
      intro hr
      exact hr_not (by
        rw [← image_openSegment ℝ F u v]
        exact ⟨r, hr, rfl⟩)
    have hs_not_real : s ∉ openSegment ℝ u v := by
      intro hs
      exact hs_not (by
        rw [← image_openSegment ℝ F u v]
        exact ⟨s, hs, rfl⟩)
    have hu_not_real : u ∉ openSegment ℝ r s := by
      intro hu
      exact hu_not (by
        rw [← image_openSegment ℝ F r s]
        exact ⟨u, hu, rfl⟩)
    have hv_not_real : v ∉ openSegment ℝ r s := by
      intro hv
      exact hv_not (by
        rw [← image_openSegment ℝ F r s]
        exact ⟨v, hv, rfl⟩)
    have hsym_real : Sym2.mk u v = Sym2.mk r s :=
      real_sym2_of_open_overlap_no_endpoints huv hrs htuv htrs
        hr_not_real hs_not_real hu_not_real hv_not_real
    apply (Sym2.eq_iff).mpr
    rcases (Sym2.eq_iff).mp hsym_real with hsame | hswap
    · exact Or.inl ⟨by simp [hsame.1], by simp [hsame.2]⟩
    · exact Or.inr ⟨by simp [hswap.1], by simp [hswap.2]⟩
  have open_disjoint :
      ∀ e f : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
        e ∈ retainedEdgesData.retainedEdges →
          f ∈ retainedEdgesData.retainedEdges →
            e ≠ f →
              Disjoint (openSegment ℝ e.1 e.2) (openSegment ℝ f.1 f.2) := by
    intro e f he hf hef
    rw [Set.disjoint_left]
    intro x hxe hxf
    rcases retainedEdgesData.retained_edge_data e he with
      ⟨hesrc, hetgt, hene, i, hiseg, k, hk, heorient, hesub, _hecarrier⟩
    rcases retainedEdgesData.retained_edge_data f hf with
      ⟨hfsrc, hftgt, hfne, j, _hjseg, l, hl, hforient, hfsub, _hfcarrier⟩
    have hxe_parent : x ∈ segment ℝ γ.vertices[i.1] γ.vertices[i.1 + 1] :=
      hesub (openSegment_subset_segment ℝ e.1 e.2 hxe)
    have hxf_parent : x ∈ segment ℝ γ.vertices[j.1] γ.vertices[j.1 + 1] :=
      hfsub (openSegment_subset_segment ℝ f.1 f.2 hxf)
    by_cases hfin : Set.Finite
        (segment ℝ γ.vertices[i.1] γ.vertices[i.1 + 1] ∩
          segment ℝ γ.vertices[j.1] γ.vertices[j.1 + 1])
    · have hxcut : x ∈ cutVertices :=
        hcut_finite_pair i.1 j.1 (by omega) (by omega) hfin x hxe_parent hxf_parent
      exact retained_no_cut_open e he x hxcut hxe
    · let E := EuclideanSpace ℝ (Fin 2)
      let Ai : E := γ.vertices[i.1]'(by omega)
      let Bi : E := γ.vertices[i.1 + 1]'(by omega)
      let Aj : E := γ.vertices[j.1]'(by omega)
      let Bj : E := γ.vertices[j.1 + 1]'(by omega)
      have segment_subset_line :
          ∀ A B : E, segment ℝ A B ⊆ (line[ℝ, A, B] : AffineSubspace ℝ E) := by
        intro A B y hy
        rw [segment_eq_image_lineMap] at hy
        rcases hy with ⟨t, _ht, rfl⟩
        exact AffineMap.lineMap_mem_affineSpan_pair t A B
      have hoverlap_exists :
          ∃ p q : E, p ≠ q ∧
            segment ℝ p q ⊆
              segment ℝ γ.vertices[i.1] γ.vertices[i.1 + 1] ∩
                segment ℝ γ.vertices[j.1] γ.vertices[j.1 + 1] := by
        by_contra hno
        have hsubsingleton :
            (segment ℝ γ.vertices[i.1] γ.vertices[i.1 + 1] ∩
              segment ℝ γ.vertices[j.1] γ.vertices[j.1 + 1] : Set E).Subsingleton := by
          intro p hp q hq
          by_contra hpq
          exact hno ⟨p, q, hpq, by
            intro y hy
            exact ⟨
              (convex_segment (𝕜 := ℝ) γ.vertices[i.1] γ.vertices[i.1 + 1]).segment_subset
                hp.1 hq.1 hy,
              (convex_segment (𝕜 := ℝ) γ.vertices[j.1] γ.vertices[j.1 + 1]).segment_subset
                hp.2 hq.2 hy⟩⟩
        exact hfin hsubsingleton.finite
      rcases hoverlap_exists with ⟨p, q, hpq, hpqsub⟩
      have hp_i : p ∈ segment ℝ Ai Bi := by
        simpa [Ai, Bi] using (hpqsub (left_mem_segment ℝ p q)).1
      have hq_i : q ∈ segment ℝ Ai Bi := by
        simpa [Ai, Bi] using (hpqsub (right_mem_segment ℝ p q)).1
      have hp_j : p ∈ segment ℝ Aj Bj := by
        simpa [Aj, Bj] using (hpqsub (left_mem_segment ℝ p q)).2
      have hq_j : q ∈ segment ℝ Aj Bj := by
        simpa [Aj, Bj] using (hpqsub (right_mem_segment ℝ p q)).2
      have hp_line_i : p ∈ (line[ℝ, Ai, Bi] : AffineSubspace ℝ E) :=
        segment_subset_line Ai Bi hp_i
      have hq_line_i : q ∈ (line[ℝ, Ai, Bi] : AffineSubspace ℝ E) :=
        segment_subset_line Ai Bi hq_i
      have hp_line_j : p ∈ (line[ℝ, Aj, Bj] : AffineSubspace ℝ E) :=
        segment_subset_line Aj Bj hp_j
      have hq_line_j : q ∈ (line[ℝ, Aj, Bj] : AffineSubspace ℝ E) :=
        segment_subset_line Aj Bj hq_j
      have hline_pq_i :
          (line[ℝ, p, q] : AffineSubspace ℝ E) = line[ℝ, Ai, Bi] :=
        affineSpan_pair_eq_of_mem_of_mem_of_ne hp_line_i hq_line_i hpq
      have hline_pq_j :
          (line[ℝ, p, q] : AffineSubspace ℝ E) = line[ℝ, Aj, Bj] :=
        affineSpan_pair_eq_of_mem_of_mem_of_ne hp_line_j hq_line_j hpq
      have hline_j_i :
          (line[ℝ, Aj, Bj] : AffineSubspace ℝ E) = line[ℝ, Ai, Bi] := by
        rw [← hline_pq_j, hline_pq_i]
      have he1_line_i : e.1 ∈ (line[ℝ, Ai, Bi] : AffineSubspace ℝ E) := by
        rcases heorient with hdir | hrev
        · rw [hdir]
          exact AffineMap.lineMap_mem_affineSpan_pair
            ((retainedEdgesData.subdivisionList i)[k]'(Nat.lt_of_succ_lt hk)) Ai Bi
        · rw [hrev]
          exact AffineMap.lineMap_mem_affineSpan_pair
            ((retainedEdgesData.subdivisionList i)[k + 1]'hk) Ai Bi
      have he2_line_i : e.2 ∈ (line[ℝ, Ai, Bi] : AffineSubspace ℝ E) := by
        rcases heorient with hdir | hrev
        · rw [hdir]
          exact AffineMap.lineMap_mem_affineSpan_pair
            ((retainedEdgesData.subdivisionList i)[k + 1]'hk) Ai Bi
        · rw [hrev]
          exact AffineMap.lineMap_mem_affineSpan_pair
            ((retainedEdgesData.subdivisionList i)[k]'(Nat.lt_of_succ_lt hk)) Ai Bi
      have hf1_line_j : f.1 ∈ (line[ℝ, Aj, Bj] : AffineSubspace ℝ E) := by
        rcases hforient with hdir | hrev
        · rw [hdir]
          exact AffineMap.lineMap_mem_affineSpan_pair
            ((retainedEdgesData.subdivisionList j)[l]'(Nat.lt_of_succ_lt hl)) Aj Bj
        · rw [hrev]
          exact AffineMap.lineMap_mem_affineSpan_pair
            ((retainedEdgesData.subdivisionList j)[l + 1]'hl) Aj Bj
      have hf2_line_j : f.2 ∈ (line[ℝ, Aj, Bj] : AffineSubspace ℝ E) := by
        rcases hforient with hdir | hrev
        · rw [hdir]
          exact AffineMap.lineMap_mem_affineSpan_pair
            ((retainedEdgesData.subdivisionList j)[l + 1]'hl) Aj Bj
        · rw [hrev]
          exact AffineMap.lineMap_mem_affineSpan_pair
            ((retainedEdgesData.subdivisionList j)[l]'(Nat.lt_of_succ_lt hl)) Aj Bj
      have hf1_line_i : f.1 ∈ (line[ℝ, Ai, Bi] : AffineSubspace ℝ E) := by
        simpa [hline_j_i] using hf1_line_j
      have hf2_line_i : f.2 ∈ (line[ℝ, Ai, Bi] : AffineSubspace ℝ E) := by
        simpa [hline_j_i] using hf2_line_j
      rcases (mem_affineSpan_pair_iff_exists_lineMap_eq (k := ℝ)
        (p := e.1) (p₁ := Ai) (p₂ := Bi)).mp he1_line_i with ⟨u, hu⟩
      rcases (mem_affineSpan_pair_iff_exists_lineMap_eq (k := ℝ)
        (p := e.2) (p₁ := Ai) (p₂ := Bi)).mp he2_line_i with ⟨v, hv⟩
      rcases (mem_affineSpan_pair_iff_exists_lineMap_eq (k := ℝ)
        (p := f.1) (p₁ := Ai) (p₂ := Bi)).mp hf1_line_i with ⟨r, hr⟩
      rcases (mem_affineSpan_pair_iff_exists_lineMap_eq (k := ℝ)
        (p := f.2) (p₁ := Ai) (p₂ := Bi)).mp hf2_line_i with ⟨s, hs⟩
      have hne_uv :
          AffineMap.lineMap Ai Bi u ≠ AffineMap.lineMap Ai Bi v := by
        intro huv
        exact hene (by rw [hu, hv] at huv; exact huv)
      have hne_rs :
          AffineMap.lineMap Ai Bi r ≠ AffineMap.lineMap Ai Bi s := by
        intro hrs
        exact hfne (by rw [hr, hs] at hrs; exact hrs)
      have hr_not :
          AffineMap.lineMap Ai Bi r ∉ openSegment ℝ
            (AffineMap.lineMap Ai Bi u) (AffineMap.lineMap Ai Bi v) := by
        intro hro
        exact retained_no_cut_open e he f.1 hfsrc (by simpa [hu, hv, hr] using hro)
      have hs_not :
          AffineMap.lineMap Ai Bi s ∉ openSegment ℝ
            (AffineMap.lineMap Ai Bi u) (AffineMap.lineMap Ai Bi v) := by
        intro hso
        exact retained_no_cut_open e he f.2 hftgt (by simpa [hu, hv, hs] using hso)
      have hu_not :
          AffineMap.lineMap Ai Bi u ∉ openSegment ℝ
            (AffineMap.lineMap Ai Bi r) (AffineMap.lineMap Ai Bi s) := by
        intro huo
        exact retained_no_cut_open f hf e.1 hesrc (by simpa [hr, hs, hu] using huo)
      have hv_not :
          AffineMap.lineMap Ai Bi v ∉ openSegment ℝ
            (AffineMap.lineMap Ai Bi r) (AffineMap.lineMap Ai Bi s) := by
        intro hvo
        exact retained_no_cut_open f hf e.2 hetgt (by simpa [hr, hs, hv] using hvo)
      have hsym :
          Sym2.mk e.1 e.2 = Sym2.mk f.1 f.2 := by
        simpa [hu, hv, hr, hs] using
          (line_sym2_of_open_overlap_no_endpoints Ai Bi hiseg u v r s
            hne_uv hne_rs
            (x := x)
            (by simpa [hu, hv] using hxe)
            (by simpa [hr, hs] using hxf)
            hr_not hs_not hu_not hv_not)
      exact hef (retainedEdgesData.retained_sym2_injective he hf hsym)
  intro e f he hf hef
  rcases retainedEdgesData.retained_edge_data e he with
    ⟨hesrc, hetgt, _hene, _⟩
  rcases retainedEdgesData.retained_edge_data f hf with
    ⟨hfsrc, hftgt, _hfne, _⟩
  exact exact_of_open_disjoint e f (open_disjoint e f he hf hef)
    (retained_no_cut_open f hf e.1 hesrc)
    (retained_no_cut_open f hf e.2 hetgt)
    (retained_no_cut_open e he f.1 hfsrc)
    (retained_no_cut_open e he f.2 hftgt)
