import Mathlib.Tactic
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Util.IncidenceGeometry.PolygonalPath

open Classical
noncomputable section

private lemma lineMap_lineMap_parameters
    (A B : EuclideanSpace ℝ (Fin 2)) (a b θ : ℝ) :
    AffineMap.lineMap (AffineMap.lineMap A B a) (AffineMap.lineMap A B b) θ =
      AffineMap.lineMap A B ((1 - θ) * a + θ * b) := by
  simp [AffineMap.lineMap_apply_module]
  module

private lemma lineMap_symmetric_midpoint
    (A B : EuclideanSpace ℝ (Fin 2)) (t ε : ℝ) :
    AffineMap.lineMap (AffineMap.lineMap A B (t - ε))
        (AffineMap.lineMap A B (t + ε)) ((1 : ℝ) / 2) =
      AffineMap.lineMap A B t := by
  rw [lineMap_lineMap_parameters]
  congr 1
  ring

private lemma weighted_average_mem_Icc
    {a b θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) 1) (hab : a ≤ b) :
    (1 - θ) * a + θ * b ∈ Set.Icc a b := by
  constructor <;> nlinarith [hθ.1, hθ.2]

private lemma half_ratio_mul_lt (c d : ℝ) (hc : 0 < c) (hd : 0 ≤ d) :
    (c / (d + 1) / 2) * d < c := by
  have hden : 0 < d + 1 := by linarith
  have hquot : 0 < c / (d + 1) := div_pos hc hden
  have hdhalf : d / 2 < d + 1 := by linarith
  have hhalf : c / (d + 1) / 2 * d < c / (d + 1) * (d + 1) := by
    calc
      c / (d + 1) / 2 * d = c / (d + 1) * (d / 2) := by ring
      _ < c / (d + 1) * (d + 1) := mul_lt_mul_of_pos_left hdhalf hquot
  rw [div_mul_cancel₀ c (ne_of_gt hden)] at hhalf
  exact hhalf


lemma PolygonalPathFiniteOccurrenceLocalCuts
    (α : PolygonalPath) (F U : Set (EuclideanSpace ℝ (Fin 2))) :
    Set.Finite (α.carrier ∩ F) →
      IsOpen U →
        (∀ (i : ℕ) (hi : i + 1 < α.vertices.length)
            (x : EuclideanSpace ℝ (Fin 2)),
            x ∈ openSegment ℝ α.vertices[i] α.vertices[i + 1] →
              x ∈ F → x ∈ U) →
          (∀ v : EuclideanSpace ℝ (Fin 2), v ∈ α.vertices → v ∉ F) →
            ∃ (cutBefore cutAfter :
                ∀ (i : ℕ), i + 1 < α.vertices.length →
                  EuclideanSpace ℝ (Fin 2) →
                    EuclideanSpace ℝ (Fin 2)),
              (∀ (i : ℕ) (hi : i + 1 < α.vertices.length)
                  (x : EuclideanSpace ℝ (Fin 2)),
                  x ∈ openSegment ℝ α.vertices[i] α.vertices[i + 1] →
                    x ∈ F →
                      cutBefore i hi x ∈ openSegment ℝ α.vertices[i] x ∧
                        cutAfter i hi x ∈ openSegment ℝ x α.vertices[i + 1] ∧
                          cutBefore i hi x ∈ U \ F ∧
                            cutAfter i hi x ∈ U \ F ∧
                              segment ℝ (cutBefore i hi x) (cutAfter i hi x) ∩ F =
                                {x}) ∧
                (∀ (i : ℕ) (hi : i + 1 < α.vertices.length)
                    (x y : EuclideanSpace ℝ (Fin 2)),
                    x ∈ openSegment ℝ α.vertices[i] α.vertices[i + 1] →
                      y ∈ openSegment ℝ α.vertices[i] α.vertices[i + 1] →
                        x ∈ F →
                          y ∈ F →
                            x ≠ y →
                              Disjoint
                                (segment ℝ (cutBefore i hi x) (cutAfter i hi x))
                                (segment ℝ (cutBefore i hi y) (cutAfter i hi y))) ∧
                (∀ (i : ℕ) (hi : i + 1 < α.vertices.length)
                    (y : EuclideanSpace ℝ (Fin 2)),
                    y ∈ segment ℝ α.vertices[i] α.vertices[i + 1] →
                      y ∈ F →
                        ∃ x : EuclideanSpace ℝ (Fin 2),
                          x ∈ openSegment ℝ α.vertices[i] α.vertices[i + 1] ∧
                            x ∈ F ∧
                              y ∈ segment ℝ (cutBefore i hi x)
                                (cutAfter i hi x)) := by
  intro hfinite hUopen hoccU hverticesAvoid
  let E := EuclideanSpace ℝ (Fin 2)
  have segment_subset_carrier :
      ∀ (i : ℕ) (hi : i + 1 < α.vertices.length),
        segment ℝ α.vertices[i] α.vertices[i + 1] ⊆ α.carrier := by
    intro i hi z hz
    rw [α.carrier_eq]
    right
    exact ⟨i, hi, hz⟩
  have exists_local :
      ∀ (i : ℕ) (hi : i + 1 < α.vertices.length) (x : E),
        x ∈ openSegment ℝ α.vertices[i] α.vertices[i + 1] →
          x ∈ F →
            ∃ u v : E,
              u ∈ openSegment ℝ α.vertices[i] x ∧
                v ∈ openSegment ℝ x α.vertices[i + 1] ∧
                  u ∈ U \ F ∧
                    v ∈ U \ F ∧
                      x ∈ segment ℝ u v ∧
                        segment ℝ u v ∩ F = {x} ∧
                          ∃ t ε : ℝ,
                            0 < t ∧ t < 1 ∧ 0 < ε ∧ ε < t ∧
                              t + ε < 1 ∧
                                AffineMap.lineMap α.vertices[i] α.vertices[i + 1] t = x ∧
                                  u = AffineMap.lineMap α.vertices[i] α.vertices[i + 1]
                                    (t - ε) ∧
                                  v = AffineMap.lineMap α.vertices[i] α.vertices[i + 1]
                                    (t + ε) ∧
                                  ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
                                    AffineMap.lineMap α.vertices[i] α.vertices[i + 1] s ∈
                                      F →
                                    s ≠ t → ε < |s - t| / 3 := by
    intro i hi x hxOpen hxF
    let A : E := α.vertices[i]
    let B : E := α.vertices[i + 1]
    have hA_mem_vertices : A ∈ α.vertices :=
      List.getElem_mem (l := α.vertices) (n := i) (Nat.lt_of_succ_lt hi)
    have hB_mem_vertices : B ∈ α.vertices :=
      List.getElem_mem (l := α.vertices) (n := i + 1) hi
    have hA_notF : A ∉ F := hverticesAvoid A hA_mem_vertices
    have hB_notF : B ∉ F := hverticesAvoid B hB_mem_vertices
    have hx_ne_A : x ≠ A := by
      intro h
      exact hA_notF (by simpa [A, h] using hxF)
    have hx_ne_B : x ≠ B := by
      intro h
      exact hB_notF (by simpa [B, h] using hxF)
    have hxOpenAB : x ∈ openSegment ℝ A B := by
      simpa [A, B] using hxOpen
    have hAB : A ≠ B := by
      intro hABeq
      have hx_eq_A : x = A := by
        simpa [A, B, hABeq] using hxOpen
      exact hx_ne_A hx_eq_A
    have hxU : x ∈ U := hoccU i hi x (by simpa [A, B] using hxOpenAB) hxF
    obtain ⟨η, hηpos, hηball⟩ := Metric.isOpen_iff.mp hUopen x hxU
    rw [openSegment_eq_image_lineMap] at hxOpen
    rcases hxOpen with ⟨t, htIoo, htx⟩
    let f : ℝ → E := fun r => AffineMap.lineMap A B r
    have htx' : f t = x := by
      simpa [f] using htx
    have ht0 : 0 < t := htIoo.1
    have ht1 : t < 1 := htIoo.2
    have hdistABpos : 0 < dist A B := dist_pos.mpr hAB
    let Xfin : Finset E := hfinite.toFinset
    let bad : Finset ℝ := Xfin.preimage f (AffineMap.lineMap_injective ℝ hAB).injOn
    have param01_in_bad_of_mem :
        ∀ {r : ℝ}, r ∈ Set.Icc (0 : ℝ) 1 → f r ∈ F → r ∈ bad := by
      intro r hr01 hrF
      apply Finset.mem_preimage.mpr
      have hfr_seg : f r ∈ segment ℝ A B := by
        rw [segment_eq_image_lineMap]
        exact ⟨r, hr01, rfl⟩
      have hfr_carrier : f r ∈ α.carrier :=
        segment_subset_carrier i hi (by simpa [A, B, f] using hfr_seg)
      have hfrX : f r ∈ α.carrier ∩ F := ⟨hfr_carrier, hrF⟩
      exact (Set.Finite.mem_toFinset hfinite).2 hfrX
    have hxCarrier : x ∈ α.carrier := by
      exact segment_subset_carrier i hi (openSegment_subset_segment ℝ A B hxOpenAB)
    have hxX : x ∈ α.carrier ∩ F := ⟨hxCarrier, hxF⟩
    have ht_bad : t ∈ bad := by
      apply Finset.mem_preimage.mpr
      have hxfin : x ∈ Xfin := (Set.Finite.mem_toFinset hfinite).2 hxX
      simpa [Xfin, f, htx'] using hxfin
    have finite_radius :
        ∀ C : Finset ℝ, (∀ s ∈ C, s ≠ t) →
          ∀ base : ℝ, 0 < base →
            ∃ ε : ℝ, 0 < ε ∧ ε ≤ base ∧
              ∀ s ∈ C, ε < |s - t| / 3 := by
      intro C
      induction C using Finset.induction with
      | empty =>
        intro hC base hbase
        exact ⟨base, hbase, le_rfl, by simp⟩
      | insert a C ha ih =>
        intro hC base hbase
        have hC' : ∀ s ∈ C, s ≠ t := by
          intro s hs
          exact hC s (Finset.mem_insert.mpr (Or.inr hs))
        obtain ⟨ε, hεpos, hεle, hεsmall⟩ := ih hC' base hbase
        have ha_ne_t : a ≠ t := hC a (Finset.mem_insert_self a C)
        have hdist_pos : 0 < |a - t| / 4 := by
          have habs : 0 < |a - t| := abs_pos.mpr (sub_ne_zero.mpr ha_ne_t)
          positivity
        let ε' : ℝ := min ε (|a - t| / 4)
        have hε'pos : 0 < ε' := lt_min hεpos hdist_pos
        refine ⟨ε', hε'pos, (min_le_left ε (|a - t| / 4)).trans hεle, ?_⟩
        intro s hs
        rw [Finset.mem_insert] at hs
        rcases hs with hs_eq | hsC
        · subst s
          dsimp [ε']
          have hle : min ε (|a - t| / 4) ≤ |a - t| / 4 := min_le_right _ _
          linarith [abs_nonneg (a - t)]
        · exact lt_of_le_of_lt (min_le_left ε (|a - t| / 4)) (hεsmall s hsC)
    let base : ℝ := min (min (t / 2) ((1 - t) / 2)) (η / (dist A B + 1) / 2)
    have hbase_pos : 0 < base := by
      dsimp [base]
      have hden_pos : 0 < dist A B + 1 := by positivity
      have hthird : 0 < η / (dist A B + 1) / 2 :=
        half_pos (div_pos hηpos hden_pos)
      exact lt_min (lt_min (half_pos ht0) (half_pos (sub_pos.mpr ht1))) hthird
    let C : Finset ℝ := bad.erase t
    have hC_ne : ∀ s ∈ C, s ≠ t := by
      intro s hs
      exact (Finset.mem_erase.mp hs).1
    obtain ⟨ε, hεpos, hεle_base, hεsmallC⟩ := finite_radius C hC_ne base hbase_pos
    have hε_lt_t : ε < t := by
      have hle : ε ≤ t / 2 := hεle_base.trans (by
        dsimp [base]
        exact (min_le_left _ _).trans (min_le_left _ _))
      linarith
    have htε_lt_one : t + ε < 1 := by
      have hle : ε ≤ (1 - t) / 2 := hεle_base.trans (by
        dsimp [base]
        exact (min_le_left _ _).trans (min_le_right _ _))
      linarith
    have hεdist_lt_η : ε * dist A B < η := by
      have hle : ε ≤ η / (dist A B + 1) / 2 := hεle_base.trans (by
        dsimp [base]
        exact min_le_right _ _)
      have hmul_le : ε * dist A B ≤ (η / (dist A B + 1) / 2) * dist A B :=
        mul_le_mul_of_nonneg_right hle dist_nonneg
      have htarget_lt : (η / (dist A B + 1) / 2) * dist A B < η :=
        half_ratio_mul_lt η (dist A B) hηpos dist_nonneg
      exact lt_of_le_of_lt hmul_le htarget_lt
    let u : E := f (t - ε)
    let v : E := f (t + ε)
    have htu0 : 0 < t - ε := by linarith
    have htu1 : t - ε < t := by linarith
    have htv0 : t < t + ε := by linarith
    have htv1 : t + ε < 1 := htε_lt_one
    have hu_open_Ax : u ∈ openSegment ℝ A x := by
      rw [openSegment_eq_image_lineMap]
      refine ⟨(t - ε) / t, ⟨by positivity, by
        rw [div_lt_one (by linarith : 0 < t)]
        exact htu1⟩, ?_⟩
      dsimp [u, f]
      rw [← htx']
      rw [AffineMap.lineMap_lineMap_right]
      field_simp [ne_of_gt ht0]
    have hv_open_xB : v ∈ openSegment ℝ x B := by
      rw [openSegment_eq_image_lineMap]
      refine ⟨ε / (1 - t), ⟨by exact div_pos hεpos (sub_pos.mpr ht1), by
        rw [div_lt_one (by linarith : 0 < 1 - t)]
        linarith⟩, ?_⟩
      dsimp [v, f]
      rw [← htx']
      rw [AffineMap.lineMap_lineMap_left]
      congr 1
      have h1mt_ne : 1 - t ≠ 0 := by linarith
      field_simp [h1mt_ne]
      ring
    have segment_uv_param :
        ∀ {z : E}, z ∈ segment ℝ u v →
          ∃ r : ℝ, r ∈ Set.Icc (t - ε) (t + ε) ∧ z = f r := by
      intro z hz
      rw [segment_eq_image_lineMap] at hz
      rcases hz with ⟨θ, hθ, hzθ⟩
      let r : ℝ := (1 - θ) * (t - ε) + θ * (t + ε)
      refine ⟨r, ?_, ?_⟩
      · exact weighted_average_mem_Icc hθ (by linarith)
      · rw [← hzθ]
        simpa [u, v, f, r] using
          lineMap_lineMap_parameters A B (t - ε) (t + ε) θ
    have param_in_bad_of_mem :
        ∀ {r : ℝ}, r ∈ Set.Icc (t - ε) (t + ε) → f r ∈ F → r ∈ bad := by
      intro r hr hrF
      have hr01 : r ∈ Set.Icc (0 : ℝ) 1 := by
        exact ⟨by linarith [hr.1], by linarith [hr.2, htv1]⟩
      exact param01_in_bad_of_mem hr01 hrF
    have param_eq_t_of_mem :
        ∀ {r : ℝ}, r ∈ Set.Icc (t - ε) (t + ε) → f r ∈ F → r = t := by
      intro r hr hrF
      have hr_bad : r ∈ bad := param_in_bad_of_mem hr hrF
      by_cases hrt : r = t
      · exact hrt
      have hrC : r ∈ C := Finset.mem_erase.mpr ⟨hrt, hr_bad⟩
      have hsmall := hεsmallC r hrC
      have habs_le : |r - t| ≤ ε := by
        rw [abs_le]
        constructor <;> linarith [hr.1, hr.2]
      linarith [hsmall, habs_le, hεpos]
    have huU : u ∈ U := by
      apply hηball
      rw [Metric.mem_ball]
      dsimp [u, f]
      rw [← htx']
      rw [dist_lineMap_lineMap, Real.dist_eq]
      have habs : |(t - ε) - t| = ε := by
        rw [abs_of_nonpos (by linarith : (t - ε) - t ≤ 0)]
        ring
      rw [habs]
      exact hεdist_lt_η
    have hvU : v ∈ U := by
      apply hηball
      rw [Metric.mem_ball]
      dsimp [v, f]
      rw [← htx']
      rw [dist_lineMap_lineMap, Real.dist_eq]
      have habs : |(t + ε) - t| = ε := by
        rw [abs_of_nonneg (by linarith : 0 ≤ (t + ε) - t)]
        ring
      rw [habs]
      exact hεdist_lt_η
    have hu_notF : u ∉ F := by
      intro huF
      have hreq := param_eq_t_of_mem (r := t - ε) ⟨le_rfl, by linarith⟩ huF
      linarith
    have hv_notF : v ∉ F := by
      intro hvF
      have hreq := param_eq_t_of_mem (r := t + ε) ⟨by linarith, le_rfl⟩ hvF
      linarith
    have hx_segment_uv : x ∈ segment ℝ u v := by
      rw [segment_eq_image_lineMap]
      refine ⟨(1 : ℝ) / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
      · dsimp [u, v, f]
        rw [← htx']
        exact lineMap_symmetric_midpoint A B t ε
    have hseg_inter : segment ℝ u v ∩ F = ({x} : Set E) := by
      ext z
      constructor
      · intro hz
        rcases hz with ⟨hzseg, hzF⟩
        rcases segment_uv_param hzseg with ⟨r, hr, rfl⟩
        have hrt := param_eq_t_of_mem hr hzF
        simp [hrt, htx']
      · intro hz
        have hz' : z = x := by simpa using hz
        subst z
        exact ⟨hx_segment_uv, hxF⟩
    have hεsmall_all :
        ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → f s ∈ F → s ≠ t →
          ε < |s - t| / 3 := by
      intro s hs01 hsF hst
      exact hεsmallC s
        (Finset.mem_erase.mpr ⟨hst, param01_in_bad_of_mem hs01 hsF⟩)
    exact ⟨u, v, hu_open_Ax, hv_open_xB, ⟨huU, hu_notF⟩, ⟨hvU, hv_notF⟩,
      hx_segment_uv, hseg_inter, t, ε, ht0, ht1, hεpos, hε_lt_t, htε_lt_one,
      htx', rfl, rfl, hεsmall_all⟩
  let cutBefore :
      ∀ (i : ℕ), i + 1 < α.vertices.length → E → E :=
    fun i hi x =>
      if h : x ∈ openSegment ℝ α.vertices[i] α.vertices[i + 1] ∧ x ∈ F then
        Classical.choose (exists_local i hi x h.1 h.2)
      else x
  let cutAfter :
      ∀ (i : ℕ), i + 1 < α.vertices.length → E → E :=
    fun i hi x =>
      if h : x ∈ openSegment ℝ α.vertices[i] α.vertices[i + 1] ∧ x ∈ F then
        Classical.choose (Classical.choose_spec (exists_local i hi x h.1 h.2))
      else x
  refine ⟨cutBefore, cutAfter, ?_, ?_, ?_⟩
  · intro i hi x hxOpen hxF
    have hcond : x ∈ openSegment ℝ α.vertices[i] α.vertices[i + 1] ∧ x ∈ F :=
      ⟨hxOpen, hxF⟩
    dsimp [cutBefore, cutAfter]
    rw [dif_pos hcond]
    rw [dif_pos hcond]
    rcases (Classical.choose_spec
      (Classical.choose_spec (exists_local i hi x hxOpen hxF))) with
      ⟨hbefore, hafter, hbeforeUF, hafterUF, _hxseg, hseg, _hparam⟩
    exact ⟨hbefore, hafter, hbeforeUF, hafterUF, hseg⟩
  · intro i hi x y hxOpen hyOpen hxF hyF hxy
    let A : E := α.vertices[i]
    let B : E := α.vertices[i + 1]
    let f : ℝ → E := fun r => AffineMap.lineMap A B r
    have hA_notF : A ∉ F :=
      hverticesAvoid A
        (List.getElem_mem (l := α.vertices) (n := i) (Nat.lt_of_succ_lt hi))
    have hAB : A ≠ B := by
      intro hABeq
      have hx_eq_A : x = A := by
        simpa [A, B, hABeq] using hxOpen
      exact hA_notF (by simpa [hx_eq_A] using hxF)
    let exx := exists_local i hi x hxOpen hxF
    let ux : E := Classical.choose exx
    let vx : E := Classical.choose (Classical.choose_spec exx)
    let exy := exists_local i hi y hyOpen hyF
    let uy : E := Classical.choose exy
    let vy : E := Classical.choose (Classical.choose_spec exy)
    have hxspec :
        ux ∈ openSegment ℝ α.vertices[i] x ∧
          vx ∈ openSegment ℝ x α.vertices[i + 1] ∧
            ux ∈ U \ F ∧
              vx ∈ U \ F ∧
                x ∈ segment ℝ ux vx ∧
                  segment ℝ ux vx ∩ F = {x} ∧
                    ∃ t ε : ℝ,
                      0 < t ∧ t < 1 ∧ 0 < ε ∧ ε < t ∧ t + ε < 1 ∧
                        f t = x ∧ ux = f (t - ε) ∧ vx = f (t + ε) ∧
                          ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
                            f s ∈ F → s ≠ t → ε < |s - t| / 3 := by
      dsimp [ux, vx, exx, f, A, B]
      exact Classical.choose_spec (Classical.choose_spec (exists_local i hi x hxOpen hxF))
    have hyspec :
        uy ∈ openSegment ℝ α.vertices[i] y ∧
          vy ∈ openSegment ℝ y α.vertices[i + 1] ∧
            uy ∈ U \ F ∧
              vy ∈ U \ F ∧
                y ∈ segment ℝ uy vy ∧
                  segment ℝ uy vy ∩ F = {y} ∧
                    ∃ t ε : ℝ,
                      0 < t ∧ t < 1 ∧ 0 < ε ∧ ε < t ∧ t + ε < 1 ∧
                        f t = y ∧ uy = f (t - ε) ∧ vy = f (t + ε) ∧
                          ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
                            f s ∈ F → s ≠ t → ε < |s - t| / 3 := by
      dsimp [uy, vy, exy, f, A, B]
      exact Classical.choose_spec (Classical.choose_spec (exists_local i hi y hyOpen hyF))
    rcases hxspec with
      ⟨_huxOpen, _hvxOpen, _huxUF, _hvxUF, _hxseg, _hxinter,
        tx, εx, htx0, htx1, hεxpos, hεx_lt_tx, htxεx_lt_one, htxparam,
        huxparam, hvxparam, hsmallx⟩
    rcases hyspec with
      ⟨_huyOpen, _hvyOpen, _huyUF, _hvyUF, _hyseg, _hyinter,
        ty, εy, hty0, hty1, hεypos, hεy_lt_ty, htyεy_lt_one, htyparam,
        huyparam, hvyparam, hsmally⟩
    have hty_ne_tx : ty ≠ tx := by
      intro htytx
      exact hxy (by
        rw [← htxparam, ← htyparam, htytx])
    have htx_ne_ty : tx ≠ ty := fun h => hty_ne_tx h.symm
    have hsmallx_ty : εx < |ty - tx| / 3 := by
      exact hsmallx ty ⟨le_of_lt hty0, le_of_lt hty1⟩
        (by simpa [← htyparam] using hyF) hty_ne_tx
    have hsmally_tx : εy < |ty - tx| / 3 := by
      have h := hsmally tx ⟨le_of_lt htx0, le_of_lt htx1⟩
        (by simpa [← htxparam] using hxF) htx_ne_ty
      rwa [abs_sub_comm] at h
    have seg_param_x :
        ∀ {z : E}, z ∈ segment ℝ ux vx →
          ∃ r : ℝ, r ∈ Set.Icc (tx - εx) (tx + εx) ∧ z = f r := by
      intro z hz
      rw [segment_eq_image_lineMap] at hz
      rcases hz with ⟨θ, hθ, hzθ⟩
      let r : ℝ := (1 - θ) * (tx - εx) + θ * (tx + εx)
      refine ⟨r, ?_, ?_⟩
      · exact weighted_average_mem_Icc hθ (by linarith)
      · rw [← hzθ, huxparam, hvxparam]
        simpa [f, r] using
          lineMap_lineMap_parameters A B (tx - εx) (tx + εx) θ
    have seg_param_y :
        ∀ {z : E}, z ∈ segment ℝ uy vy →
          ∃ r : ℝ, r ∈ Set.Icc (ty - εy) (ty + εy) ∧ z = f r := by
      intro z hz
      rw [segment_eq_image_lineMap] at hz
      rcases hz with ⟨θ, hθ, hzθ⟩
      let r : ℝ := (1 - θ) * (ty - εy) + θ * (ty + εy)
      refine ⟨r, ?_, ?_⟩
      · exact weighted_average_mem_Icc hθ (by linarith)
      · rw [← hzθ, huyparam, hvyparam]
        simpa [f, r] using
          lineMap_lineMap_parameters A B (ty - εy) (ty + εy) θ
    have hcondx : x ∈ openSegment ℝ α.vertices[i] α.vertices[i + 1] ∧ x ∈ F :=
      ⟨hxOpen, hxF⟩
    have hcondy : y ∈ openSegment ℝ α.vertices[i] α.vertices[i + 1] ∧ y ∈ F :=
      ⟨hyOpen, hyF⟩
    dsimp [cutBefore, cutAfter]
    rw [dif_pos hcondx, dif_pos hcondx, dif_pos hcondy, dif_pos hcondy]
    change Disjoint (segment ℝ ux vx) (segment ℝ uy vy)
    rw [Set.disjoint_left]
    intro z hzx hzy
    rcases seg_param_x hzx with ⟨rx, hrx, hzrx⟩
    rcases seg_param_y hzy with ⟨ry, hry, hzry⟩
    have hrxy : rx = ry := by
      exact (AffineMap.lineMap_injective ℝ hAB) (hzrx.symm.trans hzry)
    subst ry
    have hdist_le : |ty - tx| ≤ εx + εy := by
      rw [abs_le]
      constructor <;> linarith [hrx.1, hrx.2, hry.1, hry.2]
    have hdist_pos : 0 < |ty - tx| := by
      exact abs_pos.mpr (sub_ne_zero.mpr hty_ne_tx)
    linarith [hdist_le, hsmallx_ty, hsmally_tx, hdist_pos]
  · intro i hi y hyseg hyF
    have hA_notF :
        α.vertices[i] ∉ F :=
      hverticesAvoid α.vertices[i]
        (List.getElem_mem (l := α.vertices) (n := i) (Nat.lt_of_succ_lt hi))
    have hB_notF :
        α.vertices[i + 1] ∉ F :=
      hverticesAvoid α.vertices[i + 1]
        (List.getElem_mem (l := α.vertices) (n := i + 1) hi)
    have hyOpen : y ∈ openSegment ℝ α.vertices[i] α.vertices[i + 1] := by
      refine mem_openSegment_of_ne_left_right (𝕜 := ℝ) ?_ ?_ hyseg
      · intro hy_eq
        exact hA_notF (by simpa [hy_eq] using hyF)
      · intro hy_eq
        exact hB_notF (by simpa [hy_eq] using hyF)
    refine ⟨y, hyOpen, hyF, ?_⟩
    have hcond : y ∈ openSegment ℝ α.vertices[i] α.vertices[i + 1] ∧ y ∈ F :=
      ⟨hyOpen, hyF⟩
    dsimp [cutBefore, cutAfter]
    rw [dif_pos hcond]
    rw [dif_pos hcond]
    exact (Classical.choose_spec
      (Classical.choose_spec (exists_local i hi y hyOpen hyF))).2.2.2.2.1
