import Util.IncidenceGeometry.JordanLocalSideData
import Util.IncidenceGeometry.PolygonalSideStrips
import Util.IncidenceGeometry.SimpleClosedPolygonalCurve
import Util.IncidenceGeometry.PolygonalArc
import Util.IncidenceGeometry.SimpleClosedCurveAsFinitePolygonalSet
import Util.IncidenceGeometry.FinitePolygonalSet
import Util.IncidenceGeometry.JordanExteriorLocalSideUnbounded
import Util.IncidenceGeometry.FinitePointLineAvoidance
import Util.IncidenceGeometry.FiniteStraightLineComplexCarrierCompact
import Util.IncidenceGeometry.EuclideanPlaneClosedBallExteriorConnected

open Classical
noncomputable section

lemma JordanGenericRayReachesLocalSide
    (J : SimpleClosedPolygonalCurve) (S : JordanLocalSideData J)
    (p : EuclideanSpace ℝ (Fin 2)) (hp : p ∈ J.carrierᶜ) :
    ∃ C : Set (EuclideanSpace ℝ (Fin 2)),
      C.Nonempty ∧ C ⊆ J.carrierᶜ ∧ IsConnected C ∧ p ∈ C ∧
        ((C ∩ S.leftRegion).Nonempty ∨ (C ∩ S.rightRegion).Nonempty) := by
  classical
  let V : Finset (EuclideanSpace ℝ (Fin 2)) :=
    (Finset.univ : Finset {γ : PolygonalArc // γ ∈ J.edgeArcs}).biUnion
      (fun γ => γ.1.vertices.toFinset)
  let E : Finset
      (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)) :=
    (Finset.univ : Finset {γ : PolygonalArc // γ ∈ J.edgeArcs}).biUnion
      (fun γ =>
        (Finset.univ : Finset (Fin (γ.1.vertices.length - 1))).image
          (fun i =>
            (γ.1.vertices[i.1]'(by omega),
              γ.1.vertices[i.1 + 1]'(by omega))))
  have vertex_mem_V :
      ∀ (γ : {γ : PolygonalArc // γ ∈ J.edgeArcs})
        {v : EuclideanSpace ℝ (Fin 2)}, v ∈ γ.1.vertices → v ∈ V := by
    intro γ v hv
    dsimp [V]
    rw [Finset.mem_biUnion]
    exact ⟨γ, by simp, by simpa using hv⟩
  have segment_mem_E :
      ∀ (γ : {γ : PolygonalArc // γ ∈ J.edgeArcs})
        (i : ℕ) (hi : i + 1 < γ.1.vertices.length),
          (γ.1.vertices[i]'(Nat.lt_of_succ_lt hi),
            γ.1.vertices[i + 1]'hi) ∈ E := by
    intro γ i hi
    dsimp [E]
    rw [Finset.mem_biUnion]
    refine ⟨γ, by simp, ?_⟩
    let k : Fin (γ.1.vertices.length - 1) := ⟨i, by omega⟩
    refine Finset.mem_image.mpr ⟨k, by simp, ?_⟩
    simp [k]
  let badVectors : Finset (EuclideanSpace ℝ (Fin 2)) :=
    V.image (fun v => v - p) ∪ E.image (fun e => e.2 - e.1)
  let nonzeroBadVectors : Finset (EuclideanSpace ℝ (Fin 2)) :=
    badVectors.filter (fun w => w ≠ 0)
  let badLines : Finset (AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))) :=
    nonzeroBadVectors.image (fun w => (ℝ ∙ w).toAffineSubspace)
  have badLine_data : ∀ ℓ ∈ badLines,
      (ℓ : Set (EuclideanSpace ℝ (Fin 2))).Nonempty ∧
        Module.finrank ℝ ℓ.direction = 1 := by
    intro ℓ hℓ
    rcases Finset.mem_image.mp hℓ with ⟨w, hw, rfl⟩
    have hw0 : w ≠ 0 := (Finset.mem_filter.mp hw).2
    constructor
    · exact ⟨0, by simp⟩
    · rw [Submodule.toAffineSubspace_direction]
      exact finrank_span_singleton hw0
  obtain ⟨u, _huUniv, huPoint, huLine⟩ :=
    FinitePointLineAvoidance Set.univ {0} badLines isOpen_univ Set.univ_nonempty
      badLine_data
  have hu0 : u ≠ 0 := by
    intro hu
    apply huPoint
    simp [hu]
  have huV : ∀ v ∈ V, u ∉ ℝ ∙ (v - p) := by
    intro v hv huv
    by_cases hvp : v - p = 0
    · apply hu0
      simpa [hvp] using huv
    · apply huLine ((ℝ ∙ (v - p)).toAffineSubspace)
      · apply Finset.mem_image.mpr
        refine ⟨v - p, ?_, rfl⟩
        apply Finset.mem_filter.mpr
        refine ⟨?_, hvp⟩
        apply Finset.mem_union_left
        exact Finset.mem_image.mpr ⟨v, hv, rfl⟩
      · change u ∈ ℝ ∙ (v - p)
        exact huv
  have huE : ∀ e ∈ E, u ∉ ℝ ∙ (e.2 - e.1) := by
    intro e he hue
    by_cases he12 : e.2 - e.1 = 0
    · apply hu0
      simpa [he12] using hue
    · apply huLine ((ℝ ∙ (e.2 - e.1)).toAffineSubspace)
      · apply Finset.mem_image.mpr
        refine ⟨e.2 - e.1, ?_, rfl⟩
        apply Finset.mem_filter.mpr
        refine ⟨?_, he12⟩
        apply Finset.mem_union_right
        exact Finset.mem_image.mpr ⟨e, he, rfl⟩
      · change u ∈ ℝ ∙ (e.2 - e.1)
        exact hue
  let ρ : ℝ → EuclideanSpace ℝ (Fin 2) := fun t => p + t • u
  have hρcontinuous : Continuous ρ :=
    continuous_const.add (continuous_id.smul continuous_const)
  let H : Set ℝ := {t | 0 ≤ t ∧ ρ t ∈ J.carrier}
  have segment_hit_subsingleton :
      ∀ e ∈ E, ({t : ℝ | 0 ≤ t ∧ ρ t ∈ segment ℝ e.1 e.2} : Set ℝ).Subsingleton := by
    intro e he s hs t ht
    rcases hs with ⟨_hs0, hsseg⟩
    rcases ht with ⟨_ht0, htseg⟩
    rw [segment_eq_image_lineMap] at hsseg htseg
    rcases hsseg with ⟨x, hxIcc, hx⟩
    rcases htseg with ⟨y, hyIcc, hy⟩
    by_contra hst
    have hlinear : (s - t) • u = (x - y) • (e.2 - e.1) := by
      rw [AffineMap.lineMap_apply_module] at hx hy
      change (1 - x) • e.1 + x • e.2 = p + s • u at hx
      change (1 - y) • e.1 + y • e.2 = p + t • u at hy
      ext i
      have hxi := congrArg (fun z => z i) hx
      have hyi := congrArg (fun z => z i) hy
      simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
        at hxi hyi ⊢
      linarith
    apply huE e he
    rw [Submodule.mem_span_singleton]
    refine ⟨(s - t)⁻¹ * (x - y), ?_⟩
    calc
      ((s - t)⁻¹ * (x - y)) • (e.2 - e.1) =
          (s - t)⁻¹ • ((x - y) • (e.2 - e.1)) := by rw [smul_smul]
      _ = (s - t)⁻¹ • ((s - t) • u) := by rw [← hlinear]
      _ = u := by
        rw [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hst), one_smul]
  have hHfinite : H.Finite := by
    let hits := fun e : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) =>
      {t : ℝ | 0 ≤ t ∧ ρ t ∈ segment ℝ e.1 e.2}
    have hUnionFinite : (⋃ e ∈ (E : Set _), hits e).Finite :=
      E.finite_toSet.biUnion fun e he =>
        (segment_hit_subsingleton e he).finite
    apply hUnionFinite.subset
    intro t ht
    rcases ht with ⟨ht0, htJ⟩
    rw [J.carrier_eq] at htJ
    rcases Set.mem_iUnion.mp htJ with ⟨γ, htγ⟩
    rw [γ.1.carrier_eq] at htγ
    rcases htγ with ⟨i, hi, htseg⟩
    let e : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) :=
      (γ.1.vertices[i]'(Nat.lt_of_succ_lt hi), γ.1.vertices[i + 1]'hi)
    have he : e ∈ E := segment_mem_E γ i hi
    rw [Set.mem_iUnion]
    refine ⟨e, ?_⟩
    rw [Set.mem_iUnion]
    exact ⟨he, ht0, by simpa [hits, e] using htseg⟩
  by_cases hHne : H.Nonempty
  · let HF : Finset ℝ := hHfinite.toFinset
    have hHFne : HF.Nonempty := by
      rcases hHne with ⟨t, ht⟩
      exact ⟨t, by simpa [HF] using ht⟩
    let t0 : ℝ := HF.min' hHFne
    have ht0H : t0 ∈ H := by
      have := Finset.min'_mem HF hHFne
      simpa [HF, t0] using this
    have ht0nonneg : 0 ≤ t0 := ht0H.1
    have ht0pos : 0 < t0 := by
      apply lt_of_le_of_ne ht0nonneg
      intro ht0zero
      have hpJ : p ∈ J.carrier := by
        have := ht0H.2
        simpa [ρ, ← ht0zero] using this
      exact hp hpJ
    have ht0least : ∀ {t : ℝ}, t ∈ H → t0 ≤ t := by
      intro t ht
      exact Finset.min'_le HF t (by simpa [HF] using ht)
    let q := ρ t0
    have hqJ : q ∈ J.carrier := ht0H.2
    rw [J.carrier_eq] at hqJ
    rcases Set.mem_iUnion.mp hqJ with ⟨γ, hqγ⟩
    have ray_avoids_vertices :
        ∀ {v : EuclideanSpace ℝ (Fin 2)}, v ∈ V → q ≠ v := by
      intro v hv hqv
      apply huV v hv
      rw [Submodule.mem_span_singleton]
      refine ⟨t0⁻¹, ?_⟩
      have hqeq : p + t0 • u = v := by simpa [q, ρ] using hqv
      rw [← hqeq]
      simp only [add_sub_cancel_left]
      rw [smul_smul, inv_mul_cancel₀ ht0pos.ne', one_smul]
    have hsourceMem : γ.1.source ∈ γ.1.vertices := by
      apply List.mem_of_mem_head?
      rw [γ.1.source_eq_head]
      simp
    have htargetMem : γ.1.target ∈ γ.1.vertices := by
      apply List.mem_of_mem_getLast?
      rw [γ.1.target_eq_last]
      simp
    have hqsource : q ≠ γ.1.source :=
      ray_avoids_vertices (vertex_mem_V γ hsourceMem)
    have hqtarget : q ≠ γ.1.target :=
      ray_avoids_vertices (vertex_mem_V γ htargetMem)
    have hqri : q ∈ γ.1.relativeInterior := by
      rw [γ.1.relativeInterior_eq]
      exact ⟨hqγ, by simp [hqsource, hqtarget]⟩
    let strip : PolygonalSideStrips γ.1 := (S.edge_strips γ).1
    have hqcollar : q ∈ strip.collar := strip.relativeInterior_subset_collar hqri
    have hopenPre : IsOpen (ρ ⁻¹' strip.collar) :=
      strip.collar_open.preimage hρcontinuous
    obtain ⟨ε, hεpos, hεball⟩ := Metric.isOpen_iff.mp hopenPre t0 hqcollar
    let d : ℝ := min (t0 / 2) (ε / 2)
    have hdpos : 0 < d := by
      dsimp [d]
      exact lt_min (half_pos ht0pos) (half_pos hεpos)
    have hdt0 : d < t0 :=
      lt_of_le_of_lt (min_le_left _ _) (half_lt_self ht0pos)
    have hdε : d < ε :=
      lt_of_le_of_lt (min_le_right _ _) (half_lt_self hεpos)
    let tm : ℝ := t0 - d
    let qm := ρ tm
    have htm0 : 0 ≤ tm := by dsimp [tm]; linarith
    have htmt0 : tm < t0 := by dsimp [tm]; linarith
    have hqmcollar : qm ∈ strip.collar := by
      apply hεball
      change dist tm t0 < ε
      rw [Real.dist_eq]
      have : |tm - t0| = d := by
        dsimp [tm]
        rw [abs_of_neg (by linarith)]
        ring
      rw [this]
      exact hdε
    have htmNotJ : ρ tm ∉ J.carrier := by
      intro htmJ
      have htmH : tm ∈ H := ⟨htm0, htmJ⟩
      linarith [ht0least htmH]
    have hqmSide : qm ∈ strip.leftStrip ∨ qm ∈ strip.rightStrip := by
      have hdiff : qm ∈ strip.collar \ γ.1.relativeInterior := by
        refine ⟨hqmcollar, ?_⟩
        intro hqmri
        exact htmNotJ (by
          rw [J.carrier_eq]
          apply Set.mem_iUnion.mpr
          refine ⟨γ, ?_⟩
          rw [γ.1.relativeInterior_eq] at hqmri
          exact hqmri.1)
      rw [strip.collar_without_arc] at hdiff
      exact hdiff
    let C : Set (EuclideanSpace ℝ (Fin 2)) := ρ '' Set.Icc 0 tm
    refine ⟨C, ?_, ?_, ?_, ?_, ?_⟩
    · exact ⟨p, ⟨0, ⟨le_rfl, htm0⟩, by simp [ρ]⟩⟩
    · rintro z ⟨t, ht, rfl⟩
      intro htJ
      have htH : t ∈ H := ⟨ht.1, htJ⟩
      exact (not_lt_of_ge (ht0least htH)) (lt_of_le_of_lt ht.2 htmt0)
    · refine ⟨?_, isPreconnected_Icc.image ρ hρcontinuous.continuousOn⟩
      exact ⟨p, ⟨0, ⟨le_rfl, htm0⟩, by simp [ρ]⟩⟩
    · exact ⟨0, ⟨le_rfl, htm0⟩, by simp [ρ]⟩
    · rcases hqmSide with hqmLeft | hqmRight
      · left
        refine ⟨qm, ⟨?_, ?_⟩⟩
        · exact ⟨tm, ⟨htm0, le_rfl⟩, rfl⟩
        · exact (S.edge_strips γ).2.1 hqmLeft
      · right
        refine ⟨qm, ⟨?_, ?_⟩⟩
        · exact ⟨tm, ⟨htm0, le_rfl⟩, rfl⟩
        · exact (S.edge_strips γ).2.2 hqmRight
  · have hHempty : H = ∅ := Set.not_nonempty_iff_eq_empty.mp hHne
    let Rray : Set (EuclideanSpace ℝ (Fin 2)) := ρ '' Set.Ici 0
    have hpRay : p ∈ Rray := ⟨0, by simp, by simp [ρ]⟩
    have hRayNonempty : Rray.Nonempty := ⟨p, hpRay⟩
    have hRaySub : Rray ⊆ J.carrierᶜ := by
      rintro z ⟨t, ht, rfl⟩ htJ
      have : t ∈ H := ⟨ht, htJ⟩
      rw [hHempty] at this
      exact this
    have hRayConn : IsConnected Rray :=
      isConnected_Ici.image ρ hρcontinuous.continuousOn
    have hRayUnbounded : ¬ Bornology.IsBounded Rray := by
      intro hbounded
      rcases Metric.isBounded_iff.mp hbounded with ⟨C, hC⟩
      have huNorm : 0 < ‖u‖ := norm_pos_iff.mpr hu0
      let t : ℝ := (|C| + 1) / ‖u‖
      have ht : 0 ≤ t := div_nonneg (by positivity) huNorm.le
      have hρt : ρ t ∈ Rray := ⟨t, ht, rfl⟩
      have hdist := hC hpRay hρt
      have hdistEq : dist p (ρ t) = t * ‖u‖ := by
        rw [dist_eq_norm]
        have : p - ρ t = -(t • u) := by simp [ρ]
        rw [this, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
      have hmul : t * ‖u‖ = |C| + 1 := by
        dsimp [t]
        field_simp
      rw [hdistEq, hmul] at hdist
      linarith [le_abs_self C]
    obtain ⟨T, hTne, hTsub, hTconn, hTunbounded, hTside⟩ :=
      JordanExteriorLocalSideUnbounded J S
    obtain ⟨K, hK⟩ := SimpleClosedCurveAsFinitePolygonalSet J
    have hJbounded : Bornology.IsBounded J.carrier := by
      rw [← hK]
      exact (FiniteStraightLineComplexCarrierCompact
        K.carrier K.points K.segments K.carrier_eq).isBounded
    obtain ⟨R, hRpos, hJR⟩ := hJbounded.subset_closedBall_lt 0 0
    let X : Set (EuclideanSpace ℝ (Fin 2)) :=
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) R)ᶜ
    have hXconn : IsConnected X :=
      EuclideanPlaneClosedBallExteriorConnected R hRpos.le
    have hXsub : X ⊆ J.carrierᶜ := by
      dsimp [X]
      exact Set.compl_subset_compl.mpr hJR
    have hRayX : (Rray ∩ X).Nonempty := by
      by_contra hempty
      apply hRayUnbounded
      apply Metric.isBounded_closedBall.subset
      intro z hz
      by_contra hzX
      apply hempty
      exact ⟨z, hz, hzX⟩
    have hTX : (T ∩ X).Nonempty := by
      by_contra hempty
      apply hTunbounded
      apply Metric.isBounded_closedBall.subset
      intro z hz
      by_contra hzX
      apply hempty
      exact ⟨z, hz, hzX⟩
    let C : Set (EuclideanSpace ℝ (Fin 2)) := (Rray ∪ X) ∪ T
    have hRayXconn : IsConnected (Rray ∪ X) :=
      IsConnected.union hRayX hRayConn hXconn
    have hUnionMeet : ((Rray ∪ X) ∩ T).Nonempty := by
      rcases hTX with ⟨z, hzT, hzX⟩
      exact ⟨z, Or.inr hzX, hzT⟩
    refine ⟨C, ?_, ?_, ?_, ?_, ?_⟩
    · exact hRayNonempty.mono (Set.subset_union_left.trans Set.subset_union_left)
    · exact Set.union_subset (Set.union_subset hRaySub hXsub) hTsub
    · exact IsConnected.union hUnionMeet hRayXconn hTconn
    · exact Set.subset_union_left (s := Rray ∪ X) (t := T)
        (Set.subset_union_left (s := Rray) (t := X) hpRay)
    · rcases hTside with hleft | hright
      · left
        rcases hleft with ⟨z, hzT, hzLeft⟩
        exact ⟨z, Set.subset_union_right hzT, hzLeft⟩
      · right
        rcases hright with ⟨z, hzT, hzRight⟩
        exact ⟨z, Set.subset_union_right hzT, hzRight⟩
