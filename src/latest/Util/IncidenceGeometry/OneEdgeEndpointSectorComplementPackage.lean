import Mathlib.Tactic
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Util.IncidenceGeometry.FinitePlanarClockwiseSuccessorSectors
import Util.IncidenceGeometry.OneEdgeEndpointGermPositiveRayDistinct
import Util.IncidenceGeometry.PlanarRot90CoefficientUniqueness

open Classical
noncomputable section

lemma OneEdgeEndpointSectorComplementPackage
    (A : Set (EuclideanSpace ℝ (Fin 2)))
    (V : Finset (EuclideanSpace ℝ (Fin 2)))
    (E : Finset (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)))
    (p q : EuclideanSpace ℝ (Fin 2))
    (hA :
      A =
        (V : Set (EuclideanSpace ℝ (Fin 2))) ∪
          ⋃ e : {e // e ∈ E}, segment ℝ e.1.1 e.1.2)
    (hEdgeSource :
      ∀ e : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
        e ∈ E → e.1 ∈ V)
    (hEdgeTarget :
      ∀ e : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
        e ∈ E → e.2 ∈ V)
    (hEdgeNondegenerate :
      ∀ e : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
        e ∈ E → e.1 ≠ e.2)
    (hEdgeOpenInteriorsDisjoint :
      ∀ e f : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
        e ∈ E → f ∈ E → e ≠ f →
          Disjoint (openSegment ℝ e.1 e.2) (openSegment ℝ f.1 f.2))
    (hpV : p ∈ V) (hqV : q ∈ V)
    (hpq : p ≠ q)
    (hNewInteriorDisjoint : Disjoint (openSegment ℝ p q) A)
    (r : ℝ) (hr_pos : 0 < r)
    (hr_vertices :
      ∀ v : EuclideanSpace ℝ (Fin 2),
        v ∈ V → v ≠ p → v ∉ Metric.ball p r)
    (hr_nonincident_edges :
      ∀ e : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2),
        e ∈ E → e.1 ≠ p → e.2 ≠ p →
          Disjoint (Metric.ball p r) (segment ℝ e.1 e.2)) :
    let Incident :=
      {e : {e // e ∈ E} // e.1.1 = p ∨ e.1.2 = p}
    let u : Option Incident → EuclideanSpace ℝ (Fin 2) :=
      fun i =>
        match i with
        | none => q - p
        | some e =>
            if e.1.1.1 = p then e.1.1.2 - p else e.1.1.1 - p
    ∃ clockwiseNext : Equiv.Perm (Option Incident),
      ∃ fullClockwiseTurn : ℝ,
      ∃ clockwiseTurn : Option Incident → Option Incident → ℝ,
      ∃ sector : Option Incident → Set (EuclideanSpace ℝ (Fin 2)),
        fullClockwiseTurn = 2 * Real.pi ∧
        0 < fullClockwiseTurn ∧
        (∀ i j : Option Incident, 0 < clockwiseTurn i j) ∧
        (∀ i j : Option Incident, clockwiseTurn i j ≤ fullClockwiseTurn) ∧
        (∀ i j : Option Incident, clockwiseTurn i j = fullClockwiseTurn ↔ j = i) ∧
        (∀ i j : Option Incident, j ≠ i →
          clockwiseTurn i (clockwiseNext i) ≤ clockwiseTurn i j) ∧
        (∀ i : Option Incident,
          clockwiseNext i = i ↔ ∀ j : Option Incident, j = i) ∧
        (∀ i : Option Incident,
          IsOpen (sector i) ∧
            IsConnected (sector i) ∧
            sector i ⊆ Metric.ball p r ∧
            sector i ⊆ (A ∪ segment ℝ p q)ᶜ) ∧
        (∀ x : EuclideanSpace ℝ (Fin 2),
          x ∈ Metric.ball p r → x ∈ A → x ≠ p →
            ∃ i : Incident, ∃ t : ℝ, 0 < t ∧ x = p + t • u (some i)) ∧
        (∀ x : EuclideanSpace ℝ (Fin 2),
          x ∈ segment ℝ p q → x ≠ p →
            ∃ t : ℝ, 0 < t ∧ x = p + t • u none) ∧
        (∀ x : EuclideanSpace ℝ (Fin 2),
          x ∈ Metric.ball p r → x ∈ (A ∪ segment ℝ p q)ᶜ →
            ∃ i : Option Incident, x ∈ sector i) := by
  classical
  intro Incident u
  have hpA : p ∈ A := by
    rw [hA]
    exact Or.inl hpV
  have hq_not_ball : q ∉ Metric.ball p r :=
    hr_vertices q hqV hpq.symm
  have hr_le_pq : r ≤ dist p q := by
    by_contra hlt
    have hqball : q ∈ Metric.ball p r := by
      rw [Metric.mem_ball]
      simpa [dist_comm] using lt_of_not_ge hlt
    exact hq_not_ball hqball
  have hgerms :
      (∀ i : Option Incident, u i ≠ 0) ∧
        (∀ {i j : Option Incident},
          (∃ t : ℝ, 0 < t ∧ u j = t • u i) → i = j) := by
    have hraw :=
      OneEdgeEndpointGermPositiveRayDistinct A V E p q hA
        hEdgeNondegenerate hEdgeOpenInteriorsDisjoint hpq hNewInteriorDisjoint
    exact hraw
  have hnew_segment_ray :
      ∀ {x : EuclideanSpace ℝ (Fin 2)},
        x ∈ segment ℝ p q → x ≠ p →
          ∃ t : ℝ, 0 < t ∧ x = p + t • u none := by
    intro x hxseg hxp
    rw [segment_eq_image_lineMap] at hxseg
    rcases hxseg with ⟨t, ht, rfl⟩
    have ht_ne_zero : t ≠ 0 := by
      intro ht0
      apply hxp
      rw [ht0]
      simp [AffineMap.lineMap_apply_module]
    have ht_pos : 0 < t := lt_of_le_of_ne' ht.1 ht_ne_zero
    refine ⟨t, ht_pos, ?_⟩
    rw [AffineMap.lineMap_apply_module]
    dsimp [u]
    module
  have hold_segment_ray :
      ∀ (e : Incident) {x : EuclideanSpace ℝ (Fin 2)},
        x ∈ segment ℝ e.1.1.1 e.1.1.2 → x ≠ p →
          ∃ t : ℝ, 0 < t ∧ x = p + t • u (some e) := by
    intro e x hxseg hxp
    rw [segment_eq_image_lineMap] at hxseg
    rcases hxseg with ⟨t, ht, htx⟩
    by_cases hsrc : e.1.1.1 = p
    · have ht_ne_zero : t ≠ 0 := by
        intro ht0
        apply hxp
        rw [← htx, hsrc, ht0]
        simp [AffineMap.lineMap_apply_module]
      have ht_pos : 0 < t := lt_of_le_of_ne' ht.1 ht_ne_zero
      refine ⟨t, ht_pos, ?_⟩
      rw [← htx, AffineMap.lineMap_apply_module]
      dsimp [u]
      simp [hsrc]
      module
    · have htgt : e.1.1.2 = p := by
        rcases e.2 with hp_left | hp_right
        · exact False.elim (hsrc hp_left)
        · exact hp_right
      have ht_ne_one : t ≠ 1 := by
        intro ht1
        apply hxp
        rw [← htx, htgt, ht1]
        simp [AffineMap.lineMap_apply_module]
      have hone_minus_pos : 0 < 1 - t := sub_pos.mpr (lt_of_le_of_ne ht.2 ht_ne_one)
      refine ⟨1 - t, hone_minus_pos, ?_⟩
      rw [← htx, AffineMap.lineMap_apply_module]
      dsimp [u]
      simp [hsrc, htgt]
      module
  have hnew_ray_segment_of_ball :
      ∀ {x : EuclideanSpace ℝ (Fin 2)} {t : ℝ},
        x ∈ Metric.ball p r → 0 < t → x = p + t • u none →
          x ∈ segment ℝ p q := by
    intro x t hxball ht hxeq
    have hxline : x = AffineMap.lineMap p q t := by
      rw [hxeq, AffineMap.lineMap_apply_module]
      dsimp [u]
      module
    have hdist_lt : t * dist p q < r := by
      have hball' : dist x p < r := by
        simpa [Metric.mem_ball] using hxball
      rw [hxline, dist_lineMap_left] at hball'
      simpa [Real.norm_eq_abs, abs_of_pos ht] using hball'
    have hdist_pos : 0 < dist p q := dist_pos.mpr hpq
    have ht_le_one : t ≤ 1 := by
      nlinarith
    rw [segment_eq_image_lineMap]
    refine ⟨t, ⟨le_of_lt ht, ht_le_one⟩, ?_⟩
    exact hxline.symm
  have hold_ray_segment_of_ball :
      ∀ (e : Incident) {x : EuclideanSpace ℝ (Fin 2)} {t : ℝ},
        x ∈ Metric.ball p r → 0 < t → x = p + t • u (some e) →
          x ∈ segment ℝ e.1.1.1 e.1.1.2 := by
    intro e x t hxball ht hxeq
    by_cases hsrc : e.1.1.1 = p
    · have hotherV : e.1.1.2 ∈ V := hEdgeTarget e.1.1 e.1.2
      have hother_ne : e.1.1.2 ≠ p := by
        intro h
        exact hEdgeNondegenerate e.1.1 e.1.2 (by
          rw [hsrc, h])
      have hother_not_ball : e.1.1.2 ∉ Metric.ball p r :=
        hr_vertices e.1.1.2 hotherV hother_ne
      have hr_le : r ≤ dist p e.1.1.2 := by
        by_contra hlt
        exact hother_not_ball (by
          rw [Metric.mem_ball]
          simpa [dist_comm] using lt_of_not_ge hlt)
      have hxline : x = AffineMap.lineMap p e.1.1.2 t := by
        rw [hxeq, AffineMap.lineMap_apply_module]
        dsimp [u]
        simp [hsrc]
        module
      have hdist_lt : t * dist p e.1.1.2 < r := by
        have hball' : dist x p < r := by
          simpa [Metric.mem_ball] using hxball
        rw [hxline, dist_lineMap_left] at hball'
        simpa [Real.norm_eq_abs, abs_of_pos ht] using hball'
      have hdist_pos : 0 < dist p e.1.1.2 := dist_pos.mpr hother_ne.symm
      have ht_le_one : t ≤ 1 := by
        nlinarith
      rw [segment_eq_image_lineMap]
      refine ⟨t, ⟨le_of_lt ht, ht_le_one⟩, ?_⟩
      simpa [hsrc] using hxline.symm
    · have htgt : e.1.1.2 = p := by
        rcases e.2 with hp_left | hp_right
        · exact False.elim (hsrc hp_left)
        · exact hp_right
      have hotherV : e.1.1.1 ∈ V := hEdgeSource e.1.1 e.1.2
      have hother_ne : e.1.1.1 ≠ p := hsrc
      have hother_not_ball : e.1.1.1 ∉ Metric.ball p r :=
        hr_vertices e.1.1.1 hotherV hother_ne
      have hr_le : r ≤ dist p e.1.1.1 := by
        by_contra hlt
        exact hother_not_ball (by
          rw [Metric.mem_ball]
          simpa [dist_comm] using lt_of_not_ge hlt)
      have hxline : x = AffineMap.lineMap p e.1.1.1 t := by
        rw [hxeq, AffineMap.lineMap_apply_module]
        dsimp [u]
        simp [hsrc]
        module
      have hdist_lt : t * dist p e.1.1.1 < r := by
        have hball' : dist x p < r := by
          simpa [Metric.mem_ball] using hxball
        rw [hxline, dist_lineMap_left] at hball'
        simpa [Real.norm_eq_abs, abs_of_pos ht] using hball'
      have hdist_pos : 0 < dist p e.1.1.1 := dist_pos.mpr hother_ne.symm
      have ht_le_one : t ≤ 1 := by
        nlinarith
      have hxseg' : x ∈ segment ℝ p e.1.1.1 := by
        rw [segment_eq_image_lineMap]
        exact ⟨t, ⟨le_of_lt ht, ht_le_one⟩, hxline.symm⟩
      simpa [htgt, segment_symm] using hxseg'
  have hold_carrier_ball_ray :
      ∀ x : EuclideanSpace ℝ (Fin 2),
        x ∈ Metric.ball p r → x ∈ A → x ≠ p →
          ∃ i : Incident, ∃ t : ℝ, 0 < t ∧ x = p + t • u (some i) := by
    intro x hxball hxA hxp
    rw [hA] at hxA
    rcases hxA with hxV | hxE
    · exact False.elim (hr_vertices x hxV hxp hxball)
    · rcases Set.mem_iUnion.mp hxE with ⟨e, hxseg⟩
      by_cases hsrc : e.1.1 = p
      · let ie : Incident := ⟨e, Or.inl hsrc⟩
        exact ⟨ie, hold_segment_ray ie hxseg hxp⟩
      · by_cases htgt : e.1.2 = p
        · let ie : Incident := ⟨e, Or.inr htgt⟩
          exact ⟨ie, hold_segment_ray ie hxseg hxp⟩
        · exact False.elim
            ((Set.disjoint_left.mp
              (hr_nonincident_edges e.1 e.2 hsrc htgt)) hxball hxseg)
  rcases FinitePlanarClockwiseSuccessorSectors
      (p := p) (ρ := r) (u := u)
      (hρ := hr_pos) (hu := hgerms.1)
      (hposRayDistinct := by
        intro i j hsame
        exact hgerms.2 hsame) with
    ⟨clockwiseNext, fullClockwiseTurn, clockwiseTurn, sector,
      hfull_eq, hfull_pos, hturn_pos, hturn_le, hturn_full, hfirst_after,
      hfixed, hsector_def, hsector_open_connected, hsector_ball,
      hsector_disjoint, hsector_cover⟩
  have hcenter_not_sector :
      ∀ i : Option Incident, p ∉ sector i := by
    intro i hpsec
    by_cases hnext : clockwiseNext i = i
    · have hdef := hsector_def i
      rw [dif_pos hnext] at hdef
      rw [hdef] at hpsec
      exact hpsec.2 (Or.inr rfl)
    · have hdef := hsector_def i
      rw [dif_neg hnext] at hdef
      rcases hdef with ⟨c, s, hcs, hnext_eq, hsec_eq⟩
      rw [hsec_eq] at hpsec
      dsimp at hpsec
      by_cases hspos : 0 < s
      · rw [if_pos hspos] at hpsec
        rcases hpsec with ⟨z, hz, hz_eq⟩
        have hzero :
            z 0 • u i + z 1 • PlanarRot90 (u i) =
              (0 : EuclideanSpace ℝ (Fin 2)) := by
          have h := congrArg (fun y => y - p) hz_eq
          have hcancel :
              p + z 0 • u i + z 1 • PlanarRot90 (u i) - p =
                z 0 • u i + z 1 • PlanarRot90 (u i) := by
            abel
          simpa [hcancel] using h
        have hzcoeff :=
          PlanarRot90CoefficientUniqueness (d := u i) (v := 0) (hgerms.1 i)
            hzero.symm
        have hz1 : z 1 = 0 := by
          simpa using hzcoeff.2
        linarith [hz.2.1]
      · by_cases hsneg : s < 0
        · rw [if_neg hspos, if_pos hsneg] at hpsec
          rcases hpsec with ⟨z, hz, hz_eq⟩
          have hzero :
              z 0 • u i + z 1 • PlanarRot90 (u i) =
                (0 : EuclideanSpace ℝ (Fin 2)) := by
            have h := congrArg (fun y => y - p) hz_eq
            have hcancel :
                p + z 0 • u i + z 1 • PlanarRot90 (u i) - p =
                  z 0 • u i + z 1 • PlanarRot90 (u i) := by
              abel
            simpa [hcancel] using h
          have hzcoeff :=
            PlanarRot90CoefficientUniqueness (d := u i) (v := 0) (hgerms.1 i)
              hzero.symm
          have hz0 : z 0 = 0 := by
            simpa using hzcoeff.1
          have hz1 : z 1 = 0 := by
            simpa using hzcoeff.2
          rcases hz.2 with hz1neg | hline
          · linarith
          · rw [hz0, hz1] at hline
            nlinarith
        · rw [if_neg hspos, if_neg hsneg] at hpsec
          rcases hpsec with ⟨z, hz, hz_eq⟩
          have hzero :
              z 0 • u i + z 1 • PlanarRot90 (u i) =
                (0 : EuclideanSpace ℝ (Fin 2)) := by
            have h := congrArg (fun y => y - p) hz_eq
            have hcancel :
                p + z 0 • u i + z 1 • PlanarRot90 (u i) - p =
                  z 0 • u i + z 1 • PlanarRot90 (u i) := by
              abel
            simpa [hcancel] using h
          have hzcoeff :=
            PlanarRot90CoefficientUniqueness (d := u i) (v := 0) (hgerms.1 i)
              hzero.symm
          have hz1 : z 1 = 0 := by
            simpa using hzcoeff.2
          linarith [hz.2]
  have hsector_compl :
      ∀ i : Option Incident, sector i ⊆ (A ∪ segment ℝ p q)ᶜ := by
    intro i x hxsec hxbad
    have hxball : x ∈ Metric.ball p r := hsector_ball i hxsec
    rcases hxbad with hxA | hxseg
    · by_cases hxp : x = p
      · exact hcenter_not_sector i (by simpa [hxp] using hxsec)
      · rcases hold_carrier_ball_ray x hxball hxA hxp with ⟨j, t, ht, hxray⟩
        exact (Set.disjoint_left.mp (hsector_disjoint i (some j)))
          hxsec ⟨t, ht, hxray⟩
    · by_cases hxp : x = p
      · exact hcenter_not_sector i (by simpa [hxp] using hxsec)
      · rcases hnew_segment_ray hxseg hxp with ⟨t, ht, hxray⟩
        exact (Set.disjoint_left.mp (hsector_disjoint i none))
          hxsec ⟨t, ht, hxray⟩
  have hcover_compl :
      ∀ x : EuclideanSpace ℝ (Fin 2),
        x ∈ Metric.ball p r → x ∈ (A ∪ segment ℝ p q)ᶜ →
          ∃ i : Option Incident, x ∈ sector i := by
    intro x hxball hxcompl
    have hxp : x ≠ p := by
      intro h
      exact hxcompl (Or.inl (by simpa [h] using hpA))
    refine hsector_cover x hxball hxp ?_
    intro i hxray
    cases i with
    | none =>
        rcases hxray with ⟨t, ht, hxeq⟩
        exact hxcompl (Or.inr (hnew_ray_segment_of_ball hxball ht hxeq))
    | some e =>
        rcases hxray with ⟨t, ht, hxeq⟩
        have hxseg : x ∈ segment ℝ e.1.1.1 e.1.1.2 :=
          hold_ray_segment_of_ball e hxball ht hxeq
        have hxA : x ∈ A := by
          rw [hA]
          right
          exact Set.mem_iUnion.2 ⟨e.1, hxseg⟩
        exact hxcompl (Or.inl hxA)
  refine ⟨clockwiseNext, fullClockwiseTurn, clockwiseTurn, sector,
    hfull_eq, hfull_pos, hturn_pos, hturn_le, hturn_full, hfirst_after,
    hfixed, ?_, hold_carrier_ball_ray, ?_, hcover_compl⟩
  · intro i
    exact ⟨(hsector_open_connected i).1, (hsector_open_connected i).2,
      hsector_ball i, hsector_compl i⟩
  · intro x hxseg hxp
    exact hnew_segment_ray hxseg hxp
