import Util.IncidenceGeometry.FinitePointLineAvoidance
import Util.IncidenceGeometry.FinitePolygonalSet
import Util.IncidenceGeometry.PlanarRot90
import Util.IncidenceGeometry.PlanarSphereGateInwardPointAvoidance
import Util.IncidenceGeometry.PolygonalArcOrderedBallCutData

open Classical
noncomputable section

private lemma endpointSide_signed_values_ne
    (sm sp a b : ℝ)
    (hsm : sm = 1 ∨ sm = -1) (hsp : sp = 1 ∨ sp = -1)
    (hsign : sm ≠ sp) (ha : 0 < sm * a) (hb : 0 < sp * b) : a ≠ b := by
  rcases hsm with rfl | rfl <;> rcases hsp with rfl | rfl
  · exact False.elim (hsign rfl)
  · norm_num at ha hb
    linarith
  · norm_num at ha hb
    linarith
  · exact False.elim (hsign rfl)

private lemma endpointSide_contact_subsingleton
    (bridge : PolygonalArc) (H : Set (EuclideanSpace ℝ (Fin 2)))
    (rminus rplus p : EuclideanSpace ℝ (Fin 2))
    (side : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)
    (sm sp : ℝ)
    (hsm : sm = 1 ∨ sm = -1) (hsp : sp = 1 ∨ sp = -1)
    (hsmPos : 0 < sm * side (rminus - p))
    (hspPos : 0 < sp * side (rplus - p))
    (hcontact : ∀ z, z ∈ bridge.relativeInterior → z ∈ H →
      z ∈ openSegment ℝ rminus rplus ∧ sm ≠ sp ∧ side (z - p) = 0) :
    (bridge.relativeInterior ∩ H).Subsingleton := by
  intro z hz w hw
  rcases hcontact z hz.1 hz.2 with ⟨hzMiddle, hsign, hzZero⟩
  rcases hcontact w hw.1 hw.2 with ⟨hwMiddle, _hsign, hwZero⟩
  have hvalues_ne : side (rminus - p) ≠ side (rplus - p) :=
    endpointSide_signed_values_ne sm sp _ _ hsm hsp hsign hsmPos hspPos
  rw [openSegment_eq_image_lineMap] at hzMiddle hwMiddle
  rcases hzMiddle with ⟨tz, _htz, hzEq⟩
  rcases hwMiddle with ⟨tw, _htw, hwEq⟩
  have side_lineMap_sub (a b : EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
      side (AffineMap.lineMap a b t - p) =
        (1 - t) * side (a - p) + t * side (b - p) := by
    have hformula : AffineMap.lineMap a b t - p =
        (1 - t) • (a - p) + t • (b - p) := by
      rw [AffineMap.lineMap_apply_module]
      module
    rw [hformula, map_add, map_smul, map_smul]
    simp [smul_eq_mul]
  have hside_z :
      (1 - tz) * side (rminus - p) + tz * side (rplus - p) = 0 := by
    rw [← side_lineMap_sub, hzEq, hzZero]
  have hside_w :
      (1 - tw) * side (rminus - p) + tw * side (rplus - p) = 0 := by
    rw [← side_lineMap_sub, hwEq, hwZero]
  have hparam : tz = tw := by
    have hprod : (tz - tw) *
        (side (rplus - p) - side (rminus - p)) = 0 := by
      calc
        (tz - tw) * (side (rplus - p) - side (rminus - p)) =
            ((1 - tz) * side (rminus - p) + tz * side (rplus - p)) -
              ((1 - tw) * side (rminus - p) + tw * side (rplus - p)) := by
                ring
        _ = 0 := by rw [hside_z, hside_w]; ring
    rcases mul_eq_zero.mp hprod with hzero | hzero
    · exact sub_eq_zero.mp hzero
    · exact False.elim (hvalues_ne (sub_eq_zero.mp hzero).symm)
  calc
    z = AffineMap.lineMap rminus rplus tz := hzEq.symm
    _ = AffineMap.lineMap rminus rplus tw := by rw [hparam]
    _ = w := hwEq

private lemma endpointSide_contact_certificate
    (bridge : PolygonalArc) (H : Set (EuclideanSpace ℝ (Fin 2)))
    (s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))
    (qminus rminus rplus qplus p : EuclideanSpace ℝ (Fin 2))
    (side : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ)
    (sm sp : ℝ)
    (hsm : sm = 1 ∨ sm = -1) (hsp : sp = 1 ∨ sp = -1)
    (hsmPos : 0 < sm * side (rminus - p))
    (hspPos : 0 < sp * side (rplus - p))
    (hbridgeVertices : bridge.vertices = [qminus, rminus, rplus, qplus])
    (hdirection_ne : s.2 - s.1 ≠ 0)
    (hsideDirection : side (s.2 - s.1) = 0)
    (hcontact : ∀ z, z ∈ bridge.relativeInterior → z ∈ H →
      z ∈ openSegment ℝ rminus rplus ∧ z ∈ openSegment ℝ s.1 s.2 ∧ sm ≠ sp) :
    ∀ z, z ∈ bridge.relativeInterior → z ∈ H →
      ∃ j : ℕ, ∃ hj : j + 1 < bridge.vertices.length,
        z ∈ openSegment ℝ bridge.vertices[j] bridge.vertices[j + 1] ∧
          z ∈ openSegment ℝ s.1 s.2 ∧
            ¬ ∃ c : ℝ,
              s.2 - s.1 = c • (bridge.vertices[j + 1] - bridge.vertices[j]) := by
  intro z hzInterior hzH
  rcases hcontact z hzInterior hzH with ⟨hzMiddle, hzListed, hsign⟩
  have hvalues_ne : side (rminus - p) ≠ side (rplus - p) :=
    endpointSide_signed_values_ne sm sp _ _ hsm hsp hsign hsmPos hspPos
  have hmiddleDirection : side (rplus - rminus) ≠ 0 := by
    have hmap : side (rplus - rminus) =
        side (rplus - p) - side (rminus - p) := by
      rw [map_sub, map_sub, map_sub]
      ring
    rw [hmap]
    exact sub_ne_zero.mpr hvalues_ne.symm
  refine ⟨1, ?_, ?_, hzListed, ?_⟩
  · simpa [hbridgeVertices]
  · simpa [hbridgeVertices] using hzMiddle
  · rintro ⟨c, hc⟩
    have hc' : s.2 - s.1 = c • (rplus - rminus) := by
      simpa [hbridgeVertices] using hc
    have hc_ne : c ≠ 0 := by
      intro hc0
      apply hdirection_ne
      rw [hc', hc0, zero_smul]
    have hparallelMap := congrArg side hc'
    rw [hsideDirection, map_smul] at hparallelMap
    exact (mul_ne_zero hc_ne hmiddleDirection) hparallelMap.symm


lemma EndpointSidePrefixEventBridge
    (Q : PolygonalArc)
    (SelectedSide H Bad : Set (EuclideanSpace ℝ (Fin 2)))
    (K : FinitePolygonalSet)
    (p : EuclideanSpace ℝ (Fin 2)) (radius : ℝ)
    (s : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))
    (D : PolygonalArcOrderedBallCutData Q p radius) :
    IsOpen SelectedSide →
      D.qminus ∈ SelectedSide →
      D.qplus ∈ SelectedSide →
      Convex ℝ (SelectedSide ∩ Metric.ball p radius) →
      K.carrier = H →
      (K.points : Set (EuclideanSpace ℝ (Fin 2))) ⊆ Bad →
      SelectedSide ∩ Bad =
        (∅ : Set (EuclideanSpace ℝ (Fin 2))) →
      s ∈ K.segments →
      p ∈ openSegment ℝ s.1 s.2 →
      Metric.ball p radius ∩ H =
        Metric.ball p radius ∩ segment ℝ s.1 s.2 →
      ∃ (bridge : PolygonalArc) (rminus rplus : EuclideanSpace ℝ (Fin 2)),
        bridge.vertices = [D.qminus, rminus, rplus, D.qplus] ∧
          bridge.source = D.qminus ∧
          bridge.target = D.qplus ∧
          rminus ∈ SelectedSide ∩ Metric.ball p radius ∧
          rplus ∈ SelectedSide ∩ Metric.ball p radius ∧
          bridge.carrier =
            segment ℝ D.qminus rminus ∪
              segment ℝ rminus rplus ∪ segment ℝ rplus D.qplus ∧
          bridge.relativeInterior ⊆
            SelectedSide ∩ Metric.ball p radius ∧
          D.prefixArc.carrier ∩ bridge.carrier = {D.qminus} ∧
          bridge.carrier ∩ D.suffixArc.carrier = {D.qplus} ∧
          (bridge.relativeInterior ∩ H).Subsingleton ∧
          ∀ z, z ∈ bridge.relativeInterior → z ∈ H →
            ∃ j : ℕ, ∃ hj : j + 1 < bridge.vertices.length,
              z ∈ openSegment ℝ bridge.vertices[j] bridge.vertices[j + 1] ∧
                z ∈ openSegment ℝ s.1 s.2 ∧
                ¬ ∃ c : ℝ,
                  s.2 - s.1 =
                    c • (bridge.vertices[j + 1] - bridge.vertices[j]) := by
  intro hSelectedOpen hqminusSelected hqplusSelected hSelectedConvex
    hKcarrier hKpoints hSelectedBad hsK hpOpen hlocal
  let E := EuclideanSpace ℝ (Fin 2)
  have hradius : 0 < radius := by
    have hminus : dist D.qminus p = radius := by
      rw [dist_eq_norm]
      exact D.qminus_mem_sphere
    have hplus : dist D.qplus p = radius := by
      rw [dist_eq_norm]
      exact D.qplus_mem_sphere
    have hr_nonneg : 0 ≤ radius := by
      rw [← hminus]
      exact dist_nonneg
    apply lt_of_le_of_ne hr_nonneg
    intro hr_zero
    have hqm : D.qminus = p :=
      dist_eq_zero.mp (hminus.trans hr_zero.symm)
    have hqp : D.qplus = p :=
      dist_eq_zero.mp (hplus.trans hr_zero.symm)
    exact D.qminus_ne_qplus (hqm.trans hqp.symm)
  let direction : E := s.2 - s.1
  have hdirection_ne : direction ≠ 0 :=
    sub_ne_zero.mpr (K.segment_nondegenerate s hsK).symm
  let sideLinear : E →ₗ[ℝ] ℝ :=
    (direction 0) • EuclideanSpace.projₗ (𝕜 := ℝ) (ι := Fin 2) 1 -
      (direction 1) • EuclideanSpace.projₗ (𝕜 := ℝ) (ι := Fin 2) 0
  let side : E →L[ℝ] ℝ := sideLinear.toContinuousLinearMap
  have side_apply : ∀ x : E,
      side x = direction 0 * x 1 - direction 1 * x 0 := by
    intro x
    change direction 0 * x 1 - direction 1 * x 0 =
      direction 0 * x 1 - direction 1 * x 0
    rfl
  let normal : E := PlanarRot90 direction
  have hdirection_sq : 0 < direction 0 * direction 0 + direction 1 * direction 1 := by
    have hcoord : direction 0 ≠ 0 ∨ direction 1 ≠ 0 := by
      by_contra h
      push Not at h
      apply hdirection_ne
      apply PiLp.ext
      intro i
      fin_cases i <;> simp [h.1, h.2]
    rcases hcoord with h0 | h1
    · nlinarith [sq_pos_of_ne_zero h0]
    · nlinarith [sq_pos_of_ne_zero h1]
  have hside_normal : 0 < side normal := by
    rw [side_apply]
    simp [normal, PlanarRot90]
    simpa [mul_comm] using hdirection_sq
  have hp_on_support : side (p - p) = 0 := by simp
  have hs1_on_support : side (s.1 - p) = 0 := by
    rw [openSegment_eq_image_lineMap] at hpOpen
    rcases hpOpen with ⟨u, hu, hpEq⟩
    have hcoordEq := congrArg side (congrArg (fun x : E => x - p) hpEq)
    rw [map_sub, map_sub] at hcoordEq
    have hside_direction : side direction = 0 := by
      rw [side_apply]
      ring
    have hp_formula : p - p = (1 - u) • (s.1 - p) + u • (s.2 - p) := by
      rw [← hpEq, AffineMap.lineMap_apply_module]
      module
    have hdir_formula : s.2 - p = (s.1 - p) + direction := by
      dsimp [direction]
      module
    have heq : 0 = side (s.1 - p) := by
      have hmap := congrArg side hp_formula
      rw [map_add, map_smul, map_smul, hp_on_support, hdir_formula,
        map_add, hside_direction, add_zero] at hmap
      simp only [smul_eq_mul] at hmap
      nlinarith
    exact heq.symm
  have hs2_on_support : side (s.2 - p) = 0 := by
    have hside_direction : side direction = 0 := by
      rw [side_apply]
      ring
    have hdir_formula : s.2 - p = (s.1 - p) + direction := by
      dsimp [direction]
      module
    rw [hdir_formula, map_add, hs1_on_support, hside_direction, add_zero]
  let signCoeff : E → ℝ := fun q => if 0 ≤ side (q - p) then 1 else -1
  have signCoeff_cases : ∀ q : E, signCoeff q = 1 ∨ signCoeff q = -1 := by
    intro q
    dsimp [signCoeff]
    split_ifs <;> simp
  have signCoeff_sq : ∀ q : E, signCoeff q * signCoeff q = 1 := by
    intro q
    rcases signCoeff_cases q with h | h <;> rw [h] <;> norm_num
  have signCoeff_gate_nonneg : ∀ q : E,
      0 ≤ (signCoeff q) * side (q - p) := by
    intro q
    dsimp [signCoeff]
    split_ifs with h
    · simpa using h
    · have hneg : side (q - p) < 0 := lt_of_not_ge h
      nlinarith
  have signed_normal_pos : ∀ q : E,
      0 < ((signCoeff q) • side) ((signCoeff q) • normal) := by
    intro q
    rw [map_smul]
    simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
    rw [← mul_assoc, signCoeff_sq, one_mul]
    simpa using hside_normal
  obtain ⟨epsMinus, hepsMinus, hballMinusSelected⟩ :=
    (Metric.isOpen_iff.mp hSelectedOpen) D.qminus hqminusSelected
  obtain ⟨epsPlus, hepsPlus, hballPlusSelected⟩ :=
    (Metric.isOpen_iff.mp hSelectedOpen) D.qplus hqplusSelected
  have hgateDist : 0 < dist D.qminus D.qplus :=
    dist_pos.mpr D.qminus_ne_qplus
  let gateRadius : ℝ :=
    min (dist D.qminus D.qplus / 3) (min epsMinus epsPlus)
  have hgateRadius : 0 < gateRadius := by
    dsimp [gateRadius]
    exact lt_min (div_pos hgateDist (by norm_num)) (lt_min hepsMinus hepsPlus)
  have hgateRadius_dist : gateRadius ≤ dist D.qminus D.qplus / 3 :=
    min_le_left _ _
  have hgateRadius_epsMinus : gateRadius ≤ epsMinus :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have hgateRadius_epsPlus : gateRadius ≤ epsPlus :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  have hgateBallsDisjoint :
      Disjoint (Metric.ball D.qminus gateRadius)
        (Metric.ball D.qplus gateRadius) := by
    apply Metric.ball_disjoint_ball
    linarith
  have line_dim_test : ∀ (u v : E), u ≠ v →
      ((affineSpan ℝ ({u, v} : Set E) : Set E).Nonempty ∧
        Module.finrank ℝ (affineSpan ℝ ({u, v} : Set E)).direction = 1) := by
    intro u v huv
    constructor
    · exact ⟨u, left_mem_affineSpan_pair ℝ u v⟩
    · rw [direction_affineSpan, vectorSpan_pair]
      exact finrank_span_singleton (sub_ne_zero.mpr huv)
  let firstLine : AffineSubspace ℝ E :=
    affineSpan ℝ ({D.qminus, D.qplus} : Set E)
  let firstLines : Finset (AffineSubspace ℝ E) := {firstLine}
  have hfirstLines : ∀ ℓ ∈ firstLines,
      (ℓ : Set E).Nonempty ∧ Module.finrank ℝ ℓ.direction = 1 := by
    intro ℓ hℓ
    simp only [firstLines, Finset.mem_singleton] at hℓ
    subst ℓ
    exact line_dim_test D.qminus D.qplus D.qminus_ne_qplus
  obtain ⟨rminus, hrminusGate, hrminusSide, hrminusPoints, hrminusLines⟩ :=
    PlanarSphereGateInwardPointAvoidance p D.qminus radius
      (Metric.ball D.qminus gateRadius)
      ((signCoeff D.qminus) • side) ((signCoeff D.qminus) • normal)
      K.points firstLines hradius D.qminus_mem_sphere Metric.isOpen_ball
      (Metric.mem_ball_self hgateRadius)
      (by
        simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
        exact signCoeff_gate_nonneg D.qminus)
      (signed_normal_pos D.qminus) hfirstLines
  have hrminusSelected : rminus ∈ SelectedSide :=
    hballMinusSelected (Metric.ball_subset_ball hgateRadius_epsMinus hrminusGate.1)
  have hrminusBall : rminus ∈ Metric.ball p radius := hrminusGate.2
  have hrminusSigned : 0 < signCoeff D.qminus * side (rminus - p) := by
    simpa [smul_eq_mul] using hrminusSide
  have hqminus_ne_rminus : D.qminus ≠ rminus := by
    intro h
    have hnot := Metric.sphere_disjoint_ball.ne_of_mem
      D.qminus_mem_sphere hrminusBall
    exact hnot h
  have hrminus_ne_qplus : rminus ≠ D.qplus := by
    intro h
    have hnot := Metric.sphere_disjoint_ball.ne_of_mem
      D.qplus_mem_sphere hrminusBall
    exact hnot h.symm
  let secondLineLeft : AffineSubspace ℝ E :=
    affineSpan ℝ ({D.qminus, rminus} : Set E)
  let secondLineRight : AffineSubspace ℝ E :=
    affineSpan ℝ ({rminus, D.qplus} : Set E)
  let secondLines : Finset (AffineSubspace ℝ E) :=
    {secondLineLeft, secondLineRight}
  have hsecondLines : ∀ ℓ ∈ secondLines,
      (ℓ : Set E).Nonempty ∧ Module.finrank ℝ ℓ.direction = 1 := by
    intro ℓ hℓ
    simp only [secondLines, Finset.mem_insert, Finset.mem_singleton] at hℓ
    rcases hℓ with rfl | rfl
    · exact line_dim_test D.qminus rminus hqminus_ne_rminus
    · exact line_dim_test rminus D.qplus hrminus_ne_qplus
  obtain ⟨rplus, hrplusGate, hrplusSide, hrplusPoints, hrplusLines⟩ :=
    PlanarSphereGateInwardPointAvoidance p D.qplus radius
      (Metric.ball D.qplus gateRadius)
      ((signCoeff D.qplus) • side) ((signCoeff D.qplus) • normal)
      K.points secondLines hradius D.qplus_mem_sphere Metric.isOpen_ball
      (Metric.mem_ball_self hgateRadius)
      (by
        simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
        exact signCoeff_gate_nonneg D.qplus)
      (signed_normal_pos D.qplus) hsecondLines
  have hrplusSelected : rplus ∈ SelectedSide :=
    hballPlusSelected (Metric.ball_subset_ball hgateRadius_epsPlus hrplusGate.1)
  have hrplusBall : rplus ∈ Metric.ball p radius := hrplusGate.2
  have hrplusSigned : 0 < signCoeff D.qplus * side (rplus - p) := by
    simpa [smul_eq_mul] using hrplusSide
  have hrminus_ne_rplus : rminus ≠ rplus := by
    intro h
    exact Set.disjoint_left.mp hgateBallsDisjoint hrminusGate.1
      (by simpa [h] using hrplusGate.1)
  have hrplus_ne_qplus : rplus ≠ D.qplus := by
    intro h
    have hnot := Metric.sphere_disjoint_ball.ne_of_mem
      D.qplus_mem_sphere hrplusBall
    exact hnot h.symm
  have hrplus_not_leftLine : rplus ∉ (secondLineLeft : Set E) :=
    hrplusLines secondLineLeft (by simp [secondLines])
  have hrplus_not_rightLine : rplus ∉ (secondLineRight : Set E) :=
    hrplusLines secondLineRight (by simp [secondLines])
  have hfirstMiddle :
      segment ℝ D.qminus rminus ∩ segment ℝ rminus rplus = {rminus} := by
    have hLI : LinearIndependent ℝ ![D.qminus - rminus, rplus - rminus] := by
      rw [LinearIndependent.pair_iff' (sub_ne_zero.mpr hqminus_ne_rminus)]
      intro c hc
      apply hrplus_not_leftLine
      have hmem := smul_vsub_vadd_mem_affineSpan_pair (k := ℝ)
        (p₁ := rminus) (p₂ := D.qminus) c
      have heq : rminus + c • (D.qminus - rminus) = rplus := by
        rw [hc]
        abel
      have hmem' : rplus ∈ affineSpan ℝ ({rminus, D.qminus} : Set E) := by
        rw [← heq]
        simpa [vsub_eq_sub, add_comm] using hmem
      simpa [secondLineLeft, Set.pair_comm] using hmem'
    have hinter := segment_inter_eq_endpoint_of_linearIndependent_sub
      (𝕜 := ℝ) (c := rminus) (x := D.qminus) (y := rplus) hLI
    simpa [segment_symm, Set.inter_comm] using hinter
  have hmiddleLast :
      segment ℝ rminus rplus ∩ segment ℝ rplus D.qplus = {rplus} := by
    have hLI : LinearIndependent ℝ ![rminus - rplus, D.qplus - rplus] := by
      rw [LinearIndependent.pair_iff' (sub_ne_zero.mpr hrminus_ne_rplus)]
      intro c hc
      apply hrplus_not_rightLine
      by_cases hc_one : c = 1
      · subst c
        have hbad : rminus = D.qplus := by
          have heqsub : rminus - rplus = D.qplus - rplus := by
            simpa using hc
          calc
            rminus = (rminus - rplus) + rplus := by abel
            _ = (D.qplus - rplus) + rplus := by rw [heqsub]
            _ = D.qplus := by abel
        exact False.elim (hrminus_ne_qplus hbad)
      · let t : ℝ := (1 - c)⁻¹
        have honec : 1 - c ≠ 0 := sub_ne_zero.mpr (by
          intro h
          exact hc_one h.symm)
        have heq : AffineMap.lineMap rminus D.qplus t = rplus := by
          apply PiLp.ext
          intro i
          have hcoord := congrArg (fun v : E => v i) hc
          change c * (rminus i - rplus i) = D.qplus i - rplus i at hcoord
          rw [AffineMap.lineMap_apply_module]
          dsimp [t]
          change (1 - (1 - c)⁻¹) * rminus i +
            (1 - c)⁻¹ * D.qplus i = rplus i
          field_simp [honec]
          nlinarith
        rw [← heq]
        exact AffineMap.lineMap_mem_affineSpan_pair t rminus D.qplus
    have hinter := segment_inter_eq_endpoint_of_linearIndependent_sub
      (𝕜 := ℝ) (c := rplus) (x := rminus) (y := D.qplus) hLI
    simpa [segment_symm] using hinter
  have hfirstLast :
      Disjoint (segment ℝ D.qminus rminus) (segment ℝ rplus D.qplus) := by
    apply hgateBallsDisjoint.mono
    · exact (convex_ball D.qminus gateRadius).segment_subset
        (Metric.mem_ball_self hgateRadius) hrminusGate.1
    · exact (convex_ball D.qplus gateRadius).segment_subset
        hrplusGate.1 (Metric.mem_ball_self hgateRadius)
  have hqminus_ne_rplus : D.qminus ≠ rplus := by
    intro h
    exact Set.disjoint_left.mp hfirstLast (left_mem_segment ℝ D.qminus rminus)
      (by simpa [h] using left_mem_segment ℝ rplus D.qplus)
  have hrminus_ne_qplus : rminus ≠ D.qplus := by
    intro h
    exact Set.disjoint_left.mp hfirstLast (right_mem_segment ℝ D.qminus rminus)
      (by simpa [h] using right_mem_segment ℝ rplus D.qplus)
  have hqminus_ne_qplus : D.qminus ≠ D.qplus := by
    intro h
    exact Set.disjoint_left.mp hfirstLast (left_mem_segment ℝ D.qminus rminus)
      (by simpa [h] using right_mem_segment ℝ rplus D.qplus)
  have hqplus_not_open_first :
      D.qplus ∉ openSegment ℝ D.qminus rminus := by
    intro h
    exact Set.disjoint_left.mp hfirstLast
      (openSegment_subset_segment ℝ D.qminus rminus h)
      (right_mem_segment ℝ rplus D.qplus)
  have hrplus_not_open_first : rplus ∉ openSegment ℝ D.qminus rminus := by
    intro h
    exact Set.disjoint_left.mp hfirstLast
      (openSegment_subset_segment ℝ D.qminus rminus h)
      (left_mem_segment ℝ rplus D.qplus)
  have hqminus_not_open_middle :
      D.qminus ∉ openSegment ℝ rminus rplus := by
    intro h
    have hinter : D.qminus ∈
        segment ℝ D.qminus rminus ∩ segment ℝ rminus rplus :=
      ⟨left_mem_segment ℝ D.qminus rminus,
        openSegment_subset_segment ℝ rminus rplus h⟩
    rw [hfirstMiddle] at hinter
    exact hqminus_ne_rminus (by simpa using hinter)
  have hqplus_not_open_middle :
      D.qplus ∉ openSegment ℝ rminus rplus := by
    intro h
    have hinter : D.qplus ∈
        segment ℝ rminus rplus ∩ segment ℝ rplus D.qplus :=
      ⟨openSegment_subset_segment ℝ rminus rplus h,
        right_mem_segment ℝ rplus D.qplus⟩
    rw [hmiddleLast] at hinter
    have heq : D.qplus = rplus := by simpa using hinter
    exact hrplus_ne_qplus heq.symm
  have hqminus_not_open_last :
      D.qminus ∉ openSegment ℝ rplus D.qplus := by
    intro h
    exact Set.disjoint_left.mp hfirstLast
      (left_mem_segment ℝ D.qminus rminus)
      (openSegment_subset_segment ℝ rplus D.qplus h)
  have hrminus_not_open_last : rminus ∉ openSegment ℝ rplus D.qplus := by
    intro h
    exact Set.disjoint_left.mp hfirstLast
      (right_mem_segment ℝ D.qminus rminus)
      (openSegment_subset_segment ℝ rplus D.qplus h)
  let bridge : PolygonalArc :=
    { vertices := [D.qminus, rminus, rplus, D.qplus]
      length_ge_two := by norm_num
      source := D.qminus
      target := D.qplus
      source_eq_head := by simp
      target_eq_last := by simp
      carrier :=
        segment ℝ D.qminus rminus ∪
          segment ℝ rminus rplus ∪ segment ℝ rplus D.qplus
      relativeInterior :=
        (segment ℝ D.qminus rminus ∪
            segment ℝ rminus rplus ∪ segment ℝ rplus D.qplus) \
          ({D.qminus, D.qplus} : Set E)
      carrier_eq := by
        ext z
        constructor
        · intro hz
          rcases hz with (hz | hz) | hz
          · exact ⟨0, by norm_num, by simpa using hz⟩
          · exact ⟨1, by norm_num, by simpa using hz⟩
          · exact ⟨2, by norm_num, by simpa using hz⟩
        · rintro ⟨i, hi, hz⟩
          have hi' : i + 1 < 4 := by simpa using hi
          have hi_cases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
          rcases hi_cases with rfl | rfl | rfl
          · exact Or.inl (Or.inl (by simpa using hz))
          · exact Or.inl (Or.inr (by simpa using hz))
          · exact Or.inr (by simpa using hz)
      relativeInterior_eq := rfl
      simple_vertices := by
        simp [hqminus_ne_rminus, hrminus_ne_rplus, hrplus_ne_qplus,
          hqminus_ne_rplus, hqminus_ne_qplus, hrminus_ne_qplus]
      segment_intersections := by
        intro i j hi hj hij
        have hi' : i + 1 < 4 := by simpa using hi
        have hj' : j + 1 < 4 := by simpa using hj
        have hi_cases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
        have hj_cases : j = 0 ∨ j = 1 ∨ j = 2 := by omega
        rcases hi_cases with rfl | rfl | rfl <;>
            rcases hj_cases with rfl | rfl | rfl
        · omega
        · simpa using hfirstMiddle
        · simpa [show (2 : ℕ) ≠ 0 + 1 by omega] using hfirstLast.inter_eq
        · omega
        · omega
        · simpa using hmiddleLast
        · omega
        · omega
        · omega
      vertices_avoid_nonincident_interiors := by
        intro i k hi hk hki hkine
        have hi' : i + 1 < 4 := by simpa using hi
        have hk' : k < 4 := by simpa using hk
        have hi_cases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
        have hk_cases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
        rcases hi_cases with rfl | rfl | rfl
        · rcases hk_cases with rfl | rfl | rfl | rfl
          · exact (hki rfl).elim
          · exact (hkine rfl).elim
          · simpa using hrplus_not_open_first
          · simpa using hqplus_not_open_first
        · rcases hk_cases with rfl | rfl | rfl | rfl
          · simpa using hqminus_not_open_middle
          · exact (hki rfl).elim
          · exact (hkine rfl).elim
          · simpa using hqplus_not_open_middle
        · rcases hk_cases with rfl | rfl | rfl | rfl
          · simpa using hqminus_not_open_last
          · simpa using hrminus_not_open_last
          · exact (hki rfl).elim
          · exact (hkine rfl).elim }
  have hbridgeVertices : bridge.vertices =
      [D.qminus, rminus, rplus, D.qplus] := rfl
  have hbridgeSource : bridge.source = D.qminus := rfl
  have hbridgeTarget : bridge.target = D.qplus := rfl
  have hbridgeCarrier : bridge.carrier =
      segment ℝ D.qminus rminus ∪
        segment ℝ rminus rplus ∪ segment ℝ rplus D.qplus := rfl
  have open_of_segment_ne_endpoints :
      ∀ (a b z : E), a ≠ b → z ∈ segment ℝ a b →
        z ≠ a → z ≠ b → z ∈ openSegment ℝ a b := by
    intro a b z hab hz hza hzb
    rw [segment_eq_image_lineMap] at hz
    rcases hz with ⟨t, ht, rfl⟩
    rw [openSegment_eq_image_lineMap]
    have ht0 : t ≠ 0 := by
      intro ht0
      apply hza
      simp [ht0]
    have ht1 : t ≠ 1 := by
      intro ht1
      apply hzb
      simp [ht1]
    exact ⟨t, ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0),
      lt_of_le_of_ne ht.2 ht1⟩, rfl⟩
  have hfirstGateSubset :
      segment ℝ D.qminus rminus ⊆ Metric.ball D.qminus gateRadius :=
    (convex_ball D.qminus gateRadius).segment_subset
      (Metric.mem_ball_self hgateRadius) hrminusGate.1
  have hlastGateSubset :
      segment ℝ rplus D.qplus ⊆ Metric.ball D.qplus gateRadius :=
    (convex_ball D.qplus gateRadius).segment_subset
      hrplusGate.1 (Metric.mem_ball_self hgateRadius)
  have hfirstSelected : segment ℝ D.qminus rminus ⊆ SelectedSide :=
    fun _ hz => hballMinusSelected
      (Metric.ball_subset_ball hgateRadius_epsMinus (hfirstGateSubset hz))
  have hlastSelected : segment ℝ rplus D.qplus ⊆ SelectedSide :=
    fun _ hz => hballPlusSelected
      (Metric.ball_subset_ball hgateRadius_epsPlus (hlastGateSubset hz))
  have hfirstOpenBall :
      openSegment ℝ D.qminus rminus ⊆ Metric.ball p radius := by
    apply openSegment_subset_ball_of_ne
    · exact Metric.sphere_subset_closedBall D.qminus_mem_sphere
    · exact Metric.ball_subset_closedBall hrminusBall
    · exact hqminus_ne_rminus
  have hlastOpenBall :
      openSegment ℝ rplus D.qplus ⊆ Metric.ball p radius := by
    apply openSegment_subset_ball_of_ne
    · exact Metric.ball_subset_closedBall hrplusBall
    · exact Metric.sphere_subset_closedBall D.qplus_mem_sphere
    · exact hrplus_ne_qplus
  have hmiddleSlice :
      segment ℝ rminus rplus ⊆ SelectedSide ∩ Metric.ball p radius :=
    hSelectedConvex.segment_subset ⟨hrminusSelected, hrminusBall⟩
      ⟨hrplusSelected, hrplusBall⟩
  have hbridgeInterior :
      bridge.relativeInterior ⊆ SelectedSide ∩ Metric.ball p radius := by
    intro z hz
    have hz' := hz
    rw [bridge.relativeInterior_eq] at hz'
    have hzCarrier : z ∈
        segment ℝ D.qminus rminus ∪ segment ℝ rminus rplus ∪
          segment ℝ rplus D.qplus := by
      simpa [hbridgeCarrier] using hz'.1
    have hz_ne_qminus : z ≠ D.qminus := by
      intro h
      apply hz'.2
      simp [h, hbridgeSource]
    have hz_ne_qplus : z ≠ D.qplus := by
      intro h
      apply hz'.2
      simp [h, hbridgeTarget]
    rcases hzCarrier with (hzFirst | hzMiddle) | hzLast
    · refine ⟨hfirstSelected hzFirst, ?_⟩
      by_cases hzrm : z = rminus
      · simpa [hzrm] using hrminusBall
      · exact hfirstOpenBall
          (open_of_segment_ne_endpoints D.qminus rminus z
            hqminus_ne_rminus hzFirst hz_ne_qminus hzrm)
    · exact hmiddleSlice hzMiddle
    · refine ⟨hlastSelected hzLast, ?_⟩
      by_cases hzrp : z = rplus
      · simpa [hzrp] using hrplusBall
      · exact hlastOpenBall
          (open_of_segment_ne_endpoints rplus D.qplus z
            hrplus_ne_qplus hzLast hzrp hz_ne_qplus)
  have arc_source_mem_carrier : ∀ Γ : PolygonalArc, Γ.source ∈ Γ.carrier := by
    intro Γ
    rw [Γ.carrier_eq]
    have hseg : 0 + 1 < Γ.vertices.length := by
      have hlen := Γ.length_ge_two
      omega
    refine ⟨0, hseg, ?_⟩
    have hzero : Γ.vertices[0] = Γ.source := by
      have hhead := Γ.source_eq_head
      rw [List.head?_eq_getElem?] at hhead
      rw [List.getElem?_eq_getElem (by omega)] at hhead
      exact Option.some.inj hhead
    rw [hzero]
    exact left_mem_segment ℝ Γ.source Γ.vertices[1]
  have arc_target_mem_carrier : ∀ Γ : PolygonalArc, Γ.target ∈ Γ.carrier := by
    intro Γ
    rw [Γ.carrier_eq]
    let m := Γ.vertices.length - 2
    have hm : m + 1 < Γ.vertices.length := by
      have hlen := Γ.length_ge_two
      dsimp [m]
      omega
    refine ⟨m, hm, ?_⟩
    have hlast : Γ.vertices[m + 1] = Γ.target := by
      have hlast_get := Γ.target_eq_last
      rw [List.getLast?_eq_getElem?] at hlast_get
      have hidx : Γ.vertices.length - 1 < Γ.vertices.length := by
        have hlen := Γ.length_ge_two
        omega
      rw [List.getElem?_eq_getElem hidx] at hlast_get
      have hm_eq : m + 1 = Γ.vertices.length - 1 := by
        dsimp [m]
        omega
      simpa [hm_eq] using Option.some.inj hlast_get
    rw [hlast]
    exact right_mem_segment ℝ Γ.vertices[m] Γ.target
  have hqminusPrefix : D.qminus ∈ D.prefixArc.carrier := by
    rw [← D.prefix_target]
    exact arc_target_mem_carrier D.prefixArc
  have hqplusSuffix : D.qplus ∈ D.suffixArc.carrier := by
    rw [← D.suffix_source]
    exact arc_source_mem_carrier D.suffixArc
  have hqminusBridge : D.qminus ∈ bridge.carrier := by
    rw [hbridgeCarrier]
    exact Or.inl (Or.inl (left_mem_segment ℝ D.qminus rminus))
  have hqplusBridge : D.qplus ∈ bridge.carrier := by
    rw [hbridgeCarrier]
    exact Or.inr (right_mem_segment ℝ rplus D.qplus)
  have hprefixBridge : D.prefixArc.carrier ∩ bridge.carrier = {D.qminus} := by
    apply Set.Subset.antisymm
    · intro z hz
      by_cases hzqm : z = D.qminus
      · simpa [hzqm]
      by_cases hzqp : z = D.qplus
      · exfalso
        exact (Set.disjoint_left.mp D.prefix_suffix_disjoint hz.1)
          (by simpa [hzqp] using hqplusSuffix)
      have hzInterior : z ∈ bridge.relativeInterior := by
        rw [bridge.relativeInterior_eq]
        exact ⟨hz.2, by simpa [hbridgeSource, hbridgeTarget, hzqm, hzqp]⟩
      exact False.elim
        (Set.disjoint_left.mp D.prefix_avoids_ball hz.1
          (hbridgeInterior hzInterior).2)
    · intro z hz
      have hzqm : z = D.qminus := by simpa using hz
      simpa [hzqm] using And.intro hqminusPrefix hqminusBridge
  have hbridgeSuffix : bridge.carrier ∩ D.suffixArc.carrier = {D.qplus} := by
    apply Set.Subset.antisymm
    · intro z hz
      by_cases hzqp : z = D.qplus
      · simpa [hzqp]
      by_cases hzqm : z = D.qminus
      · exfalso
        exact (Set.disjoint_left.mp D.prefix_suffix_disjoint hqminusPrefix)
          (by simpa [hzqm] using hz.2)
      have hzInterior : z ∈ bridge.relativeInterior := by
        rw [bridge.relativeInterior_eq]
        exact ⟨hz.1, by simpa [hbridgeSource, hbridgeTarget, hzqm, hzqp]⟩
      exact False.elim
        (Set.disjoint_left.mp D.suffix_avoids_ball hz.2
          (hbridgeInterior hzInterior).2)
    · intro z hz
      have hzqp : z = D.qplus := by simpa using hz
      simpa [hzqp] using And.intro hqplusBridge hqplusSuffix
  have side_lineMap_sub : ∀ (a b : E) (t : ℝ),
      side (AffineMap.lineMap a b t - p) =
        (1 - t) * side (a - p) + t * side (b - p) := by
    intro a b t
    have hformula : AffineMap.lineMap a b t - p =
        (1 - t) • (a - p) + t • (b - p) := by
      rw [AffineMap.lineMap_apply_module]
      module
    rw [hformula, map_add, map_smul, map_smul]
    simp [smul_eq_mul]
  have side_zero_on_listed_segment : ∀ z : E,
      z ∈ segment ℝ s.1 s.2 → side (z - p) = 0 := by
    intro z hz
    rw [segment_eq_image_lineMap] at hz
    rcases hz with ⟨t, _ht, rfl⟩
    rw [side_lineMap_sub, hs1_on_support, hs2_on_support]
    ring
  have signed_after_left_endpoint :
      ∀ (σ : ℝ) (a b z : E),
        (σ = 1 ∨ σ = -1) →
          0 ≤ σ * side (a - p) →
            0 < σ * side (b - p) →
              a ≠ b → z ∈ segment ℝ a b → z ≠ a →
                0 < σ * side (z - p) := by
    intro σ a b z hσ ha hb hab hz hza
    rw [segment_eq_image_lineMap] at hz
    rcases hz with ⟨t, ht, rfl⟩
    have ht0 : t ≠ 0 := by
      intro ht0
      apply hza
      simp [ht0]
    have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    have hone : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
    rw [side_lineMap_sub]
    rcases hσ with rfl | rfl
    · simp only [one_mul] at ha hb ⊢
      nlinarith
    · simp only [neg_mul] at ha hb ⊢
      nlinarith
  have signed_before_right_endpoint :
      ∀ (σ : ℝ) (a b z : E),
        (σ = 1 ∨ σ = -1) →
          0 < σ * side (a - p) →
            0 ≤ σ * side (b - p) →
              a ≠ b → z ∈ segment ℝ a b → z ≠ b →
                0 < σ * side (z - p) := by
    intro σ a b z hσ ha hb hab hz hzb
    exact signed_after_left_endpoint σ b a z hσ hb ha hab.symm
      (by simpa [segment_symm] using hz) hzb
  have signed_on_middle :
      ∀ (σ : ℝ) (z : E),
        (σ = 1 ∨ σ = -1) →
          0 < σ * side (rminus - p) →
            0 < σ * side (rplus - p) →
              z ∈ segment ℝ rminus rplus →
                0 < σ * side (z - p) := by
    intro σ z hσ hm hpz hz
    by_cases hzrm : z = rminus
    · simpa [hzrm] using hm
    exact signed_after_left_endpoint σ rminus rplus z hσ
      hm.le hpz hrminus_ne_rplus hz hzrm
  have hcontact_data : ∀ z : E,
      z ∈ bridge.relativeInterior → z ∈ H →
        z ∈ openSegment ℝ rminus rplus ∧
          z ∈ openSegment ℝ s.1 s.2 ∧
            signCoeff D.qminus ≠ signCoeff D.qplus ∧
              side (z - p) = 0 := by
    intro z hzInterior hzH
    have hzSlice := hbridgeInterior hzInterior
    have hzListed : z ∈ segment ℝ s.1 s.2 := by
      have hzLocal : z ∈ Metric.ball p radius ∩ H := ⟨hzSlice.2, hzH⟩
      rw [hlocal] at hzLocal
      exact hzLocal.2
    have hzSideZero := side_zero_on_listed_segment z hzListed
    have hzRel := hzInterior
    rw [bridge.relativeInterior_eq] at hzRel
    have hz_ne_qminus : z ≠ D.qminus := by
      intro h
      apply hzRel.2
      simp [h, hbridgeSource]
    have hz_ne_qplus : z ≠ D.qplus := by
      intro h
      apply hzRel.2
      simp [h, hbridgeTarget]
    have hzCarrier : z ∈
        segment ℝ D.qminus rminus ∪ segment ℝ rminus rplus ∪
          segment ℝ rplus D.qplus := by
      simpa [hbridgeCarrier] using hzRel.1
    have hzMiddle : z ∈ segment ℝ rminus rplus := by
      rcases hzCarrier with (hzFirst | hzMiddle) | hzLast
      · have hpos := signed_after_left_endpoint
          (signCoeff D.qminus) D.qminus rminus z
          (signCoeff_cases D.qminus)
          (signCoeff_gate_nonneg D.qminus) hrminusSigned
          hqminus_ne_rminus hzFirst hz_ne_qminus
        rw [hzSideZero, mul_zero] at hpos
        exact False.elim (lt_irrefl 0 hpos)
      · exact hzMiddle
      · have hpos := signed_before_right_endpoint
          (signCoeff D.qplus) rplus D.qplus z
          (signCoeff_cases D.qplus) hrplusSigned
          (signCoeff_gate_nonneg D.qplus) hrplus_ne_qplus hzLast hz_ne_qplus
        rw [hzSideZero, mul_zero] at hpos
        exact False.elim (lt_irrefl 0 hpos)
    have hsign_ne : signCoeff D.qminus ≠ signCoeff D.qplus := by
      intro hsign
      have hrplusSame : 0 < signCoeff D.qminus * side (rplus - p) := by
        simpa [hsign] using hrplusSigned
      have hpos := signed_on_middle (signCoeff D.qminus) z
        (signCoeff_cases D.qminus) hrminusSigned hrplusSame hzMiddle
      rw [hzSideZero, mul_zero] at hpos
      exact lt_irrefl 0 hpos
    have hz_ne_rminus : z ≠ rminus := by
      intro h
      have hpos := hrminusSigned
      rw [← h, hzSideZero, mul_zero] at hpos
      exact lt_irrefl 0 hpos
    have hz_ne_rplus : z ≠ rplus := by
      intro h
      have hpos := hrplusSigned
      rw [← h, hzSideZero, mul_zero] at hpos
      exact lt_irrefl 0 hpos
    have hzMiddleOpen := open_of_segment_ne_endpoints rminus rplus z
      hrminus_ne_rplus hzMiddle hz_ne_rminus hz_ne_rplus
    have hs_ne : s.1 ≠ s.2 := K.segment_nondegenerate s hsK
    have hz_ne_s1 : z ≠ s.1 := by
      intro h
      have hs1Point : s.1 ∈ K.points := (K.segment_endpoints_listed s hsK).1
      have hzBad : z ∈ Bad := hKpoints (by simpa [h] using hs1Point)
      have hzEmpty : z ∈ SelectedSide ∩ Bad := ⟨hzSlice.1, hzBad⟩
      rw [hSelectedBad] at hzEmpty
      exact hzEmpty
    have hz_ne_s2 : z ≠ s.2 := by
      intro h
      have hs2Point : s.2 ∈ K.points := (K.segment_endpoints_listed s hsK).2
      have hzBad : z ∈ Bad := hKpoints (by simpa [h] using hs2Point)
      have hzEmpty : z ∈ SelectedSide ∩ Bad := ⟨hzSlice.1, hzBad⟩
      rw [hSelectedBad] at hzEmpty
      exact hzEmpty
    have hzListedOpen := open_of_segment_ne_endpoints s.1 s.2 z
      hs_ne hzListed hz_ne_s1 hz_ne_s2
    exact ⟨hzMiddleOpen, hzListedOpen, hsign_ne, hzSideZero⟩
  have hcontactSubsingleton :
      (bridge.relativeInterior ∩ H).Subsingleton := by
    apply endpointSide_contact_subsingleton bridge H rminus rplus p side
      (signCoeff D.qminus) (signCoeff D.qplus)
      (signCoeff_cases D.qminus) (signCoeff_cases D.qplus)
      hrminusSigned hrplusSigned
    intro z hzInterior hzH
    rcases hcontact_data z hzInterior hzH with
      ⟨hzMiddle, _hzListed, hsign, hzZero⟩
    exact ⟨hzMiddle, hsign, hzZero⟩
  have hsideListedDirection : side (s.2 - s.1) = 0 := by
    rw [side_apply]
    dsimp [direction]
    ring
  have hcontactCertificate : ∀ z, z ∈ bridge.relativeInterior → z ∈ H →
      ∃ j : ℕ, ∃ hj : j + 1 < bridge.vertices.length,
        z ∈ openSegment ℝ bridge.vertices[j] bridge.vertices[j + 1] ∧
          z ∈ openSegment ℝ s.1 s.2 ∧
            ¬ ∃ c : ℝ,
              s.2 - s.1 = c • (bridge.vertices[j + 1] - bridge.vertices[j]) := by
    apply endpointSide_contact_certificate bridge H s D.qminus rminus rplus D.qplus p side
      (signCoeff D.qminus) (signCoeff D.qplus)
      (signCoeff_cases D.qminus) (signCoeff_cases D.qplus)
      hrminusSigned hrplusSigned hbridgeVertices hdirection_ne hsideListedDirection
    intro z hzInterior hzH
    rcases hcontact_data z hzInterior hzH with
      ⟨hzMiddle, hzListed, hsign, _hzZero⟩
    exact ⟨hzMiddle, hzListed, hsign⟩
  refine ⟨bridge, rminus, rplus, hbridgeVertices, hbridgeSource,
    hbridgeTarget, ⟨hrminusSelected, hrminusBall⟩,
    ⟨hrplusSelected, hrplusBall⟩, hbridgeCarrier, hbridgeInterior,
    hprefixBridge, hbridgeSuffix, hcontactSubsingleton, hcontactCertificate⟩
