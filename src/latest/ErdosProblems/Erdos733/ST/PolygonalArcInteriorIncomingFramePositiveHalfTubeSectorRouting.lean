import ErdosProblems.Erdos733.ST.PolygonalArcCollarCompatibleOrientedTubeData
import ErdosProblems.Erdos733.ST.PlanarRot90CoefficientUniqueness
import ErdosProblems.Erdos733.ST.PlanarRot90LinearCombination

open Set
open Classical
noncomputable section


-- [TABLET NODE: PolygonalArcInteriorIncomingFramePositiveHalfTubeSectorRouting]
lemma PolygonalArcInteriorIncomingFramePositiveHalfTubeSectorRouting
    (γ : PolygonalArc) {η : ℝ}
    (controlRadii : PolygonalArcCollarControlRadii γ η)
    (middleSegments : PolygonalArcCollarMiddleSegmentData γ controlRadii)
    (forbiddenMargins :
      PolygonalArcCollarMiddleForbiddenMargins γ controlRadii middleSegments)
    (compatibleTubes :
      PolygonalArcCollarCompatibleOrientedTubeData γ controlRadii middleSegments
        forbiddenMargins)
    (j : ℕ) (hj : j + 1 < γ.vertices.length)
    (hnext : (j + 1) + 1 < γ.vertices.length)
    (c s : ℝ)
    (hrep : γ.vertices[j + 2] - γ.vertices[j + 1] =
      c • (γ.vertices[j] - γ.vertices[j + 1]) +
        s • PlanarRot90 (γ.vertices[j] - γ.vertices[j + 1]))
    (hpos : 0 < s ∨ s = 0 ∧ c < 0) :
    let sep :=
      compatibleTubes.orientedTubes.toPolygonalArcCollarSeparatedTubeData
    let p : EuclideanSpace ℝ (Fin 2) := γ.vertices[j + 1]
    let u : EuclideanSpace ℝ (Fin 2) := γ.vertices[j] - γ.vertices[j + 1]
    let rho : ℝ := controlRadii.radius ⟨j + 1, hj⟩
    let chart : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
      fun z => p + z 0 • u + z 1 • PlanarRot90 u
    let C : Set (EuclideanSpace ℝ (Fin 2)) :=
      Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (rho / ‖u‖)
    let R : Set (EuclideanSpace ℝ (Fin 2)) :=
      {z | z ∈ C ∧ (z 1 < 0 ∨ 0 < c * z 1 - s * z 0)}
    sep.leftHalf j hj ∩ chart '' C ⊆ chart '' R ∧
      sep.leftHalf (j + 1) hnext ∩ chart '' C ⊆ chart '' R := by
-- BODY
  intro sep p u rho chart C R
  have hdist_prev : 0 < dist γ.vertices[j] γ.vertices[j + 1] := by
    have hsum := controlRadii.adjacent_radii_sum_lt (j := j) hj
    have hleft := controlRadii.radius_pos ⟨j, Nat.lt_of_succ_lt hj⟩
    have hright := controlRadii.radius_pos ⟨j + 1, hj⟩
    nlinarith
  have hu : u ≠ 0 := by
    dsimp [u]
    exact sub_ne_zero.mpr (dist_pos.mp hdist_prev)
  have hchart_inj : Function.Injective chart := by
    intro z w hzw
    have hrep0 :
        (0 : EuclideanSpace ℝ (Fin 2)) =
          (z 0 - w 0) • u + (z 1 - w 1) • PlanarRot90 u := by
      have hzero : chart z - chart w = (0 : EuclideanSpace ℝ (Fin 2)) :=
        sub_eq_zero.mpr hzw
      have hdiff :
          chart z - chart w =
            (z 0 - w 0) • u + (z 1 - w 1) • PlanarRot90 u := by
        apply PiLp.ext
        intro k
        fin_cases k <;> simp [chart] <;> ring
      rw [← hdiff]
      exact hzero.symm
    have hcoeff :=
      PlanarRot90CoefficientUniqueness (d := u)
        (v := (0 : EuclideanSpace ℝ (Fin 2))) hu hrep0
    have hz0 : z 0 = w 0 := by
      have h : z 0 - w 0 = 0 := by
        simpa using hcoeff.1
      linarith
    have hz1 : z 1 = w 1 := by
      have h : z 1 - w 1 = 0 := by
        simpa using hcoeff.2
      linarith
    apply PiLp.ext
    intro k
    fin_cases k
    · exact hz0
    · exact hz1
  constructor
  · rintro x ⟨hxLeft, hxC⟩
    rw [sep.leftHalf_eq j hj] at hxLeft
    rcases hxLeft with ⟨t, _ht, r, hr, hx_eq⟩
    let z : EuclideanSpace ℝ (Fin 2) :=
      WithLp.toLp 2 (fun k : Fin 2 => if k = 0 then 1 - t else -r)
    have hx_chart : x = chart z := by
      rw [hx_eq]
      dsimp [chart, p, u, z]
      rw [compatibleTubes.orientedTubes.normal_eq_positive_quarter_turn j hj]
      apply PiLp.ext
      intro k
      fin_cases k <;> simp [PlanarRot90, AffineMap.lineMap_apply_module] <;> ring
    rcases hxC with ⟨w, hwC, hwx⟩
    have hwz : w = z := hchart_inj (by simpa [hx_chart] using hwx)
    have hzC : z ∈ C := by simpa [hwz] using hwC
    refine ⟨z, ?_, hx_chart.symm⟩
    dsimp [R]
    exact ⟨hzC, Or.inl (by simpa [z] using (by linarith [hr.1] : -r < 0))⟩
  · rintro x ⟨hxLeft, hxC⟩
    rw [sep.leftHalf_eq (j + 1) hnext] at hxLeft
    rcases hxLeft with ⟨t, _ht, r, hr, hx_eq⟩
    let v : EuclideanSpace ℝ (Fin 2) :=
      γ.vertices[j + 2] - γ.vertices[j + 1]
    let z : EuclideanSpace ℝ (Fin 2) :=
      WithLp.toLp 2 (fun k : Fin 2 =>
        if k = 0 then t * c - r * s else t * s + r * c)
    have hrep_v : v = c • u + s • PlanarRot90 u := by
      simpa [v, u] using hrep
    have hrot_v : PlanarRot90 v = (-s) • u + c • PlanarRot90 u := by
      rw [hrep_v]
      exact PlanarRot90LinearCombination u c s
    have hline_next :
        AffineMap.lineMap γ.vertices[j + 1] γ.vertices[j + 1 + 1] t =
          p + t • v := by
      have hidx : j + 1 + 1 = j + 2 := by omega
      apply PiLp.ext
      intro k
      fin_cases k <;> simp [p, v, hidx, AffineMap.lineMap_apply_module] <;> ring
    have hnormal_next : sep.normal (j + 1) hnext = PlanarRot90 v := by
      rw [compatibleTubes.orientedTubes.normal_eq_positive_quarter_turn (j + 1) hnext]
      have hidx : j + 1 + 1 = j + 2 := by omega
      apply PiLp.ext
      intro k
      fin_cases k <;> simp [PlanarRot90, v, hidx]
    have hx_chart : x = chart z := by
      calc
        x = AffineMap.lineMap γ.vertices[j + 1] γ.vertices[j + 1 + 1] t +
            r • sep.normal (j + 1) hnext := hx_eq
        _ = p + t • v + r • PlanarRot90 v := by rw [hline_next, hnormal_next]
        _ = chart z := by
          dsimp [chart, z]
          rw [hrot_v, hrep_v]
          apply PiLp.ext
          intro k
          fin_cases k <;> simp [PlanarRot90] <;> ring
    rcases hxC with ⟨w, hwC, hwx⟩
    have hwz : w = z := hchart_inj (by simpa [hx_chart] using hwx)
    have hzC : z ∈ C := by simpa [hwz] using hwC
    have hsq_pos : 0 < c ^ 2 + s ^ 2 := by
      rcases hpos with hspos | ⟨hszero, hcneg⟩
      · nlinarith
      · nlinarith
    refine ⟨z, ?_, hx_chart.symm⟩
    dsimp [R]
    refine ⟨hzC, Or.inr ?_⟩
    have hcross : c * z 1 - s * z 0 = r * (c ^ 2 + s ^ 2) := by
      simp [z]
      ring
    rw [hcross]
    exact mul_pos hr.1 hsq_pos
