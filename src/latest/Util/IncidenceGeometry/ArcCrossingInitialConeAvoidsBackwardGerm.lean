import Mathlib.Tactic
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Util.IncidenceGeometry.PlanarRot90CoefficientUniqueness
import Util.IncidenceGeometry.PolygonalArcInitialEndpointCone

open Classical
noncomputable section

lemma ArcCrossingInitialConeAvoidsBackwardGerm
    (δ τ : PolygonalArc) (j : ℕ) (c : EuclideanSpace ℝ (Fin 2))
    (r K₀ : ℝ)
    (hj : j + 1 < δ.vertices.length)
    (hcOpen : c ∈ openSegment ℝ δ.vertices[j] δ.vertices[j + 1])
    (hτvertices : τ.vertices = c :: δ.vertices.drop (j + 1))
    (hτsource : τ.source = c) :
    Disjoint (PolygonalArcInitialEndpointCone τ r K₀) (segment ℝ c δ.vertices[j]) := by
  classical
  rw [Set.disjoint_left]
  intro z hzCone hzBack
  have hτfirst : 1 < τ.vertices.length := Nat.lt_of_succ_le τ.length_ge_two
  have hτone : τ.vertices[1] = δ.vertices[j + 1] := by
    have hdrop : 0 < (δ.vertices.drop (j + 1)).length := by
      simp [List.length_drop]
      omega
    have hget :
        (δ.vertices.drop (j + 1))[0] = δ.vertices[j + 1] := by
      simpa using
        (List.getElem_drop (xs := δ.vertices) (i := j + 1) (j := 0)
          (h := hdrop))
    simpa [hτvertices] using hget
  have hδneq : δ.vertices[j] ≠ δ.vertices[j + 1] := by
    intro hEq
    have hidx : j = j + 1 :=
      (δ.simple_vertices.getElem_inj_iff
        (i := j) (j := j + 1)
        (hi := Nat.lt_of_succ_lt hj) (hj := hj)).1 hEq
    omega
  have hc_ne_right : c ≠ δ.vertices[j + 1] := by
    intro h
    have hright : δ.vertices[j + 1] ∈
        openSegment ℝ δ.vertices[j] δ.vertices[j + 1] := by
      simpa [h] using hcOpen
    exact hδneq
      ((right_mem_openSegment_iff (𝕜 := ℝ)
        (x := δ.vertices[j]) (y := δ.vertices[j + 1])).1 hright)
  let dvec : EuclideanSpace ℝ (Fin 2) := δ.vertices[j + 1] - c
  have hdvec_ne : dvec ≠ 0 := by
    intro h
    exact hc_ne_right (sub_eq_zero.mp h).symm
  rw [PolygonalArcInitialEndpointCone] at hzCone
  rcases hzCone with ⟨q, hq, hzConeEq⟩
  dsimp at hq
  rw [segment_eq_image_lineMap] at hzBack
  rcases hzBack with ⟨u, hu, hzBackEq⟩
  rw [openSegment_eq_image_lineMap] at hcOpen
  rcases hcOpen with ⟨a, ha, hcEq⟩
  have hone_sub_pos : 0 < 1 - a := sub_pos.mpr ha.2
  have hback_dir :
      δ.vertices[j] - c = (-(a / (1 - a))) • dvec := by
    dsimp [dvec]
    rw [← hcEq]
    ext k
    simp [AffineMap.lineMap_apply_module]
    field_simp [ne_of_gt hone_sub_pos]
    ring
  have hcone_vec :
      z - c = q 0 • dvec + q 1 • PlanarRot90 dvec := by
    calc
      z - c =
          (τ.source + q 0 • (τ.vertices[1] - τ.source) +
              q 1 • PlanarRot90 (τ.vertices[1] - τ.source)) - c := by
            simpa [hτfirst, hτsource, hτone, dvec] using
              congrArg (fun w => w - c) hzConeEq.symm
      _ = q 0 • dvec + q 1 • PlanarRot90 dvec := by
            rw [hτsource, hτone]
            dsimp [dvec]
            abel
  have hback_vec :
      z - c =
          (-(u * (a / (1 - a)))) • dvec + (0 : ℝ) • PlanarRot90 dvec := by
    calc
      z - c = AffineMap.lineMap c δ.vertices[j] u - c := by
        simpa [hzBackEq]
      _ = u • (δ.vertices[j] - c) := by
        ext k
        simp [AffineMap.lineMap_apply_module]
        ring
      _ = (-(u * (a / (1 - a)))) • dvec + (0 : ℝ) • PlanarRot90 dvec := by
        rw [hback_dir]
        ext k
        simp
        ring
  have hqcoeff := (PlanarRot90CoefficientUniqueness (d := dvec)
    (v := z - c) hdvec_ne hcone_vec).1
  have hbackcoeff := (PlanarRot90CoefficientUniqueness (d := dvec)
    (v := z - c) (a := -(u * (a / (1 - a)))) (b := 0) hdvec_ne hback_vec).1
  have hq0_eq : q 0 = -(u * (a / (1 - a))) := by
    exact hqcoeff.trans hbackcoeff.symm
  have hnonpos : -(u * (a / (1 - a))) ≤ 0 := by
    have hu_nonneg : 0 ≤ u := hu.1
    have hfrac_nonneg : 0 ≤ a / (1 - a) :=
      div_nonneg (le_of_lt ha.1) (le_of_lt hone_sub_pos)
    nlinarith
  have hq0_pos : 0 < q 0 := hq.1
  linarith
