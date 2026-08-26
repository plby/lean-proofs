import ErdosProblems.Erdos633.CyclotomicTilingAngles
import ErdosProblems.Erdos633.TriangleUpperModel

/-!
# Geometric normalization of congruent tilings

Reference isometries may be changed independently of the outer triangle.
A common similarity then fixes scale and outer placement. The angle triples
are preserved without assuming that classical choices of tile isometries
remain identical after changing the reference triangle.
-/

namespace Erdos633

noncomputable def CongruentTiling.changeReferenceIsometry
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N) (e : ℂ ≃ᵢ ℂ) :
    CongruentTiling P (R.mapIsometry e) N where
  toTriangleDissection := T.toTriangleDissection
  congruent := by
    intro i
    obtain ⟨f, hf⟩ := T.congruent i
    refine ⟨e.symm.trans f, ?_⟩
    rw [R.mapIsometry_carrier, Set.image_image]
    have he : (e.symm.trans f) ∘ e = f := by
      funext z
      simp
    change ((e.symm.trans f) ∘ e) '' R.carrier = (T.tile i).carrier
    rw [he]
    exact hf

theorem Triangle.sideLength_mapSimilarity (P : Triangle) (u v : ℂ) (hv : v ≠ 0)
    (k : Fin 3) : (P.mapSimilarity u v hv).sideLength k = ‖v‖ * P.sideLength k := by
  fin_cases k <;>
    exact similarity_dist u v _ _

theorem Triangle.angleA_mapSimilarity (P : Triangle) (u v : ℂ) (hv : v ≠ 0) :
    (P.mapSimilarity u v hv).angleA = P.angleA := by
  apply Real.injOn_cos
    ⟨(P.mapSimilarity u v hv).angleA_pos.le, (P.mapSimilarity u v hv).angleA_lt_pi.le⟩
    ⟨P.angleA_pos.le, P.angleA_lt_pi.le⟩
  rw [(P.mapSimilarity u v hv).cos_angleA_eq_side_ratios, P.cos_angleA_eq_side_ratios]
  simp only [P.sideLength_mapSimilarity]
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hratio (i : Fin 3) : (‖v‖ * P.sideLength i) / (‖v‖ * P.sideLength 2) =
      P.sideLength i / P.sideLength 2 := by field_simp
  rw [hratio 0, hratio 1]

theorem Triangle.rotate_mapSimilarity (P : Triangle) (u v : ℂ) (hv : v ≠ 0) :
    (P.mapSimilarity u v hv).rotate = P.rotate.mapSimilarity u v hv := rfl

theorem Triangle.cornerAngle_mapSimilarity (P : Triangle) (u v : ℂ) (hv : v ≠ 0)
    (k : Fin 3) : (P.mapSimilarity u v hv).cornerAngle k = P.cornerAngle k := by
  fin_cases k
  · exact P.angleA_mapSimilarity u v hv
  · change (P.mapSimilarity u v hv).angleB = P.angleB
    rw [← Triangle.angleA_rotate, P.rotate_mapSimilarity,
      P.rotate.angleA_mapSimilarity, P.angleA_rotate]
  · change (P.mapSimilarity u v hv).angleC = P.angleC
    rw [← Triangle.angleB_rotate, ← Triangle.angleA_rotate,
      P.rotate_mapSimilarity, P.rotate.rotate_mapSimilarity,
      P.rotate.rotate.angleA_mapSimilarity, P.rotate.angleA_rotate, P.angleB_rotate]

theorem Triangle.upperModel_cornerAngle (P : Triangle) (k : Fin 3) :
    P.upperModel.cornerAngle k = P.cornerAngle k := by
  have h := P.cornerAngle_mapIsometry P.upperIsometry k
  rwa [P.map_upperIsometry] at h

theorem Triangle.upperModel_sideLength (P : Triangle) (k : Fin 3) :
    P.upperModel.sideLength k = P.sideLength k := by
  rw [← P.map_upperIsometry]
  fin_cases k <;>
    exact P.upperIsometry.dist_eq _ _

noncomputable def CongruentTiling.upperReference
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N) :
    CongruentTiling P R.upperModel N :=
  (T.changeReferenceIsometry R.upperIsometry).of_reference_carrier_eq
    (congrArg Triangle.carrier R.map_upperIsometry.symm)

theorem Triangle.upperModel_coordinatesIn_of_rotations (R : Triangle) (F : Subfield ℝ)
    (hA : Complex.exp ((R.angleA : ℂ) * Complex.I) ∈ complexCoordinateSubfield F)
    (hB : Complex.exp ((R.angleB : ℂ) * Complex.I) ∈ complexCoordinateSubfield F)
    (hc : R.sideLength 2 ∈ F) : R.upperModel.CoordinatesIn F := by
  have hs := R.sideLengths_mem_of_rotations F hA hB hc
  have hac : dist R.a R.c ∈ F := by
    simpa [Triangle.sideLength, Triangle.edgeStart, Triangle.edgeEnd, dist_comm] using hs 1
  have hab : dist R.a R.b ∈ F := by
    simpa [Triangle.sideLength, Triangle.edgeStart, Triangle.edgeEnd] using hc
  obtain ⟨hcos, hsin⟩ := (exp_angle_mem_complexCoordinateSubfield_iff F R.angleA).mp hA
  intro k
  fin_cases k
  · exact ⟨F.zero_mem, F.zero_mem⟩
  · exact ⟨hab, F.zero_mem⟩
  · exact ⟨F.mul_mem hac hcos, F.mul_mem hac hsin⟩

theorem Triangle.unit_base_of_real_endpoints (P : Triangle) (x : ℝ) (hx : 0 < x)
    (ha : P.a = 0) (hb : P.b = (x : ℂ)) :
    P.unitEdgeVector 2 = (P.orientationSign : ℂ) := by
  have hs : P.sideLength 2 = x := by
    change dist P.a P.b = x
    rw [ha, hb, dist_zero_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx]
  rw [Triangle.unitEdgeVector, hs, Triangle.orientedEdgeVector, Triangle.edgeVector]
  change x⁻¹ • (P.orientationSign • (P.b - P.a)) = (P.orientationSign : ℂ)
  rw [ha, hb, sub_zero, smul_smul, Complex.real_smul]
  push_cast
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hx
  field_simp [hxC]

theorem CongruentTiling.exists_field_normalization
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N) (F : Subfield ℝ)
    (hA : Complex.exp ((R.angleA : ℂ) * Complex.I) ∈ complexCoordinateSubfield F)
    (hB : Complex.exp ((R.angleB : ℂ) * Complex.I) ∈ complexCoordinateSubfield F) :
    ∃ P' R' : Triangle, ∃ _U : CongruentTiling P' R' N,
      (∀ k : Fin 3, P'.cornerAngle k = P.cornerAngle k) ∧
      (∀ k : Fin 3, R'.cornerAngle k = R.cornerAngle k) ∧
      R'.CoordinatesIn F ∧ P'.a = 0 ∧
      P'.unitEdgeVector 2 ∈ complexCoordinateSubfield F ∧ R'.sideLength 2 = 1 := by
  let r := dist R.a R.b
  let p := dist P.a P.b
  have hr : 0 < r := dist_pos.mpr R.a_ne_b
  have hp : 0 < p := dist_pos.mpr P.a_ne_b
  let x := p / r
  have hx : 0 < x := div_pos hp hr
  let v : ℂ := (x : ℂ) / (P.b - P.a)
  have hd : P.b - P.a ≠ 0 := sub_ne_zero.mpr P.a_ne_b.symm
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hx
  have hv : v ≠ 0 := div_ne_zero hxC hd
  let u := -v * P.a
  let P' := P.mapSimilarity u v hv
  let S := R.mapSimilarity u v hv
  have hvnorm : ‖v‖ = 1 / r := by
    dsimp [v]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx,
      ← dist_eq_norm, dist_comm P.b P.a]
    change (p / r) / p = 1 / r
    field_simp
  have hPa : P'.a = 0 := by dsimp [P', Triangle.mapSimilarity, u]; ring
  have hPb : P'.b = (x : ℂ) := by
    dsimp [P', Triangle.mapSimilarity, u, v]
    field_simp
    ring
  have hSc : S.sideLength 2 = 1 := by
    rw [Triangle.sideLength_mapSimilarity, hvnorm]
    change (1 / r) * r = 1
    field_simp
  have hSA : Complex.exp ((S.angleA : ℂ) * Complex.I) ∈ complexCoordinateSubfield F := by
    rw [Triangle.angleA_mapSimilarity]
    exact hA
  have hSB : Complex.exp ((S.angleB : ℂ) * Complex.I) ∈ complexCoordinateSubfield F := by
    have h := R.cornerAngle_mapSimilarity u v hv 1
    change S.angleB = R.angleB at h
    rw [h]
    exact hB
  let U := (T.mapSimilarity u v hv).upperReference
  refine ⟨P', S.upperModel, U, fun k => P.cornerAngle_mapSimilarity u v hv k,
    fun k => (S.upperModel_cornerAngle k).trans (R.cornerAngle_mapSimilarity u v hv k),
    S.upperModel_coordinatesIn_of_rotations F hSA hSB (by rw [hSc]; exact F.one_mem),
    hPa, ?_, ?_⟩
  · rw [P'.unit_base_of_real_endpoints x hx hPa hPb]
    exact ofReal_mem_complexCoordinateSubfield F (P'.orientationSign_mem_subfield F)
  · rw [S.upperModel_sideLength, hSc]

end Erdos633
