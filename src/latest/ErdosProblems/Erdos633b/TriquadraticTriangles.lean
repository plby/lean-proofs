import ErdosProblems.Erdos633b.PlanarMotions
import ErdosProblems.Erdos633b.TriquadraticRegions
import ErdosProblems.Erdos633b.Scaling

/-! The actual outer triangle and its three rigidly placed enlarged reference triangles. -/

namespace Erdos633b.TriquadraticCoordinates

theorem swapped_normalized_independent (c x y : ℝ) (hc : c ≠ 0) (hy : y ≠ 0) :
    AffineIndependent ℝ ![(0 : Plane), !₂[x, y], !₂[c, 0]] := by
  have h := (normalized_independent c x y hc hy).comp_embedding
    (Equiv.swap (1 : Fin 3) 2).toEmbedding
  convert h using 1
  funext i
  fin_cases i <;> simp [Equiv.swap_apply_def, Fin.ext_iff]

noncomputable def outer (c s d : ℝ) (hc : 0 < c) (hs : 0 < s) (hs1 : s < 1)
    (hd : 0 < d) : Triangle where
  points := ![0, bigB c s d, bigC c s]
  independent := by
    have ht := parameter_denominator_pos s hs hs1
    have hbase : 0 < c ^ 2 * (1 - s ^ 2) := mul_pos (sq_pos_of_pos hc) ht.1
    have hheight : 0 < c ^ 2 * ((2 - s ^ 2) * s * d / 2) :=
      mul_pos (sq_pos_of_pos hc) (div_pos (mul_pos (mul_pos ht.2 hs) hd) (by norm_num))
    have h := swapped_normalized_independent (c ^ 2 * (1 - s ^ 2))
      (c ^ 2 * (1 - 2 * s ^ 2 + s ^ 4 / 2))
      (c ^ 2 * ((2 - s ^ 2) * s * d / 2)) hbase.ne' hheight.ne'
    convert h using 1
    funext i
    fin_cases i <;> ext j <;> fin_cases j <;> simp [bigB, bigC, w]

noncomputable def firstTriangle (c s d : ℝ) (hc : 0 < c) (hs : 0 < s) (hs1 : s < 1)
    (hd : 0 < d) : Triangle :=
  (reference c s d hc hs hs1 hd).homothetic 0 (c * (1 - s ^ 2))
    (mul_pos hc (parameter_denominator_pos s hs hs1).1).ne'

noncomputable def secondTriangle (c s d : ℝ) (hc : 0 < c) (hs : 0 < s) (hs1 : s < 1)
    (hd : 0 < d) (he : d ^ 2 = 4 - s ^ 2) : Triangle :=
  (firstTriangle c s d hc hs hs1 hd).move (mirror s d he).toAffineIsometryEquiv

noncomputable def thirdMotion (c s d : ℝ) (he : d ^ 2 = 4 - s ^ 2) :
    Plane ≃ᵃⁱ[ℝ] Plane :=
  (turn s d he).toAffineIsometryEquiv.trans (AffineIsometryEquiv.constVAdd ℝ Plane (bigC c s))

noncomputable def thirdTriangle (c s d : ℝ) (hc : 0 < c) (hs : 0 < s) (hs1 : s < 1)
    (hd : 0 < d) (he : d ^ 2 = 4 - s ^ 2) : Triangle :=
  ((reference c s d hc hs hs1 hd).homothetic 0 (c * s) (mul_pos hc hs).ne').move
    (thirdMotion c s d he)

theorem firstTriangle_points (c s d : ℝ) (hc : 0 < c) (hs : 0 < s) (hs1 : s < 1)
    (hd : 0 < d) :
    (firstTriangle c s d hc hs hs1 hd).points = ![0, bigC c s, centerQ c s d] := by
  funext i
  rw [firstTriangle, Triangle.homothetic_points, AffineMap.homothety_apply]
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [reference, bigC, centerQ, z] <;> ring

theorem mirror_bigC (c s d : ℝ) (he : d ^ 2 = 4 - s ^ 2) :
    mirror s d he (bigC c s) = sideD c s d := by
  ext i
  fin_cases i <;> simp [mirror, reflection, reflectionMap, bigC, sideD, bigB, w] <;> ring

theorem mirror_centerQ (c s d : ℝ) (he : d ^ 2 = 4 - s ^ 2) :
    mirror s d he (centerQ c s d) = centerQ c s d := by
  simp only [centerQ, map_smul, mirror_z]

theorem secondTriangle_points (c s d : ℝ) (hc : 0 < c) (hs : 0 < s) (hs1 : s < 1)
    (hd : 0 < d) (he : d ^ 2 = 4 - s ^ 2) :
    (secondTriangle c s d hc hs hs1 hd he).points = ![0, sideD c s d, centerQ c s d] := by
  funext i
  change mirror s d he ((firstTriangle c s d hc hs hs1 hd).points i) = _
  rw [firstTriangle_points]
  fin_cases i <;> simp [mirror_bigC, mirror_centerQ]

theorem thirdTriangle_points (c s d : ℝ) (hc : 0 < c) (hs : 0 < s) (hs1 : s < 1)
    (hd : 0 < d) (he : d ^ 2 = 4 - s ^ 2) :
    (thirdTriangle c s d hc hs hs1 hd he).points = ![bigC c s, sideE c s d, centerQ c s d] := by
  funext i
  change bigC c s + turn s d he
    (((reference c s d hc hs hs1 hd).homothetic 0 (c * s) _).points i) = _
  rw [Triangle.homothetic_points, AffineMap.homothety_apply]
  fin_cases i
  · simp [reference]
  · ext j
    fin_cases j <;> simp [reference, turn, rotation, rotationMap, sideE, bigC] <;> ring
  · have hp : (c * s) • ((reference c s d hc hs hs1 hd).points 2 -ᵥ (0 : Plane)) +ᵥ
        (0 : Plane) =
        (c ^ 2 * s * (1 - s ^ 2)) • z s d := by
      ext j
      fin_cases j <;> simp [reference, z] <;> ring
    change bigC c s + turn s d he
      ((c * s) • ((reference c s d hc hs hs1 hd).points 2 -ᵥ (0 : Plane)) +ᵥ (0 : Plane)) =
        centerQ c s d
    rw [hp]
    exact turn_third_vertex c s d he

theorem outer_coords_combination (c s d : ℝ) (hc : 0 < c) (hs : 0 < s) (hs1 : s < 1)
    (hd : 0 < d) (x y : ℝ) :
    (outer c s d hc hs hs1 hd).coord 1 (x • bigB c s d + y • bigC c s) = x ∧
      (outer c s d hc hs hs1 hd).coord 2 (x • bigB c s d + y • bigC c s) = y :=
  (outer c s d hc hs hs1 hd).coord_origin_combination rfl x y

theorem outer_coords_centerQ (c s d : ℝ) (hc : 0 < c) (hs : 0 < s) (hs1 : s < 1)
    (hd : 0 < d) :
    (outer c s d hc hs hs1 hd).coord 1 (centerQ c s d) =
        (1 - s ^ 2) ^ 2 / (2 - s ^ 2) ∧
      (outer c s d hc hs hs1 hd).coord 2 (centerQ c s d) =
        (1 - s ^ 2) / (2 - s ^ 2) := by
  rw [center_barycentric c s d (parameter_denominator_pos s hs hs1).2.ne']
  exact outer_coords_combination c s d hc hs hs1 hd _ _

theorem outer_coords_sideD (c s d : ℝ) (hc : 0 < c) (hs : 0 < s) (hs1 : s < 1)
    (hd : 0 < d) :
    (outer c s d hc hs hs1 hd).coord 1 (sideD c s d) = 1 - s ^ 2 ∧
      (outer c s d hc hs hs1 hd).coord 2 (sideD c s d) = 0 := by
  simpa only [zero_smul, add_zero, sideD] using
    outer_coords_combination c s d hc hs hs1 hd (1 - s ^ 2) 0

theorem outer_coords_sideE (c s d : ℝ) (hc : 0 < c) (hs : 0 < s) (hs1 : s < 1)
    (hd : 0 < d) :
    (outer c s d hc hs hs1 hd).coord 1 (sideE c s d) = 1 / (2 - s ^ 2) ∧
      (outer c s d hc hs hs1 hd).coord 2 (sideE c s d) =
        (1 - s ^ 2) / (2 - s ^ 2) := by
  rw [sideE_barycentric c s d (parameter_denominator_pos s hs hs1).2.ne']
  exact outer_coords_combination c s d hc hs hs1 hd _ _

theorem three_triangle_supports (c s d : ℝ) (hc : 0 < c) (hs : 0 < s) (hs1 : s < 1)
    (hd : 0 < d) (he : d ^ 2 = 4 - s ^ 2) :
    (firstTriangle c s d hc hs hs1 hd).support =
        TriquadraticPartition.region (outer c s d hc hs hs1 hd) (1 - s ^ 2) .first ∧
      (secondTriangle c s d hc hs hs1 hd he).support =
        TriquadraticPartition.region (outer c s d hc hs hs1 hd) (1 - s ^ 2) .second ∧
      (thirdTriangle c s d hc hs hs1 hd he).support =
        TriquadraticPartition.region (outer c s d hc hs hs1 hd) (1 - s ^ 2) .third := by
  let T := outer c s d hc hs hs1 hd
  let t := 1 - s ^ 2
  let q := (1 - s ^ 2) / (2 - s ^ 2)
  have ht : 0 < t := (parameter_denominator_pos s hs hs1).1
  have ht1 : t < 1 := by dsimp [t]; nlinarith [sq_pos_of_pos hs]
  have hden := (parameter_denominator_pos s hs hs1).2
  have hq : 0 < q := div_pos ht hden
  have hrel : (1 + t) * q = t := by
    dsimp [t, q]
    field_simp
    ring
  have hxA : T.coord 1 0 = 0 := by
    change T.coord 1 (T.points 0) = 0
    simp [Triangle.coord_vertex]
  have hyA : T.coord 2 0 = 0 := by
    change T.coord 2 (T.points 0) = 0
    simp [Triangle.coord_vertex]
  have hxC : T.coord 1 (bigC c s) = 0 := by
    change T.coord 1 (T.points 2) = 0
    simp [Triangle.coord_vertex]
  have hyC : T.coord 2 (bigC c s) = 1 := by
    change T.coord 2 (T.points 2) = 1
    simp [Triangle.coord_vertex]
  have hQ := outer_coords_centerQ c s d hc hs hs1 hd
  have hxQ : T.coord 1 (centerQ c s d) = t * q := by
    rw [hQ.1]
    dsimp [t, q]
    ring
  have hyQ : T.coord 2 (centerQ c s d) = q := hQ.2
  have hD := outer_coords_sideD c s d hc hs hs1 hd
  have hxD : T.coord 1 (sideD c s d) = t := hD.1
  have hyD : T.coord 2 (sideD c s d) = 0 := hD.2
  have hE := outer_coords_sideE c s d hc hs hs1 hd
  have hxE : T.coord 1 (sideE c s d) = 1 - q := by
    rw [hE.1]
    dsimp [q]
    field_simp
    ring
  have hyE : T.coord 2 (sideE c s d) = q := hE.2
  constructor
  · apply TriquadraticPartition.first_support_of_vertices T _ t q ht hq hrel
    · intro i
      rw [firstTriangle_points]
      fin_cases i <;> simp [hxA, hxC, hxQ]
    · intro i
      rw [firstTriangle_points]
      fin_cases i <;> simp [hyA, hyC, hyQ]
  constructor
  · apply TriquadraticPartition.second_support_of_vertices T _ t q ht hq hrel
    · intro i
      rw [secondTriangle_points]
      fin_cases i <;> simp [hxA, hxD, hxQ]
    · intro i
      rw [secondTriangle_points]
      fin_cases i <;> simp [hyA, hyD, hyQ]
  · apply TriquadraticPartition.third_support_of_vertices T _ t q ht ht1 hq hrel
    · intro i
      rw [thirdTriangle_points]
      fin_cases i <;> simp [hxC, hxE, hxQ]
    · intro i
      rw [thirdTriangle_points]
      fin_cases i <;> simp [hyC, hyE, hyQ]

end Erdos633b.TriquadraticCoordinates
