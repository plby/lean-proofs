import ErdosProblems.Erdos633b.Parallelogram
import ErdosProblems.Erdos633b.TriquadraticTriangles

/-! Place the finite parallelogram array in the fourth triquadratic region. -/

namespace Erdos633b

namespace TriquadraticPartition

theorem parallelogram_coordinates (t q : ℝ) (ht : 0 < t) (ht1 : t < 1) (hq : 0 < q)
    (he : (1 + t) * q = t) (u v : ℝ) :
    Closed t .parallelogram (t * q + (1 - t) * u + t * (1 - q) * v) (q * (1 - v)) ↔
      0 ≤ u ∧ u ≤ 1 ∧ 0 ≤ v ∧ v ≤ 1 := by
  have hxysum : t * q + (1 - t) * u + t * (1 - q) * v + q * (1 - v) =
      t + (1 - t) * u := by
    linear_combination (1 - v) * he
  have h1 : 0 ≤ q * (1 - v) ↔ v ≤ 1 := by
    rw [mul_nonneg_iff_of_pos_left hq, sub_nonneg]
  have h2 : (1 + t) * (q * (1 - v)) ≤ t ↔ 0 ≤ v := by
    rw [← sub_nonneg]
    have h : t - (1 + t) * (q * (1 - v)) = t * v := by
      linear_combination (v - 1) * he
    rw [h, mul_nonneg_iff_of_pos_left ht]
  have h3 : t ≤ t + (1 - t) * u ↔ 0 ≤ u := by
    rw [le_add_iff_nonneg_right, mul_nonneg_iff_of_pos_left (sub_pos.mpr ht1)]
  have h4 : t + (1 - t) * u ≤ 1 ↔ u ≤ 1 := by
    rw [← sub_nonneg, show 1 - (t + (1 - t) * u) = (1 - t) * (1 - u) by ring,
      mul_nonneg_iff_of_pos_left (sub_pos.mpr ht1), sub_nonneg]
  change (_ ∧ _ ∧ _ ∧ _) ↔ _
  rw [hxysum, h1, h2, h3, h4]
  tauto

theorem parallelogram_coordinate_inverse (t q : ℝ) (ht : t ≠ 1) (hq : q ≠ 0)
    (he : (1 + t) * q = t) (x y : ℝ) :
    t * q + (1 - t) * ((x + y - t) / (1 - t)) + t * (1 - q) * (1 - y / q) = x ∧
      q * (1 - (1 - y / q)) = y := by
  have htn : 1 - t ≠ 0 := sub_ne_zero.mpr ht.symm
  have hy : q * (1 - (1 - y / q)) = y := by field_simp; ring
  have hsum : t * q + (1 - t) * ((x + y - t) / (1 - t)) +
      t * (1 - q) * (1 - y / q) + q * (1 - (1 - y / q)) = x + y := by
    calc
      _ = t + (1 - t) * ((x + y - t) / (1 - t)) := by
        linear_combination (y / q) * he
      _ = x + y := by field_simp; ring
  exact ⟨by linarith, hy⟩

theorem parallelogram_support_of_vertices (T : Triangle) (t q : ℝ)
    (ht : 0 < t) (ht1 : t < 1) (hq : 0 < q) (he : (1 + t) * q = t)
    (Q E D : Plane)
    (hxQ : T.coord 1 Q = t * q) (hyQ : T.coord 2 Q = q)
    (hxE : T.coord 1 E = 1 - q) (hyE : T.coord 2 E = q)
    (hxD : T.coord 1 D = t) (hyD : T.coord 2 D = 0) :
    parallelogram Q (E - Q) (D - Q) = region T t .parallelogram := by
  have hx (u v : ℝ) : T.coord 1 (Q + u • (E - Q) + v • (D - Q)) =
      t * q + (1 - t) * u + t * (1 - q) * v := by
    rw [affineMap_two_edges, hxQ, hxE, hxD]
    change t * q + u * (1 - q - t * q) + v * (t - t * q) = _
    linear_combination -u * he
  have hy (u v : ℝ) : T.coord 2 (Q + u • (E - Q) + v • (D - Q)) = q * (1 - v) := by
    rw [affineMap_two_edges, hyQ, hyE, hyD]
    change q + u * (q - q) + v * (0 - q) = _
    ring
  ext p
  rw [mem_region]
  constructor
  · rintro ⟨u, v, hu, hu1, hv, hv1, rfl⟩
    rw [hx, hy]
    exact (parallelogram_coordinates t q ht ht1 hq he u v).mpr ⟨hu, hu1, hv, hv1⟩
  · intro hp
    let u := (T.coord 1 p + T.coord 2 p - t) / (1 - t)
    let v := 1 - T.coord 2 p / q
    have hi := parallelogram_coordinate_inverse t q ht1.ne hq.ne' he (T.coord 1 p) (T.coord 2 p)
    have huv : 0 ≤ u ∧ u ≤ 1 ∧ 0 ≤ v ∧ v ≤ 1 := by
      apply (parallelogram_coordinates t q ht ht1 hq he u v).mp
      rwa [hi.1, hi.2]
    refine ⟨u, v, huv.1, huv.2.1, huv.2.2.1, huv.2.2.2, ?_⟩
    apply T.ext_coords
    · rw [hx, hi.1]
    · rw [hy, hi.2]

end TriquadraticPartition

namespace TriquadraticCoordinates

noncomputable def arrayReference (c s d : ℝ) (hc : 0 < c) (hs : 0 < s) (hs1 : s < 1)
    (hd : 0 < d) : Triangle :=
  (reference c s d hc hs hs1 hd).reindex (Equiv.swap 0 1)

noncomputable def arrayMotion (c s d : ℝ) (he : d ^ 2 = 4 - s ^ 2) :
    Plane ≃ᵃⁱ[ℝ] Plane :=
  ((mirror s d he).toAffineIsometryEquiv.trans
    (AffineIsometryEquiv.pointReflection ℝ (0 : Plane))).trans
      (AffineIsometryEquiv.constVAdd ℝ Plane (centerQ c s d + c • w s d))

theorem arrayMotion_apply (c s d : ℝ) (he : d ^ 2 = 4 - s ^ 2) (p : Plane) :
    arrayMotion c s d he p = centerQ c s d + c • w s d - mirror s d he p := by
  simp [arrayMotion, AffineIsometryEquiv.pointReflection_apply, sub_eq_add_neg]

theorem arrayReference_points (c s d : ℝ) (hc : 0 < c) (hs : 0 < s) (hs1 : s < 1)
    (hd : 0 < d) :
    (arrayReference c s d hc hs hs1 hd).points = ![!₂[c, 0], 0, (c * (1 - s ^ 2)) • z s d] := by
  funext i
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [arrayReference, Affine.Simplex.reindex, reference, z]

theorem mirror_ce (c s d : ℝ) (he : d ^ 2 = 4 - s ^ 2) :
    mirror s d he !₂[c, 0] = c • w s d := by
  rw [show (!₂[c, 0] : Plane) = c • (!₂[1, 0] : Plane) by
    ext i; fin_cases i <;> simp]
  rw [map_smul, mirror_e]

theorem array_vertices (c s d : ℝ) (hc : 0 < c) (hs : 0 < s) (hs1 : s < 1)
    (hd : 0 < d) (he : d ^ 2 = 4 - s ^ 2) :
    arrayMotion c s d he ((arrayReference c s d hc hs hs1 hd).points 0) = centerQ c s d ∧
      arrayMotion c s d he ((arrayReference c s d hc hs hs1 hd).points 1) =
        centerQ c s d + c • w s d ∧
      arrayMotion c s d he ((arrayReference c s d hc hs hs1 hd).points 2) =
        centerQ c s d + c • w s d - (c * (1 - s ^ 2)) • z s d := by
  simp [arrayReference_points, arrayMotion_apply, mirror_ce, map_smul, mirror_z]

theorem array_first_edge (c s d : ℝ) (hc : 0 < c) (hs : 0 < s) (hs1 : s < 1)
    (hd : 0 < d) (he : d ^ 2 = 4 - s ^ 2) :
    (c * s ^ 2) •
        (arrayMotion c s d he ((arrayReference c s d hc hs hs1 hd).points 1) -
          arrayMotion c s d he ((arrayReference c s d hc hs hs1 hd).points 0)) =
      sideE c s d - centerQ c s d := by
  obtain ⟨h0, h1, _⟩ := array_vertices c s d hc hs hs1 hd he
  rw [h1, h0, add_sub_cancel_left, parallelogram_first_edge]
  simp only [bigB, smul_smul]
  congr 1
  ring

theorem array_second_edge (c s d : ℝ) (hc : 0 < c) (hs : 0 < s) (hs1 : s < 1)
    (hd : 0 < d) (he : d ^ 2 = 4 - s ^ 2) :
    (c * (1 - s ^ 2)) •
        (arrayMotion c s d he ((arrayReference c s d hc hs hs1 hd).points 2) -
          arrayMotion c s d he ((arrayReference c s d hc hs hs1 hd).points 0)) =
      sideD c s d - centerQ c s d := by
  obtain ⟨h0, _, h2⟩ := array_vertices c s d hc hs hs1 hd he
  rw [h2, h0]
  ext i
  fin_cases i <;> simp [sideD, bigB, centerQ, z, w] <;> ring

theorem fourth_support (c s d : ℝ) (hc : 0 < c) (hs : 0 < s) (hs1 : s < 1) (hd : 0 < d) :
    parallelogram (centerQ c s d) (sideE c s d - centerQ c s d) (sideD c s d - centerQ c s d) =
      TriquadraticPartition.region (outer c s d hc hs hs1 hd) (1 - s ^ 2) .parallelogram := by
  let t := 1 - s ^ 2
  let q := (1 - s ^ 2) / (2 - s ^ 2)
  have ht : 0 < t := (parameter_denominator_pos s hs hs1).1
  have ht1 : t < 1 := by dsimp [t]; nlinarith [sq_pos_of_pos hs]
  have hden := (parameter_denominator_pos s hs hs1).2
  have hq : 0 < q := div_pos ht hden
  have hrel : (1 + t) * q = t := by dsimp [t, q]; field_simp; ring
  apply TriquadraticPartition.parallelogram_support_of_vertices
    (outer c s d hc hs hs1 hd) t q ht ht1 hq hrel
  · rw [(outer_coords_centerQ c s d hc hs hs1 hd).1]
    dsimp [t, q]
    ring
  · exact (outer_coords_centerQ c s d hc hs hs1 hd).2
  · rw [(outer_coords_sideE c s d hc hs hs1 hd).1]
    dsimp [q]
    field_simp
    ring
  · exact (outer_coords_sideE c s d hc hs hs1 hd).2
  · exact (outer_coords_sideD c s d hc hs hs1 hd).1
  · exact (outer_coords_sideD c s d hc hs hs1 hd).2

noncomputable def fourth_patch (c s d : ℝ) (hc : 0 < c) (hs : 0 < s) (hs1 : s < 1)
    (hd : 0 < d) (he : d ^ 2 = 4 - s ^ 2) (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hmv : (m : ℝ) = c * s ^ 2) (hnv : (n : ℝ) = c * (1 - s ^ 2)) :
    Patch (reference c s d hc hs hs1 hd)
      (TriquadraticPartition.region (outer c s d hc hs hs1 hd) (1 - s ^ 2) .parallelogram)
      (2 * m * n) := by
  have patch := parallelogram_patch (arrayReference c s d hc hs hs1 hd)
    (arrayMotion c s d he) m n hm hn
  rw [hmv, hnv, array_first_edge c s d hc hs hs1 hd he,
    array_second_edge c s d hc hs hs1 hd he, (array_vertices c s d hc hs hs1 hd he).1,
    fourth_support c s d hc hs hs1 hd] at patch
  exact patch.changeTile (Triangle.support_reindex (reference c s d hc hs hs1 hd) _)

end TriquadraticCoordinates

end Erdos633b
