import ErdosProblems.Erdos633.Similarity

/-!
# The complete isosceles class

Every nondegenerate isosceles triangle, at any position, orientation, or scale,
has a genuine two-piece congruent tiling. The proof normalizes its base to
`[-1,1]` and transports the canonical altitude dissection back by a similarity.
-/

namespace Erdos633

theorem Triangle.a_ne_b (P : Triangle) : P.a ≠ P.b := by
  intro h
  apply P.nondegenerate
  rw [h]
  simp

theorem Triangle.b_ne_c (T : Triangle) : T.b ≠ T.c := by
  intro h
  apply T.nondegenerate
  rw [h]
  ring

/-- Cyclic relabelling does not change the geometric triangle. -/
def Triangle.rotate (T : Triangle) : Triangle where
  a := T.b
  b := T.c
  c := T.a
  nondegenerate := by
    have h : orientedDoubleArea T.b T.c T.a = orientedDoubleArea T.a T.b T.c := by
      simp only [orientedDoubleArea, Complex.sub_re, Complex.sub_im]
      ring
    change orientedDoubleArea T.b T.c T.a ≠ 0
    rw [h]
    exact T.nondegenerate

theorem Triangle.rotate_carrier (T : Triangle) : T.rotate.carrier = T.carrier := by
  change convexHull ℝ {T.b, T.c, T.a} = convexHull ℝ {T.a, T.b, T.c}
  congr 1
  ext z
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

/-- Equal distances to `-1` and `1` characterize the imaginary axis. -/
theorem re_eq_zero_of_dist_neg_one_eq_dist_one (z : ℂ)
    (hz : dist z (-1) = dist z 1) : z.re = 0 := by
  have hs : Complex.normSq (z - (-1)) = Complex.normSq (z - 1) := by
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    simpa only [dist_eq_norm] using congrArg (fun r : ℝ => r ^ 2) hz
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.neg_re,
    Complex.neg_im, Complex.one_re, Complex.one_im, neg_zero, sub_zero] at hs
  nlinarith

/-- A triangle whose two sides from `a` have the same length is a similarity
image of the canonical isosceles triangle, allowing either sign of its height. -/
theorem Triangle.exists_canonicalIsosceles_similarity (T : Triangle)
    (hleg : dist T.a T.b = dist T.a T.c) :
    ∃ (h : ℝ) (hh : h ≠ 0) (u v : ℂ) (hv : v ≠ 0),
      (canonicalIsosceles h hh).mapSimilarity u v hv = T := by
  let u := (T.b + T.c) / 2
  let v := (T.c - T.b) / 2
  have hv : v ≠ 0 := div_ne_zero (sub_ne_zero.mpr T.b_ne_c.symm) (by norm_num)
  let z := (T.a - u) / v
  have ha : u + v * z = T.a := by
    dsimp [z]
    field_simp
    ring
  have hb : u + v * (-1) = T.b := by dsimp [u, v]; ring
  have hc : u + v * 1 = T.c := by dsimp [u, v]; ring
  have hz : dist z (-1) = dist z 1 := by
    have h := hleg
    rw [← ha, ← hb, ← hc, similarity_dist, similarity_dist] at h
    exact (mul_left_cancel₀ (norm_ne_zero_iff.mpr hv)) h
  have hre := re_eq_zero_of_dist_neg_one_eq_dist_one z hz
  have hzmk : z = (⟨0, z.im⟩ : ℂ) := by
    apply Complex.ext
    · exact hre
    · rfl
  have him : z.im ≠ 0 := by
    intro hzero
    have hz0 : z = 0 := by rw [hzmk, hzero]; rfl
    have hau : T.a = u := by simpa only [hz0, mul_zero, add_zero] using ha.symm
    apply T.nondegenerate
    rw [hau]
    dsimp [u]
    simp only [Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.add_re, Complex.add_im]
    ring
  refine ⟨z.im, him, u, v, hv, ?_⟩
  apply Triangle.ext
  · change u + v * (⟨0, z.im⟩ : ℂ) = T.a
    rw [← hzmk]
    exact ha
  · exact hb
  · exact hc

theorem Triangle.two_tiling_of_equal_legs (T : Triangle)
    (hleg : dist T.a T.b = dist T.a T.c) :
    ∃ R : Triangle, Nonempty (CongruentTiling T R 2) := by
  obtain ⟨h, hh, u, v, hv, hT⟩ := T.exists_canonicalIsosceles_similarity hleg
  refine ⟨(leftHalf h hh).mapSimilarity u v hv, ?_⟩
  rw [← hT]
  exact ⟨(canonicalIsoscelesTwoTiling h hh).mapSimilarity u v hv⟩

/-- At least two of the three side lengths are equal. -/
def Triangle.Isosceles (T : Triangle) : Prop :=
  dist T.a T.b = dist T.a T.c ∨
  dist T.b T.a = dist T.b T.c ∨
  dist T.c T.a = dist T.c T.b

theorem Triangle.two_tiling_of_isosceles (T : Triangle) (hT : T.Isosceles) :
    ∃ R : Triangle, Nonempty (CongruentTiling T R 2) := by
  rcases hT with h | h | h
  · exact T.two_tiling_of_equal_legs h
  · obtain ⟨R, ⟨S⟩⟩ := T.rotate.two_tiling_of_equal_legs h.symm
    exact ⟨R, ⟨S.of_carrier_eq T.rotate_carrier⟩⟩
  · obtain ⟨R, ⟨S⟩⟩ := T.rotate.rotate.two_tiling_of_equal_legs h
    exact ⟨R, ⟨S.of_carrier_eq (T.rotate.rotate_carrier.trans T.rotate_carrier)⟩⟩

theorem Triangle.admitsNonsquareTiling_of_isosceles (T : Triangle) (hT : T.Isosceles) :
    AdmitsNonsquareTiling T := by
  obtain ⟨R, hR⟩ := T.two_tiling_of_isosceles hT
  exact ⟨2, R, by norm_num, hR⟩

end Erdos633
