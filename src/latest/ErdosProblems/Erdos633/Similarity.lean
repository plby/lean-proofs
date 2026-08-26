import ErdosProblems.Erdos633.Geometry

/-!
# Transport of triangle tilings under Euclidean similarities

The transport acts on actual closed regions and on the witnessing ambient
isometries, so coverage, disjoint interiors, and congruence are all preserved.
-/

namespace Erdos633

@[ext] theorem Triangle.ext {P Q : Triangle} (ha : P.a = Q.a) (hb : P.b = Q.b)
    (hc : P.c = Q.c) : P = Q := by
  cases P
  cases Q
  cases ha
  cases hb
  cases hc
  rfl

def orientedDoubleArea (a b c : ℂ) : ℝ :=
  (b - a).re * (c - a).im - (b - a).im * (c - a).re

theorem orientedDoubleArea_similarity (u v a b c : ℂ) :
    orientedDoubleArea (u + v * a) (u + v * b) (u + v * c) =
      Complex.normSq v * orientedDoubleArea a b c := by
  simp only [orientedDoubleArea, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.normSq_apply]
  ring

noncomputable def similarityAffineMap (u v : ℂ) : ℂ →ᵃ[ℝ] ℂ where
  toFun z := u + v * z
  linear := LinearMap.mulLeft ℝ v
  map_vadd' z w := by
    simp only [vadd_eq_add, LinearMap.mulLeft_apply]
    ring

noncomputable def similarityEquiv (u v : ℂ) (hv : v ≠ 0) : ℂ ≃ ℂ where
  toFun z := u + v * z
  invFun z := (z - u) / v
  left_inv z := by field_simp; ring
  right_inv z := by field_simp; ring

noncomputable def similarityHomeomorph (u v : ℂ) (hv : v ≠ 0) : ℂ ≃ₜ ℂ where
  toEquiv := similarityEquiv u v hv
  continuous_toFun := continuous_const.add (continuous_const.mul continuous_id)
  continuous_invFun := (continuous_id.sub continuous_const).div_const v

noncomputable def similarityAffineEquiv (u v : ℂ) (hv : v ≠ 0) : ℂ ≃ᵃ[ℝ] ℂ :=
  AffineEquiv.ofBijective (φ := similarityAffineMap u v) (similarityEquiv u v hv).bijective

theorem similarityAffineEquiv_apply (u v : ℂ) (hv : v ≠ 0) (z : ℂ) :
    similarityAffineEquiv u v hv z = u + v * z := rfl

theorem similarity_dist (u v x y : ℂ) :
    dist (u + v * x) (u + v * y) = ‖v‖ * dist x y := by
  rw [dist_eq_norm, dist_eq_norm]
  have heq : u + v * x - (u + v * y) = v * (x - y) := by ring
  rw [heq, norm_mul]

def Triangle.mapSimilarity (T : Triangle) (u v : ℂ) (hv : v ≠ 0) : Triangle where
  a := u + v * T.a
  b := u + v * T.b
  c := u + v * T.c
  nondegenerate := by
    change orientedDoubleArea (u + v * T.a) (u + v * T.b) (u + v * T.c) ≠ 0
    rw [orientedDoubleArea_similarity]
    exact mul_ne_zero (ne_of_gt (Complex.normSq_pos.mpr hv)) T.nondegenerate

theorem Triangle.mapSimilarity_carrier (T : Triangle) (u v : ℂ) (hv : v ≠ 0) :
    (T.mapSimilarity u v hv).carrier = similarityEquiv u v hv '' T.carrier := by
  have h := (similarityAffineMap u v).image_convexHull {T.a, T.b, T.c}
  change (fun z : ℂ => u + v * z) '' convexHull ℝ {T.a, T.b, T.c} =
    convexHull ℝ ((fun z : ℂ => u + v * z) '' {T.a, T.b, T.c}) at h
  change convexHull ℝ {u + v * T.a, u + v * T.b, u + v * T.c} =
    (fun z : ℂ => u + v * z) '' convexHull ℝ {T.a, T.b, T.c}
  simpa only [Set.image_insert_eq, Set.image_singleton] using h.symm

theorem Triangle.mapSimilarity_comp (T : Triangle) (u v : ℂ) (hv : v ≠ 0)
    (x y : ℂ) (hy : y ≠ 0) :
    (T.mapSimilarity u v hv).mapSimilarity x y hy =
      T.mapSimilarity (x + y * u) (y * v) (mul_ne_zero hy hv) := by
  apply Triangle.ext
  · change x + y * (u + v * T.a) = (x + y * u) + (y * v) * T.a
    ring
  · change x + y * (u + v * T.b) = (x + y * u) + (y * v) * T.b
    ring
  · change x + y * (u + v * T.c) = (x + y * u) + (y * v) * T.c
    ring

/-- Similarities carry the interior of a triangle onto the interior of its image. -/
theorem Triangle.mapSimilarity_interior (T : Triangle) (u v : ℂ) (hv : v ≠ 0) :
    interior (T.mapSimilarity u v hv).carrier =
      similarityEquiv u v hv '' interior T.carrier := by
  rw [Triangle.mapSimilarity_carrier]
  exact ((similarityHomeomorph u v hv).image_interior T.carrier).symm

/-- Conjugating an ambient isometry by a similarity is again an isometry. -/
noncomputable def conjugateIsometry (u v : ℂ) (hv : v ≠ 0) (e : ℂ ≃ᵢ ℂ) : ℂ ≃ᵢ ℂ where
  toEquiv := (similarityEquiv u v hv).symm.trans
    (e.toEquiv.trans (similarityEquiv u v hv))
  isometry_toFun := by
    apply Isometry.of_dist_eq
    intro x y
    change dist (u + v * e ((similarityEquiv u v hv).symm x))
      (u + v * e ((similarityEquiv u v hv).symm y)) = dist x y
    rw [similarity_dist, e.dist_eq, ← similarity_dist u v]
    change dist ((similarityEquiv u v hv) ((similarityEquiv u v hv).symm x))
      ((similarityEquiv u v hv) ((similarityEquiv u v hv).symm y)) = dist x y
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]

theorem conjugateIsometry_image (u v : ℂ) (hv : v ≠ 0) (e : ℂ ≃ᵢ ℂ) (s : Set ℂ) :
    conjugateIsometry u v hv e '' (similarityEquiv u v hv '' s) =
      similarityEquiv u v hv '' (e '' s) := by
  rw [Set.image_image, Set.image_image]
  congr 1
  funext z
  change (similarityEquiv u v hv) (e ((similarityEquiv u v hv).symm
    ((similarityEquiv u v hv) z))) = (similarityEquiv u v hv) (e z)
  rw [Equiv.symm_apply_apply]

noncomputable def CongruentTiling.mapSimilarity {P R : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) (u v : ℂ) (hv : v ≠ 0) :
    CongruentTiling (P.mapSimilarity u v hv) (R.mapSimilarity u v hv) N where
  tile i := (T.tile i).mapSimilarity u v hv
  congruent := by
    intro i
    obtain ⟨e, he⟩ := T.congruent i
    refine ⟨conjugateIsometry u v hv e, ?_⟩
    rw [Triangle.mapSimilarity_carrier, conjugateIsometry_image, he,
      Triangle.mapSimilarity_carrier]
  covers := by
    simp only [Triangle.mapSimilarity_carrier]
    rw [← Set.image_iUnion, T.covers]
  disjoint := by
    intro i j hij
    have hi := (similarityHomeomorph u v hv).image_interior (T.tile i).carrier
    have hj := (similarityHomeomorph u v hv).image_interior (T.tile j).carrier
    simp only [Triangle.mapSimilarity_carrier]
    change Disjoint
      (interior ((similarityHomeomorph u v hv) '' (T.tile i).carrier))
      (interior ((similarityHomeomorph u v hv) '' (T.tile j).carrier))
    rw [← hi, ← hj]
    apply Set.disjoint_left.mpr
    rintro z ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    have hyx : y = x := (similarityEquiv u v hv).injective hxy
    subst y
    exact Set.disjoint_left.mp (T.disjoint hij) hx hy

theorem admitsNonsquareTiling_mapSimilarity {P : Triangle}
    (hP : AdmitsNonsquareTiling P) (u v : ℂ) (hv : v ≠ 0) :
    AdmitsNonsquareTiling (P.mapSimilarity u v hv) := by
  obtain ⟨N, R, hN, ⟨T⟩⟩ := hP
  exact ⟨N, R.mapSimilarity u v hv, hN, ⟨T.mapSimilarity u v hv⟩⟩

/-- Relabelling a triangle or otherwise presenting the same closed region does
not change the existence of a congruent tiling. -/
def CongruentTiling.of_carrier_eq {P Q R : Triangle} {N : ℕ}
    (T : CongruentTiling P R N) (hPQ : P.carrier = Q.carrier) :
    CongruentTiling Q R N := { T with covers := T.covers.trans hPQ }

theorem admitsNonsquareTiling_of_carrier_eq {P Q : Triangle}
    (hP : AdmitsNonsquareTiling P) (hPQ : P.carrier = Q.carrier) :
    AdmitsNonsquareTiling Q := by
  obtain ⟨N, R, hN, ⟨T⟩⟩ := hP
  exact ⟨N, R, hN, ⟨T.of_carrier_eq hPQ⟩⟩

end Erdos633
