import ErdosProblems.Erdos633.Coordinates

/-!
# Congruence from the three squared side lengths

The affine coordinate equivalence between two triangles is an ambient
isometry whenever their corresponding squared side lengths agree. This
includes reflected triangles and gives the isometries required by tilings.
-/

namespace Erdos633

def Triangle.swapBC (T : Triangle) : Triangle where
  a := T.a
  b := T.c
  c := T.b
  nondegenerate := by
    change orientedDoubleArea T.a T.c T.b ≠ 0
    have h : orientedDoubleArea T.a T.c T.b = -orientedDoubleArea T.a T.b T.c := by
      simp only [orientedDoubleArea]
      ring
    rw [h]
    exact neg_ne_zero.mpr T.nondegenerate

theorem Triangle.swapBC_carrier (T : Triangle) : T.swapBC.carrier = T.carrier := by
  change convexHull ℝ {T.a, T.c, T.b} = convexHull ℝ {T.a, T.b, T.c}
  congr 1
  ext z
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

def Triangle.swapAB (T : Triangle) : Triangle where
  a := T.b
  b := T.a
  c := T.c
  nondegenerate := by
    change orientedDoubleArea T.b T.a T.c ≠ 0
    have h : orientedDoubleArea T.b T.a T.c = -orientedDoubleArea T.a T.b T.c := by
      simp only [orientedDoubleArea, Complex.sub_re, Complex.sub_im]
      ring
    rw [h]
    exact neg_ne_zero.mpr T.nondegenerate

theorem Triangle.swapAB_carrier (T : Triangle) : T.swapAB.carrier = T.carrier := by
  change convexHull ℝ {T.b, T.a, T.c} = convexHull ℝ {T.a, T.b, T.c}
  congr 1
  ext z
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

def Triangle.swapAC (T : Triangle) : Triangle := T.swapAB.swapBC.swapAB

theorem Triangle.swapAC_carrier (T : Triangle) : T.swapAC.carrier = T.carrier := by
  simp only [Triangle.swapAC, Triangle.swapAB_carrier, Triangle.swapBC_carrier]

theorem Triangle.coordinateEquiv_normSq_sub (T : Triangle) (x y : ℂ) :
    Complex.normSq (T.coordinateEquiv x - T.coordinateEquiv y) =
      (x.re - y.re) ^ 2 * Complex.normSq (T.b - T.a) +
      (x.im - y.im) ^ 2 * Complex.normSq (T.c - T.a) +
      (x.re - y.re) * (x.im - y.im) *
        (Complex.normSq (T.b - T.a) + Complex.normSq (T.c - T.a) -
          Complex.normSq (T.c - T.b)) := by
  simp only [Triangle.coordinateEquiv_apply, Complex.normSq_apply,
    Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
    Complex.smul_re, Complex.smul_im, smul_eq_mul]
  ring

/-- The unique affine map matching the ordered vertices is an isometry
when the three corresponding squared side lengths agree. -/
noncomputable def Triangle.isometryOfNormSq (P Q : Triangle)
    (hab : Complex.normSq (P.b - P.a) = Complex.normSq (Q.b - Q.a))
    (hac : Complex.normSq (P.c - P.a) = Complex.normSq (Q.c - Q.a))
    (hbc : Complex.normSq (P.c - P.b) = Complex.normSq (Q.c - Q.b)) : ℂ ≃ᵢ ℂ where
  toEquiv := P.coordinateEquiv.toEquiv.symm.trans Q.coordinateEquiv.toEquiv
  isometry_toFun := by
    apply Isometry.of_dist_eq
    intro x y
    change dist (Q.coordinateEquiv (P.coordinateEquiv.symm x))
      (Q.coordinateEquiv (P.coordinateEquiv.symm y)) = dist x y
    apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp
    simp only [dist_eq_norm, ← Complex.normSq_eq_norm_sq]
    have hP := P.coordinateEquiv_normSq_sub
      (P.coordinateEquiv.symm x) (P.coordinateEquiv.symm y)
    rw [P.coordinateEquiv.apply_symm_apply, P.coordinateEquiv.apply_symm_apply] at hP
    rw [Q.coordinateEquiv_normSq_sub, hP, hab, hac, hbc]

theorem Triangle.isometryOfNormSq_apply (P Q : Triangle) (hab hac hbc) (z : ℂ) :
    P.isometryOfNormSq Q hab hac hbc z = Q.coordinateEquiv (P.coordinateEquiv.symm z) := rfl

theorem Triangle.isometryOfNormSq_image (P Q : Triangle) (hab hac hbc) :
    P.isometryOfNormSq Q hab hac hbc '' P.carrier = Q.carrier := by
  rw [← Triangle.mapIsometry_carrier]
  congr 1
  apply Triangle.ext
  · change P.isometryOfNormSq Q hab hac hbc P.a = Q.a
    rw [Triangle.isometryOfNormSq_apply, ← P.coordinateEquiv_zero,
      P.coordinateEquiv.symm_apply_apply, Q.coordinateEquiv_zero]
  · change P.isometryOfNormSq Q hab hac hbc P.b = Q.b
    rw [Triangle.isometryOfNormSq_apply, ← P.coordinateEquiv_one,
      P.coordinateEquiv.symm_apply_apply, Q.coordinateEquiv_one]
  · change P.isometryOfNormSq Q hab hac hbc P.c = Q.c
    rw [Triangle.isometryOfNormSq_apply, ← P.coordinateEquiv_I,
      P.coordinateEquiv.symm_apply_apply, Q.coordinateEquiv_I]

theorem Triangle.congruent_of_normSq (P Q : Triangle)
    (hab : Complex.normSq (P.b - P.a) = Complex.normSq (Q.b - Q.a))
    (hac : Complex.normSq (P.c - P.a) = Complex.normSq (Q.c - Q.a))
    (hbc : Complex.normSq (P.c - P.b) = Complex.normSq (Q.c - Q.b)) :
    ∃ e : ℂ ≃ᵢ ℂ, e '' P.carrier = Q.carrier :=
  ⟨P.isometryOfNormSq Q hab hac hbc, P.isometryOfNormSq_image Q hab hac hbc⟩

/-- Applying the same similarity preserves ambient congruence. -/
theorem Triangle.congruent_mapSimilarity {P Q : Triangle}
    (h : ∃ e : ℂ ≃ᵢ ℂ, e '' P.carrier = Q.carrier) (u v : ℂ) (hv : v ≠ 0) :
    ∃ e : ℂ ≃ᵢ ℂ, e '' (P.mapSimilarity u v hv).carrier =
      (Q.mapSimilarity u v hv).carrier := by
  obtain ⟨e, he⟩ := h
  refine ⟨conjugateIsometry u v hv e, ?_⟩
  rw [Triangle.mapSimilarity_carrier, conjugateIsometry_image, he,
    Triangle.mapSimilarity_carrier]

theorem admitsNonsquareTiling_of_congruent {P Q : Triangle}
    (hP : AdmitsNonsquareTiling P) (hPQ : ∃ e : ℂ ≃ᵢ ℂ, e '' P.carrier = Q.carrier) :
    AdmitsNonsquareTiling Q := by
  obtain ⟨N, R, hN, ⟨T⟩⟩ := hP
  obtain ⟨e, he⟩ := hPQ
  exact ⟨N, R, hN, ⟨(T.mapIsometry e).of_carrier_eq
    ((P.mapIsometry_carrier e).trans he)⟩⟩

theorem normSq_similarity_sub (u v x y : ℂ) :
    Complex.normSq ((u + v * x) - (u + v * y)) =
      Complex.normSq v * Complex.normSq (x - y) := by
  rw [show (u + v * x) - (u + v * y) = v * (x - y) by ring, Complex.normSq_mul]

theorem normSq_sub_eq_dist_sq (a b : ℂ) : Complex.normSq (b - a) = dist a b ^ 2 := by
  rw [Complex.normSq_eq_norm_sq, dist_eq_norm, norm_sub_rev]

end Erdos633
