import ErdosProblems.Erdos633.EmbeddingTransport
import ErdosProblems.Erdos633.NormalizedArea

/-!
# A common orientation change under field embeddings

For congruent tiles the outer absolute determinant is the tile determinant
times the tile count. Multiplying by the original orientation signs makes
this a field identity. Every real embedding therefore changes all triangle
orientations by the same sign, as required for crossing reconstruction.
-/

namespace Erdos633

theorem Triangle.orientationSign_cases (P : Triangle) :
    P.orientationSign = 1 ∨ P.orientationSign = -1 := by
  unfold Triangle.orientationSign
  split_ifs <;> simp

theorem Triangle.orientationSign_mul_doubleArea_eq_abs (P : Triangle) :
    P.orientationSign * orientedDoubleArea P.a P.b P.c =
      |orientedDoubleArea P.a P.b P.c| := by
  unfold Triangle.orientationSign
  split_ifs with h
  · rw [one_mul, abs_of_pos h]
  · rw [neg_one_mul, abs_of_nonpos (le_of_not_gt h)]

theorem signs_eq_of_positive_weighted_eq (r s x y : ℝ)
    (hr : r = 1 ∨ r = -1) (hs : s = 1 ∨ s = -1)
    (hx : 0 < x) (hy : 0 < y) (h : r * x = s * y) : r = s := by
  rcases hr with rfl | rfl <;> rcases hs with rfl | rfl <;> norm_num at * <;> linarith

theorem Triangle.orientation_product_eq_of_signed_area (P Q : Triangle)
    (r s n : ℝ) (hr : r = 1 ∨ r = -1) (hs : s = 1 ∨ s = -1) (hn : 0 < n)
    (h : r * orientedDoubleArea P.a P.b P.c =
      n * (s * orientedDoubleArea Q.a Q.b Q.c)) :
    P.orientationSign * r = Q.orientationSign * s := by
  have hPr : P.orientationSign * r = 1 ∨ P.orientationSign * r = -1 := by
    rcases P.orientationSign_cases with hp | hp <;> rcases hr with hr | hr <;>
      simp [hp, hr]
  have hQs : Q.orientationSign * s = 1 ∨ Q.orientationSign * s = -1 := by
    rcases Q.orientationSign_cases with hq | hq <;> rcases hs with hs | hs <;>
      simp [hq, hs]
  apply signs_eq_of_positive_weighted_eq _ _
    (P.orientationSign * orientedDoubleArea P.a P.b P.c)
    (n * (Q.orientationSign * orientedDoubleArea Q.a Q.b Q.c)) hPr hQs
    P.orientationSign_area_pos (mul_pos hn Q.orientationSign_area_pos)
  calc
    (P.orientationSign * r) * (P.orientationSign * orientedDoubleArea P.a P.b P.c) =
        (P.orientationSign * P.orientationSign) *
          (r * orientedDoubleArea P.a P.b P.c) := by ring
    _ = n * (s * orientedDoubleArea Q.a Q.b Q.c) := by
      rw [P.orientationSign_mul_self, one_mul, h]
    _ = (Q.orientationSign * Q.orientationSign) *
        (n * (s * orientedDoubleArea Q.a Q.b Q.c)) := by
      rw [Q.orientationSign_mul_self, one_mul]
    _ = _ := by ring

noncomputable def FieldTriangle.orientationCoefficient {F : Type*} [Field F]
    (P : FieldTriangle F) (τ : F →+* ℝ) : F :=
  if 0 < orientedDoubleArea (P.realize τ).a (P.realize τ).b (P.realize τ).c then 1 else -1

theorem FieldTriangle.map_orientationCoefficient {F : Type*} [Field F]
    (P : FieldTriangle F) (τ σ : F →+* ℝ) :
    σ (P.orientationCoefficient τ) = (P.realize τ).orientationSign := by
  unfold FieldTriangle.orientationCoefficient Triangle.orientationSign
  split_ifs <;> simp

theorem FieldTriangle.signed_doubleArea_transfer {F : Type*} [Field F]
    (P Q : FieldTriangle F) (τ σ : F →+* ℝ) (N : ℕ)
    (h : |orientedDoubleArea (P.realize τ).a (P.realize τ).b (P.realize τ).c| =
      N * |orientedDoubleArea (Q.realize τ).a (Q.realize τ).b (Q.realize τ).c|) :
    (P.realize τ).orientationSign *
        orientedDoubleArea (P.realize σ).a (P.realize σ).b (P.realize σ).c =
      N * ((Q.realize τ).orientationSign *
        orientedDoubleArea (Q.realize σ).a (Q.realize σ).b (Q.realize σ).c) := by
  have heq : P.orientationCoefficient τ * fieldDoubleArea P.a P.b P.c =
      (N : F) * (Q.orientationCoefficient τ * fieldDoubleArea Q.a Q.b Q.c) := by
    apply τ.injective
    simpa only [map_mul, map_natCast, FieldTriangle.map_orientationCoefficient,
      ← FieldTriangle.realize_doubleArea, Triangle.orientationSign_mul_doubleArea_eq_abs] using h
  simpa only [map_mul, map_natCast, FieldTriangle.map_orientationCoefficient,
    ← FieldTriangle.realize_doubleArea] using congrArg σ heq

theorem FieldTriangle.orientation_ratio_transfer {F : Type*} [Field F]
    (P Q : FieldTriangle F) (τ σ : F →+* ℝ) (N : ℕ) (hN : 0 < N)
    (h : |orientedDoubleArea (P.realize τ).a (P.realize τ).b (P.realize τ).c| =
      N * |orientedDoubleArea (Q.realize τ).a (Q.realize τ).b (Q.realize τ).c|) :
    (P.realize σ).orientationSign * (P.realize τ).orientationSign =
      (Q.realize σ).orientationSign * (Q.realize τ).orientationSign := by
  exact (P.realize σ).orientation_product_eq_of_signed_area (Q.realize σ)
    _ _ N (P.realize τ).orientationSign_cases (Q.realize τ).orientationSign_cases
    (by exact_mod_cast hN) (P.signed_doubleArea_transfer Q τ σ N h)

theorem CongruentTiling.abs_doubleArea_eq_tile
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N) (i : Fin N) :
    |orientedDoubleArea P.a P.b P.c| =
      N * |orientedDoubleArea (T.tile i).a (T.tile i).b (T.tile i).c| := by
  have harea : (T.tile i).area = R.area := by
    obtain ⟨e, he⟩ := T.congruent i
    unfold Triangle.area
    rw [← he, isometry_volume_image]
  apply mul_right_cancel₀ (ne_of_gt standardTriangle.area_pos)
  calc
    |orientedDoubleArea P.a P.b P.c| * standardTriangle.area = P.area :=
      P.area_eq_abs_orientedDoubleArea_mul_standard.symm
    _ = (N : ℝ) * (T.tile i).area := by rw [harea]; exact T.area_eq
    _ = _ := by rw [(T.tile i).area_eq_abs_orientedDoubleArea_mul_standard]; ring

end Erdos633
