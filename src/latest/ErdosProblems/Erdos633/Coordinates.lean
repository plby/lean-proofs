import ErdosProblems.Erdos633.Refinement
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Coordinates for triangle subdivisions

The standard triangle is the closed region `x ≥ 0`, `y ≥ 0`, `x+y ≤ 1`.
Both its boundary and its interior are characterized explicitly.
-/

namespace Erdos633

theorem Triangle.edge_vectors_independent (T : Triangle) (r s : ℝ)
    (h : r • (T.b - T.a) + s • (T.c - T.a) = 0) : r = 0 ∧ s = 0 := by
  have hx := congrArg Complex.re h
  have hy := congrArg Complex.im h
  simp only [Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im,
    Complex.zero_re, Complex.zero_im, smul_eq_mul, Complex.sub_re, Complex.sub_im] at hx hy
  let d := orientedDoubleArea T.a T.b T.c
  have hd : d ≠ 0 := T.nondegenerate
  have hr : r * d = 0 := by
    dsimp [d, orientedDoubleArea]
    linear_combination (T.c.im - T.a.im) * hx - (T.c.re - T.a.re) * hy
  have hs : s * d = 0 := by
    dsimp [d, orientedDoubleArea]
    linear_combination (T.b.re - T.a.re) * hy - (T.b.im - T.a.im) * hx
  exact ⟨(mul_eq_zero.mp hr).resolve_right hd, (mul_eq_zero.mp hs).resolve_right hd⟩

noncomputable def Triangle.coordinateLinearMap (T : Triangle) : ℂ →ₗ[ℝ] ℂ :=
  Complex.reLm.smulRight (T.b - T.a) + Complex.imLm.smulRight (T.c - T.a)

theorem Triangle.coordinateLinearMap_injective (T : Triangle) :
    Function.Injective T.coordinateLinearMap := by
  intro x y hxy
  have hz : T.coordinateLinearMap (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  obtain ⟨hr, hi⟩ := T.edge_vectors_independent (x - y).re (x - y).im hz
  exact sub_eq_zero.mp (Complex.ext hr hi)

/-- The affine coordinate map sends `0,1,I` to the three vertices of `T`. -/
noncomputable def Triangle.coordinateEquiv (T : Triangle) : ℂ ≃ᵃ[ℝ] ℂ :=
  (LinearEquiv.ofInjectiveEndo T.coordinateLinearMap
    T.coordinateLinearMap_injective).toAffineEquiv.trans
    (AffineEquiv.vaddConst ℝ T.a)

theorem Triangle.coordinateEquiv_apply (T : Triangle) (z : ℂ) :
    T.coordinateEquiv z = z.re • (T.b - T.a) + z.im • (T.c - T.a) + T.a := rfl

@[simp] theorem Triangle.coordinateEquiv_zero (T : Triangle) : T.coordinateEquiv 0 = T.a := by
  simp [T.coordinateEquiv_apply]

@[simp] theorem Triangle.coordinateEquiv_one (T : Triangle) : T.coordinateEquiv 1 = T.b := by
  simp [T.coordinateEquiv_apply]

@[simp] theorem Triangle.coordinateEquiv_I (T : Triangle) : T.coordinateEquiv Complex.I = T.c := by
  simp [T.coordinateEquiv_apply]

def standardTriangle : Triangle where
  a := 0
  b := 1
  c := Complex.I
  nondegenerate := by norm_num

theorem Triangle.standard_map_coordinateEquiv (T : Triangle) :
    standardTriangle.mapAffineEquiv T.coordinateEquiv = T := by
  apply Triangle.ext
  · exact T.coordinateEquiv_zero
  · exact T.coordinateEquiv_one
  · exact T.coordinateEquiv_I

theorem Triangle.mapAffineEquiv_interior (T : Triangle) (e : ℂ ≃ᵃ[ℝ] ℂ) :
    interior (T.mapAffineEquiv e).carrier = e '' interior T.carrier := by
  rw [Triangle.mapAffineEquiv_carrier]
  exact (e.toContinuousAffineEquiv.toHomeomorph.image_interior T.carrier).symm

theorem standardTriangle_carrier : standardTriangle.carrier =
    {z : ℂ | 0 ≤ z.re ∧ 0 ≤ z.im ∧ z.re + z.im ≤ 1} := by
  have hconv : Convex ℝ {z : ℂ | 0 ≤ z.re ∧ 0 ≤ z.im ∧ z.re + z.im ≤ 1} := by
    intro x hx y hy a b ha hb hab
    simp only [Set.mem_ofPred_eq, Complex.add_re, Complex.add_im,
      Complex.smul_re, Complex.smul_im, smul_eq_mul]
    refine ⟨add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1),
      add_nonneg (mul_nonneg ha hx.2.1) (mul_nonneg hb hy.2.1), ?_⟩
    have hxa := mul_le_mul_of_nonneg_left hx.2.2 ha
    have hyb := mul_le_mul_of_nonneg_left hy.2.2 hb
    nlinarith
  apply Set.Subset.antisymm
  · apply convexHull_min _ hconv
    intro z hz
    change z ∈ ({0, 1, Complex.I} : Set ℂ) at hz
    rcases hz with rfl | rfl | rfl <;> norm_num
  · intro z hz
    apply mem_convexHull_of_exists_fintype
      (![1 - z.re - z.im, z.re, z.im] : Fin 3 → ℝ) (![0, 1, Complex.I] : Fin 3 → ℂ)
    · intro i
      fin_cases i
      · change 0 ≤ 1 - z.re - z.im
        linarith [hz.2.2]
      · exact hz.1
      · exact hz.2.1
    · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
        Matrix.cons_val_zero, Matrix.cons_val_succ]
      ring
    · intro i
      fin_cases i <;> simp [standardTriangle]
    · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
        Matrix.cons_val_zero, Matrix.cons_val_succ, smul_zero, zero_add]
      apply Complex.ext <;> simp

theorem interior_re_add_im_le (a : ℝ) :
    interior {z : ℂ | z.re + z.im ≤ a} = {z : ℂ | z.re + z.im < a} := by
  let f : ℂ →L[ℝ] ℝ := Complex.reCLM + Complex.imCLM
  have hf : Function.Surjective f := by
    intro r
    exact ⟨(r : ℂ), by simp [f]⟩
  have h := f.interior_preimage hf (Set.Iic a)
  simpa [f, Set.preimage, interior_Iic] using h

theorem standardTriangle_interior : interior standardTriangle.carrier =
    {z : ℂ | 0 < z.re ∧ 0 < z.im ∧ z.re + z.im < 1} := by
  rw [standardTriangle_carrier]
  simp only [Set.ofPred_and, interior_inter, Complex.interior_setOfPred_le_re,
    Complex.interior_setOfPred_le_im, interior_re_add_im_le]

/-- A unit cell may be chosen with a strict lower bound except at zero. This
choice handles the boundary of the large triangle without a limiting argument. -/
theorem exists_unit_interval_index (n : ℕ) (hn : 0 < n) (x : ℝ)
    (hx0 : 0 ≤ x) (hxn : x ≤ n) :
    ∃ i : Fin n, (i : ℝ) ≤ x ∧ x ≤ (i : ℝ) + 1 ∧ (0 < x → (i : ℝ) < x) := by
  by_cases hx : x = 0
  · subst x
    exact ⟨⟨0, hn⟩, by simp⟩
  have hxpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hx)
  have hceilpos : 0 < ⌈x⌉₊ := Nat.ceil_pos.mpr hxpos
  have hceiln : ⌈x⌉₊ ≤ n := Nat.ceil_le.mpr hxn
  let i : Fin n := ⟨⌈x⌉₊ - 1, by omega⟩
  have hi : (i : ℝ) < x := Nat.lt_ceil.mp (show i.val < ⌈x⌉₊ by dsimp [i]; omega)
  have hieq : i.val + 1 = ⌈x⌉₊ := by dsimp [i]; omega
  refine ⟨i, hi.le, ?_, fun _ => hi⟩
  have hupper := Nat.le_ceil x
  have hc : (i : ℝ) + 1 = (⌈x⌉₊ : ℝ) := by exact_mod_cast hieq
  linarith

theorem integer_unit_interval_unique {i j : ℤ} {x : ℝ}
    (hi : (i : ℝ) < x ∧ x < (i : ℝ) + 1)
    (hj : (j : ℝ) < x ∧ x < (j : ℝ) + 1) : i = j := by
  have hij : (i : ℝ) < (j : ℝ) + 1 := by linarith [hi.1, hj.2]
  have hji : (j : ℝ) < (i : ℝ) + 1 := by linarith [hj.1, hi.2]
  have hij' : i < j + 1 := by exact_mod_cast hij
  have hji' : j < i + 1 := by exact_mod_cast hji
  omega

end Erdos633
