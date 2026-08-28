import Wikipedia.NoExoticSixSphere.CayleyTransform

/-!
# Exact inverse identities for Cayley coordinates

The rational transform `(1 - A)(1 + A)⁻¹` is an involution wherever `1 + A`
is invertible. For orthogonal operators it is skew-adjoint, giving exact
inverse coordinate maps on the open set without eigenvalue `-1`.
-/

namespace NoExoticSixSphere.CayleyTransform

open GLOrthonormalization OrthogonalPaths

variable {n : ℕ}

/-- The Cayley rational expression, defined on ambient operators. -/
noncomputable def fraction (A : Vector n →L[ℝ] Vector n) : Vector n →L[ℝ] Vector n :=
  (1 - A).comp (1 + A).inverse

theorem operator_eq_fraction (K : SkewOperators n) : operator K = fraction K := rfl

theorem fraction_apply_one_add (A : Vector n →L[ℝ] Vector n) (hA : (1 + A).IsInvertible)
    (x : Vector n) : fraction A ((1 + A) x) = (1 - A) x := by
  change (1 - A) ((1 + A).inverse ((1 + A) x)) = _
  rw [hA.inverse_apply_self]

theorem one_add_fraction_apply_one_add (A : Vector n →L[ℝ] Vector n)
    (hA : (1 + A).IsInvertible) (x : Vector n) :
    (1 + fraction A) ((1 + A) x) = (2 : ℝ) • x := by
  change (1 + A) x + fraction A ((1 + A) x) = _
  rw [fraction_apply_one_add A hA]
  change (x + A x) + (x - A x) = (2 : ℝ) • x
  rw [two_smul]
  abel

theorem one_sub_fraction_apply_one_add (A : Vector n →L[ℝ] Vector n)
    (hA : (1 + A).IsInvertible) (x : Vector n) :
    (1 - fraction A) ((1 + A) x) = (2 : ℝ) • A x := by
  change (1 + A) x - fraction A ((1 + A) x) = _
  rw [fraction_apply_one_add A hA]
  change (x + A x) - (x - A x) = (2 : ℝ) • A x
  rw [two_smul]
  abel

theorem one_add_fraction_injective (A : Vector n →L[ℝ] Vector n)
    (hA : (1 + A).IsInvertible) :
    Function.Injective ((1 + fraction A) : Vector n →L[ℝ] Vector n) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  obtain ⟨y, rfl⟩ := hA.surjective x
  change (1 + fraction A) ((1 + A) y) = 0 at hx
  rw [one_add_fraction_apply_one_add A hA] at hx
  have hy : y = 0 := (smul_eq_zero.mp hx).resolve_left (by norm_num)
  rw [hy, map_zero]

theorem one_add_fraction_isInvertible (A : Vector n →L[ℝ] Vector n)
    (hA : (1 + A).IsInvertible) : (1 + fraction A).IsInvertible := by
  let e := (LinearEquiv.ofInjectiveEndo (1 + fraction A).toLinearMap
    (one_add_fraction_injective A hA)).toContinuousLinearEquiv
  exact ⟨e, by apply ContinuousLinearMap.ext; intro x; rfl⟩

/-- The Cayley rational transform is its own inverse on its domain. -/
theorem fraction_fraction (A : Vector n →L[ℝ] Vector n) (hA : (1 + A).IsInvertible) :
    fraction (fraction A) = A := by
  apply ContinuousLinearMap.ext
  intro x
  have h := fraction_apply_one_add (fraction A) (one_add_fraction_isInvertible A hA)
    ((1 + A) x)
  rw [one_add_fraction_apply_one_add A hA, one_sub_fraction_apply_one_add A hA,
    map_smul] at h
  exact (smul_right_injective (Vector n) (by norm_num : (2 : ℝ) ≠ 0)) h

/-- The inverse Cayley expression is skew for the actual inner product. -/
theorem inner_fraction_skew (a : OrthogonalOperators n) (ha : (1 + a.1.1).IsInvertible)
    (x y : Vector n) :
    inner ℝ (fraction a.1.1 x) y = -inner ℝ x (fraction a.1.1 y) := by
  obtain ⟨u, rfl⟩ := ha.surjective x
  obtain ⟨w, rfl⟩ := ha.surjective y
  rw [fraction_apply_one_add _ ha, fraction_apply_one_add _ ha]
  change inner ℝ (u - a.1.1 u) (w + a.1.1 w) =
    -inner ℝ (u + a.1.1 u) (w - a.1.1 w)
  have hinner : inner ℝ (a.1.1 u) (a.1.1 w) = inner ℝ u w :=
    (toEquiv a).inner_map_map u w
  simp only [inner_sub_left, inner_add_right, inner_add_left, inner_sub_right, hinner]
  ring

theorem fraction_adjoint_eq_neg (a : OrthogonalOperators n) (ha : (1 + a.1.1).IsInvertible) :
    (fraction a.1.1).adjoint = -fraction a.1.1 := by
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_left ℝ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_right]
  change inner ℝ (fraction a.1.1 x) y = inner ℝ x (-(fraction a.1.1 y))
  rw [inner_neg_right]
  exact inner_fraction_skew a ha x y

/-- Inverse Cayley coordinates for an orthogonal operator without eigenvalue `-1`. -/
noncomputable def coordinate (a : OrthogonalOperators n) (ha : (1 + a.1.1).IsInvertible) :
    SkewOperators n := ⟨fraction a.1.1, fraction_adjoint_eq_neg a ha⟩

theorem coordinate_operator (a : OrthogonalOperators n) (ha : (1 + a.1.1).IsInvertible) :
    (coordinate a ha : Vector n →L[ℝ] Vector n) = fraction a.1.1 := rfl

theorem orthogonal_coordinate (a : OrthogonalOperators n) (ha : (1 + a.1.1).IsInvertible) :
    orthogonal (coordinate a ha) = a := by
  apply Subtype.ext
  apply Subtype.ext
  change fraction (fraction a.1.1) = a.1.1
  exact fraction_fraction a.1.1 ha

theorem orthogonal_mem_domain (K : SkewOperators n) :
    (1 + (orthogonal K).1.1).IsInvertible := by
  rw [orthogonal_operator, operator_eq_fraction]
  exact one_add_fraction_isInvertible (n := n) (K : Vector n →L[ℝ] Vector n)
    (one_add_isInvertible K)

theorem coordinate_orthogonal (K : SkewOperators n) :
    coordinate (orthogonal K) (orthogonal_mem_domain K) = K := by
  apply Subtype.ext
  rw [coordinate_operator, orthogonal_operator, operator_eq_fraction]
  exact fraction_fraction (n := n) (K : Vector n →L[ℝ] Vector n) (one_add_isInvertible K)

end NoExoticSixSphere.CayleyTransform
