import Wikipedia.HopfProblem.EllipticFundamentalGroupDeck

/-!
# Multiplication in the unique affine deck-group coordinates

The normal form `(w,r)` denotes the actual affine automorphism `T_w h^r`,
with `0 ≤ r < m`. Multiplication adds `A^r z` to the lattice coordinate.
When the exponent sum crosses `m`, the relation `h^m = T_v` contributes
one additional copy of `v`. The inverse is likewise computed explicitly.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.Elliptic

/-- The explicit product of the unique normal-form coordinates. Since
both exponents are below `m`, at most one copy of the twist vector carries
into the lattice coordinate. -/
def coordinateProduct (j : Kind) (v : Lattice)
    (a b : Lattice × Fin j.order) : Lattice × Fin j.order :=
  if h : a.2.val + b.2.val < j.order then
    (a.1 + j.matrix ^ a.2.val *ᵥ b.1, ⟨a.2.val + b.2.val, h⟩)
  else
    (a.1 + j.matrix ^ a.2.val *ᵥ b.1 + v,
      ⟨a.2.val + b.2.val - j.order, by have := a.2.isLt; have := b.2.isLt; omega⟩)

theorem coordinateProduct_of_lt (j : Kind) (v : Lattice)
    (a b : Lattice × Fin j.order) (h : a.2.val + b.2.val < j.order) :
    coordinateProduct j v a b =
      (a.1 + j.matrix ^ a.2.val *ᵥ b.1, ⟨a.2.val + b.2.val, h⟩) := by
  simp only [coordinateProduct, dif_pos h]

theorem coordinateProduct_of_ge (j : Kind) (v : Lattice)
    (a b : Lattice × Fin j.order) (h : j.order ≤ a.2.val + b.2.val) :
    coordinateProduct j v a b =
      (a.1 + j.matrix ^ a.2.val *ᵥ b.1 + v,
        ⟨a.2.val + b.2.val - j.order, by have := a.2.isLt; have := b.2.isLt; omega⟩) := by
  simp only [coordinateProduct, dif_neg (not_lt.mpr h)]

/-- Equivalently, the lattice-coordinate carry is the integer quotient
of the exponent sum by the elliptic order. -/
theorem coordinateProduct_fst (j : Kind) (v : Lattice)
    (a b : Lattice × Fin j.order) :
    (coordinateProduct j v a b).1 =
      a.1 + j.matrix ^ a.2.val *ᵥ b.1 +
        (((a.2.val + b.2.val) / j.order : ℕ) : ℤ) • v := by
  by_cases h : a.2.val + b.2.val < j.order
  · have hc : (a.2.val + b.2.val) / j.order = 0 := Nat.div_eq_of_lt h
    simp [coordinateProduct, h, hc]
  · have hc : (a.2.val + b.2.val) / j.order = 1 := by
      have ha := a.2.isLt
      have hb := b.2.isLt
      cases j <;> simp only [Kind.order] at * <;> omega
    simp [coordinateProduct, h, hc]

/-- The finite exponent is the remainder of the exponent sum modulo the
elliptic order. -/
theorem coordinateProduct_snd_val (j : Kind) (v : Lattice)
    (a b : Lattice × Fin j.order) :
    (coordinateProduct j v a b).2.val = (a.2.val + b.2.val) % j.order := by
  by_cases h : a.2.val + b.2.val < j.order
  · simp [coordinateProduct, h, Nat.mod_eq_of_lt h]
  · have hm : (a.2.val + b.2.val) % j.order = a.2.val + b.2.val - j.order := by
      have ha := a.2.isLt
      have hb := b.2.isLt
      cases j <;> simp only [Kind.order] at * <;> omega
    simp [coordinateProduct, h, hm]

/-- The coordinate product agrees with multiplication of the actual affine
deck transformations. -/
theorem deckNormalForm_mul_coordinates (j : Kind) (v : Lattice)
    (hv : j.matrix *ᵥ v = v) (a b : Lattice × Fin j.order) :
    deckNormalForm j v a * deckNormalForm j v b =
      deckNormalForm j v (coordinateProduct j v a b) := by
  apply Subtype.ext
  change affineNormalForm j v a.1 a.2.val * affineNormalForm j v b.1 b.2.val =
    affineNormalForm j v (coordinateProduct j v a b).1 (coordinateProduct j v a b).2.val
  rw [affineNormalForm_mul]
  by_cases h : a.2.val + b.2.val < j.order
  · rw [coordinateProduct_of_lt j v a b h]
  · rw [coordinateProduct_of_ge j v a b (Nat.le_of_not_gt h)]
    exact affineNormalForm_reduce_order j v _ hv _ (Nat.le_of_not_gt h)

/-- The inverse coordinates, including the contribution of `h^m = T_v`
when the finite exponent is nonzero. -/
def coordinateInverse (j : Kind) (v : Lattice)
    (a : Lattice × Fin j.order) : Lattice × Fin j.order :=
  if h : a.2.val = 0 then
    (-a.1, ⟨0, j.order_pos⟩)
  else
    (j.matrix ^ (j.order - a.2.val) *ᵥ (-v - a.1),
      ⟨j.order - a.2.val, by have := a.2.isLt; omega⟩)

/-- The explicit inverse formula computes the inverse of the actual deck
transformation. -/
theorem deckNormalForm_inv_coordinates (j : Kind) (v : Lattice)
    (hv : j.matrix *ᵥ v = v) (a : Lattice × Fin j.order) :
    (deckNormalForm j v a)⁻¹ = deckNormalForm j v (coordinateInverse j v a) := by
  apply Subtype.ext
  change (affineNormalForm j v a.1 a.2.val)⁻¹ =
    affineNormalForm j v (coordinateInverse j v a).1 (coordinateInverse j v a).2.val
  by_cases h : a.2.val = 0
  · simp [coordinateInverse, h, affineNormalForm]
  · simp only [coordinateInverse, dif_neg h]
    apply inv_eq_of_mul_eq_one_right
    have hrk : a.2.val + (j.order - a.2.val) = j.order :=
      Nat.add_sub_of_le a.2.isLt.le
    rw [affineNormalForm_mul, Matrix.mulVec_mulVec, ← pow_add, hrk,
      j.matrix_pow_order, Matrix.one_mulVec]
    have hw : a.1 + (-v - a.1) = -v := by abel
    rw [hw, affineNormalForm, affineGenerator_pow_order j v hv,
      integerTranslation_neg, inv_mul_cancel]

/-- For an admissible twist these formulas compute multiplication in the
unique normal-form coordinates of every pair of deck-group elements. -/
theorem deckNormalFormEquiv_symm_mul (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (g h : AffineDeckGroup j v) :
    (deckNormalFormEquiv j v hv).symm (g * h) =
      coordinateProduct j v ((deckNormalFormEquiv j v hv).symm g)
        ((deckNormalFormEquiv j v hv).symm h) := by
  apply (deckNormalFormEquiv j v hv).injective
  rw [Equiv.apply_symm_apply]
  change g * h = deckNormalForm j v _
  rw [← deckNormalForm_mul_coordinates j v hv.1]
  exact congrArg₂ (· * ·) ((deckNormalFormEquiv j v hv).apply_symm_apply g).symm
    ((deckNormalFormEquiv j v hv).apply_symm_apply h).symm

/-- Inversion in the actual group has the stated explicit coordinate
formula. -/
theorem deckNormalFormEquiv_symm_inv (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (g : AffineDeckGroup j v) :
    (deckNormalFormEquiv j v hv).symm g⁻¹ =
      coordinateInverse j v ((deckNormalFormEquiv j v hv).symm g) := by
  apply (deckNormalFormEquiv j v hv).injective
  rw [Equiv.apply_symm_apply]
  change g⁻¹ = deckNormalForm j v _
  rw [← deckNormalForm_inv_coordinates j v hv.1]
  exact congrArg Inv.inv ((deckNormalFormEquiv j v hv).apply_symm_apply g).symm

end Wikipedia.HopfProblem.Elliptic
