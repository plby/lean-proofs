import Wikipedia.HopfProblem.EllipticData

/-!
# Iteration and freeness of the elliptic affine twists

These are the flat-coordinate calculations of §5.2.  The matrices and the
integer lattice are the actual ones fixed in §2; congruence always means
congruence modulo that lattice.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.Elliptic

theorem flatLinear_realCast (j : Kind) (v : Lattice) :
    flatLinear j (realCast v) = realCast (j.matrix *ᵥ v) := by
  ext i
  exact (RingHom.map_mulVec (Int.castRingHom ℝ) j.matrix v i).symm

theorem flatLinear_fixes_realCast (j : Kind) (v : Lattice)
    (hv : j.matrix *ᵥ v = v) : flatLinear j (realCast v) = realCast v := by
  rw [flatLinear_realCast, hv]

/-- Each affine map respects congruence modulo the coordinate lattice. -/
theorem flatAffine_congruent (j : Kind) (v : Lattice) {x y : RealCoordinates}
    (hxy : FlatCongruent x y) : FlatCongruent (flatAffine j v x) (flatAffine j v y) := by
  obtain ⟨w, hw⟩ := hxy
  refine ⟨j.matrix *ᵥ w, ?_⟩
  simp only [flatAffine, add_sub_add_right_eq_sub, ← map_sub, hw, flatLinear_realCast]

/-- The formula `A^r x + (r/m) v` for every iterate of an invariant twist. -/
theorem flatAffine_iterate (j : Kind) (v : Lattice)
    (hv : j.matrix *ᵥ v = v) (r : ℕ) (x : RealCoordinates) :
    (flatAffine j v)^[r] x =
      (j.matrix.map (Int.castRingHom ℝ)) ^ r *ᵥ x +
        ((r : ℝ) / (j.order : ℝ)) • realCast v := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply', ih, flatAffine, map_add, map_smul,
      flatLinear_fixes_realCast j v hv]
    have hlin : flatLinear j ((j.matrix.map (Int.castRingHom ℝ)) ^ r *ᵥ x) =
        (j.matrix.map (Int.castRingHom ℝ)) ^ (r + 1) *ᵥ x := by
      simp only [flatLinear, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, pow_succ']
    rw [hlin, add_assoc, ← add_smul]
    congr 2
    push_cast
    ring

/-- After `m` iterations the affine map is precisely translation by `v`. -/
theorem flatAffine_iterate_order (j : Kind) (v : Lattice)
    (hv : j.matrix *ᵥ v = v) (x : RealCoordinates) :
    (flatAffine j v)^[j.order] x = x + realCast v := by
  rw [flatAffine_iterate j v hv, ← Matrix.map_pow, j.matrix_pow_order]
  have hm : (j.order : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt j.order_pos)
  simp [hm]

/-- The `m`-th iterate is the identity modulo the integral lattice. -/
theorem flatAffine_iterate_order_congruent (j : Kind) (v : Lattice)
    (hv : j.matrix *ᵥ v = v) (x : RealCoordinates) :
    FlatCongruent ((flatAffine j v)^[j.order] x) x := by
  refine ⟨v, ?_⟩
  rw [flatAffine_iterate_order j v hv]
  abel

/-- The functional `γ` is unchanged by each linear monodromy matrix. -/
@[simp] theorem flatLinear_gamma (j : Kind) (x : RealCoordinates) :
    flatLinear j x 0 = x 0 := by
  cases j <;>
    simp [flatLinear, Kind.matrix, A₁, A₂, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]

/-- The first coordinate already obstructs every nontrivial fixed point. -/
theorem flatAffine_iterate_gamma (j : Kind) (v : Lattice) (r : ℕ)
    (x : RealCoordinates) :
    (flatAffine j v)^[r] x 0 = x 0 +
      ((r : ℝ) / (j.order : ℝ)) * (γ v : ℝ) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply']
    change flatLinear j ((flatAffine j v)^[r] x) 0 +
      (1 / (j.order : ℝ)) * (γ v : ℝ) = _
    rw [flatLinear_gamma, ih]
    push_cast
    ring

/-- An admissible twist has no fixed point modulo the lattice for any
nonidentity power below its order. -/
theorem flatAffine_iterate_not_congruent (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (r : ℕ) (hr : 0 < r) (hrm : r < j.order)
    (x : RealCoordinates) : ¬ FlatCongruent ((flatAffine j v)^[r] x) x := by
  rintro ⟨w, hw⟩
  have hgamma := congrFun hw 0
  change (flatAffine j v)^[r] x 0 - x 0 = (w 0 : ℝ) at hgamma
  rw [flatAffine_iterate_gamma] at hgamma
  have hm : (j.order : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt j.order_pos)
  have hreal : (r : ℝ) * (γ v : ℝ) = (j.order : ℝ) * (w 0 : ℝ) := by
    field_simp at hgamma
    nlinarith
  have hint : (r : ℤ) * γ v = (j.order : ℤ) * w 0 := by exact_mod_cast hreal
  cases j with
  | three =>
    have ha : ¬ 3 ∣ γ v := by simpa [AdmissibleTwist] using hv.2
    change r < 3 at hrm
    change (r : ℤ) * γ v = 3 * w 0 at hint
    interval_cases r <;> norm_num at hint <;> omega
  | four =>
    have ha : Odd (γ v) := by simpa [AdmissibleTwist] using hv.2
    rcases ha with ⟨a, ha⟩
    change r < 4 at hrm
    change (r : ℤ) * γ v = 4 * w 0 at hint
    interval_cases r <;> norm_num at hint <;> omega

/-- When `3 ∣ γ(v)`, the generator of the order-three action has an explicit
fixed point modulo the lattice. -/
theorem bad_three_twist_has_fixed_point (v : Lattice)
    (hv : A₁ *ᵥ v = v) (ha : (3 : ℤ) ∣ γ v) :
    ∃ x : RealCoordinates, FlatCongruent (flatAffine .three v x) x := by
  obtain ⟨h₁, h₂⟩ := (A₁_fixed_iff v).mp hv
  obtain ⟨m, hm⟩ := ha
  have hm' : (v 0 : ℝ) = 3 * (m : ℝ) := by
    exact_mod_cast hm
  refine ⟨![0, -(v 3 : ℝ) / 3, -((v 3 : ℝ) + 2 * (v 0 : ℝ)) / 3, 0],
    ![m, 0, v 3, 0], ?_⟩
  ext i
  fin_cases i <;>
    simp [flatAffine, flatLinear, Kind.matrix, Kind.order, A₁,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      realCast, h₁, h₂, hm'] <;> ring

/-- When `γ(v)` is even, the square of the order-four generator has an explicit
fixed point modulo the lattice. -/
theorem bad_four_twist_has_square_fixed_point (v : Lattice)
    (hv : A₂ *ᵥ v = v) (ha : Even (γ v)) :
    ∃ x : RealCoordinates, FlatCongruent ((flatAffine .four v)^[2] x) x := by
  obtain ⟨h₁, h₂⟩ := (A₂_fixed_iff v).mp hv
  obtain ⟨m, hm⟩ := ha
  have hm' : (v 0 : ℝ) = 2 * (m : ℝ) := by
    change v 0 = m + m at hm
    exact_mod_cast (show v 0 = 2 * m by omega)
  refine ⟨![0, 3 * (v 0 : ℝ) / 4, -3 * (v 0 : ℝ) / 4 - (v 3 : ℝ) / 2, 0],
    ![m, 0, v 3, 0], ?_⟩
  ext i
  fin_cases i <;>
    simp [Function.iterate_succ_apply, flatAffine, flatLinear, Kind.matrix, Kind.order, A₂,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      realCast, h₁, h₂, hm'] <;> ring

/-- Proposition 5.6: the exact freeness criterion, expressed on flat-coordinate
representatives of the torus.  The necessity uses the explicit fixed points above. -/
theorem flatAffine_free_iff (j : Kind) (v : Lattice) (hv : j.matrix *ᵥ v = v) :
    (∀ r : ℕ, 0 < r → r < j.order →
      ∀ x : RealCoordinates, ¬ FlatCongruent ((flatAffine j v)^[r] x) x) ↔
        AdmissibleTwist j v := by
  constructor
  · intro hfree
    refine ⟨hv, ?_⟩
    cases j with
    | three =>
      change ¬ 3 ∣ γ v
      intro ha
      obtain ⟨x, hx⟩ := bad_three_twist_has_fixed_point v hv ha
      exact hfree 1 (by decide) (by decide) x (by simpa using hx)
    | four =>
      change Odd (γ v)
      apply Int.not_even_iff_odd.mp
      intro ha
      obtain ⟨x, hx⟩ := bad_four_twist_has_square_fixed_point v hv ha
      exact hfree 2 (by decide) (by decide) x hx
  · intro ha r hr hrm x
    exact flatAffine_iterate_not_congruent j v ha r hr hrm x

/-- An invariant twist is inadmissible exactly when some nonidentity power
has a fixed point on the real torus. -/
theorem flatAffine_nontrivial_fixed_iff (j : Kind) (v : Lattice)
    (hv : j.matrix *ᵥ v = v) :
    (∃ r : ℕ, 0 < r ∧ r < j.order ∧
      ∃ x : RealCoordinates, FlatCongruent ((flatAffine j v)^[r] x) x) ↔
        ¬ AdmissibleTwist j v := by
  simpa only [not_forall, not_not, exists_prop] using
    not_congr (flatAffine_free_iff j v hv)

end Wikipedia.HopfProblem.Elliptic
