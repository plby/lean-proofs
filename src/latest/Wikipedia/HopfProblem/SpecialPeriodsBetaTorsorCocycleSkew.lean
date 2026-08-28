import Wikipedia.HopfProblem.SpecialPeriodsTriangleRepresentation

/-!
# Actual additive skew permutations

The skew map `(z, b) ↦ (e z, b + φ z)` is an actual permutation.
Its powers sum the prescribed shifts around the corresponding orbit.
The property of being an additive skew map over a base permutation is
preserved under multiplication and inversion.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.BetaTorsor

variable {X : Type*}

/-- An actual invertible additive skew map over a base permutation. -/
def skewPerm (e : Equiv.Perm X) (φ : X → ℂ) : Equiv.Perm (X × ℂ) where
  toFun x := (e x.1, x.2 + φ x.1)
  invFun x := (e.symm x.1, x.2 - φ (e.symm x.1))
  left_inv := by
    rintro ⟨z, b⟩
    simp
  right_inv := by
    rintro ⟨z, b⟩
    simp

@[simp] theorem skewPerm_apply (e : Equiv.Perm X) (φ : X → ℂ) (z : X) (b : ℂ) :
    skewPerm e φ (z, b) = (e z, b + φ z) := rfl

@[simp] theorem skewPerm_symm_apply (e : Equiv.Perm X) (φ : X → ℂ) (z : X) (b : ℂ) :
    (skewPerm e φ).symm (z, b) = (e.symm z, b - φ (e.symm z)) := rfl

/-- A power of a skew map sums the shifts along the actual base orbit. -/
theorem skewPerm_pow_apply (e : Equiv.Perm X) (φ : X → ℂ) (n : ℕ) (z : X) (b : ℂ) :
    (skewPerm e φ ^ n) (z, b) =
      ((e ^ n) z, b + ∑ k ∈ Finset.range n, φ ((e ^ k) z)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, ih, skewPerm_apply]
      rw [pow_succ', Equiv.Perm.mul_apply, Finset.sum_range_succ]
      simp only [add_assoc]

/-- The cyclic-sum relation proves the corresponding finite-order relation
for the actual skew permutation. -/
theorem skewPerm_pow_eq_one (e : Equiv.Perm X) (φ : X → ℂ) (m : ℕ)
    (he : e ^ m = 1) (hφ : ∀ z, (∑ k ∈ Finset.range m, φ ((e ^ k) z)) = 0) :
    skewPerm e φ ^ m = 1 := by
  apply Equiv.ext
  rintro ⟨z, b⟩
  rw [skewPerm_pow_apply, he, hφ z]
  simp

/-- A permutation is additive in the fibre coordinate and covers the given
base permutation. This is a property of an actual permutation, not extra
affine-cocycle data. -/
def IsAdditiveSkewOver (e : Equiv.Perm X) (p : Equiv.Perm (X × ℂ)) : Prop :=
  ∀ z b, p (z, b) = (e z, b + (p (z, 0)).2)

theorem isAdditiveSkewOver_skewPerm (e : Equiv.Perm X) (φ : X → ℂ) :
    IsAdditiveSkewOver e (skewPerm e φ) := by
  intro z b
  simp

theorem isAdditiveSkewOver_one :
    IsAdditiveSkewOver (1 : Equiv.Perm X) (1 : Equiv.Perm (X × ℂ)) := by
  intro z b
  simp

theorem IsAdditiveSkewOver.mul {e f : Equiv.Perm X} {p q : Equiv.Perm (X × ℂ)}
    (hp : IsAdditiveSkewOver e p) (hq : IsAdditiveSkewOver f q) :
    IsAdditiveSkewOver (e * f) (p * q) := by
  intro z b
  have hzero : ((p * q) (z, 0)).2 = (q (z, 0)).2 + (p (f z, 0)).2 := by
    change (p (q (z, 0))).2 = _
    rw [hq z 0]
    simpa only [zero_add] using
      congrArg Prod.snd (hp (f z) ((q (z, 0)).2))
  change p (q (z, b)) = (e (f z), b + ((p * q) (z, 0)).2)
  rw [hq z b, hp (f z) (b + (q (z, 0)).2), hzero]
  simp only [add_assoc]

theorem IsAdditiveSkewOver.inv {e : Equiv.Perm X} {p : Equiv.Perm (X × ℂ)}
    (hp : IsAdditiveSkewOver e p) : IsAdditiveSkewOver e⁻¹ p⁻¹ := by
  have hpi (z : X) (b : ℂ) :
      p.symm (z, b) = (e.symm z, b - (p (e.symm z, 0)).2) := by
    apply p.injective
    rw [p.apply_symm_apply, hp]
    simp
  intro z b
  change p.symm (z, b) = (e.symm z, b + (p.symm (z, 0)).2)
  rw [hpi z b, hpi z 0]
  simp only [sub_eq_add_neg, zero_add]

end Wikipedia.HopfProblem.SpecialPeriods.BetaTorsor
