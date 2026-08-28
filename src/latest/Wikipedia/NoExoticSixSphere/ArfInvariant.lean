import Wikipedia.NoExoticSixSphere.ArfGaussSum

/-!
# A basis-independent Arf invariant over the field with two elements

For a quadratic form with nondegenerate polar form, the integer Gauss sum is
nonzero. Its sign defines an invariant in `ZMod 2`. This invariant is preserved
by actual quadratic-form isometries and is additive for orthogonal products.
The invariant of the zero-dimensional vector space is zero.

The geometric quadratic refinement on a framed manifold is not constructed here.
-/

namespace NoExoticSixSphere.Arf

def signParity (z : ℤ) : F₂ := if z < 0 then 1 else 0

theorem signParity_mul (z w : ℤ) (hz : z ≠ 0) (hw : w ≠ 0) :
    signParity (z * w) = signParity z + signParity w := by
  by_cases hzneg : z < 0
  · by_cases hwneg : w < 0
    · have hp := mul_pos_of_neg_of_neg hzneg hwneg
      simp only [signParity, hzneg, hwneg, not_lt_of_gt hp, if_false, if_true]
      decide
    · have hwpos : 0 < w := lt_of_le_of_ne (le_of_not_gt hwneg) hw.symm
      have hp := mul_neg_of_neg_of_pos hzneg hwpos
      simp [signParity, hzneg, hwneg, hp]
  · have hzpos : 0 < z := lt_of_le_of_ne (le_of_not_gt hzneg) hz.symm
    by_cases hwneg : w < 0
    · have hp := mul_neg_of_pos_of_neg hzpos hwneg
      simp [signParity, hzneg, hwneg, hp]
    · have hwpos : 0 < w := lt_of_le_of_ne (le_of_not_gt hwneg) hw.symm
      have hp := mul_pos hzpos hwpos
      simp [signParity, hzneg, hwneg, not_lt_of_gt hp]

variable {V W : Type*} [AddCommGroup V] [Module F₂ V]
  [AddCommGroup W] [Module F₂ W]

theorem nondegenerate_polar_prod (q : QuadraticForm F₂ V) (r : QuadraticForm F₂ W)
    (hq : q.polarBilin.Nondegenerate) (hr : r.polarBilin.Nondegenerate) :
    (q.prod r).polarBilin.Nondegenerate := by
  constructor
  · rintro ⟨x, y⟩ h
    apply Prod.ext
    · apply hq.1 x
      intro x'
      simpa [QuadraticMap.polarBilin_apply_apply] using h (x', 0)
    · apply hr.1 y
      intro y'
      simpa [QuadraticMap.polarBilin_apply_apply] using h (0, y')
  · rintro ⟨x, y⟩ h
    apply Prod.ext
    · apply hq.2 x
      intro x'
      simpa [QuadraticMap.polarBilin_apply_apply] using h (x', 0)
    · apply hr.2 y
      intro y'
      simpa [QuadraticMap.polarBilin_apply_apply] using h (0, y')

variable [Fintype V] [Fintype W]

def invariant (q : QuadraticForm F₂ V) (_hq : q.polarBilin.Nondegenerate) : F₂ :=
  signParity (gaussSum q)

theorem invariant_isometry (q : QuadraticForm F₂ V) (r : QuadraticForm F₂ W)
    (hq : q.polarBilin.Nondegenerate) (hr : r.polarBilin.Nondegenerate)
    (e : q.IsometryEquiv r) : invariant q hq = invariant r hr := by
  have he : (fun x ↦ r (e x)) = q := funext e.map_app
  have hs := gaussSum_equiv r e.toEquiv
  change gaussSum (fun x ↦ r (e x)) = gaussSum r at hs
  rw [he] at hs
  exact congrArg signParity hs

theorem invariant_prod (q : QuadraticForm F₂ V) (r : QuadraticForm F₂ W)
    (hq : q.polarBilin.Nondegenerate) (hr : r.polarBilin.Nondegenerate) :
    invariant (q.prod r) (nondegenerate_polar_prod q r hq hr) =
      invariant q hq + invariant r hr := by
  unfold invariant
  change signParity (gaussSum (fun p : V × W ↦ q p.1 + r p.2)) = _
  rw [gaussSum_prod]
  exact signParity_mul _ _ (gaussSum_ne_zero q hq) (gaussSum_ne_zero r hr)

omit [Fintype W] in
theorem invariant_eq_zero_iff (q : QuadraticForm F₂ V) (hq : q.polarBilin.Nondegenerate) :
    invariant q hq = 0 ↔ 0 < gaussSum q := by
  by_cases hn : gaussSum q < 0
  · simp [invariant, signParity, hn, not_lt_of_gt hn]
  · have hp : 0 < gaussSum q :=
      lt_of_le_of_ne (le_of_not_gt hn) (gaussSum_ne_zero q hq).symm
    simp [invariant, signParity, hn, hp]

omit [Fintype W] in
theorem invariant_eq_one_iff (q : QuadraticForm F₂ V) (hq : q.polarBilin.Nondegenerate) :
    invariant q hq = 1 ↔ gaussSum q < 0 := by
  by_cases hn : gaussSum q < 0 <;> simp [invariant, signParity, hn]

omit [Fintype W] in
theorem invariant_subsingleton [Subsingleton V] (q : QuadraticForm F₂ V)
    (hq : q.polarBilin.Nondegenerate) : invariant q hq = 0 := by
  have hqzero : ∀ x, q x = 0 := fun x ↦ by rw [Subsingleton.elim x 0, map_zero]
  have hc : Fintype.card V = 1 := Fintype.card_eq_one_iff.mpr ⟨0, fun x ↦ Subsingleton.elim x 0⟩
  have hs : gaussSum q = 1 := by simp [gaussSum, hqzero, hc]
  simp [invariant, signParity, hs]

end NoExoticSixSphere.Arf
