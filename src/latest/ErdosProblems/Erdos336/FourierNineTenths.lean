import ErdosProblems.Erdos336.FreimanSemicircle
import ErdosProblems.Erdos336.FourierDirectionCircle

/- Ported from Lean 4.31.0 to 4.33.0; imports, helper namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos336

open scoped Real BigOperators ComplexConjugate

noncomputable def circleLowerArg (z : Circle) : ℝ :=
  if Complex.arg (z : ℂ) = Real.pi then -Real.pi
  else Complex.arg (z : ℂ)

lemma circleLowerArg_mem (z : Circle) :
    -Real.pi ≤ circleLowerArg z ∧ circleLowerArg z < Real.pi := by
  unfold circleLowerArg
  by_cases h : Complex.arg (z : ℂ) = Real.pi
  · simp [h, Real.pi_pos]
  · simp only [h, if_false]
    exact ⟨(Complex.neg_pi_lt_arg (z : ℂ)).le,
      lt_of_le_of_ne (Complex.arg_le_pi (z : ℂ)) h⟩

lemma cos_circleLowerArg (z : Circle) :
    Real.cos (circleLowerArg z) = (z : ℂ).re := by
  have hnorm : ‖(z : ℂ)‖ = 1 := by
    simpa using z.property
  have hz : (z : ℂ) ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hnorm
    norm_num at hnorm
  unfold circleLowerArg
  by_cases h : Complex.arg (z : ℂ) = Real.pi
  · simp only [h, if_true]
    rw [Real.cos_neg]
    rw [← h]
    rw [Complex.cos_arg hz, hnorm, div_one]
  · simp only [h, if_false]
    rw [Complex.cos_arg hz, hnorm, div_one]

variable {N : ℕ} [NeZero N]

lemma sum_rotated_fourier_re
    (A : Finset (ZMod N)) (k : ZMod N)
    (hF : cyclicFinsetFourier A k ≠ 0) :
    (∑ x ∈ A, (((fourierDirectionCircle A k hF : Circle) : ℂ) *
      ZMod.stdAddChar (-(x * k))).re) =
      ‖cyclicFinsetFourier A k‖ := by
  let F := cyclicFinsetFourier A k
  have hnorm : (0 : ℝ) < ‖F‖ := norm_pos_iff.mpr hF
  calc
    (∑ x ∈ A, (((fourierDirectionCircle A k hF : Circle) : ℂ) *
      ZMod.stdAddChar (-(x * k))).re) =
        (((fourierDirectionCircle A k hF : Circle) : ℂ) *
          ∑ x ∈ A, ZMod.stdAddChar (-(x * k))).re := by
            rw [Finset.mul_sum]
            simp
    _ = ((starRingEnd ℂ F / ‖F‖) * F).re := by
      simp [F, cyclicFinsetFourier]
    _ = ‖F‖ := by
      rw [div_mul_eq_mul_div]
      rw [show starRingEnd ℂ F * F = (‖F‖ ^ 2 : ℝ) by
        rw [show starRingEnd ℂ F * F = F * starRingEnd ℂ F by ring]
        simpa [Complex.normSq_eq_norm_sq] using Complex.mul_conj F]
      rw [← Complex.ofReal_div, Complex.ofReal_re]
      field_simp


/-- A Fourier coefficient above four fifths has more than nine tenths of its
terms in a consistently half-open semicircle. -/
theorem exists_fourier_halfopen_slice_nine_tenths
    (A : Finset (ZMod N)) (k : ZMod N)
    (hF : cyclicFinsetFourier A k ≠ 0)
    (hlarge : 4 * (A.card : ℝ) <
      5 * ‖cyclicFinsetFourier A k‖) :
    ∃ θ ∈ Set.Icc (0 : ℝ) Real.pi,
      ∃ B : Finset (ZMod N), B ⊆ A ∧
        9 * A.card < 10 * B.card ∧
        ∀ x ∈ B, semicircleArcMem
          (circleLowerArg (fourierDirectionCircle A k hF *
            ZMod.toCircle (-(x * k)))) θ := by
  let w : ZMod N → Circle := fun x => fourierDirectionCircle A k hF *
    ZMod.toCircle (-(x * k))
  let φ : ↥A → ℝ := fun x => circleLowerArg (w x)
  have hφ : ∀ x, -Real.pi ≤ φ x ∧ φ x < Real.pi := by
    intro x
    exact circleLowerArg_mem (w x)
  let g : ZMod N → ℝ := fun x => (((w x : Circle) : ℂ)).re
  have hsum : (∑ x, Real.cos (φ x)) =
      ‖cyclicFinsetFourier A k‖ := by
    have hcos : ∀ x : ↥A, Real.cos (φ x) = g x := by
      intro x
      exact cos_circleLowerArg (w x)
    simp_rw [hcos]
    rw [← Finset.sum_subtype A (by simp) g]
    simpa only [g, w, Circle.coe_mul, ← ZMod.stdAddChar_apply] using
      sum_rotated_fourier_re A k hF
  have hresult : 4 * (Fintype.card ↥A : ℝ) <
      5 * ∑ x, Real.cos (φ x) := by
    rw [hsum]
    simpa using hlarge
  obtain ⟨θ, hθ, hcount⟩ :=
    exists_halfopen_semicircle_nine_tenths φ hφ hresult
  let p : ZMod N → Prop := fun x => semicircleArcMem
    (circleLowerArg (w x)) θ
  let B := A.filter p
  have hcard : (Finset.univ.filter fun x : ↥A => p x).card = B.card := by
    rw [Finset.univ_eq_attach A]
    have heq := congrArg Finset.card (Finset.filter_attach p A)
    simpa [B] using heq
  refine ⟨θ, hθ, B, Finset.filter_subset _ _, ?_, ?_⟩
  · change 9 * A.card < 10 * B.card
    change 9 * Fintype.card ↥A <
      10 * (Finset.univ.filter fun x : ↥A => p x).card at hcount
    rw [hcard] at hcount
    simpa using hcount
  · intro x hx
    change p x
    exact (Finset.mem_filter.mp hx).2

end Erdos336
