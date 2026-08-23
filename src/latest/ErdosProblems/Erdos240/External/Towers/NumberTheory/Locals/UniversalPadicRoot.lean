import ErdosProblems.Erdos240.External.Towers.NumberTheory.Quadratic.PrimeFactorization
import ErdosProblems.Erdos240.External.Towers.NumberTheory.Locals.NewtonRootLifting

/-!
# Milne, Chapter 7, Exercise 7-4(a)

For every prime `p`, one of `2`, `17`, and `34` is a square in the
`p`-adic integers.  Consequently `(X^2 - 2)(X^2 - 17)(X^2 - 34)` has a
root in `ℤ_[p]`.
-/

namespace Towers.NumberTheory.Milne

open Polynomial

noncomputable section

/-- The quadratic factors in Milne's Exercise 7-4(a). -/
def universalPadicQuadratic (m : ℤ) : ℤ[X] :=
  X ^ 2 - C m

/-- The polynomial in Milne's Exercise 7-4(a). -/
def universalPadicRoot : ℤ[X] :=
  universalPadicQuadratic 2 * universalPadicQuadratic 17 * universalPadicQuadratic 34

/-- A nonzero square modulo an odd prime lifts to a square in the corresponding
ring of p-adic integers. -/
theorem sq_square_zmod
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (m : ℤ)
    (hm0 : (m : ZMod p) ≠ 0) (hm : IsSquare (m : ZMod p)) :
    ∃ α : ℤ_[p], α ^ 2 = m := by
  obtain ⟨a, ha⟩ :=
    (square_zmod_sq m p).mp hm
  have hsquare : (a : ZMod p) ^ 2 = (m : ZMod p) := by
    have hz : ((a ^ 2 - m : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (a ^ 2 - m) p).mpr ha
    exact sub_eq_zero.mp (by simpa only [Int.cast_sub, Int.cast_pow] using hz)
  have ha0 : (a : ZMod p) ≠ 0 := by
    intro ha0
    rw [ha0, zero_pow (by decide : 2 ≠ 0)] at hsquare
    exact hm0 hsquare.symm
  have htwo0 : ((2 : ℤ) : ZMod p) ≠ 0 := by
    intro h
    have hdvd : p ∣ 2 := by
      exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd (2 : ℤ) p).mp h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) (by decide)).mp hdvd)
  let F : ℤ[X] := universalPadicQuadratic m
  have hFa : F.aeval (a : ℤ_[p]) = ((a ^ 2 - m : ℤ) : ℤ_[p]) := by
    simp [F, universalPadicQuadratic, aeval_def]
  have hFda : F.derivative.aeval (a : ℤ_[p]) = ((2 * a : ℤ) : ℤ_[p]) := by
    simp [F, universalPadicQuadratic, aeval_def]
  have hderiv : ‖F.derivative.aeval (a : ℤ_[p])‖ = 1 := by
    rw [hFda]
    apply le_antisymm (PadicInt.norm_le_one _)
    apply not_lt.mp
    rw [PadicInt.norm_intCast_lt_one_iff]
    intro hdvd
    have hz : ((2 * a : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd (2 * a) p).mpr hdvd
    have hz' : ((2 : ℤ) : ZMod p) * ((a : ℤ) : ZMod p) = 0 := by
      simpa only [Int.cast_mul] using hz
    exact (mul_ne_zero htwo0 ha0) hz'
  have hnewton :
      ‖F.aeval (a : ℤ_[p])‖ < ‖F.derivative.aeval (a : ℤ_[p])‖ ^ 2 := by
    rw [hFa, hderiv, one_pow]
    exact PadicInt.norm_intCast_lt_one_iff.mpr ha
  obtain ⟨α, hroot, -, -, -⟩ := padic_newton_root F a hnewton
  refine ⟨α, ?_⟩
  have hFeval : F.aeval α = α ^ 2 - algebraMap ℤ ℤ_[p] m := by
    simp [F, universalPadicQuadratic, aeval_def]
    cases m <;> simp
  rw [hFeval, sub_eq_zero] at hroot
  simpa using hroot

/-- The exceptional prime `2`: Newton's inequality for `X^2 - 17` at `1`. -/
theorem adic_sq_seventeen :
    ∃ α : ℤ_[2], α ^ 2 = 17 := by
  let F : ℤ[X] := universalPadicQuadratic 17
  have hF1 : F.aeval (1 : ℤ_[2]) = (-16 : ℤ_[2]) := by
    norm_num [F, universalPadicQuadratic, aeval_def]
  have hFd1 : F.derivative.aeval (1 : ℤ_[2]) = (2 : ℤ_[2]) := by
    norm_num [F, universalPadicQuadratic, aeval_def]
  have hFbound : ‖(-16 : ℤ_[2])‖ ≤ (2 : ℝ) ^ (-4 : ℤ) := by
    exact PadicInt.norm_int_le_pow_iff_dvd.mpr (by norm_num)
  have hnewton :
      ‖F.aeval (1 : ℤ_[2])‖ < ‖F.derivative.aeval (1 : ℤ_[2])‖ ^ 2 := by
    rw [hF1, hFd1]
    calc
      ‖(-16 : ℤ_[2])‖ ≤ (2 : ℝ) ^ (-4 : ℤ) := hFbound
      _ < ((2 : ℝ)⁻¹) ^ 2 := by norm_num
      _ = ‖(2 : ℤ_[2])‖ ^ 2 :=
        (congrArg (fun x : ℝ ↦ x ^ 2) (@PadicInt.norm_p 2 inferInstance)).symm
  obtain ⟨α, hroot, -, -, -⟩ := padic_newton_root F 1 hnewton
  refine ⟨α, ?_⟩
  have hFeval : F.aeval α = α ^ 2 - algebraMap ℤ ℤ_[2] 17 := by
    simp [F, universalPadicQuadratic, aeval_def]
  rw [hFeval, sub_eq_zero] at hroot
  simpa using hroot

private theorem square_zmod_seventeen :
    IsSquare ((2 : ℤ) : ZMod 17) := by
  refine ⟨6, ?_⟩
  decide

private theorem ne_zmod_seventeen :
    ((2 : ℤ) : ZMod 17) ≠ 0 := by
  decide

/-- Milne, Exercise 7-4(a): `(X^2-2)(X^2-17)(X^2-34)` has a root in
`ℤ_[p]` for every prime `p`. -/
theorem universalPadic4 (p : ℕ) [Fact p.Prime] :
    ∃ α : ℤ_[p], universalPadicRoot.aeval α = 0 := by
  by_cases hp2 : p = 2
  · subst p
    obtain ⟨α, hα⟩ := adic_sq_seventeen
    refine ⟨α, ?_⟩
    simp [universalPadicRoot, universalPadicQuadratic, aeval_def, hα]
  · have h2zero : ((2 : ℤ) : ZMod p) ≠ 0 := by
      intro h
      have hdvd : p ∣ 2 := by
        exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd (2 : ℤ) p).mp h
      exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) (by decide)).mp hdvd)
    by_cases hp17 : p = 17
    · subst p
      obtain ⟨α, hα⟩ :=
        sq_square_zmod 17 (by decide) 2
          ne_zmod_seventeen square_zmod_seventeen
      refine ⟨α, ?_⟩
      simp [universalPadicRoot, universalPadicQuadratic, aeval_def, hα]
    · have h17zero : ((17 : ℤ) : ZMod p) ≠ 0 := by
        intro h
        have hdvd : p ∣ 17 := by
          exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd (17 : ℤ) p).mp h
        exact hp17 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) (by decide)).mp hdvd)
      have h34zero : ((34 : ℤ) : ZMod p) ≠ 0 := by
        rw [show ((34 : ℤ) : ZMod p) = ((2 : ℤ) : ZMod p) * ((17 : ℤ) : ZMod p) by
          norm_num]
        exact mul_ne_zero h2zero h17zero
      have hsquare :
          IsSquare ((2 : ℤ) : ZMod p) ∨ IsSquare ((17 : ℤ) : ZMod p) ∨
            IsSquare ((34 : ℤ) : ZMod p) := by
        by_cases h2sq : IsSquare ((2 : ℤ) : ZMod p)
        · exact Or.inl h2sq
        by_cases h17sq : IsSquare ((17 : ℤ) : ZMod p)
        · exact Or.inr (Or.inl h17sq)
        · right
          right
          apply (legendreSym.eq_one_iff p h34zero).mp
          rw [show (34 : ℤ) = 2 * 17 by norm_num, legendreSym.mul,
            (legendreSym.eq_neg_one_iff p).mpr h2sq,
            (legendreSym.eq_neg_one_iff p).mpr h17sq]
          norm_num
      rcases hsquare with h2sq | h17sq | h34sq
      · obtain ⟨α, hα⟩ :=
          sq_square_zmod p hp2 2 h2zero h2sq
        refine ⟨α, ?_⟩
        simp [universalPadicRoot, universalPadicQuadratic, aeval_def, hα]
      · obtain ⟨α, hα⟩ :=
          sq_square_zmod p hp2 17 h17zero h17sq
        refine ⟨α, ?_⟩
        simp [universalPadicRoot, universalPadicQuadratic, aeval_def, hα]
      · obtain ⟨α, hα⟩ :=
          sq_square_zmod p hp2 34 h34zero h34sq
        refine ⟨α, ?_⟩
        simp [universalPadicRoot, universalPadicQuadratic, aeval_def, hα]

end

end Towers.NumberTheory.Milne
