import Util.Bernays.GoodNormArithmetic

/-!
# Genus characters and their pullbacks to the ideal class group
-/

namespace Bernays

noncomputable def genusClassChar {R : Type*} [CommRing R] [IsDomain R]
    (ψ : AddChar (Additive (GenusGroup R)) ℂ) : AddChar (Additive (ClassGroup R)) ℂ :=
  ψ.compAddMonoidHom (genusMap (R := R)).toAdditive

theorem genusClassChar_apply {R : Type*} [CommRing R] [IsDomain R]
    (ψ : AddChar (Additive (GenusGroup R)) ℂ) (C : ClassGroup R) :
    genusClassChar ψ (Additive.ofMul C) = ψ (Additive.ofMul (genusMap C)) := rfl

theorem genusClassChar_ne_zero {R : Type*} [CommRing R] [IsDomain R]
    (ψ : AddChar (Additive (GenusGroup R)) ℂ) (hψ : ψ ≠ 0) : genusClassChar ψ ≠ 0 := by
  have hsurj : Function.Surjective (genusMap (R := R)).toAdditive := by
    intro x
    obtain ⟨C, hC⟩ := QuotientGroup.mk'_surjective classSquareSubgroup x.toMul
    exact ⟨Additive.ofMul C, congrArg Additive.ofMul hC⟩
  intro h
  apply hψ
  apply AddChar.compAddMonoidHom_injective_left _ hsurj
  have hz : (0 : AddChar (Additive (GenusGroup R)) ℂ).compAddMonoidHom
      (genusMap (R := R)).toAdditive = 0 := by
    ext C
    rfl
  exact h.trans hz.symm

theorem genusChar_sq {R : Type*} [CommRing R] [IsDomain R]
    (ψ : AddChar (Additive (GenusGroup R)) ℂ) (g : GenusGroup R) :
    ψ (Additive.ofMul g) ^ 2 = 1 := by
  rw [← AddChar.map_nsmul_eq_pow, ← ofMul_pow, genusGroup_sq]
  exact ψ.map_zero_eq_one

theorem genusChar_norm {R : Type*} [CommRing R] [IsDomain R]
    (ψ : AddChar (Additive (GenusGroup R)) ℂ) (g : GenusGroup R) :
    ‖ψ (Additive.ofMul g)‖ = 1 := by
  have h := congrArg norm (genusChar_sq ψ g)
  rw [norm_pow, norm_one] at h
  nlinarith [norm_nonneg (ψ (Additive.ofMul g))]

theorem quadraticBadIdeal_cardQuot {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    (quadraticBadIdeal d b).cardQuot = discriminantLevel (b ^ 2 + 4 * d) ^ 2 :=
  principal_nat_cardQuot hD (discriminantLevel_pos hD.ne)

theorem quadraticBadIdeal_ne_bot {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    quadraticBadIdeal d b ≠ ⊥ := by
  rw [quadraticBadIdeal, ne_eq, Ideal.span_singleton_eq_bot]
  exact quadratic_natCast_ne_zero (discriminantLevel_pos hD.ne)

theorem quadraticBadIdeal_ne_top {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    quadraticBadIdeal d b ≠ ⊤ := by
  intro h
  have hnorm := quadraticBadIdeal_cardQuot hD
  rw [h, Submodule.cardQuot_top] at hnorm
  have hp := discriminantLevel_one_lt hD.ne
  nlinarith

theorem genusIdealLSeries_continuation {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ ψ : AddChar (Additive (GenusGroup (QuadraticAlgebra ℤ d b))) ℂ, ψ ≠ 0 →
      ∃ G : ℂ → ℂ,
        (∀ s : ℂ, (1 / 2 : ℝ) < s.re → DifferentiableAt ℂ G s) ∧
        (∀ s : ℂ, 1 < s.re → G s = LSeries
          (weightedIdealNormCoeff hD (quadraticBadIdeal d b)
            (fun C => ψ (Additive.ofMul (genusMap C)))) s) := by
  let := quadraticOrderIsDomain hD
  intro ψ hψ
  exact classCharacterLSeries_continuation hD (quadraticBadIdeal d b)
    (quadraticBadIdeal_ne_bot hD) (quadraticBadIdeal_ne_top hD)
    (genusClassChar ψ) (genusClassChar_ne_zero ψ hψ)

end Bernays
