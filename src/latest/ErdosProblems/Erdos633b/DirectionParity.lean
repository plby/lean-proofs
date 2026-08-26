import ErdosProblems.Erdos633b.AngleCombinationKernel
import ErdosProblems.Erdos633b.CosetCharacterExtension

/-! Explicit parity characters on the direction subgroup, extended
 equivariantly to all circular directions by coset representatives. -/

namespace Erdos633b

noncomputable def parityOnDirections {a b : ℝ} (P Q : ℤ) (hQ : Q ≠ 0)
    (hrel : (P : ℝ) * a + (Q : ℝ) * b = Real.pi) (ha : Irrational (a / Real.pi))
    (w₀ w₁ : ZMod 2) : (angleCombination a b).range →+ ZMod 2 :=
  ((angleCombination a b).rangeRestrict.liftOfSurjective
    (angleCombination a b).rangeRestrict_surjective)
    ⟨parityCombination w₀ w₁, by
      rw [AddMonoidHom.ker_rangeRestrict]
      exact angleCombination_ker_le_parity P Q hQ hrel ha w₀ w₁⟩

theorem parityOnDirections_apply {a b : ℝ} (P Q : ℤ) (hQ : Q ≠ 0)
    (hrel : (P : ℝ) * a + (Q : ℝ) * b = Real.pi) (ha : Irrational (a / Real.pi))
    (w₀ w₁ : ZMod 2) (z : ℤ × ℤ) :
    parityOnDirections P Q hQ hrel ha w₀ w₁ ((angleCombination a b).rangeRestrict z) =
      parityCombination w₀ w₁ z := by
  unfold parityOnDirections AddMonoidHom.liftOfSurjective
  apply AddMonoidHom.liftOfRightInverse_comp_apply

noncomputable def directionParity {a b : ℝ} (P Q : ℤ) (hQ : Q ≠ 0)
    (hrel : (P : ℝ) * a + (Q : ℝ) * b = Real.pi) (ha : Irrational (a / Real.pi))
    (w₀ w₁ : ZMod 2) : Real.Angle → ZMod 2 :=
  cosetCharacterExtension (angleCombination a b).range (parityOnDirections P Q hQ hrel ha w₀ w₁)

theorem directionParity_add_combination {a b : ℝ} (P Q : ℤ) (hQ : Q ≠ 0)
    (hrel : (P : ℝ) * a + (Q : ℝ) * b = Real.pi) (ha : Irrational (a / Real.pi))
    (w₀ w₁ : ZMod 2) (x : Real.Angle) (z : ℤ × ℤ) :
    directionParity P Q hQ hrel ha w₀ w₁ (x + angleCombination a b z) =
      directionParity P Q hQ hrel ha w₀ w₁ x + parityCombination w₀ w₁ z := by
  exact (cosetCharacterExtension_add (angleCombination a b).range
    (parityOnDirections P Q hQ hrel ha w₀ w₁) x ((angleCombination a b).rangeRestrict z)).trans
    (congrArg (fun t => directionParity P Q hQ hrel ha w₀ w₁ x + t)
      (parityOnDirections_apply P Q hQ hrel ha w₀ w₁ z))

theorem directionParity_add_pi {a b : ℝ} (P Q : ℤ) (hQ : Q ≠ 0)
    (hrel : (P : ℝ) * a + (Q : ℝ) * b = Real.pi) (ha : Irrational (a / Real.pi))
    (w₀ w₁ : ZMod 2) (x : Real.Angle) :
    directionParity P Q hQ hrel ha w₀ w₁ (x + (Real.pi : Real.Angle)) =
      directionParity P Q hQ hrel ha w₀ w₁ x + (P : ZMod 2) * w₀ + (Q : ZMod 2) * w₁ := by
  have hpi : angleCombination a b (P, Q) = (Real.pi : Real.Angle) :=
    congrArg ((↑) : ℝ → Real.Angle) hrel
  have h := directionParity_add_combination P Q hQ hrel ha w₀ w₁ x (P, Q)
  rw [hpi] at h
  simpa only [parityCombination, AddMonoidHom.coe_mk, ZeroHom.coe_mk, add_assoc] using h

theorem exists_direction_parity {a b : ℝ} (P Q : ℤ) (hQ : Q ≠ 0)
    (hrel : (P : ℝ) * a + (Q : ℝ) * b = Real.pi) (ha : Irrational (a / Real.pi))
    (w₀ w₁ : ZMod 2) : ∃ f : Real.Angle → ZMod 2, ∀ (x : Real.Angle) (m n : ℤ),
      f (x + (((m : ℝ) * a + (n : ℝ) * b : ℝ) : Real.Angle)) =
        f x + (m : ZMod 2) * w₀ + (n : ZMod 2) * w₁ := by
  refine ⟨directionParity P Q hQ hrel ha w₀ w₁, ?_⟩
  intro x m n
  have h := directionParity_add_combination P Q hQ hrel ha w₀ w₁ x (m, n)
  simpa only [angleCombination, realAngleCombination, parityCombination, AddMonoidHom.comp_apply,
    AddMonoidHom.coe_mk, ZeroHom.coe_mk, Real.Angle.coe_coeHom, add_assoc] using h

end Erdos633b
