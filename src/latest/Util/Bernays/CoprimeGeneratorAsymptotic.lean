import Util.Bernays.ResidueCosetCounts

/-!
# The area term for generators in coprime residue classes
-/

open scoped Classical

namespace Bernays

theorem coprimeQuadraticBall_error {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (I F : Ideal (QuadraticAlgebra ℤ d b)) (hI : I ≠ ⊥) (hF : F ≠ ⊥)
    (hIF : IsCoprime I F) :
    ∃ K : ℝ, 0 < K ∧ ∀ T : ℕ,
      |(Nat.card (CoprimeQuadraticBall I F T) : ℝ) -
        ((Nat.card (QuadraticAlgebra ℤ d b ⧸ F)ˣ : ℝ) *
          (4 * Real.pi / (((F * I).cardQuot : ℝ) *
            ZLattice.covolume (quadraticIdealLattice d b ⊤)))) * T| ≤
      K * (Real.sqrt (T : ℝ) + 1) := by
  let := quadraticOrderIsDomain hD
  let O := QuadraticAlgebra ℤ d b
  let : Finite (O ⧸ F) := Ring.HasFiniteQuotients.finiteQuotient hF
  let := Fintype.ofFinite (O ⧸ F)
  have hFI : F * I ≠ ⊥ := (Ideal.mul_eq_bot).not.mpr (not_or.mpr ⟨hF, hI⟩)
  obtain ⟨K, hK, hbound⟩ := quadraticIdealCosetBall_error hD (F * I) hFI
  have hU : (0 : ℝ) < Nat.card (O ⧸ F)ˣ := by exact_mod_cast Nat.card_pos (α := (O ⧸ F)ˣ)
  refine ⟨Nat.card (O ⧸ F)ˣ * K, mul_pos hU hK, ?_⟩
  intro T
  have hsurj := quotient_surjective_on_coprime_ideal I F hIF
  let c : (O ⧸ F)ˣ → I := fun u => (hsurj (u : O ⧸ F)).choose
  have hc (u : (O ⧸ F)ˣ) : Ideal.Quotient.mk F (c u : O) = u := (hsurj (u : O ⧸ F)).choose_spec
  let C := 4 * Real.pi / (((F * I).cardQuot : ℝ) * ZLattice.covolume (quadraticIdealLattice d b ⊤))
  have heq : (Nat.card (CoprimeQuadraticBall I F T) : ℝ) - (Nat.card (O ⧸ F)ˣ : ℝ) * C * T =
      ∑ u : (O ⧸ F)ˣ, ((Nat.card (quadraticIdealCosetBall (F * I) (c u) T) : ℝ) - C * T) := by
    rw [coprimeQuadraticBall_eq_sum_cosets hD I F hIF c hc, Nat.cast_sum,
      Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
      Nat.card_eq_fintype_card]
    ring
  change |(Nat.card (CoprimeQuadraticBall I F T) : ℝ) - (Nat.card (O ⧸ F)ˣ : ℝ) * C * T| ≤ _
  rw [heq]
  calc
    _ ≤ ∑ u : (O ⧸ F)ˣ,
        |(Nat.card (quadraticIdealCosetBall (F * I) (c u) T) : ℝ) - C * T| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _u : (O ⧸ F)ˣ, K * (Real.sqrt (T : ℝ) + 1) :=
      Finset.sum_le_sum fun u _ => hbound (c u) T
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
      Nat.card_eq_fintype_card, mul_assoc]

end Bernays
