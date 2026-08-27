import ErdosProblems.Erdos4.FGKMTMaskedSupport
import ErdosProblems.Erdos4.FGKMTMaskedDecay
import ErdosProblems.Erdos4.FGKMTWeightedMeanSquare
import ErdosProblems.Erdos4.AnchoredFourierAverage

/-! Exact weighted source averages and the small/high character decomposition. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open Classical FiniteCharacterSupport ProductCharacterEncoding
open ProductFourierInversion AnchoredFourierAverage

variable {P Q : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q] {k : ℕ}
    (ell₀ : P → ℕ) (ell₁ : Q → ℕ)
    [∀ p, Fact (ell₀ p).Prime] [∀ q, Fact (ell₁ q).Prime]

theorem aggregateUnitWeight_truncated_inversion (b : ℝ) (R M : ℕ)
    (hM : (∏ p, ell₀ p) * R ^ 2 ≤ M ^ 2)
    (h₀ : ∀ p, Fin k → ZMod (ell₀ p)) (h₁ : ∀ q, Fin k → ZMod (ell₁ q))
    (u : ∀ s, (ZMod (Sum.elim ell₀ ell₁ s))ˣ) :
    (aggregateUnitWeight ell₀ ell₁ b R h₀ h₁ u : ℂ) =
      aggregateUnitFourier ell₀ ell₁ b R h₀ h₁ (fun _ => 1) +
        ∑ chi : smallCharacters (Sum.elim ell₀ ell₁) M,
          aggregateUnitFourier ell₀ ell₁ b R h₀ h₁ chi.val *
            ProductFourierInversion.value (Sum.elim ell₀ ell₁) chi.val u := by
  let f : (∀ s, DirichletCharacter ℂ (Sum.elim ell₀ ell₁ s)) → ℂ :=
    fun chi => aggregateUnitFourier ell₀ ell₁ b R h₀ h₁ chi *
      ProductFourierInversion.value (Sum.elim ell₀ ell₁) chi u
  let oneChar : ∀ s, DirichletCharacter ℂ (Sum.elim ell₀ ell₁ s) := fun _ => 1
  have hs : smallCharacters (Sum.elim ell₀ ell₁) M ⊆ Finset.univ.erase oneChar := by
    intro chi hchi
    exact Finset.mem_erase.mpr
      ⟨((mem_smallCharacters (Sum.elim ell₀ ell₁) M chi).mp hchi).1, Finset.mem_univ _⟩
  have hsub : (∑ chi ∈ smallCharacters (Sum.elim ell₀ ell₁) M, f chi) =
      ∑ chi ∈ Finset.univ.erase oneChar, f chi := by
    apply Finset.sum_subset hs
    intro chi hchi hnot
    have hne : chi ≠ fun _ => 1 := (Finset.mem_erase.mp hchi).1
    simp only [f, aggregateUnitFourier_zero_outside ell₀ ell₁ b R M hM h₀ h₁ chi hne hnot,
      zero_mul]
  have hone : f oneChar = aggregateUnitFourier ell₀ ell₁ b R h₀ h₁ (fun _ => 1) := by
    have hv : ProductFourierInversion.value (Sum.elim ell₀ ell₁) (fun _ => 1) u = 1 := by
      unfold ProductFourierInversion.value
      exact Finset.prod_eq_one (fun s _ => MulChar.one_apply_coe (u s))
    change aggregateUnitFourier ell₀ ell₁ b R h₀ h₁ (fun _ => 1) *
      ProductFourierInversion.value (Sum.elim ell₀ ell₁) (fun _ => 1) u = _
    rw [hv, mul_one]
  calc
    _ = ∑ chi, f chi := (aggregateUnitWeight_inversion ell₀ ell₁ b R h₀ h₁ u).symm
    _ = (∑ chi ∈ Finset.univ.erase oneChar, f chi) + f oneChar :=
      (Finset.sum_erase_add _ _ (Finset.mem_univ oneChar)).symm
    _ = aggregateUnitFourier ell₀ ell₁ b R h₀ h₁ (fun _ => 1) +
        ∑ chi ∈ smallCharacters (Sum.elim ell₀ ell₁) M, f chi := by
      rw [← hsub, hone]
      ring
    _ = _ := by rw [Finset.sum_coe_sort (smallCharacters (Sum.elim ell₀ ell₁) M) f]

noncomputable def highMaskedCoefficient (b : ℝ) (R M : ℕ)
    (h₀ : ∀ p, Fin k → ZMod (ell₀ p)) (h₁ : ∀ q, Fin k → ZMod (ell₁ q))
    (chi : smallCharacters (Sum.elim ell₀ ell₁) M) : ℂ :=
  if (fun q => chi.val (.inr q)) = (fun _ => 1) then 0
  else aggregateUnitFourier ell₀ ell₁ b R h₀ h₁ chi.val

noncomputable def lowMaskedCoefficient (b : ℝ) (R M : ℕ)
    (h₀ : ∀ p, Fin k → ZMod (ell₀ p)) (h₁ : ∀ q, Fin k → ZMod (ell₁ q))
    (chi : smallCharacters (Sum.elim ell₀ ell₁) M) : ℂ :=
  if (fun q => chi.val (.inr q)) = (fun _ => 1)
  then aggregateUnitFourier ell₀ ell₁ b R h₀ h₁ chi.val else 0

theorem high_add_low_coefficient (b : ℝ) (R M : ℕ)
    (h₀ : ∀ p, Fin k → ZMod (ell₀ p)) (h₁ : ∀ q, Fin k → ZMod (ell₁ q))
    (chi : smallCharacters (Sum.elim ell₀ ell₁) M) :
    highMaskedCoefficient ell₀ ell₁ b R M h₀ h₁ chi +
      lowMaskedCoefficient ell₀ ell₁ b R M h₀ h₁ chi =
        aggregateUnitFourier ell₀ ell₁ b R h₀ h₁ chi.val := by
  unfold highMaskedCoefficient lowMaskedCoefficient
  split_ifs <;> simp

theorem highMaskedCoefficient_norm_le {b : ℝ} (hb : 0 ≤ b) (R M : ℕ)
    (hell : ∀ q, k + 2 ≤ ell₁ q) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hlocal : ∀ q, 20 * (k : ℝ) ^ 3 ≤ δ * ell₁ q)
    (h₀ : ∀ p, Fin k → ZMod (ell₀ p)) (h₁ : ∀ q, Fin k → ZMod (ell₁ q))
    (hinj : ∀ q, Function.Injective (h₁ q))
    (chi : smallCharacters (Sum.elim ell₀ ell₁) M) :
    ‖highMaskedCoefficient ell₀ ell₁ b R M h₀ h₁ chi‖ ≤
      (k : ℝ) * maskedFourierScale ell₀ ell₁ b R h₀ * δ := by
  unfold highMaskedCoefficient
  split_ifs with hhigh
  · rw [norm_zero]
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg k)
      (maskedFourierScale_nonneg ell₀ ell₁ b R h₀)) hδ0
  · exact aggregateUnitFourier_norm_le_high ell₀ ell₁ hb R hell hδ1 hlocal
      h₀ h₁ hinj chi.val hhigh

theorem lowMaskedCoefficient_norm_le {b : ℝ} (hb : 0 ≤ b) (R M : ℕ)
    (hell : ∀ q, k + 2 ≤ ell₁ q) {δ : ℝ} (hδ1 : δ ≤ 1)
    (hlocal : ∀ q, 20 * (k : ℝ) ^ 3 ≤ δ * ell₁ q)
    (h₀ : ∀ p, Fin k → ZMod (ell₀ p)) (h₁ : ∀ q, Fin k → ZMod (ell₁ q))
    (hinj : ∀ q, Function.Injective (h₁ q))
    (chi : smallCharacters (Sum.elim ell₀ ell₁) M) :
    ‖lowMaskedCoefficient ell₀ ell₁ b R M h₀ h₁ chi‖ ≤
      (k : ℝ) * maskedFourierScale ell₀ ell₁ b R h₀ := by
  unfold lowMaskedCoefficient
  split_ifs
  · exact aggregateUnitFourier_norm_le ell₀ ell₁ hb R hell hδ1 hlocal h₀ h₁ hinj chi.val
  · rw [norm_zero]
    exact mul_nonneg (Nat.cast_nonneg k) (maskedFourierScale_nonneg ell₀ ell₁ b R h₀)

theorem aggregate_weighted_source_average_eq (b : ℝ) (R M : ℕ)
    (hM : (∏ p, ell₀ p) * R ^ 2 ≤ M ^ 2)
    (h₀ : ∀ p, Fin k → ZMod (ell₀ p)) (h₁ : ∀ q, Fin k → ZMod (ell₁ q))
    (sources : Finset ℕ) (hs : ∀ p ∈ sources, p.Coprime (modulus (Sum.elim ell₀ ell₁)))
    (a : sources → ℂ) (q : ℕ) (hq : q.Coprime (modulus (Sum.elim ell₀ ell₁))) :
    (∑ p : sources, a p * (aggregateUnitWeight ell₀ ell₁ b R h₀ h₁
      (unitPoint (Sum.elim ell₀ ell₁) p (hs p p.property) /
        unitPoint (Sum.elim ell₀ ell₁) q hq) : ℂ)) =
      (∑ p : sources, a p) * aggregateUnitFourier ell₀ ell₁ b R h₀ h₁ (fun _ => 1) +
        ProductPrimeMeanSquare.weightedSourceError (Sum.elim ell₀ ell₁) M
          (fun chi => aggregateUnitFourier ell₀ ell₁ b R h₀ h₁ chi.val) sources a q := by
  simp_rw [aggregateUnitWeight_truncated_inversion ell₀ ell₁ b R M hM h₀ h₁,
    value_ratio, mul_add, Finset.mul_sum]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  unfold ProductPrimeMeanSquare.weightedSourceError
  apply Finset.sum_congr rfl
  intro chi _
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p _
  ring

theorem aggregate_source_error_split (b : ℝ) (R M : ℕ)
    (h₀ : ∀ p, Fin k → ZMod (ell₀ p)) (h₁ : ∀ q, Fin k → ZMod (ell₁ q))
    (sources : Finset ℕ) (a : sources → ℂ) (q : ℕ) :
    ProductPrimeMeanSquare.weightedSourceError (Sum.elim ell₀ ell₁) M
      (fun chi => aggregateUnitFourier ell₀ ell₁ b R h₀ h₁ chi.val) sources a q =
        ProductPrimeMeanSquare.weightedSourceError (Sum.elim ell₀ ell₁) M
          (highMaskedCoefficient ell₀ ell₁ b R M h₀ h₁) sources a q +
        ProductPrimeMeanSquare.weightedSourceError (Sum.elim ell₀ ell₁) M
          (lowMaskedCoefficient ell₀ ell₁ b R M h₀ h₁) sources a q := by
  rw [← ProductPrimeMeanSquare.weightedSourceError_add]
  congr 1
  funext chi
  exact (high_add_low_coefficient ell₀ ell₁ b R M h₀ h₁ chi).symm

end Erdos4.FGKMT
