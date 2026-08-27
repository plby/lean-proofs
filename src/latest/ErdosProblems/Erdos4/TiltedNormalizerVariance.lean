import ErdosProblems.Erdos4.TiltedLabelLaw

/-! Second moments of the actual importance normalizer, with its diagonal separated. -/

open scoped BigOperators

namespace Erdos4.Tilted

open FGKMT

theorem mean_swap {Ω I : Type*} [Fintype Ω] [Fintype I]
    (ν : FiniteLaw Ω) (σ : FiniteLaw I) (f : Ω → I → ℝ) :
    ν.mean (fun o => σ.mean (f o)) = σ.mean (fun i => ν.mean (fun o => f o i)) := by
  simp only [FiniteLaw.mean, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro o _
  ring

theorem pairLaw_mean_mul {I J : Type*} [Fintype I] [Fintype J]
    (σ : FiniteLaw I) (ρ : FiniteLaw J) (f : I → ℝ) (g : J → ℝ) :
    (pairLaw σ ρ).mean (fun ij => f ij.1 * g ij.2) = σ.mean f * ρ.mean g := by
  rw [pairLaw_mean]
  simp only [FiniteLaw.mean_const_mul]
  exact σ.mean_mul_const f (ρ.mean g)

theorem eventNormalizer_second {Ω I : Type*} [Fintype Ω] [Fintype I]
    (ν : FiniteLaw Ω) (σ : FiniteLaw I) (E : I → Ω → Prop) :
    ν.mean (fun o => eventNormalizer ν σ E o ^ 2) =
      (pairLaw σ σ).mean (fun ij => ν.mean (fun o =>
        eventWeight ν (E ij.1) o * eventWeight ν (E ij.2) o)) := by
  calc
    _ = ν.mean (fun o => (pairLaw σ σ).mean (fun ij =>
        eventWeight ν (E ij.1) o * eventWeight ν (E ij.2) o)) := by
      apply ν.mean_congr
      intro o
      rw [pairLaw_mean_mul σ σ (fun i => eventWeight ν (E i) o) (fun i => eventWeight ν (E i) o)]
      exact pow_two _
    _ = _ := mean_swap ν (pairLaw σ σ) _

theorem pairLaw_diagonal_prob_le {I : Type*} [Fintype I]
    (σ : FiniteLaw I) {b : ℝ} (hσ : ∀ i, σ.weight i ≤ b) :
    (pairLaw σ σ).prob (fun ij => ij.1 = ij.2) ≤ b := by
  classical
  rw [FiniteLaw.prob_eq_mean, pairLaw_mean]
  have heq (i : I) : σ.mean (fun j => if i = j then (1 : ℝ) else 0) = σ.weight i := by
    simp [FiniteLaw.mean]
  simp only [heq]
  exact (σ.mean_mono hσ).trans_eq (σ.mean_const b)

theorem eventNormalizer_variance_le {Ω I : Type*} [Fintype Ω] [Fintype I]
    (ν : FiniteLaw Ω) (σ : FiniteLaw I) (E : I → Ω → Prop)
    (hE : ∀ i, ν.prob (E i) ≠ 0) {B b ε : ℝ} (hB : 0 ≤ B)
    (hσ : ∀ i, σ.weight i ≤ b) (hdiag : ∀ i, 1 / ν.prob (E i) ≤ B)
    (H : I × I → ℝ) (hH : ∀ ij, 0 ≤ H ij)
    (hcross : ∀ i j, i ≠ j →
      ν.prob (fun o => E i o ∧ E j o) / (ν.prob (E i) * ν.prob (E j)) ≤ H (i, j))
    (hmean : (pairLaw σ σ).mean H ≤ 1 + ε) :
    ν.mean (fun o => (eventNormalizer ν σ E o - 1) ^ 2) ≤ B * b + ε := by
  classical
  have hsecond : ν.mean (fun o => eventNormalizer ν σ E o ^ 2) ≤ B * b + (1 + ε) := by
    rw [eventNormalizer_second]
    calc
      _ ≤ (pairLaw σ σ).mean (fun ij => (if ij.1 = ij.2 then B else 0) + H ij) := by
        apply (pairLaw σ σ).mean_mono
        rintro ⟨i, j⟩
        dsimp only
        by_cases hij : i = j
        · subst j
          rw [if_pos rfl]
          have heq : ν.mean (fun o => eventWeight ν (E i) o * eventWeight ν (E i) o) =
              1 / ν.prob (E i) := by
            simpa only [pow_two] using mean_eventWeight_sq ν (E i) (hE i)
          rw [heq]
          linarith [hdiag i, hH (i, i)]
        · rw [if_neg hij, zero_add, mean_eventWeight_mul]
          exact hcross i j hij
      _ = B * (pairLaw σ σ).prob (fun ij => ij.1 = ij.2) + (pairLaw σ σ).mean H := by
        rw [FiniteLaw.mean_add, mean_indicator_const]
      _ ≤ _ := add_le_add
        (mul_le_mul_of_nonneg_left (pairLaw_diagonal_prob_le σ hσ) hB) hmean
  rw [FiniteLaw.mean_sq_sub_one, mean_eventNormalizer ν σ E hE]
  linarith

end Erdos4.Tilted
