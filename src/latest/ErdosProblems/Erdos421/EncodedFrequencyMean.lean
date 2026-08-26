import ErdosProblems.Erdos421.SeparatedFrequencyMean

/-! # The frequency mean-square bound for any encodable index set -/

namespace Erdos421

open MeasureTheory

theorem separated_frequency_sum_bound {ι : Type*} [Encodable ι]
    (S : Finset ι) (c : ι → ℂ) (ω : ι → ℝ) {δ A B : ℝ} (hδ : 0 < δ)
    (hω : ∀ n ∈ S, A ≤ ω n ∧ ω n ≤ B)
    (hsep : ∀ m ∈ S, ∀ n ∈ S, m ≠ n → δ ≤ |ω m - ω n|) (a b : ℝ) :
    (∫ t in a..b, ‖∑ n ∈ S, c n * oscillatoryPhase (ω n) t‖ ^ 2) ≤
      (b - a + 16 / δ * Real.log ((B - A) / δ + 2)) * ∑ n ∈ S, ‖c n‖ ^ 2 := by
  classical
  let T : Finset ℕ := S.image Encodable.encode
  let d : ℕ → ℂ := fun n ↦ ((Encodable.decode (α := ι) n).map c).getD 0
  let f : ℕ → ℝ := fun n ↦ ((Encodable.decode (α := ι) n).map ω).getD 0
  have hd (i : ι) : d (Encodable.encode i) = c i := by simp [d]
  have hf (i : ι) : f (Encodable.encode i) = ω i := by simp [f]
  have hTf : ∀ n ∈ T, A ≤ f n ∧ f n ≤ B := by
    intro n hn
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hn
    simpa only [hf] using hω i hi
  have hTsep : ∀ m ∈ T, ∀ n ∈ T, m ≠ n → δ ≤ |f m - f n| := by
    intro m hm n hn hmn
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hn
    have hij : i ≠ j := fun he ↦ hmn (congrArg Encodable.encode he)
    simpa only [hf] using hsep i hi j hj hij
  have hsum (t : ℝ) : exponentialSum T d f t =
      ∑ n ∈ S, c n * oscillatoryPhase (ω n) t := by
    unfold exponentialSum
    dsimp only [T]
    rw [Finset.sum_image (fun i _ j _ he ↦ Encodable.encode_injective he)]
    simp only [hd, hf]
  have henergy : (∑ n ∈ T, ‖d n‖ ^ 2) = ∑ n ∈ S, ‖c n‖ ^ 2 := by
    dsimp only [T]
    rw [Finset.sum_image (fun i _ j _ he ↦ Encodable.encode_injective he)]
    simp only [hd]
  simpa only [hsum, henergy] using
    separated_frequency_mean_square_bound T d f hδ hTf hTsep a b

end Erdos421
