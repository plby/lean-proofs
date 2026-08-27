import ErdosProblems.Erdos4.TiltedMoments

/-! Label laws and exact passage from finite witness counts to probability bounds. -/

open scoped BigOperators

namespace Erdos4.Tilted

open FGKMT

noncomputable def uniformLabelLaw (I : Type*) [Fintype I] [Nonempty I] : FiniteLaw I where
  weight _ := (Fintype.card I : ℝ)⁻¹
  nonneg _ := inv_nonneg.mpr (Nat.cast_nonneg _)
  total := by simp [Fintype.card_ne_zero]

theorem uniformLabelLaw_mean (I : Type*) [Fintype I] [Nonempty I] (f : I → ℝ) :
    (uniformLabelLaw I).mean f = (∑ i, f i) / Fintype.card I := by
  simp only [FiniteLaw.mean, uniformLabelLaw, div_eq_mul_inv]
  rw [← Finset.mul_sum]
  ring

noncomputable def pairLaw {I J : Type*} [Fintype I] [Fintype J]
    (σ : FiniteLaw I) (ρ : FiniteLaw J) : FiniteLaw (I × J) where
  weight ij := σ.weight ij.1 * ρ.weight ij.2
  nonneg ij := mul_nonneg (σ.nonneg ij.1) (ρ.nonneg ij.2)
  total := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, ρ.total, mul_one, σ.total]

theorem pairLaw_mean {I J : Type*} [Fintype I] [Fintype J]
    (σ : FiniteLaw I) (ρ : FiniteLaw J) (f : I × J → ℝ) :
    (pairLaw σ ρ).mean f = σ.mean (fun i => ρ.mean (fun j => f (i, j))) := by
  simp only [FiniteLaw.mean, pairLaw, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

theorem prob_le_weight_mul_card {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω)
    (E : Ω → Prop) [DecidablePred E] {b : ℝ} (hb : ∀ o, μ.weight o ≤ b) :
    μ.prob E ≤ b * ((Finset.univ.filter E).card : ℝ) := by
  classical
  rw [FiniteLaw.prob_eq_mean]
  simp only [FiniteLaw.mean, mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
  calc
    _ ≤ ∑ _o ∈ Finset.univ.filter E, b := Finset.sum_le_sum (fun o _ => hb o)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, mul_comm]

theorem prob_le_weight_mul_card_of_injection {Ω α : Type*} [Fintype Ω] [DecidableEq α]
    (μ : FiniteLaw Ω) (E : Ω → Prop) (S : Finset α) (value : Ω → α)
    (hinj : Function.Injective value) (hvalue : ∀ o, E o → value o ∈ S)
    {b : ℝ} (hb : 0 ≤ b) (hweight : ∀ o, μ.weight o ≤ b) :
    μ.prob E ≤ b * (S.card : ℝ) := by
  classical
  have hsub : (Finset.univ.filter E).image value ⊆ S := by
    intro a ha
    obtain ⟨o, ho, rfl⟩ := Finset.mem_image.mp ha
    exact hvalue o (Finset.mem_filter.mp ho).2
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj] at hc
  exact (prob_le_weight_mul_card μ E hweight).trans
    (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hc) hb)

theorem pairLaw_prob_le_count {α : Type*} [DecidableEq α] (S : Finset α)
    (σ : FiniteLaw S) (E : α → α → Prop) [DecidablePred (fun ij : α × α => E ij.1 ij.2)]
    {b : ℝ} (hb : 0 ≤ b) (hσ : ∀ i, σ.weight i ≤ b) :
    (pairLaw σ σ).prob (fun ij => E ij.1.val ij.2.val) ≤
      b ^ 2 * (((S ×ˢ S).filter (fun ij => E ij.1 ij.2)).card : ℝ) := by
  classical
  apply prob_le_weight_mul_card_of_injection (pairLaw σ σ) _ _
    (fun ij => (ij.1.val, ij.2.val))
  · intro ij kl h
    apply Prod.ext
    · exact Subtype.ext (congrArg Prod.fst h)
    · exact Subtype.ext (congrArg Prod.snd h)
  · intro ij hij
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ij.1.property, ij.2.property⟩, hij⟩
  · exact sq_nonneg b
  · intro ij
    exact (mul_le_mul (hσ ij.1) (hσ ij.2) (σ.nonneg ij.2) hb).trans_eq (pow_two b).symm

theorem squared_divisor_count_bound {d X M k : ℕ} (hd : 0 < d) (hdX : d ≤ X)
    {b V : ℝ} (hV : 0 ≤ V) :
    b ^ 2 * (V ^ k * ((M : ℝ) / d + 1)) ^ 2 ≤
      (b * ((M : ℝ) + X)) ^ 2 * (V ^ 2) ^ k / (d : ℝ) ^ 2 := by
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hbracket : (M : ℝ) / d + 1 ≤ ((M : ℝ) + X) / d := by
    calc
      _ = ((M : ℝ) + d) / d := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_right (add_le_add le_rfl (Nat.cast_le.mpr hdX)) hdpos.le
  calc
    _ ≤ b ^ 2 * (V ^ k * (((M : ℝ) + X) / d)) ^ 2 :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (mul_nonneg (pow_nonneg hV _) (by positivity))
          (mul_le_mul_of_nonneg_left hbracket (pow_nonneg hV _)) 2) (sq_nonneg b)
    _ = _ := by
      rw [show (V ^ 2) ^ k = (V ^ k) ^ 2 by rw [← pow_mul, ← pow_mul, Nat.mul_comm]]
      ring

end Erdos4.Tilted
