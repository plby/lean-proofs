import ErdosProblems.Erdos67.StationaryEntropy

/-!
# Conditional finite entropy

Conditional probability vectors are defined even at zero-probability conditioning
values. The weighted formulas do not depend on that choice.
-/

open scoped BigOperators
open Finset

namespace Erdos67.FiniteEntropy

variable {α β γ Ω : Type*}
variable [Fintype α] [Fintype β] [Fintype γ] [Fintype Ω]

/-- Conditional law of the first coordinate given a value of the second. -/
noncomputable def conditionalLaw (p : FinProb (α × β)) (b : β) : FinProb α :=
  if hb : sndMarginal p b = 0 then fstMarginal p else
    ⟨fun a ↦ p (a, b) / sndMarginal p b, by
      constructor
      · intro a
        exact div_nonneg (prob_nonneg p (a, b)) (prob_nonneg (sndMarginal p) b)
      · rw [← Finset.sum_div, ← sndMarginal_apply, div_self hb]⟩

theorem joint_eq_marginal_mul_conditional (p : FinProb (α × β)) (a : α) (b : β) :
    p (a, b) = sndMarginal p b * conditionalLaw p b a := by
  by_cases hb : sndMarginal p b = 0
  · have hz : p (a, b) = 0 := by
      apply le_antisymm
      · simpa only [hb] using joint_le_sndMarginal p a b
      · exact prob_nonneg p (a, b)
    simp only [hb, zero_mul, hz]
  · simp only [conditionalLaw, dif_neg hb]
    exact (mul_div_cancel₀ (p (a, b)) hb).symm

theorem entropy_eq_marginal_add_weighted_conditional (p : FinProb (α × β)) :
    entropy p = entropy (sndMarginal p) +
      ∑ b, sndMarginal p b * entropy (conditionalLaw p b) := by
  unfold entropy
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  have hrow (b : β) :
      (∑ a, Real.negMulLog (p (a, b))) = Real.negMulLog (sndMarginal p b) +
        sndMarginal p b * ∑ a, Real.negMulLog (conditionalLaw p b a) := by
    simp_rw [joint_eq_marginal_mul_conditional p, Real.negMulLog_mul]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, stdSimplex.sum_eq_one,
      one_mul, ← Finset.mul_sum]
  simp_rw [hrow]
  exact Finset.sum_add_distrib

theorem condEntropy_eq_weighted_conditional (p : FinProb (α × β)) :
    condEntropy p = ∑ b, sndMarginal p b * entropy (conditionalLaw p b) := by
  rw [condEntropy, entropy_eq_marginal_add_weighted_conditional]
  ring

theorem conditionalLaw_product (p : FinProb α) (q : FinProb β) (b : β) :
    conditionalLaw (product p q) b = p := by
  classical
  by_cases hb : q b = 0
  · simp only [conditionalLaw, sndMarginal_product, dif_pos hb, fstMarginal_product]
  · apply Subtype.ext
    funext a
    change conditionalLaw (product p q) b a = p a
    simp only [conditionalLaw, sndMarginal_product, dif_neg hb]
    change p a * q b / q b = p a
    exact mul_div_cancel_right₀ (p a) hb

/-- Apply a function to the first coordinate of a joint probability vector. -/
noncomputable def mapLeft (p : FinProb (α × γ)) (f : α → β) : FinProb (β × γ) :=
  stdSimplex.map (fun z ↦ (f z.1, z.2)) p

theorem sndMarginal_mapLeft (p : FinProb (α × γ)) (f : α → β) :
    sndMarginal (mapLeft p f) = sndMarginal p := by
  unfold sndMarginal mapLeft
  rw [stdSimplex.map_comp_apply]
  rfl

theorem fstMarginal_mapLeft (p : FinProb (α × γ)) (f : α → β) :
    fstMarginal (mapLeft p f) = stdSimplex.map f (fstMarginal p) := by
  unfold fstMarginal mapLeft
  rw [stdSimplex.map_comp_apply, stdSimplex.map_comp_apply]
  rfl

open scoped Classical in
theorem mapLeft_apply (p : FinProb (α × γ)) (f : α → β) (b : β) (c : γ) :
    mapLeft p f (b, c) = ∑ a, if f a = b then p (a, c) else 0 := by
  classical
  simp only [mapLeft, stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply,
    Finset.sum_filter, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hab : f a = b
  · simp [hab, Prod.mk.injEq]
  · simp [hab, Prod.mk.injEq]

theorem conditionalLaw_mapLeft (p : FinProb (α × γ)) (f : α → β) (c : γ) :
    conditionalLaw (mapLeft p f) c = stdSimplex.map f (conditionalLaw p c) := by
  classical
  by_cases hc : sndMarginal p c = 0
  · simp only [conditionalLaw, sndMarginal_mapLeft, dif_pos hc,
      fstMarginal_mapLeft]
  · apply Subtype.ext
    funext b
    change conditionalLaw (mapLeft p f) c b = stdSimplex.map f (conditionalLaw p c) b
    rw [stdSimplex.map_coe]
    simp only [conditionalLaw, sndMarginal_mapLeft, dif_neg hc,
      FunOnFinite.linearMap_apply_apply, Finset.sum_filter]
    change mapLeft p f (b, c) / sndMarginal p c =
      ∑ a, if f a = b then p (a, c) / sndMarginal p c else 0
    rw [mapLeft_apply, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro a _
    split_ifs <;> simp

theorem conditionalLaw_map_fst (p : FinProb ((α × β) × γ)) (c : γ) :
    conditionalLaw (mapLeft p Prod.fst) c = fstMarginal (conditionalLaw p c) :=
  conditionalLaw_mapLeft p Prod.fst c

theorem conditionalLaw_map_snd (p : FinProb ((α × β) × γ)) (c : γ) :
    conditionalLaw (mapLeft p Prod.snd) c = sndMarginal (conditionalLaw p c) :=
  conditionalLaw_mapLeft p Prod.snd c

/-- Subadditivity of entropy conditional on a third variable. -/
theorem condEntropy_pair_le (p : FinProb ((α × β) × γ)) :
    condEntropy p ≤ condEntropy (mapLeft p Prod.fst) +
      condEntropy (mapLeft p Prod.snd) := by
  rw [condEntropy_eq_weighted_conditional, condEntropy_eq_weighted_conditional,
    condEntropy_eq_weighted_conditional]
  simp only [sndMarginal_mapLeft, conditionalLaw_map_fst, conditionalLaw_map_snd]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro c _
  have h := mul_le_mul_of_nonneg_left
    (entropy_le_add_marginals (conditionalLaw p c)) (prob_nonneg (sndMarginal p) c)
  simpa only [mul_add] using h

theorem mapLeft_jointLaw (p : FinProb Ω) (X : Ω → α) (Z : Ω → γ) (f : α → β) :
    mapLeft (jointLaw p X Z) f = jointLaw p (f ∘ X) Z := by
  unfold mapLeft jointLaw law
  rw [stdSimplex.map_comp_apply]
  rfl

/-- Conditional subadditivity for finite random variables. -/
theorem rvCondEntropy_pair_le (p : FinProb Ω) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) :
    rvCondEntropy p (fun ω ↦ (X ω, Y ω)) Z ≤
      rvCondEntropy p X Z + rvCondEntropy p Y Z := by
  have h := condEntropy_pair_le (jointLaw p (fun ω ↦ (X ω, Y ω)) Z)
  simpa only [mapLeft_jointLaw, Function.comp_def, rvCondEntropy] using h

theorem entropy_map_equiv (p : FinProb α) (e : α ≃ β) :
    entropy (stdSimplex.map e p) = entropy p := by
  apply le_antisymm (entropy_map_le e p)
  have h := entropy_map_le e.symm (stdSimplex.map e p)
  have he : e.symm ∘ e = id := by funext a; simp
  rw [stdSimplex.map_comp_apply, he, stdSimplex.map_id_apply] at h
  exact h

theorem rvEntropy_equiv (p : FinProb Ω) (X : Ω → α) (e : α ≃ β) :
    rvEntropy p (e ∘ X) = rvEntropy p X := by
  unfold rvEntropy law
  rw [← stdSimplex.map_comp_apply, entropy_map_equiv]

theorem rvEntropy_pair_comm (p : FinProb Ω) (X : Ω → α) (Y : Ω → β) :
    rvEntropy p (fun ω ↦ (X ω, Y ω)) = rvEntropy p (fun ω ↦ (Y ω, X ω)) := by
  exact (rvEntropy_equiv p (fun ω ↦ (Y ω, X ω)) (Equiv.prodComm β α))

theorem rvEntropy_triple_assoc (p : FinProb Ω) (X : Ω → α)
    (Y : Ω → β) (Z : Ω → γ) :
    rvEntropy p (fun ω ↦ ((X ω, Y ω), Z ω)) =
      rvEntropy p (fun ω ↦ (X ω, (Y ω, Z ω))) := by
  exact (rvEntropy_equiv p (fun ω ↦ ((X ω, Y ω), Z ω))
    (Equiv.prodAssoc α β γ)).symm

theorem rvCondEntropy_eq_sub (p : FinProb Ω) (X : Ω → α) (Y : Ω → β) :
    rvCondEntropy p X Y = rvEntropy p (fun ω ↦ (X ω, Y ω)) - rvEntropy p Y := by
  rw [rvCondEntropy, condEntropy, sndMarginal_jointLaw]
  rfl

theorem rvCondEntropy_chain_rule (p : FinProb Ω) (X : Ω → α)
    (Y : Ω → β) (Z : Ω → γ) :
    rvCondEntropy p (fun ω ↦ (X ω, Y ω)) Z =
      rvCondEntropy p Y Z + rvCondEntropy p X (fun ω ↦ (Y ω, Z ω)) := by
  simp only [rvCondEntropy_eq_sub]
  rw [rvEntropy_triple_assoc]
  ring

/-- Additional conditioning cannot increase finite entropy. -/
theorem rvCondEntropy_condition_pair_le (p : FinProb Ω) (X : Ω → α)
    (Y : Ω → β) (Z : Ω → γ) :
    rvCondEntropy p X (fun ω ↦ (Y ω, Z ω)) ≤ rvCondEntropy p X Z := by
  have h := rvCondEntropy_pair_le p X Y Z
  rw [rvCondEntropy_chain_rule] at h
  linarith

/-- Conditional mutual information, with the conditioning variable last. -/
noncomputable def rvCondMutualInfo (p : FinProb Ω) (X : Ω → α)
    (Y : Ω → β) (Z : Ω → γ) : ℝ :=
  rvCondEntropy p X Z - rvCondEntropy p X (fun ω ↦ (Y ω, Z ω))

theorem rvCondMutualInfo_nonneg (p : FinProb Ω) (X : Ω → α)
    (Y : Ω → β) (Z : Ω → γ) :
    0 ≤ rvCondMutualInfo p X Y Z :=
  sub_nonneg.mpr (rvCondEntropy_condition_pair_le p X Y Z)

theorem rvCondMutualInfo_eq_entropy (p : FinProb Ω) (X : Ω → α)
    (Y : Ω → β) (Z : Ω → γ) :
    rvCondMutualInfo p X Y Z =
      rvEntropy p (fun ω ↦ (X ω, Z ω)) + rvEntropy p (fun ω ↦ (Y ω, Z ω)) -
        rvEntropy p Z - rvEntropy p (fun ω ↦ ((X ω, Y ω), Z ω)) := by
  unfold rvCondMutualInfo
  simp only [rvCondEntropy_eq_sub]
  rw [rvEntropy_triple_assoc]
  ring

theorem rvCondEntropy_nonneg (p : FinProb Ω) (X : Ω → α) (Y : Ω → β) :
    0 ≤ rvCondEntropy p X Y :=
  condEntropy_nonneg (jointLaw p X Y)

theorem rvCondEntropy_le_entropy (p : FinProb Ω) (X : Ω → α) (Y : Ω → β) :
    rvCondEntropy p X Y ≤ rvEntropy p X := by
  have h := condEntropy_le_entropy_fst (jointLaw p X Y)
  simpa only [fstMarginal_jointLaw, rvCondEntropy, rvEntropy] using h

theorem rvCondEntropy_le_log_card [Nonempty α] (p : FinProb Ω)
    (X : Ω → α) (Y : Ω → β) :
    rvCondEntropy p X Y ≤ Real.log (Fintype.card α) :=
  (rvCondEntropy_le_entropy p X Y).trans (entropy_le_log_card (law p X))

/-- A sign block of length `n` has at most `n log 2` conditional entropy. -/
theorem rvCondEntropy_signBlock_le (p : FinProb Ω) (n : ℕ)
    (X : Ω → (Fin n → Bool)) (Y : Ω → β) :
    rvCondEntropy p X Y ≤ (n : ℝ) * Real.log 2 := by
  have h := rvCondEntropy_le_log_card p X Y
  simpa only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
    Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] using h

end Erdos67.FiniteEntropy
