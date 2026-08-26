import ErdosProblems.Erdos67b.RareEventEntropy

/-!
# Conditional entropy subadditivity for the entropy decrement

We first prove the homogeneous finite-mass inequality.  Applying it on
each conditioning fibre avoids introducing arbitrary conditional laws at
zero-probability events.
-/

open scoped BigOperators
open Finset

namespace Erdos67b.FiniteEntropy

/-- Multiplying the entropy of normalized nonnegative weights by their
total mass removes the normalization exactly. -/
theorem mass_mul_sum_negMulLog_div
    {α : Type*} [Fintype α] (w : α → ℝ) (hw : ∀ a, 0 ≤ w a)
    {r : ℝ} (hr : 0 < r) (hsum : ∑ a, w a = r) :
    r * (∑ a, Real.negMulLog (w a / r)) =
      (∑ a, Real.negMulLog (w a)) - Real.negMulLog r := by
  rw [Finset.mul_sum]
  simp_rw [mul_negMulLog_div (hw _) hr]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, hsum]
  simp [Real.negMulLog]

/-- Shannon subadditivity for a finite nonnegative matrix of arbitrary
total mass, including total mass zero. -/
theorem homogeneous_entropy_subadditivity
    {α β : Type*} [Fintype α] [Fintype β]
    (w : α → β → ℝ) (hw : ∀ a b, 0 ≤ w a b) :
    (∑ a, ∑ b, Real.negMulLog (w a b)) +
        Real.negMulLog (∑ a, ∑ b, w a b) ≤
      (∑ a, Real.negMulLog (∑ b, w a b)) +
        ∑ b, Real.negMulLog (∑ a, w a b) := by
  classical
  let r := ∑ a, ∑ b, w a b
  have hr : 0 ≤ r := Finset.sum_nonneg fun a _ ↦
    Finset.sum_nonneg fun b _ ↦ hw a b
  by_cases hr0 : r = 0
  · have hzero (a : α) (b : β) : w a b = 0 := by
      have hrow : w a b ≤ ∑ b, w a b :=
        Finset.single_le_sum (fun b _ ↦ hw a b) (Finset.mem_univ b)
      have htotal : (∑ b, w a b) ≤ r :=
        Finset.single_le_sum (fun a _ ↦ Finset.sum_nonneg fun b _ ↦ hw a b)
          (Finset.mem_univ a)
      exact le_antisymm (hr0 ▸ hrow.trans htotal) (hw a b)
    simp [hzero]
  · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
    let p : FinProb (α × β) := ⟨fun z ↦ w z.1 z.2 / r, by
      constructor
      · intro z
        exact div_nonneg (hw z.1 z.2) hr
      · rw [← Finset.sum_div, Fintype.sum_prod_type]
        exact div_self hr0⟩
    have hfst (a : α) : fstMarginal p a = (∑ b, w a b) / r := by
      rw [fstMarginal_apply, Finset.sum_div]
      rfl
    have hsnd (b : β) : sndMarginal p b = (∑ a, w a b) / r := by
      rw [sndMarginal_apply, Finset.sum_div]
      rfl
    have hp : r * entropy p =
        (∑ a, ∑ b, Real.negMulLog (w a b)) - Real.negMulLog r := by
      have h := mass_mul_sum_negMulLog_div (fun z : α × β ↦ w z.1 z.2)
        (fun z ↦ hw z.1 z.2) hrpos (by rw [Fintype.sum_prod_type])
      change r * (∑ z : α × β, Real.negMulLog (w z.1 z.2 / r)) = _
      simpa only [Fintype.sum_prod_type] using h
    have hA : r * entropy (fstMarginal p) =
        (∑ a, Real.negMulLog (∑ b, w a b)) - Real.negMulLog r := by
      unfold entropy
      simp_rw [hfst]
      exact mass_mul_sum_negMulLog_div (fun a ↦ ∑ b, w a b)
        (fun a ↦ Finset.sum_nonneg fun b _ ↦ hw a b) hrpos rfl
    have hB : r * entropy (sndMarginal p) =
        (∑ b, Real.negMulLog (∑ a, w a b)) - Real.negMulLog r := by
      unfold entropy
      simp_rw [hsnd]
      exact mass_mul_sum_negMulLog_div (fun b ↦ ∑ a, w a b)
        (fun b ↦ Finset.sum_nonneg fun a _ ↦ hw a b) hrpos Finset.sum_comm
    have h := mul_le_mul_of_nonneg_left (entropy_le_add_marginals p) hr
    rw [mul_add, hp, hA, hB] at h
    change _ + Real.negMulLog r ≤ _
    linarith

@[simp]
theorem law_comp
    {Ω α β : Type*} [Fintype Ω] [Fintype α] [Fintype β]
    (p : FinProb Ω) (X : Ω → α) (g : α → β) :
    law (law p X) g = law p (g ∘ X) := by
  exact stdSimplex.map_comp_apply X g p

theorem law_first_last_apply
    {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (p : FinProb ((α × β) × γ)) (a : α) (c : γ) :
    law p (fun z ↦ (z.1.1, z.2)) (a, c) = ∑ b, p ((a, b), c) := by
  classical
  simp only [law, stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply,
    Finset.sum_filter, Fintype.sum_prod_type, Prod.mk.injEq]
  simp only [ite_and]
  rw [Finset.sum_eq_single a]
  · simp
  · intro x _ hx
    simp [hx]
  · simp

theorem law_second_last_apply
    {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (p : FinProb ((α × β) × γ)) (b : β) (c : γ) :
    law p (fun z ↦ (z.1.2, z.2)) (b, c) = ∑ a, p ((a, b), c) := by
  classical
  simp only [law, stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply,
    Finset.sum_filter, Fintype.sum_prod_type, Prod.mk.injEq]
  simp only [ite_and]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_eq_single b]
  · simp
  · intro y _ hy
    simp [hy]
  · simp

/-- Strong subadditivity obtained by summing the homogeneous inequality
over the last-coordinate fibres. -/
theorem entropy_strong_subadditivity
    {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (p : FinProb ((α × β) × γ)) :
    entropy p + entropy (sndMarginal p) ≤
      entropy (law p (fun z ↦ (z.1.1, z.2))) +
        entropy (law p (fun z ↦ (z.1.2, z.2))) := by
  have h := Finset.sum_le_sum (fun c (_ : c ∈ Finset.univ) ↦
    homogeneous_entropy_subadditivity (fun a b ↦ p ((a, b), c))
      (fun a b ↦ prob_nonneg p ((a, b), c)))
  simp only [Finset.sum_add_distrib] at h
  have hleft : (∑ c, ∑ a, ∑ b, Real.negMulLog (p ((a, b), c))) = entropy p := by
    simp only [entropy, Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    exact Finset.sum_comm
  have hlast : (∑ c, Real.negMulLog (∑ a, ∑ b, p ((a, b), c))) =
      entropy (sndMarginal p) := by
    simp only [entropy, sndMarginal_apply, Fintype.sum_prod_type]
  have hfirst : (∑ c, ∑ a, Real.negMulLog (∑ b, p ((a, b), c))) =
      entropy (law p (fun z ↦ (z.1.1, z.2))) := by
    simp only [entropy, Fintype.sum_prod_type, law_first_last_apply]
    exact Finset.sum_comm
  have hsecond : (∑ c, ∑ b, Real.negMulLog (∑ a, p ((a, b), c))) =
      entropy (law p (fun z ↦ (z.1.2, z.2))) := by
    simp only [entropy, Fintype.sum_prod_type, law_second_last_apply]
    exact Finset.sum_comm
  rwa [hleft, hlast, hfirst, hsecond] at h

@[simp]
theorem rvCondEntropy_eq_sub
    {Ω α β : Type*} [Fintype Ω] [Fintype α] [Fintype β]
    (p : FinProb Ω) (X : Ω → α) (Y : Ω → β) :
    rvCondEntropy p X Y = rvEntropy p (fun ω ↦ (X ω, Y ω)) - rvEntropy p Y := by
  change entropy (jointLaw p X Y) - entropy (sndMarginal (jointLaw p X Y)) = _
  rw [sndMarginal_jointLaw]
  rfl

/-- Conditional entropy is subadditive for two finite random variables,
without assumptions on independence or on individual conditioning events. -/
theorem rvCondEntropy_pair_le
    {Ω α β γ : Type*} [Fintype Ω] [Fintype α] [Fintype β] [Fintype γ]
    (p : FinProb Ω) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) :
    rvCondEntropy p (fun ω ↦ (X ω, Y ω)) Z ≤
      rvCondEntropy p X Z + rvCondEntropy p Y Z := by
  have h := entropy_strong_subadditivity (jointLaw p (fun ω ↦ (X ω, Y ω)) Z)
  rw [sndMarginal_jointLaw] at h
  simp only [jointLaw, law_comp, Function.comp_def] at h
  simp only [rvCondEntropy_eq_sub, rvEntropy]
  linarith

/-- Applying a deterministic function to the variable being conditioned
cannot increase its conditional entropy. -/
theorem rvCondEntropy_comp_le
    {Ω α β γ : Type*} [Fintype Ω] [Fintype α] [Fintype β] [Fintype γ]
    (p : FinProb Ω) (X : Ω → α) (Z : Ω → γ) (g : α → β) :
    rvCondEntropy p (g ∘ X) Z ≤ rvCondEntropy p X Z := by
  simp only [rvCondEntropy_eq_sub]
  apply sub_le_sub_right
  exact rvEntropy_comp_le p (fun ω ↦ (X ω, Z ω)) (fun z ↦ (g z.1, z.2))

/-- A finite tuple has conditional entropy at most the sum of its
coordinate conditional entropies. -/
theorem rvCondEntropy_fin_le_sum
    {Ω α γ : Type*} [Fintype Ω] [Fintype α] [Fintype γ]
    (p : FinProb Ω) (Z : Ω → γ) (n : ℕ) (X : Ω → Fin n → α) :
    rvCondEntropy p X Z ≤ ∑ i, rvCondEntropy p (fun ω ↦ X ω i) Z := by
  induction n with
  | zero =>
    simp only [Fin.sum_univ_zero, rvCondEntropy_eq_sub]
    apply sub_nonpos.mpr
    have h := rvEntropy_comp_le p Z
      (fun z ↦ ((fun i : Fin 0 ↦ Fin.elim0 i : Fin 0 → α), z))
    convert h using 1
    congr 1
    funext ω
    congr 1
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    let Xhead : Ω → α := fun ω ↦ X ω 0
    let Xtail : Ω → Fin n → α := fun ω i ↦ X ω i.succ
    have hrecover := rvCondEntropy_comp_le p (fun ω ↦ (Xhead ω, Xtail ω)) Z
      (fun z ↦ Fin.cons (α := fun _ : Fin (n + 1) ↦ α) z.1 z.2)
    have heq : (fun z ↦ Fin.cons (α := fun _ : Fin (n + 1) ↦ α) z.1 z.2) ∘
        (fun ω ↦ (Xhead ω, Xtail ω)) = X := by
      funext ω i
      refine Fin.cases ?_ (fun j ↦ ?_) i <;> rfl
    rw [heq] at hrecover
    have hpair := rvCondEntropy_pair_le p Xhead Xtail Z
    have htail := ih Xtail
    rw [Fin.sum_univ_succ]
    exact hrecover.trans (hpair.trans (add_le_add (le_refl _) htail))

/-- Conditional entropy equals entropy minus mutual information. -/
theorem rvCondEntropy_eq_entropy_sub_mutualInfo
    {Ω α γ : Type*} [Fintype Ω] [Fintype α] [Fintype γ]
    (p : FinProb Ω) (X : Ω → α) (Y : Ω → γ) :
    rvCondEntropy p X Y = rvEntropy p X - rvMutualInfo p X Y := by
  have h := mutualInfo_eq_entropy_fst_sub_condEntropy (jointLaw p X Y)
  rw [fstMarginal_jointLaw] at h
  change rvMutualInfo p X Y = rvEntropy p X - rvCondEntropy p X Y at h
  linarith

/-- Entropy of a deterministic encoding of finitely many blocks, with
the entropy cost of the common conditioning variable counted only once. -/
theorem rvEntropy_of_block_encoding_le
    {Ω α γ δ : Type*} [Fintype Ω] [Fintype α] [Fintype γ] [Fintype δ]
    (p : FinProb Ω) (Y : Ω → γ) (k : ℕ) (X : Ω → Fin k → α)
    (decode : (Fin k → α) → δ) :
    rvEntropy p (decode ∘ X) ≤
      rvEntropy p Y + ∑ i, rvCondEntropy p (fun ω ↦ X ω i) Y := by
  have hmap := rvEntropy_comp_le p (fun ω ↦ (X ω, Y ω)) (fun z ↦ decode z.1)
  change rvEntropy p (decode ∘ X) ≤ rvEntropy p (fun ω ↦ (X ω, Y ω)) at hmap
  rw [rvEntropy_chain_rule] at hmap
  exact hmap.trans (add_le_add (le_refl _) (rvCondEntropy_fin_le_sum p Y k X))

/-- The exact one-step block entropy decrement, before division by block
length. Approximate stationarity is expressed solely by the checked
conditional-entropy error of each block. -/
theorem rvEntropy_block_decrement
    {Ω α γ δ : Type*} [Fintype Ω] [Fintype α] [Fintype γ] [Fintype δ]
    (p : FinProb Ω) (Y : Ω → γ) (k : ℕ) (X : Ω → Fin k → α)
    (Xref : Ω → α) (decode : (Fin k → α) → δ) (e : ℝ)
    (hshift : ∀ i, rvCondEntropy p (fun ω ↦ X ω i) Y ≤
      rvCondEntropy p Xref Y + e) :
    rvEntropy p (decode ∘ X) ≤ rvEntropy p Y +
      k * (rvEntropy p Xref - rvMutualInfo p Xref Y + e) := by
  have h := rvEntropy_of_block_encoding_le p Y k X decode
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) ↦ hshift i)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    rvCondEntropy_eq_entropy_sub_mutualInfo] at hsum
  exact h.trans (add_le_add (le_refl _) hsum)

/-- Normalized entropy-rate recurrence. All scale parameters are finite
and positive, and the residue entropy is paid with the factor `1 / k`. -/
theorem rvEntropy_rate_decrement
    {Ω α γ δ : Type*} [Fintype Ω] [Fintype α] [Fintype γ] [Fintype δ]
    (p : FinProb Ω) (Y : Ω → γ) {k : ℕ} (hk : 0 < k)
    (X : Ω → Fin k → α) (Xref : Ω → α) (decode : (Fin k → α) → δ)
    {H : ℝ} (hH : 0 < H) (C e : ℝ)
    (hY : rvEntropy p Y ≤ C * H)
    (hshift : ∀ i, rvCondEntropy p (fun ω ↦ X ω i) Y ≤
      rvCondEntropy p Xref Y + e) :
    rvEntropy p (decode ∘ X) / (k * H) ≤
      rvEntropy p Xref / H - rvMutualInfo p Xref Y / H + C / k + e / H := by
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  apply (div_le_iff₀ (mul_pos hkR hH)).mpr
  have h := rvEntropy_block_decrement p Y k X Xref decode e hshift
  have hcalc :
      (rvEntropy p Xref / H - rvMutualInfo p Xref Y / H + C / k + e / H) *
        (k * H) = C * H + k * (rvEntropy p Xref - rvMutualInfo p Xref Y + e) := by
    field_simp
    ring
  rw [hcalc]
  exact h.trans (add_le_add hY (le_refl _))

end Erdos67b.FiniteEntropy
