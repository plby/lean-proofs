import ErdosProblems.Erdos1141.BurgessEnergyArithmetic

/-!
# Ratio energy with arbitrary coprime natural denominators

The incidence box is kept in the natural numbers. In particular, the argument
does not require every small integer to be coprime to the modulus.
-/

namespace Pollack17.Burgess

open scoped BigOperators

def naturalRatioWeight (q M H : ℕ) (D : Finset ℕ) (x : ZMod q) : ℕ :=
  ((Finset.range H ×ˢ D).filter fun iu =>
    (iu.2 : ZMod q)⁻¹ * (M + iu.1 : ℕ) = x).card

noncomputable def naturalRatioEnergy (q M H : ℕ) [NeZero q] (D : Finset ℕ) : ℝ :=
  ∑ x : ZMod q, (naturalRatioWeight q M H D x : ℝ) ^ 2

theorem sum_naturalRatioWeight (q M H : ℕ) [NeZero q] (D : Finset ℕ) :
    ∑ x : ZMod q, naturalRatioWeight q M H D x = H * D.card := by
  have h := Finset.card_eq_sum_card_fiberwise
    (s := Finset.range H ×ˢ D) (t := Finset.univ)
    (f := fun iu : ℕ × ℕ => (iu.2 : ZMod q)⁻¹ * (M + iu.1 : ℕ)) (by simp)
  simpa only [Finset.card_product, Finset.card_range, naturalRatioWeight] using h.symm

theorem sum_naturalRatioWeight_mul (q M H : ℕ) [NeZero q]
    (D : Finset ℕ) (f : ZMod q → ℝ) :
    (∑ x : ZMod q, (naturalRatioWeight q M H D x : ℝ) * f x) =
      ∑ i ∈ Finset.range H, ∑ u ∈ D, f ((u : ZMod q)⁻¹ * (M + i : ℕ)) := by
  calc
    _ = ∑ iu ∈ Finset.range H ×ˢ D,
        f ((iu.2 : ZMod q)⁻¹ * (M + iu.1 : ℕ)) := by
      rw [← Finset.sum_fiberwise' (Finset.range H ×ˢ D)
        (fun iu : ℕ × ℕ => (iu.2 : ZMod q)⁻¹ * (M + iu.1 : ℕ)) f]
      apply Finset.sum_congr rfl
      intro x _
      simp [naturalRatioWeight, nsmul_eq_mul]
    _ = _ := Finset.sum_product _ _ _

theorem sum_card_fiber_sq_eq_card_collision
    {α β : Type*} [Fintype β] [DecidableEq α] [DecidableEq β]
    (s : Finset α) (f : α → β) :
    (∑ y : β, ((s.filter fun a => f a = y).card) ^ 2) =
      (((s ×ˢ s).filter fun ab => f ab.1 = f ab.2).card) := by
  let c := (s ×ˢ s).filter fun ab => f ab.1 = f ab.2
  have hmap : (c : Set (α × α)).MapsTo (fun ab => f ab.1)
      (Finset.univ : Finset β) := by
    intro ab _
    exact Finset.mem_univ _
  change (∑ y : β, ((s.filter fun a => f a = y).card) ^ 2) = c.card
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  apply Finset.sum_congr rfl
  intro y _
  rw [pow_two, ← Finset.card_product]
  congr 1
  ext ab
  simp only [c, Finset.mem_product, Finset.mem_filter]
  aesop

theorem natural_inv_ratio_eq_iff {q n₁ n₂ u₁ u₂ : ℕ}
    (h₁ : u₁.Coprime q) (h₂ : u₂.Coprime q) :
    (u₁ : ZMod q)⁻¹ * n₁ = (u₂ : ZMod q)⁻¹ * n₂ ↔
      n₁ * u₂ ≡ n₂ * u₁ [MOD q] := by
  rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_mul, Nat.cast_mul]
  have hmul₁ := ZMod.coe_mul_inv_eq_one u₁ h₁
  have hmul₂ := ZMod.coe_mul_inv_eq_one u₂ h₂
  constructor
  · intro h
    calc
      (n₁ : ZMod q) * u₂ = ((u₁ : ZMod q) * (u₁ : ZMod q)⁻¹) * (n₁ * u₂) := by
        rw [hmul₁, one_mul]
      _ = ((u₁ : ZMod q) * u₂) * ((u₁ : ZMod q)⁻¹ * n₁) := by ring
      _ = ((u₁ : ZMod q) * u₂) * ((u₂ : ZMod q)⁻¹ * n₂) := by rw [h]
      _ = ((u₂ : ZMod q) * (u₂ : ZMod q)⁻¹) * (n₂ * u₁) := by ring
      _ = _ := by rw [hmul₂, one_mul]
  · intro h
    calc
      (u₁ : ZMod q)⁻¹ * n₁ = ((u₂ : ZMod q) * (u₂ : ZMod q)⁻¹) *
          ((u₁ : ZMod q)⁻¹ * n₁) := by rw [hmul₂, one_mul]
      _ = ((u₁ : ZMod q)⁻¹ * (u₂ : ZMod q)⁻¹) * (n₁ * u₂) := by ring
      _ = ((u₁ : ZMod q)⁻¹ * (u₂ : ZMod q)⁻¹) * (n₂ * u₁) := by rw [h]
      _ = ((u₁ : ZMod q) * (u₁ : ZMod q)⁻¹) * ((u₂ : ZMod q)⁻¹ * n₂) := by ring
      _ = _ := by rw [hmul₁, one_mul]

theorem naturalRatioEnergy_eq_sum (q M H : ℕ) [NeZero q] (D : Finset ℕ)
    (hD : ∀ u ∈ D, u.Coprime q) :
    naturalRatioEnergy q M H D =
      ((∑ u ∈ D, ∑ v ∈ D, (burgessIntervalCollision q M H u v).card : ℕ) : ℝ) := by
  let box := Finset.range H ×ˢ D
  have h := sum_card_fiber_sq_eq_card_collision box
    (fun iu : ℕ × ℕ => (iu.2 : ZMod q)⁻¹ * (M + iu.1 : ℕ))
  have heq : ((box ×ˢ box).filter fun ab =>
      (ab.1.2 : ZMod q)⁻¹ * (M + ab.1.1 : ℕ) =
        (ab.2.2 : ZMod q)⁻¹ * (M + ab.2.1 : ℕ)) =
      ((box ×ˢ box).filter fun ab =>
        (M + ab.1.1) * ab.2.2 ≡ (M + ab.2.1) * ab.1.2 [MOD q]) := by
    apply Finset.filter_congr
    intro ab hab
    have hmem := Finset.mem_product.mp hab
    exact natural_inv_ratio_eq_iff
      (hD ab.1.2 (Finset.mem_product.mp hmem.1).2)
      (hD ab.2.2 (Finset.mem_product.mp hmem.2).2)
  rw [heq] at h
  have hcard : (((box ×ˢ box).filter fun ab =>
      (M + ab.1.1) * ab.2.2 ≡ (M + ab.2.1) * ab.1.2 [MOD q]).card) =
      ∑ u ∈ D, ∑ v ∈ D, (burgessIntervalCollision q M H u v).card := by
    simp only [box, burgessIntervalCollision, Finset.card_eq_sum_ones,
      Finset.sum_filter, Finset.sum_product]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _
    calc
      _ = ∑ i ∈ Finset.range H, ∑ v ∈ D, ∑ j ∈ Finset.range H,
          if (M + i) * v ≡ (M + j) * u [MOD q] then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
      _ = _ := Finset.sum_comm
  rw [hcard] at h
  have hcast := congrArg (fun n : ℕ => (n : ℝ)) h
  simpa only [naturalRatioEnergy, naturalRatioWeight, box, Nat.cast_sum,
    Nat.cast_pow] using hcast

theorem naturalRatioEnergy_le {q M H U : ℕ} [NeZero q] (D : Finset ℕ)
    (hD : D ⊆ Finset.Icc 1 U) (hcop : ∀ u ∈ D, u.Coprime q)
    (hH : 0 < H) (hU : 0 < U) (hsmall : 2 * (U * H) < q) :
    naturalRatioEnergy q M H D ≤
      ((H : ℝ) * (1 + Real.log U) + U) * ((U : ℝ) * (1 + Real.log U)) := by
  rw [naturalRatioEnergy_eq_sum q M H D hcop]
  have hfirst : (∑ u ∈ D, ∑ v ∈ D, (burgessIntervalCollision q M H u v).card) ≤
      ∑ u ∈ D, ∑ v ∈ D, (H / (u / u.gcd v) + 1) := by
    apply Finset.sum_le_sum
    intro u hu
    apply Finset.sum_le_sum
    intro v hv
    exact burgessIntervalCollision_card_le_of_coprime hH hU
      (hD hu) (hD hv) (hcop u hu).symm hsmall
  have hsecond : (∑ u ∈ D, ∑ v ∈ D, (H / (u / u.gcd v) + 1)) ≤
      ∑ u ∈ Finset.Icc 1 U, ∑ v ∈ Finset.Icc 1 U, (H / (u / u.gcd v) + 1) := by
    exact (Finset.sum_le_sum fun u _ => Finset.sum_le_sum_of_subset hD).trans
      (Finset.sum_le_sum_of_subset hD)
  calc
    _ ≤ ((∑ u ∈ Finset.Icc 1 U, ∑ v ∈ Finset.Icc 1 U,
        (H / (u / u.gcd v) + 1) : ℕ) : ℝ) := by exact_mod_cast hfirst.trans hsecond
    _ ≤ (burgessDivisorOvercount H U : ℝ) := reduced_denominator_sum_cast_le H U
    _ ≤ _ := burgessDivisorOvercount_cast_le H U hU

end Pollack17.Burgess
