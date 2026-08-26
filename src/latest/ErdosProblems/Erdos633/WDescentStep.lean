import ErdosProblems.Erdos633.WDescent

/-!
# The strict descent step for doubled-leg Pythagorean pairs

The four-factor decomposition uses gcds and divisibility, without assuming
that an arbitrary factorization has a prescribed arrangement.
-/

namespace Erdos633

theorem coprime_product_rectangle (u v x f : ℕ) (hu : 0 < u) (hv : 0 < v) (hx : 0 < x)
    (huv : u.Coprime v) (hprod : u * v = x * f) :
    ∃ α β γ δ : ℕ, 0 < α ∧ 0 < β ∧ 0 < γ ∧ 0 < δ ∧
      u = α * β ∧ v = γ * δ ∧ x = α * γ ∧ f = β * δ ∧
      α.Coprime δ ∧ β.Coprime γ := by
  obtain ⟨β, γ, hβγ, huβ, hxγ⟩ := Nat.exists_coprime u x
  let α := Nat.gcd u x
  have hα : 0 < α := Nat.gcd_pos_of_pos_left x hu
  have hβ : 0 < β := by
    by_contra h
    have hz : β = 0 := by omega
    simp only [hz, zero_mul] at huβ
    omega
  have hγ : 0 < γ := by
    by_contra h
    have hz : γ = 0 := by omega
    simp only [hz, zero_mul] at hxγ
    omega
  have hcross : β * v = γ * f := by
    apply mul_right_cancel₀ (ne_of_gt hα)
    calc
      β * v * α = u * v := by rw [huβ]; ring
      _ = x * f := hprod
      _ = γ * f * α := by rw [hxγ]; ring
  have hγv : γ ∣ v := hβγ.symm.dvd_of_dvd_mul_left ⟨f, hcross⟩
  obtain ⟨δ, hvδ⟩ := hγv
  have hδ : 0 < δ := by
    by_contra h
    have hz : δ = 0 := by omega
    simp only [hz, mul_zero] at hvδ
    omega
  have hfδ : f = β * δ := by
    apply mul_left_cancel₀ (ne_of_gt hγ)
    calc
      γ * f = β * v := hcross.symm
      _ = γ * (β * δ) := by rw [hvδ]; ring
  have huα : u = α * β := by rw [huβ]; ring
  have hxα : x = α * γ := by rw [hxγ]; ring
  have hαδ : α.Coprime δ := by
    exact Nat.Coprime.of_dvd_right (show δ ∣ v from ⟨γ, by rw [hvδ]; ring⟩)
      (Nat.Coprime.of_dvd_left (show α ∣ u from ⟨β, huα⟩) huv)
  exact ⟨α, β, γ, δ, hα, hβ, hγ, hδ, huα, hvδ, hxα, hfδ, hαδ, hβγ⟩

theorem primitive_doubled_leg_descent (a b c d : ℕ) (hb : 0 < b)
    (hab : a.Coprime b) (haodd : a % 2 = 1)
    (h₁ : a ^ 2 + b ^ 2 = c ^ 2) (h₂ : a ^ 2 + (2 * b) ^ 2 = d ^ 2) :
    ∃ α δ β γ : ℕ, 0 < δ ∧ δ < b ∧ α.Coprime δ ∧ α % 2 = 1 ∧
      α ^ 2 + δ ^ 2 = β ^ 2 ∧ α ^ 2 + (2 * δ) ^ 2 = γ ^ 2 := by
  have hc : 0 < c := by nlinarith only [h₁, hb]
  have hd : 0 < d := by nlinarith only [h₂, hb]
  obtain ⟨u, v, x, y, hu, hv, hx, hy, huv, _, huodd, _, hyeven, hbuv, hbxy, hsums⟩ :=
    doubled_leg_parameters a b c d hb hc hd hab haodd h₁ h₂
  have hy2 : 2 ∣ y := Nat.dvd_of_mod_eq_zero hyeven
  obtain ⟨f, hyf⟩ := hy2
  have hprod : u * v = x * f := by
    rw [hyf] at hbxy
    nlinarith only [hbuv, hbxy]
  obtain ⟨α, β, γ, δ, hα, hβ, hγ, hδ, huα, hvδ, hxα, hfδ, hαδ, hβγ⟩ :=
    coprime_product_rectangle u v x f hu hv hx huv hprod
  have hαodd : α % 2 = 1 := by
    by_contra h
    have hzero : α % 2 = 0 := by omega
    rw [huα, Nat.mul_mod, hzero, zero_mul] at huodd
    norm_num at huodd
  have hbalance : β ^ 2 * (α ^ 2 + 4 * δ ^ 2) = γ ^ 2 * (α ^ 2 + δ ^ 2) := by
    rw [huα, hvδ, hxα, hyf, hfδ] at hsums
    nlinarith only [hsums]
  have hAB := coprime_sq_add_four_sq α δ hαδ
  have hAβ : α ^ 2 + δ ^ 2 ∣ β ^ 2 := by
    apply hAB.dvd_of_dvd_mul_right
    exact ⟨γ ^ 2, by nlinarith only [hbalance]⟩
  have hβA : β ^ 2 ∣ α ^ 2 + δ ^ 2 := by
    apply (hβγ.pow 2 2).dvd_of_dvd_mul_left
    exact ⟨α ^ 2 + 4 * δ ^ 2, by nlinarith only [hbalance]⟩
  have hA : α ^ 2 + δ ^ 2 = β ^ 2 := Nat.dvd_antisymm hAβ hβA
  have hB : α ^ 2 + 4 * δ ^ 2 = γ ^ 2 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 (ne_of_gt hβ))
    rw [hbalance, hA]
    ring
  have hδv : δ ≤ v := Nat.le_of_dvd hv ⟨γ, by rw [hvδ]; ring⟩
  have hvb : v < b := by nlinarith only [hbuv, hu, hv]
  refine ⟨α, δ, β, γ, hδ, lt_of_le_of_lt hδv hvb, hαδ, hαodd, hA, ?_⟩
  nlinarith only [hB]

/-- The doubled-leg pair is impossible when the common odd leg is primitive. -/
theorem no_primitive_doubled_leg (a b c d : ℕ) (hb : 0 < b)
    (hab : a.Coprime b) (haodd : a % 2 = 1)
    (h₁ : a ^ 2 + b ^ 2 = c ^ 2) (h₂ : a ^ 2 + (2 * b) ^ 2 = d ^ 2) : False := by
  induction b using Nat.strong_induction_on generalizing a c d with
  | h b ih =>
    obtain ⟨α, δ, β, γ, hδ, hlt, hαδ, hodd, hA, hB⟩ :=
      primitive_doubled_leg_descent a b c d hb hab haodd h₁ h₂
    exact ih δ hlt α β γ hδ hαδ hodd hA hB

end Erdos633
