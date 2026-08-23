import Mathlib

open Filter
open scoped Asymptotics BigOperators

noncomputable section


namespace Erdos980

open scoped Classical in
def Eligible (k p : ℕ) : Prop := p.Prime ∧ p ≡ 1 [MOD k]

open scoped Classical in
def IsKthPowerNonresidue (k p a : ℕ) : Prop :=
  IsUnit (a : ZMod p) ∧ ¬ ∃ b : ZMod p, b ^ k = (a : ZMod p)

open scoped Classical in
theorem eligible_prime {k p : ℕ} (h : Eligible k p) : p.Prime := h.1

open scoped Classical in
theorem eligible_modEq {k p : ℕ} (h : Eligible k p) : p ≡ 1 [MOD k] := h.2

open scoped Classical in
theorem dvd_prime_sub_one_of_eligible {k p : ℕ} (h : Eligible k p) :
    k ∣ p - 1 := by
  exact h.2.symm.dvd'

open scoped Classical in
theorem exists_not_mem_powMonoidHom_range
    (G : Type*) [CommGroup G] [Finite G] [IsCyclic G]
    {k : ℕ} (hk : 2 ≤ k) (hdiv : k ∣ Nat.card G) :
    ∃ u : G, u ∉ (powMonoidHom k : G →* G).range := by
  have hgcd : (Nat.card G).gcd k = k := Nat.gcd_eq_right_iff_dvd.mpr hdiv
  have hindex : (powMonoidHom k : G →* G).range.index = k := by
    rw [IsCyclic.index_powMonoidHom_range, hgcd]
  have hne : (powMonoidHom k : G →* G).range ≠ ⊤ := by
    intro htop
    have hone : (powMonoidHom k : G →* G).range.index = 1 :=
      Subgroup.index_eq_one.mpr htop
    omega
  exact SetLike.exists_not_mem_of_ne_top _ hne

open scoped Classical in
theorem exists_kthPowerNonresidue_lt {k p : ℕ} (hk : 2 ≤ k)
    (hp : Eligible k p) :
    ∃ a : ℕ, a < p ∧ IsKthPowerNonresidue k p a := by
  letI : Fact p.Prime := ⟨hp.1⟩
  letI : IsCyclic (ZMod p)ˣ := ZMod.isCyclic_units_prime hp.1
  have hdiv : k ∣ Nat.card (ZMod p)ˣ := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units]
    exact dvd_prime_sub_one_of_eligible hp
  obtain ⟨u, hu⟩ := exists_not_mem_powMonoidHom_range (ZMod p)ˣ hk hdiv
  refine ⟨(u : ZMod p).val, ZMod.val_lt (u : ZMod p), ?_⟩
  have hcast : ((u : ZMod p).val : ZMod p) = (u : ZMod p) :=
    ZMod.natCast_zmod_val (u : ZMod p)
  refine ⟨?_, ?_⟩
  · rw [hcast]
    exact u.isUnit
  · rintro ⟨b, hb⟩
    have hbunit : IsUnit b := by
      rw [← isUnit_pow_iff (show k ≠ 0 by omega), hb, hcast]
      exact u.isUnit
    let v : (ZMod p)ˣ := hbunit.unit
    apply hu
    refine ⟨v, ?_⟩
    apply Units.ext
    simpa [v, IsUnit.unit_spec, hcast] using hb

open scoped Classical in
theorem exists_kthPowerNonresidue {k p : ℕ} (hk : 2 ≤ k)
    (hp : Eligible k p) : ∃ a : ℕ, IsKthPowerNonresidue k p a := by
  obtain ⟨a, _, ha⟩ := exists_kthPowerNonresidue_lt hk hp
  exact ⟨a, ha⟩

open scoped Classical in
noncomputable def leastKthPowerNonresidue (k p : ℕ) : ℕ :=
  if h : 2 ≤ k ∧ Eligible k p then
    Nat.find (exists_kthPowerNonresidue h.1 h.2)
  else 0

end Erdos980

namespace Erdos980

open scoped Classical in
theorem erdos_980 :
    True ↔ ∀ k : ℕ, 2 ≤ k → ∃ c : ℝ, 0 < c ∧
      ((fun x : ℕ ↦ ∑ p ∈ (Finset.range x).filter Nat.Prime,
          (leastKthPowerNonresidue k p : ℝ)) ~[atTop]
        (fun x : ℕ ↦ c * (x : ℝ) / Real.log (x : ℝ))) := by
  sorry

end Erdos980

end
