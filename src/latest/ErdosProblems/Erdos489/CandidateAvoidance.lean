import ErdosProblems.Erdos489.AffineCandidateDensity

/- Ported from Lean 4.31.0 to 4.33.0; imports and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos489

/-- Keep only those moduli coprime to the progression modulus `Q`. -/
def coprimePart (l : List ℕ) (Q : ℕ) : List ℕ :=
  l.filter fun a => decide (Nat.Coprime Q a)

/-- A number congruent to one modulo `Q` cannot be divisible by a modulus
having a nontrivial common factor with `Q`. -/
theorem not_dvd_of_modEq_one_of_not_coprime
    (Q a n : ℕ) (hmod : Nat.ModEq Q n 1) (hncop : ¬Nat.Coprime Q a) :
    ¬a ∣ n := by
  intro han
  obtain ⟨p, hp, hpQ, hpa⟩ := Nat.Prime.not_coprime_iff_dvd.mp hncop
  have hpn : p ∣ n := hpa.trans han
  have hp1 : p ∣ 1 := (hmod.dvd_iff hpQ).mp hpn
  exact hp.ne_one (Nat.dvd_one.mp hp1)

/-- Affine candidates avoiding the coprime part of a list automatically avoid
the whole list. -/
theorem affineCandidates_coprimePart_avoid_all
    (l : List ℕ) (Q n : ℕ)
    (hn : affineCandidates (coprimePart l Q) Q n) :
    ∀ a ∈ l, ¬a ∣ n := by
  intro a ha
  by_cases hcop : Nat.Coprime Q a
  · apply hn.2 a
    exact List.mem_filter.mpr ⟨ha, decide_eq_true hcop⟩
  · exact not_dvd_of_modEq_one_of_not_coprime Q a n hn.1 hcop

/-- Every element of the filtered list is coprime to `Q`. -/
theorem coprimePart_all_coprime (l : List ℕ) (Q : ℕ) :
    ∀ a ∈ coprimePart l Q, Nat.Coprime Q a := by
  intro a ha
  exact of_decide_eq_true (List.mem_filter.mp ha).2

/-- Consequently `Q` is coprime to the product of the filtered list. -/
theorem coprime_coprimePart_prod (l : List ℕ) (Q : ℕ) :
    Nat.Coprime Q (coprimePart l Q).prod := by
  induction l with
  | nil => simp [coprimePart]
  | cons a l ih =>
      change Nat.Coprime Q
        (List.filter (fun b => decide (Nat.Coprime Q b)) (a :: l)).prod
      change Nat.Coprime Q
        (List.filter (fun b => decide (Nat.Coprime Q b)) l).prod at ih
      rw [List.filter_cons]
      by_cases hcop : Nat.Coprime Q a
      · rw [if_pos (decide_eq_true hcop), List.prod_cons]
        exact hcop.mul_right ih
      · have hd : decide (Nat.Coprime Q a) ≠ true :=
          fun h => hcop (of_decide_eq_true h)
        rw [if_neg hd]
        exact ih

end Erdos489
