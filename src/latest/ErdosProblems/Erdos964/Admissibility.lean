import ErdosProblems.Erdos964.Basic

/-!
# The elementary local conditions for the GPY input

We choose the prescribed factors by the Chinese remainder theorem modulo
their squares. The square moduli make the quotients coprime to the factors
removed from the linear forms.
-/

namespace Erdos964

/-- A primitive affine form takes every residue class. -/
theorem exists_affine_modEq (a b c m : ℕ) (hm : 0 < m) (ham : a.Coprime m) :
    ∃ x : ℕ, a * x + b ≡ c [MOD m] := by
  let : NeZero m := ⟨ne_of_gt hm⟩
  let z : ZMod m := (a : ZMod m)⁻¹ * ((c : ZMod m) - b)
  refine ⟨z.val, ?_⟩
  rw [← ZMod.natCast_eq_natCast_iff]
  simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val]
  dsimp [z]
  rw [← mul_assoc, ZMod.coe_mul_inv_eq_one a ham, one_mul, sub_add_cancel]

/-- Simultaneous congruences specifying the removed factors exactly. -/
theorem exists_prescribed_factor_progression (a r : Fin 3 → ℕ)
    (hr : ∀ i, 0 < r i) (hra : ∀ i, (r i).Coprime (a i))
    (hrr : ∀ i j, i ≠ j → (r i).Coprime (r j)) :
    ∃ b : ℕ, ∀ i, L (a i) b ≡ r i [MOD r i ^ 2] := by
  have hroots : ∀ i, ∃ x : ℕ, a i * x + 1 ≡ r i [MOD r i ^ 2] := by
    intro i
    exact exists_affine_modEq (a i) 1 (r i) (r i ^ 2)
      (pow_pos (hr i) 2) ((hra i).symm.pow_right 2)
  choose t ht using hroots
  let b := Nat.chineseRemainderOfFinset t (fun i => r i ^ 2) Finset.univ
    (fun i _ => pow_ne_zero 2 (ne_of_gt (hr i)))
    (fun i _ j _ hij => (hrr i j hij).pow 2 2)
  refine ⟨b.val, fun i => ?_⟩
  exact ((b.property i (Finset.mem_univ i)).mul_left (a i)).add_right 1 |>.trans (ht i)

/-- The square-modulus congruence makes the quotient a unit modulo `r`. -/
theorem quotient_coprime_of_modEq (n r : ℕ) (hr : 0 < r)
    (h : n ≡ r [MOD r ^ 2]) : r ∣ n ∧ (n / r).Coprime r := by
  have hr2 : r ∣ r ^ 2 := dvd_pow_self r (by decide)
  have hd : r ∣ n := (h.dvd_iff hr2).mpr (dvd_refl r)
  refine ⟨hd, ?_⟩
  have hmul : r * (n / r) ≡ r * 1 [MOD r * r] := by
    simpa only [Nat.mul_div_cancel' hd, mul_one, pow_two] using h
  have hquot : n / r ≡ 1 [MOD r] :=
    Nat.ModEq.mul_left_cancel' (ne_of_gt hr) hmul
  change (n / r).gcd r = 1
  rw [hquot.gcd_eq, Nat.gcd_one_left]

/-- A common divisor of two forms also divides the difference of their slopes. -/
theorem dvd_slope_sub_of_dvd_forms (a b x p : ℕ)
    (ha : p ∣ L a x) (hb : p ∣ L b x) : p ∣ a - b := by
  have h₁ : p ∣ b * (a * x + 1) := dvd_mul_of_dvd_right ha b
  have h₂ : p ∣ a * (b * x + 1) := dvd_mul_of_dvd_right hb a
  have hcommon₁ : b * (a * x + 1) = a * b * x + b := by ring
  have hcommon₂ : a * (b * x + 1) = a * b * x + a := by ring
  rw [hcommon₁] at h₁
  rw [hcommon₂] at h₂
  simpa only [Nat.add_sub_add_left] using Nat.dvd_sub h₂ h₁

/-- No prime dividing one prescribed factor divides any of the reduced forms. -/
theorem prime_not_dvd_reduced_form (a r : Fin 3 → ℕ) (b : ℕ)
    (hr : ∀ i, 0 < r i)
    (hdiff : ∀ i j, i ≠ j → (r i).Coprime
      (if a i > a j then a i - a j else a j - a i))
    (hb : ∀ i, L (a i) b ≡ r i [MOD r i ^ 2])
    (p : ℕ) (hp : p.Prime) (j : Fin 3) (hpj : p ∣ r j) (i : Fin 3) :
    ¬p ∣ L (a i) b / r i := by
  have hdiv i := (quotient_coprime_of_modEq _ _ (hr i) (hb i)).1
  intro hi
  by_cases hij : i = j
  · subst i
    have hc := (quotient_coprime_of_modEq _ _ (hr j) (hb j)).2
    exact hp.ne_one (Nat.eq_one_of_dvd_coprimes hc hi hpj)
  · have hLi : p ∣ L (a i) b := hi.trans (Nat.div_dvd_of_dvd (hdiv i))
    have hLj : p ∣ L (a j) b := hpj.trans (hdiv j)
    have hD : p ∣ if a j > a i then a j - a i else a i - a j := by
      split
      · exact dvd_slope_sub_of_dvd_forms _ _ _ _ hLj hLi
      · exact dvd_slope_sub_of_dvd_forms _ _ _ _ hLi hLj
    exact hp.ne_one (Nat.eq_one_of_dvd_coprimes (hdiff j i (Ne.symm hij)) hpj hD)

/-- The product of square moduli used for the common progression. -/
def progressionModulus (r : Fin 3 → ℕ) : ℕ := ∏ i, r i ^ 2

theorem progressionModulus_pos (r : Fin 3 → ℕ) (hr : ∀ i, 0 < r i) :
    0 < progressionModulus r :=
  Finset.prod_pos (fun i _ => pow_pos (hr i) 2)

theorem sq_dvd_progressionModulus (r : Fin 3 → ℕ) (i : Fin 3) :
    r i ^ 2 ∣ progressionModulus r :=
  Finset.dvd_prod_of_mem _ (Finset.mem_univ i)

theorem dvd_progressionModulus (r : Fin 3 → ℕ) (i : Fin 3) :
    r i ∣ progressionModulus r :=
  (dvd_pow_self (r i) (by decide : 2 ≠ 0)).trans (sq_dvd_progressionModulus r i)

/-- Local admissibility of the three quotient forms after removing prescribed factors. -/
theorem reduced_forms_admissible (a r : Fin 3 → ℕ) (b : ℕ)
    (hr : ∀ i, 0 < r i)
    (hdiff : ∀ i j, i ≠ j → (r i).Coprime
      (if a i > a j then a i - a j else a j - a i))
    (hb : ∀ i, L (a i) b ≡ r i [MOD r i ^ 2]) :
    ∀ p : ℕ, p.Prime → ∃ t : ℕ, ∀ i,
      ¬p ∣ a i * (progressionModulus r / r i) * t + L (a i) b / r i := by
  intro p hp
  by_cases hpM : p ∣ progressionModulus r
  · have hp_prod : p ∣ ∏ i, r i ^ 2 := hpM
    obtain ⟨j, _, hpj⟩ := (hp.prime.dvd_finsetProd_iff _).mp hp_prod
    have hpj' := hp.dvd_of_dvd_pow hpj
    refine ⟨0, fun i => ?_⟩
    simpa only [mul_zero, zero_add] using
      prime_not_dvd_reduced_form a r b hr hdiff hb p hp j hpj' i
  · obtain ⟨t, ht⟩ := exists_affine_modEq (progressionModulus r) b 0 p hp.pos
      (hp.coprime_iff_not_dvd.mpr hpM).symm
    refine ⟨t, fun i hi => ?_⟩
    have hdiv := (quotient_coprime_of_modEq _ _ (hr i) (hb i)).1
    have hprod : r i * (a i * (progressionModulus r / r i) * t +
        L (a i) b / r i) = a i * (progressionModulus r * t + b) + 1 := by
      rw [mul_add, Nat.mul_div_cancel' hdiv]
      have hM := Nat.mul_div_cancel' (dvd_progressionModulus r i)
      calc
        _ = a i * (r i * (progressionModulus r / r i)) * t + (a i * b + 1) := by
          dsimp [L]
          ring
        _ = _ := by rw [hM]; ring
    have hpd : p ∣ a i * (progressionModulus r * t + b) + 1 :=
      hprod ▸ dvd_mul_of_dvd_right hi (r i)
    have hzero : p ∣ progressionModulus r * t + b := Nat.modEq_zero_iff_dvd.mp ht
    exact hp.not_dvd_one ((Nat.dvd_add_iff_right (dvd_mul_of_dvd_right hzero (a i))).mpr hpd)

end Erdos964
