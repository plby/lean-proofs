import Util.Bernays.GoodNormArithmetic

/-!
# Local coefficients of the good ideal counting series
-/

namespace Bernays

theorem discriminantCharacter_eq_zero_of_not_coprime {D : ℤ} (hD : D ≠ 0)
    {n : ℕ} (hn : ¬ n.Coprime (discriminantLevel D)) : discriminantCharacter D hD n = 0 :=
  MulChar.map_nonunit _ ((ZMod.isUnit_iff_coprime n _).not.mpr hn)

theorem exists_splitPrime_of_coprime_not_inert {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    {p : ℕ} (hp : p.Prime) (hc : p.Coprime (discriminantLevel (b ^ 2 + 4 * d)))
    (hχ : discriminantCharacter (b ^ 2 + 4 * d) hD.ne p ≠ -1) :
    ∃ s : SplitPrime d b, s.1 = p := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨r, hr⟩ := (discriminantCharacter_root_iff hD.ne hc).mpr hχ
  have hpd : ¬ (p : ℤ) ∣ b ^ 2 + 4 * d := by
    intro h
    have hdvd : p ∣ discriminantLevel (b ^ 2 + 4 * d) :=
      (show p ∣ (b ^ 2 + 4 * d).natAbs by simpa using Int.natAbs_dvd_natAbs.mpr h).trans (dvd_mul_left _ _)
    exact (hp.coprime_iff_not_dvd.mp hc) hdvd
  exact ⟨⟨p, hp, hpd, r, hr⟩, rfl⟩

theorem goodIdealNormAF_split_primePower {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (s : SplitPrime d b) (hc : s.1.Coprime (discriminantLevel (b ^ 2 + 4 * d))) (e : ℕ) :
    goodIdealNormAF hD (s.1 ^ e) = (e + 1 : ℕ) := by
  letI := quadraticOrderIsDomain hD
  change (Nat.card (GoodIdealNormFiber (quadraticBadIdeal d b) (s.1 ^ e)) : ℂ) = _
  rw [s.normPower_card hD hc e]

theorem goodIdealNormAF_inert_primePower {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    {p : ℕ} (hp : p.Prime) (hc : p.Coprime (discriminantLevel (b ^ 2 + 4 * d)))
    (hχ : discriminantCharacter (b ^ 2 + 4 * d) hD.ne p = -1) (e : ℕ) :
    goodIdealNormAF hD (p ^ e) = if Even e then 1 else 0 := by
  classical
  letI := quadraticOrderIsDomain hD
  change (Nat.card (GoodIdealNormFiber (quadraticBadIdeal d b) (p ^ e)) : ℂ) = _
  rw [inert_normPower_card hD hp hc hχ e]
  split_ifs <;> simp

theorem goodIdealNormAF_bad_primePower {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    {p : ℕ} (hc : ¬ p.Coprime (discriminantLevel (b ^ 2 + 4 * d)))
    {e : ℕ} (he : 0 < e) : goodIdealNormAF hD (p ^ e) = 0 := by
  letI := quadraticOrderIsDomain hD
  change (Nat.card (GoodIdealNormFiber (quadraticBadIdeal d b) (p ^ e)) : ℂ) = 0
  rw [goodIdealNormFiber_card_eq_zero_of_not_coprime hD (p ^ e)
    ((Nat.coprime_pow_left_iff he _ _).not.mpr hc), Nat.cast_zero]

end Bernays
