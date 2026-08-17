/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos215.SelectorFinal

namespace Erdos215.Selector.Final

open Erdos215.Selector
open Erdos215.Selector.Modular

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

private lemma integer_line_factorization
    (d A B K M L R m : ℤ)
    (hline : B = L * A - m * d)
    (hroot : d * R = 1 + L ^ 2) :
    A ^ 2 + B ^ 2 + 2 * d * (A * K + B * M) =
      d * (A * (R * A + 2 * (K + L * M - L * m)) +
        d * (m ^ 2 - 2 * m * M)) := by
  rw [hline]
  linear_combination -A ^ 2 * hroot

private lemma surviving_times_difference_dvd
    (d : ℕ) (A : ℤ) :
    (d : ℤ) ∣ A * (survivingModulus d A.natAbs : ℤ) := by
  let g := Nat.gcd d A.natAbs
  let q := d / g
  have hg : g ∣ d := Nat.gcd_dvd_left _ _
  have hga : g ∣ A.natAbs := Nat.gcd_dvd_right _ _
  have hqg : q * g = d := Nat.div_mul_cancel hg
  rcases hga with ⟨a, ha⟩
  have hqa : q * A.natAbs = d * a := by
    calc
      q * A.natAbs = q * (g * a) := by rw [ha]
      _ = (q * g) * a := by ring
      _ = d * a := by rw [hqg]
  change (d : ℤ) ∣ A * (q : ℤ)
  refine ⟨Int.sign A * (a : ℤ), ?_⟩
  have hqa' : (q : ℤ) * (A.natAbs : ℤ) = (d : ℤ) * a := by
    exact_mod_cast hqa
  have hsign : Int.sign A * (A.natAbs : ℤ) = A := Int.sign_mul_natAbs A
  calc
    A * (q : ℤ) = (Int.sign A * (A.natAbs : ℤ)) * q := by rw [hsign]
    _ = Int.sign A * ((q : ℤ) * A.natAbs) := by ring
    _ = Int.sign A * ((d : ℤ) * a) := by rw [hqa']
    _ = (d : ℤ) * (Int.sign A * a) := by ring

private lemma square_dvd_of_line_divisibility
    (d q A B K M L R P C m : ℤ)
    (hqd : q ∣ d)
    (hAq : d ∣ A * q)
    (hC : q ∣ C)
    (hout : d ∣ C - (K + L * M - L * m + P * A))
    (hphase : d ∣ 2 * P - R)
    (hline : B = L * A - m * d)
    (hroot : d * R = 1 + L ^ 2) :
    d ^ 2 ∣ A ^ 2 + B ^ 2 + 2 * d * (A * K + B * M) := by
  let X := K + L * M - L * m
  let Y := R * A + 2 * X
  have hX : q ∣ X + P * A := by
    have hsub : q ∣ C - (X + P * A) := dvd_trans hqd hout
    have hx' := dvd_sub hC hsub
    simpa only [sub_sub_cancel] using hx'
  have hPA : q ∣ A * (2 * P - R) := dvd_mul_of_dvd_right (dvd_trans hqd hphase) A
  have hY : q ∣ Y := by
    have htwo : q ∣ 2 * (X + P * A) := dvd_mul_of_dvd_right hX 2
    have : Y = 2 * (X + P * A) - A * (2 * P - R) := by
      dsimp [Y, X]
      ring
    rw [this]
    exact dvd_sub htwo hPA
  have hAY : d ∣ A * Y := by
    rcases hAq with ⟨z, hz⟩
    rcases hY with ⟨y, hy⟩
    refine ⟨z * y, ?_⟩
    rw [hy, ← mul_assoc, hz]
    ring
  rw [integer_line_factorization d A B K M L R m hline hroot]
  rcases hAY with ⟨z, hz⟩
  refine ⟨z + (m ^ 2 - 2 * m * M), ?_⟩
  dsimp [Y, X] at hz
  rw [hz]
  ring

/-- Formula (4.4a): a separated selector induces good line maps at every
root of `-1` when two is invertible modulo the denominator. -/
theorem inducedFamily_good {d : ℕ} (hd : d ≠ 0) (hodd : Nat.Coprime 2 d)
    (s : LiftData d) (hs : s.Separated) :
    FamilyGood (inducedFamily hd s) := by
  let _ : NeZero d := ⟨hd⟩
  intro lam jtilde i₁ i₂ hi hbad
  let j₁ := lineResidue hd lam jtilde i₁
  let j₂ := lineResidue hd lam jtilde i₂
  let A : ℤ := (i₁ : ℕ) - (i₂ : ℕ)
  let B : ℤ := (j₁ : ℕ) - (j₂ : ℕ)
  let K : ℤ := s.k i₁ j₁ - s.k i₂ j₂
  let M : ℤ := s.l i₁ j₁ - s.l i₂ j₂
  let L : ℤ := rootVal hd lam
  let R : ℤ := rootQuotient lam
  let P : ℤ := (rootPhase lam).val
  let C : ℤ :=
    ((inducedFamily hd s lam jtilde i₁ : Fin d) : ℕ) -
      ((inducedFamily hd s lam jtilde i₂ : Fin d) : ℕ)
  let m : ℤ := lineCarry hd lam jtilde i₁ - lineCarry hd lam jtilde i₂
  let q : ℕ := survivingModulus d (indexDiff i₁ i₂)
  have hqdNat : q ∣ d := survivingModulus_dvd _ _
  have hqd : (q : ℤ) ∣ d := by exact_mod_cast hqdNat
  have hAabs : A.natAbs = indexDiff i₁ i₂ := by rfl
  have hAq : (d : ℤ) ∣ A * (q : ℤ) := by
    simpa [q, hAabs] using surviving_times_difference_dvd d A
  have hC : (q : ℤ) ∣ C := by
    exact hbad
  have hline : B = L * A - m * d := by
    have h₁ := lineResidue_int_equation hd lam jtilde i₁
    have h₂ := lineResidue_int_equation hd lam jtilde i₂
    dsimp [A, B, L, m, j₁, j₂]
    linear_combination h₁ - h₂
  have hroot : (d : ℤ) * R = 1 + L ^ 2 := by
    dsimp [R, L]
    exact_mod_cast mul_rootQuotient hd lam
  have hPcast : ((P : ℤ) : ZMod d) = rootPhase lam := by
    simpa [P] using (ZMod.natCast_zmod_val (rootPhase lam))
  have hphase : (d : ℤ) ∣ 2 * P - R := by
    apply (ZMod.intCast_eq_intCast_iff_dvd_sub R (2 * P) d).mp
    push_cast
    rw [hPcast]
    simpa [R] using (two_mul_rootPhase hodd lam).symm
  have hvalue : ((C : ℤ) : ZMod d) =
      ((K + L * M - L * m + P * A : ℤ) : ZMod d) := by
    dsimp [C, K, L, M, m, A]
    push_cast
    rw [inducedFamily_formula hd s lam jtilde i₁,
      inducedFamily_formula hd s lam jtilde i₂]
    simp only [lineValue]
    rw [hPcast, rootVal_cast hd lam]
    ring
  have hout : (d : ℤ) ∣ C - (K + L * M - L * m + P * A) := by
    have hout' := (ZMod.intCast_eq_intCast_iff_dvd_sub C
      (K + L * M - L * m + P * A) d).mp hvalue
    simpa only [neg_sub] using dvd_neg.mpr hout'
  have hconf : (d : ℤ) ^ 2 ∣
      conflictNumerator d i₁ j₁ i₂ j₂
        (s.k i₁ j₁) (s.l i₁ j₁) (s.k i₂ j₂) (s.l i₂ j₂) := by
    apply square_dvd_of_line_divisibility (d : ℤ) q A B K M L R P C m
      hqd hAq hC hout hphase hline hroot
  apply hs i₁ j₁ i₂ j₂
  · intro hp
    exact hi (congrArg Prod.fst hp)
  · simpa [conflictNumerator, A, B, K, M] using hconf

end
end Erdos215.Selector.Final
