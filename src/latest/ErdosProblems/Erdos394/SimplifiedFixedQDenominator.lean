import ErdosProblems.Erdos394.FixedQDenominator

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Simplified fixed-q denominator bound with Euler cancellation
-/

open Nat Finset

namespace Erdos394

/-- Exact cancellation between the totient density of a selected prime product
and the sieve density of its complement. -/
theorem totient_div_primeProduct_mul_complementEuler
    (P T : Finset ℕ) (hTP : T ⊆ P)
    (hprime : ∀ p ∈ P, p.Prime) :
    (((primeProduct T).totient : ℝ) / (primeProduct T : ℝ)) *
      localEulerProduct (P \ T) (fun p ↦ 1 / (p : ℝ)) =
        localEulerProduct P (fun p ↦ 1 / (p : ℝ)) := by
  have hTprime : ∀ p ∈ T, p.Prime := fun p hp ↦ hprime p (hTP hp)
  have hqpos : (0 : ℝ) < primeProduct T := by
    exact_mod_cast (show 0 < primeProduct T by
      unfold primeProduct
      exact Finset.prod_pos fun p hp ↦ (hTprime p hp).pos)
  rw [totient_primeProduct_real T hTprime]
  have hsplit := localEulerProduct_mul_sdiff P T hTP
    (fun p ↦ 1 / (p : ℝ))
  field_simp
  exact hsplit

/-- F-079 with its bad main term simplified by exact Euler cancellation and
its bad discrepancy term bounded using `φ(q)≤q`. -/
theorem fixedQ_shiftedGoodPrimeTMass_lower_simplified
    (P T : Finset ℕ) (K Y A U R C0 : ℕ)
    (hK : 0 < K) (hC0 : 0 < C0)
    (hTP : T ⊆ P) (hprime : ∀ p ∈ P, p.Prime)
    (hlarge : ∀ p ∈ T, K < p)
    (hPupper : ∀ p ∈ P, p ≤ A)
    (hheight : 2 * K ≤ Y * A)
    (hR : Even R)
    (htail :
      (∑ p ∈ P, (1 / (p : ℝ))) ^ (R + 1) /
          ((R + 1).factorial : ℝ) ≤
        localEulerProduct P (fun p ↦ 1 / (p : ℝ)))
    (hY : C0 * K ^ (T.card + 1) * Y ≤ primeProduct T)
    {L : ℝ} (htotal : L ≤ primeIntervalWeightedMass A U) :
    ((Y : ℝ) / 2) *
      (L - (((U : ℝ) ^ 2 /
          (C0 : ℝ)) * localEulerProduct P (fun p ↦ 1 / (p : ℝ)) +
        ((primeProduct T : ℝ) / (C0 : ℝ)) *
          ((truncatedSubsets (P \ T) R).card : ℝ) * (2 * (U : ℝ)))) ≤
      shiftedGoodPrimeTMass T K Y A U
        (fun p hp ↦ hprime p (hTP hp)) := by
  have hTprime : ∀ p ∈ T, p.Prime := fun p hp ↦ hprime p (hTP hp)
  have hcompPrime : ∀ p ∈ P \ T, p.Prime := by
    intro p hp
    exact hprime p (Finset.mem_sdiff.mp hp).1
  have hcopComp : ∀ p ∈ P \ T, (primeProduct T).Coprime p := by
    intro p hp
    exact primeProduct_coprime_of_not_mem hTP hprime
      (Finset.mem_sdiff.mp hp).1 (Finset.mem_sdiff.mp hp).2
  have htailComp := factorial_tail_le_localEulerProduct_sdiff
    P T hTP R htail hprime
  have hbase := fixedQ_shiftedGoodPrimeTMass_lower
    T (P \ T) K Y A U R hK hTprime hlarge
    (fun p hp ↦ hPupper p (hTP hp)) hcompPrime
    (fun p hp ↦ hPupper p (Finset.mem_sdiff.mp hp).1)
    hcopComp hheight hR htailComp htotal
  let q : ℕ := primeProduct T
  let kpow : ℕ := K ^ (T.card + 1)
  let Vc : ℝ := localEulerProduct (P \ T) (fun p ↦ 1 / (p : ℝ))
  let V : ℝ := localEulerProduct P (fun p ↦ 1 / (p : ℝ))
  let Nerr : ℝ := ((truncatedSubsets (P \ T) R).card : ℝ)
  have hqposNat : 0 < q := by
    dsimp [q, primeProduct]
    exact Finset.prod_pos fun p hp ↦ (hTprime p hp).pos
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hqposNat
  have hkpowpos : (0 : ℝ) < kpow := by
    dsimp [kpow]
    exact_mod_cast pow_pos hK _
  have hCpos : (0 : ℝ) < C0 := by exact_mod_cast hC0
  have hYcast : (C0 : ℝ) * (kpow : ℝ) * (Y : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast hY
  have hD : (kpow : ℝ) * (Y : ℝ) / (q : ℝ) ≤ 1 / (C0 : ℝ) := by
    have hkYle : (kpow : ℝ) * (Y : ℝ) ≤ (q : ℝ) / (C0 : ℝ) := by
      apply (le_div_iff₀ hCpos).2
      nlinarith
    calc
      (kpow : ℝ) * (Y : ℝ) / (q : ℝ) ≤
          ((q : ℝ) / (C0 : ℝ)) / (q : ℝ) :=
        div_le_div_of_nonneg_right hkYle hqpos.le
      _ = 1 / (C0 : ℝ) := by field_simp
  have hphi : ((q.totient : ℕ) : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast Nat.totient_le q
  have hphi0 : (0 : ℝ) ≤ q.totient := by positivity
  have hV0 : 0 ≤ V := by
    dsimp [V]
    apply localEulerProduct_nonneg P (fun p ↦ 1 / (p : ℝ))
    · intro p hp; positivity
    · intro p hp
      have hp0 : (0 : ℝ) < p := by exact_mod_cast (hprime p hp).pos
      exact (div_le_one hp0).2 (by exact_mod_cast (hprime p hp).one_le)
  have hVc0 : 0 ≤ Vc := by
    dsimp [Vc]
    apply localEulerProduct_nonneg (P \ T) (fun p ↦ 1 / (p : ℝ))
    · intro p hp; positivity
    · intro p hp
      have hpprime := hprime p (Finset.mem_sdiff.mp hp).1
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hpprime.pos
      exact (div_le_one hp0).2 (by exact_mod_cast hpprime.one_le)
  have hcancel : (((q.totient : ℕ) : ℝ) / (q : ℝ)) * Vc = V := by
    dsimp [q, Vc, V]
    exact totient_div_primeProduct_mul_complementEuler P T hTP hprime
  let D : ℝ := (kpow : ℝ) * (Y : ℝ) / (q : ℝ)
  let Xmain : ℝ := ((U : ℝ) ^ 2 / (q : ℝ)) * Vc +
    Nerr * (2 * (U : ℝ))
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  have hN0 : 0 ≤ Nerr := by dsimp [Nerr]; positivity
  have hmainEq : (D * (q.totient : ℝ)) *
      (((U : ℝ) ^ 2 / (q : ℝ)) * Vc) =
        D * (U : ℝ) ^ 2 * V := by
    calc
      (D * (q.totient : ℝ)) * (((U : ℝ) ^ 2 / (q : ℝ)) * Vc) =
          D * (U : ℝ) ^ 2 * (((q.totient : ℝ) / (q : ℝ)) * Vc) := by ring
      _ = D * (U : ℝ) ^ 2 * V := by rw [hcancel]
  have hmainLe : (D * (q.totient : ℝ)) *
      (((U : ℝ) ^ 2 / (q : ℝ)) * Vc) ≤
        ((U : ℝ) ^ 2 / (C0 : ℝ)) * V := by
    rw [hmainEq]
    have hscale : 0 ≤ (U : ℝ) ^ 2 * V := by positivity
    calc
      D * (U : ℝ) ^ 2 * V = D * ((U : ℝ) ^ 2 * V) := by ring
      _ ≤ (1 / (C0 : ℝ)) * ((U : ℝ) ^ 2 * V) :=
        mul_le_mul_of_nonneg_right (by simpa [D] using hD) hscale
      _ = ((U : ℝ) ^ 2 / (C0 : ℝ)) * V := by ring
  have herrLe : (D * (q.totient : ℝ)) *
      (Nerr * (2 * (U : ℝ))) ≤
        ((q : ℝ) / (C0 : ℝ)) * Nerr * (2 * (U : ℝ)) := by
    have hDphi : D * (q.totient : ℝ) ≤ (q : ℝ) / (C0 : ℝ) := by
      calc
        D * (q.totient : ℝ) ≤ (1 / (C0 : ℝ)) * (q.totient : ℝ) :=
          mul_le_mul_of_nonneg_right (by simpa [D] using hD) hphi0
        _ ≤ (1 / (C0 : ℝ)) * (q : ℝ) :=
          mul_le_mul_of_nonneg_left hphi (by positivity)
        _ = (q : ℝ) / (C0 : ℝ) := by ring
    have hU0 : 0 ≤ 2 * (U : ℝ) := by positivity
    calc
      (D * (q.totient : ℝ)) * (Nerr * (2 * (U : ℝ))) ≤
          ((q : ℝ) / (C0 : ℝ)) * (Nerr * (2 * (U : ℝ))) :=
        mul_le_mul_of_nonneg_right hDphi (mul_nonneg hN0 hU0)
      _ = ((q : ℝ) / (C0 : ℝ)) * Nerr * (2 * (U : ℝ)) := by ring
  have hE : (D * (q.totient : ℝ)) * Xmain ≤
      ((U : ℝ) ^ 2 / (C0 : ℝ)) * V +
        ((q : ℝ) / (C0 : ℝ)) * Nerr * (2 * (U : ℝ)) := by
    dsimp [Xmain]
    rw [mul_add]
    exact _root_.add_le_add hmainLe herrLe
  rw [← totient_primeProduct_eq_primeUnitCount T hTprime] at hbase
  dsimp [q, kpow, Vc, V, Nerr, D, Xmain] at hbase hE ⊢
  have hY0 : 0 ≤ (Y : ℝ) / 2 := by positivity
  apply (mul_le_mul_of_nonneg_left (sub_le_sub_left hE L) hY0).trans
  exact hbase

end Erdos394
