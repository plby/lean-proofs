/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ErdosProblems.Erdos999.PairGeometry

/-!
# Determinant encoding for pairs of rational centres

This file isolates the elementary arithmetic behind the pair count in the
Duffin--Schaeffer overlap argument.  A pair of residue representatives
`a mod q`, `b mod r` is encoded by its raw cross-difference
`a * r - b * q`.  For each fixed cross-difference there are at most
`gcd q r` pairs.  Retaining the raw cross-difference, rather than selecting a
circular representative, avoids an extra wrap parameter: closeness on the
circle merely places it in three short intervals around `-q*r`, `0`, and
`q*r`.
-/

open Set

namespace Erdos999

/-- The unreduced integral cross-difference of two residue representatives. -/
def pairDet (q r : ℕ) (z : Fin q × Fin r) : ℤ :=
  (z.1 : ℤ) * r - (z.2 : ℤ) * q

/-- The determinant together with the quotient of the first numerator by
`q / gcd q r`.  The quotient parametrizes the pairs in a determinant fiber. -/
def pairDetCode (q r : ℕ) (z : Fin q × Fin r) : ℤ × ℕ :=
  (pairDet q r z, (z.1 : ℕ) / (q / q.gcd r))

theorem pairDetCode_injective {q r : ℕ} (hq : 0 < q) :
    Function.Injective (pairDetCode q r) := by
  intro z z' hcode
  have hdet : pairDet q r z = pairDet q r z' := congrArg Prod.fst hcode
  have hdiv : (z.1 : ℕ) / (q / q.gcd r) =
      (z'.1 : ℕ) / (q / q.gcd r) := congrArg Prod.snd hcode
  have hmodMul : (z.1 : ℕ) * r ≡ (z'.1 : ℕ) * r [MOD q] := by
    rw [Nat.modEq_iff_dvd]
    refine ⟨(z'.2 : ℤ) - (z.2 : ℤ), ?_⟩
    dsimp [pairDet] at hdet
    push_cast
    linear_combination -hdet
  have hmod : (z.1 : ℕ) ≡ (z'.1 : ℕ) [MOD q / q.gcd r] :=
    hmodMul.cancel_right_div_gcd hq
  have haNat : (z.1 : ℕ) = (z'.1 : ℕ) := Nat.ext_div_modEq hdiv hmod
  have ha : z.1 = z'.1 := Fin.ext haNat
  have hbNat : (z.2 : ℕ) = (z'.2 : ℕ) := by
    have hdet' := hdet
    dsimp [pairDet] at hdet'
    rw [ha] at hdet'
    have hbmul : (z.2 : ℤ) * q = (z'.2 : ℤ) * q := sub_right_inj.mp hdet'
    have hqz : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
    exact_mod_cast (mul_right_cancel₀ hqz hbmul)
  have hb : z.2 = z'.2 := Fin.ext hbNat
  exact Prod.ext ha hb

theorem pairDetCode_second_lt_gcd {q r : ℕ} (hq : 0 < q)
    (z : Fin q × Fin r) :
    (pairDetCode q r z).2 < q.gcd r := by
  have hg : 0 < q.gcd r := Nat.gcd_pos_of_pos_left r hq
  have hgle : q.gcd r ≤ q := Nat.le_of_dvd hq (Nat.gcd_dvd_left q r)
  have hqdiv : 0 < q / q.gcd r := Nat.div_pos hgle hg
  rw [pairDetCode, Nat.div_lt_iff_lt_mul hqdiv]
  rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left q r)]
  exact z.1.isLt

/-- The finite parameter within an exact determinant fiber. -/
def pairDetFiberCode {q r : ℕ} (hq : 0 < q)
    (z : Fin q × Fin r) : Fin (q.gcd r) :=
  ⟨(pairDetCode q r z).2, pairDetCode_second_lt_gcd hq z⟩

/-- The raw determinant and the fiber parameter jointly determine the pair. -/
theorem pairDet_fiberCode_injective {q r : ℕ} (hq : 0 < q) :
    Function.Injective (fun z : Fin q × Fin r =>
      (pairDet q r z, pairDetFiberCode hq z)) := by
  intro z z' h
  apply pairDetCode_injective hq
  apply Prod.ext
  · change pairDet q r z = pairDet q r z'
    exact congrArg Prod.fst h
  · exact congrArg Fin.val (congrArg Prod.snd h)

/-- Every exact determinant fiber contains at most `gcd q r` pairs. -/
theorem card_pairDet_fiber_le_gcd {q r : ℕ} (hq : 0 < q) (c : ℤ) :
    ((Finset.univ : Finset (Fin q × Fin r)).filter
      (fun z => pairDet q r z = c)).card ≤ q.gcd r := by
  classical
  let s := (Finset.univ : Finset (Fin q × Fin r)).filter
    (fun z => pairDet q r z = c)
  have hmaps : Set.MapsTo (pairDetFiberCode hq) (s : Set (Fin q × Fin r))
      (Finset.univ : Finset (Fin (q.gcd r))) := by
    intro z hz
    simp
  have hinj : Set.InjOn (pairDetFiberCode hq) (s : Set (Fin q × Fin r)) := by
    intro z hz z' hz' hcode
    apply pairDet_fiberCode_injective hq
    apply Prod.ext
    · change pairDet q r z = pairDet q r z'
      simpa [s] using (Finset.mem_filter.mp hz).2.trans
        (Finset.mem_filter.mp hz').2.symm
    · exact hcode
  have hcard := Finset.card_le_card_of_injOn (pairDetFiberCode hq) hmaps hinj
  simpa [s] using hcard

/-- The raw determinant always lies strictly between `-q*r` and `q*r`. -/
theorem pairDet_mem_raw_interval {q r : ℕ} (hq : 0 < q) (hr : 0 < r)
    (z : Fin q × Fin r) :
    -(q * r : ℕ) < pairDet q r z ∧ pairDet q r z < (q * r : ℕ) := by
  have ha : (z.1 : ℤ) < q := by exact_mod_cast z.1.isLt
  have hb : (z.2 : ℤ) < r := by exact_mod_cast z.2.isLt
  have haq : (0 : ℤ) ≤ z.1 := by positivity
  have hbq : (0 : ℤ) ≤ z.2 := by positivity
  have hqz : (0 : ℤ) < q := by exact_mod_cast hq
  have hrz : (0 : ℤ) < r := by exact_mod_cast hr
  dsimp [pairDet]
  constructor
  · have hbr : (z.2 : ℤ) * q < (r : ℤ) * q :=
      mul_lt_mul_of_pos_right hb hqz
    nlinarith
  · have har : (z.1 : ℤ) * r < (q : ℤ) * r :=
      mul_lt_mul_of_pos_right ha hrz
    nlinarith

/-- `gcd q r` divides every raw determinant. -/
theorem gcd_dvd_pairDet (q r : ℕ) (z : Fin q × Fin r) :
    (q.gcd r : ℤ) ∣ pairDet q r z := by
  dsimp [pairDet]
  apply dvd_sub
  · exact (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right q r)).mul_left _
  · exact (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left q r)).mul_left _

/-- After division by `gcd q r`, the determinant has the expected expression
in terms of the coprime denominator quotients. -/
theorem pairDet_ediv_gcd {q r : ℕ} (hq : 0 < q) (z : Fin q × Fin r) :
    pairDet q r z / (q.gcd r : ℤ) =
      (z.1 : ℤ) * ((r / q.gcd r : ℕ) : ℤ) -
        (z.2 : ℤ) * ((q / q.gcd r : ℕ) : ℤ) := by
  have hg : 0 < q.gcd r := Nat.gcd_pos_of_pos_left r hq
  have hgnz : (q.gcd r : ℤ) ≠ 0 := by exact_mod_cast hg.ne'
  apply Int.ediv_eq_of_eq_mul_left hgnz
  dsimp [pairDet]
  have hqfac := Nat.mul_div_cancel' (Nat.gcd_dvd_left q r)
  have hrfac := Nat.mul_div_cancel' (Nat.gcd_dvd_right q r)
  have hqfacZ : (q.gcd r : ℤ) * (q / q.gcd r : ℕ) = q := by
    exact_mod_cast hqfac
  have hrfacZ : (q.gcd r : ℤ) * (r / q.gcd r : ℕ) = r := by
    exact_mod_cast hrfac
  calc
    (z.1 : ℤ) * r - (z.2 : ℤ) * q =
        (z.1 : ℤ) * ((q.gcd r : ℤ) * (r / q.gcd r : ℕ)) -
          (z.2 : ℤ) * ((q.gcd r : ℤ) * (q / q.gcd r : ℕ)) :=
      congrArg₂ (fun R Q : ℤ => (z.1 : ℤ) * R - (z.2 : ℤ) * Q)
        hrfacZ.symm hqfacZ.symm
    _ = ((z.1 : ℤ) * ((r / q.gcd r : ℕ) : ℤ) -
          (z.2 : ℤ) * ((q / q.gcd r : ℕ) : ℤ)) * (q.gcd r : ℤ) := by
      ring

/-- For reduced residue representatives, the normalized determinant is
coprime to the product of the coprime denominator quotients.  This is the
arithmetic restriction used when the determinant intervals are sieved. -/
theorem normalized_pairDet_coprime {q r : ℕ} (hq : 0 < q)
    {z : Fin q × Fin r} (hqa : q.Coprime (z.1 : ℕ))
    (hrb : r.Coprime (z.2 : ℕ)) :
    (pairDet q r z / (q.gcd r : ℤ)).natAbs.Coprime
      ((q / q.gcd r) * (r / q.gcd r)) := by
  have hg : 0 < q.gcd r := Nat.gcd_pos_of_pos_left r hq
  have hQR : (q / q.gcd r).Coprime (r / q.gcd r) :=
    Nat.coprime_div_gcd_div_gcd hg
  apply Nat.coprime_of_dvd
  intro p hp hpc hpQR
  have hpcZ : (p : ℤ) ∣ pairDet q r z / (q.gcd r : ℤ) :=
    Int.natCast_dvd.mpr hpc
  rw [pairDet_ediv_gcd hq z] at hpcZ
  rcases (hp.dvd_mul.mp hpQR) with hpQ | hpR
  · have hpQZ : (p : ℤ) ∣ ((q / q.gcd r : ℕ) : ℤ) :=
      Int.natCast_dvd_natCast.mpr hpQ
    have hpbQZ : (p : ℤ) ∣
        (z.2 : ℤ) * ((q / q.gcd r : ℕ) : ℤ) := hpQZ.mul_left _
    have hpaRZ : (p : ℤ) ∣
        (z.1 : ℤ) * ((r / q.gcd r : ℕ) : ℤ) := by
      simpa only [sub_add_cancel] using dvd_add hpcZ hpbQZ
    have hpaR : p ∣ (z.1 : ℕ) * (r / q.gcd r) := by
      exact_mod_cast hpaRZ
    rcases hp.dvd_mul.mp hpaR with hpa | hpR'
    · have hpq : p ∣ q := hpQ.trans (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left q r))
      exact hp.ne_one (Nat.eq_one_of_dvd_coprimes hqa hpq hpa)
    · exact hp.ne_one (Nat.eq_one_of_dvd_coprimes hQR hpQ hpR')
  · have hpRZ : (p : ℤ) ∣ ((r / q.gcd r : ℕ) : ℤ) :=
      Int.natCast_dvd_natCast.mpr hpR
    have hpaRZ : (p : ℤ) ∣
        (z.1 : ℤ) * ((r / q.gcd r : ℕ) : ℤ) := hpRZ.mul_left _
    have hpbQZ : (p : ℤ) ∣
        (z.2 : ℤ) * ((q / q.gcd r : ℕ) : ℤ) := by
      have hd := dvd_sub hpaRZ hpcZ
      have hid :
          (z.1 : ℤ) * ((r / q.gcd r : ℕ) : ℤ) -
              ((z.1 : ℤ) * ((r / q.gcd r : ℕ) : ℤ) -
                (z.2 : ℤ) * ((q / q.gcd r : ℕ) : ℤ)) =
            (z.2 : ℤ) * ((q / q.gcd r : ℕ) : ℤ) := by ring
      rwa [hid] at hd
    have hpbQ : p ∣ (z.2 : ℕ) * (q / q.gcd r) := by
      exact_mod_cast hpbQZ
    rcases hp.dvd_mul.mp hpbQ with hpb | hpQ'
    · have hpr : p ∣ r := hpR.trans (Nat.div_dvd_of_dvd (Nat.gcd_dvd_right q r))
      exact hp.ne_one (Nat.eq_one_of_dvd_coprimes hrb hpr hpb)
    · exact hp.ne_one (Nat.eq_one_of_dvd_coprimes hQR hpQ' hpR)

/-- If the sum of the physical radii is at most one, a nearby pair's raw
determinant lies in one of the three short intervals around `-qr`, `0`, and
`qr`, each of radius `r*L + q*M`. -/
theorem nearby_pairDet_mem_three_intervals {q r : ℕ} {L M : ℝ}
    (hq : 0 < q) (hr : 0 < r)
    (hsmall : L / q + M / r ≤ 1)
    {z : Fin q × Fin r} (hz : isNearbyReducedPair q r L M z) :
    |(pairDet q r z : ℝ)| < r * L + q * M ∨
      |(pairDet q r z : ℝ) - q * r| < r * L + q * M ∨
      |(pairDet q r z : ℝ) + q * r| < r * L + q * M := by
  rcases hz.2.2 with ⟨k, hk⟩
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have ha0 : (0 : ℝ) ≤ (z.1 : ℝ) / q := div_nonneg (by positivity) hqR.le
  have hb0 : (0 : ℝ) ≤ (z.2 : ℝ) / r := div_nonneg (by positivity) hrR.le
  have ha1 : (z.1 : ℝ) / q < 1 := by
    rw [div_lt_one hqR]
    exact_mod_cast z.1.isLt
  have hb1 : (z.2 : ℝ) / r < 1 := by
    rw [div_lt_one hrR]
    exact_mod_cast z.2.isLt
  have hxlo : -1 < (z.1 : ℝ) / q - (z.2 : ℝ) / r := by linarith
  have hxhi : (z.1 : ℝ) / q - (z.2 : ℝ) / r < 1 := by linarith
  have hkparts := abs_lt.mp hk
  have hkloR : (-2 : ℝ) < k := by linarith
  have hkhiR : (k : ℝ) < 2 := by linarith
  have hklo : (-2 : ℤ) < k := by exact_mod_cast hkloR
  have hkhi : k < (2 : ℤ) := by exact_mod_cast hkhiR
  have hk_cases : k = -1 ∨ k = 0 ∨ k = 1 := by omega
  have hscale :
      |(pairDet q r z : ℝ) - (k : ℝ) * (q * r)| < r * L + q * M := by
    have halg :
        (pairDet q r z : ℝ) - (k : ℝ) * (q * r) =
          ((q : ℝ) * r) *
            ((z.1 : ℝ) / q - (z.2 : ℝ) / r - k) := by
      dsimp [pairDet]
      push_cast
      field_simp
    rw [halg, abs_mul, abs_of_pos (mul_pos hqR hrR)]
    calc
      (q : ℝ) * r *
          |(z.1 : ℝ) / q - (z.2 : ℝ) / r - k| <
          (q : ℝ) * r * (L / q + M / r) :=
        mul_lt_mul_of_pos_left hk (mul_pos hqR hrR)
      _ = r * L + q * M := by field_simp
  rcases hk_cases with rfl | rfl | rfl
  · right; right
    convert hscale using 1 <;> push_cast <;> ring
  · left
    simpa using hscale
  · right; left
    convert hscale using 1 <;> push_cast <;> ring

end Erdos999
