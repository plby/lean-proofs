/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos378.ReciprocalChebyshevAsymptotic

/-!
# Reciprocal cancellation on the square-root prime window

This specializes the finite Vaughan estimate to the interval
`(sqrt k, 2 sqrt k]`, with reciprocal frequency `k`.
-/

open Filter
open scoped Topology

namespace Erdos378
namespace ReciprocalPrimeWindow

open PrimeReciprocal
open VaughanReciprocalFull
open ReciprocalChebyshevAsymptotic

noncomputable section

theorem norm_weightedChebyshev_sqrt_window_le {k : ℕ}
    (hk : 4 * 16384 ^ 2 ≤ Nat.sqrt k)
    (hsize : 16 * reciprocalDifferencingLength (2 * Nat.sqrt k) *
      ((reciprocalVaughanCutoff (2 * Nat.sqrt k)) ^ 2) ^ 2 ≤ Nat.sqrt k) :
    ‖weightedChebyshevInterval (reciprocalWeight (k : ℝ))
        (Nat.sqrt k) (2 * Nat.sqrt k)‖ ≤
      reciprocalChebyshevMajorant (2 * Nat.sqrt k)
        (reciprocalVaughanCutoff (2 * Nat.sqrt k))
        (reciprocalDifferencingLength (2 * Nat.sqrt k)) := by
  let s := Nat.sqrt k
  let y := 2 * s
  let T := reciprocalVaughanCutoff y
  let L := reciprocalDifferencingLength y
  have hs : 1 ≤ s := by omega
  have hkpos : 0 < k := by
    exact lt_of_lt_of_le Nat.zero_lt_one
      (hs.trans (by simpa only [s] using Nat.sqrt_le_self k))
  have hT : 0 < T := reciprocalVaughanCutoff_pos y
  have hL : 2 ≤ L := by
    unfold L reciprocalDifferencingLength
    have hypos : (0 : ℝ) < y := by positivity
    have hfloor : 1 ≤ Nat.floor (Real.sqrt (y : ℝ)) := by
      apply Nat.le_floor
      rw [Real.le_sqrt (by norm_num) (by positivity)]
      exact_mod_cast (show 1 ≤ y by omega)
    omega
  have hTx : T ≤ s := by
    have hsize' : 16 * L * T ^ 4 ≤ s := by
      change 16 * L * (T ^ 2) ^ 2 ≤ s at hsize
      convert hsize using 1 <;> ring
    calc
      T ≤ T ^ 4 := le_self_pow₀ (by omega) (by norm_num)
      _ = 1 * T ^ 4 := by simp
      _ ≤ (16 * L) * T ^ 4 :=
        Nat.mul_le_mul_right (T ^ 4) (by omega : 1 ≤ 16 * L)
      _ = 16 * L * T ^ 4 := by ring
      _ ≤ s := hsize'
  have hTy : T ≤ y := hTx.trans (by omega)
  have hXlo : ((y : ℝ) ^ 2) ≤ 4 * (k : ℝ) := by
    have hsSq : s ^ 2 ≤ k := by simpa [pow_two] using Nat.sqrt_le k
    have hnat : (2 * s) ^ 2 ≤ 4 * k := by nlinarith
    exact_mod_cast hnat
  have hklt : k < (s + 1) ^ 2 := by
    simpa only [s, pow_two] using Nat.lt_succ_sqrt k
  have hXhi : (k : ℝ) ≤ (y : ℝ) ^ 2 := by
    have hsone : (s + 1) ^ 2 ≤ (2 * s) ^ 2 := by nlinarith
    exact_mod_cast hklt.le.trans hsone
  apply norm_weightedChebyshevInterval_reciprocal_le
    (X := (k : ℝ)) (x := s) (y := y) (T := T) (L := L)
  · exact_mod_cast hkpos
  · exact hT
  · exact hTy
  · exact hTx
  · exact hL
  · simpa only [s, y, T, L] using hsize
  · simpa only [s] using hk
  · exact hXlo
  · exact hXhi
  · dsimp only [y]
    omega

lemma tendsto_two_mul_sqrt :
    Tendsto (fun k : ℕ ↦ 2 * Nat.sqrt k) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  refine ⟨b ^ 2, fun a ha ↦ ?_⟩
  have hb : b ≤ Nat.sqrt a := Nat.le_sqrt'.mpr ha
  omega

theorem tendsto_reciprocal_sqrt_window_majorant :
    Tendsto (fun k : ℕ ↦
      reciprocalChebyshevMajorant (2 * Nat.sqrt k)
        (reciprocalVaughanCutoff (2 * Nat.sqrt k))
        (reciprocalDifferencingLength (2 * Nat.sqrt k)) /
          (2 * Nat.sqrt k : ℕ)) atTop (nhds 0) :=
  tendsto_reciprocalChebyshevMajorant_div.comp tendsto_two_mul_sqrt

end

end ReciprocalPrimeWindow
end Erdos378
