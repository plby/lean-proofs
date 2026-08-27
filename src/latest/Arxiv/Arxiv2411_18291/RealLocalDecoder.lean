import Arxiv.Arxiv2411_18291.LocalDecoderOn
import Arxiv.Arxiv2411_18291.RationalIncidence
import Mathlib.Data.Real.Basic

/-!
# Normalized real local decoders for regularity boosting

Divide the integer local decoder by its positive multiplier. The resulting
real vector has unit boundary at the distinguished edge, vanishes outside
its decoding set, and retains an explicit coefficient bound.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [DecidableEq V] {q r : ℕ}

def realLocalDecoderOn (q : ℕ) (Z : Finset V) (e : Block V r) (Q : Block V q) : ℝ :=
  (q.descFactorial r : ℝ)⁻¹ * (localDecoderOn q Z e Q : ℝ)

theorem realLocalDecoderOn_eq_zero (Z : Finset V) (e : Block V r) (Q : Block V q)
    (hQ : ¬Q.val ⊆ Z) : realLocalDecoderOn q Z e Q = 0 := by
  simp only [realLocalDecoderOn, localDecoderOn, if_neg hQ, Int.cast_zero, mul_zero]

theorem realLocalDecoderOn_abs_le (hqr : r ≤ q) (Z : Finset V)
    (e : Block V r) (Q : Block V q) :
    |realLocalDecoderOn q Z e Q| ≤ (2 ^ q * r.factorial : ℕ) / (q.descFactorial r : ℝ) := by
  have hN : (0 : ℝ) < q.descFactorial r := by
    exact_mod_cast Nat.descFactorial_pos.mpr hqr
  have hcoeff : |(localDecoderOn q Z e Q : ℝ)| ≤ (2 ^ q * r.factorial : ℕ) := by
    exact_mod_cast localDecoderOn_abs_le hqr Z e Q
  rw [realLocalDecoderOn, abs_mul, abs_inv, abs_of_pos hN]
  calc
    _ ≤ (q.descFactorial r : ℝ)⁻¹ * (2 ^ q * r.factorial : ℕ) :=
      mul_le_mul_of_nonneg_left hcoeff (inv_nonneg.mpr hN.le)
    _ = _ := by ring

variable [Fintype V]

theorem boundary_realLocalDecoderOn (Z : Finset V) (hZ : Z.card = q + r) (hqr : r ≤ q)
    (e : Block V r) (heZ : e.val ⊆ Z) :
    boundary r (realLocalDecoderOn q Z e) = fun e' => if e' = e then (1 : ℝ) else 0 := by
  have hN : (q.descFactorial r : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_pos.mpr hqr).ne'
  unfold realLocalDecoderOn
  rw [boundary_mul]
  have hmap := boundary_map (r := r) (Int.castAddHom ℝ) (localDecoderOn q Z e)
  simp only [Int.coe_castAddHom] at hmap
  rw [hmap, boundary_localDecoderOn Z hZ hqr e heZ]
  funext e'
  by_cases h : e' = e <;> simp [h, hN]

end Arxiv2411_18291
