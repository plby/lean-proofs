import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Scalar inequalities for the outgoing N5 facet

These lemmas use only ordered real algebra.  Trigonometric facts about the two
facet directions are supplied separately by their callers.
-/

namespace Puzzling139335.N5Facet

/-- The two support inequalities place the difference vector in the cone
spanned by the two facet directions. -/
theorem cone_projection_bounds {c s p q x y : ℝ}
    (hc : 0 < c) (hp : 0 < p) (hs : 0 ≤ s) (hq : 0 ≤ q)
    (hd : 0 < c * q - s * p) (hpq : p ^ 2 + q ^ 2 = 1)
    (h1 : 0 ≤ -s * x + c * y) (h2 : -q * x + p * y ≤ 0) :
    0 ≤ x ∧ 0 ≤ p * x + q * y := by
  have h2' : 0 ≤ q * x - p * y := by linarith
  have hx : 0 ≤ (c * q - s * p) * x := by
    calc
      0 ≤ c * (q * x - p * y) + p * (-s * x + c * y) :=
        add_nonneg (mul_nonneg hc.le h2') (mul_nonneg hp.le h1)
      _ = (c * q - s * p) * x := by ring
  refine ⟨(mul_nonneg_iff_of_pos_left hd).mp hx, ?_⟩
  have hcoef : 0 ≤ c * p + s * q :=
    add_nonneg (mul_nonneg hc.le hp.le) (mul_nonneg hs hq)
  have hid : (c * q - s * p) * (p * x + q * y) =
      (c * p + s * q) * (q * x - p * y) + (-s * x + c * y) := by
    calc
      (c * q - s * p) * (p * x + q * y) =
          (c * p + s * q) * (q * x - p * y) +
            (-s * x + c * y) * (p ^ 2 + q ^ 2) := by ring
      _ = (c * p + s * q) * (q * x - p * y) + (-s * x + c * y) := by
        rw [hpq, mul_one]
  apply (mul_nonneg_iff_of_pos_left hd).mp
  rw [hid]
  exact add_nonneg (mul_nonneg hcoef h2') h1

/-- The two source endpoints and the positive intervening face force a strict
bound on the combined horizontal and vertical span. -/
theorem source_span {L T p s Xx h c : ℝ}
    (hj : 0 < L - T) (hps : s < p) (hX : Xx ≤ h - L * c)
    (hlower : (L - T) * p ≤ Xx) (hF : h + T * s ≤ 1) :
    L * (c + s) < 1 := by
  have hstrict : (L - T) * s < (L - T) * p :=
    mul_lt_mul_of_pos_left hps hj
  nlinarith only [hstrict, hX, hlower, hF]

/-- The rightward placement would require the larger coefficient at length
`L` to be at most the smaller positive coefficient at length `T < L`. -/
theorem right_suffix_algebra {L T p q Xx Xy h c s : ℝ}
    (hL : 0 < L) (hTL : T < L) (hp : 0 < p) (hq : 0 < q)
    (hX : Xx ≤ h - L * c) (htri : Xy ≤ Xx) (hF : h + T * s ≤ 1)
    (hw : p + q * (1 - L) - T ≤ p * Xx + q * Xy)
    (hB : 0 < 1 - s * (p + q))
    (hAB : 1 - s * (p + q) < c * (p + q) - q) : False := by
  have hpq : 0 < p + q := add_pos hp hq
  have hwu : p * Xx + q * Xy ≤ (p + q) * (1 - L * c - T * s) := by
    calc
      p * Xx + q * Xy ≤ p * Xx + q * Xx :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left htri hq.le)
      _ = (p + q) * Xx := by ring
      _ ≤ (p + q) * (h - L * c) := mul_le_mul_of_nonneg_left hX hpq.le
      _ ≤ (p + q) * (1 - L * c - T * s) :=
        mul_le_mul_of_nonneg_left (by linarith) hpq.le
  have hcoeff : (c * (p + q) - q) * L ≤ (1 - s * (p + q)) * T := by
    nlinarith only [le_trans hw hwu]
  have hstrict : (1 - s * (p + q)) * T < (c * (p + q) - q) * L := by
    calc
      (1 - s * (p + q)) * T < (1 - s * (p + q)) * L :=
        mul_lt_mul_of_pos_left hTL hB
      _ < (c * (p + q) - q) * L := mul_lt_mul_of_pos_right hAB hL
  exact (not_lt_of_ge hcoeff) hstrict

/-- The leftward placement exceeds the available endpoint coordinate. -/
theorem left_suffix_algebra {L T v u s z b : ℝ}
    (hL : 0 < L) (hTL : T < L) (hv : 0 < v) (huv : s < u - v)
    (hz : 0 ≤ z) (hb : b < L * s) (hsource : z + L * u - T * v ≤ b) :
    False := by
  have hTv : T * v < L * v := mul_lt_mul_of_pos_right hTL hv
  have hLs : L * s < L * (u - v) := mul_lt_mul_of_pos_left huv hL
  nlinarith only [hTv, hLs, hz, hb, hsource]

end Puzzling139335.N5Facet
