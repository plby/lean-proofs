import ErdosProblems.Erdos19.CoveredColorParameters
import ErdosProblems.Erdos19.ReservedPaletteParameters

/-! # Capacity room supplied by a degree deficit inside a buffer -/

namespace Erdos19

theorem buffer_capacity_room (n D b r L M s t : ℕ) (hs : 2 ≤ s) (ht : 0 < t)
    (hns : s ≤ n) (hDpos : 0 < D) (hDlow : n ≤ 2 * D) (hDhigh : D ≤ n)
    (hbuffer : n / t ≤ b) (hDM : D ≤ L * M)
    (hpool : 2 * r + (2 * r) * (2 * r * M) + 1 ≤ n / (16 * s * t)) :
    b * (D - n / s) / D + 2 * r + (2 * r) * ((2 * r) * D / L) <
      b - n / (16 * s * t) := by
  let q := n / (16 * s * t)
  let d := n / s
  let load := b * (D - d) / D
  have hspos : 0 < s := by omega
  have hdpos : 1 ≤ d := (Nat.le_div_iff_mul_le hspos).mpr (by simpa using hns)
  have hfloor := Nat.lt_mul_div_succ n hspos
  have hDscale : D ≤ 2 * s * d := by
    have hscale := Nat.mul_le_mul_left s (show d + 1 ≤ 2 * d by omega)
    change n < s * (d + 1) at hfloor
    nlinarith only [hDhigh, hfloor, hscale]
  have hdD : d ≤ D := by
    have hdscale := Nat.mul_le_mul_right d hs
    have hdiv : s * d ≤ n := Nat.mul_div_le n s
    omega
  have hbq : 4 * s * q ≤ b := by
    have h := scaled_floor_le_div n (16 * s) t ht
    change (16 * s) * q ≤ n / t at h
    nlinarith only [h, hbuffer]
  have hload : load + 2 * q ≤ b := by
    have hdiv : D * load ≤ b * (D - d) := Nat.mul_div_le (b * (D - d)) D
    have hscale := Nat.mul_le_mul_left (2 * q) hDscale
    have hbufferScale := Nat.mul_le_mul_right d hbq
    have hsum := Nat.sub_add_cancel hdD
    have hsumScale := congrArg (fun z ↦ b * z) hsum
    apply Nat.le_of_mul_le_mul_left (c := D) _ hDpos
    nlinarith only [hdiv, hscale, hbufferScale, hsumScale]
  have hdiv : (2 * r) * D / L ≤ 2 * r * M := by
    apply Nat.div_le_of_le_mul
    have h := Nat.mul_le_mul_left (2 * r) hDM
    nlinarith only [h]
  have hterm := Nat.mul_le_mul_left (2 * r) hdiv
  change 2 * r + (2 * r) * (2 * r * M) + 1 ≤ q at hpool
  change load + 2 * r + (2 * r) * ((2 * r) * D / L) < b - q
  omega

#print axioms buffer_capacity_room

end Erdos19
