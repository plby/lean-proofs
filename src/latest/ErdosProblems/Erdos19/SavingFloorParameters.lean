import ErdosProblems.Erdos19.SavingDegreeParameters

/-! # Explicit integer parameters for the saving completion -/

namespace Erdos19

theorem mul_floor_le_div_of_den_le (n a c d : ℕ) (hd : 0 < d) (hden : c * d ≤ a) :
    c * (n / a) ≤ n / d := by
  apply (Nat.le_div_iff_mul_le hd).mpr
  have h := Nat.mul_le_mul_right (n / a) hden
  have hf := Nat.mul_div_le n a
  nlinarith only [h, hf]

theorem saving_special_count_bound (n s B C h : ℕ) (hs : 0 < s)
    (hB : 2048 * s ≤ B) (hn : 2048 * s * C ≤ n) (hh : h ≤ n / B + C) :
    h ≤ n / (1024 * s) := by
  apply (Nat.le_div_iff_mul_le (by positivity : 0 < 1024 * s)).mpr
  have hfloor := Nat.mul_div_le n B
  have hden := Nat.mul_le_mul_right (n / B) hB
  have hscale := Nat.mul_le_mul_left (2048 * s) hh
  nlinarith only [hfloor, hden, hscale, hn]

structure SavingNumericalBounds (n s k t w H L h : ℕ) : Prop where
  degreeError : 2 ≤ n / L
  freshPositive : 8 * (n / L) < n / k
  paletteRoom : 2 * (h + n / k) ≤ n
  specialSmall : 4 * h ≤ n / (32 * s)
  bufferDegreeRoom : 4 * (h + n / (1024 * s)) ≤ n / (4 * s)
  highSubset : n / H ≤ n / (32 * s)
  highLowDisjoint : n / (32 * s) < n / (4 * s)
  initialMissing : n / (32 * s) + n / k + n / L ≤ n / (16 * s)
  finalDegreeRoom : 9 * k * (n / L) + k ≤ n / H
  repairBuffer : n / w + 2 * (n / H) + 9 * (n / L) + 1 ≤ n / (16 * (1024 * s) * t)
  traceRoom : 2 * (n / w) ≤ n / (4 * s) + 1
  specialBuffer : 2 * (n / (16 * s) + h) + 1 ≤ n / (4 * s)
  blockRoom : k * (n / t + n / L) ≤ n / (4 * s)

theorem saving_numerical_bounds (n s k t w H L h : ℕ) (hs : 0 < s) (ht : 0 < t)
    (hk : 128 * s ≤ k) (htk : 8 * s * k ≤ t)
    (hw : 8 * (16 * (1024 * s) * t) ≤ w)
    (hH : 256 * (16 * (1024 * s) * t) ≤ H)
    (hL : 100 * k * H ≤ L) (htL : t ≤ L)
    (hn : max (2 * L) (max H (32 * s)) ≤ n)
    (hh : h ≤ n / (1024 * s)) : SavingNumericalBounds n s k t w H L h := by
  have hkpos : 0 < k := by omega
  have hsbuf : 0 < 16 * (1024 * s) * t := by positivity
  have hHpos : 0 < H := by omega
  have hLpos : 0 < L := by have := Nat.mul_pos hkpos hHpos; nlinarith only [hL, this]
  have hH32 : 32 * s ≤ H := by
    have ht1 : 1 ≤ t := ht
    have hprod := Nat.mul_le_mul_left (16 * (1024 * s)) ht1
    nlinarith only [hH, hprod]
  have hkL : k ≤ L := by
    have hprod := Nat.mul_le_mul_left k (show 1 ≤ 100 * H by omega)
    nlinarith only [hL, hprod]
  have he : 2 ≤ n / L := (Nat.le_div_iff_mul_le hLpos).mpr (by omega)
  have hd₀ : 1 ≤ n / (32 * s) :=
    (Nat.le_div_iff_mul_le (by positivity : 0 < 32 * s)).mpr (by omega)
  have hdelta : 1 ≤ n / H := (Nat.le_div_iff_mul_le hHpos).mpr (by omega)
  have hfScale : 16 * (n / L) ≤ n / k :=
    mul_floor_le_div_of_den_le n L 16 k hkpos (by
      have hp := Nat.mul_le_mul_left k (show 16 ≤ 100 * H by omega)
      nlinarith only [hL, hp])
  have hh4 : 4 * h ≤ n := by
    have hfloor := Nat.mul_div_le n (1024 * s)
    have hscale := Nat.mul_le_mul_left (1024 * s) hh
    have hsmall := Nat.mul_le_mul_right h (show 4 ≤ 1024 * s by omega)
    omega
  have hf4 : 4 * (n / k) ≤ n := by
    have hf := Nat.mul_div_le n k
    have hk4 := Nat.mul_le_mul_right (n / k) (show 4 ≤ k by omega)
    omega
  have hhSmall := mul_floor_le_div_of_den_le n (1024 * s) 4 (32 * s)
    (by positivity) (by omega)
  have hySlack := mul_floor_le_div_of_den_le n (1024 * s) 8 (4 * s)
    (by positivity) (by omega)
  have hd₀Scale := mul_floor_le_div_of_den_le n (32 * s) 8 (4 * s)
    (by positivity) (by omega)
  have hfInitial := mul_floor_le_div_of_den_le n k 4 (32 * s)
    (by positivity) (by omega)
  have heF : n / L ≤ n / k := Nat.div_le_div_left hkL hkpos
  have hd₀Initial := mul_floor_le_div_of_den_le n (32 * s) 2 (16 * s)
    (by positivity) (by omega)
  have hfinal := mul_floor_le_div_of_den_le n L (100 * k) H hHpos hL
  have heDelta := mul_floor_le_div_of_den_le n L 9 H hHpos (by
    have hp := Nat.mul_le_mul_right H (show 9 ≤ 100 * k by omega)
    exact hp.trans hL)
  have hA := mul_floor_le_div_of_den_le n w 8 (16 * (1024 * s) * t) hsbuf hw
  have hdeltaBuf := mul_floor_le_div_of_den_le n H 256 (16 * (1024 * s) * t) hsbuf hH
  have htrace := mul_floor_le_div_of_den_le n w 2 (4 * s) (by positivity) (by
    have hp := Nat.mul_le_mul_left (16 * (1024 * s)) (show 1 ≤ t from ht)
    nlinarith only [hw, hp])
  have hdInit := mul_floor_le_div_of_den_le n (16 * s) 4 (4 * s)
    (by positivity) (by omega)
  have hhInit := mul_floor_le_div_of_den_le n (1024 * s) 2 (16 * s)
    (by positivity) (by omega)
  have hblock := mul_floor_le_div_of_den_le n t (2 * k) (4 * s)
    (by positivity) (by nlinarith only [htk])
  have heT : n / L ≤ n / t := Nat.div_le_div_left htL ht
  have heTscale := Nat.mul_le_mul_left k heT
  refine ⟨he, by omega, by omega, by omega, by omega,
    Nat.div_le_div_left hH32 (by positivity), by omega, by omega, ?_, by omega,
    by omega, by omega, ?_⟩
  · have hke := Nat.mul_le_mul_left k (show 1 ≤ n / L by omega)
    nlinarith only [hfinal, hke]
  · nlinarith only [hblock, heTscale]

#print axioms saving_special_count_bound
#print axioms saving_numerical_bounds

end Erdos19
