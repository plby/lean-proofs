import ErdosProblems.Erdos378.HighIndexArithmetic

open Filter
open scoped Topology

namespace Erdos378
namespace HighIndexCutoffBridge

def middleIndexBase (N : ℕ) : ℕ :=
  Nat.sqrt (Nat.sqrt (Nat.sqrt N))

def middleIndexAmplifier (N : ℕ) : ℕ :=
  Nat.sqrt (Nat.sqrt (Nat.sqrt (middleIndexBase N)))

def middleIndexCutoff (N : ℕ) : ℕ :=
  middleIndexBase N * middleIndexAmplifier N

lemma tendsto_middleIndexBase_atTop : Tendsto middleIndexBase atTop atTop := by
  unfold middleIndexBase
  have h : Tendsto (fun n : ℕ ↦ Nat.sqrt n) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b ↦ ⟨b * b, fun _ ha ↦ Nat.le_sqrt.mpr ha⟩
  exact h.comp (h.comp h)

lemma tendsto_middleIndexAmplifier_atTop :
    Tendsto middleIndexAmplifier atTop atTop := by
  unfold middleIndexAmplifier
  have h : Tendsto (fun n : ℕ ↦ Nat.sqrt n) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b ↦ ⟨b * b, fun _ ha ↦ Nat.le_sqrt.mpr ha⟩
  exact h.comp (h.comp (h.comp tendsto_middleIndexBase_atTop))

lemma tripleSqrt_upper {m z : ℕ}
    (hz : z = Nat.sqrt (Nat.sqrt (Nat.sqrt m))) (hzpos : 0 < z) :
    m ≤ 16384 * z ^ 8 := by
  let x := Nat.sqrt m
  let y := Nat.sqrt x
  have hzx : z ≤ y := by
    dsimp only [y]
    rw [hz]
    exact Nat.sqrt_le_self _
  have hyx : y ≤ x := Nat.sqrt_le_self _
  have hxpos : 0 < x := lt_of_lt_of_le hzpos (hzx.trans hyx)
  have hypos : 0 < y := lt_of_lt_of_le hzpos hzx
  have hm : m < (x + 1) ^ 2 := by
    simpa only [x, pow_two] using Nat.lt_succ_sqrt m
  have hx : x < (y + 1) ^ 2 := by
    simpa only [y, pow_two] using Nat.lt_succ_sqrt x
  have hy : y < (z + 1) ^ 2 := by
    rw [hz]
    simpa only [pow_two] using
      Nat.lt_succ_sqrt (Nat.sqrt (Nat.sqrt m))
  have hm' : m ≤ 4 * x ^ 2 := by
    calc
      m ≤ (x + 1) ^ 2 := hm.le
      _ ≤ (2 * x) ^ 2 := by gcongr <;> omega
      _ = 4 * x ^ 2 := by ring
  have hx' : x ≤ 4 * y ^ 2 := by
    calc
      x ≤ (y + 1) ^ 2 := hx.le
      _ ≤ (2 * y) ^ 2 := by gcongr <;> omega
      _ = 4 * y ^ 2 := by ring
  have hy' : y ≤ 4 * z ^ 2 := by
    calc
      y ≤ (z + 1) ^ 2 := hy.le
      _ ≤ (2 * z) ^ 2 := by gcongr <;> omega
      _ = 4 * z ^ 2 := by ring
  calc
    m ≤ 4 * x ^ 2 := hm'
    _ ≤ 4 * (4 * y ^ 2) ^ 2 := by gcongr
    _ ≤ 4 * (4 * (4 * z ^ 2) ^ 2) ^ 2 := by gcongr
    _ = 16384 * z ^ 8 := by ring

theorem eventually_N_le_sourceUpper_cutoff_pow_fifteen :
    ∀ᶠ N : ℕ in atTop,
      N ≤ ReciprocalPrimeSelection.sourcePrimeUpper (middleIndexCutoff N) ^ 15 := by
  filter_upwards [tendsto_middleIndexAmplifier_atTop.eventually
    (eventually_ge_atTop 1000000)] with N hb
  let a := middleIndexBase N
  let b := middleIndexAmplifier N
  let q := middleIndexCutoff N
  let t := Nat.sqrt q
  let u := ReciprocalPrimeSelection.sourcePrimeUpper q
  have hbpos : 0 < b := by omega
  have haUpper : a ≤ 16384 * b ^ 8 := by
    apply tripleSqrt_upper (z := b)
    · rfl
    · exact hbpos
  have haPos : 0 < a := by
    have hbLeA : b ≤ a := by
      dsimp only [b, middleIndexAmplifier]
      exact (Nat.sqrt_le_self _).trans
        ((Nat.sqrt_le_self _).trans (Nat.sqrt_le_self _))
    exact lt_of_lt_of_le hbpos hbLeA
  have hNUpper : N ≤ 16384 * a ^ 8 := by
    exact tripleSqrt_upper rfl haPos
  have hqPos : 0 < q := by
    dsimp only [q, middleIndexCutoff]
    positivity
  have htPos : 0 < t := Nat.sqrt_pos.2 hqPos
  have hqUpper : q ≤ b ^ 10 := by
    calc
      q = a * b := rfl
      _ ≤ (16384 * b ^ 8) * b := Nat.mul_le_mul_right b haUpper
      _ = 16384 * b ^ 9 := by ring
      _ ≤ b * b ^ 9 := by
        exact Nat.mul_le_mul_right (b ^ 9) (by omega)
      _ = b ^ 10 := by ring
  have htB : t ≤ b ^ 5 := by
    have := Nat.sqrt_le_sqrt hqUpper
    simpa only [t, show Nat.sqrt (b ^ 10) = b ^ 5 by
      rw [show b ^ 10 = (b ^ 5) ^ 2 by ring, Nat.sqrt_eq']] using this
  have hqLower : q ≤ 4 * t ^ 2 := by
    have hlt : q < (t + 1) ^ 2 := by
      simpa only [t, pow_two] using Nat.lt_succ_sqrt q
    calc
      q ≤ (t + 1) ^ 2 := hlt.le
      _ ≤ (2 * t) ^ 2 := by gcongr <;> omega
      _ = 4 * t ^ 2 := by ring
  have hpow : a ^ 8 * b ^ 8 ≤ 65536 * t ^ 16 := by
    calc
      a ^ 8 * b ^ 8 = q ^ 8 := by
        dsimp only [q, middleIndexCutoff]
        ring
      _ ≤ (4 * t ^ 2) ^ 8 := by gcongr
      _ = 65536 * t ^ 16 := by ring
  have hstep : a ^ 8 * b ^ 8 ≤ 65536 * t ^ 15 * b ^ 5 := by
    calc
      a ^ 8 * b ^ 8 ≤ 65536 * t ^ 16 := hpow
      _ = 65536 * t ^ 15 * t := by ring
      _ ≤ 65536 * t ^ 15 * b ^ 5 := Nat.mul_le_mul_left _ htB
  have hcancel : a ^ 8 * b ^ 3 ≤ 65536 * t ^ 15 := by
    apply Nat.le_of_mul_le_mul_right (c := b ^ 5)
    · simpa only [show a ^ 8 * b ^ 3 * b ^ 5 = a ^ 8 * b ^ 8 by ring,
        show 65536 * t ^ 15 * b ^ 5 = 65536 * t ^ 15 * b ^ 5 by rfl]
        using hstep
    · positivity
  have hbCube : 16384 * 65536 ≤ b ^ 3 := by
    calc
      16384 * 65536 ≤ 1000000 ^ 3 := by norm_num
      _ ≤ b ^ 3 := by gcongr
  have haT : 16384 * a ^ 8 ≤ t ^ 15 := by
    apply Nat.le_of_mul_le_mul_right (c := 65536)
    · calc
        16384 * a ^ 8 * 65536 ≤ a ^ 8 * b ^ 3 := by
          calc
            16384 * a ^ 8 * 65536 = a ^ 8 * (16384 * 65536) := by ring
            _ ≤ a ^ 8 * b ^ 3 := Nat.mul_le_mul_left _ hbCube
        _ ≤ 65536 * t ^ 15 := hcancel
        _ = t ^ 15 * 65536 := by ring
    · norm_num
  have htU : t ≤ u := by
    dsimp only [u, ReciprocalPrimeSelection.sourcePrimeUpper]
    have ht9 : 9 ≤ t := by
      have hbq : b ≤ q := by
        dsimp only [q, middleIndexCutoff]
        simpa using Nat.mul_le_mul_right b (show 1 ≤ a by omega)
      have hbSq : 81 ≤ q := (show 81 ≤ b by omega).trans hbq
      exact Nat.le_sqrt'.mpr hbSq
    omega
  exact hNUpper.trans (haT.trans (by gcongr))

end HighIndexCutoffBridge
end Erdos378
