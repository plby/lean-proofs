/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib.Tactic

/-! # Explicit rounded integer gates for the repaired Claim 6.18 -/

noncomputable section
namespace Erdos547b.ZhaoClaim618RoundedNumerics

def initialCount (r : ℝ) (k : ℕ) : ℕ := ⌊8 * r * k⌋₊
def neighborCount (r : ℝ) (k : ℕ) : ℕ := ⌈3 * r * k⌉₊
def exceptionalCount (η : ℝ) (k : ℕ) : ℕ := ⌈2 * η * k⌉₊
def auxiliaryDegree (r : ℝ) (k : ℕ) : ℕ := ⌊12 * r ^ 2 * k⌋₊
def partnerDegree (r : ℝ) (k : ℕ) : ℕ := ⌊11 * r ^ 2 * k⌋₊
def terminalCount (r : ℝ) (k : ℕ) : ℕ := ⌊(149 / 100 : ℝ) * r * k⌋₊

theorem rounded_gates (r η : ℝ) (k miss v : ℕ)
    (hr : 0 < r) (hr1 : r ≤ 1) (hη : 0 ≤ η) (hηsmall : η ≤ 1 / 100000)
    (hηr : η ≤ r ^ 2 / 1000) (hscale : 1000 ≤ r ^ 2 * k)
    (hmiss : (miss : ℝ) ≤ r * k / 100) (hv : (v : ℝ) ≤ (1 + 8 * η) * k) :
    0 < k ∧ 0 < initialCount r k ∧ (initialCount r k : ℝ) ≤ 8 * r * k ∧
    2 * (neighborCount r k + exceptionalCount η k + 1) + miss ≤ initialCount r k ∧
    partnerDegree r k + exceptionalCount η k ≤ auxiliaryDegree r k ∧
    terminalCount r k * initialCount r k + v * auxiliaryDegree r k ≤
      initialCount r k * neighborCount r k ∧
    16 * r ^ 3 * (k : ℝ) ^ 2 ≤ (terminalCount r k * partnerDegree r k : ℕ) := by
  have hkR : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hr2 : r ^ 2 ≤ r := by nlinarith only [mul_nonneg hr.le (sub_nonneg.mpr hr1)]
  have hrk := mul_le_mul_of_nonneg_right hr2 hkR
  have hrk0 : 0 ≤ r * k := mul_nonneg hr.le hkR
  have hunit : 1 ≤ r * k / 1000 := by linarith only [hscale, hrk]
  have hunit2 : 1 ≤ r ^ 2 * k / 1000 := by linarith only [hscale]
  have ha0 : 0 ≤ 8 * r * k := by positivity
  have hb0 : 0 ≤ 3 * r * k := by positivity
  have he0 : 0 ≤ 2 * η * k := by positivity
  have ht0 : 0 ≤ 12 * r ^ 2 * k := by positivity
  have hu0 : 0 ≤ 11 * r ^ 2 * k := by positivity
  have hz0 : 0 ≤ (149 / 100 : ℝ) * r * k := by positivity
  have haU := Nat.floor_le ha0
  have haL := Nat.lt_floor_add_one (8 * r * k)
  have hbL := Nat.le_ceil (3 * r * k)
  have hbU := Nat.ceil_lt_add_one hb0
  have heU := Nat.ceil_lt_add_one he0
  have htU := Nat.floor_le ht0
  have htL := Nat.lt_floor_add_one (12 * r ^ 2 * k)
  have huU := Nat.floor_le hu0
  have huL := Nat.lt_floor_add_one (11 * r ^ 2 * k)
  have hzU := Nat.floor_le hz0
  have hzL := Nat.lt_floor_add_one ((149 / 100 : ℝ) * r * k)
  change (initialCount r k : ℝ) ≤ _ at haU
  change _ < (initialCount r k : ℝ) + 1 at haL
  change _ ≤ (neighborCount r k : ℝ) at hbL
  change (neighborCount r k : ℝ) < _ at hbU
  change (exceptionalCount η k : ℝ) < _ at heU
  change (auxiliaryDegree r k : ℝ) ≤ _ at htU
  change _ < (auxiliaryDegree r k : ℝ) + 1 at htL
  change (partnerDegree r k : ℝ) ≤ _ at huU
  change _ < (partnerDegree r k : ℝ) + 1 at huL
  change (terminalCount r k : ℝ) ≤ _ at hzU
  change _ < (terminalCount r k : ℝ) + 1 at hzL
  have ha : (799 / 100 : ℝ) * r * k ≤ initialCount r k := by
    linarith only [haL, hunit]
  have hb : (neighborCount r k : ℝ) ≤ (301 / 100 : ℝ) * r * k := by
    linarith only [hbU, hunit]
  have hηk := mul_le_mul_of_nonneg_right hηr hkR
  have he : (exceptionalCount η k : ℝ) ≤ r ^ 2 * k / 100 := by
    linarith only [heU, hηk, hunit2]
  have ht : (1199 / 100 : ℝ) * r ^ 2 * k ≤ auxiliaryDegree r k := by
    linarith only [htL, hunit2]
  have hu : (1099 / 100 : ℝ) * r ^ 2 * k ≤ partnerDegree r k := by
    linarith only [huL, hunit2]
  have hz : (148 / 100 : ℝ) * r * k ≤ terminalCount r k := by
    linarith only [hzL, hunit]
  have hv' : (v : ℝ) ≤ (1001 / 1000 : ℝ) * k := by
    have hηk' := mul_le_mul_of_nonneg_right hηsmall hkR
    nlinarith only [hv, hηk', hkR]
  have hk : 0 < k := by
    by_contra h
    have hz : k = 0 := by omega
    simp only [hz, Nat.cast_zero, mul_zero] at hscale
    norm_num at hscale
  have haPos : 0 < initialCount r k := by
    have haposR : (0 : ℝ) < initialCount r k := by linarith only [ha, hunit]
    exact_mod_cast haposR
  refine ⟨hk, haPos, haU, ?_, ?_, ?_, ?_⟩
  · have h : 2 * ((neighborCount r k : ℝ) + exceptionalCount η k + 1) + miss ≤ initialCount r k := by
      linarith only [ha, hb, he, hmiss, hunit, hrk]
    exact_mod_cast h
  · have h : (partnerDegree r k : ℝ) + exceptionalCount η k ≤ auxiliaryDegree r k := by
      linarith only [huU, he, ht]
    exact_mod_cast h
  · have hgap : (151 / 100 : ℝ) * r * k ≤ (neighborCount r k : ℝ) - terminalCount r k := by
      linarith only [hbL, hzU]
    have hleft := mul_le_mul ha hgap (by positivity : 0 ≤ (151 / 100 : ℝ) * r * k)
      (Nat.cast_nonneg (initialCount r k) : (0 : ℝ) ≤ _)
    have hright := mul_le_mul hv' htU (Nat.cast_nonneg (auxiliaryDegree r k) : (0 : ℝ) ≤ _)
      (by positivity : 0 ≤ (1001 / 1000 : ℝ) * k)
    have h : (terminalCount r k : ℝ) * initialCount r k + (v : ℝ) * auxiliaryDegree r k ≤
        (initialCount r k : ℝ) * neighborCount r k := by
      nlinarith only [hleft, hright, sq_nonneg (r * k)]
    exact_mod_cast h
  · have hprod := mul_le_mul hz hu (by positivity : 0 ≤ (1099 / 100 : ℝ) * r ^ 2 * k)
      (Nat.cast_nonneg (terminalCount r k) : (0 : ℝ) ≤ _)
    have hnonneg : 0 ≤ r ^ 3 * (k : ℝ) ^ 2 := by positivity
    have h : 16 * r ^ 3 * (k : ℝ) ^ 2 ≤ (terminalCount r k : ℝ) * partnerDegree r k := by
      nlinarith only [hprod, hnonneg]
    exact_mod_cast h

end Erdos547b.ZhaoClaim618RoundedNumerics

#print axioms Erdos547b.ZhaoClaim618RoundedNumerics.rounded_gates
