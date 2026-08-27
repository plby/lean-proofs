import ErdosProblems.Erdos587.HooleyNearbyHigh
import ErdosProblems.Erdos587.HighBlocks

/-! # Exact real dual widths and the global nearby scale margins -/

namespace Erdos587

lemma delta_nearby_profile_scale {R r v : ℕ} (hR : 0 < R) (hv : 0 < v)
    {L : ℝ} (hL : 0 < L) (hlo : R ≤ r) (hhi : r ≤ 2 * R) :
    1 / 2 ≤ ((v : ℝ) / (r * L)) * (2 * R * L / v) ∧
      ((v : ℝ) / (r * L)) * (2 * R * L / v) ≤ 2 := by
  have hr : 0 < (r : ℝ) := by exact_mod_cast hR.trans_le hlo
  have hvR : (v : ℝ) ≠ 0 := by exact_mod_cast hv.ne'
  have heq : ((v : ℝ) / (r * L)) * (2 * R * L / v) = 2 * R / r := by field_simp
  rw [heq]
  have hloR : (R : ℝ) ≤ r := by exact_mod_cast hlo
  have hhiR : (r : ℝ) ≤ 2 * R := by exact_mod_cast hhi
  constructor
  · apply (le_div_iff₀ hr).mpr
    linarith
  · apply (div_le_iff₀ hr).mpr
    linarith

lemma delta_nearby_global_block_parameters {u v M d q R X : ℕ}
    (hd : 0 < d) (hq : 0 < q) (hv : 0 < v) (hR : 0 < R)
    (hdq : d * q = u) (hdR : d * R ≤ M) {L κ : ℝ} (hL : 0 < L)
    (hwidth : 2 ≤ (R : ℝ) * L / v)
    (hsep : 4 * L * (X : ℝ) ^ κ ≤ v) (hglobal : 4 * (M : ℝ) * L ≤ u * v)
    (hsize : (4 * L + 16 * u) * M ≤ X) :
    let K := 2 * (R : ℝ) * L / v
    1 ≤ K ∧ 2 * K ≤ X ∧ K < q ∧ (v : ℝ) * K + 16 * q * R ≤ X ∧
      2 * K * (X : ℝ) ^ κ ≤ R ∧ K * v ≤ 4 * R * L := by
  let K := 2 * (R : ℝ) * L / v
  change 1 ≤ K ∧ 2 * K ≤ X ∧ K < q ∧ (v : ℝ) * K + 16 * q * R ≤ X ∧
    2 * K * (X : ℝ) ^ κ ≤ R ∧ K * v ≤ 4 * R * L
  have hdreal : 0 < (d : ℝ) := by exact_mod_cast hd
  have hqreal : 0 < (q : ℝ) := by exact_mod_cast hq
  have hvreal : 0 < (v : ℝ) := by exact_mod_cast hv
  have hvone : (1 : ℝ) ≤ v := by exact_mod_cast hv
  have hRreal : 0 < (R : ℝ) := by exact_mod_cast hR
  have hdqreal : (d : ℝ) * q = u := by exact_mod_cast hdq
  have hdRreal : (d : ℝ) * R ≤ M := by exact_mod_cast hdR
  have hRM : R ≤ M := (Nat.le_mul_of_pos_left R hd).trans hdR
  have hRMreal : (R : ℝ) ≤ M := by exact_mod_cast hRM
  have hqu : q ≤ u := by rw [← hdq]; exact Nat.le_mul_of_pos_left q hd
  have hqureal : (q : ℝ) ≤ u := by exact_mod_cast hqu
  have hK : 1 ≤ K := by
    have heq : K = 2 * ((R : ℝ) * L / v) := by dsimp [K]; ring
    rw [heq]
    linarith
  have hKv : K * v = 2 * R * L := by dsimp [K]; field_simp
  have hKle : K ≤ 2 * R * L := by nlinarith
  have hKX : 2 * K ≤ X := by
    have ht : 4 * (R : ℝ) * L ≤ 4 * M * L := by gcongr
    have huM : 0 ≤ (16 * (u : ℝ)) * M := by positivity
    nlinarith [ht]
  have hlocal : 4 * (R : ℝ) * L ≤ q * v := by
    apply (mul_le_mul_iff_right₀ hdreal).mp
    calc
      (d : ℝ) * (4 * R * L) = 4 * ((d : ℝ) * R) * L := by ring
      _ ≤ 4 * M * L := by gcongr
      _ ≤ (u : ℝ) * v := hglobal
      _ = (d : ℝ) * (q * v) := by rw [← hdqreal]; ring
  have hKq : K < q := by
    have ht : K * (v : ℝ) < q * v := by nlinarith
    exact (mul_lt_mul_iff_left₀ hvreal).mp ht
  have hvalue : (v : ℝ) * K + 16 * q * R ≤ X := by
    have ht : 16 * (q : ℝ) * R ≤ 16 * u * M := by gcongr
    have hs : 2 * (R : ℝ) * L ≤ 2 * M * L := by gcongr
    have hML : 0 ≤ (M : ℝ) * L := by positivity
    nlinarith [ht, hs]
  have hsep' : 2 * K * (X : ℝ) ^ κ ≤ R := by
    apply (mul_le_mul_iff_left₀ hvreal).mp
    calc
      (2 * K * (X : ℝ) ^ κ) * v = (R : ℝ) * (4 * L * (X : ℝ) ^ κ) := by
        calc
          _ = 2 * (K * v) * (X : ℝ) ^ κ := by ring
          _ = _ := by rw [hKv]; ring
      _ ≤ (R : ℝ) * v := mul_le_mul_of_nonneg_left hsep hRreal.le
  refine ⟨hK, hKX, hKq, hvalue, hsep', ?_⟩
  rw [hKv]
  nlinarith

end Erdos587
