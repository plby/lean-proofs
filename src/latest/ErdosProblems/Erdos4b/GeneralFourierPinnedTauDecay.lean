/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierPinnedUnconditionalDistribution

/-!
# Explicit logarithmic saving in the pinned weighted discrepancy bound

The prime-level exponent may be chosen after the fixed divisor-power
base. An even integer exponent leaves any desired inverse log power.
-/

namespace Erdos4b

noncomputable section

theorem sqrt_weighted_log_envelope_identity
    (D L : ℕ) {C x t : ℝ} (hC : 0 ≤ C) (hx : 0 ≤ x) (ht : 0 < t) :
    Real.sqrt (6 * x * (2 * t) ^ (2 * D)) *
      Real.sqrt (C * x / t ^ (2 * (D + L))) =
      Real.sqrt (6 * C) * 2 ^ D * x / t ^ L := by
  have hp (n : ℕ) : Real.sqrt (t ^ (2 * n)) = t ^ n := by
    rw [Nat.mul_comm 2 n, pow_mul, Real.sqrt_sq (pow_nonneg ht.le n)]
  have hp2 : Real.sqrt ((2 * t) ^ (2 * D)) = (2 * t) ^ D := by
    rw [Nat.mul_comm 2 D, pow_mul, Real.sqrt_sq (by positivity)]
  rw [Real.sqrt_mul (by positivity : 0 ≤ 6 * x), hp2,
    Real.sqrt_div (mul_nonneg hC hx), hp, Real.sqrt_mul hC]
  have hcombine : Real.sqrt (6 * x) * Real.sqrt C * Real.sqrt x = Real.sqrt (6 * C) * x := by
    rw [← Real.sqrt_mul (by positivity : 0 ≤ 6 * x),
      ← Real.sqrt_mul (by positivity : 0 ≤ 6 * x * C)]
    rw [show 6 * x * C * x = (6 * C) * x ^ 2 by ring,
      Real.sqrt_mul (by positivity : 0 ≤ 6 * C), Real.sqrt_sq hx]
  rw [mul_pow, pow_add]
  have htD : t ^ D ≠ 0 := pow_ne_zero _ ht.ne'
  have htL : t ^ L ≠ 0 := pow_ne_zero _ ht.ne'
  field_simp
  nlinarith [hcombine]

theorem sqrt_progressionTauEnvelope_le_logSaving
    (D L : ℕ) {C : ℝ} {x Q : ℕ} (hC : 0 ≤ C) (hx : 1 ≤ x)
    (hlog : 1 ≤ Real.log x) (hQ : 1 ≤ Q) (hQx : Q ≤ x) :
    Real.sqrt ((3 : ℝ) * ((x + 1 : ℕ) : ℝ) * (1 + Real.log Q) ^ (2 * D)) *
      Real.sqrt (C * (x : ℝ) / Real.log x ^ (2 * (D + L))) ≤
      Real.sqrt (6 * C) * 2 ^ D * (x : ℝ) / Real.log x ^ L := by
  have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast (zero_lt_one.trans_le hQ)
  have hlogQ0 : 0 ≤ Real.log Q := Real.log_nonneg (by exact_mod_cast hQ)
  have hlogQx : Real.log Q ≤ Real.log x :=
    Real.log_le_log hQpos (by exact_mod_cast hQx)
  have hbase : 1 + Real.log Q ≤ 2 * Real.log x := by linarith
  have hxone : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hfront : (3 : ℝ) * ((x + 1 : ℕ) : ℝ) ≤ 6 * (x : ℝ) := by
    push_cast
    linarith
  have hfirst : (3 : ℝ) * ((x + 1 : ℕ) : ℝ) * (1 + Real.log Q) ^ (2 * D) ≤
      6 * (x : ℝ) * (2 * Real.log x) ^ (2 * D) :=
    mul_le_mul hfront (pow_le_pow_left₀ (by linarith) hbase _)
      (pow_nonneg (by linarith) _) (by positivity)
  apply (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hfirst) (Real.sqrt_nonneg _)).trans_eq
  exact sqrt_weighted_log_envelope_identity D L hC hx0 (by linarith)

theorem pinnedFlatTauDiscrepancyBound_le_logSaving
    (K L : ℕ) {C : ℝ} {x Q : ℕ} (hC : 0 ≤ C) (hx : 1 ≤ x)
    (hlog : 1 ≤ Real.log x) (hQ : 1 ≤ Q) (hQx : Q ≤ x) :
    pinnedFlatTauDiscrepancyBound K C
        ((2 * ((2 ^ (4 * (K - 1))) ^ 2 + L) : ℕ) : ℝ) x Q ≤
      Real.sqrt (6 * C) * 2 ^ ((2 ^ (4 * (K - 1))) ^ 2) * (x : ℝ) / Real.log x ^ L := by
  have hrpow : Real.rpow (Real.log x) ((2 * ((2 ^ (4 * (K - 1))) ^ 2 + L) : ℕ) : ℝ) =
      Real.log x ^ (2 * ((2 ^ (4 * (K - 1))) ^ 2 + L)) := Real.rpow_natCast _ _
  unfold pinnedFlatTauDiscrepancyBound
  rw [hrpow]
  exact sqrt_progressionTauEnvelope_le_logSaving ((2 ^ (4 * (K - 1))) ^ 2) L hC hx hlog hQ hQx

theorem exists_uniform_pinnedSourceEndpoint_logSaving
    {K : ℕ} {J : Type*} (S : Finset J) (F : J → Fin K → ℝ → ℝ) (G : ℝ → ℝ)
    (hFcompact : ∀ j i, HasCompactSupport (F j i)) (hFcont : ∀ j i, Continuous (F j i))
    (hGcompact : HasCompactSupport G) (hGcont : Continuous G)
    (hFsupport : ∀ j ∈ S, ∀ u : Fin K → ℝ,
      (∀ i, 0 ≤ u i) → (∀ i, F j i (u i) ≠ 0) → (∑ i, u i) ≤ (1 : ℝ) / 10)
    (hGsupport : ∀ t, 0 ≤ t → G t ≠ 0 → t ≤ 1) (L : ℕ) :
    ∃ C ≥ 0, ∃ X₀ : ℕ, 3 ≤ X₀ ∧
      ∀ (h : Fin K) (P : Finset ℕ) (V LE : ℝ) (x : ℕ),
        (∀ p ∈ P, p.Prime) → 80 ≤ V → 0 < LE → (K : ℝ) * LE ≤ V / 40 →
        3 * V / 4 ≤ Real.log x → X₀ ≤ x →
        pinnedSourceEndpointErrorBound S F G h P x V LE ≤ C * (x : ℝ) / Real.log x ^ L := by
  let D : ℕ := (2 ^ (4 * (K - 1))) ^ 2
  have he : 0 < ((2 * (D + L) : ℕ) : ℝ) := by
    dsimp only [D]
    positivity
  obtain ⟨C₀, hC₀, C, hC, X₀, hX₀, hbound⟩ := exists_uniform_pinnedSourceEndpointErrorBound
    S F G hFcompact hFcont hGcompact hGcont hFsupport hGsupport he
  refine ⟨C₀ ^ 2 * (Real.sqrt (6 * C) * 2 ^ D), by positivity, X₀, hX₀, ?_⟩
  intro h P V LE x hP hV hLE hsmall hlog hx
  have hxpos : 0 < x := by omega
  have hlog1 : 1 ≤ Real.log x := by linarith
  have hRpos : 1 ≤ pinnedSourceProductRadius K V LE := pinnedSourceProductRadius_pos K V LE
  have hRx := pinnedSourceProductRadius_le_endpoint K hV hLE.le hsmall hxpos hlog
  have hdecay := pinnedFlatTauDiscrepancyBound_le_logSaving K L hC hxpos hlog1 hRpos hRx
  calc
    _ ≤ C₀ ^ 2 * pinnedFlatTauDiscrepancyBound K C
        ((2 * (D + L) : ℕ) : ℝ) x (pinnedSourceProductRadius K V LE) :=
      hbound h P V LE x hP hV hLE hsmall hlog hx
    _ ≤ C₀ ^ 2 * (Real.sqrt (6 * C) * 2 ^ D * (x : ℝ) / Real.log x ^ L) :=
      mul_le_mul_of_nonneg_left hdecay (sq_nonneg C₀)
    _ = _ := by ring

end

end Erdos4b
