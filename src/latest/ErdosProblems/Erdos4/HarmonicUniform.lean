import ErdosProblems.Erdos4.SelbergHarmonicMass

/-!
# Uniform endpoints from the fixed-modulus harmonic asymptotic

An `o(log Q)` error is uniformly `o(log R)` over all `Q ≤ R`: the large
endpoints use the asymptotic and the finitely many small endpoints are
absorbed by `log R`. This avoids a growing-modulus asymptotic in the
coefficient-energy approach to the principal term.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos4.HarmonicUniform

theorem eventually_error_le_log (f : ℕ → ℝ)
    (hf : Tendsto (fun n : ℕ => f n / Real.log n) atTop (nhds 0))
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ n : ℕ in atTop, |f n| ≤ ε * Real.log n := by
  have hlo := (tendsto_order.mp hf).1 (-ε) (by linarith)
  have hhi := (tendsto_order.mp hf).2 ε hε
  filter_upwards [hlo, hhi, eventually_ge_atTop 2] with n hlo hhi hn
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hl := (lt_div_iff₀ hlog).mp hlo
  have hh := (div_lt_iff₀ hlog).mp hhi
  exact abs_le.mpr ⟨by linarith, hh.le⟩

/-- Uniformity here is over the endpoint, with the underlying arithmetic
modulus fixed. -/
theorem eventually_uniform_error_le_log (f : ℕ → ℝ)
    (hf : Tendsto (fun n : ℕ => f n / Real.log n) atTop (nhds 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ R : ℕ in atTop, 2 ≤ R ∧ ∀ Q : ℕ, Q ≤ R → |f Q| ≤ ε * Real.log R := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_error_le_log f hf hε)
  let B : ℝ := ∑ q ∈ Finset.range (max 2 N), |f q|
  have hlog : Tendsto (fun R : ℕ => Real.log (R : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlarge : ∀ᶠ R : ℕ in atTop, B / ε ≤ Real.log R :=
    hlog.eventually (eventually_ge_atTop (B / ε))
  filter_upwards [hlarge, eventually_ge_atTop 2] with R hR htwo
  refine ⟨htwo, ?_⟩
  intro Q hQR
  by_cases hQ : max 2 N ≤ Q
  · have hQN : N ≤ Q := (le_max_right _ _).trans hQ
    have hQpos : 0 < Q := lt_of_lt_of_le (by norm_num : 0 < (2 : ℕ)) ((le_max_left _ _).trans hQ)
    exact (hN Q hQN).trans (mul_le_mul_of_nonneg_left
      (Real.log_le_log (by exact_mod_cast hQpos) (by exact_mod_cast hQR)) hε.le)
  · have hsmall : |f Q| ≤ B :=
      Finset.single_le_sum (s := Finset.range (max 2 N)) (f := fun q => |f q|)
        (fun q _hq => abs_nonneg _) (Finset.mem_range.mpr (by omega))
    have hB : B ≤ ε * Real.log R := by
      have hh := (div_le_iff₀ hε).mp hR
      nlinarith
    exact hsmall.trans hB

/-- The concrete squarefree reciprocal-totient sum has the required
uniform endpoint error for every fixed positive squarefree modulus. -/
theorem fixed_modulus_uniform {W : ℕ} (hW : 0 < W) (hSq : Squarefree W)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ R : ℕ in atTop, 2 ≤ R ∧ ∀ Q : ℕ, Q ≤ R →
      |BoundedGaps.Maynard.squarefreeCoprimeInvTotientMean W Q -
        BoundedGaps.Maynard.coprimeHarmonicDensity W * Real.log Q| ≤ ε * Real.log R := by
  let H := BoundedGaps.Maynard.squarefreeCoprimeInvTotientMean W
  let ρ := BoundedGaps.Maynard.coprimeHarmonicDensity W
  have hbase := BoundedGaps.Maynard.tendsto_squarefreeCoprimeInvTotientMean_div_log hW hSq
  have hlim : Tendsto (fun Q : ℕ => H Q / Real.log Q - ρ) atTop (nhds 0) := by
    simpa only [H, ρ, sub_self] using hbase.sub (tendsto_const_nhds (x := ρ))
  have herror : Tendsto (fun Q : ℕ => (H Q - ρ * Real.log Q) / Real.log Q) atTop (nhds 0) := by
    apply hlim.congr'
    filter_upwards [eventually_ge_atTop 2] with Q hQ
    have hlog : Real.log (Q : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hQ)).ne'
    field_simp
  exact eventually_uniform_error_le_log (fun Q => H Q - ρ * Real.log Q) herror hε

theorem log_floor_error_le {x : ℝ} (hx : 1 ≤ x) :
    |Real.log (⌊x⌋₊ : ℝ) - Real.log x| ≤ Real.log 2 := by
  have hn : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast (Nat.floor_pos.mpr hx)
  have hnpos : (0 : ℝ) < ⌊x⌋₊ := lt_of_lt_of_le zero_lt_one hn
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hfloor : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hxpos.le
  have hupper : x ≤ 2 * (⌊x⌋₊ : ℝ) := by nlinarith [Nat.lt_floor_add_one x]
  have hlo := Real.log_le_log hnpos hfloor
  have hhi := Real.log_le_log hxpos hupper
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hnpos.ne'] at hhi
  exact abs_le.mpr ⟨by linarith, by linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]⟩

/-- The same uniform estimate holds at real endpoints, with the floor
error absorbed by the growing outer logarithm. -/
theorem fixed_modulus_uniform_real {W : ℕ} (hW : 0 < W) (hSq : Squarefree W)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ R : ℕ in atTop, 2 ≤ R ∧ ∀ x : ℝ, 1 ≤ x → x ≤ R →
      |BoundedGaps.Maynard.squarefreeCoprimeInvTotientMean W ⌊x⌋₊ -
        BoundedGaps.Maynard.coprimeHarmonicDensity W * Real.log x| ≤ ε * Real.log R := by
  let ρ := BoundedGaps.Maynard.coprimeHarmonicDensity W
  have hρ : 0 ≤ ρ := by unfold ρ BoundedGaps.Maynard.coprimeHarmonicDensity; positivity
  have hhalf : 0 < ε / 2 := by linarith
  have hlog : Tendsto (fun R : ℕ => Real.log (R : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlarge : ∀ᶠ R : ℕ in atTop, (ρ * Real.log 2) / (ε / 2) ≤ Real.log R :=
    hlog.eventually (eventually_ge_atTop _)
  filter_upwards [fixed_modulus_uniform hW hSq hhalf, hlarge] with R hR hlarge
  refine ⟨hR.1, ?_⟩
  intro x hx hxR
  have hfloorR : ⌊x⌋₊ ≤ R := by
    exact_mod_cast (Nat.floor_le (show 0 ≤ x by linarith)).trans hxR
  have hfirst := hR.2 ⌊x⌋₊ hfloorR
  have hsecond := mul_le_mul_of_nonneg_left (log_floor_error_le hx) hρ
  have hsmall : ρ * Real.log 2 ≤ (ε / 2) * Real.log R := by
    have hh := (div_le_iff₀ hhalf).mp hlarge
    nlinarith
  have hsplit : BoundedGaps.Maynard.squarefreeCoprimeInvTotientMean W ⌊x⌋₊ - ρ * Real.log x =
      (BoundedGaps.Maynard.squarefreeCoprimeInvTotientMean W ⌊x⌋₊ - ρ * Real.log (⌊x⌋₊ : ℝ)) +
        ρ * (Real.log (⌊x⌋₊ : ℝ) - Real.log x) := by ring
  rw [hsplit]
  apply (abs_add_le _ _).trans
  rw [abs_mul, abs_of_nonneg hρ]
  exact (add_le_add hfirst (hsecond.trans hsmall)).trans_eq (by ring)

end Erdos4.HarmonicUniform
