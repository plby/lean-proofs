import ErdosProblems.Erdos321.DiscreteOperator
import ErdosProblems.Erdos321.KernelLimit

namespace Erdos321

open Filter Asymptotics
open scoped Topology

/-- A deliberately small fixed fraction of the logarithmic scale. -/
noncomputable def adaptiveLogScale (N : ℕ) : ℕ :=
  ⌊Real.log N / 16⌋₊

/-- The smooth cutoff paired with `adaptiveLogScale`. -/
noncomputable def adaptiveSmoothCutoff (N : ℕ) : ℕ :=
  N / adaptiveLogScale N

/-- The exact quotient endpoint produced by `adaptiveSmoothCutoff`. -/
noncomputable def adaptiveEndpoint (N : ℕ) : ℕ :=
  N / (adaptiveSmoothCutoff N + 1)

/-- All endpoint conditions needed to feed exactly the same adaptive endpoint
into the normalized lower and upper recurrences. -/
structure AdaptiveCutoffData (N : ℕ) : Prop where
  logScale_ge_four : 4 ≤ adaptiveLogScale N
  logScale_sq_le : adaptiveLogScale N * adaptiveLogScale N ≤ N
  smooth_ge_one : 1 ≤ adaptiveSmoothCutoff N
  smooth_le : adaptiveSmoothCutoff N ≤ N
  entropy_unique : N < (adaptiveSmoothCutoff N + 1) ^ 2
  endpoint_ge_two : 2 ≤ adaptiveEndpoint N
  endpoint_lt_scale : adaptiveEndpoint N < adaptiveLogScale N
  endpoint_le_log : ((adaptiveEndpoint N : ℕ) : ℝ) ≤ Real.log N
  lower_disjoint : adaptiveEndpoint N < N / (adaptiveEndpoint N + 1)
  upper_endpoint : 2 ≤ N / (adaptiveEndpoint N + 1)
  log_ge_one : 1 ≤ Real.log N

private theorem adaptiveCutoffData_of_bounds {N : ℕ}
    (hlog : 64 ≤ Real.log N)
    (hlogSq : Real.log N ^ 2 ≤ (N : ℝ)) :
    AdaptiveCutoffData N := by
  let L := adaptiveLogScale N
  let Q := adaptiveSmoothCutoff N
  let T := adaptiveEndpoint N
  have hlog0 : 0 ≤ Real.log N := by linarith
  have hLcast : (L : ℝ) ≤ Real.log N / 16 := by
    dsimp [L, adaptiveLogScale]
    exact Nat.floor_le (by positivity)
  have hL4 : 4 ≤ L := by
    apply Nat.le_floor
    dsimp [L, adaptiveLogScale]
    norm_num
    linarith
  have hLpos : 0 < L := by omega
  have hLsqR : (L : ℝ) ^ 2 ≤ Real.log N ^ 2 := by
    nlinarith
  have hLsq : L * L ≤ N := by
    have : L ^ 2 ≤ N := by exact_mod_cast hLsqR.trans hlogSq
    simpa [pow_two] using this
  have hLN : L ≤ N := by
    nlinarith
  have hQ1 : 1 ≤ Q := by
    dsimp [Q, adaptiveSmoothCutoff]
    exact Nat.div_pos hLN hLpos
  have hQN : Q ≤ N := by
    dsimp [Q, adaptiveSmoothCutoff]
    exact Nat.div_le_self N L
  have hLQ : L ≤ Q := by
    dsimp [Q, adaptiveSmoothCutoff]
    exact (Nat.le_div_iff_mul_le hLpos).2 hLsq
  have hNltLQ : N < L * (Q + 1) := by
    dsimp [Q, adaptiveSmoothCutoff]
    exact Nat.lt_mul_div_succ N hLpos
  have hUnique : N < (Q + 1) ^ 2 := by
    calc
      N < L * (Q + 1) := hNltLQ
      _ ≤ (Q + 1) * (Q + 1) := by
        exact Nat.mul_le_mul_right (Q + 1) (hLQ.trans (Nat.le_add_right Q 1))
      _ = (Q + 1) ^ 2 := by ring
  have hTltL : T < L := by
    dsimp [T, adaptiveEndpoint]
    rw [Nat.div_lt_iff_lt_mul (by omega : 0 < Q + 1)]
    simpa [mul_comm] using hNltLQ
  have hQL : Q * L ≤ N := by
    dsimp [Q, adaptiveSmoothCutoff]
    exact Nat.div_mul_le_self N L
  have h4Q : 4 * Q ≤ N := by
    calc
      4 * Q ≤ L * Q := Nat.mul_le_mul_right Q hL4
      _ = Q * L := Nat.mul_comm L Q
      _ ≤ N := hQL
  have hTwoQ : 2 * (Q + 1) ≤ N := by
    omega
  have hT2 : 2 ≤ T := by
    dsimp [T, adaptiveEndpoint]
    exact (Nat.le_div_iff_mul_le (by omega : 0 < Q + 1)).2 hTwoQ
  have hTsuccL : T + 1 ≤ L := by omega
  have hTsq : (T + 1) * (T + 1) ≤ N := by
    calc
      (T + 1) * (T + 1) ≤ L * L :=
        Nat.mul_le_mul hTsuccL hTsuccL
      _ ≤ N := hLsq
  have hDisjoint : T < N / (T + 1) := by
    have hle : T + 1 ≤ N / (T + 1) :=
      (Nat.le_div_iff_mul_le (by omega : 0 < T + 1)).2 hTsq
    omega
  have hUpperEnd : 2 ≤ N / (T + 1) := by
    apply (Nat.le_div_iff_mul_le (by omega : 0 < T + 1)).2
    have h2T : 2 * (T + 1) ≤ (T + 1) * (T + 1) := by
      exact Nat.mul_le_mul_right (T + 1) (by omega : 2 ≤ T + 1)
    exact h2T.trans hTsq
  have hTlog : (T : ℝ) ≤ Real.log N := by
    have hTL : (T : ℝ) ≤ L := by exact_mod_cast (Nat.le_of_lt hTltL)
    nlinarith
  exact {
    logScale_ge_four := hL4
    logScale_sq_le := hLsq
    smooth_ge_one := hQ1
    smooth_le := hQN
    entropy_unique := hUnique
    endpoint_ge_two := hT2
    endpoint_lt_scale := hTltL
    endpoint_le_log := hTlog
    lower_disjoint := hDisjoint
    upper_endpoint := hUpperEnd
    log_ge_one := by linarith
  }

/-- The common adaptive cutoff eventually satisfies every endpoint hypothesis
of both normalized recurrences. -/
theorem eventually_adaptiveCutoffData :
    ∀ᶠ N : ℕ in atTop, AdaptiveCutoffData N := by
  have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hlogTop : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hcast
  have hlog64 : ∀ᶠ N : ℕ in atTop, 64 ≤ Real.log (N : ℝ) :=
    hlogTop.eventually (eventually_ge_atTop 64)
  have hratioR : Tendsto
      (fun x : ℝ => Real.log x ^ 2 / x) atTop (𝓝 0) :=
    Real.isLittleO_pow_log_id_atTop.tendsto_div_nhds_zero
  have hratioN : Tendsto
      (fun n : ℕ => Real.log (n : ℝ) ^ 2 / (n : ℝ)) atTop (𝓝 0) :=
    hratioR.comp hcast
  have hratioLe : ∀ᶠ N : ℕ in atTop,
      Real.log (N : ℝ) ^ 2 / (N : ℝ) ≤ 1 :=
    hratioN.eventually (Iic_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  have hNpos : ∀ᶠ N : ℕ in atTop, 0 < N := eventually_atTop.2 ⟨1, by omega⟩
  filter_upwards [hlog64, hratioLe, hNpos] with N hlog hratio hNp
  apply adaptiveCutoffData_of_bounds hlog
  simpa using (div_le_iff₀ (by exact_mod_cast hNp)).mp hratio

end Erdos321
