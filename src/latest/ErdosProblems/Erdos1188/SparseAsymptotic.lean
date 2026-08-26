import ErdosProblems.Erdos1188.SparseCoarseBound

/- Ported from Lean 4.31.0 to 4.33.0; module names and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Asymptotic exponent scale of the sparse construction
-/

namespace Erdos1188

open Filter Asymptotics
open scoped Topology

/-- Every fixed power of the integer binary logarithm occurring in the sparse
cutoff is little-o of the cutoff itself. -/
theorem sparseBinaryLogPow_isLittleO (k : ℕ) :
    (fun x : ℕ => (((Nat.log 2 (x + 1) + 1 : ℕ) : ℝ) ^ k)) =o[atTop]
      (fun x : ℕ => (x : ℝ)) := by
  have hshift : Tendsto (fun x : ℕ => ((x + 1 : ℕ) : ℝ)) atTop atTop := by
    exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hlog := (Real.isLittleO_pow_log_id_atTop (n := k)).comp_tendsto hshift
  rw [isLittleO_iff]
  intro ε hε
  let c : ℝ := (Real.log 2)⁻¹ + 1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : 0 < c := by dsimp [c]; positivity
  have hδ : 0 < ε / (2 * c ^ k) := by positivity
  have hb := hlog.bound hδ
  have hloglarge : ∀ᶠ x : ℕ in atTop,
      1 ≤ Real.log ((x + 1 : ℕ) : ℝ) :=
    (Real.tendsto_log_atTop.comp hshift).eventually_ge_atTop 1
  filter_upwards [hb, hloglarge, Ici_mem_atTop 1] with x hx hL hx1
  let L := Real.log ((x + 1 : ℕ) : ℝ)
  let R : ℕ := Nat.log 2 (x + 1) + 1
  have hnatlog := Real.natLog_le_logb (x + 1) 2
  have hR : (R : ℝ) ≤ c * L := by
    have hbase : Real.logb 2 ((x + 1 : ℕ) : ℝ) = L * (Real.log 2)⁻¹ := by
      simp [Real.logb, L, div_eq_mul_inv]
    dsimp only [R]
    push_cast
    have hnatlog' : ((Nat.log 2 (x + 1) : ℕ) : ℝ) ≤
        Real.logb 2 (((x + 1 : ℕ) : ℝ)) := by simpa using hnatlog
    rw [hbase] at hnatlog'
    dsimp [c]
    nlinarith
  have hRnonneg : (0 : ℝ) ≤ R := by positivity
  have hLnonneg : 0 ≤ L := le_trans (by norm_num) hL
  have hpow : (R : ℝ) ^ k ≤ c ^ k * L ^ k := by
    calc
      (R : ℝ) ^ k ≤ (c * L) ^ k := pow_le_pow_left₀ hRnonneg hR k
      _ = c ^ k * L ^ k := mul_pow c L k
  have hxnorm : ‖L ^ k‖ ≤ (ε / (2 * c ^ k)) * ‖((x + 1 : ℕ) : ℝ)‖ := by
    simpa [L] using hx
  have hxcast : (((x + 1 : ℕ) : ℝ)) ≤ 2 * (x : ℝ) := by
    have hx1' : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx1
    push_cast
    linarith
  rw [Real.norm_of_nonneg (pow_nonneg hLnonneg k), Real.norm_of_nonneg (by positivity)] at hxnorm
  rw [Real.norm_of_nonneg (pow_nonneg hRnonneg k), Real.norm_of_nonneg (by positivity)]
  calc
    (R : ℝ) ^ k ≤ c ^ k * L ^ k := hpow
    _ ≤ c ^ k * ((ε / (2 * c ^ k)) * (((x + 1 : ℕ) : ℝ))) := by gcongr
    _ ≤ c ^ k * ((ε / (2 * c ^ k)) * (2 * (x : ℝ))) := by gcongr
    _ = ε * (x : ℝ) := by field_simp [ne_of_gt hc]

/-- The logarithm of the integer binary-log factor is negligible compared
with the logarithm of the cutoff. -/
theorem sparseBinaryLog_log_ratio_tendsto_zero :
    Tendsto (fun x : ℕ =>
      Real.log ((Nat.log 2 (x + 1) + 1 : ℕ) : ℝ) /
        Real.log (x : ℝ)) atTop (𝓝 0) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    filter_upwards [Ici_mem_atTop 2] with x hx
    have hxpos : (1 : ℝ) < (x : ℝ) := by exact_mod_cast hx
    have hR : (1 : ℝ) ≤ ((Nat.log 2 (x + 1) + 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 1 ≤ Nat.log 2 (x + 1) + 1)
    have hratio : 0 ≤
        Real.log ((Nat.log 2 (x + 1) + 1 : ℕ) : ℝ) /
          Real.log (x : ℝ) := div_nonneg (Real.log_nonneg hR)
            (Real.log_pos hxpos).le
    exact ha.trans_le hratio
  · intro a ha
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt ha
    let k := n + 1
    have hk : 0 < k := by omega
    have hkreal : (0 : ℝ) < (k : ℝ) := by positivity
    have hkfrac : (1 : ℝ) / (k : ℝ) < a := by simpa [k] using hn
    have hb := (sparseBinaryLogPow_isLittleO k).bound
      (by norm_num : (0 : ℝ) < 1)
    filter_upwards [hb, Ici_mem_atTop 2] with x hpow hx
    let R := Nat.log 2 (x + 1) + 1
    have hR : (1 : ℝ) ≤ (R : ℝ) := by
      exact_mod_cast (by simp [R] : 1 ≤ R)
    have hRpos : (0 : ℝ) < (R : ℝ) := lt_of_lt_of_le zero_lt_one hR
    have hxpos : (1 : ℝ) < (x : ℝ) := by exact_mod_cast hx
    have hxlog : 0 < Real.log (x : ℝ) := Real.log_pos hxpos
    have hpow' : (R : ℝ) ^ k ≤ (x : ℝ) := by
      rw [Real.norm_of_nonneg (pow_nonneg hRpos.le k),
        Real.norm_of_nonneg (by positivity)] at hpow
      simpa [R] using hpow
    have hlogs : (k : ℝ) * Real.log (R : ℝ) ≤ Real.log (x : ℝ) := by
      rw [← Real.log_pow]
      exact Real.strictMonoOn_log.monotoneOn (pow_pos hRpos k)
        (zero_lt_one.trans hxpos) hpow'
    have hsmall : Real.log (R : ℝ) / Real.log (x : ℝ) ≤ (1 : ℝ) / k := by
      rw [div_le_iff₀ hxlog]
      have hdiv : Real.log (R : ℝ) ≤ Real.log (x : ℝ) / (k : ℝ) :=
        (le_div_iff₀ hkreal).2 (by simpa [mul_comm] using hlogs)
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm] using hdiv
    exact hsmall.trans_lt hkfrac

/-- The logarithm of the coarse denominator is negligible compared with
`log x`. -/
theorem sparseCoarseDenominator_log_ratio_tendsto_zero (D : ℕ) (hD : 0 < D) :
    Tendsto (fun x : ℕ =>
      Real.log (sparseCoarseDenominator D x : ℝ) / Real.log (x : ℝ))
      atTop (𝓝 0) := by
  let A : ℕ := 2048 * D
  have hA : 0 < A := by dsimp [A]; positivity
  have hlogx : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hc : Tendsto (fun x : ℕ => Real.log (A : ℝ) / Real.log (x : ℝ))
      atTop (𝓝 0) := hlogx.const_div_atTop _
  have hR := sparseBinaryLog_log_ratio_tendsto_zero
  have hsum : Tendsto (fun x : ℕ =>
      Real.log (A : ℝ) / Real.log (x : ℝ) +
        4 * (Real.log ((Nat.log 2 (x + 1) + 1 : ℕ) : ℝ) /
          Real.log (x : ℝ))) atTop (𝓝 0) := by
    convert hc.add (hR.const_mul 4) using 1 <;> norm_num
  apply hsum.congr'
  filter_upwards [Ici_mem_atTop 2] with x hx
  let R : ℕ := Nat.log 2 (x + 1) + 1
  have hRpos : 0 < R := by simp [R]
  have hxlog : Real.log (x : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hx)).ne'
  have hlogden : Real.log (sparseCoarseDenominator D x : ℝ) =
      Real.log (A : ℝ) + 4 * Real.log (R : ℝ) := by
    unfold sparseCoarseDenominator
    change Real.log (((A * R ^ 4 : ℕ) : ℝ)) = _
    push_cast
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
    norm_num
  rw [hlogden]
  dsimp only [R]
  field_simp [hxlog]

/-- The dimension quotient used in the all-cutoff construction tends to
infinity for every fixed positive coefficient. -/
theorem sparseAllCutoffQuotient_tendsto_atTop (D : ℕ) (hD : 0 < D) :
    Tendsto (sparseAllCutoffQuotient D) atTop atTop := by
  rw [tendsto_atTop]
  intro Q
  let C : ℕ := D * (Q + 1) ^ 2
  have hC : 0 < C := by dsimp [C]; positivity
  have hε : (0 : ℝ) < (C : ℝ)⁻¹ := inv_pos.mpr (by positivity)
  have hb := (sparseBinaryLogPow_isLittleO 4).bound hε
  filter_upwards [hb] with x hx
  let R := Nat.log 2 (x + 1) + 1
  have hR : 0 < R := by simp [R]
  have hxreal : (C : ℝ) * (R : ℝ) ^ 4 ≤ (x : ℝ) := by
    rw [Real.norm_of_nonneg (pow_nonneg (by positivity) 4),
      Real.norm_of_nonneg (by positivity)] at hx
    change (R : ℝ) ^ 4 ≤ (C : ℝ)⁻¹ * (x : ℝ) at hx
    calc
      (C : ℝ) * (R : ℝ) ^ 4 ≤
          (C : ℝ) * ((C : ℝ)⁻¹ * (x : ℝ)) := by gcongr
      _ = (x : ℝ) := by field_simp
  have hxnat : C * R ^ 4 ≤ x := by exact_mod_cast hxreal
  have hsmall : D * (Q * R ^ 2) ^ 2 ≤ x := by
    calc
      D * (Q * R ^ 2) ^ 2 = D * Q ^ 2 * R ^ 4 := by ring
      _ ≤ D * (Q + 1) ^ 2 * R ^ 4 := by gcongr <;> omega
      _ = C * R ^ 4 := by simp [C]
      _ ≤ x := hxnat
  have hsq : (Q * R ^ 2) ^ 2 ≤ x / D := by
    rw [Nat.le_div_iff_mul_le hD]
    simpa [mul_comm] using hsmall
  have hsqrt : Q * R ^ 2 ≤ Nat.sqrt (x / D) := Nat.le_sqrt'.2 hsq
  unfold sparseAllCutoffQuotient
  change Q ≤ Nat.sqrt (x / D) / R ^ 2
  rw [Nat.le_div_iff_mul_le (pow_pos hR 2)]
  exact hsqrt

/-- The elementary exponent `x/(2048 D log₂(x+1)^4)` tends to infinity. -/
theorem sparseCoarseExponent_tendsto_atTop (D : ℕ) (hD : 0 < D) :
    Tendsto (fun x => x / sparseCoarseDenominator D x) atTop atTop := by
  rw [tendsto_atTop]
  intro Q
  let C : ℕ := (Q + 1) * 2048 * D
  have hC : 0 < C := by dsimp [C]; positivity
  have hε : (0 : ℝ) < (C : ℝ)⁻¹ := inv_pos.mpr (by positivity)
  have hb := (sparseBinaryLogPow_isLittleO 4).bound hε
  filter_upwards [hb] with x hx
  let R := Nat.log 2 (x + 1) + 1
  have hxreal : (C : ℝ) * (R : ℝ) ^ 4 ≤ (x : ℝ) := by
    rw [Real.norm_of_nonneg (pow_nonneg (by positivity) 4),
      Real.norm_of_nonneg (by positivity)] at hx
    change (R : ℝ) ^ 4 ≤ (C : ℝ)⁻¹ * (x : ℝ) at hx
    calc
      (C : ℝ) * (R : ℝ) ^ 4 ≤
          (C : ℝ) * ((C : ℝ)⁻¹ * (x : ℝ)) := by gcongr
      _ = (x : ℝ) := by field_simp
  have hxnat : C * R ^ 4 ≤ x := by exact_mod_cast hxreal
  have hmul : Q * sparseCoarseDenominator D x ≤ x := by
    unfold sparseCoarseDenominator
    change Q * (2048 * D * R ^ 4) ≤ x
    calc
      Q * (2048 * D * R ^ 4) ≤ (Q + 1) * (2048 * D * R ^ 4) := by
        gcongr <;> omega
      _ = C * R ^ 4 := by simp [C]; ring
      _ ≤ x := hxnat
  rw [Nat.le_div_iff_mul_le]
  · exact hmul
  · unfold sparseCoarseDenominator
    positivity

/-- The logarithm of the coarse exponent is asymptotic to `log x`. -/
theorem sparseCoarseExponent_log_ratio_tendsto_one (D : ℕ) (hD : 0 < D) :
    Tendsto (fun x : ℕ =>
      Real.log (x / sparseCoarseDenominator D x : ℕ) / Real.log (x : ℝ))
      atTop (𝓝 1) := by
  let E : ℕ → ℕ := fun x => x / sparseCoarseDenominator D x
  let N : ℕ → ℕ := fun x => sparseCoarseDenominator D x
  have hlogx : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hconst : Tendsto (fun x : ℕ => Real.log 2 / Real.log (x : ℝ))
      atTop (𝓝 0) := hlogx.const_div_atTop _
  have hN := sparseCoarseDenominator_log_ratio_tendsto_zero D hD
  have herror : Tendsto (fun x : ℕ =>
      (Real.log 2 + Real.log (N x : ℝ)) / Real.log (x : ℝ))
      atTop (𝓝 0) := by
    convert hconst.add hN using 1 <;> simp [N, add_div]
  have hlower : Tendsto (fun x : ℕ =>
      1 - (Real.log 2 + Real.log (N x : ℝ)) / Real.log (x : ℝ))
      atTop (𝓝 1) := by
    convert tendsto_const_nhds.sub herror using 1 <;> norm_num
  apply hlower.squeeze' tendsto_const_nhds
  · have hEtop := sparseCoarseExponent_tendsto_atTop D hD
    filter_upwards [hEtop.eventually_ge_atTop 1, Ici_mem_atTop 2] with x hE hx
    have hNpos : 0 < N x := by
      dsimp [N]
      unfold sparseCoarseDenominator
      positivity
    have hxpos : (1 : ℝ) < (x : ℝ) := by exact_mod_cast hx
    have hxlog : 0 < Real.log (x : ℝ) := Real.log_pos hxpos
    have hE' : 1 ≤ E x := by simpa [E] using hE
    have hEpos : (0 : ℝ) < (E x : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hE')
    have hNxpos : (0 : ℝ) < (N x : ℝ) := by exact_mod_cast hNpos
    have hxlt : x < 2 * E x * N x := by
      have hmod := Nat.mod_lt x hNpos
      have heq := Nat.div_add_mod x (N x)
      change N x * E x + x % N x = x at heq
      have hfirst : x < N x * (E x + 1) := by
        calc
          x = N x * E x + x % N x := heq.symm
          _ < N x * E x + N x := Nat.add_lt_add_left hmod _
          _ = N x * (E x + 1) := by ring
      calc
        x < N x * (E x + 1) := hfirst
        _ ≤ N x * (2 * E x) := Nat.mul_le_mul_left _ (by omega)
        _ = 2 * E x * N x := by ring
    have hlogmul : Real.log (x : ℝ) ≤
        Real.log 2 + Real.log (E x : ℝ) + Real.log (N x : ℝ) := by
      have hrightpos : (0 : ℝ) < 2 * (E x : ℝ) * (N x : ℝ) :=
        mul_pos (mul_pos (by norm_num) hEpos) hNxpos
      have hcast : (x : ℝ) ≤ 2 * (E x : ℝ) * (N x : ℝ) := by
        exact_mod_cast (Nat.le_of_lt hxlt)
      have hmono := Real.strictMonoOn_log.monotoneOn
        (zero_lt_one.trans hxpos) hrightpos hcast
      rw [Real.log_mul (mul_ne_zero (by norm_num) hEpos.ne') hNxpos.ne',
        Real.log_mul (by norm_num) hEpos.ne'] at hmono
      linarith
    change 1 - (Real.log 2 + Real.log (N x : ℝ)) / Real.log (x : ℝ) ≤
      Real.log (E x : ℝ) / Real.log (x : ℝ)
    calc
      1 - (Real.log 2 + Real.log (N x : ℝ)) / Real.log (x : ℝ) =
          (Real.log (x : ℝ) - (Real.log 2 + Real.log (N x : ℝ))) /
            Real.log (x : ℝ) := by field_simp
      _ ≤ Real.log (E x : ℝ) / Real.log (x : ℝ) :=
        (div_le_div_iff_of_pos_right hxlog).2 (by linarith)
  · have hEtop := sparseCoarseExponent_tendsto_atTop D hD
    filter_upwards [hEtop.eventually_ge_atTop 1, Ici_mem_atTop 2] with x hE hx
    have hxpos : (1 : ℝ) < (x : ℝ) := by exact_mod_cast hx
    have hxlog : 0 < Real.log (x : ℝ) := Real.log_pos hxpos
    have hEx : E x ≤ x := Nat.div_le_self _ _
    have hEpos : (0 : ℝ) < (E x : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hE)
    have hlogle : Real.log (E x : ℝ) ≤ Real.log (x : ℝ) :=
      Real.strictMonoOn_log.monotoneOn hEpos
        (zero_lt_one.trans hxpos) (by exact_mod_cast hEx)
    change Real.log (E x : ℝ) / Real.log (x : ℝ) ≤ 1
    exact (div_le_iff₀ hxlog).2 (by simpa using hlogle)

/-- The iterated logarithm of the explicit power-of-two coarse lower function
has ratio one to `log x`. -/
theorem sparsePowerLower_loglog_ratio_tendsto_one (D : ℕ) (hD : 0 < D) :
    Tendsto (fun x : ℕ =>
      Real.log (Real.log ((2 ^ (x / sparseCoarseDenominator D x) : ℕ) : ℝ)) /
        Real.log (x : ℝ)) atTop (𝓝 1) := by
  let E : ℕ → ℕ := fun x => x / sparseCoarseDenominator D x
  have hEratio := sparseCoarseExponent_log_ratio_tendsto_one D hD
  have hlogx : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hc : Tendsto (fun x : ℕ =>
      Real.log (Real.log 2) / Real.log (x : ℝ)) atTop (𝓝 0) :=
    hlogx.const_div_atTop _
  have hsum : Tendsto (fun x : ℕ =>
      Real.log (E x : ℝ) / Real.log (x : ℝ) +
        Real.log (Real.log 2) / Real.log (x : ℝ)) atTop (𝓝 1) := by
    convert hEratio.add hc using 1 <;> norm_num [E]
  apply hsum.congr'
  have hEtop := sparseCoarseExponent_tendsto_atTop D hD
  filter_upwards [hEtop.eventually_ge_atTop 1, Ici_mem_atTop 2] with x hE hx
  have hE' : 0 < E x := by
    change 0 < x / sparseCoarseDenominator D x
    omega
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hxlog : Real.log (x : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hx)).ne'
  have hinner : Real.log ((2 ^ E x : ℕ) : ℝ) =
      (E x : ℝ) * Real.log 2 := by
    push_cast
    exact Real.log_pow 2 (E x)
  have houter : Real.log (Real.log ((2 ^ E x : ℕ) : ℝ)) =
      Real.log (E x : ℝ) + Real.log (Real.log 2) := by
    rw [hinner, Real.log_mul (by exact_mod_cast hE'.ne') hlog2.ne']
  rw [houter]
  dsimp only [E]
  field_simp [hxlog]

/-- Shifting a natural argument by a fixed real constant does not change its
logarithm at first order. -/
theorem log_add_nat_ratio_tendsto_one (c : ℝ) :
    Tendsto (fun x : ℕ => Real.log ((x : ℝ) + c) / Real.log (x : ℝ))
      atTop (𝓝 1) := by
  have hlogx : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hdiff : Tendsto (fun x : ℕ =>
      Real.log ((x : ℝ) + c) - Real.log (x : ℝ)) atTop (𝓝 0) :=
    (Real.tendsto_log_comp_add_sub_log c).comp tendsto_natCast_atTop_atTop
  have hzero := hdiff.div_atTop hlogx
  have hone : Tendsto (fun x : ℕ =>
      1 + (Real.log ((x : ℝ) + c) - Real.log (x : ℝ)) /
        Real.log (x : ℝ)) atTop (𝓝 1) := by
    convert tendsto_const_nhds.add hzero using 1 <;> norm_num
  apply hone.congr'
  filter_upwards [Ici_mem_atTop 2] with x hx
  have hxlog : Real.log (x : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hx)).ne'
  field_simp [hxlog]
  ring

/-- One further logarithm of a shifted natural logarithm is negligible
compared with `log x`. -/
theorem log_log_add_nat_ratio_tendsto_zero (c : ℝ) :
    Tendsto (fun x : ℕ =>
      Real.log (Real.log ((x : ℝ) + c)) / Real.log (x : ℝ))
      atTop (𝓝 0) := by
  have hshift : Tendsto (fun x : ℕ => (x : ℝ) + c) atTop atTop :=
    tendsto_atTop_add_const_right atTop c tendsto_natCast_atTop_atTop
  have hg : Tendsto (fun x : ℕ => Real.log ((x : ℝ) + c)) atTop atTop :=
    Real.tendsto_log_atTop.comp hshift
  have hsmall := (Real.isLittleO_log_id_atTop.comp_tendsto hg).tendsto_div_nhds_zero
  have hratio := log_add_nat_ratio_tendsto_one c
  have hprod := hsmall.mul hratio
  have hprod' : Tendsto (fun x : ℕ =>
      Real.log (Real.log ((x : ℝ) + c)) / Real.log (x : ℝ))
      atTop (𝓝 (0 * 1)) := by
    apply hprod.congr'
    filter_upwards [hg.eventually_gt_atTop 0, Ici_mem_atTop 2] with x hgpos hx
    have hxlog : Real.log (x : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast hx)).ne'
    simp only [Function.comp_apply, id_eq]
    field_simp [hgpos.ne', hxlog]
  simpa using hprod'

/-- The iterated logarithm of the elementary encoding upper function also has
ratio one to `log x`. -/
theorem elementaryUpper_loglog_ratio_tendsto_one :
    Tendsto (fun x : ℕ =>
      Real.log (Real.log (((x + 2) ^ (x + 1) : ℕ) : ℝ)) /
        Real.log (x : ℝ)) atTop (𝓝 1) := by
  have hfirst := log_add_nat_ratio_tendsto_one 1
  have hsecond := log_log_add_nat_ratio_tendsto_zero 2
  have hsum : Tendsto (fun x : ℕ =>
      Real.log ((x : ℝ) + 1) / Real.log (x : ℝ) +
        Real.log (Real.log ((x : ℝ) + 2)) / Real.log (x : ℝ))
      atTop (𝓝 1) := by
    convert hfirst.add hsecond using 1 <;> norm_num
  apply hsum.congr'
  filter_upwards [Ici_mem_atTop 2] with x hx
  have hbase : (0 : ℝ) < (x : ℝ) + 2 := by positivity
  have hexp : (0 : ℝ) < (x : ℝ) + 1 := by positivity
  have hlogbase : 0 < Real.log ((x : ℝ) + 2) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < x + 2))
  have hxlog : Real.log (x : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hx)).ne'
  have hinner : Real.log ((((x + 2) ^ (x + 1) : ℕ) : ℝ)) =
      ((x : ℝ) + 1) * Real.log ((x : ℝ) + 2) := by
    push_cast
    rw [Real.log_pow]
    push_cast
    ring
  have houter : Real.log (Real.log ((((x + 2) ^ (x + 1) : ℕ) : ℝ))) =
      Real.log ((x : ℝ) + 1) + Real.log (Real.log ((x : ℝ) + 2)) := by
    rw [hinner, Real.log_mul hexp.ne' hlogbase.ne']
  rw [houter]
  field_simp [hxlog]

/-- The asymptotic estimate obtained from any fixed coefficient large enough
for the sparse construction.  The conclusion is independent of that auxiliary
coefficient. -/
theorem erdos1188_loglog_ratio_tendsto_one_of_coefficient (D : ℕ)
    (hDlarge : sparseSeedProduct * (256 ^ 3 * 2048 * 2049) ≤ D) :
    Tendsto (fun x : ℕ =>
      Real.log (Real.log (coveringCount x : ℝ)) / Real.log (x : ℝ))
      atTop (𝓝 1) := by
  let E : ℕ → ℕ := fun x => x / sparseCoarseDenominator D x
  let P : ℕ → ℕ := fun x => 2 ^ E x
  let U : ℕ → ℕ := fun x => (x + 2) ^ (x + 1)
  have hD : 0 < D := by
    have hc : 0 < sparseSeedProduct * (256 ^ 3 * 2048 * 2049) :=
      Nat.mul_pos sparseSeedProduct_pos (by norm_num)
    omega
  have hlower := sparsePowerLower_loglog_ratio_tendsto_one D hD
  have hupper := elementaryUpper_loglog_ratio_tendsto_one
  apply hlower.squeeze' hupper
  · have hqtop := sparseAllCutoffQuotient_tendsto_atTop D hD
    have hEtop := sparseCoarseExponent_tendsto_atTop D hD
    filter_upwards [hqtop.eventually_ge_atTop (2 * (sparseSeed + 1)),
      hEtop.eventually_ge_atTop 1, Ici_mem_atTop 2] with x hq hE hx
    have hconstruct : P x ≤ coveringCount x := by
      dsimp [P, E]
      exact explicit_sparse_coarse_lower D x hDlarge hq
    have hPone : 1 < P x := by
      dsimp [P]
      have hE' : 1 ≤ E x := by simpa [E] using hE
      exact one_lt_pow₀ (by decide : (1 : ℕ) < 2) (Nat.ne_of_gt hE')
    have hPpos : (0 : ℝ) < (P x : ℝ) := by positivity
    have hCpos : (0 : ℝ) < (coveringCount x : ℝ) := by
      exact lt_of_lt_of_le hPpos (by exact_mod_cast hconstruct)
    have hlogPpos : 0 < Real.log (P x : ℝ) :=
      Real.log_pos (by exact_mod_cast hPone)
    have hlogCpos : 0 < Real.log (coveringCount x : ℝ) := by
      have hlogle := Real.strictMonoOn_log.monotoneOn hPpos hCpos
        (by exact_mod_cast hconstruct)
      exact lt_of_lt_of_le hlogPpos hlogle
    have hlogle := Real.strictMonoOn_log.monotoneOn hPpos hCpos
      (by exact_mod_cast hconstruct)
    have hloglogle := Real.strictMonoOn_log.monotoneOn hlogPpos hlogCpos hlogle
    have hxlog : 0 < Real.log (x : ℝ) :=
      Real.log_pos (by exact_mod_cast hx)
    change Real.log (Real.log (P x : ℝ)) / Real.log (x : ℝ) ≤
      Real.log (Real.log (coveringCount x : ℝ)) / Real.log (x : ℝ)
    exact (div_le_div_iff_of_pos_right hxlog).2 hloglogle
  · have hqtop := sparseAllCutoffQuotient_tendsto_atTop D hD
    have hEtop := sparseCoarseExponent_tendsto_atTop D hD
    filter_upwards [hqtop.eventually_ge_atTop (2 * (sparseSeed + 1)),
      hEtop.eventually_ge_atTop 1, Ici_mem_atTop 2] with x hq hE hx
    have hconstruct : P x ≤ coveringCount x := by
      dsimp [P, E]
      exact explicit_sparse_coarse_lower D x hDlarge hq
    have hupperCount : coveringCount x ≤ U x := by
      dsimp [U]
      exact coveringCount_le_elementary x
    have hPone : 1 < P x := by
      dsimp [P]
      have hE' : 1 ≤ E x := by simpa [E] using hE
      exact one_lt_pow₀ (by decide : (1 : ℕ) < 2) (Nat.ne_of_gt hE')
    have hCpos : (0 : ℝ) < (coveringCount x : ℝ) := by
      have hPpos : (0 : ℝ) < (P x : ℝ) := by positivity
      exact lt_of_lt_of_le hPpos (by exact_mod_cast hconstruct)
    have hUposNat : 0 < U x := by
      dsimp [U]
      exact pow_pos (by omega) _
    have hUpos : (0 : ℝ) < (U x : ℝ) := by exact_mod_cast hUposNat
    have hPoneR : (1 : ℝ) < (P x : ℝ) := by exact_mod_cast hPone
    have hconstructR : (P x : ℝ) ≤ (coveringCount x : ℝ) := by
      exact_mod_cast hconstruct
    have hCone : (1 : ℝ) < (coveringCount x : ℝ) :=
      hPoneR.trans_le hconstructR
    have hlogCpos : 0 < Real.log (coveringCount x : ℝ) := Real.log_pos hCone
    have hlogle := Real.strictMonoOn_log.monotoneOn hCpos hUpos
      (by exact_mod_cast hupperCount)
    have hlogUpos : 0 < Real.log (U x : ℝ) := lt_of_lt_of_le hlogCpos hlogle
    have hloglogle := Real.strictMonoOn_log.monotoneOn hlogCpos hlogUpos hlogle
    have hxlog : 0 < Real.log (x : ℝ) :=
      Real.log_pos (by exact_mod_cast hx)
    change Real.log (Real.log (coveringCount x : ℝ)) / Real.log (x : ℝ) ≤
      Real.log (Real.log (U x : ℝ)) / Real.log (x : ℝ)
    exact (div_le_div_iff_of_pos_right hxlog).2 hloglogle

/-- **Asymptotic estimate for Erdős Problem 1188.**  The double logarithm of
the number of minimal distinct covering systems has the same first-order
growth as the logarithm of the modulus cutoff:
`log(log F(x)) / log x → 1`. -/
theorem erdos1188_loglog_ratio_tendsto_one :
    Tendsto (fun x : ℕ =>
      Real.log (Real.log (coveringCount x : ℝ)) / Real.log (x : ℝ))
      atTop (𝓝 1) :=
  erdos1188_loglog_ratio_tendsto_one_of_coefficient
    (sparseSeedProduct * (256 ^ 3 * 2048 * 2049)) le_rfl

end Erdos1188
