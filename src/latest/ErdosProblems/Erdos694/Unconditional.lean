import ErdosProblems.Erdos694.Height

/-!
# The unconditional lower bound

Invert the height `exp (8*k^(D+1))` using a floored real root. For each
fixed `D`, the resulting coefficient is `exp(γ)*D/(D+1)`. Since `D` can
be arbitrarily large, this yields the full constant `exp(γ)`.
-/

namespace Erdos694

open Filter Topology Asymptotics

noncomputable def heightRoot (d x : ℕ) : ℝ :=
  (Real.log (x : ℝ) / 8) ^ (d : ℝ)⁻¹

noncomputable def heightIndex (d x : ℕ) : ℕ := ⌊heightRoot d x⌋₊

lemma heightRoot_tendsto (d : ℕ) (hd : 0 < d) :
    Tendsto (heightRoot d) atTop atTop := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  exact (tendsto_rpow_atTop (inv_pos.mpr hdR)).comp
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).atTop_div_const
      (by norm_num : (0 : ℝ) < 8))

lemma heightIndex_tendsto (d : ℕ) (hd : 0 < d) :
    Tendsto (heightIndex d) atTop atTop :=
  tendsto_nat_floor_atTop.comp (heightRoot_tendsto d hd)

lemma heightIndex_bound (d : ℕ) (hd : 0 < d) (x : ℕ) (hx : 2 ≤ x) :
    Real.exp (8 * (heightIndex d x : ℝ) ^ d) ≤ x := by
  have hxR : (1 : ℝ) < x := by exact_mod_cast (show 1 < x by omega)
  have hlog : 0 ≤ Real.log (x : ℝ) / 8 := by positivity [Real.log_pos hxR]
  have hfloor : (heightIndex d x : ℝ) ≤ heightRoot d x :=
    Nat.floor_le (Real.rpow_nonneg hlog _)
  have hpow : (heightRoot d x) ^ d = Real.log (x : ℝ) / 8 :=
    Real.rpow_inv_natCast_pow hlog hd.ne'
  calc
    Real.exp (8 * (heightIndex d x : ℝ) ^ d) ≤
        Real.exp (8 * (heightRoot d x) ^ d) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (Nat.cast_nonneg _) hfloor d) (by norm_num)
    _ = x := by
      rw [hpow, mul_div_cancel₀ _ (by norm_num : (8 : ℝ) ≠ 0)]
      exact Real.exp_log (zero_lt_one.trans hxR)

lemma loglog_nat_tendsto :
    Tendsto (fun x : ℕ => Real.log (Real.log (x : ℝ))) atTop atTop :=
  Real.tendsto_log_atTop.comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

lemma log_heightIndex_tendsto (d : ℕ) (hd : 0 < d) :
    Tendsto (fun x : ℕ => Real.log (heightIndex d x : ℝ) /
      Real.log (Real.log (x : ℝ))) atTop (𝓝 (d : ℝ)⁻¹) := by
  have ht := heightRoot_tendsto d hd
  have hf := (Asymptotics.isEquivalent_nat_floor (R := ℝ)).comp_tendsto ht
  have hflog := hf.log ht
  have hlogt := Real.tendsto_log_atTop.comp ht
  have hfloor : Tendsto (fun x : ℕ =>
      Real.log (heightIndex d x : ℝ) / Real.log (heightRoot d x)) atTop (𝓝 1) :=
    (Asymptotics.isEquivalent_iff_tendsto_one (hlogt.eventually_ne_atTop 0)).mp hflog
  have hconst : Tendsto (fun x : ℕ => Real.log 8 / Real.log (Real.log (x : ℝ)))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop loglog_nat_tendsto
  have hroot : Tendsto (fun x : ℕ => Real.log (heightRoot d x) /
      Real.log (Real.log (x : ℝ))) atTop (𝓝 (d : ℝ)⁻¹) := by
    have h := ((tendsto_const_nhds (x := (1 : ℝ))).sub hconst).const_mul (d : ℝ)⁻¹
    simp only [sub_zero, mul_one] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop 2, loglog_nat_tendsto.eventually_ne_atTop 0]
      with x hx hll
    have hlog : 0 < Real.log (x : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < x by omega))
    rw [heightRoot, Real.log_rpow (by positivity), Real.log_div hlog.ne' (by norm_num)]
    field_simp
  have h := hfloor.mul hroot
  simp only [one_mul] at h
  apply h.congr'
  filter_upwards [hlogt.eventually_ne_atTop 0] with x hx
  exact div_mul_div_cancel₀ hx

lemma rescaled_dyadicRatio_tendsto (D : ℕ) (hD : 0 < D) :
    Tendsto (fun x : ℕ => dyadicRatio D (heightIndex (D + 1) x) /
      Real.log (Real.log (x : ℝ))) atTop
      (𝓝 (Real.exp Real.eulerMascheroniConstant * D / (D + 1 : ℕ))) := by
  have hi := heightIndex_tendsto (D + 1) (Nat.succ_pos D)
  have h := ((dyadicRatio_tendsto D hD).comp hi).mul
    (log_heightIndex_tendsto (D + 1) (Nat.succ_pos D))
  simp only [← div_eq_mul_inv] at h
  apply h.congr'
  filter_upwards [hi.eventually_ge_atTop 2] with x hx
  have hlog : Real.log (heightIndex (D + 1) x : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < heightIndex (D + 1) x by omega))).ne'
  exact div_mul_div_cancel₀ hlog

theorem unconditional_totient_collision_construction :
    ∀ ε > 0, ∀ᶠ x : ℕ in atTop,
      ∃ a b n : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ 1 ≤ n ∧ n ≤ x ∧
        Nat.totient a = n ∧ Nat.totient b = n ∧
        (b : ℝ) / a ≥ (Real.exp Real.eulerMascheroniConstant - ε) *
          Real.log (Real.log x) := by
  intro ε hε
  let γ := Real.exp Real.eulerMascheroniConstant
  obtain ⟨D, hD⟩ := exists_nat_gt (max (γ / ε) 1)
  have hD1 : (1 : ℝ) < D := (le_max_right _ _).trans_lt hD
  have hDpos : 0 < D := by exact_mod_cast (zero_lt_one.trans hD1)
  have hgap : γ - ε < γ * D / (D + 1 : ℕ) := by
    have hbound : γ / ε < D := (le_max_left _ _).trans_lt hD
    have hmul : γ < (D : ℝ) * ε := (div_lt_iff₀ hε).mp hbound
    apply (lt_div_iff₀ (by positivity : (0 : ℝ) < (D + 1 : ℕ))).mpr
    push_cast
    nlinarith
  have hratio := (rescaled_dyadicRatio_tendsto D hDpos).eventually (lt_mem_nhds hgap)
  have hi := heightIndex_tendsto (D + 1) (Nat.succ_pos D)
  filter_upwards [hi.eventually (dyadic_collision_height D), hratio,
    eventually_ge_atTop 2, loglog_nat_tendsto.eventually_gt_atTop 0]
    with x hx hratio hx2 hll
  obtain ⟨a, b, n, ha, hb, hn, hφa, hφb, hba, hsize⟩ := hx
  have hnx : n ≤ x := by
    exact_mod_cast hsize.trans (heightIndex_bound (D + 1) (Nat.succ_pos D) x hx2)
  refine ⟨a, b, n, ha, hb, hn, hnx, hφa, hφb, ?_⟩
  exact ((le_div_iff₀ hll).mp hratio.le).trans hba

end Erdos694

#print axioms Erdos694.unconditional_totient_collision_construction
