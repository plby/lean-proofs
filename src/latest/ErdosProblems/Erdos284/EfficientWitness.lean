/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos284.HarmonicConstruction

/-!
# Efficient representations above a prescribed denominator

The pre-crossing harmonic block is completed by the short factorial
Egyptian expansion of its residual.  Positivity and the bound by `1/M`
force every correction denominator to be at least `M`, so no collision with
the harmonic block is possible.
-/

open Filter Finset
open scoped BigOperators Topology Real

namespace Erdos284

noncomputable section

attribute [local instance] Classical.propDecidable

/-- A convenient upper bound for the size of the constructed representation. -/
def constructionBound (N : ℕ) : ℕ :=
  harmonicEndpoint N - N + 2 * factorialCutoff (harmonicEndpoint N)

private theorem residual_den_dvd_initialLcm (N : ℕ) :
    (1 - UnitFractions.rec_sum
      (Ioc N (harmonicEndpoint N - 1))).den ∣
        Erdos285.PrimePowers.initialLcm (harmonicEndpoint N) := by
  let B := Ioc N (harmonicEndpoint N - 1)
  have hrec : (UnitFractions.rec_sum B).den ∣ B.lcm id :=
    Erdos285.PrimePowers.recSum_den_dvd_lcm B
  have hsub : (1 - UnitFractions.rec_sum B).den ∣
      (UnitFractions.rec_sum B).den := by
    have h := Rat.sub_den_dvd_lcm (1 : ℚ) (UnitFractions.rec_sum B)
    simpa only [Rat.den_one, Nat.lcm_one_left] using h
  have hBlcm : B.lcm id ∣
      Erdos285.PrimePowers.initialLcm (harmonicEndpoint N) := by
    apply Finset.lcm_dvd
    intro d hd
    apply Finset.dvd_lcm
    rw [Finset.mem_Icc]
    have hdI := Finset.mem_Ioc.mp hd
    constructor
    · omega
    · omega
  exact hsub.trans (hrec.trans hBlcm)

private theorem residual_pos (N : ℕ) :
    0 < 1 - UnitFractions.rec_sum
      (Ioc N (harmonicEndpoint N - 1)) := by
  linarith [harmonicEndpoint_prefix_lt N]

private theorem residual_le_inv_endpoint (N : ℕ) :
    1 - UnitFractions.rec_sum
        (Ioc N (harmonicEndpoint N - 1)) ≤
      1 / (harmonicEndpoint N : ℚ) := by
  have hgt := harmonicEndpoint_gt N
  have hsplit : Ioc N (harmonicEndpoint N) =
      insert (harmonicEndpoint N) (Ioc N (harmonicEndpoint N - 1)) := by
    ext x
    simp only [Finset.mem_Ioc, Finset.mem_insert]
    omega
  have hcross := harmonicEndpoint_spec N
  rw [hsplit, UnitFractions.rec_sum, Finset.sum_insert] at hcross
  · change 1 ≤ (1 : ℚ) / harmonicEndpoint N +
      UnitFractions.rec_sum (Ioc N (harmonicEndpoint N - 1)) at hcross
    linarith
  · simp [Finset.mem_Ioc]
    omega

/-- Eventually there is a representation of one above `N` with at most
`constructionBound N` summands. -/
theorem eventually_exists_efficient_representation :
    ∀ᶠ N : ℕ in atTop, ∃ A : Finset ℕ,
      0 ∉ A ∧ UnitFractions.rec_sum A = 1 ∧
      (∀ d ∈ A, N < d) ∧ A.card ≤ constructionBound N := by
  have hfac :=
    harmonicEndpoint_tendsto_atTop.eventually
      eventually_initialLcm_le_factorialCutoff_factorial
  filter_upwards [hfac, eventually_ge_atTop 1] with N hfacN hN
  let M := harmonicEndpoint N
  let B := Ioc N (M - 1)
  let ρ : ℚ := 1 - UnitFractions.rec_sum B
  have hNM : N < M := harmonicEndpoint_gt N
  have hρpos : 0 < ρ := by
    simpa [ρ, B, M] using residual_pos N
  have hρle : ρ ≤ 1 / (M : ℚ) := by
    simpa [ρ, B, M] using residual_le_inv_endpoint N
  have hMtwo : 2 ≤ M := by omega
  have hρone : ρ < 1 := by
    have hMinv : (1 : ℚ) / M < 1 := by
      rw [div_lt_one (by exact_mod_cast (by omega : 0 < M))]
      exact_mod_cast hMtwo
    exact hρle.trans_lt hMinv
  let a : ℕ := ρ.num.natAbs
  let q : ℕ := ρ.den
  have hqpos : 0 < q := ρ.den_pos
  have hanum : (a : ℤ) = ρ.num := by
    simpa [a] using Int.natAbs_of_nonneg (Rat.num_nonneg.mpr hρpos.le)
  have hρeq : ρ = (a : ℚ) / q := by
    rw [show ρ = (ρ.num : ℚ) / ρ.den from (Rat.num_div_den ρ).symm]
    congr 2
    exact_mod_cast hanum.symm
  have hapos : 0 < a := by
    have : 0 < ρ.num := Rat.num_pos.mpr hρpos
    simpa [a, Int.natAbs_pos] using this.ne'
  have haq : a < q := by
    have hrat : (a : ℚ) / q < 1 := by simpa [← hρeq] using hρone
    rw [div_lt_one (by exact_mod_cast hqpos)] at hrat
    exact_mod_cast hrat
  have hqfac : q ≤ (factorialCutoff M).factorial := by
    have hqdvd : q ∣ Erdos285.PrimePowers.initialLcm M := by
      simpa [q, ρ, B, M] using residual_den_dvd_initialLcm N
    have hLpos : 0 < Erdos285.PrimePowers.initialLcm M :=
      Nat.lcmUpto_pos M
    exact (Nat.le_of_dvd hLpos hqdvd).trans hfacN
  obtain ⟨E, hEzero, hEsum, hEcard⟩ :=
    exists_short_egyptian_of_le_factorial hapos haq hqfac
  have hEsumρ : UnitFractions.rec_sum E = ρ := hEsum.trans hρeq.symm
  have hElarge : ∀ d ∈ E, M ≤ d := by
    intro d hd
    have hdpos : 0 < d := Nat.pos_of_ne_zero fun hd0 ↦ hEzero (hd0 ▸ hd)
    have hterm : (1 : ℚ) / d ≤ UnitFractions.rec_sum E := by
      rw [UnitFractions.rec_sum]
      exact Finset.single_le_sum
        (fun i _ ↦ by positivity : ∀ i ∈ E, (0 : ℚ) ≤ 1 / i) hd
    have hinv : (1 : ℚ) / d ≤ 1 / M :=
      hterm.trans (hEsumρ.trans_le hρle)
    exact_mod_cast le_of_one_div_le_one_div (by exact_mod_cast hdpos) hinv
  have hBE : Disjoint B E := by
    rw [Finset.disjoint_left]
    intro d hdB hdE
    have hdBI := Finset.mem_Ioc.mp hdB
    have hdM := hElarge d hdE
    omega
  refine ⟨B ∪ E, ?_, ?_, ?_, ?_⟩
  · intro hz
    rw [Finset.mem_union] at hz
    rcases hz with hz | hz
    · have := (Finset.mem_Ioc.mp hz).1
      omega
    · exact hEzero hz
  · rw [UnitFractions.rec_sum_disjoint hBE, hEsumρ]
    simp [ρ]
  · intro d hd
    rw [Finset.mem_union] at hd
    rcases hd with hd | hd
    · exact (Finset.mem_Ioc.mp hd).1
    · exact hNM.trans_le (hElarge d hd)
  · rw [Finset.card_union_of_disjoint hBE]
    have hBcard : B.card = M - 1 - N := by simp [B]
    rw [hBcard]
    unfold constructionBound
    dsimp [M] at hEcard ⊢
    omega

theorem constructionBound_ratio_tendsto :
    Tendsto (fun N : ℕ ↦ (constructionBound N : ℝ) / (N : ℝ))
      atTop (nhds (Real.exp 1 - 1)) := by
  have hMratio := harmonicEndpoint_ratio_tendsto
  have hMtop := harmonicEndpoint_tendsto_atTop
  have hcutM := factorialCutoff_ratio_tendsto_zero.comp hMtop
  have hcorr : Tendsto
      (fun N : ℕ ↦
        (factorialCutoff (harmonicEndpoint N) : ℝ) / (N : ℝ))
      atTop (nhds 0) := by
    have hprod := hcutM.mul hMratio
    convert hprod using 1
    · funext N
      by_cases hN : N = 0
      · simp [hN]
      have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN
      have hM0 : (harmonicEndpoint N : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt (harmonicEndpoint_gt N)))
      simp only [Function.comp_apply]
      field_simp
    · norm_num
  have hgap : Tendsto
      (fun N : ℕ ↦ ((harmonicEndpoint N - N : ℕ) : ℝ) / (N : ℝ))
      atTop (nhds (Real.exp 1 - 1)) := by
    have hone : Tendsto (fun _N : ℕ ↦ (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    have hsub := hMratio.sub hone
    have heq :
        (fun N : ℕ ↦ (harmonicEndpoint N : ℝ) / (N : ℝ) - 1) =ᶠ[atTop]
          (fun N : ℕ ↦ ((harmonicEndpoint N - N : ℕ) : ℝ) / (N : ℝ)) := by
      filter_upwards [eventually_ge_atTop 1] with N hN
      rw [Nat.cast_sub (harmonicEndpoint_gt N).le]
      field_simp
    simpa using hsub.congr' heq
  have htotal := hgap.add (hcorr.const_mul 2)
  convert htotal using 1
  · funext N
    by_cases hN : N = 0
    · simp [hN, constructionBound]
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN
    simp only [constructionBound, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    field_simp
  · norm_num

end

end Erdos284

#print axioms Erdos284.eventually_exists_efficient_representation
#print axioms Erdos284.constructionBound_ratio_tendsto
