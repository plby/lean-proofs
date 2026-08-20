import ErdosProblems.Erdos783.PrimeGridMoment

open MeasureTheory Set Finset Filter
open scoped BigOperators Topology

namespace Erdos783

noncomputable section

def logarithmicEndpoint (N y : ℕ) : ℝ :=
  Real.log N / Real.log y

def exactGridStep (N y K : ℕ) : ℝ :=
  (logarithmicEndpoint N y - 1) / K

lemma gsGridPoint_exactGridStep
    {N y K : ℕ} (hK : 0 < K) :
    gsGridPoint (exactGridStep N y K) K = logarithmicEndpoint N y := by
  unfold gsGridPoint exactGridStep
  have hKR : (K : ℝ) ≠ 0 := by exact_mod_cast hK.ne'
  field_simp [hKR]
  ring

lemma exactGridStep_pos
    {N y K : ℕ} (hK : 0 < K) (hu : 1 < logarithmicEndpoint N y) :
    0 < exactGridStep N y K := by
  unfold exactGridStep
  positivity

lemma floor_rpow_logarithmicEndpoint
    {N y : ℕ} (hy : 2 ≤ y) (hN : 0 < N) :
    ⌊(y : ℝ) ^ logarithmicEndpoint N y⌋₊ = N := by
  have hyPos : (0 : ℝ) < y := by positivity
  have hyNe : (y : ℝ) ≠ 1 := by
    exact_mod_cast (show y ≠ 1 by omega)
  have hNPos : (0 : ℝ) < N := by exact_mod_cast hN
  unfold logarithmicEndpoint
  change ⌊(y : ℝ) ^ Real.logb (y : ℝ) (N : ℝ)⌋₊ = N
  rw [Real.rpow_logb hyPos hyNe hNPos]
  exact Nat.floor_natCast N

lemma packetGrid_cover_exactGrid
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {N y K : ℕ} (hy : 2 ≤ y) (hN : 0 < N) (hK : 0 < K)
    (hyN : y < N)
    (hhigh : ∀ p ∈ P, y < p)
    (hendpoint : ∀ p ∈ P, p ≤ N) :
    ∀ p ∈ P, ∃ i < K, p ∈ packetExponentCell P y
      (gsGridPoint (exactGridStep N y K) i)
      (gsGridPoint (exactGridStep N y K) (i + 1)) := by
  have hu : 1 < logarithmicEndpoint N y := by
    have hyR : (0 : ℝ) < y := by positivity
    have hlogy : 0 < Real.log (y : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < y by omega))
    unfold logarithmicEndpoint
    rw [lt_div_iff₀ hlogy]
    have hyMem : (y : ℝ) ∈ Set.Ioi 0 := by
      change (0 : ℝ) < y
      exact_mod_cast (show 0 < y by omega)
    have hNMem : (N : ℝ) ∈ Set.Ioi 0 := by
      change (0 : ℝ) < N
      exact_mod_cast hN
    simpa using Real.strictMonoOn_log hyMem hNMem (by exact_mod_cast hyN)
  have hh := (exactGridStep_pos hK hu).le
  apply packetGrid_cover_of_bounds hP (show 1 ≤ y by omega) hh
  · intro p hp
    simpa [gsGridPoint] using hhigh p hp
  · intro p hp
    rw [gsGridPoint_exactGridStep hK,
      floor_rpow_logarithmicEndpoint hy hN]
    exact hendpoint p hp

theorem tendsto_logarithmicEndpoint_powerCutoff
    {b : ℝ} (hb : 0 < b) :
    Tendsto
      (fun N : ℕ ↦ logarithmicEndpoint N (powerCutoff b N))
      atTop (nhds b⁻¹) := by
  have hratio := tendsto_log_powerCutoff_div_log hb
  have hinv := hratio.inv₀ hb.ne'
  simpa only [logarithmicEndpoint, inv_div] using hinv

lemma logarithmicEndpoint_gt_one
    {N y : ℕ} (hy : 2 ≤ y) (hyN : y < N) :
    1 < logarithmicEndpoint N y := by
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  unfold logarithmicEndpoint
  rw [lt_div_iff₀ hlogy]
  have hyMem : (y : ℝ) ∈ Set.Ioi 0 := by
    change (0 : ℝ) < y
    positivity
  have hNMem : (N : ℝ) ∈ Set.Ioi 0 := by
    change (0 : ℝ) < N
    exact_mod_cast (show 0 < N by omega)
  simpa using Real.strictMonoOn_log hyMem hNMem (by exact_mod_cast hyN)

lemma lt_of_logarithmicEndpoint_gt_one
    {N y : ℕ} (hy : 2 ≤ y) (hN : 0 < N)
    (hu : 1 < logarithmicEndpoint N y) :
    y < N := by
  by_contra hnot
  have hNy : N ≤ y := Nat.le_of_not_gt hnot
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hlogNle : Real.log (N : ℝ) ≤ Real.log (y : ℝ) :=
    Real.log_le_log hNpos (by exact_mod_cast hNy)
  have : logarithmicEndpoint N y ≤ 1 := by
    unfold logarithmicEndpoint
    exact (div_le_one hlogy).mpr hlogNle
  linarith

lemma atomMass_scaled_reciprocal
    (P : Finset ℕ) (lambda : ℝ) :
    atomMass P (fun p : ℕ ↦ lambda * (p : ℝ)⁻¹) =
      lambda * reciprocalMass P := by
  unfold atomMass reciprocalMass
  rw [Finset.mul_sum]

lemma gsGridCellLog_ge_of_bounds
    {h hmin U : ℝ} (hhmin : 0 < hmin) (hh : hmin ≤ h)
    (hU : 0 < U) {K i : ℕ} (hi : i < K)
    (hend : gsGridPoint h K ≤ U) :
    Real.log (1 + hmin / U) ≤
      Real.log (gsGridPoint h (i + 1) / gsGridPoint h i) := by
  have hh0 : 0 ≤ h := hhmin.le.trans hh
  have hxi : 0 < gsGridPoint h i := gsGridPoint_pos hh0 i
  have hiK : i ≤ K := hi.le
  have hxiU : gsGridPoint h i ≤ U :=
    (gsGridPoint_mono hh0 hiK).trans hend
  have hdiv1 : hmin / U ≤ hmin / gsGridPoint h i :=
    div_le_div_of_nonneg_left hhmin.le hxi hxiU
  have hdiv2 : hmin / gsGridPoint h i ≤ h / gsGridPoint h i :=
    div_le_div_of_nonneg_right hh hxi.le
  have hratio :
      gsGridPoint h (i + 1) / gsGridPoint h i =
        1 + h / gsGridPoint h i := by
    rw [gsGridPoint_succ]
    field_simp [hxi.ne']
  have hlowerPos : 0 < 1 + hmin / U := by positivity
  apply Real.log_le_log hlowerPos
  rw [hratio]
  linarith

lemma packetGridCoefficient_le_one_of_close
    {lambda h error ell : ℝ}
    (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    (hh : 0 < h) (herror : 0 ≤ error)
    {P : Finset ℕ} {y i : ℕ}
    (hclose : ∀ a b : ℝ, 1 ≤ a → a ≤ b →
      |primeExponentCellMass y a b - (Real.log b - Real.log a)| < error)
    (hell : ell ≤
      Real.log (gsGridPoint h (i + 1) / gsGridPoint h i))
    (herrorle : error ≤ (1 - lambda) * ell) :
    packetGridCoefficient lambda P y h i ≤ 1 := by
  have ha1 : 1 ≤ gsGridPoint h i := by
    unfold gsGridPoint
    have : 0 ≤ (i : ℝ) * h := mul_nonneg (by positivity) hh.le
    linarith
  have hab : gsGridPoint h i ≤ gsGridPoint h (i + 1) :=
    (gsGridPoint_lt_succ hh i).le
  have hraw := hclose (gsGridPoint h i) (gsGridPoint h (i + 1)) ha1 hab
  have hmassSub :
      primeExponentCellMass y (gsGridPoint h i) (gsGridPoint h (i + 1)) -
          (Real.log (gsGridPoint h (i + 1)) - Real.log (gsGridPoint h i)) ≤
        error := (le_abs_self _).trans (le_of_lt hraw)
  have haPos := gsGridPoint_pos hh.le i
  have hbPos := gsGridPoint_pos hh.le (i + 1)
  have hlogEq :
      Real.log (gsGridPoint h (i + 1)) - Real.log (gsGridPoint h i) =
        Real.log (gsGridPoint h (i + 1) / gsGridPoint h i) := by
    rw [Real.log_div hbPos.ne' haPos.ne']
  have hmass :
      primeExponentCellMass y (gsGridPoint h i) (gsGridPoint h (i + 1)) ≤
        Real.log (gsGridPoint h (i + 1) / gsGridPoint h i) + error := by
    rw [← hlogEq]
    linarith
  have hone : 0 ≤ 1 - lambda := sub_nonneg.mpr hlambda1
  have herrorLog : error ≤
      (1 - lambda) *
        Real.log (gsGridPoint h (i + 1) / gsGridPoint h i) :=
    herrorle.trans (mul_le_mul_of_nonneg_left hell hone)
  have hlambdaError : lambda * error ≤ error :=
    mul_le_of_le_one_left herror hlambda1
  apply packetGridCoefficient_le_one hlambda0 hh hmass
  calc
    lambda *
        (Real.log (gsGridPoint h (i + 1) / gsGridPoint h i) + error) =
        lambda * Real.log (gsGridPoint h (i + 1) / gsGridPoint h i) +
          lambda * error := by ring
    _ ≤ lambda * Real.log (gsGridPoint h (i + 1) / gsGridPoint h i) +
          error := add_le_add_right hlambdaError _
    _ ≤ lambda * Real.log (gsGridPoint h (i + 1) / gsGridPoint h i) +
          (1 - lambda) *
            Real.log (gsGridPoint h (i + 1) / gsGridPoint h i) :=
      add_le_add_right herrorLog _
    _ = Real.log (gsGridPoint h (i + 1) / gsGridPoint h i) := by ring

lemma exists_damping_parameter
    {C M eta : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M) (heta : 0 < eta)
    (r : ℕ) :
    ∃ lambda : ℝ,
      0 < lambda ∧ lambda < 1 ∧
      ((r + 1 : ℕ) : ℝ) *
          ((r : ℝ) * (1 - lambda) * M ^ r) < eta ∧
      ∀ m ∈ Set.Icc (0 : ℝ) C,
        dickmanRho (Real.exp m) - eta <
          dickmanRho (Real.exp (lambda * m)) := by
  let f : ℝ → ℝ := fun x ↦ dickmanRho (Real.exp x)
  have hf : ContinuousOn f (Set.Icc (0 : ℝ) C) := by
    apply continuousOn_dickmanRho_Ici_zero.comp
      Real.continuous_exp.continuousOn
    intro x hx
    exact Set.mem_Ici.mpr (Real.exp_pos x).le
  have huc : UniformContinuousOn f (Set.Icc (0 : ℝ) C) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hf
  obtain ⟨delta, hdelta, hcontrol⟩ :=
    (Metric.uniformContinuousOn_iff.mp huc) eta heta
  let A : ℝ := ((r + 1 : ℕ) : ℝ) * (r : ℝ) * M ^ r
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  obtain ⟨k, hk⟩ := exists_nat_gt (max (C / delta) (max (A / eta) 1))
  have hkC : C / delta < (k : ℝ) :=
    (le_max_left (C / delta) (max (A / eta) 1)).trans_lt hk
  have hkA : A / eta < (k : ℝ) := by
    exact (le_max_left (A / eta) 1 |>.trans
      (le_max_right (C / delta) (max (A / eta) 1))).trans_lt hk
  have hk1 : (1 : ℝ) < k :=
    (le_max_right (A / eta) 1 |>.trans
      (le_max_right (C / delta) (max (A / eta) 1))).trans_lt hk
  let d : ℝ := (k + 1 : ℕ)
  have hd : 1 < d := by
    dsimp only [d]
    push_cast
    linarith
  have hd0 : 0 < d := zero_lt_one.trans hd
  have hCdelta : C / d < delta := by
    rw [div_lt_iff₀ hd0]
    have hCk : C < (k : ℝ) * delta := (div_lt_iff₀ hdelta).mp hkC
    dsimp only [d]
    push_cast
    nlinarith
  have hAeta : A / d < eta := by
    rw [div_lt_iff₀ hd0]
    have hAk : A < (k : ℝ) * eta := (div_lt_iff₀ heta).mp hkA
    dsimp only [d]
    push_cast
    nlinarith
  let lambda : ℝ := 1 - 1 / d
  have hlambda0 : 0 < lambda := by
    dsimp only [lambda]
    rw [sub_pos, div_lt_one hd0]
    exact hd
  have hlambda1 : lambda < 1 := by
    dsimp only [lambda]
    have : 0 < 1 / d := by positivity
    linarith
  refine ⟨lambda, hlambda0, hlambda1, ?_, ?_⟩
  · have hone : 1 - lambda = 1 / d := by
      dsimp only [lambda]
      ring
    rw [hone]
    dsimp only [A] at hAeta ⊢
    convert hAeta using 1 <;> field_simp <;> ring
  · intro m hm
    have hlambda0' : 0 ≤ lambda := hlambda0.le
    have hlambda1' : lambda ≤ 1 := hlambda1.le
    have hlm0 : 0 ≤ lambda * m := mul_nonneg hlambda0' hm.1
    have hlmC : lambda * m ≤ C := by
      exact (mul_le_of_le_one_left hm.1 hlambda1').trans hm.2
    have hdist : dist (lambda * m) m < delta := by
      rw [Real.dist_eq]
      have hone : 1 - lambda = 1 / d := by
        dsimp only [lambda]
        ring
      have hmdiv : m / d ≤ C / d :=
        div_le_div_of_nonneg_right hm.2 hd0.le
      rw [show lambda * m - m = -(m / d) by
        dsimp only [lambda]
        field_simp [hd0.ne']
        ring,
        abs_neg, abs_of_nonneg (div_nonneg hm.1 hd0.le)]
      exact hmdiv.trans_lt hCdelta
    have hfclose := hcontrol (lambda * m) ⟨hlm0, hlmC⟩ m hm hdist
    dsimp only [f] at hfclose
    rw [Real.dist_eq] at hfclose
    linarith [neg_lt_of_abs_lt hfclose]

def highGridUpperEndpoint (b : ℝ) : ℝ := b⁻¹ + 1

def highGridLowerEndpoint (b : ℝ) : ℝ := (1 + b⁻¹) / 2

def highGridUpperStep (b : ℝ) (K : ℕ) : ℝ :=
  (highGridUpperEndpoint b - 1) / K

def highGridLowerStep (b : ℝ) (K : ℕ) : ℝ :=
  (highGridLowerEndpoint b - 1) / K

def highGridLogWidth (b : ℝ) (K : ℕ) : ℝ :=
  Real.log (1 + highGridLowerStep b K / highGridUpperEndpoint b)

def highGridMertensAllowance (b lambda : ℝ) (K : ℕ) : ℝ :=
  (1 - lambda) * highGridLogWidth b K / 2

def highGridFixedTransferError
    (b lambda M : ℝ) (r K : ℕ) : ℝ :=
  ((r + 1 : ℕ) : ℝ) *
    ((r : ℝ) *
      (((r + 1 : ℕ) : ℝ) * highGridUpperStep b K +
        highGridMertensAllowance b lambda K) * M ^ r)

theorem tendsto_highGridUpperStep (b : ℝ) :
    Tendsto (highGridUpperStep b) atTop (nhds 0) := by
  change Tendsto
    (fun K : ℕ ↦ (highGridUpperEndpoint b - 1) / (K : ℝ))
    atTop (nhds 0)
  exact tendsto_const_div_atTop_nhds_zero_nat (highGridUpperEndpoint b - 1)

theorem tendsto_highGridLowerStep (b : ℝ) :
    Tendsto (highGridLowerStep b) atTop (nhds 0) := by
  change Tendsto
    (fun K : ℕ ↦ (highGridLowerEndpoint b - 1) / (K : ℝ))
    atTop (nhds 0)
  exact tendsto_const_div_atTop_nhds_zero_nat (highGridLowerEndpoint b - 1)

theorem tendsto_highGridLogWidth (b : ℝ) (hU : highGridUpperEndpoint b ≠ 0) :
    Tendsto (highGridLogWidth b) atTop (nhds 0) := by
  have harg : Tendsto
      (fun K : ℕ ↦ 1 + highGridLowerStep b K / highGridUpperEndpoint b)
      atTop (nhds (1 + 0 / highGridUpperEndpoint b)) :=
    tendsto_const_nhds.add ((tendsto_highGridLowerStep b).div_const _)
  have harg' : Tendsto
      (fun K : ℕ ↦ 1 + highGridLowerStep b K / highGridUpperEndpoint b)
      atTop (nhds 1) := by simpa using harg
  have hlog := (Real.continuousAt_log one_ne_zero).tendsto.comp harg'
  change Tendsto
    (fun K : ℕ ↦ Real.log
      (1 + highGridLowerStep b K / highGridUpperEndpoint b))
    atTop (nhds 0)
  simpa [Function.comp_def] using hlog

theorem tendsto_highGridMertensAllowance
    (b lambda : ℝ) (hU : highGridUpperEndpoint b ≠ 0) :
    Tendsto (highGridMertensAllowance b lambda) atTop (nhds 0) := by
  have hc : Tendsto (fun _ : ℕ ↦ 1 - lambda) atTop (nhds (1 - lambda)) :=
    tendsto_const_nhds
  have h := hc.mul (tendsto_highGridLogWidth b hU)
  have h' := h.div_const (2 : ℝ)
  change Tendsto
    (fun K : ℕ ↦ (1 - lambda) * highGridLogWidth b K / 2)
    atTop (nhds 0)
  simpa [mul_assoc] using h'

theorem tendsto_highGridFixedTransferError
    (b lambda M : ℝ) (r : ℕ)
    (hU : highGridUpperEndpoint b ≠ 0) :
    Tendsto (highGridFixedTransferError b lambda M r) atTop (nhds 0) := by
  have hr1 : Tendsto (fun _ : ℕ ↦ ((r + 1 : ℕ) : ℝ)) atTop
      (nhds ((r + 1 : ℕ) : ℝ)) := tendsto_const_nhds
  have hr : Tendsto (fun _ : ℕ ↦ (r : ℝ)) atTop (nhds (r : ℝ)) :=
    tendsto_const_nhds
  have hMr : Tendsto (fun _ : ℕ ↦ M ^ r) atTop (nhds (M ^ r)) :=
    tendsto_const_nhds
  have hinner :=
    (hr1.mul (tendsto_highGridUpperStep b)).add
      (tendsto_highGridMertensAllowance b lambda hU)
  have h := hr.mul (hinner.mul hMr)
  have h' := hr1.mul h
  change Tendsto
    (fun K : ℕ ↦ ((r + 1 : ℕ) : ℝ) *
      ((r : ℝ) *
        (((r + 1 : ℕ) : ℝ) * highGridUpperStep b K +
          highGridMertensAllowance b lambda K) * M ^ r))
    atTop (nhds 0)
  simpa [mul_assoc] using h'

lemma exists_fine_highGrid
    {b lambda M eta : ℝ} (heta : 0 < eta) (r : ℕ)
    (hU : highGridUpperEndpoint b ≠ 0) :
    ∃ K : ℕ, 0 < K ∧ highGridFixedTransferError b lambda M r K < eta := by
  have hevent := (tendsto_highGridFixedTransferError b lambda M r hU).eventually
    (Iio_mem_nhds heta)
  obtain ⟨K, hK, hK1⟩ := (hevent.and (eventually_ge_atTop 1)).exists
  exact ⟨K, by omega, hK⟩

def highGridCollisionTransferError (M : ℝ) (r y : ℕ) : ℝ :=
  ((r + 1 : ℕ) : ℝ) * ((r : ℝ) ^ 2 * (y : ℝ)⁻¹ * M ^ r)

theorem tendsto_highGridCollisionTransferError_powerCutoff
    {b : ℝ} (hb : 0 < b) (M : ℝ) (r : ℕ) :
    Tendsto
      (fun N : ℕ ↦ highGridCollisionTransferError M r (powerCutoff b N))
      atTop (nhds 0) := by
  have hyTop : Tendsto (fun N : ℕ ↦ (powerCutoff b N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_powerCutoff_atTop hb)
  have hinv := tendsto_inv_atTop_zero.comp hyTop
  have hc1 : Tendsto
      (fun _ : ℕ ↦ ((r + 1 : ℕ) : ℝ) * (r : ℝ) ^ 2)
      atTop (nhds (((r + 1 : ℕ) : ℝ) * (r : ℝ) ^ 2)) :=
    tendsto_const_nhds
  have hc2 : Tendsto (fun _ : ℕ ↦ M ^ r) atTop (nhds (M ^ r)) :=
    tendsto_const_nhds
  have h := (hc1.mul hinv).mul hc2
  change Tendsto
    (fun N : ℕ ↦ ((r + 1 : ℕ) : ℝ) *
      ((r : ℝ) ^ 2 * (powerCutoff b N : ℝ)⁻¹ * M ^ r))
    atTop (nhds 0)
  simpa [mul_assoc] using h

theorem eventually_powerCutoff_prime_lower
    {C b epsilon : ℝ} (hC : 0 ≤ C)
    (hb : 0 < b) (hb1 : b < 1) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, ∀ P : Finset ℕ,
      Admissible C N P →
      (∀ p ∈ P, p.Prime) →
      (∀ p ∈ P, powerCutoff b N < p) →
      dickmanRho (Real.exp (reciprocalMass P)) - epsilon <
        sieveDensity N P := by
  let eta : ℝ := epsilon / 8
  have heta : 0 < eta := by dsimp only [eta]; positivity
  let M : ℝ := max 1 C
  have hM1 : 1 ≤ M := le_max_left _ _
  have hCM : C ≤ M := le_max_right _ _
  have hM0 : 0 ≤ M := zero_le_one.trans hM1
  let u0 : ℝ := b⁻¹
  have hu0 : 1 < u0 := by
    dsimp only [u0]
    exact (one_lt_inv₀ hb).mpr hb1
  let L : ℝ := highGridLowerEndpoint b
  let U : ℝ := highGridUpperEndpoint b
  have hLu0 : L < u0 := by
    dsimp only [L, u0, highGridLowerEndpoint]
    linarith
  have hu0U : u0 < U := by
    dsimp only [U, u0, highGridUpperEndpoint]
    linarith
  have hL1 : 1 < L := by
    dsimp only [L, u0, highGridLowerEndpoint] at hLu0 ⊢
    linarith
  have hU0 : 0 < U := by linarith
  have hUne : highGridUpperEndpoint b ≠ 0 := by
    dsimp only [U] at hU0
    exact hU0.ne'
  have htailEventually : ∀ᶠ r : ℕ in atTop, factorialTail C r < eta :=
    (tendsto_factorialTail C).eventually (Iio_mem_nhds heta)
  rw [eventually_atTop] at htailEventually
  obtain ⟨r0, hr0⟩ := htailEventually
  let r : ℕ := max r0 ⌈U⌉₊
  have htail : factorialTail C r < eta := hr0 r (le_max_left _ _)
  have hUr : U ≤ (r : ℝ) := by
    exact (Nat.le_ceil U).trans (by
      exact_mod_cast (le_max_right r0 ⌈U⌉₊))
  have hlayer : C ^ (r + 1) / (r + 1).factorial < eta :=
    (factorialLayer_le_factorialTail hC r).trans_lt htail
  obtain ⟨lambda, hlambda0, hlambda1, hscaledUniform, hdamping⟩ :=
    exists_damping_parameter hC hM0 heta r
  have hlambda0' : 0 ≤ lambda := hlambda0.le
  have hlambda1' : lambda ≤ 1 := hlambda1.le
  obtain ⟨K, hK, hfixed⟩ :=
    exists_fine_highGrid (b := b) (lambda := lambda) (M := M) heta r hUne
  let error : ℝ := highGridMertensAllowance b lambda K
  have hLowerStep : 0 < highGridLowerStep b K := by
    unfold highGridLowerStep
    have hnum : 0 < highGridLowerEndpoint b - 1 := by
      dsimp only [L] at hL1
      linarith
    positivity
  have hLogWidth : 0 < highGridLogWidth b K := by
    unfold highGridLogWidth
    rw [Real.log_pos_iff (by positivity)]
    have : 0 < highGridLowerStep b K / highGridUpperEndpoint b := by
      dsimp only [U] at hU0
      positivity
    linarith
  have herror : 0 < error := by
    dsimp only [error, highGridMertensAllowance]
    have : 0 < 1 - lambda := sub_pos.mpr hlambda1
    positivity
  have huEvent : ∀ᶠ N : ℕ in atTop,
      logarithmicEndpoint N (powerCutoff b N) ∈ Set.Ioo L U := by
    have hlim := tendsto_logarithmicEndpoint_powerCutoff hb
    exact hlim.eventually (Ioo_mem_nhds hLu0 hu0U)
  have hcloseBase := eventually_primeExponentCellMass_close error herror
  have hcloseEvent : ∀ᶠ N : ℕ in atTop, ∀ a c : ℝ,
      1 ≤ a → a ≤ c →
      |primeExponentCellMass (powerCutoff b N) a c -
        (Real.log c - Real.log a)| < error :=
    (tendsto_powerCutoff_atTop hb).eventually hcloseBase
  have hyEvent : ∀ᶠ N : ℕ in atTop, 2 ≤ powerCutoff b N :=
    (tendsto_powerCutoff_atTop hb).eventually (eventually_ge_atTop 2)
  have hcollisionEvent : ∀ᶠ N : ℕ in atTop,
      highGridCollisionTransferError M r (powerCutoff b N) < eta :=
    (tendsto_highGridCollisionTransferError_powerCutoff hb M r).eventually
      (Iio_mem_nhds heta)
  have hbonfEvent := eventually_sieveDensity_truncated_abs_lt
    hC heta 1 r
  filter_upwards [huEvent, hcloseEvent, hyEvent, hcollisionEvent,
      hbonfEvent, eventually_ge_atTop 1]
      with N huBounds hclose hy2 hcollision hbonf hN1
  intro P hP hPprime hPhigh
  let y : ℕ := powerCutoff b N
  let u : ℝ := logarithmicEndpoint N y
  let h : ℝ := exactGridStep N y K
  have hN : 0 < N := by omega
  have hy2' : 2 ≤ y := by exact hy2
  have huL : L < u := huBounds.1
  have huU : u < U := huBounds.2
  have hu1 : 1 < u := hL1.trans huL
  have hyN : y < N := lt_of_logarithmicEndpoint_gt_one hy2' hN hu1
  have hh : 0 < h := exactGridStep_pos hK hu1
  have hendpoint : gsGridPoint h K = u := by
    dsimp only [h, u]
    exact gsGridPoint_exactGridStep hK
  have hLower : highGridLowerStep b K ≤ h := by
    unfold highGridLowerStep
    dsimp only [h, exactGridStep, u]
    dsimp only [L] at huL
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  have hUpper : h ≤ highGridUpperStep b K := by
    unfold highGridUpperStep
    dsimp only [h, exactGridStep, u]
    dsimp only [U] at huU
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  have hcover : ∀ p ∈ P, ∃ i < K, p ∈ packetExponentCell P y
      (gsGridPoint h i) (gsGridPoint h (i + 1)) := by
    dsimp only [h, y]
    exact packetGrid_cover_exactGrid hPprime hy2' hN hK hyN hPhigh
      (fun p hp ↦ hP.le_endpoint hp)
  have hc0 : ∀ i < K, 0 ≤ packetGridCoefficient lambda P y h i := by
    intro i hi
    exact packetGridCoefficient_nonneg hlambda0' hh P y i
  have hc1 : ∀ i < K, packetGridCoefficient lambda P y h i ≤ 1 := by
    intro i hi
    have hlogLower : highGridLogWidth b K ≤
        Real.log (gsGridPoint h (i + 1) / gsGridPoint h i) := by
      unfold highGridLogWidth
      apply gsGridCellLog_ge_of_bounds hLowerStep hLower
        (by dsimp only [U] at hU0; exact hU0) hi
      rw [hendpoint]
      exact huU.le
    have herrorLe : error ≤
        (1 - lambda) * highGridLogWidth b K := by
      dsimp only [error, highGridMertensAllowance]
      have hnonneg : 0 ≤ (1 - lambda) * highGridLogWidth b K := by
        positivity
      linarith
    exact packetGridCoefficient_le_one_of_close hlambda0' hlambda1' hh
      herror.le hclose hlogLower herrorLe
  have hmass : atomMass P (fun p : ℕ ↦ lambda * (p : ℝ)⁻¹) ≤ M := by
    rw [atomMass_scaled_reciprocal]
    calc
      lambda * reciprocalMass P ≤ reciprocalMass P :=
        mul_le_of_le_one_left (reciprocalMass_nonneg P) hlambda1'
      _ ≤ C := hP.mass_le
      _ ≤ M := hCM
  have hpacket := packetGrid_lower_bound hPprime hy2' hN
    hlambda0' hlambda1' hh herror.le hcover hc0 hc1 hclose hPhigh
    hM1 hmass r (by
      change 0 ≤ u
      exact zero_le_one.trans hu1.le) (by
      dsimp only [u] at hendpoint
      exact hendpoint.symm) (huU.le.trans hUr)
  have htransferBound := packetMomentTransferErrorSum_le_uniform
    hh.le herror.le hM1 (y := y) (r := r)
  have hfirst :
      (r : ℝ) * (((r + 1 : ℕ) : ℝ) * h + error) * M ^ r ≤
        (r : ℝ) *
          (((r + 1 : ℕ) : ℝ) * highGridUpperStep b K + error) * M ^ r := by
    gcongr
  have htransfer :
      (∑ j ∈ Finset.range (r + 1),
        packetMomentTransferError y j h error M / j.factorial) < 2 * eta := by
    have hbound :
        ((r + 1 : ℕ) : ℝ) *
            ((r : ℝ) * (((r + 1 : ℕ) : ℝ) * h + error) * M ^ r +
              (r : ℝ) ^ 2 * (y : ℝ)⁻¹ * M ^ r) ≤
          highGridFixedTransferError b lambda M r K +
            highGridCollisionTransferError M r y := by
      unfold highGridFixedTransferError highGridCollisionTransferError
      rw [mul_add]
      exact add_le_add
        (mul_le_mul_of_nonneg_left hfirst (by positivity)) le_rfl
    have hsum :
        highGridFixedTransferError b lambda M r K +
            highGridCollisionTransferError M r y < 2 * eta := by
      dsimp only [error, y] at hfixed hcollision ⊢
      linarith
    exact (htransferBound.trans hbound).trans_lt hsum
  have hscaledBound := scaledTruncatedError_le_uniform hC hlambda0'
    hlambda1' hM1 hCM hP.mass_le r (N := N)
  have hscaled :
      (∑ j ∈ Finset.range (r + 1),
        |lambda ^ j - 1| * cutoffElementaryReciprocalMass N P j) < eta :=
    hscaledBound.trans_lt hscaledUniform
  have hbonfP :
      |sieveDensity N P - truncatedSieveApprox N P r| < 2 * eta := by
    have hraw := hbonf P hP (fun a ha hnot ↦ (hnot (hPprime a ha)).elim)
    linarith
  have hdamp := hdamping (reciprocalMass P)
    ⟨reciprocalMass_nonneg P, hP.mass_le⟩
  have hpacket' :
      dickmanRho (Real.exp (lambda * reciprocalMass P)) <
        truncatedSieveApprox N P r + 3 * eta := by
    linarith
  rw [abs_lt] at hbonfP
  have heq : epsilon = 8 * eta := by dsimp only [eta]; ring
  rw [heq]
  linarith

end

end Erdos783
