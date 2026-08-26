import ErdosProblems.Erdos1002.FixedAwayUnconditionalDeletion
import ErdosProblems.Erdos1002.FixedAwayUnshiftedElementaryMiddle

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Subquadratic aggregation of the elementary unshifted shells

The elementary denominator decomposition gives a bound on frequency shell
`K = 2^s` which grows only like `clog₂(s + 2)`.  This file sums those
bounds over the `O(log N)` relevant frequency shells and proves the exact
subquadratic zero-carrier statement consumed by
`FixedAwayUnconditionalDeletion`.
-/

open Filter MeasureTheory Set
open scoped BigOperators Topology Real

namespace Erdos1002

noncomputable section

/-! ## The elementary shell count is `o(sqrt s)` -/

/-- A real majorant for the square of the binary ceiling logarithm divided
by its natural scale. -/
def fixedAwayClogSquareMajorant (s : ℕ) : ℝ :=
  (Real.log ((s + 2 : ℕ) : ℝ) / Real.log 2 + 1) ^ 2 /
    ((s + 1 : ℕ) : ℝ)

theorem fixedAwayClogSquareMajorant_nonneg (s : ℕ) :
    0 ≤ fixedAwayClogSquareMajorant s := by
  unfold fixedAwayClogSquareMajorant
  positivity

theorem cast_clog_two_sq_div_le_fixedAwayClogSquareMajorant
    (s : ℕ) :
    (Nat.clog 2 (s + 2) : ℝ) ^ 2 / ((s + 1 : ℕ) : ℝ) ≤
      fixedAwayClogSquareMajorant s := by
  have hclog :=
    nat_clog_two_cast_le_log_div_add_one (s + 2) (by omega)
  have hclog0 : 0 ≤ (Nat.clog 2 (s + 2) : ℝ) := by positivity
  have hmajor0 :
      0 ≤ Real.log ((s + 2 : ℕ) : ℝ) / Real.log 2 + 1 :=
    hclog0.trans hclog
  have hsq :
      (Nat.clog 2 (s + 2) : ℝ) ^ 2 ≤
        (Real.log ((s + 2 : ℕ) : ℝ) / Real.log 2 + 1) ^ 2 :=
    pow_le_pow_left₀ hclog0 hclog 2
  exact div_le_div_of_nonneg_right hsq (by positivity)

/-- The logarithmic majorant tends to zero. -/
theorem tendsto_fixedAwayClogSquareMajorant_zero :
    Tendsto fixedAwayClogSquareMajorant atTop (nhds 0) := by
  let x : ℕ → ℝ := fun s ↦ ((s + 2 : ℕ) : ℝ)
  have hx : Tendsto x atTop atTop := by
    exact tendsto_natCast_atTop_atTop.comp
      (Filter.tendsto_add_atTop_nat 2)
  have hlog2 : Real.log 2 ≠ 0 :=
    (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have h2 :=
    (Real.tendsto_pow_log_div_mul_add_atTop
      1 (-1) 2 one_ne_zero).comp hx
  have h1 :=
    (Real.tendsto_pow_log_div_mul_add_atTop
      1 (-1) 1 one_ne_zero).comp hx
  have h0 :=
    (Real.tendsto_pow_log_div_mul_add_atTop
      1 (-1) 0 one_ne_zero).comp hx
  have h2' :
      Tendsto
        (fun s : ℕ ↦ Real.log (x s) ^ 2 / (x s - 1))
        atTop (nhds 0) := by
    simpa only [one_mul, sub_eq_add_neg] using! h2
  have h1' :
      Tendsto
        (fun s : ℕ ↦ Real.log (x s) / (x s - 1))
        atTop (nhds 0) := by
    simpa only [one_mul, sub_eq_add_neg, pow_one] using! h1
  have h0' :
      Tendsto
        (fun s : ℕ ↦ 1 / (x s - 1))
        atTop (nhds 0) := by
    simpa only [one_mul, sub_eq_add_neg, pow_zero] using! h0
  have hsum :
      Tendsto
        (fun s : ℕ ↦
          (1 / Real.log 2 ^ 2) *
              (Real.log (x s) ^ 2 / (x s - 1)) +
            (2 / Real.log 2) *
              (Real.log (x s) / (x s - 1)) +
            1 / (x s - 1))
        atTop (nhds 0) := by
    simpa using!
      ((tendsto_const_nhds.mul h2').add
        (tendsto_const_nhds.mul h1')).add h0'
  apply hsum.congr'
  filter_upwards with s
  dsimp [fixedAwayClogSquareMajorant, x]
  have hden :
      (((s + 2 : ℕ) : ℝ) - 1) = ((s + 1 : ℕ) : ℝ) := by
    push_cast
    ring
  rw [hden]
  have hden0 : (((s + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp [hlog2, hden0]
  ring

/-- Consequently the square binary-ceiling logarithm is `o(s)`, in the
explicit epsilon form used in the finite shell sum. -/
theorem eventually_cast_clog_two_sq_le_mul
    {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ s : ℕ in atTop,
      (Nat.clog 2 (s + 2) : ℝ) ^ 2 ≤
        eta * ((s + 1 : ℕ) : ℝ) := by
  have hsmall :
      ∀ᶠ s : ℕ in atTop,
        fixedAwayClogSquareMajorant s < eta :=
    tendsto_fixedAwayClogSquareMajorant_zero.eventually_lt_const heta
  filter_upwards [hsmall] with s hs
  have hdiv :=
    (cast_clog_two_sq_div_le_fixedAwayClogSquareMajorant s).trans hs.le
  have hpos : (0 : ℝ) < ((s + 1 : ℕ) : ℝ) := by positivity
  exact (div_le_iff₀ hpos).mp hdiv

/-! ## Summation over frequency shells -/

def fixedAwayUnshiftedPowerShellGrowthConstant
    (T δ : ℝ) : ℝ :=
  2 * fixedAwayUnshiftedLowShellUniformConstant T δ +
    4 * fixedAwayUnshiftedElementaryShellUniformConstant T δ +
    48 * fixedAwayUnshiftedHighMultiplierUniformConstant T δ

theorem fixedAwayUnshiftedPowerShellGrowthConstant_nonneg
    {T δ : ℝ} (hT : 0 ≤ T) :
    0 ≤ fixedAwayUnshiftedPowerShellGrowthConstant T δ := by
  unfold fixedAwayUnshiftedPowerShellGrowthConstant
  have hlow :=
    fixedAwayUnshiftedLowShellUniformConstant_nonneg_of_nonneg
      (T := T) (δ := δ) hT
  have hmiddle :=
    fixedAwayUnshiftedElementaryShellUniformConstant_nonneg
      (T := T) (δ := δ) hT
  have hhigh :=
    fixedAwayUnshiftedHighMultiplierUniformConstant_nonneg_of_nonneg
      (T := T) (δ := δ) hT
  positivity

theorem fixedAwayUnshiftedPowerShellUniformBound_le_clog
    {T δ : ℝ} (hT : 0 ≤ T) (s : ℕ) :
    fixedAwayUnshiftedPowerShellUniformBound T δ s ≤
      fixedAwayUnshiftedPowerShellGrowthConstant T δ *
        ((Nat.clog 2 (s + 2) : ℝ) + 1) := by
  let A : ℝ :=
    2 * fixedAwayUnshiftedLowShellUniformConstant T δ +
      48 * fixedAwayUnshiftedHighMultiplierUniformConstant T δ
  let B : ℝ :=
    fixedAwayUnshiftedElementaryShellUniformConstant T δ
  let c : ℕ := Nat.clog 2 (s + 2)
  have hlow :=
    fixedAwayUnshiftedLowShellUniformConstant_nonneg_of_nonneg
      (T := T) (δ := δ) hT
  have hhigh :=
    fixedAwayUnshiftedHighMultiplierUniformConstant_nonneg_of_nonneg
      (T := T) (δ := δ) hT
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hB : 0 ≤ B := by
    dsimp [B]
    exact fixedAwayUnshiftedElementaryShellUniformConstant_nonneg hT
  have hc : 0 ≤ (c : ℝ) := by positivity
  have hR :
      (fixedAwayUnshiftedPowerShellMiddleCount s : ℝ) ≤
        4 * (c : ℝ) := by
    exact_mod_cast fixedAwayUnshiftedPowerShellMiddleCount_le s
  calc
    fixedAwayUnshiftedPowerShellUniformBound T δ s =
        A +
          (fixedAwayUnshiftedPowerShellMiddleCount s : ℝ) * B := by
      dsimp [A, B]
      unfold fixedAwayUnshiftedPowerShellUniformBound
      ring
    _ ≤ A + (4 * (c : ℝ)) * B := by gcongr
    _ ≤ (A + 4 * B) * ((c : ℝ) + 1) := by
      nlinarith
    _ = fixedAwayUnshiftedPowerShellGrowthConstant T δ *
        ((Nat.clog 2 (s + 2) : ℝ) + 1) := by
      dsimp [A, B, c]
      unfold fixedAwayUnshiftedPowerShellGrowthConstant
      ring

/-- The energy of the first `H` positive frequency shells is
`o(H²)`, uniformly in the denominator cutoff and in the fixed-away
threshold. -/
theorem eventually_sum_sq_norm_fixedAwayUnshifted_powerShells_small
    {δ T : ℝ} (hδ : 0 < δ) (hδT : δ < T) :
    ∀ eta > 0, ∀ᶠ H : ℕ in atTop,
      ∀ (t : ℝ) (N : ℕ), δ < t → t ≤ T →
        ∑ s ∈ Finset.range H,
            ‖fixedAwayUnshiftedFiniteVector
              t δ (2 ^ s) 2 N‖ ^ 2 ≤
          eta * (H : ℝ) ^ 2 := by
  intro eta heta
  let C : ℝ := fixedAwayUnshiftedPowerShellGrowthConstant T δ
  let q : ℝ := eta / (6 * (C ^ 2 + 1))
  have hT : 0 ≤ T := hδ.le.trans hδT.le
  have hC : 0 ≤ C := by
    dsimp [C]
    exact fixedAwayUnshiftedPowerShellGrowthConstant_nonneg hT
  have hq : 0 < q := by
    dsimp [q]
    positivity
  have hclog := eventually_cast_clog_two_sq_le_mul hq
  have hcast :
      ∀ᶠ H : ℕ in atTop, 1 / q ≤ (H : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually
      (eventually_ge_atTop (1 / q))
  filter_upwards [eventually_ge_atTop 1, hclog, hcast] with
      H hH hclogH hcastH
  intro t N hδt htT
  let c : ℕ := Nat.clog 2 (H + 2)
  have hqH : 1 ≤ q * (H : ℝ) := by
    have := (div_le_iff₀ hq).mp hcastH
    simpa only [one_div, mul_comm] using! this
  have hHsucc : ((H + 1 : ℕ) : ℝ) ≤ 2 * (H : ℝ) := by
    have hHR : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
    push_cast
    linarith
  have hcSq :
      (c : ℝ) ^ 2 ≤ 2 * q * (H : ℝ) := by
    calc
      (c : ℝ) ^ 2 ≤ q * ((H + 1 : ℕ) : ℝ) := by
        simpa only [c] using! hclogH
      _ ≤ q * (2 * (H : ℝ)) := by gcongr
      _ = 2 * q * (H : ℝ) := by ring
  have hcOneSq :
      ((c : ℝ) + 1) ^ 2 ≤ 6 * q * (H : ℝ) := by
    have hsquare :
        ((c : ℝ) + 1) ^ 2 ≤
          2 * ((c : ℝ) ^ 2 + 1) := by
      nlinarith [sq_nonneg ((c : ℝ) - 1)]
    calc
      ((c : ℝ) + 1) ^ 2 ≤
          2 * ((c : ℝ) ^ 2 + 1) := hsquare
      _ ≤ 2 * (2 * q * (H : ℝ) + q * (H : ℝ)) := by
        gcongr
      _ = 6 * q * (H : ℝ) := by ring
  have hpoint : ∀ s ∈ Finset.range H,
      ‖fixedAwayUnshiftedFiniteVector t δ (2 ^ s) 2 N‖ ^ 2 ≤
        eta * (H : ℝ) := by
    intro s hs
    have hsH : s < H := Finset.mem_range.mp hs
    have hclogMono :
        Nat.clog 2 (s + 2) ≤ c := by
      dsimp [c]
      exact Nat.clog_mono_right 2 (by omega)
    have hnorm :=
      norm_fixedAwayUnshiftedFiniteVector_powerShell_le_uniform
        s N hδ hδt htT
    have hbound :=
      fixedAwayUnshiftedPowerShellUniformBound_le_clog
        (δ := δ) hT s
    have hcNonneg : 0 ≤ (c : ℝ) + 1 := by positivity
    have hsmallNonneg :
        0 ≤ (Nat.clog 2 (s + 2) : ℝ) + 1 := by positivity
    have hcarrier :
        ‖fixedAwayUnshiftedFiniteVector t δ (2 ^ s) 2 N‖ ≤
          C * ((c : ℝ) + 1) := by
      calc
        ‖fixedAwayUnshiftedFiniteVector t δ (2 ^ s) 2 N‖ ≤
            fixedAwayUnshiftedPowerShellUniformBound T δ s := hnorm
        _ ≤ C * ((Nat.clog 2 (s + 2) : ℝ) + 1) := by
          simpa only [C] using! hbound
        _ ≤ C * ((c : ℝ) + 1) := by
          apply mul_le_mul_of_nonneg_left _ hC
          have hclogMonoReal :
              (Nat.clog 2 (s + 2) : ℝ) ≤ (c : ℝ) := by
            exact_mod_cast hclogMono
          linarith
    have hcarrierSq :
        ‖fixedAwayUnshiftedFiniteVector t δ (2 ^ s) 2 N‖ ^ 2 ≤
          C ^ 2 * ((c : ℝ) + 1) ^ 2 := by
      calc
        ‖fixedAwayUnshiftedFiniteVector t δ (2 ^ s) 2 N‖ ^ 2 ≤
            (C * ((c : ℝ) + 1)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hcarrier 2
        _ = C ^ 2 * ((c : ℝ) + 1) ^ 2 := by ring
    calc
      ‖fixedAwayUnshiftedFiniteVector t δ (2 ^ s) 2 N‖ ^ 2 ≤
          C ^ 2 * ((c : ℝ) + 1) ^ 2 := hcarrierSq
      _ ≤ C ^ 2 * (6 * q * (H : ℝ)) := by gcongr
      _ ≤ eta * (H : ℝ) := by
        dsimp [q]
        have hden : 0 < 6 * (C ^ 2 + 1) := by positivity
        have hratio : C ^ 2 / (C ^ 2 + 1) ≤ 1 := by
          apply (div_le_one₀ (by positivity : 0 < C ^ 2 + 1)).2
          linarith
        calc
          C ^ 2 * (6 * (eta / (6 * (C ^ 2 + 1))) * (H : ℝ)) =
              eta * (H : ℝ) * (C ^ 2 / (C ^ 2 + 1)) := by
            field_simp
          _ ≤ eta * (H : ℝ) * 1 := by
            gcongr
          _ = eta * (H : ℝ) := by ring
  calc
    ∑ s ∈ Finset.range H,
        ‖fixedAwayUnshiftedFiniteVector
          t δ (2 ^ s) 2 N‖ ^ 2 ≤
        ∑ _s ∈ Finset.range H, eta * (H : ℝ) :=
      Finset.sum_le_sum hpoint
    _ = eta * (H : ℝ) ^ 2 := by
      simp
      ring

/-! ## From finite frequency shells to the complete positive spectrum -/

/-- Exact summation bridge: a bound `M` for the frequency shells below
`clog₂(N²)` controls the whole positive spectrum, up to the single
frequency `n = 1` and the already proved geometric tail. -/
theorem tsum_fixedAwayZeroCarrierRest_nat_le_of_powerShellSum
    {t δ T M : ℝ} (N : ℕ)
    (hδ : 0 < δ) (hδt : δ < t) (htT : t ≤ T) (hN : 1 ≤ N)
    (hfirst :
      ∑ s ∈ Finset.range (Nat.clog 2 (N ^ 2)),
          ‖fixedAwayUnshiftedFiniteVector t δ (2 ^ s) 2 N‖ ^ 2 ≤ M) :
    (∑' n : ℕ,
      ‖fixedAwayZeroCarrierRestCoefficients
        t δ N (n : ℤ)‖ ^ 2) ≤
      (fixedAwayPVGlobalDecayConstant t δ *
          fixedAwayInverseSquareMass) ^ 2 +
        M +
        8 * fixedAwayUnshiftedLowShellUniformConstant T δ ^ 2 := by
  let R : ℕ := Nat.clog 2 (N ^ 2)
  let f : ℕ → ℝ := fun n ↦
    ‖fixedAwayZeroCarrierRestCoefficients t δ N (n : ℤ)‖ ^ 2
  let C1 : ℝ :=
    fixedAwayPVGlobalDecayConstant t δ *
      fixedAwayInverseSquareMass
  let Tail : ℝ :=
    8 * fixedAwayUnshiftedLowShellUniformConstant T δ ^ 2
  have hfzero : f 0 = 0 := by
    dsimp [f]
    rw [fixedAwayZeroCarrierRestCoefficients_zero, norm_zero,
      zero_pow (by omega : (2 : ℕ) ≠ 0)]
  have hfone : f 1 ≤ C1 ^ 2 := by
    dsimp [f, C1]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (norm_fixedAwayUnshiftedRest_one_le N hδ hδt) 2
  have hpowSelf : ∀ k : ℕ, k ≤ 2 ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ]
        have hone : 1 ≤ 2 ^ k := Nat.one_le_two_pow
        omega
  apply Real.tsum_le_of_sum_range_le (fun n ↦ sq_nonneg _)
  intro k
  let E : ℕ := max R k
  let H : ℕ := E - R
  let S : Finset ℕ :=
    insert 0 (insert 1 (Finset.Ioc (1 : ℕ) (2 ^ E)))
  have hRE : R ≤ E := by
    dsimp [E]
    exact le_max_left _ _
  have hkE : k ≤ E := by
    dsimp [E]
    exact le_max_right _ _
  have hRH : R + H = E := by
    dsimp [H]
    omega
  have hkPow : k ≤ 2 ^ E := hkE.trans (hpowSelf E)
  have hsubset : Finset.range k ⊆ S := by
    intro n hn
    have hnk : n < k := Finset.mem_range.mp hn
    have hnPow : n ≤ 2 ^ E := (Nat.le_of_lt hnk).trans hkPow
    simp only [S, Finset.mem_insert, Finset.mem_Ioc]
    omega
  have hfirst' :
      ∑ s ∈ Finset.range R,
          ‖fixedAwayUnshiftedFiniteVector t δ (2 ^ s) 2 N‖ ^ 2 ≤ M := by
    simpa only [R] using! hfirst
  have htail :
      ∑ r ∈ Finset.range H,
          ‖fixedAwayUnshiftedFiniteVector t δ
            (2 ^ (R + r)) 2 N‖ ^ 2 ≤ Tail := by
    dsimp [R, Tail]
    exact sum_sq_norm_fixedAwayUnshiftedFiniteVector_clogTail_le
      N H hδ hδt htT (by omega)
  have hshell :
      ∑ s ∈ Finset.range E,
          ‖fixedAwayUnshiftedFiniteVector t δ (2 ^ s) 2 N‖ ^ 2 ≤
        M + Tail := by
    rw [← hRH, Finset.sum_range_add]
    exact add_le_add hfirst' htail
  have hfinite :
      ∑ n ∈ Finset.Ioc (1 : ℕ) (2 ^ E), f n ≤
        M + Tail := by
    rw [← sum_sq_norm_fixedAwayUnshiftedFiniteVector_range_eq
      t δ N E]
    simpa only [f] using! hshell
  calc
    ∑ n ∈ Finset.range k, f n ≤ ∑ n ∈ S, f n := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro n _hn _hnot
      exact sq_nonneg _
    _ = f 0 + f 1 + ∑ n ∈ Finset.Ioc (1 : ℕ) (2 ^ E), f n := by
      simp [S, add_assoc]
    _ ≤ C1 ^ 2 + (M + Tail) := by
      rw [hfzero, zero_add]
      exact add_le_add hfone hfinite
    _ = (fixedAwayPVGlobalDecayConstant t δ *
            fixedAwayInverseSquareMass) ^ 2 +
          M +
          8 * fixedAwayUnshiftedLowShellUniformConstant T δ ^ 2 := by
      dsimp [C1, Tail]
      ring

/-- The binary shell index corresponding to `N²` tends to infinity. -/
theorem tendsto_clog_two_natSquare_atTop :
    Tendsto (fun N : ℕ ↦ Nat.clog 2 (N ^ 2)) atTop atTop := by
  refine tendsto_atTop.2 fun b ↦ ?_
  filter_upwards [eventually_ge_atTop (2 ^ b + 1)] with N hN
  have hpowN : 2 ^ b < N := by omega
  have hpowPos : 0 < 2 ^ b := by positivity
  have hNpos : 0 < N := hpowPos.trans hpowN
  have hNN : N ≤ N ^ 2 := by
    nlinarith [Nat.one_le_iff_ne_zero.2 hNpos.ne']
  have hpowSq : 2 ^ b < N ^ 2 := hpowN.trans_le hNN
  exact (Nat.lt_clog_iff_pow_lt (by omega : 1 < 2)).2 hpowSq |>.le

/-! ## Unconditional subquadratic zero-carrier energy -/

/-- The elementary middle-range decomposition proves the exact
subquadratic zero-carrier proposition required by the fixed-away
probability deletion. -/
theorem fixedAwayZeroCarrierSubquadraticEnergy :
    FixedAwayZeroCarrierSubquadraticEnergy := by
  intro δ T hδ hδT eta heta
  let L : ℕ → ℝ := fun N ↦ Real.log (N : ℝ)
  let c : ℝ := 2 / Real.log 2 + 1
  let G : ℝ :=
    fixedAwayPVGlobalDecayUniformConstant T δ *
      fixedAwayInverseSquareMass
  let Tail : ℝ :=
    8 * fixedAwayUnshiftedLowShellUniformConstant T δ ^ 2
  let Const : ℝ := G ^ 2 + Tail
  let etaShell : ℝ := eta / (3 * c ^ 2)
  let etaConst : ℝ := 2 * eta / 3
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hetaShell : 0 < etaShell := by
    dsimp [etaShell]
    positivity
  have hetaConst : 0 < etaConst := by
    dsimp [etaConst]
    positivity
  have hlog :
      Tendsto L atTop atTop := by
    dsimp [L]
    exact Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogOne : ∀ᶠ N : ℕ in atTop, 1 ≤ L N :=
    hlog.eventually (eventually_ge_atTop 1)
  have hlogSq :
      Tendsto (fun N : ℕ ↦ L N ^ 2) atTop atTop :=
    (tendsto_pow_atTop (α := ℝ)
      (by norm_num : (2 : ℕ) ≠ 0)).comp hlog
  have hconstEvent :
      ∀ᶠ N : ℕ in atTop, Const / etaConst ≤ L N ^ 2 :=
    hlogSq.eventually (eventually_ge_atTop (Const / etaConst))
  have hshellH :=
    eventually_sum_sq_norm_fixedAwayUnshifted_powerShells_small
      hδ hδT etaShell hetaShell
  have hshellN :
      ∀ᶠ N : ℕ in atTop,
        ∀ (t : ℝ) (P : ℕ), δ < t → t ≤ T →
          ∑ s ∈ Finset.range (Nat.clog 2 (N ^ 2)),
              ‖fixedAwayUnshiftedFiniteVector
                t δ (2 ^ s) 2 P‖ ^ 2 ≤
            etaShell * (Nat.clog 2 (N ^ 2) : ℝ) ^ 2 :=
    tendsto_clog_two_natSquare_atTop.eventually hshellH
  have hclogBound :
      ∀ᶠ N : ℕ in atTop,
        (Nat.clog 2 (N ^ 2) : ℝ) ≤ c * L N := by
    filter_upwards [eventually_ge_atTop 1, hlogOne] with N hN hLN
    have hclog :=
      nat_clog_two_cast_le_log_div_add_one (N ^ 2) (by
        nlinarith [Nat.zero_le N])
    have hlogPow :
        Real.log ((N ^ 2 : ℕ) : ℝ) = 2 * L N := by
      dsimp [L]
      norm_num only [Nat.cast_pow]
      rw [Real.log_pow]
      norm_num
    rw [hlogPow] at hclog
    calc
      (Nat.clog 2 (N ^ 2) : ℝ) ≤
          2 * L N / Real.log 2 + 1 := hclog
      _ ≤ 2 * L N / Real.log 2 + L N := by linarith
      _ = c * L N := by
        dsimp [c]
        ring
  filter_upwards [
      eventually_ge_atTop 1, hlogOne, hconstEvent, hshellN, hclogBound] with
      N hN hLN hconstN hshellN' hclogN
  intro t hδt htT
  have hTnonneg : 0 ≤ T := hδ.le.trans hδT.le
  have hLpos : 0 < L N := lt_of_lt_of_le zero_lt_one hLN
  have hRnonneg :
      0 ≤ (Nat.clog 2 (N ^ 2) : ℝ) := by positivity
  have hcLnonneg : 0 ≤ c * L N :=
    mul_nonneg hc.le hLpos.le
  have hRSq :
      (Nat.clog 2 (N ^ 2) : ℝ) ^ 2 ≤
        (c * L N) ^ 2 :=
    pow_le_pow_left₀ hRnonneg hclogN 2
  have hshell :
      ∑ s ∈ Finset.range (Nat.clog 2 (N ^ 2)),
          ‖fixedAwayUnshiftedFiniteVector
            t δ (2 ^ s) 2 N‖ ^ 2 ≤
        (eta / 3) * L N ^ 2 := by
    calc
      ∑ s ∈ Finset.range (Nat.clog 2 (N ^ 2)),
          ‖fixedAwayUnshiftedFiniteVector
            t δ (2 ^ s) 2 N‖ ^ 2 ≤
          etaShell * (Nat.clog 2 (N ^ 2) : ℝ) ^ 2 :=
        hshellN' t N hδt htT
      _ ≤ etaShell * (c * L N) ^ 2 := by gcongr
      _ = (eta / 3) * L N ^ 2 := by
        dsimp [etaShell]
        field_simp
  have hraw :=
    tsum_fixedAwayZeroCarrierRest_nat_le_of_powerShellSum
      N hδ hδt htT hN hshell
  have hglobal :=
    fixedAwayPVGlobalDecayConstant_le_uniform hδ hδt.le htT
  have hmass : 0 ≤ fixedAwayInverseSquareMass :=
    fixedAwayInverseSquareMass_nonneg
  have hactualGlobal :
      (fixedAwayPVGlobalDecayConstant t δ *
          fixedAwayInverseSquareMass) ^ 2 ≤ G ^ 2 := by
    apply pow_le_pow_left₀
      (mul_nonneg
        (fixedAwayPVGlobalDecayConstant_nonneg t δ) hmass)
    dsimp [G]
    exact mul_le_mul_of_nonneg_right hglobal hmass
  have hconst :
      Const ≤ etaConst * L N ^ 2 := by
    have := (div_le_iff₀ hetaConst).mp hconstN
    simpa only [mul_comm] using! this
  calc
    (∑' n : ℕ,
      ‖fixedAwayZeroCarrierRestCoefficients
        t δ N (n : ℤ)‖ ^ 2) ≤
        (fixedAwayPVGlobalDecayConstant t δ *
            fixedAwayInverseSquareMass) ^ 2 +
          (eta / 3) * L N ^ 2 +
          8 * fixedAwayUnshiftedLowShellUniformConstant T δ ^ 2 :=
      hraw
    _ ≤ G ^ 2 + (eta / 3) * L N ^ 2 + Tail := by
      dsimp [Tail]
      gcongr
    _ = Const + (eta / 3) * L N ^ 2 := by
      dsimp [Const, Tail]
      ring
    _ ≤ etaConst * L N ^ 2 + (eta / 3) * L N ^ 2 := by
      gcongr
    _ = eta * Real.log (N : ℝ) ^ 2 := by
      dsimp [etaConst, L]
      ring

/-- The fixed-away minor remainder is therefore deleted in probability
without a Chan--Kumchev or any other external arithmetic hypothesis. -/
theorem
    iterated_probabilityDeletion_normalizedFixedAwayMinorRemainder_unconditional
    (ε : ℝ) (hε : 0 < ε) (hεhalf : ε < 1 / 2) :
    ∀ r > 0, ∀ δ > 0,
      ∀ᶠ A : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
        uniform01Measure.real
          {alpha | r ≤
            ‖normalizedFixedAwayMinorRemainder
              N (A : ℝ) ε alpha‖} < δ :=
  iterated_probabilityDeletion_normalizedFixedAwayMinorRemainder_of_zeroRest
    fixedAwayZeroCarrierSubquadraticEnergy ε hε hεhalf

end

end Erdos1002
