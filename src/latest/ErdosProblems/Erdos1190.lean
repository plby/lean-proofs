/-
Erdős Problem 1190 — reciprocal-sum corollary of Problem 202.

The PDF states the 1190 quantity using finite increasing sequences
`m < n₁ < ... < n_k` with pairwise disjoint residue classes.  We use the
equivalent finite-set formulation: a `Finset ℕ` has a unique increasing
enumeration, and the residue-class data is indexed by the moduli themselves.
-/

import Mathlib
import Mathlib.NumberTheory.AbelSummation
import ErdosProblems.Erdos202

namespace Erdos1190

open Filter Finset
open Erdos202
open scoped BigOperators

/-! ## Statement layer -/

/-- Reciprocal mass of a finite set of moduli. -/
noncomputable def reciprocalSum (Q : Finset ℕ) : ℝ :=
  ∑ q ∈ Q, (q : ℝ)⁻¹

/- The next four aliases match the notation used in the PDF-roadmap notes. -/

/-- Alias for `reciprocalSum`, matching the shorter roadmap name. -/
noncomputable abbrev recipSum : Finset ℕ → ℝ :=
  reciprocalSum

/-- A 1190-admissible tail family: all moduli are strictly larger than `m`, and
some choice of residue classes modulo those moduli is pairwise disjoint. -/
def TailAdmissible (m : ℕ) (Q : Finset ℕ) : Prop :=
  (∀ q ∈ Q, m < q) ∧
  ∃ a : ResidueAssignment Q, PairwiseDisjointResidues Q a

/-- Alias for `TailAdmissible`, matching the roadmap name. -/
abbrev AdmissibleAbove : ℕ → Finset ℕ → Prop :=
  TailAdmissible

/-- The set of reciprocal sums appearing in Problem 1190. -/
noncomputable def reciprocalSums1190 (m : ℕ) : Set ℝ :=
  {s : ℝ | ∃ Q : Finset ℕ, TailAdmissible m Q ∧ reciprocalSum Q = s}

/-- Alias for `reciprocalSums1190`, matching the roadmap name. -/
noncomputable abbrev eps1190Set : ℕ → Set ℝ :=
  reciprocalSums1190

/-- Erdős's `ε_m`: the supremum of reciprocal sums over all finite
1190-admissible tail families. -/
noncomputable def epsilon1190 (m : ℕ) : ℝ :=
  sSup (reciprocalSums1190 m)

/-- Alias for `epsilon1190`, matching the roadmap name. -/
noncomputable abbrev eps1190 : ℕ → ℝ :=
  epsilon1190

/-- PDF Corollary 1.2 in epsilon form:
`ε_m = exp(-(1+o(1)) sqrt(log m log log m))`. -/
def HasErdos1190Asymptotic : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop,
    Lscale (-(1 + ε)) m ≤ epsilon1190 m ∧
    epsilon1190 m ≤ Lscale (-(1 - ε)) m

/-- Public statement name for Erdős Problem 1190. -/
def Erdos1190Statement : Prop :=
  HasErdos1190Asymptotic

/-! ## Elementary API for the 1190 supremum -/

lemma reciprocalSum_empty : reciprocalSum (∅ : Finset ℕ) = 0 := by
  simp [reciprocalSum]

lemma reciprocalSum_nonneg (Q : Finset ℕ) : 0 ≤ reciprocalSum Q := by
  classical
  unfold reciprocalSum
  exact Finset.sum_nonneg fun q _hq =>
    inv_nonneg.2 (by exact_mod_cast Nat.zero_le q)

lemma reciprocalSum_mono {Q Q' : Finset ℕ} (hsub : Q' ⊆ Q) :
    reciprocalSum Q' ≤ reciprocalSum Q := by
  classical
  unfold reciprocalSum
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (by
    intro q _hq _hq'
    exact inv_nonneg.2 (by exact_mod_cast Nat.zero_le q))

lemma reciprocalSum_filter_add_filter_not
    (Q : Finset ℕ) (p : ℕ → Prop) [DecidablePred p] :
    reciprocalSum (Q.filter p) + reciprocalSum (Q.filter fun q => ¬ p q) =
      reciprocalSum Q := by
  classical
  simpa [reciprocalSum] using
    (Finset.sum_filter_add_sum_filter_not (s := Q) (p := p)
      (f := fun q : ℕ => (q : ℝ)⁻¹))

lemma tailAdmissible_empty (m : ℕ) : TailAdmissible m (∅ : Finset ℕ) := by
  constructor
  · intro q hq
    simp at hq
  · refine ⟨fun _ => 0, ?_⟩
    intro i _j _hij
    cases i with
    | mk q hq => simp at hq

lemma reciprocalSums1190_nonempty (m : ℕ) :
    (reciprocalSums1190 m).Nonempty := by
  refine ⟨0, ?_⟩
  exact ⟨∅, tailAdmissible_empty m, reciprocalSum_empty⟩

lemma eps1190Set_nonempty (m : ℕ) : (eps1190Set m).Nonempty := by
  simpa [eps1190Set] using reciprocalSums1190_nonempty m

lemma reciprocalSums1190_nonneg {m : ℕ} {s : ℝ}
    (hs : s ∈ reciprocalSums1190 m) : 0 ≤ s := by
  rcases hs with ⟨Q, _hQ, rfl⟩
  exact reciprocalSum_nonneg Q

lemma epsilon1190_nonneg (m : ℕ) : 0 ≤ epsilon1190 m := by
  exact Real.sSup_nonneg (fun _s hs => reciprocalSums1190_nonneg hs)

lemma le_epsilon1190_of_tailAdmissible
    {m : ℕ} {Q : Finset ℕ}
    (hQ : TailAdmissible m Q)
    (hbdd : BddAbove (reciprocalSums1190 m)) :
    reciprocalSum Q ≤ epsilon1190 m := by
  exact le_csSup hbdd ⟨Q, hQ, rfl⟩

lemma le_eps1190_of_admissibleAbove
    {m : ℕ} {Q : Finset ℕ}
    (hQ : AdmissibleAbove m Q)
    (hbdd : BddAbove (eps1190Set m)) :
    recipSum Q ≤ eps1190 m := by
  exact le_epsilon1190_of_tailAdmissible hQ hbdd

lemma epsilon1190_le_of_all_sums_le
    {m : ℕ} {B : ℝ}
    (hB : ∀ Q : Finset ℕ, TailAdmissible m Q → reciprocalSum Q ≤ B) :
    epsilon1190 m ≤ B := by
  refine csSup_le (reciprocalSums1190_nonempty m) ?_
  intro s hs
  rcases hs with ⟨Q, hQ, rfl⟩
  exact hB Q hQ

lemma eps1190_le_of_all_sums_le
    {m : ℕ} {B : ℝ}
    (hB : ∀ Q : Finset ℕ, AdmissibleAbove m Q → recipSum Q ≤ B) :
    eps1190 m ≤ B := by
  exact epsilon1190_le_of_all_sums_le hB

lemma TailAdmissible.mono {m : ℕ} {Q Q' : Finset ℕ}
    (hQ : TailAdmissible m Q) (hsub : Q' ⊆ Q) :
    TailAdmissible m Q' := by
  rcases hQ with ⟨hTail, a, hDisj⟩
  constructor
  · intro q hq
    exact hTail q (hsub hq)
  · exact ⟨restrictAssignment a hsub, PairwiseDisjointResidues.mono hDisj hsub⟩

/-- Every bounded subfamily of a 1190 tail family is admissible for Problem 202. -/
lemma TailAdmissible.admissible_of_subset_le
    {m N : ℕ} {Q Q' : Finset ℕ}
    (hQ : TailAdmissible m Q) (hsub : Q' ⊆ Q)
    (hupper : ∀ q ∈ Q', q ≤ N) :
    Admissible N Q' := by
  rcases hQ with ⟨hTail, a, hDisj⟩
  constructor
  · intro q hq
    have hqpos : 1 ≤ q := Nat.succ_le_of_lt ((Nat.zero_le m).trans_lt (hTail q (hsub hq)))
    exact ⟨hqpos, hupper q hq⟩
  · exact ⟨restrictAssignment a hsub, PairwiseDisjointResidues.mono hDisj hsub⟩

/-- The counting function of any 1190 tail family is pointwise bounded by the
Erdős 202 extremal function. -/
lemma TailAdmissible.card_filter_le_f
    {m N : ℕ} {Q : Finset ℕ} (hQ : TailAdmissible m Q) :
    (Q.filter fun q => q ≤ N).card ≤ f N := by
  classical
  let Q' : Finset ℕ := Q.filter fun q => q ≤ N
  have hsub : Q' ⊆ Q := by
    intro q hq
    exact (Finset.mem_filter.1 hq).1
  have hupper : ∀ q ∈ Q', q ≤ N := by
    intro q hq
    exact (Finset.mem_filter.1 hq).2
  have hAdm : Admissible N Q' :=
    hQ.admissible_of_subset_le hsub hupper
  exact le_f_of_possibleCard ⟨Q', hAdm, rfl⟩

/-- Real-valued version of `TailAdmissible.card_filter_le_f`. -/
lemma TailAdmissible.card_filter_cast_le_f
    {m N : ℕ} {Q : Finset ℕ} (hQ : TailAdmissible m Q) :
    (((Q.filter fun q => q ≤ N).card : ℕ) : ℝ) ≤ (f N : ℝ) := by
  exact_mod_cast hQ.card_filter_le_f (N := N)

/-! ## Finite partial-summation bridge -/

/-- The finite counting function of a family of moduli. -/
noncomputable def tailCountingFunction (Q : Finset ℕ) (N : ℕ) : ℕ :=
  (Q.filter fun q => q ≤ N).card

lemma tailCountingFunction_le_f
    {m N : ℕ} {Q : Finset ℕ} (hQ : TailAdmissible m Q) :
    tailCountingFunction Q N ≤ f N := by
  simpa [tailCountingFunction] using hQ.card_filter_le_f (N := N)

/-! ## The real `sqrt(u log u)` scale used in the dyadic tail -/

/-- Real-variable version of the BFV exponent as a function of `u = log x`. -/
noncomputable def g1190 (u : ℝ) : ℝ :=
  Real.sqrt (u * Real.log u)

lemma Zscale_eq_g1190_log (N : ℕ) :
    Zscale N = g1190 (Real.log (N : ℝ)) := by
  simp [Zscale, g1190]

lemma g1190_mono_of_one_le {u v : ℝ}
    (hu : 1 ≤ u) (huv : u ≤ v) :
    g1190 u ≤ g1190 v := by
  have hlog : Real.log u ≤ Real.log v := by
    exact Real.log_le_log (zero_lt_one.trans_le hu) huv
  have hlog_nonneg : 0 ≤ Real.log u := Real.log_nonneg hu
  have hv_nonneg : 0 ≤ v := by linarith
  have hmul : u * Real.log u ≤ v * Real.log v :=
    mul_le_mul huv hlog hlog_nonneg hv_nonneg
  exact Real.sqrt_le_sqrt hmul

lemma g1190_mono_on_large :
    ∀ᶠ u0 : ℝ in atTop,
      ∀ u v : ℝ, u0 ≤ u → u ≤ v → g1190 u ≤ g1190 v := by
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with u0 hu0 u v huu huv
  exact g1190_mono_of_one_le (hu0.trans huu) huv

lemma g1190_four_pow_lower_of_one_le {u0 : ℝ}
    (hu0 : 1 ≤ u0) (j : ℕ) :
    (2 : ℝ) ^ j * g1190 u0 ≤ g1190 ((4 : ℝ) ^ j * u0) := by
  have hu0_pos : 0 < u0 := zero_lt_one.trans_le hu0
  have hu0_nonneg : 0 ≤ u0 := hu0_pos.le
  have hlogu_nonneg : 0 ≤ Real.log u0 := Real.log_nonneg hu0
  have hpow4_nonneg : 0 ≤ (4 : ℝ) ^ j := pow_nonneg (by norm_num) j
  have hpow4_pos : 0 < (4 : ℝ) ^ j := pow_pos (by norm_num) j
  have hpow4_ge_one : 1 ≤ (4 : ℝ) ^ j := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 4)
  have hprod_pos : 0 < (4 : ℝ) ^ j * u0 := mul_pos hpow4_pos hu0_pos
  have hu_le_prod : u0 ≤ (4 : ℝ) ^ j * u0 := by
    nlinarith
  have hlog_le : Real.log u0 ≤ Real.log ((4 : ℝ) ^ j * u0) :=
    Real.log_le_log hu0_pos hu_le_prod
  have harg_nonneg :
      0 ≤ ((4 : ℝ) ^ j * u0) * Real.log ((4 : ℝ) ^ j * u0) := by
    exact mul_nonneg (mul_nonneg hpow4_nonneg hu0_nonneg)
      (Real.log_nonneg (by nlinarith))
  have hx_nonneg : 0 ≤ (2 : ℝ) ^ j * g1190 u0 := by
    exact mul_nonneg (pow_nonneg (by norm_num) j) (Real.sqrt_nonneg _)
  rw [g1190]
  refine (Real.le_sqrt hx_nonneg harg_nonneg).2 ?_
  have hsq_g : (Real.sqrt (u0 * Real.log u0)) ^ 2 = u0 * Real.log u0 := by
    exact Real.sq_sqrt (mul_nonneg hu0_nonneg hlogu_nonneg)
  have hpow_sq : ((2 : ℝ) ^ j) * ((2 : ℝ) ^ j) = (4 : ℝ) ^ j := by
    rw [← mul_pow]
    norm_num
  have hinner :
      u0 * Real.log u0 ≤ u0 * Real.log ((4 : ℝ) ^ j * u0) :=
    mul_le_mul_of_nonneg_left hlog_le hu0_nonneg
  calc
    ((2 : ℝ) ^ j * Real.sqrt (u0 * Real.log u0)) ^ 2
        = ((2 : ℝ) ^ j * (2 : ℝ) ^ j) *
            (Real.sqrt (u0 * Real.log u0)) ^ 2 := by ring
    _ = (4 : ℝ) ^ j * (u0 * Real.log u0) := by
          rw [hpow_sq, hsq_g]
    _ ≤ (4 : ℝ) ^ j * (u0 * Real.log ((4 : ℝ) ^ j * u0)) :=
          mul_le_mul_of_nonneg_left hinner hpow4_nonneg
    _ = ((4 : ℝ) ^ j * u0) * Real.log ((4 : ℝ) ^ j * u0) := by ring

lemma g1190_four_pow_lower :
    ∀ᶠ u0 : ℝ in atTop,
      ∀ j : ℕ,
        (2 : ℝ) ^ j * g1190 u0 ≤ g1190 ((4 : ℝ) ^ j * u0) := by
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with u0 hu0 j
  exact g1190_four_pow_lower_of_one_le hu0 j

lemma eventually_Zscale_ge_const_1190 (A : ℝ) :
    ∀ᶠ N : ℕ in atTop, A ≤ Zscale N := by
  let B : ℝ := max A 1
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_right A 1)
  have hBnonneg : 0 ≤ B := hBpos.le
  filter_upwards [eventually_Mscale_ge 1 zero_lt_one,
      eventually_sqrt_loglog_ge (Real.sqrt B),
      Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with N hM hsqrt hNlarge_nat
  have hNlarge : Real.exp 1 < (N : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hNlarge_nat)
  have hNpos : 0 < (N : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlog_gt_one : 1 < Real.log (N : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
  have hloglog_pos : 0 < Real.log (Real.log (N : ℝ)) :=
    Real.log_pos hlog_gt_one
  have hloglog_nonneg : 0 ≤ Real.log (Real.log (N : ℝ)) := hloglog_pos.le
  have hsq :
      (Real.sqrt B) ^ 2 ≤
        (Real.sqrt (Real.log (Real.log (N : ℝ)))) ^ 2 :=
    pow_le_pow_left₀ (Real.sqrt_nonneg B) hsqrt 2
  have hloglog_ge_B : B ≤ Real.log (Real.log (N : ℝ)) := by
    simpa [Real.sq_sqrt hBnonneg, Real.sq_sqrt hloglog_nonneg] using hsq
  have hZ := Mscale_mul_loglog_eq_Zscale hNlarge
  have hB_le_Z : B ≤ Zscale N := by
    rw [← hZ]
    nlinarith [hM, hloglog_ge_B, hBpos.le]
  exact (le_max_left A 1).trans hB_le_Z

lemma eventually_Lscale_neg_le_const_1190 {A c : ℝ}
    (hA : 0 < A) (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, Lscale (-A) N ≤ c := by
  filter_upwards [eventually_Zscale_ge_const_1190 ((-Real.log c) / A)] with N hZ
  rw [Lscale]
  exact (Real.le_log_iff_exp_le hc).1 (by
    have hmul : -Real.log c ≤ A * Zscale N := by
      simpa [mul_comm] using (div_le_iff₀ hA).1 hZ
    nlinarith)

lemma log_four_add_two_log_nat_succ_le_const_sqrt (k : ℕ) :
    Real.log 4 + 2 * Real.log (((k + 1 : ℕ) : ℝ)) ≤
      (Real.log 4 + 4) * Real.sqrt (((k + 1 : ℕ) : ℝ)) := by
  have hn1 : 1 ≤ (((k + 1 : ℕ) : ℝ)) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
  have hsqrt_ge_one : 1 ≤ Real.sqrt (((k + 1 : ℕ) : ℝ)) := by
    rw [Real.one_le_sqrt]
    exact hn1
  have hlog4_nonneg : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hlog4 :
      Real.log 4 ≤ Real.log 4 * Real.sqrt (((k + 1 : ℕ) : ℝ)) := by
    simpa using mul_le_mul_of_nonneg_left hsqrt_ge_one hlog4_nonneg
  have hlog_le :
      Real.log (((k + 1 : ℕ) : ℝ)) ≤
        2 * Real.sqrt (((k + 1 : ℕ) : ℝ)) := by
    have h :=
      Real.log_natCast_le_rpow_div (k + 1)
        (show 0 < (1 / 2 : ℝ) by norm_num)
    calc
      Real.log (((k + 1 : ℕ) : ℝ))
          ≤ (((k + 1 : ℕ) : ℝ) ^ (1 / 2 : ℝ)) / (1 / 2 : ℝ) := h
      _ = 2 * Real.sqrt (((k + 1 : ℕ) : ℝ)) := by
            rw [Real.sqrt_eq_rpow]
            ring
  calc
    Real.log 4 + 2 * Real.log (((k + 1 : ℕ) : ℝ))
        ≤ Real.log 4 * Real.sqrt (((k + 1 : ℕ) : ℝ)) +
            2 * (2 * Real.sqrt (((k + 1 : ℕ) : ℝ))) := by
          exact add_le_add hlog4 (mul_le_mul_of_nonneg_left hlog_le (by norm_num))
    _ = (Real.log 4 + 4) * Real.sqrt (((k + 1 : ℕ) : ℝ)) := by ring

lemma Zscale_dyadic_endpoint_ge_const_sqrt
    (C : ℝ) (hC : 0 < C) :
    ∀ᶠ m : ℕ in atTop,
      ∀ k : ℕ,
        C * Real.sqrt (((k + 1 : ℕ) : ℝ)) ≤
          Zscale ((2 ^ (k + 1)) * m) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  filter_upwards [tendsto_loglog_nat_atTop.eventually_ge_atTop (C ^ 2 / Real.log 2),
      Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with m hloglog_m hmlarge_nat k
  have hmlarge : Real.exp 1 < (m : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hmlarge_nat)
  have hmpos : 0 < (m : ℝ) := (Real.exp_pos 1).trans hmlarge
  have hlogm_gt_one : 1 < Real.log (m : ℝ) :=
    (Real.lt_log_iff_exp_lt hmpos).2 hmlarge
  have hlogm_pos : 0 < Real.log (m : ℝ) := zero_lt_one.trans hlogm_gt_one
  let N : ℕ := (2 ^ (k + 1)) * m
  have hN_cast : (N : ℝ) = ((2 : ℝ) ^ (k + 1)) * (m : ℝ) := by
    simp [N]
  have hpow_pos : 0 < ((2 : ℝ) ^ (k + 1)) := pow_pos (by norm_num) _
  have hNpos : 0 < (N : ℝ) := by
    rw [hN_cast]
    exact mul_pos hpow_pos hmpos
  have hlogN_eq :
      Real.log (N : ℝ) = ((k + 1 : ℕ) : ℝ) * Real.log 2 + Real.log (m : ℝ) := by
    rw [hN_cast, Real.log_mul hpow_pos.ne' hmpos.ne', Real.log_pow]
  have hlogN_ge :
      ((k + 1 : ℕ) : ℝ) * Real.log 2 ≤ Real.log (N : ℝ) := by
    rw [hlogN_eq]
    exact le_add_of_nonneg_right hlogm_pos.le
  have hm_le_N_nat : m ≤ N := by
    have hpow_nat : 1 ≤ 2 ^ (k + 1) := one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 2)
    dsimp [N]
    nlinarith
  have hlogm_le_logN : Real.log (m : ℝ) ≤ Real.log (N : ℝ) := by
    exact Real.log_le_log hmpos (by exact_mod_cast hm_le_N_nat)
  have hloglogN_ge :
      C ^ 2 / Real.log 2 ≤ Real.log (Real.log (N : ℝ)) := by
    exact hloglog_m.trans (Real.log_le_log hlogm_pos hlogm_le_logN)
  have hleft_nonneg : 0 ≤ ((k + 1 : ℕ) : ℝ) * Real.log 2 := by positivity
  have hright_nonneg : 0 ≤ C ^ 2 / Real.log 2 := by positivity
  have hlogN_nonneg : 0 ≤ Real.log (N : ℝ) := hleft_nonneg.trans hlogN_ge
  have hprod_ge :
      C ^ 2 * (((k + 1 : ℕ) : ℝ)) ≤
        Real.log (N : ℝ) * Real.log (Real.log (N : ℝ)) := by
    have hmul := mul_le_mul hlogN_ge hloglogN_ge hright_nonneg hlogN_nonneg
    calc
      C ^ 2 * (((k + 1 : ℕ) : ℝ))
          = ((k + 1 : ℕ) : ℝ) * Real.log 2 * (C ^ 2 / Real.log 2) := by
            rw [div_eq_mul_inv]
            calc
              C ^ 2 * (((k + 1 : ℕ) : ℝ))
                  = C ^ 2 * (((k + 1 : ℕ) : ℝ)) *
                    (Real.log 2 * (Real.log 2)⁻¹) := by
                    rw [mul_inv_cancel₀ hlog2.ne']
                    ring
              _ = ((k + 1 : ℕ) : ℝ) * Real.log 2 * (C ^ 2 * (Real.log 2)⁻¹) := by
                    ring
      _ ≤ Real.log (N : ℝ) * Real.log (Real.log (N : ℝ)) := hmul
  have harg_nonneg : 0 ≤ Real.log (N : ℝ) * Real.log (Real.log (N : ℝ)) := by
    exact (mul_nonneg (sq_nonneg C) (by positivity)).trans hprod_ge
  have hleft_sqrt_nonneg : 0 ≤ C * Real.sqrt (((k + 1 : ℕ) : ℝ)) := by positivity
  rw [Zscale]
  refine (Real.le_sqrt hleft_sqrt_nonneg harg_nonneg).2 ?_
  calc
    (C * Real.sqrt (((k + 1 : ℕ) : ℝ))) ^ 2
        = C ^ 2 * (((k + 1 : ℕ) : ℝ)) := by
            rw [mul_pow, Real.sq_sqrt (by positivity)]
    _ ≤ Real.log (N : ℝ) * Real.log (Real.log (N : ℝ)) := hprod_ge

lemma Zscale_le_dyadic_endpoint :
    ∀ᶠ m : ℕ in atTop,
      ∀ k : ℕ, Zscale m ≤ Zscale ((2 ^ (k + 1)) * m) := by
  filter_upwards [Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with m hmlarge_nat k
  have hmlarge : Real.exp 1 < (m : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hmlarge_nat)
  have hmpos : 0 < (m : ℝ) := (Real.exp_pos 1).trans hmlarge
  have hlogm_ge_one : 1 ≤ Real.log (m : ℝ) := by
    exact ((Real.lt_log_iff_exp_lt hmpos).2 hmlarge).le
  let N : ℕ := (2 ^ (k + 1)) * m
  have hm_le_N_nat : m ≤ N := by
    have hpow_nat : 1 ≤ 2 ^ (k + 1) := one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 2)
    dsimp [N]
    nlinarith
  have hlog_le : Real.log (m : ℝ) ≤ Real.log (N : ℝ) :=
    Real.log_le_log hmpos (by exact_mod_cast hm_le_N_nat)
  rw [Zscale_eq_g1190_log m, Zscale_eq_g1190_log N]
  exact g1190_mono_of_one_le hlogm_ge_one hlog_le

lemma dyadic_tail_exponent_gap
    (a b : ℝ) (hb : 0 < b) (hba : b < a) :
    ∀ᶠ m : ℕ in atTop,
      ∀ k : ℕ,
        Real.log 4 + 2 * Real.log (((k + 1 : ℕ) : ℝ)) + b * Zscale m
          ≤ a * Zscale ((2 ^ (k + 1)) * m) := by
  let C0 : ℝ := Real.log 4 + 4
  have hgap : 0 < a - b := sub_pos.2 hba
  have hC0pos : 0 < C0 := by
    dsimp [C0]
    nlinarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)]
  have hCpos : 0 < C0 / (a - b) := div_pos hC0pos hgap
  filter_upwards [Zscale_dyadic_endpoint_ge_const_sqrt (C0 / (a - b)) hCpos,
      Zscale_le_dyadic_endpoint] with m hsqrt hmono k
  let N : ℕ := (2 ^ (k + 1)) * m
  have hpoly := log_four_add_two_log_nat_succ_le_const_sqrt k
  have hgapZ :
      C0 * Real.sqrt (((k + 1 : ℕ) : ℝ)) ≤ (a - b) * Zscale N := by
    have hmul := mul_le_mul_of_nonneg_left (hsqrt k) hgap.le
    calc
      C0 * Real.sqrt (((k + 1 : ℕ) : ℝ))
          = (a - b) * ((C0 / (a - b)) * Real.sqrt (((k + 1 : ℕ) : ℝ))) := by
            rw [div_eq_mul_inv]
            calc
              C0 * Real.sqrt (((k + 1 : ℕ) : ℝ))
                  = C0 * Real.sqrt (((k + 1 : ℕ) : ℝ)) * ((a - b) * (a - b)⁻¹) := by
                    rw [mul_inv_cancel₀ hgap.ne']
                    ring
              _ = (a - b) * ((C0 * (a - b)⁻¹) *
                    Real.sqrt (((k + 1 : ℕ) : ℝ))) := by
                    ring
      _ ≤ (a - b) * Zscale N := hmul
  have hbmono : b * Zscale m ≤ b * Zscale N :=
    mul_le_mul_of_nonneg_left (hmono k) hb.le
  have hpolyC :
      Real.log 4 + 2 * Real.log (((k + 1 : ℕ) : ℝ)) ≤
        C0 * Real.sqrt (((k + 1 : ℕ) : ℝ)) := by
    simpa [C0] using hpoly
  calc
    Real.log 4 + 2 * Real.log (((k + 1 : ℕ) : ℝ)) + b * Zscale m
        ≤ (a - b) * Zscale N + b * Zscale N :=
          add_le_add (hpolyC.trans hgapZ) hbmono
    _ = a * Zscale N := by ring_nf

lemma half_inv_sq_succ_le_telescope (k : ℕ) :
    1 / (2 * ((((k + 1 : ℕ) : ℝ) ^ 2))) ≤
      1 / (((k + 1 : ℕ) : ℝ)) - 1 / (((k + 2 : ℕ) : ℝ)) := by
  have hk1 : 0 < (((k + 1 : ℕ) : ℝ)) := by positivity
  have hk2 : 0 < (((k + 2 : ℕ) : ℝ)) := by positivity
  have hk1_ge : 1 ≤ (((k + 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
  have hkdiff : (((k + 2 : ℕ) : ℝ)) - (((k + 1 : ℕ) : ℝ)) = 1 := by
    norm_num
  have hkle : (((k + 2 : ℕ) : ℝ)) ≤ 2 * (((k + 1 : ℕ) : ℝ)) := by
    nlinarith
  field_simp [hk1.ne', hk2.ne', (show (2 : ℝ) ≠ 0 by norm_num)]
  nlinarith

lemma sum_half_inv_sq_succ_le_one_sub_inv_succ (K : ℕ) :
    (∑ k ∈ Finset.range K,
      1 / (2 * ((((k + 1 : ℕ) : ℝ) ^ 2)))) ≤
        1 - 1 / (((K + 1 : ℕ) : ℝ)) := by
  induction K with
  | zero =>
      simp
  | succ K ih =>
      rw [Finset.sum_range_succ]
      calc
        (∑ k ∈ Finset.range K, 1 / (2 * ↑(k + 1) ^ 2)) +
            1 / (2 * ↑(K + 1) ^ 2)
            ≤ (1 - 1 / (((K + 1 : ℕ) : ℝ))) +
                (1 / (((K + 1 : ℕ) : ℝ)) - 1 / (((K + 2 : ℕ) : ℝ))) := by
              exact add_le_add ih (half_inv_sq_succ_le_telescope K)
        _ = 1 - 1 / (((K + 2 : ℕ) : ℝ)) := by ring

lemma sum_half_inv_sq_succ_le_one (K : ℕ) :
    (∑ k ∈ Finset.range K,
      1 / (2 * ((((k + 1 : ℕ) : ℝ) ^ 2)))) ≤ 1 := by
  have h := sum_half_inv_sq_succ_le_one_sub_inv_succ K
  have hnonneg : 0 ≤ 1 / (((K + 1 : ℕ) : ℝ)) := by positivity
  linarith

lemma dyadic_L_tail_term_le_half_inv_sq
    (a b : ℝ) (hb : 0 < b) (hba : b < a) :
    ∀ᶠ m : ℕ in atTop,
      ∀ k : ℕ,
        2 * Lscale (-a) ((2 ^ (k + 1)) * m) ≤
          (1 / (2 * ((((k + 1 : ℕ) : ℝ) ^ 2))) * Lscale (-b) m) := by
  filter_upwards [dyadic_tail_exponent_gap a b hb hba] with m hgap_exp k
  let N : ℕ := (2 ^ (k + 1)) * m
  let n : ℝ := (((k + 1 : ℕ) : ℝ))
  have hnpos : 0 < n := by positivity
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
    ring
  have hgap :
      Real.log 4 + 2 * Real.log n + b * Zscale m ≤ a * Zscale N := by
    simpa [N, n] using hgap_exp k
  have hineq :
      Real.log 2 - a * Zscale N ≤
        -Real.log 2 - 2 * Real.log n - b * Zscale m := by
    nlinarith [hgap, hlog4]
  have hleft :
      2 * Lscale (-a) N = Real.exp (Real.log 2 - a * Zscale N) := by
    rw [Lscale]
    calc
      2 * Real.exp ((-a) * Zscale N)
          = Real.exp (Real.log 2) * Real.exp ((-a) * Zscale N) := by
              rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      _ = Real.exp (Real.log 2 + (-a) * Zscale N) := by
              rw [Real.exp_add]
      _ = Real.exp (Real.log 2 - a * Zscale N) := by ring_nf
  have hexp_neg_log_two : Real.exp (-Real.log 2) = (1 / 2 : ℝ) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hexp_two_log : Real.exp (2 * Real.log n) = n ^ 2 := by
    have htwo : (2 : ℝ) * Real.log n = (2 : ℕ) * Real.log n := by norm_num
    rw [htwo, Real.exp_nat_mul, Real.exp_log hnpos]
  have hexp_neg_two_log : Real.exp (-2 * Real.log n) = (n ^ 2)⁻¹ := by
    rw [show -2 * Real.log n = -(2 * Real.log n) by ring, Real.exp_neg, hexp_two_log]
  have hright :
      Real.exp (-Real.log 2 - 2 * Real.log n - b * Zscale m) =
        (1 / (2 * n ^ 2)) * Lscale (-b) m := by
    rw [Lscale]
    calc
      Real.exp (-Real.log 2 - 2 * Real.log n - b * Zscale m)
          = Real.exp (-Real.log 2) * Real.exp (-2 * Real.log n) *
              Real.exp ((-b) * Zscale m) := by
                rw [← Real.exp_add, ← Real.exp_add]
                ring_nf
      _ = (1 / 2) * (n ^ 2)⁻¹ * Real.exp ((-b) * Zscale m) := by
                rw [hexp_neg_log_two, hexp_neg_two_log]
      _ = (1 / (2 * n ^ 2)) * Real.exp ((-b) * Zscale m) := by
                field_simp [hnpos.ne']
  calc
    2 * Lscale (-a) ((2 ^ (k + 1)) * m)
        = Real.exp (Real.log 2 - a * Zscale N) := by simpa [N] using hleft
    _ ≤ Real.exp (-Real.log 2 - 2 * Real.log n - b * Zscale m) :=
        Real.exp_le_exp.2 hineq
    _ = (1 / (2 * ((((k + 1 : ℕ) : ℝ) ^ 2))) * Lscale (-b) m) := by
        simpa [n] using hright

/-- Pure dyadic tail estimate for the `L` scale.  This is the finite-sum
replacement for the partial-summation tail used in the PDF proof of
Corollary 1.2. -/
theorem dyadic_L_tail_of_gap
    (a b : ℝ) (hb : 0 < b) (hba : b < a) :
    ∀ᶠ m : ℕ in atTop,
      ∀ K : ℕ,
        (∑ k ∈ Finset.range K,
          2 * Lscale (-a) ((2 ^ (k + 1)) * m))
          ≤ Lscale (-b) m := by
  filter_upwards [dyadic_L_tail_term_le_half_inv_sq a b hb hba] with m hterm K
  calc
    (∑ k ∈ Finset.range K, 2 * Lscale (-a) ((2 ^ (k + 1)) * m))
        ≤ ∑ k ∈ Finset.range K,
            (1 / (2 * ((((k + 1 : ℕ) : ℝ) ^ 2))) * Lscale (-b) m) := by
          exact Finset.sum_le_sum (by
            intro k hk
            exact hterm k)
    _ = (∑ k ∈ Finset.range K,
            1 / (2 * ((((k + 1 : ℕ) : ℝ) ^ 2)))) * Lscale (-b) m := by
          rw [Finset.sum_mul]
    _ ≤ 1 * Lscale (-b) m := by
          exact mul_le_mul_of_nonneg_right
            (sum_half_inv_sq_succ_le_one K) (Lscale_nonneg (-b) m)
    _ = Lscale (-b) m := by ring

theorem dyadic_upper_tail_for_1190
    (ε : ℝ) (hε : 0 < ε) (hεsmall : ε ≤ 1 / 2) :
    ∀ᶠ m : ℕ in atTop,
      ∀ K : ℕ,
        (∑ k ∈ Finset.range K,
          2 * Lscale (-(1 - ε / 4)) ((2 ^ (k + 1)) * m))
          ≤ Lscale (-(1 - ε)) m := by
  have hb : 0 < 1 - ε := by linarith
  have hba : 1 - ε < 1 - ε / 4 := by linarith
  simpa using dyadic_L_tail_of_gap (a := 1 - ε / 4) (b := 1 - ε) hb hba

/-! ## Dyadic finite decomposition API -/

/-- The part of `Q` in the dyadic interval `(2^k m, 2^(k+1)m]`. -/
def dyadicBlock (m k : ℕ) (Q : Finset ℕ) : Finset ℕ :=
  Q.filter fun q => (2 ^ k) * m < q ∧ q ≤ (2 ^ (k + 1)) * m

lemma mem_dyadicBlock {m k : ℕ} {Q : Finset ℕ} {q : ℕ} :
    q ∈ dyadicBlock m k Q ↔
      q ∈ Q ∧ (2 ^ k) * m < q ∧ q ≤ (2 ^ (k + 1)) * m := by
  simp [dyadicBlock]

lemma dyadicBlock_subset (m k : ℕ) (Q : Finset ℕ) :
    dyadicBlock m k Q ⊆ Q := by
  intro q hq
  exact (mem_dyadicBlock.1 hq).1

lemma TailAdmissible.dyadicBlock_card_le_f
    {m k : ℕ} {Q : Finset ℕ} (hQ : TailAdmissible m Q) :
    (dyadicBlock m k Q).card ≤ f ((2 ^ (k + 1)) * m) := by
  have hAdm : Admissible ((2 ^ (k + 1)) * m) (dyadicBlock m k Q) :=
    hQ.admissible_of_subset_le (dyadicBlock_subset m k Q) (by
      intro q hq
      exact (mem_dyadicBlock.1 hq).2.2)
  exact le_f_of_possibleCard ⟨dyadicBlock m k Q, hAdm, rfl⟩

lemma reciprocalSum_le_card_div_of_lower_lt
    {A : ℕ} {Q : Finset ℕ}
    (hApos : 0 < A)
    (hlower : ∀ q ∈ Q, A < q) :
    reciprocalSum Q ≤ (Q.card : ℝ) / (A : ℝ) := by
  classical
  have hApos_real : 0 < (A : ℝ) := by exact_mod_cast hApos
  unfold reciprocalSum
  calc
    ∑ q ∈ Q, (q : ℝ)⁻¹
        ≤ ∑ q ∈ Q, (A : ℝ)⁻¹ := by
            refine Finset.sum_le_sum ?_
            intro q hq
            have hqpos_nat : 0 < q := hApos.trans (hlower q hq)
            have hqpos : 0 < (q : ℝ) := by exact_mod_cast hqpos_nat
            have hAq : (A : ℝ) ≤ (q : ℝ) := by exact_mod_cast (hlower q hq).le
            exact (inv_le_inv₀ hqpos hApos_real).2 hAq
    _ = (Q.card : ℝ) / (A : ℝ) := by
            simp [div_eq_mul_inv]

lemma dyadicBlock_reciprocalSum_le_f_div
    {m k : ℕ} {Q : Finset ℕ}
    (hm : 0 < m) (hQ : TailAdmissible m Q) :
    reciprocalSum (dyadicBlock m k Q) ≤
      (f ((2 ^ (k + 1)) * m) : ℝ) / (((2 ^ k) * m : ℕ) : ℝ) := by
  have hApos : 0 < (2 ^ k) * m := Nat.mul_pos (pow_pos (by norm_num) k) hm
  calc
    reciprocalSum (dyadicBlock m k Q)
        ≤ ((dyadicBlock m k Q).card : ℝ) / (((2 ^ k) * m : ℕ) : ℝ) := by
            exact reciprocalSum_le_card_div_of_lower_lt hApos (by
              intro q hq
              exact (mem_dyadicBlock.1 hq).2.1)
    _ ≤ (f ((2 ^ (k + 1)) * m) : ℝ) / (((2 ^ k) * m : ℕ) : ℝ) := by
            have hden : 0 ≤ (((2 ^ k) * m : ℕ) : ℝ) := by positivity
            exact div_le_div_of_nonneg_right
              (by exact_mod_cast hQ.dyadicBlock_card_le_f (k := k)) hden

lemma dyadic_endpoint_cast_eq_two_mul (m k : ℕ) :
    (((2 ^ (k + 1)) * m : ℕ) : ℝ) =
      2 * (((2 ^ k) * m : ℕ) : ℝ) := by
  norm_num [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  ring

lemma dyadicBlock_reciprocalSum_le_Lscale_of_f_bound
    {m k : ℕ} {Q : Finset ℕ} {a : ℝ}
    (hm : 0 < m) (hQ : TailAdmissible m Q)
    (hf :
      (f ((2 ^ (k + 1)) * m) : ℝ) ≤
        (((2 ^ (k + 1)) * m : ℕ) : ℝ) *
          Lscale (-a) ((2 ^ (k + 1)) * m)) :
    reciprocalSum (dyadicBlock m k Q) ≤
      2 * Lscale (-a) ((2 ^ (k + 1)) * m) := by
  have hdenpos_nat : 0 < (2 ^ k) * m :=
    Nat.mul_pos (pow_pos (by norm_num) k) hm
  have hdenpos : 0 < (((2 ^ k) * m : ℕ) : ℝ) := by exact_mod_cast hdenpos_nat
  calc
    reciprocalSum (dyadicBlock m k Q)
        ≤ (f ((2 ^ (k + 1)) * m) : ℝ) /
            (((2 ^ k) * m : ℕ) : ℝ) :=
          dyadicBlock_reciprocalSum_le_f_div hm hQ
    _ ≤ ((((2 ^ (k + 1)) * m : ℕ) : ℝ) *
            Lscale (-a) ((2 ^ (k + 1)) * m)) /
            (((2 ^ k) * m : ℕ) : ℝ) := by
          exact div_le_div_of_nonneg_right hf hdenpos.le
    _ = 2 * Lscale (-a) ((2 ^ (k + 1)) * m) := by
          rw [dyadic_endpoint_cast_eq_two_mul]
          field_simp [hdenpos.ne']

lemma dyadicBlock_mono_right {m k : ℕ} {Q Q' : Finset ℕ}
    (hsub : Q' ⊆ Q) :
    dyadicBlock m k Q' ⊆ dyadicBlock m k Q := by
  intro q hq
  rcases mem_dyadicBlock.1 hq with ⟨hqQ', hlo, hup⟩
  exact mem_dyadicBlock.2 ⟨hsub hqQ', hlo, hup⟩

lemma reciprocalSum_le_sum_dyadicBlocks_of_cover
    {m K : ℕ} {Q : Finset ℕ}
    (hQ : TailAdmissible m Q)
    (hcover : ∀ q ∈ Q, q ≤ (2 ^ K) * m) :
    reciprocalSum Q ≤
      (∑ k ∈ Finset.range K, reciprocalSum (dyadicBlock m k Q)) := by
  classical
  induction K generalizing Q with
  | zero =>
      have hQempty : Q = ∅ := by
        ext q
        constructor
        · intro hq
          have htail := hQ.1 q hq
          have hcov := hcover q hq
          simp at hcov
          omega
        · intro hq
          simp at hq
      simp [hQempty, reciprocalSum_empty]
  | succ K ih =>
      let Low : Finset ℕ := Q.filter fun q => q ≤ (2 ^ K) * m
      let High : Finset ℕ := Q.filter fun q => ¬ q ≤ (2 ^ K) * m
      have hsplit :
          reciprocalSum Q = reciprocalSum Low + reciprocalSum High := by
        dsimp [Low, High]
        exact (reciprocalSum_filter_add_filter_not Q
          (fun q => q ≤ (2 ^ K) * m)).symm
      have hLowTail : TailAdmissible m Low :=
        hQ.mono (by
          intro q hq
          exact (Finset.mem_filter.1 hq).1)
      have hLowCover : ∀ q ∈ Low, q ≤ (2 ^ K) * m := by
        intro q hq
        exact (Finset.mem_filter.1 hq).2
      have hLowBound :
          reciprocalSum Low ≤
            ∑ k ∈ Finset.range K, reciprocalSum (dyadicBlock m k Low) :=
        ih hLowTail hLowCover
      have hLowBlocks :
          (∑ k ∈ Finset.range K, reciprocalSum (dyadicBlock m k Low)) ≤
            ∑ k ∈ Finset.range K, reciprocalSum (dyadicBlock m k Q) := by
        refine Finset.sum_le_sum ?_
        intro k hk
        exact reciprocalSum_mono (dyadicBlock_mono_right (m := m) (k := k) (by
          intro q hq
          exact (Finset.mem_filter.1 hq).1))
      have hHighSubset : High ⊆ dyadicBlock m K Q := by
        intro q hq
        have hqQ : q ∈ Q := (Finset.mem_filter.1 hq).1
        have hnot : ¬ q ≤ (2 ^ K) * m := (Finset.mem_filter.1 hq).2
        exact mem_dyadicBlock.2
          ⟨hqQ, Nat.lt_of_not_ge hnot, hcover q hqQ⟩
      have hHighBound :
          reciprocalSum High ≤ reciprocalSum (dyadicBlock m K Q) :=
        reciprocalSum_mono hHighSubset
      calc
        reciprocalSum Q
            = reciprocalSum Low + reciprocalSum High := hsplit
        _ ≤ (∑ k ∈ Finset.range K, reciprocalSum (dyadicBlock m k Low)) +
              reciprocalSum (dyadicBlock m K Q) :=
            add_le_add hLowBound hHighBound
        _ ≤ (∑ k ∈ Finset.range K, reciprocalSum (dyadicBlock m k Q)) +
              reciprocalSum (dyadicBlock m K Q) :=
            by
              simpa [add_comm, add_left_comm, add_assoc] using
                add_le_add_right hLowBlocks (reciprocalSum (dyadicBlock m K Q))
        _ = ∑ k ∈ Finset.range (K + 1), reciprocalSum (dyadicBlock m k Q) := by
            rw [Finset.sum_range_succ]

lemma exists_dyadic_cover_cutoff
    {m : ℕ} (hm : 1 ≤ m) (Q : Finset ℕ) :
    ∃ K : ℕ, ∀ q ∈ Q, q ≤ (2 ^ K) * m := by
  classical
  refine ⟨Q.sup (fun q => Nat.log 2 q + 1), ?_⟩
  intro q hq
  have hlog_le : Nat.log 2 q + 1 ≤ Q.sup (fun q => Nat.log 2 q + 1) :=
    Finset.le_sup (f := fun q => Nat.log 2 q + 1) hq
  have hq_lt_pow : q < 2 ^ (Nat.log 2 q).succ :=
    Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) q
  have hpow_le :
      2 ^ (Nat.log 2 q).succ ≤
        2 ^ Q.sup (fun q => Nat.log 2 q + 1) :=
    Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hlog_le
  have hq_le_pow : q ≤ 2 ^ Q.sup (fun q => Nat.log 2 q + 1) :=
    hq_lt_pow.le.trans hpow_le
  exact hq_le_pow.trans (by
    have hpow_nonneg : 0 ≤ 2 ^ Q.sup (fun q => Nat.log 2 q + 1) := Nat.zero_le _
    nlinarith [hm])

lemma reciprocalSum_le_dyadic_L_tail_of_cover
    {m K : ℕ} {Q : Finset ℕ} {a b : ℝ}
    (hm : 0 < m) (hQ : TailAdmissible m Q)
    (hcover : ∀ q ∈ Q, q ≤ (2 ^ K) * m)
    (hf :
      ∀ k ∈ Finset.range K,
        (f ((2 ^ (k + 1)) * m) : ℝ) ≤
          (((2 ^ (k + 1)) * m : ℕ) : ℝ) *
            Lscale (-a) ((2 ^ (k + 1)) * m))
    (htail :
      (∑ k ∈ Finset.range K, 2 * Lscale (-a) ((2 ^ (k + 1)) * m)) ≤
        Lscale (-b) m) :
    reciprocalSum Q ≤ Lscale (-b) m := by
  calc
    reciprocalSum Q
        ≤ ∑ k ∈ Finset.range K, reciprocalSum (dyadicBlock m k Q) :=
          reciprocalSum_le_sum_dyadicBlocks_of_cover hQ hcover
    _ ≤ ∑ k ∈ Finset.range K, 2 * Lscale (-a) ((2 ^ (k + 1)) * m) := by
          refine Finset.sum_le_sum ?_
          intro k hk
          exact dyadicBlock_reciprocalSum_le_Lscale_of_f_bound hm hQ (hf k hk)
    _ ≤ Lscale (-b) m := htail

lemma reciprocalSum_le_dyadic_L_tail
    {m : ℕ} {Q : Finset ℕ} {a b : ℝ}
    (hm : 1 ≤ m) (hQ : TailAdmissible m Q)
    (hf :
      ∀ N : ℕ, m ≤ N →
        (f N : ℝ) ≤ (N : ℝ) * Lscale (-a) N)
    (htail :
      ∀ K : ℕ,
        (∑ k ∈ Finset.range K, 2 * Lscale (-a) ((2 ^ (k + 1)) * m)) ≤
          Lscale (-b) m) :
    reciprocalSum Q ≤ Lscale (-b) m := by
  rcases exists_dyadic_cover_cutoff hm Q with ⟨K, hcover⟩
  exact reciprocalSum_le_dyadic_L_tail_of_cover (Nat.pos_of_ne_zero (by omega)) hQ hcover
    (by
      intro k _hk
      apply hf
      have hm_le : m ≤ (2 ^ (k + 1)) * m := by
        have hpow : 1 ≤ 2 ^ (k + 1) := one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 2)
        nlinarith [hm, hpow]
      exact hm_le)
    (htail K)

/-- Upper half of Problem 1190, reduced to the pure real-analysis dyadic
tail estimate.  The missing work after this theorem is exactly to prove the
`htail` hypothesis from the `L`-scale algebra. -/
theorem eps1190_upper_from_dyadic_tail
    (ε : ℝ) (hε : 0 < ε)
    (htail :
      ∀ᶠ m : ℕ in atTop,
        ∀ K : ℕ,
          (∑ k ∈ Finset.range K,
            2 * Lscale (-(1 - ε / 4)) ((2 ^ (k + 1)) * m))
            ≤ Lscale (-(1 - ε)) m) :
    ∀ᶠ m : ℕ in atTop,
      eps1190 m ≤ Lscale (-(1 - ε)) m := by
  have hδ : 0 < ε / 4 := by positivity
  rcases eventually_atTop.1 (erdos202_upper_bound_from_inputs (ε / 4) hδ) with
    ⟨N₀, h202⟩
  filter_upwards [Filter.eventually_ge_atTop (max 1 N₀), htail] with m hm htail_m
  have hm1 : 1 ≤ m := le_of_max_le_left hm
  have hmN₀ : N₀ ≤ m := le_of_max_le_right hm
  refine eps1190_le_of_all_sums_le ?_
  intro Q hQ
  exact reciprocalSum_le_dyadic_L_tail (m := m) (Q := Q)
    (a := 1 - ε / 4) (b := 1 - ε) hm1 hQ
    (by
      intro N hN
      exact h202 N (hmN₀.trans hN))
    htail_m

/-- Family-level dyadic upper bound for Problem 1190. -/
theorem recipSum_le_dyadic_tail
    (ε : ℝ) (hε : 0 < ε) (hεsmall : ε ≤ 1 / 2) :
    ∀ᶠ m : ℕ in atTop,
      ∀ Q : Finset ℕ,
        AdmissibleAbove m Q →
        recipSum Q ≤ Lscale (-(1 - ε)) m := by
  have hδ : 0 < ε / 4 := by positivity
  rcases eventually_atTop.1 (erdos202_upper_bound_from_inputs (ε / 4) hδ) with
    ⟨N₀, h202⟩
  filter_upwards [Filter.eventually_ge_atTop (max 1 N₀),
      dyadic_upper_tail_for_1190 ε hε hεsmall] with m hm htail Q hQ
  have hm1 : 1 ≤ m := le_of_max_le_left hm
  have hmN₀ : N₀ ≤ m := le_of_max_le_right hm
  exact reciprocalSum_le_dyadic_L_tail (m := m) (Q := Q)
    (a := 1 - ε / 4) (b := 1 - ε) hm1 hQ
    (by
      intro N hN
      exact h202 N (hmN₀.trans hN))
    htail

/-- Upper half of Erdős 1190. -/
theorem eps1190_upper (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop,
      eps1190 m ≤ Lscale (-(1 - ε)) m := by
  let η : ℝ := min ε (1 / 2)
  have hηpos : 0 < η := lt_min hε (by norm_num)
  have hηsmall : η ≤ 1 / 2 := min_le_right ε (1 / 2 : ℝ)
  have hηleε : η ≤ ε := min_le_left ε (1 / 2 : ℝ)
  have hηupper :
      ∀ᶠ m : ℕ in atTop,
        eps1190 m ≤ Lscale (-(1 - η)) m :=
    eps1190_upper_from_dyadic_tail η hηpos
      (dyadic_upper_tail_for_1190 η hηpos hηsmall)
  filter_upwards [hηupper] with m hm
  exact hm.trans (Lscale_mono_in_alpha (N := m) (by linarith : -(1 - η) ≤ -(1 - ε)))

/-- The 1190 corollary reduces to bounding reciprocal sums using the 202
counting function.  The analytic tail estimate needed to finish Corollary 1.2
is the standard partial-summation/integral estimate stated in the PDF:
`∫_m^∞ dt / (t · L(β,t)) = L(-β+o(1),m)`.

This file keeps the statement layer and the finite bridge axiom-free; the
full asymptotic theorem is added once that analytic estimate is formalized. -/
def Erdos1190BridgeReady : Prop :=
  ∀ m N : ℕ, ∀ Q : Finset ℕ,
    TailAdmissible m Q →
    tailCountingFunction Q N ≤ f N

theorem erdos1190_bridge_ready : Erdos1190BridgeReady := by
  intro m N Q hQ
  exact tailCountingFunction_le_f (m := m) (N := N) hQ

/-! ## Finite lower-bound bridge -/

lemma reciprocalSum_ge_card_div_of_pos_le
    {N : ℕ} {Q : Finset ℕ}
    (hpos : ∀ q ∈ Q, 0 < q)
    (hupper : ∀ q ∈ Q, q ≤ N) :
    (Q.card : ℝ) / (N : ℝ) ≤ reciprocalSum Q := by
  classical
  by_cases hN : N = 0
  · subst N
    have hQempty : Q = ∅ := by
      ext q
      constructor
      · intro hq
        have hp := hpos q hq
        have hu := hupper q hq
        omega
      · intro hq
        simp at hq
    simp [hQempty, reciprocalSum]
  · have hNpos_nat : 0 < N := Nat.pos_of_ne_zero hN
    have hNpos : 0 < (N : ℝ) := by exact_mod_cast hNpos_nat
    unfold reciprocalSum
    calc
      (Q.card : ℝ) / (N : ℝ)
          = ∑ q ∈ Q, (N : ℝ)⁻¹ := by
              simp [div_eq_mul_inv]
      _ ≤ ∑ q ∈ Q, (q : ℝ)⁻¹ := by
          refine Finset.sum_le_sum ?_
          intro q hq
          have hqpos : 0 < (q : ℝ) := by exact_mod_cast hpos q hq
          have hqN : (q : ℝ) ≤ (N : ℝ) := by exact_mod_cast hupper q hq
          exact (inv_le_inv₀ hNpos hqpos).2 hqN

lemma Admissible.tail_filter_tailAdmissible
    {m N : ℕ} {Q : Finset ℕ} (hQ : Admissible N Q) :
    TailAdmissible m (Q.filter fun q => m < q) := by
  classical
  constructor
  · intro q hq
    exact (Finset.mem_filter.1 hq).2
  · rcases hQ.2 with ⟨a, hdisj⟩
    exact ⟨restrictAssignment a (by intro q hq; exact (Finset.mem_filter.1 hq).1),
      PairwiseDisjointResidues.mono hdisj (by intro q hq; exact (Finset.mem_filter.1 hq).1)⟩

lemma Admissible.tail_filter_card_ge_sub
    {m N : ℕ} {Q : Finset ℕ} (hQ : Admissible N Q) :
    Q.card - m ≤ (Q.filter fun q => m < q).card := by
  classical
  let Small : Finset ℕ := Q.filter fun q => q ≤ m
  let Large : Finset ℕ := Q.filter fun q => m < q
  have hSmall_card : Small.card ≤ m := by
    have hsub : Small ⊆ Finset.Icc 1 m := by
      intro q hq
      have hqQ : q ∈ Q := (Finset.mem_filter.1 hq).1
      have hqm : q ≤ m := (Finset.mem_filter.1 hq).2
      exact Finset.mem_Icc.2 ⟨(hQ.1 q hqQ).1, hqm⟩
    have hcard := Finset.card_le_card hsub
    have hIcc : (Finset.Icc 1 m).card = m := by
      rw [Nat.card_Icc]
      omega
    simpa [Small, hIcc] using hcard
  have hpartition : Q = Small ∪ Large := by
    ext q
    by_cases hqQ : q ∈ Q
    · by_cases hqm : q ≤ m
      · simp [Small, Large, hqQ, hqm, not_lt_of_ge hqm]
      · have hlt : m < q := Nat.lt_of_not_ge hqm
        simp [Small, Large, hqQ, hqm, hlt]
    · simp [Small, Large, hqQ]
  have hdisj : Disjoint Small Large := by
    rw [Finset.disjoint_iff_ne]
    intro a ha b hb hab
    subst b
    have hle : a ≤ m := (Finset.mem_filter.1 ha).2
    have hlt : m < a := (Finset.mem_filter.1 hb).2
    exact (not_lt_of_ge hle) hlt
  have hcard_eq : Q.card = Small.card + Large.card := by
    rw [hpartition, Finset.card_union_of_disjoint hdisj]
  have : Q.card - Small.card ≤ Large.card := by omega
  exact (Nat.sub_le_sub_left hSmall_card Q.card).trans this

lemma exists_tailAdmissible_card_ge_sub_f
    (m N : ℕ) :
    ∃ Q : Finset ℕ,
      TailAdmissible m Q ∧
      Q.card ≥ f N - m ∧
      (∀ q ∈ Q, q ≤ N) := by
  classical
  rcases exists_admissible_card_f N with ⟨Q₀, hQ₀, hcard⟩
  let Q : Finset ℕ := Q₀.filter fun q => m < q
  refine ⟨Q, Admissible.tail_filter_tailAdmissible hQ₀, ?_, ?_⟩
  · rw [← hcard]
    exact Admissible.tail_filter_card_ge_sub hQ₀
  · intro q hq
    exact (hQ₀.1 q (Finset.mem_filter.1 hq).1).2

lemma exists_tailAdmissible_reciprocalSum_ge_sub_f_div
    (m N : ℕ) :
    ∃ Q : Finset ℕ,
      TailAdmissible m Q ∧
      (reciprocalSum Q ≥ ((f N - m : ℕ) : ℝ) / (N : ℝ)) := by
  classical
  rcases exists_tailAdmissible_card_ge_sub_f m N with ⟨Q, hTail, hcard, hupper⟩
  refine ⟨Q, hTail, ?_⟩
  have hpos : ∀ q ∈ Q, 0 < q := by
    intro q hq
    exact (Nat.zero_le m).trans_lt (hTail.1 q hq)
  have hmass := reciprocalSum_ge_card_div_of_pos_le (N := N) (Q := Q) hpos hupper
  by_cases hN : N = 0
  · subst N
    have hQempty : Q = ∅ := by
      ext q
      constructor
      · intro hq
        have hp := hpos q hq
        have hu := hupper q hq
        omega
      · intro hq
        simp at hq
    simp [hQempty, reciprocalSum]
  · have hNnonneg : 0 ≤ (N : ℝ) := by positivity
    exact (div_le_div_of_nonneg_right (by exact_mod_cast hcard) hNnonneg).trans hmass

lemma exists_tailAdmissible_reciprocalSum_ge_f_div_sub_m_div
    (m N : ℕ) (hfm : m ≤ f N) :
    ∃ Q : Finset ℕ,
      TailAdmissible m Q ∧
      (reciprocalSum Q ≥ (f N : ℝ) / (N : ℝ) - (m : ℝ) / (N : ℝ)) := by
  rcases exists_tailAdmissible_reciprocalSum_ge_sub_f_div m N with ⟨Q, hQ, hmass⟩
  refine ⟨Q, hQ, ?_⟩
  have hcast : (((f N - m : ℕ) : ℕ) : ℝ) = (f N : ℝ) - (m : ℝ) := by
    simpa using (Nat.cast_sub (R := ℝ) hfm)
  have heq :
      (((f N - m : ℕ) : ℕ) : ℝ) / (N : ℝ) =
        (f N : ℝ) / (N : ℝ) - (m : ℝ) / (N : ℝ) := by
    rw [hcast]
    ring
  simpa [heq] using hmass

lemma le_epsilon1190_of_tailAdmissible'
    {m : ℕ} {Q : Finset ℕ} {B : ℝ}
    (hQ : TailAdmissible m Q)
    (hmass : B ≤ reciprocalSum Q)
    (hbdd : BddAbove (reciprocalSums1190 m)) :
    B ≤ epsilon1190 m :=
  hmass.trans (le_epsilon1190_of_tailAdmissible hQ hbdd)

lemma f_div_sub_m_div_le_epsilon1190
    (m N : ℕ) (hfm : m ≤ f N)
    (hbdd : BddAbove (reciprocalSums1190 m)) :
    (f N : ℝ) / (N : ℝ) - (m : ℝ) / (N : ℝ) ≤ epsilon1190 m := by
  rcases exists_tailAdmissible_reciprocalSum_ge_f_div_sub_m_div m N hfm with
    ⟨Q, hQ, hmass⟩
  exact le_epsilon1190_of_tailAdmissible' hQ hmass hbdd

/-! ## Lift endpoint for the lower-bound corollary -/

/-- Endpoint used in the PDF lower bound for 1190:
`N = ceil(m · L(2,m))`. -/
noncomputable def lift1190N (m : ℕ) : ℕ :=
  Nat.ceil ((m : ℝ) * Lscale 2 m)

lemma lift1190N_ge_mul_Lscale (m : ℕ) :
    (m : ℝ) * Lscale 2 m ≤ (lift1190N m : ℝ) := by
  exact Nat.le_ceil _

lemma lift1190N_pos_of_pos {m : ℕ} (hm : 0 < m) :
    0 < lift1190N m := by
  have hpos : 0 < (m : ℝ) * Lscale 2 m := by
    exact mul_pos (by exact_mod_cast hm) (Lscale_pos 2 m)
  have hle := lift1190N_ge_mul_Lscale m
  exact_mod_cast hpos.trans_le hle

lemma lift1190N_ge_self (m : ℕ) :
    m ≤ lift1190N m := by
  have hL : 1 ≤ Lscale 2 m := by
    rw [Lscale]
    exact Real.one_le_exp (mul_nonneg (by norm_num) (Zscale_nonneg m))
  have hmul : (m : ℝ) ≤ (m : ℝ) * Lscale 2 m := by
    exact le_mul_of_one_le_right (by positivity) hL
  have hceil := lift1190N_ge_mul_Lscale m
  exact_mod_cast hmul.trans hceil

lemma tendsto_lift1190N_atTop :
    Tendsto lift1190N atTop atTop := by
  exact tendsto_atTop_mono lift1190N_ge_self tendsto_id

lemma log_lift1190N_le_one_plus_mul_log
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ m : ℕ in atTop,
      Real.log (lift1190N m : ℝ) ≤ (1 + η) * Real.log (m : ℝ) := by
  let c : ℝ := η / 2
  have hc : 0 < c := by positivity
  have hlog_atTop : Tendsto (fun m : ℕ => Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_Mscale_ge (4 / c) (by positivity),
      hlog_atTop.eventually_ge_atTop (2 * Real.log 2 / c),
      Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1)),
      Filter.eventually_ge_atTop 1] with m hM hlog_large hmlarge_nat hm1
  have hmlarge : Real.exp 1 < (m : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hmlarge_nat)
  have hmpos_nat : 0 < m := by omega
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast hmpos_nat
  have hlogm_pos : 0 < Real.log (m : ℝ) :=
    zero_lt_one.trans ((Real.lt_log_iff_exp_lt hmpos).2 hmlarge)
  have hZ_nonneg : 0 ≤ Zscale m := Zscale_nonneg m
  have hlog_eq := Mscale_mul_Zscale_eq_log hmlarge
  have htwoZ_le : 2 * Zscale m ≤ c / 2 * Real.log (m : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right hM hZ_nonneg
    rw [hlog_eq] at hmul
    have hfour : 4 * Zscale m ≤ c * Real.log (m : ℝ) := by
      have hmulc := mul_le_mul_of_nonneg_left hmul hc.le
      calc
        4 * Zscale m = c * ((4 / c) * Zscale m) := by
          rw [div_eq_mul_inv]
          calc
            4 * Zscale m = 4 * Zscale m * (c * c⁻¹) := by
              rw [mul_inv_cancel₀ hc.ne']
              ring
            _ = c * ((4 * c⁻¹) * Zscale m) := by ring
        _ ≤ c * Real.log (m : ℝ) := hmulc
    nlinarith
  have hlog2_le : Real.log 2 ≤ c / 2 * Real.log (m : ℝ) := by
    have h := (div_le_iff₀ hc).1 hlog_large
    nlinarith
  let x : ℝ := (m : ℝ) * Lscale 2 m
  have hxpos : 0 < x := mul_pos hmpos (Lscale_pos 2 m)
  have hxge1 : 1 ≤ x := by
    have hL : 1 ≤ Lscale 2 m := by
      rw [Lscale]
      exact Real.one_le_exp (mul_nonneg (by norm_num) hZ_nonneg)
    have hmreal1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
    nlinarith
  have hceil_lt : (lift1190N m : ℝ) < x + 1 := by
    simpa [lift1190N, x] using
      Nat.ceil_lt_add_one (show 0 ≤ (m : ℝ) * Lscale 2 m by positivity)
  have hceil_le : (lift1190N m : ℝ) ≤ 2 * x := by linarith
  have hNpos : 0 < (lift1190N m : ℝ) := by
    exact_mod_cast lift1190N_pos_of_pos hmpos_nat
  have h2xpos : 0 < 2 * x := by positivity
  have hlog_le : Real.log (lift1190N m : ℝ) ≤ Real.log (2 * x) :=
    Real.log_le_log hNpos hceil_le
  have hlog2x :
      Real.log (2 * x) = Real.log 2 + Real.log (m : ℝ) + 2 * Zscale m := by
    rw [show 2 * x = 2 * ((m : ℝ) * Lscale 2 m) by rfl]
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
        (mul_ne_zero (by exact_mod_cast hmpos_nat.ne') (Lscale_pos 2 m).ne'),
      Real.log_mul (by exact_mod_cast hmpos_nat.ne') (Lscale_pos 2 m).ne']
    simp [Lscale]
    ring
  calc
    Real.log (lift1190N m : ℝ)
        ≤ Real.log (2 * x) := hlog_le
    _ = Real.log 2 + Real.log (m : ℝ) + 2 * Zscale m := hlog2x
    _ ≤ (1 + η) * Real.log (m : ℝ) := by
          have hmain : Real.log 2 + 2 * Zscale m ≤ c * Real.log (m : ℝ) := by
            linarith
          dsimp [c] at hmain
          nlinarith

lemma loglog_lift1190N_le_one_plus_mul_loglog
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ m : ℕ in atTop,
      Real.log (Real.log (lift1190N m : ℝ)) ≤
        (1 + η) * Real.log (Real.log (m : ℝ)) := by
  have hApos : 0 < 1 + η := by positivity
  have hlog_atTop : Tendsto (fun m : ℕ => Real.log (Real.log (m : ℝ))) atTop atTop :=
    tendsto_loglog_nat_atTop
  filter_upwards [log_lift1190N_le_one_plus_mul_log η hη,
      hlog_atTop.eventually_ge_atTop (Real.log (1 + η) / η),
      Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with m hlogN hloglog_large hmlarge_nat
  have hmlarge : Real.exp 1 < (m : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hmlarge_nat)
  have hmpos : 0 < (m : ℝ) := (Real.exp_pos 1).trans hmlarge
  have hlogm_gt_one : 1 < Real.log (m : ℝ) :=
    (Real.lt_log_iff_exp_lt hmpos).2 hmlarge
  have hlogm_pos : 0 < Real.log (m : ℝ) := zero_lt_one.trans hlogm_gt_one
  have hNge : m ≤ lift1190N m := lift1190N_ge_self m
  have hNlarge : Real.exp 1 < (lift1190N m : ℝ) :=
    hmlarge.trans_le (by exact_mod_cast hNge)
  have hNpos : 0 < (lift1190N m : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlogN_pos : 0 < Real.log (lift1190N m : ℝ) :=
    zero_lt_one.trans ((Real.lt_log_iff_exp_lt hNpos).2 hNlarge)
  have htarget_pos : 0 < (1 + η) * Real.log (m : ℝ) :=
    mul_pos hApos hlogm_pos
  have hloglog_le :
      Real.log (Real.log (lift1190N m : ℝ)) ≤
        Real.log ((1 + η) * Real.log (m : ℝ)) :=
    Real.log_le_log hlogN_pos hlogN
  have hlog_prod :
      Real.log ((1 + η) * Real.log (m : ℝ)) =
        Real.log (1 + η) + Real.log (Real.log (m : ℝ)) := by
    rw [Real.log_mul hApos.ne' hlogm_pos.ne']
  have hconst_le : Real.log (1 + η) ≤ η * Real.log (Real.log (m : ℝ)) := by
    simpa [mul_comm] using (div_le_iff₀ hη).1 hloglog_large
  calc
    Real.log (Real.log (lift1190N m : ℝ))
        ≤ Real.log ((1 + η) * Real.log (m : ℝ)) := hloglog_le
    _ = Real.log (1 + η) + Real.log (Real.log (m : ℝ)) := hlog_prod
    _ ≤ (1 + η) * Real.log (Real.log (m : ℝ)) := by
          nlinarith

lemma Zscale_lift1190N_le
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ m : ℕ in atTop,
      Zscale (lift1190N m) ≤ (1 + η) * Zscale m := by
  let c : ℝ := η / 2
  have hc : 0 < c := by positivity
  filter_upwards [log_lift1190N_le_one_plus_mul_log c hc,
      loglog_lift1190N_le_one_plus_mul_loglog c hc,
      Filter.eventually_gt_atTop (Nat.ceil (Real.exp 1))] with
    m hlog hloglog hmlarge_nat
  have hmlarge : Real.exp 1 < (m : ℝ) :=
    lt_of_le_of_lt (Nat.le_ceil _) (by exact_mod_cast hmlarge_nat)
  have hmpos : 0 < (m : ℝ) := (Real.exp_pos 1).trans hmlarge
  have hlogm_gt_one : 1 < Real.log (m : ℝ) :=
    (Real.lt_log_iff_exp_lt hmpos).2 hmlarge
  have hlogm_pos : 0 < Real.log (m : ℝ) := zero_lt_one.trans hlogm_gt_one
  have hloglogm_pos : 0 < Real.log (Real.log (m : ℝ)) :=
    Real.log_pos hlogm_gt_one
  have hNge : m ≤ lift1190N m := lift1190N_ge_self m
  have hNlarge : Real.exp 1 < (lift1190N m : ℝ) :=
    hmlarge.trans_le (by exact_mod_cast hNge)
  have hNpos : 0 < (lift1190N m : ℝ) := (Real.exp_pos 1).trans hNlarge
  have hlogN_gt_one : 1 < Real.log (lift1190N m : ℝ) :=
    (Real.lt_log_iff_exp_lt hNpos).2 hNlarge
  have hlogN_pos : 0 < Real.log (lift1190N m : ℝ) := zero_lt_one.trans hlogN_gt_one
  have hloglogN_nonneg : 0 ≤ Real.log (Real.log (lift1190N m : ℝ)) :=
    (Real.log_pos hlogN_gt_one).le
  have hfactor_nonneg : 0 ≤ 1 + c := by positivity
  have hprod :
      Real.log (lift1190N m : ℝ) * Real.log (Real.log (lift1190N m : ℝ)) ≤
        ((1 + c) * Real.log (m : ℝ)) *
          ((1 + c) * Real.log (Real.log (m : ℝ))) := by
    have hright_nonneg : 0 ≤ (1 + c) * Real.log (m : ℝ) :=
      mul_nonneg hfactor_nonneg hlogm_pos.le
    exact mul_le_mul hlog hloglog hloglogN_nonneg hright_nonneg
  have hargm_nonneg :
      0 ≤ Real.log (m : ℝ) * Real.log (Real.log (m : ℝ)) :=
    mul_nonneg hlogm_pos.le hloglogm_pos.le
  have hZn_sq :
      Zscale (lift1190N m) ^ 2 ≤ ((1 + c) * Zscale m) ^ 2 := by
    rw [Zscale, Zscale, Real.sq_sqrt]
    · rw [mul_pow, Real.sq_sqrt hargm_nonneg]
      nlinarith [hprod]
    · exact mul_nonneg hlogN_pos.le hloglogN_nonneg
  have hleft_nonneg : 0 ≤ Zscale (lift1190N m) := Zscale_nonneg _
  have hright_nonneg : 0 ≤ (1 + c) * Zscale m := by
    exact mul_nonneg hfactor_nonneg (Zscale_nonneg m)
  have hmain : Zscale (lift1190N m) ≤ (1 + c) * Zscale m :=
    by
      have habs := sq_le_sq.1 hZn_sq
      simpa [abs_of_nonneg hleft_nonneg, abs_of_nonneg hright_nonneg] using habs
  have hc_le_eta : c ≤ η := by dsimp [c]; linarith
  calc
    Zscale (lift1190N m)
        ≤ (1 + c) * Zscale m := hmain
    _ ≤ (1 + η) * Zscale m := by
          exact mul_le_mul_of_nonneg_right (by linarith) (Zscale_nonneg m)

lemma Lscale_lift1190N_neg_compare
    (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∀ᶠ m : ℕ in atTop,
      Lscale (-b) m ≤ Lscale (-a) (lift1190N m) := by
  let δ : ℝ := (b - a) / (2 * a)
  have hδ : 0 < δ := by
    exact div_pos (sub_pos.2 hab) (mul_pos (by norm_num) ha)
  have hcoef : a * (1 + δ) ≤ b := by
    dsimp [δ]
    field_simp [ha.ne']
    nlinarith
  filter_upwards [Zscale_lift1190N_le δ hδ] with m hZ
  rw [Lscale, Lscale]
  apply Real.exp_le_exp.2
  have hmul : a * Zscale (lift1190N m) ≤ b * Zscale m := by
    calc
      a * Zscale (lift1190N m)
          ≤ a * ((1 + δ) * Zscale m) :=
            mul_le_mul_of_nonneg_left hZ ha.le
      _ = (a * (1 + δ)) * Zscale m := by ring
      _ ≤ b * Zscale m :=
            mul_le_mul_of_nonneg_right hcoef (Zscale_nonneg m)
  nlinarith

lemma m_div_lift1190N_le_Lscale_neg_two_of_pos
    {m : ℕ} (hm : 0 < m) :
    (m : ℝ) / (lift1190N m : ℝ) ≤ Lscale (-2) m := by
  have hNpos_nat : 0 < lift1190N m := lift1190N_pos_of_pos hm
  have hNpos : 0 < (lift1190N m : ℝ) := by exact_mod_cast hNpos_nat
  rw [div_le_iff₀ hNpos]
  have hceil := lift1190N_ge_mul_Lscale m
  have hprod : Lscale (-2) m * Lscale 2 m = 1 := Lscale_neg_mul 2 m
  have heq :
      Lscale (-2) m * ((m : ℝ) * Lscale 2 m) = (m : ℝ) := by
    calc
      Lscale (-2) m * ((m : ℝ) * Lscale 2 m)
          = (m : ℝ) * (Lscale (-2) m * Lscale 2 m) := by ring
      _ = (m : ℝ) * 1 := by rw [hprod]
      _ = (m : ℝ) := by ring
  calc
    (m : ℝ)
        = Lscale (-2) m * ((m : ℝ) * Lscale 2 m) := heq.symm
    _ ≤ Lscale (-2) m * (lift1190N m : ℝ) :=
          mul_le_mul_of_nonneg_left hceil (Lscale_nonneg (-2) m)

lemma m_div_lift1190N_le_Lscale_neg_two :
    ∀ᶠ m : ℕ in atTop,
      (m : ℝ) / (lift1190N m : ℝ) ≤ Lscale (-2) m := by
  filter_upwards [Filter.eventually_gt_atTop 0] with m hm
  exact m_div_lift1190N_le_Lscale_neg_two_of_pos (by omega)

lemma Lscale_neg_two_le_half_Lscale_neg
    (b : ℝ) (hb : b < 2) :
    ∀ᶠ m : ℕ in atTop,
      Lscale (-2) m ≤ (1 / 2) * Lscale (-b) m := by
  have hgap : 0 < 2 - b := by linarith
  filter_upwards [eventually_Lscale_neg_le_const_1190 (A := 2 - b) (c := 1 / 2)
    hgap (by norm_num)] with m hsmall
  calc
    Lscale (-2) m
        = Lscale (-b + -(2 - b)) m := by ring_nf
    _ = Lscale (-b) m * Lscale (-(2 - b)) m := by
          rw [Lscale_add]
    _ ≤ Lscale (-b) m * (1 / 2) :=
          mul_le_mul_of_nonneg_left hsmall (Lscale_nonneg (-b) m)
    _ = (1 / 2) * Lscale (-b) m := by ring

lemma m_div_lift1190N_negligible
    (b : ℝ) (hb : b < 2) :
    ∀ᶠ m : ℕ in atTop,
      (m : ℝ) / (lift1190N m : ℝ)
        ≤ (1 / 2) * Lscale (-b) m := by
  filter_upwards [m_div_lift1190N_le_Lscale_neg_two,
      Lscale_neg_two_le_half_Lscale_neg b hb] with m hdiv hscale
  exact hdiv.trans hscale

lemma self_le_lift1190N_mul_Lscale_neg
    (a : ℝ) (ha : 0 < a) (ha_lt : a < 3 / 2) :
    ∀ᶠ m : ℕ in atTop,
      (m : ℝ) ≤ (lift1190N m : ℝ) * Lscale (-a) (lift1190N m) := by
  filter_upwards [Lscale_lift1190N_neg_compare (a := a) (b := 3 / 2) ha ha_lt]
    with m hscale
  have hhalf_one : 1 ≤ Lscale (1 / 2) m := by
    rw [Lscale]
    exact Real.one_le_exp (mul_nonneg (by norm_num) (Zscale_nonneg m))
  have hceil := lift1190N_ge_mul_Lscale m
  calc
    (m : ℝ)
        ≤ (m : ℝ) * Lscale (1 / 2) m := by
            exact le_mul_of_one_le_right (by positivity) hhalf_one
    _ = ((m : ℝ) * Lscale 2 m) * Lscale (-(3 / 2)) m := by
            have hL :
                Lscale (1 / 2) m = Lscale 2 m * Lscale (-(3 / 2)) m := by
              rw [← Lscale_add]
              ring_nf
            rw [hL]
            ring
    _ ≤ (lift1190N m : ℝ) * Lscale (-a) (lift1190N m) := by
            exact mul_le_mul hceil hscale (Lscale_nonneg (-(3 / 2)) m) (by positivity)

lemma Lscale_neg_big_le_half_mid
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ m : ℕ in atTop,
      Lscale (-(1 + η)) m ≤
        (1 / 2) * Lscale (-(1 + η / 3)) m := by
  have hgap : 0 < 2 * η / 3 := by positivity
  filter_upwards [eventually_Lscale_neg_le_const_1190
      (A := 2 * η / 3) (c := 1 / 2) hgap (by norm_num)] with m hsmall
  calc
    Lscale (-(1 + η)) m
        = Lscale (-(1 + η / 3)) m * Lscale (-(2 * η / 3)) m := by
            rw [← Lscale_add]
            ring_nf
    _ ≤ Lscale (-(1 + η / 3)) m * (1 / 2) := by
            exact mul_le_mul_of_nonneg_left hsmall (Lscale_nonneg (-(1 + η / 3)) m)
    _ = (1 / 2) * Lscale (-(1 + η / 3)) m := by ring

/-- Lower half of Erdős 1190, obtained from the lower half of Erdős 202 by
taking `N = ceil(m L(2,m))` and discarding moduli at most `m`. -/
theorem eps1190_lower (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop,
      Lscale (-(1 + ε)) m ≤ eps1190 m := by
  let η : ℝ := min ε (1 / 2)
  have hηpos : 0 < η := lt_min hε (by norm_num)
  have hηsmall : η ≤ 1 / 2 := min_le_right ε (1 / 2 : ℝ)
  have hηleε : η ≤ ε := min_le_left ε (1 / 2 : ℝ)
  have hη8 : 0 < η / 8 := by positivity
  rcases eventually_atTop.1 (erdos202_main (η / 8) hη8) with ⟨N₀, h202⟩
  have hfamily := recipSum_le_dyadic_tail η hηpos hηsmall
  have hscale :=
    Lscale_lift1190N_neg_compare
      (a := 1 + η / 8) (b := 1 + η / 3)
      (by positivity) (by nlinarith [hηpos])
  have hself :=
    self_le_lift1190N_mul_Lscale_neg
      (a := 1 + η / 8) (by positivity) (by nlinarith [hηsmall])
  have hdiscard :=
    m_div_lift1190N_negligible (b := 1 + η / 3) (by nlinarith [hηsmall])
  have hhalf := Lscale_neg_big_le_half_mid η hηpos
  filter_upwards [Filter.eventually_ge_atTop (max 1 N₀), hfamily, hscale, hself, hdiscard, hhalf]
    with m hm hfamily_m hscale_m hself_m hdiscard_m hhalf_m
  let N : ℕ := lift1190N m
  have hm1 : 1 ≤ m := le_of_max_le_left hm
  have hmN₀ : N₀ ≤ m := le_of_max_le_right hm
  have hNge : N₀ ≤ N := by
    exact hmN₀.trans (by simpa [N] using lift1190N_ge_self m)
  have h202lower :
      (N : ℝ) * Lscale (-(1 + η / 8)) N ≤ (f N : ℝ) :=
    (h202 N hNge).1
  have hNpos_nat : 0 < N := by
    have hmpos : 0 < m := Nat.succ_le_iff.mp hm1
    simpa [N] using lift1190N_pos_of_pos hmpos
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hNpos_nat
  have hfm : m ≤ f N := by
    have hreal : (m : ℝ) ≤ (f N : ℝ) := by
      have hselfN :
          (m : ℝ) ≤ (N : ℝ) * Lscale (-(1 + η / 8)) N := by
        simpa [N] using hself_m
      exact hselfN.trans h202lower
    exact_mod_cast hreal
  have hbdd : BddAbove (reciprocalSums1190 m) := by
    refine ⟨Lscale (-(1 - η)) m, ?_⟩
    intro s hs
    rcases hs with ⟨Q, hQ, rfl⟩
    exact hfamily_m Q hQ
  have heps_base :
      (f N : ℝ) / (N : ℝ) - (m : ℝ) / (N : ℝ) ≤ eps1190 m :=
    f_div_sub_m_div_le_epsilon1190 m N hfm hbdd
  have hfdiv_ge :
      Lscale (-(1 + η / 3)) m ≤ (f N : ℝ) / (N : ℝ) := by
    have hLN_div :
        Lscale (-(1 + η / 8)) N ≤ (f N : ℝ) / (N : ℝ) := by
      rw [le_div_iff₀ hNpos]
      simpa [mul_comm] using h202lower
    exact hscale_m.trans hLN_div
  have htarget_eta :
      Lscale (-(1 + η)) m ≤ (f N : ℝ) / (N : ℝ) - (m : ℝ) / (N : ℝ) := by
    nlinarith [hfdiv_ge, hdiscard_m, hhalf_m]
  have htarget_eps :
      Lscale (-(1 + ε)) m ≤ Lscale (-(1 + η)) m :=
    Lscale_mono_in_alpha (N := m) (by linarith : -(1 + ε) ≤ -(1 + η))
  exact htarget_eps.trans (htarget_eta.trans heps_base)

/-- **Erdős Problem 1190 — main theorem.** -/
theorem erdos1190_main : HasErdos1190Asymptotic := by
  intro ε hε
  filter_upwards [eps1190_lower ε hε, eps1190_upper ε hε] with m hlow hup
  exact ⟨hlow, hup⟩

/-! ## Axiom audit

The statement and finite bridge above are axiom-free beyond the usual Lean
foundational axioms inherited from `ErdosProblems.Erdos202`.
-/

end Erdos1190

/-! ## Axiom audit -/

#print axioms Erdos1190.erdos1190_bridge_ready
-- 'Erdos1190.erdos1190_bridge_ready' depends on axioms: [propext, Classical.choice,
-- Quot.sound]
#print axioms Erdos1190.erdos1190_main
-- 'Erdos1190.erdos1190_main' depends on axioms: [propext, Classical.choice, Quot.sound]
