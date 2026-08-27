import ErdosProblems.Erdos4.FGKMTConditionalLaw
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.ZMod.Basic

/-!
# The tilted preliminary residue law

Exact finite probability laws for Section 3 of
`output/pdf/Erdos_4_GPT_5.6_Sol.tex`. The parameter `u` is the local tilt
`s ^ (-τ)`. All normalization and survival identities are proved from
finite sums; no distribution estimate is assumed.
-/

open scoped BigOperators

namespace Erdos4.Tilted

open FGKMT

noncomputable def atom (s : ℕ) (u : ℝ) : ℝ := u / ((s : ℝ) - 1 + u)

noncomputable def beta (s : ℕ) (u : ℝ) : ℝ := ((s : ℝ) - 1) * atom s u

noncomputable def baseline (s : ℕ) (u : ℝ) : ℝ :=
  ((s : ℝ) - 1) / ((s : ℝ) - 1 + u)

theorem denominator_pos {s : ℕ} (hs : 2 ≤ s) {u : ℝ} (hu : 0 ≤ u) :
    0 < (s : ℝ) - 1 + u := by
  have hsR : (2 : ℝ) ≤ s := by exact_mod_cast hs
  linarith

theorem atom_nonneg {s : ℕ} (hs : 2 ≤ s) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ atom s u := div_nonneg hu (denominator_pos hs hu).le

theorem beta_nonneg {s : ℕ} (hs : 2 ≤ s) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ beta s u := by
  have hsR : (2 : ℝ) ≤ s := by exact_mod_cast hs
  exact mul_nonneg (by linarith) (atom_nonneg hs hu)

theorem beta_le_one {s : ℕ} (hs : 2 ≤ s) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    beta s u ≤ 1 := by
  have hsR : (2 : ℝ) ≤ s := by exact_mod_cast hs
  unfold beta atom
  rw [← mul_div_assoc]
  apply (div_le_one (denominator_pos hs hu0)).mpr
  have hh := mul_le_mul_of_nonneg_left hu1 (show 0 ≤ (s : ℝ) - 1 by linarith)
  nlinarith

theorem baseline_pos {s : ℕ} (hs : 2 ≤ s) {u : ℝ} (hu : 0 ≤ u) :
    0 < baseline s u := by
  have hsR : (2 : ℝ) ≤ s := by exact_mod_cast hs
  exact div_pos (by linarith) (denominator_pos hs hu)

theorem baseline_eq_one_sub_atom {s : ℕ} (hs : 2 ≤ s) {u : ℝ} (hu : 0 ≤ u) :
    baseline s u = 1 - atom s u := by
  unfold baseline atom
  field_simp [(denominator_pos hs hu).ne']
  ring

theorem beta_eq_baseline_mul (s : ℕ) (u : ℝ) :
    beta s u = baseline s u * u := by
  unfold beta baseline atom
  ring

theorem beta_pos {s : ℕ} (hs : 2 ≤ s) {u : ℝ} (hu : 0 < u) :
    0 < beta s u := by
  rw [beta_eq_baseline_mul]
  exact mul_pos (baseline_pos hs hu.le) hu

/-- The local likelihood ratio, equation (3.6). -/
theorem beta_div_baseline {s : ℕ} (hs : 2 ≤ s) {u : ℝ} (hu : 0 ≤ u) :
    beta s u / baseline s u = u := by
  rw [beta_eq_baseline_mul]
  exact mul_div_cancel_left₀ u (baseline_pos hs hu).ne'

noncomputable def localWeight (s : ℕ) [NeZero s] (u : ℝ) (a : ZMod s) : ℝ :=
  if a = 0 then 1 - beta s u else atom s u

theorem localWeight_nonneg {s : ℕ} [NeZero s] (hs : 2 ≤ s)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (a : ZMod s) :
    0 ≤ localWeight s u a := by
  unfold localWeight
  split_ifs
  · exact sub_nonneg.mpr (beta_le_one hs hu0 hu1)
  · exact atom_nonneg hs hu0

theorem localWeight_eq (s : ℕ) [NeZero s] (u : ℝ) (a : ZMod s) :
    localWeight s u a =
      atom s u + (if a = 0 then 1 - beta s u - atom s u else 0) := by
  unfold localWeight
  split_ifs <;> ring

theorem localWeight_sum (s : ℕ) [NeZero s] (u : ℝ) :
    ∑ a : ZMod s, localWeight s u a = 1 := by
  simp_rw [localWeight_eq]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    ZMod.card, nsmul_eq_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  unfold beta
  ring

/-- The genuine normalized law in (3.1)--(3.2). -/
noncomputable def localLaw (s : ℕ) [NeZero s] (hs : 2 ≤ s)
    (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) : FiniteLaw (ZMod s) where
  weight := localWeight s u
  nonneg := localWeight_nonneg hs hu0 hu1
  total := localWeight_sum s u

theorem localLaw_prob_eq (s : ℕ) [NeZero s] (hs : 2 ≤ s)
    (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (b : ZMod s) :
    (localLaw s hs u hu0 hu1).prob (fun a => a = b) = localWeight s u b := by
  classical
  simp only [FiniteLaw.prob, localLaw]
  rw [Finset.sum_eq_single b]
  · simp
  · intro a _ha hab
    simp [hab]
  · intro hb
    exact (hb (Finset.mem_univ b)).elim

theorem localLaw_prob_ne (s : ℕ) [NeZero s] (hs : 2 ≤ s)
    (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (b : ZMod s) :
    (localLaw s hs u hu0 hu1).prob (fun a => a ≠ b) =
      if b = 0 then beta s u else baseline s u := by
  rw [FiniteLaw.prob_compl, localLaw_prob_eq]
  unfold localWeight
  by_cases hb : b = 0
  · simp only [if_pos hb]
    ring
  · simp only [if_neg hb]
    exact (baseline_eq_one_sub_atom hs hu0).symm

/-- Equation (3.5), with divisibility of the integer target made explicit. -/
theorem localLaw_survival (s : ℕ) [NeZero s] (hs : 2 ≤ s)
    (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (n : ℕ) :
    (localLaw s hs u hu0 hu1).prob (fun a => a ≠ (n : ZMod s)) =
      baseline s u * (if s ∣ n then u else 1) := by
  rw [localLaw_prob_ne]
  simp only [ZMod.natCast_eq_zero_iff]
  by_cases hn : s ∣ n
  · simp only [if_pos hn, beta_eq_baseline_mul]
  · simp only [if_neg hn, mul_one]

theorem localLaw_prob_ne_pos (s : ℕ) [NeZero s] (hs : 2 ≤ s)
    (u : ℝ) (hu0 : 0 < u) (hu1 : u ≤ 1) (b : ZMod s) :
    0 < (localLaw s hs u hu0.le hu1).prob (fun a => a ≠ b) := by
  rw [localLaw_prob_ne]
  split_ifs
  · exact beta_pos hs hu0
  · exact baseline_pos hs hu0.le

theorem localLaw_prob_mem (s : ℕ) [NeZero s] (hs : 2 ≤ s)
    (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (E : Finset (ZMod s)) :
    (localLaw s hs u hu0 hu1).prob (fun a => a ∈ E) =
      (E.card : ℝ) * atom s u + (if 0 ∈ E then 1 - beta s u - atom s u else 0) := by
  classical
  rw [FiniteLaw.prob_eq_mean]
  simp only [FiniteLaw.mean, localLaw, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  have hfilter : Finset.univ.filter (fun a : ZMod s => a ∈ E) = E := by
    ext a
    simp
  rw [hfilter]
  simp_rw [localWeight_eq]
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
    Finset.sum_ite_eq']

/-- The exact local block factor (4.7), expressed using the mass of a nonzero residue. -/
theorem localLaw_prob_avoid (s : ℕ) [NeZero s] (hs : 2 ≤ s)
    (u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (E : Finset (ZMod s)) :
    (localLaw s hs u hu0 hu1).prob (fun a => a ∉ E) =
      if 0 ∈ E then beta s u * (1 - ((E.card : ℝ) - 1) / ((s : ℝ) - 1))
      else 1 - (E.card : ℝ) * atom s u := by
  classical
  rw [FiniteLaw.prob_compl, localLaw_prob_mem]
  by_cases hz : (0 : ZMod s) ∈ E
  · simp only [if_pos hz]
    have hsR : (2 : ℝ) ≤ s := by exact_mod_cast hs
    unfold beta
    field_simp [show (s : ℝ) - 1 ≠ 0 by linarith]
    ring
  · simp only [if_neg hz, add_zero]

theorem rpow_tilt_pos {s : ℕ} (hs : 2 ≤ s) (τ : ℝ) :
    0 < (s : ℝ) ^ (-τ) := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  exact Real.rpow_pos_of_pos hsR _

theorem rpow_tilt_le_one {s : ℕ} (hs : 2 ≤ s) {τ : ℝ} (hτ : 0 ≤ τ) :
    (s : ℝ) ^ (-τ) ≤ 1 := by
  exact Real.rpow_le_one_of_one_le_of_nonpos
    (by exact_mod_cast (show 1 ≤ s by omega)) (neg_nonpos.mpr hτ)

/-- The manuscript's local law with the actual real-power tilt. -/
noncomputable def residueLaw (s : ℕ) [NeZero s] (hs : 2 ≤ s)
    (τ : ℝ) (hτ : 0 ≤ τ) : FiniteLaw (ZMod s) :=
  localLaw s hs ((s : ℝ) ^ (-τ)) (rpow_tilt_pos hs τ).le (rpow_tilt_le_one hs hτ)

theorem residueLaw_survival (s : ℕ) [NeZero s] (hs : 2 ≤ s)
    (τ : ℝ) (hτ : 0 ≤ τ) (n : ℕ) :
    (residueLaw s hs τ hτ).prob (fun a => a ≠ (n : ZMod s)) =
      baseline s ((s : ℝ) ^ (-τ)) * (if s ∣ n then (s : ℝ) ^ (-τ) else 1) :=
  localLaw_survival s hs _ _ _ n

theorem residueLaw_survival_pos (s : ℕ) [NeZero s] (hs : 2 ≤ s)
    (τ : ℝ) (hτ : 0 ≤ τ) (n : ℕ) :
    0 < (residueLaw s hs τ hτ).prob (fun a => a ≠ (n : ZMod s)) :=
  localLaw_prob_ne_pos s hs _ (rpow_tilt_pos hs τ) (rpow_tilt_le_one hs hτ) _

end Erdos4.Tilted
