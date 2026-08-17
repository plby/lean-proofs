/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos896.Ford.OrderQ

/-!
# Ford's integral `U_k(v)`

This file formalizes the integral introduced before Lemma 3.5 of Ford's
short paper *Integers with a divisor in (y, 2y]*.  Paper indices run from
one; coordinates of `Fin k → ℝ` run from zero.
-/

namespace Erdos896.Ford

open MeasureTheory
open scoped BigOperators

/-- The `g`-th expression in the minimum defining Ford's integrand.

The sum is over the first `g` coordinates.  It is useful to allow arbitrary
`g`; `ukIntegrand` only uses `0 ≤ g ≤ k`. -/
noncomputable def prefixWeight (k v g : ℕ) (x : Fin k → ℝ) : ℝ :=
  ((∑ i : Fin k, if (i : ℕ) < g then
      (2 : ℝ) ^ ((v : ℝ) * x i) else 0) + 1) / (2 : ℝ) ^ g

/-- Running minimum of the first `g + 1` prefix weights. -/
noncomputable def ukIntegrandAux (k v : ℕ) (x : Fin k → ℝ) : ℕ → ℝ
  | 0 => prefixWeight k v 0 x
  | g + 1 => min (ukIntegrandAux k v x g) (prefixWeight k v (g + 1) x)

/-- Ford's pointwise integrand
`min_{0 ≤ g ≤ k} 2⁻ᵍ (1 + ∑_{i ≤ g} 2^(v ξᵢ))`. -/
noncomputable def ukIntegrand (k v : ℕ) (x : Fin k → ℝ) : ℝ :=
  ukIntegrandAux k v x k

/-- Ford's `U_k(v)`, integrated over the ordered unit simplex. -/
noncomputable def uk (k v : ℕ) : ℝ :=
  ∫ x in orderedSimplex k 0 1, ukIntegrand k v x

lemma continuous_prefixWeight (k v g : ℕ) :
    Continuous (prefixWeight k v g) := by
  classical
  unfold prefixWeight
  apply Continuous.div
  · apply Continuous.add
    · apply continuous_finsetSum
      intro i hi
      split_ifs
      · exact (Real.continuous_const_rpow (by norm_num)).comp
          (continuous_const.mul (continuous_apply i))
      · fun_prop
    · fun_prop
  · fun_prop
  · intro x
    positivity

lemma measurable_prefixWeight (k v g : ℕ) :
    Measurable (prefixWeight k v g) :=
  (continuous_prefixWeight k v g).measurable

lemma continuous_ukIntegrandAux (k v g : ℕ) :
    Continuous (fun x ↦ ukIntegrandAux k v x g) := by
  induction g with
  | zero => simpa [ukIntegrandAux] using continuous_prefixWeight k v 0
  | succ g ih =>
      simpa [ukIntegrandAux] using ih.min (continuous_prefixWeight k v (g + 1))

lemma continuous_ukIntegrand (k v : ℕ) :
    Continuous (ukIntegrand k v) := by
  exact continuous_ukIntegrandAux k v k

lemma measurable_ukIntegrand (k v : ℕ) :
    Measurable (ukIntegrand k v) :=
  (continuous_ukIntegrand k v).measurable

lemma prefixWeight_pos (k v g : ℕ) (x : Fin k → ℝ) :
    0 < prefixWeight k v g x := by
  unfold prefixWeight
  positivity

lemma ukIntegrandAux_pos (k v g : ℕ) (x : Fin k → ℝ) :
    0 < ukIntegrandAux k v x g := by
  induction g with
  | zero => simpa [ukIntegrandAux] using prefixWeight_pos k v 0 x
  | succ g ih =>
      simpa [ukIntegrandAux] using lt_min ih (prefixWeight_pos k v (g + 1) x)

lemma ukIntegrand_pos (k v : ℕ) (x : Fin k → ℝ) :
    0 < ukIntegrand k v x := by
  simpa only [ukIntegrand] using ukIntegrandAux_pos k v k x

lemma ukIntegrand_nonneg (k v : ℕ) (x : Fin k → ℝ) :
    0 ≤ ukIntegrand k v x := (ukIntegrand_pos k v x).le

lemma prefixWeight_zero (k v : ℕ) (x : Fin k → ℝ) :
    prefixWeight k v 0 x = 1 := by
  simp [prefixWeight]

lemma ukIntegrandAux_le_prefixWeight_zero (k v g : ℕ) (x : Fin k → ℝ) :
    ukIntegrandAux k v x g ≤ prefixWeight k v 0 x := by
  induction g with
  | zero => simp [ukIntegrandAux]
  | succ g ih => exact (min_le_left _ _).trans ih

lemma ukIntegrandAux_le_prefixWeight_of_le (k v n g : ℕ) (x : Fin k → ℝ)
    (hg : g ≤ n) : ukIntegrandAux k v x n ≤ prefixWeight k v g x := by
  induction n generalizing g with
  | zero =>
      have : g = 0 := by omega
      subst g
      simp [ukIntegrandAux]
  | succ n ih =>
      by_cases htop : g = n + 1
      · subst g
        exact min_le_right _ _
      · exact (min_le_left _ _).trans (ih (g := g) (by omega))

lemma ukIntegrand_le_prefixWeight (k v g : ℕ) (x : Fin k → ℝ) (hg : g ≤ k) :
    ukIntegrand k v x ≤ prefixWeight k v g x :=
  ukIntegrandAux_le_prefixWeight_of_le k v k g x hg

lemma ukIntegrand_le_one (k v : ℕ) (x : Fin k → ℝ) :
    ukIntegrand k v x ≤ 1 := by
  rw [← prefixWeight_zero k v x]
  exact ukIntegrandAux_le_prefixWeight_zero k v k x

/-- Every prefix expression is at least its constant summand. -/
lemma one_div_pow_le_prefixWeight (k v g : ℕ) (x : Fin k → ℝ) :
    1 / (2 : ℝ) ^ g ≤ prefixWeight k v g x := by
  unfold prefixWeight
  apply (div_le_div_iff_of_pos_right (by positivity : 0 < (2 : ℝ) ^ g)).2
  have hs : 0 ≤ ∑ i : Fin k, if (i : ℕ) < g then
      (2 : ℝ) ^ ((v : ℝ) * x i) else 0 := by
    apply Finset.sum_nonneg
    intro i hi
    split_ifs <;> positivity
  linarith

lemma one_div_pow_le_ukIntegrandAux (k v g : ℕ) (x : Fin k → ℝ) :
    1 / (2 : ℝ) ^ g ≤ ukIntegrandAux k v x g := by
  induction g with
  | zero => simpa [ukIntegrandAux] using one_div_pow_le_prefixWeight k v 0 x
  | succ g ih =>
      rw [ukIntegrandAux]
      apply le_min
      · calc
          1 / (2 : ℝ) ^ (g + 1) ≤ 1 / (2 : ℝ) ^ g := by
            rw [div_le_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ (g + 1))
              (by positivity : 0 < (2 : ℝ) ^ g)]
            norm_num [pow_succ]
          _ ≤ ukIntegrandAux k v x g := ih
      · exact one_div_pow_le_prefixWeight k v (g + 1) x

lemma one_div_pow_le_ukIntegrand (k v : ℕ) (x : Fin k → ℝ) :
    1 / (2 : ℝ) ^ k ≤ ukIntegrand k v x :=
  one_div_pow_le_ukIntegrandAux k v k x

/-- A number in `[2⁻ᵏ,1]` lies below the upper endpoint of one of the
`k+1` dyadic layers whose lower endpoint it exceeds. -/
lemma exists_dyadic_cover {k : ℕ} {a : ℝ}
    (hlower : 1 / (2 : ℝ) ^ k ≤ a) (hupper : a ≤ 1) :
    ∃ m ≤ k, 1 / (2 : ℝ) ^ m ≤ a ∧ a ≤ 2 / (2 : ℝ) ^ m := by
  induction k generalizing a with
  | zero =>
      exact ⟨0, le_rfl, by simpa using hlower, by norm_num; linarith⟩
  | succ k ih =>
      by_cases hmiddle : 1 / (2 : ℝ) ^ k ≤ a
      · obtain ⟨m, hmk, hmlo, hmhi⟩ := ih hmiddle hupper
        exact ⟨m, hmk.trans (Nat.le_succ k), hmlo, hmhi⟩
      · refine ⟨k + 1, le_rfl, hlower, ?_⟩
        rw [pow_succ]
        calc
          a ≤ 1 / (2 : ℝ) ^ k := le_of_lt (lt_of_not_ge hmiddle)
          _ = 2 / ((2 : ℝ) ^ k * 2) := by field_simp

/-! ## Measurable dyadic superlevel stratification -/

/-- The `m`-th superlevel inside the ordered simplex. -/
def ukSuperlevel (k v m : ℕ) : Set (Fin k → ℝ) :=
  orderedSimplex k 0 1 ∩ {x | 1 / (2 : ℝ) ^ m ≤ ukIntegrand k v x}

lemma measurableSet_ukSuperlevel (k v m : ℕ) :
    MeasurableSet (ukSuperlevel k v m) := by
  unfold ukSuperlevel
  apply MeasurableSet.inter (measurableSet_orderedSimplex k 0 1)
  change MeasurableSet ((ukIntegrand k v) ⁻¹' Set.Ici (1 / (2 : ℝ) ^ m))
  exact measurable_ukIntegrand k v measurableSet_Ici

/-- The first `j+1` exponential terms, in the normalization used by `U_k`.
This is kept local to the integral layer so the definition of `U_k` does not
depend on the later cluster-volume estimate. -/
noncomputable def ukPrefixExpSum {k : ℕ} (v : ℕ) (x : Fin k → ℝ)
    (j : Fin k) : ℝ :=
  ∑ i ∈ Finset.Iic j, (2 : ℝ) ^ ((v : ℝ) * x i)

lemma measurable_ukPrefixExpSum {k v : ℕ} (j : Fin k) :
    Measurable (fun x : Fin k → ℝ ↦ ukPrefixExpSum v x j) := by
  unfold ukPrefixExpSum
  apply Finset.measurable_sum
  intro i hi
  exact (Real.continuous_const_rpow (by norm_num)).measurable.comp
    (measurable_const.mul (measurable_pi_apply i))

/-- Ford's prefix-sum region `T(k,v,γ)`, stated inside the independent
integral layer.  `Cluster` identifies this with its geometrically decomposed
version. -/
noncomputable def ukPrefixRegion (k v gamma : ℕ) : Set (Fin k → ℝ) :=
  orderedSimplex k 0 1 ∩
    ⋂ j : Fin k, {x : Fin k → ℝ |
      (2 : ℝ) ^ ((j.1 + 1 : ℝ) - gamma) ≤ ukPrefixExpSum v x j}

lemma measurableSet_ukPrefixRegion (k v gamma : ℕ) :
    MeasurableSet (ukPrefixRegion k v gamma) := by
  unfold ukPrefixRegion
  apply MeasurableSet.inter (measurableSet_orderedSimplex k 0 1)
  apply MeasurableSet.iInter
  intro j
  change MeasurableSet ((ukPrefixExpSum v · j) ⁻¹'
    Set.Ici ((2 : ℝ) ^ ((j.1 + 1 : ℝ) - gamma)))
  exact measurable_ukPrefixExpSum j measurableSet_Ici

lemma prefixWeight_succ_eq (k v : ℕ) (x : Fin k → ℝ) (j : Fin k) :
    prefixWeight k v (j.1 + 1) x =
      (ukPrefixExpSum v x j + 1) / (2 : ℝ) ^ (j.1 + 1) := by
  classical
  unfold prefixWeight ukPrefixExpSum
  congr 2
  have hiff (i : Fin k) : (i : ℕ) < j.1 + 1 ↔ i ≤ j := by
    constructor
    · intro h
      exact Fin.mk_le_mk.mpr (by omega)
    · intro h
      exact Nat.lt_add_one_iff.mpr (Fin.mk_le_mk.mp h)
  simp_rw [hiff]
  rw [show Finset.Iic j = Finset.univ.filter (fun i : Fin k ↦ i ≤ j) by
    ext i
    simp only [Finset.mem_Iic, Finset.mem_filter, Finset.mem_univ, true_and]]
  rw [Finset.sum_filter]

/-- The `m`-th dyadic superlevel is contained in Ford's prefix region with
parameter `γ=m+1`.  This is the pointwise heart of the integral
stratification in the proof of Lemma 3.6. -/
lemma ukSuperlevel_subset_ukPrefixRegion (k v m : ℕ) :
    ukSuperlevel k v m ⊆ ukPrefixRegion k v (m + 1) := by
  intro x hx
  unfold ukPrefixRegion
  refine ⟨hx.1, ?_⟩
  rw [Set.mem_iInter]
  intro j
  have hFprefix := (hx.2.trans
    (ukIntegrand_le_prefixWeight k v (j.1 + 1) x (by omega)))
  rw [prefixWeight_succ_eq] at hFprefix
  have hdenm : 0 < (2 : ℝ) ^ m := by positivity
  have hdeng : 0 < (2 : ℝ) ^ (j.1 + 1) := by positivity
  rw [div_le_div_iff₀ hdenm hdeng] at hFprefix
  have hxj : 0 ≤ x j := (hx.1.1 j).1
  have hone_exp : 1 ≤ (2 : ℝ) ^ ((v : ℝ) * x j) := by
    exact Real.one_le_rpow (by norm_num) (mul_nonneg (Nat.cast_nonneg _) hxj)
  have hone_sum : 1 ≤ ukPrefixExpSum v x j := by
    have hterm : (2 : ℝ) ^ ((v : ℝ) * x j) ≤ ukPrefixExpSum v x j := by
      unfold ukPrefixExpSum
      apply Finset.single_le_sum (s := Finset.Iic j)
        (f := fun i : Fin k ↦ (2 : ℝ) ^ ((v : ℝ) * x i))
      · intro i hi
        positivity
      · exact Finset.mem_Iic.mpr le_rfl
    exact hone_exp.trans hterm
  have hhalf : (2 : ℝ) ^ (j.1 + 1) / (2 : ℝ) ^ (m + 1) ≤
      ukPrefixExpSum v x j := by
    rw [pow_succ] at hFprefix
    rw [pow_succ, pow_succ]
    apply (div_le_iff₀ (mul_pos hdenm (by norm_num))).2
    nlinarith [mul_nonneg (zero_le_one.trans hone_sum) hdenm.le]
  rw [Real.rpow_sub (by norm_num)]
  have hjcast : (j.1 : ℝ) + 1 = ((j.1 + 1 : ℕ) : ℝ) := by norm_num
  rw [hjcast, Real.rpow_natCast, Real.rpow_natCast]
  simpa only [Set.mem_ofPred_eq] using hhalf

/-! ## The dyadic extraction behind Ford's cluster cover -/

private lemma sum_Iic_eq_reverse_sum {k : ℕ} (l : Fin k) (f : Fin k → ℝ) :
    (∑ i ∈ Finset.Iic l, f i) =
      ∑ d ∈ Finset.range (l.1 + 1),
        f ⟨l.1 - d, (Nat.sub_le _ _).trans_lt l.isLt⟩ := by
  classical
  apply Finset.sum_bij (fun i _ ↦ l.1 - i.1)
  · intro i hi
    simp only [Finset.mem_range]
    have hil : i.1 ≤ l.1 := Fin.mk_le_mk.mp (Finset.mem_Iic.mp hi)
    omega
  · intro i hi j hj hij
    have hil : i.1 ≤ l.1 := Fin.mk_le_mk.mp (Finset.mem_Iic.mp hi)
    have hjl : j.1 ≤ l.1 := Fin.mk_le_mk.mp (Finset.mem_Iic.mp hj)
    apply Fin.ext
    omega
  · intro d hd
    simp only [Finset.mem_range] at hd
    let i : Fin k := ⟨l.1 - d, (Nat.sub_le _ _).trans_lt l.isLt⟩
    refine ⟨i, ?_, ?_⟩
    · exact Finset.mem_Iic.mpr (Fin.mk_le_mk.mpr (Nat.sub_le _ _))
    · dsimp [i]
      omega
  · intro i hi
    congr 1
    apply Fin.ext
    have hil : i.1 ≤ l.1 := Fin.mk_le_mk.mp (Finset.mem_Iic.mp hi)
    change i.1 = l.1 - (l.1 - i.1)
    omega

/-- The coefficient sum in the powers-of-two version of Ford's dyadic
contradiction.  The first `2^(h-3)` coordinates contribute at most `1/4`;
grouping the remainder by `Nat.log 2` contributes at most `1/2`. -/
private lemma extraction_coefficient_bound_pow (L h : ℕ) (hh : 6 ≤ h) :
    (∑ d ∈ Finset.range (L + 1),
      if d < 2 ^ (h - 3) then
        1 / (2 : ℝ) ^ (h - 1)
      else
        1 / (2 : ℝ) ^ (2 * Nat.log 2 d)) < 1 := by
  classical
  let r := h - 3
  let q : ℕ → ℕ := Nat.log 2
  let high := (Finset.range (L + 1)).filter fun d ↦ 2 ^ r ≤ d
  let image := high.image q
  have hr : 3 ≤ r := by omega
  have hhr : h - 1 = r + 2 := by omega
  have hsplit :
      (∑ d ∈ Finset.range (L + 1),
        if d < 2 ^ r then 1 / (2 : ℝ) ^ (h - 1)
        else 1 / (2 : ℝ) ^ (2 * q d)) =
      (∑ d ∈ Finset.range (L + 1) with d < 2 ^ r,
        1 / (2 : ℝ) ^ (h - 1)) +
      ∑ d ∈ high, 1 / (2 : ℝ) ^ (2 * q d) := by
    have hhighset :
        (Finset.range (L + 1)).filter (fun d ↦ ¬d < 2 ^ r) = high := by
      ext d
      simp only [high, Finset.mem_filter, Finset.mem_range]
      omega
    rw [Finset.sum_ite]
    rw [hhighset]
  rw [show h - 3 = r by rfl, show Nat.log 2 = q by rfl]
  have hlow :
      (∑ d ∈ Finset.range (L + 1) with d < 2 ^ r,
          1 / (2 : ℝ) ^ (h - 1)) ≤ 1 / 4 := by
    rw [Finset.sum_const, nsmul_eq_mul]
    have hsub :
        (Finset.range (L + 1)).filter (fun d ↦ d < 2 ^ r) ⊆
          Finset.range (2 ^ r) := by
      intro d hd
      rw [Finset.mem_filter] at hd
      exact Finset.mem_range.mpr hd.2
    have hcard : ((Finset.range (L + 1)).filter
        (fun d ↦ d < 2 ^ r)).card ≤ 2 ^ r := by
      simpa using Finset.card_le_card hsub
    have hcardR : (((Finset.range (L + 1)).filter
        (fun d ↦ d < 2 ^ r)).card : ℝ) ≤ (2 : ℝ) ^ r := by
      exact_mod_cast hcard
    rw [hhr, pow_add]
    norm_num
    have hp : 0 < (2 : ℝ) ^ r := by positivity
    calc
      (((Finset.range (L + 1)).filter
          (fun d ↦ d < 2 ^ r)).card : ℝ) *
            (1 / 4 * ((2 : ℝ) ^ r)⁻¹) ≤
          (2 : ℝ) ^ r * (1 / 4 * ((2 : ℝ) ^ r)⁻¹) := by
        gcongr
      _ = 1 / 4 := by field_simp
  have hmaps : ∀ d ∈ high, q d ∈ image := by
    intro d hd
    exact Finset.mem_image_of_mem q hd
  have hfiberCard (m : ℕ) :
      (high.filter fun d ↦ q d = m).card ≤ 2 ^ (m + 1) := by
    have hsub : (high.filter fun d ↦ q d = m) ⊆
        Finset.range (2 ^ (m + 1)) := by
      intro d hd
      rw [Finset.mem_filter] at hd
      have hlt := Nat.lt_pow_succ_log_self (by omega : 1 < 2) d
      rw [show Nat.log 2 d = q d by rfl, hd.2] at hlt
      exact Finset.mem_range.mpr hlt
    have hc := Finset.card_le_card hsub
    simpa using hc
  have hfiber (m : ℕ) :
      (∑ d ∈ high with q d = m, 1 / (2 : ℝ) ^ (2 * q d)) ≤
        2 * (1 / 2 : ℝ) ^ m := by
    have hcardR : ((high.filter fun d ↦ q d = m).card : ℝ) ≤
        (2 : ℝ) ^ (m + 1) := by
      exact_mod_cast hfiberCard m
    calc
      (∑ d ∈ high with q d = m, 1 / (2 : ℝ) ^ (2 * q d)) =
          ((high.filter fun d ↦ q d = m).card : ℝ) /
            (2 : ℝ) ^ (2 * m) := by
        rw [show (∑ d ∈ high with q d = m,
            1 / (2 : ℝ) ^ (2 * q d)) =
            ∑ d ∈ high.filter (fun d ↦ q d = m),
              1 / (2 : ℝ) ^ (2 * m) by
          apply Finset.sum_congr rfl
          intro d hd
          rw [Finset.mem_filter] at hd
          rw [hd.2]]
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
      _ ≤ (2 : ℝ) ^ (m + 1) / (2 : ℝ) ^ (2 * m) := by
        gcongr
      _ = 2 * (1 / 2 : ℝ) ^ m := by
        rw [one_div_pow, pow_add, pow_mul]
        norm_num
        field_simp
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
        rw [mul_comm m 2]
        rw [pow_mul]
  have himage (m : ℕ) (hm : m ∈ image) : r ≤ m := by
    obtain ⟨d, hd, hdm⟩ := Finset.mem_image.mp hm
    have hdr : 2 ^ r ≤ d := by
      have hd' := Finset.mem_filter.mp hd
      exact hd'.2
    have hrlog : r ≤ Nat.log 2 d :=
      Nat.le_log_of_pow_le (by omega : 1 < 2) hdr
    simpa only [q, hdm] using hrlog
  let tail : ℕ → ℝ := fun m ↦
    if r ≤ m then 2 * (1 / 2 : ℝ) ^ m else 0
  have htailSummable : Summable tail := by
    apply Summable.of_nonneg_of_le
    · intro m
      dsimp [tail]
      split_ifs <;> positivity
    · intro m
      dsimp [tail]
      split_ifs
      · exact le_rfl
      · positivity
    · exact summable_geometric_two.mul_left 2
  have hhigh :
      (∑ d ∈ high, 1 / (2 : ℝ) ^ (2 * q d)) ≤ 1 / 2 := by
    have hfiberwise := Finset.sum_fiberwise_of_maps_to hmaps
      (fun d ↦ 1 / (2 : ℝ) ^ (2 * q d))
    calc
      (∑ d ∈ high, 1 / (2 : ℝ) ^ (2 * q d)) =
          ∑ m ∈ image,
            ∑ d ∈ high with q d = m,
              1 / (2 : ℝ) ^ (2 * q d) := hfiberwise.symm
      _ ≤ ∑ m ∈ image, tail m := by
        apply Finset.sum_le_sum
        intro m hm
        simpa [tail, himage m hm] using hfiber m
      _ ≤ ∑' m : ℕ, tail m :=
        htailSummable.sum_le_tsum _ (by
          intro m hm
          dsimp [tail]
          split_ifs <;> positivity)
      _ = 4 * (1 / 2 : ℝ) ^ r := by
        have hgeom := tsum_geometric_inv_two_ge r
        calc
          (∑' m : ℕ, tail m) =
              2 * ∑' m : ℕ, if r ≤ m then (1 / 2 : ℝ) ^ m else 0 := by
            rw [← tsum_mul_left]
            apply tsum_congr
            intro m
            simp only [tail, mul_ite, mul_zero]
          _ = 2 * (2 * (1 / 2 : ℝ) ^ r) := by
            rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, hgeom]
          _ = 4 * (1 / 2 : ℝ) ^ r := by ring
      _ ≤ 1 / 2 := by
        rw [one_div_pow]
        have hpNat : 2 ^ 3 ≤ 2 ^ r :=
          Nat.pow_le_pow_right (by omega : 0 < 2) hr
        have hp : (2 : ℝ) ^ 3 ≤ (2 : ℝ) ^ r := by exact_mod_cast hpNat
        rw [show 4 * (1 / (2 : ℝ) ^ r) = 4 / (2 : ℝ) ^ r by ring]
        apply (div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ r)).2
        norm_num at hp ⊢
        nlinarith
  rw [hsplit]
  linarith

/-- Ford's exact dyadic contradiction (4.7).  The coordinate gap is the
power `2^m`, while the lower barrier drops by `2m`. -/
theorem uk_prefix_cluster_extraction
    {k v gamma h : ℕ} (hv : 0 < v) (hh : 6 ≤ h)
    {x : Fin k → ℝ} (hmono : Monotone x) {l : Fin k}
    (hl : x l < (((l.1 : ℝ) + 2 - gamma - h) / v))
    (hp : (2 : ℝ) ^ (((l.1 : ℝ) + 1) - gamma) ≤ ukPrefixExpSum v x l) :
    ∃ m : ℕ, h - 3 ≤ m ∧ 2 ^ m ≤ l.1 ∧
      (((l.1 : ℝ) + 1 - gamma - 2 * m) / v) ≤
        x ⟨l.1 - 2 ^ m, (Nat.sub_le _ _).trans_lt l.isLt⟩ := by
  classical
  by_contra hnone
  push Not at hnone
  let B : ℝ := (2 : ℝ) ^ (((l.1 : ℝ) + 1) - gamma)
  have hBpos : 0 < B := by dsimp [B]; positivity
  have hvR : 0 < (v : ℝ) := by exact_mod_cast hv
  have hvne : (v : ℝ) ≠ 0 := ne_of_gt hvR
  have hfactor (n : ℕ) :
      (2 : ℝ) ^ ((((l.1 : ℝ) + 1) - gamma) - (n : ℝ)) =
        B * (1 / (2 : ℝ) ^ n) := by
    rw [Real.rpow_sub (by norm_num), Real.rpow_natCast]
    dsimp [B]
    ring
  have hpoint (d : ℕ) (hd : d ∈ Finset.range (l.1 + 1)) :
      (2 : ℝ) ^ ((v : ℝ) *
          x ⟨l.1 - d, (Nat.sub_le _ _).trans_lt l.isLt⟩) ≤
        B * (if d < 2 ^ (h - 3) then
          1 / (2 : ℝ) ^ (h - 1)
        else
          1 / (2 : ℝ) ^ (2 * Nat.log 2 d)) := by
    have hdl : d ≤ l.1 := by
      simp only [Finset.mem_range] at hd
      omega
    let i : Fin k := ⟨l.1 - d, (Nat.sub_le _ _).trans_lt l.isLt⟩
    by_cases hdsmall : d < 2 ^ (h - 3)
    · rw [if_pos hdsmall]
      have hil : i ≤ l := Fin.mk_le_mk.mpr (Nat.sub_le _ _)
      have hxi : x i < (((l.1 : ℝ) + 2 - gamma - h) / v) :=
        (hmono hil).trans_lt hl
      have hexp : (v : ℝ) * x i ≤
          (l.1 : ℝ) + 2 - gamma - h := by
        apply le_of_lt
        calc
          (v : ℝ) * x i <
              (v : ℝ) * (((l.1 : ℝ) + 2 - gamma - h) / v) :=
            mul_lt_mul_of_pos_left hxi hvR
          _ = (l.1 : ℝ) + 2 - gamma - h := by field_simp
      calc
        (2 : ℝ) ^ ((v : ℝ) * x i) ≤
            (2 : ℝ) ^ ((l.1 : ℝ) + 2 - gamma - h) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
        _ = (2 : ℝ) ^
            ((((l.1 : ℝ) + 1) - gamma) - ((h - 1 : ℕ) : ℝ)) := by
          congr 1
          norm_num [Nat.cast_sub (by omega : 1 ≤ h)]
          ring
        _ = B * (1 / (2 : ℝ) ^ (h - 1)) := hfactor (h - 1)
    · rw [if_neg hdsmall]
      have hdpos : d ≠ 0 := by
        have : 0 < 2 ^ (h - 3) := by positivity
        omega
      have hlarge : h - 3 ≤ Nat.log 2 d :=
        Nat.le_log_of_pow_le (by omega : 1 < 2) (by omega)
      have hpowle : 2 ^ Nat.log 2 d ≤ d :=
        Nat.pow_log_le_self 2 hdpos
      have hqle : 2 ^ Nat.log 2 d ≤ l.1 := hpowle.trans hdl
      let j : Fin k :=
        ⟨l.1 - 2 ^ Nat.log 2 d, (Nat.sub_le _ _).trans_lt l.isLt⟩
      have hij : i ≤ j := Fin.mk_le_mk.mpr (by omega)
      have hxj : x j <
          (((l.1 : ℝ) + 1 - gamma -
            ((2 * Nat.log 2 d : ℕ) : ℝ)) / v) := by
        simpa only [j, Nat.cast_mul, Nat.cast_ofNat] using
          hnone (Nat.log 2 d) hlarge hqle
      have hxi : x i <
          (((l.1 : ℝ) + 1 - gamma -
            ((2 * Nat.log 2 d : ℕ) : ℝ)) / v) :=
        (hmono hij).trans_lt hxj
      have hexp : (v : ℝ) * x i ≤
          (l.1 : ℝ) + 1 - gamma -
            ((2 * Nat.log 2 d : ℕ) : ℝ) := by
        apply le_of_lt
        calc
          (v : ℝ) * x i < (v : ℝ) *
              (((l.1 : ℝ) + 1 - gamma -
                ((2 * Nat.log 2 d : ℕ) : ℝ)) / v) :=
            mul_lt_mul_of_pos_left hxi hvR
          _ = (l.1 : ℝ) + 1 - gamma -
              ((2 * Nat.log 2 d : ℕ) : ℝ) := by field_simp
      calc
        (2 : ℝ) ^ ((v : ℝ) * x i) ≤
            (2 : ℝ) ^ ((l.1 : ℝ) + 1 - gamma -
              ((2 * Nat.log 2 d : ℕ) : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
        _ = (2 : ℝ) ^ ((((l.1 : ℝ) + 1) - gamma) -
            ((2 * Nat.log 2 d : ℕ) : ℝ)) := by
          congr 1
        _ = B * (1 / (2 : ℝ) ^ (2 * Nat.log 2 d)) := hfactor _
  have hcoeff := extraction_coefficient_bound_pow l.1 h hh
  have hpfxlt : ukPrefixExpSum v x l < B := by
    unfold ukPrefixExpSum
    rw [sum_Iic_eq_reverse_sum]
    calc
      (∑ d ∈ Finset.range (l.1 + 1),
          (2 : ℝ) ^ ((v : ℝ) *
            x ⟨l.1 - d, (Nat.sub_le _ _).trans_lt l.isLt⟩)) ≤
          ∑ d ∈ Finset.range (l.1 + 1),
            B * (if d < 2 ^ (h - 3) then
              1 / (2 : ℝ) ^ (h - 1)
            else
              1 / (2 : ℝ) ^ (2 * Nat.log 2 d)) := by
        apply Finset.sum_le_sum
        intro d hd
        exact hpoint d hd
      _ = B * (∑ d ∈ Finset.range (l.1 + 1),
            if d < 2 ^ (h - 3) then
              1 / (2 : ℝ) ^ (h - 1)
            else
              1 / (2 : ℝ) ^ (2 * Nat.log 2 d)) := by
        rw [Finset.mul_sum]
      _ < B * 1 := mul_lt_mul_of_pos_left hcoeff hBpos
      _ = B := mul_one B
  exact (hp.trans_lt hpfxlt).false

/-! ## Integral stratification -/

/-- The constant upper endpoint of a dyadic layer, supported on the
corresponding superlevel. -/
noncomputable def ukLayer (k v m : ℕ) : (Fin k → ℝ) → ℝ :=
  (ukSuperlevel k v m).indicator (fun _ ↦ 2 / (2 : ℝ) ^ m)

lemma volume_ukSuperlevel_ne_top (k v m : ℕ) :
    volume (ukSuperlevel k v m) ≠ ⊤ := by
  apply lt_top_iff_ne_top.mp
  calc
    volume (ukSuperlevel k v m) ≤ volume (orderedSimplex k 0 1) :=
      measure_mono Set.inter_subset_left
    _ < ⊤ := by
      rw [volume_orderedSimplex k (by norm_num)]
      simp

lemma integrable_ukLayer (k v m : ℕ) : Integrable (ukLayer k v m) := by
  unfold ukLayer
  rw [integrable_indicator_iff (measurableSet_ukSuperlevel k v m)]
  exact integrableOn_const (volume_ukSuperlevel_ne_top k v m)

lemma integrableOn_ukIntegrand (k v : ℕ) :
    IntegrableOn (ukIntegrand k v) (orderedSimplex k 0 1) := by
  have hvol : volume (orderedSimplex k 0 1) ≠ ⊤ := by
    apply lt_top_iff_ne_top.mp
    rw [volume_orderedSimplex k (by norm_num)]
    simp
  have hc : IntegrableOn (fun _ : Fin k → ℝ ↦ (1 : ℝ))
      (orderedSimplex k 0 1) := integrableOn_const hvol
  apply hc.mono'
  · exact (measurable_ukIntegrand k v).aestronglyMeasurable.mono_measure
      Measure.restrict_le_self
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (ukIntegrand_nonneg k v x)]
    exact ukIntegrand_le_one k v x

lemma ukIntegrand_le_sum_layers {k v : ℕ} {x : Fin k → ℝ}
    (hx : x ∈ orderedSimplex k 0 1) :
    ukIntegrand k v x ≤ ∑ m ∈ Finset.range (k + 1), ukLayer k v m x := by
  obtain ⟨m, hmk, hmlo, hmhi⟩ := exists_dyadic_cover
    (one_div_pow_le_ukIntegrand k v x) (ukIntegrand_le_one k v x)
  calc
    ukIntegrand k v x ≤ 2 / (2 : ℝ) ^ m := hmhi
    _ = ukLayer k v m x := by
      rw [ukLayer, Set.indicator_of_mem]
      exact ⟨hx, hmlo⟩
    _ ≤ ∑ i ∈ Finset.range (k + 1), ukLayer k v i x := by
      apply Finset.single_le_sum (s := Finset.range (k + 1))
        (f := fun i ↦ ukLayer k v i x)
      · intro i hi
        unfold ukLayer
        by_cases hxi : x ∈ ukSuperlevel k v i
        · rw [Set.indicator_of_mem hxi]
          positivity
        · simp [Set.indicator, hxi]
      · simp only [Finset.mem_range]
        omega

/-- Exact finite integral stratification used in Ford's proof of Lemma 3.6.
There is no unrecorded limiting argument: positivity gives the uniform lower
cutoff `2⁻ᵏ`, hence the `k+1` displayed layers cover the integrand. -/
theorem uk_le_sum_superlevel_volume (k v : ℕ) :
    uk k v ≤ ∑ m ∈ Finset.range (k + 1),
      (volume (ukSuperlevel k v m)).toReal * (2 / (2 : ℝ) ^ m) := by
  have hsumInt : Integrable
      (fun x : Fin k → ℝ ↦ ∑ m ∈ Finset.range (k + 1), ukLayer k v m x)
      (volume.restrict (orderedSimplex k 0 1)) := by
    apply integrable_finsetSum
    intro m hm
    exact (integrable_ukLayer k v m).mono_measure Measure.restrict_le_self
  unfold uk
  calc
    (∫ x in orderedSimplex k 0 1, ukIntegrand k v x) ≤
        ∫ x in orderedSimplex k 0 1,
          ∑ m ∈ Finset.range (k + 1), ukLayer k v m x := by
      apply integral_mono_ae (integrableOn_ukIntegrand k v) hsumInt
      filter_upwards [ae_restrict_mem (measurableSet_orderedSimplex k 0 1)] with x hx
      exact ukIntegrand_le_sum_layers hx
    _ = ∑ m ∈ Finset.range (k + 1),
        ∫ x in orderedSimplex k 0 1, ukLayer k v m x := by
      apply integral_finsetSum
      intro m hm
      exact (integrable_ukLayer k v m).mono_measure Measure.restrict_le_self
    _ = ∑ m ∈ Finset.range (k + 1),
        (volume (ukSuperlevel k v m)).toReal * (2 / (2 : ℝ) ^ m) := by
      apply Finset.sum_congr rfl
      intro m hm
      unfold ukLayer
      rw [integral_indicator_const _ (measurableSet_ukSuperlevel k v m)]
      rw [Measure.real, Measure.restrict_apply (measurableSet_ukSuperlevel k v m)]
      rw [Set.inter_eq_left.mpr (fun x hx ↦ hx.1)]
      simp only [smul_eq_mul]

/-- The zero-dimensional integral is exactly one.  This discharges the
`k=0` endpoint of Lemma 3.6 separately from the positive-dimensional cluster
estimate. -/
theorem uk_zero (v : ℕ) : uk 0 v = 1 := by
  classical
  have hvol : (volume (orderedSimplex 0 0 1)).toReal = 1 := by
    rw [volume_orderedSimplex 0 (by norm_num : (0 : ℝ) ≤ 1)]
    norm_num
  have hvol' : volume.real (orderedSimplex 0 0 1) = 1 := by
    simpa [Measure.real] using hvol
  simp [uk, ukIntegrand, ukIntegrandAux, prefixWeight, hvol']

end Erdos896.Ford
