/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ErdosProblems.Erdos144.Harmonic

/-!
# Concrete regularity bounds on the harmonic stages

This file specializes the finite Chernoff bookkeeping to the exact scales
`Harmonic.lowerScale` and `Harmonic.stageTop`.  Its deterministic input is an
entirely finite lower bound for reciprocal mass.  A dyadic shell is split
into sixteen equal blocks, giving

`sum_{k=17}^{32} 1/k > 203/300`.

Three such shells form one octave, so an `r`-octave tail has reciprocal mass
at least `(203/100) r`.  This retains the initial `s` octaves that do not
appear in the regularity threshold `2(r-s)`, and consequently gives an error
that tends to zero with `s`, uniformly in the stage number.
-/

open scoped BigOperators Topology

namespace Erdos144.HarmonicStageRegularity

noncomputable section

open HarmonicProb

attribute [local instance] Classical.propDecidable

/-- The explicit rational estimate used in one dyadic shell. -/
theorem two_hundred_three_div_three_hundred_lt_sum_Ioc_sixteen_thirty_two :
    (203 / 300 : ℝ) <
      ∑ k ∈ (Finset.Ioc 16 32 : Finset ℕ), (1 : ℝ) / k := by
  norm_num [Finset.sum_Ioc_succ_top]

/-- Splitting `(16m,(16+t)m]` into `t` consecutive blocks shows that its
reciprocal mass dominates the corresponding sum of `1/k`. -/
theorem sum_Ioc_reciprocal_le_scaled_param
    (m t : ℕ) (hm : 1 ≤ m) :
    (∑ k ∈ Finset.Ioc 16 (16 + t), (1 : ℝ) / k) ≤
      ∑ n ∈ Finset.Ioc (16 * m) ((16 + t) * m), param n := by
  induction t with
  | zero => simp
  | succ t ih =>
      let q := 16 + t
      have hq : 16 ≤ q := by omega
      have hqm : 16 * m ≤ q * m := Nat.mul_le_mul_right m hq
      have hqsuccm : q * m ≤ (q + 1) * m :=
        Nat.mul_le_mul_right m (Nat.le_succ q)
      have hdisj : Disjoint (Finset.Ioc (16 * m) (q * m))
          (Finset.Ioc (q * m) ((q + 1) * m)) :=
        Finset.disjoint_left.mpr fun n hn₁ hn₂ => by
          simp only [Finset.mem_Ioc] at hn₁ hn₂
          omega
      have hblock :
          (1 : ℝ) / (q + 1 : ℕ) ≤
            ∑ n ∈ Finset.Ioc (q * m) ((q + 1) * m), param n := by
        have hv : 1 ≤ (q + 1) * m :=
          Nat.mul_pos (Nat.succ_pos q) (Nat.zero_lt_of_lt hm)
        have hraw := sub_div_right_le_sum_Ioc_param
          (u := q * m) (v := (q + 1) * m) hv
        have hsub : (q + 1) * m - q * m = m := by
          rw [Nat.add_mul]
          omega
        have hmR : (m : ℝ) ≠ 0 := by
          exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt hm))
        calc
          (1 : ℝ) / (q + 1 : ℕ) =
              (m : ℝ) / (((q + 1) * m : ℕ) : ℝ) := by
            push_cast
            field_simp
          _ = (((q + 1) * m - q * m : ℕ) : ℝ) /
              (((q + 1) * m : ℕ) : ℝ) := by rw [hsub]
          _ ≤ ∑ n ∈ Finset.Ioc (q * m) ((q + 1) * m), param n := hraw
      change (∑ k ∈ Finset.Ioc 16 (q + 1), (1 : ℝ) / k) ≤
        ∑ n ∈ Finset.Ioc (16 * m) ((q + 1) * m), param n
      rw [Finset.sum_Ioc_succ_top hq]
      rw [← Finset.Ioc_union_Ioc_eq_Ioc hqm hqsuccm,
        Finset.sum_union hdisj]
      exact add_le_add ih hblock

/-- Every dyadic shell whose left endpoint is a positive multiple of sixteen
has reciprocal mass at least `203/300`. -/
theorem dyadicShell_param_ge
    (A : ℕ) (hA : 0 < A) (h16 : 16 ∣ A) :
    (203 / 300 : ℝ) ≤ ∑ n ∈ Finset.Ioc A (2 * A), param n := by
  rcases h16 with ⟨m, rfl⟩
  have hm : 1 ≤ m := by
    by_contra hm0
    have : m = 0 := Nat.eq_zero_of_not_pos hm0
    subst m
    simp at hA
  have hscaled := sum_Ioc_reciprocal_le_scaled_param m 16 hm
  norm_num at hscaled ⊢
  exact le_trans
    (two_hundred_three_div_three_hundred_lt_sum_Ioc_sixteen_thirty_two).le
    (by
      rw [show 2 * (16 * m) = 32 * m by ring]
      simpa [one_div] using hscaled)

private theorem sum_Ioc_concat
    (f : ℕ → ℝ) {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    (∑ n ∈ Finset.Ioc a c, f n) =
      (∑ n ∈ Finset.Ioc a b, f n) + ∑ n ∈ Finset.Ioc b c, f n := by
  have hdisj : Disjoint (Finset.Ioc a b) (Finset.Ioc b c) :=
    Finset.disjoint_left.mpr fun n hn₁ hn₂ => by
      simp only [Finset.mem_Ioc] at hn₁ hn₂
      omega
  rw [← Finset.Ioc_union_Ioc_eq_Ioc hab hbc, Finset.sum_union hdisj]

/-- Three dyadic shells make one octave, with reciprocal mass at least
`203/100`. -/
theorem octaveShell_param_ge
    (A : ℕ) (hA : 0 < A) (h16 : 16 ∣ A) :
    (203 / 100 : ℝ) ≤ ∑ n ∈ Finset.Ioc A (8 * A), param n := by
  have h16two : 16 ∣ 2 * A := by
    rcases h16 with ⟨m, rfl⟩
    exact ⟨2 * m, by ring⟩
  have h16four : 16 ∣ 4 * A := by
    rcases h16 with ⟨m, rfl⟩
    exact ⟨4 * m, by ring⟩
  have h₁ := dyadicShell_param_ge A hA h16
  have h₂ := dyadicShell_param_ge (2 * A) (by positivity) h16two
  have h₃ := dyadicShell_param_ge (4 * A) (by positivity) h16four
  have h₂' :
      (203 / 300 : ℝ) ≤
        ∑ n ∈ Finset.Ioc (2 * A) (4 * A), param n := by
    rw [show 4 * A = 2 * (2 * A) by ring]
    exact h₂
  have h₃' :
      (203 / 300 : ℝ) ≤
        ∑ n ∈ Finset.Ioc (4 * A) (8 * A), param n := by
    rw [show 8 * A = 2 * (4 * A) by ring]
    exact h₃
  have hsplit₁ := sum_Ioc_concat param
    (show A ≤ 2 * A by omega) (show 2 * A ≤ 4 * A by omega)
  have hsplit₂ := sum_Ioc_concat param
    (show A ≤ 4 * A by omega) (show 4 * A ≤ 8 * A by omega)
  rw [hsplit₂, hsplit₁]
  norm_num at h₁ h₂' h₃' ⊢
  nlinarith

/-- Iterating the preceding estimate over `q` octaves. -/
theorem repeatedOctave_param_ge
    (A q : ℕ) (hA : 0 < A) (h16 : 16 ∣ A) :
    (203 / 100 : ℝ) * q ≤
      ∑ n ∈ Finset.Ioc A (8 ^ q * A), param n := by
  induction q with
  | zero => simp
  | succ q ih =>
      let B := 8 ^ q * A
      have hB : 0 < B := by positivity
      have h16B : 16 ∣ B := by
        rcases h16 with ⟨m, rfl⟩
        exact ⟨8 ^ q * m, by simp [B]; ring⟩
      have hAB : A ≤ B := by
        have hp : 1 ≤ 8 ^ q := Nat.one_le_pow q 8 (by norm_num)
        simpa [B, mul_comm] using Nat.mul_le_mul_right A hp
      have hBB : B ≤ 8 * B := by omega
      have hoct := octaveShell_param_ge B hB h16B
      have hsplit := sum_Ioc_concat param hAB hBB
      have hend : 8 ^ (q + 1) * A = 8 * B := by
        simp [B, pow_succ]
        ring
      rw [hend, hsplit]
      push_cast
      nlinarith

theorem sixteen_dvd_pow_eight {E : ℕ} (hE : 2 ≤ E) :
    16 ∣ 8 ^ E := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hE
  rw [pow_add]
  exact ⟨4 * 8 ^ k, by norm_num; ring⟩

/-- A concrete `r`-octave tail starting above `8^E` has reciprocal mass at
least `(203/100)r`. -/
theorem powEight_div_tail_param_ge
    (E R r : ℕ) (hE : 2 ≤ E) (hr : r ≤ R) :
    (203 / 100 : ℝ) * r ≤
      ∑ n ∈ Finset.Ioc (8 ^ (E + R) / 8 ^ r) (8 ^ (E + R)), param n := by
  have hrER : r ≤ E + R := le_trans hr (Nat.le_add_left R E)
  rw [Nat.pow_div hrER (by norm_num : 0 < 8)]
  let A := 8 ^ (E + R - r)
  have hExp : E ≤ E + R - r := by omega
  have hA : 0 < A := by positivity
  have h16A : 16 ∣ A :=
    sixteen_dvd_pow_eight (hE.trans hExp)
  have hmass := repeatedOctave_param_ge A r hA h16A
  have hend : 8 ^ r * A = 8 ^ (E + R) := by
    simp only [A]
    rw [← pow_add]
    congr 1
    omega
  simpa [A, hend] using hmass

/-- The exact eight-adic depth from `Harmonic.lowerScale s` to
`Harmonic.stageTop s j`. -/
def stageDepth (s j : ℕ) : ℕ :=
  19 * Harmonic.lowerExponent s + Harmonic.stageStride s * j

theorem stageTop_eq_pow_lowerExponent_add_depth (s j : ℕ) :
    Harmonic.stageTop s j =
      8 ^ (Harmonic.lowerExponent s + stageDepth s j) := by
  unfold Harmonic.stageTop stageDepth
  congr 1
  omega

theorem two_le_lowerExponent {s : ℕ} (hs : 2 ≤ s) :
    2 ≤ Harmonic.lowerExponent s := by
  have hc : 1 ≤ Harmonic.stageCount s := Harmonic.stageCount_pos s
  have hc2 : 1 ≤ Harmonic.stageCount s ^ 2 := one_le_pow₀ hc
  simpa [Harmonic.lowerExponent] using Nat.mul_le_mul hs hc2

/-- Deterministic reciprocal mass for every exact tail of a harmonic stage. -/
theorem stageTail_param_ge
    {s : ℕ} (hs : 2 ≤ s) (j r : ℕ) (hr : r ≤ stageDepth s j) :
    (203 / 100 : ℝ) * r ≤
      ∑ n ∈ Finset.Ioc
        (Harmonic.stageTop s j / 8 ^ r) (Harmonic.stageTop s j), param n := by
  rw [stageTop_eq_pow_lowerExponent_add_depth]
  exact powEight_div_tail_param_ge
    (Harmonic.lowerExponent s) (stageDepth s j) r
    (two_le_lowerExponent hs) hr

/-! ## Chernoff and stage specialization -/

/-- The Chernoff estimate retaining the full `r`-octave mass while the
regularity threshold only asks for `2(r-base)` selected points. -/
theorem prob_inter_card_lt_two_sub_le_exp_neg_index
    (I tail : Finset ℕ) (htail : tail ⊆ I)
    (htailPos : ∀ n ∈ tail, 1 ≤ n) {base r : ℕ} (hbase : base ≤ r)
    (hmean : (203 / 100 : ℝ) * r ≤ ∑ n ∈ tail, param n) :
    prob I (fun T => (T ∩ tail).card < 2 * (r - base)) ≤
      Real.exp (-(r : ℝ) / 10000) := by
  have hK : ((2 * (r - base) : ℕ) : ℝ) ≤
      (200 / 203 : ℝ) * ∑ n ∈ tail, param n := by
    push_cast
    rw [Nat.cast_sub hbase]
    nlinarith
  have h := Erdos697.Bernoulli.lower_tail_chernoff tail param
    (fun n _ => param_nonneg n)
    (fun n hn => param_le_one (htailPos n hn))
    (hEW := rfl) (r := (200 / 203 : ℝ))
    (by norm_num) (by norm_num) hK
  have hcoeff :
      (200 / 203 : ℝ) *
          ((1 - (200 / 203 : ℝ)) / (2 * (200 / 203 : ℝ))) +
          (1 / (1 + ((1 - (200 / 203 : ℝ)) /
            (2 * (200 / 203 : ℝ)))) - 1) =
        -(9 / 163618 : ℝ) := by
    norm_num
  rw [hcoeff] at h
  rw [HarmonicRegularity.prob_inter_eq I tail
    (fun T => T.card < 2 * (r - base)) htail]
  calc
    prob tail (fun T => T.card < 2 * (r - base)) ≤
        Real.exp (-(9 / 163618 : ℝ) * ∑ n ∈ tail, param n) := by
      simpa [prob, HarmonicProb.weight] using h
    _ ≤ Real.exp (-(r : ℝ) / 10000) := by
      apply Real.exp_le_exp.mpr
      nlinarith

/-- The exact finite error sum for regularity at stage `(s,j)`. -/
def stageRegularityError (s j : ℕ) : ℝ :=
  ∑ r ∈ Finset.Ioc s (stageDepth s j),
    Real.exp (-(r : ℝ) / 10000)

/-- The concrete regularity estimate on the actual harmonic stage
`(lowerScale s, stageTop s j]`. -/
theorem prob_stage_not_octaveRegular_le
    {s : ℕ} (hs : 2 ≤ s) (j : ℕ) :
    prob (Finset.Ioc (Harmonic.lowerScale s) (Harmonic.stageTop s j))
        (fun T => ¬ HarmonicOctaves.OctaveRegular
          (Harmonic.stageTop s j) (stageDepth s j) s T) ≤
      stageRegularityError s j := by
  let C := Harmonic.lowerScale s
  let D := Harmonic.stageTop s j
  let R := stageDepth s j
  let I := Finset.Ioc C D
  let tail : ℕ → Finset ℕ := fun r => Finset.Ioc (D / 8 ^ r) D
  let bad : ℕ → Finset ℕ → Prop := fun r T =>
    (T ∩ tail r).card < 2 * (r - s)
  have hIpos : ∀ n ∈ I, 1 ≤ n := by
    intro n hn
    have hn0 := (Finset.mem_Ioc.mp hn).1
    omega
  have hbad : ∀ T,
      ¬ HarmonicOctaves.OctaveRegular D R s T →
        ∃ r ∈ Finset.Ioc s R, bad r T := by
    intro T hT
    simp only [HarmonicOctaves.OctaveRegular, not_forall, not_le] at hT
    rcases hT with ⟨r, hr, hlt⟩
    have hrs : s < r := by
      rcases Finset.mem_Icc.mp hr with ⟨hsr, _⟩
      omega
    exact ⟨r, Finset.mem_Ioc.mpr ⟨hrs, (Finset.mem_Icc.mp hr).2⟩, hlt⟩
  have htailSubset : ∀ r ∈ Finset.Ioc s R, tail r ⊆ I := by
    intro r hr n hn
    have hrR : r ≤ R := (Finset.mem_Ioc.mp hr).2
    have hrER : r ≤ Harmonic.lowerExponent s + R :=
      hrR.trans (Nat.le_add_left R (Harmonic.lowerExponent s))
    have hdiv : D / 8 ^ r =
        8 ^ (Harmonic.lowerExponent s + R - r) := by
      rw [show D = 8 ^ (Harmonic.lowerExponent s + R) by
        exact stageTop_eq_pow_lowerExponent_add_depth s j]
      exact Nat.pow_div hrER (by norm_num)
    have hExp : Harmonic.lowerExponent s ≤
        Harmonic.lowerExponent s + R - r := by omega
    have hpow : 8 ^ Harmonic.lowerExponent s ≤
        8 ^ (Harmonic.lowerExponent s + R - r) :=
      Nat.pow_le_pow_right (by norm_num) hExp
    rcases Finset.mem_Ioc.mp hn with ⟨hnleft, hnright⟩
    apply Finset.mem_Ioc.mpr
    refine ⟨?_, hnright⟩
    change 8 ^ Harmonic.lowerExponent s < n
    exact lt_of_le_of_lt (by simpa [hdiv] using hpow) hnleft
  change prob I (fun T => ¬ HarmonicOctaves.OctaveRegular D R s T) ≤ _
  calc
    prob I (fun T => ¬ HarmonicOctaves.OctaveRegular D R s T) ≤
        prob I (fun T => ∃ r ∈ Finset.Ioc s R, bad r T) :=
      prob_mono I _ _ hIpos hbad
    _ ≤ ∑ r ∈ Finset.Ioc s R, prob I (bad r) :=
      prob_exists_le_sum I (Finset.Ioc s R) bad hIpos
    _ ≤ ∑ r ∈ Finset.Ioc s R, Real.exp (-(r : ℝ) / 10000) := by
      apply Finset.sum_le_sum
      intro r hr
      apply prob_inter_card_lt_two_sub_le_exp_neg_index
        I (tail r) (htailSubset r hr)
      · intro n hn
        exact hIpos n (htailSubset r hr hn)
      · exact (Finset.mem_Ioc.mp hr).1.le
      · simpa [D, R, tail] using
          stageTail_param_ge hs j r (Finset.mem_Ioc.mp hr).2
    _ = stageRegularityError s j := by
      rfl

/-- A single geometric-tail error function valid for every stage. -/
def uniformStageRegularityError (s : ℕ) : ℝ :=
  Real.exp (-(s : ℝ) / 10000) /
    (1 - Real.exp (-(1 : ℝ) / 10000))

theorem stageDepth_mono_right {s j k : ℕ} (hjk : j ≤ k) :
    stageDepth s j ≤ stageDepth s k := by
  unfold stageDepth
  exact Nat.add_le_add_left
    (Nat.mul_le_mul_left (Harmonic.stageStride s) hjk) _

private theorem sum_Ioc_exp_neg_index_le_uniform (s R : ℕ) :
    (∑ r ∈ Finset.Ioc s R, Real.exp (-(r : ℝ) / 10000)) ≤
      uniformStageRegularityError s := by
  let q : ℝ := Real.exp (-(1 : ℝ) / 10000)
  have hq0 : 0 ≤ q := Real.exp_pos _ |>.le
  have hq1 : q < 1 := by
    dsimp [q]
    exact Real.exp_lt_one_iff.mpr (by norm_num)
  have hden : 0 < 1 - q := sub_pos.mpr hq1
  have hterm : ∀ r : ℕ,
      Real.exp (-(r : ℝ) / 10000) = q ^ r := by
    intro r
    dsimp [q]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hpartial : ∀ N : ℕ,
      (∑ k ∈ Finset.range N, q ^ k) ≤ 1 / (1 - q) := by
    intro N
    have hqne : q ≠ 1 := ne_of_lt hq1
    calc
      (∑ k ∈ Finset.range N, q ^ k) = (q ^ N - 1) / (q - 1) :=
        geom_sum_eq hqne N
      _ = (1 - q ^ N) / (1 - q) := by
        field_simp [hqne]
        ring
      _ ≤ 1 / (1 - q) := by
        apply (div_le_div_iff_of_pos_right hden).2
        nlinarith [pow_nonneg hq0 N]
  have hset : Finset.Ioc s R = Finset.Ico (s + 1) (R + 1) := by
    ext r
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  rw [hset, Finset.sum_Ico_eq_sum_range]
  simp_rw [hterm]
  calc
    (∑ k ∈ Finset.range (R + 1 - (s + 1)), q ^ (s + 1 + k)) =
        q ^ (s + 1) *
          (∑ k ∈ Finset.range (R + 1 - (s + 1)), q ^ k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [pow_add]
    _ ≤ q ^ (s + 1) * (1 / (1 - q)) := by
      gcongr
      exact hpartial _
    _ ≤ q ^ s * (1 / (1 - q)) := by
      have hpow : q ^ (s + 1) ≤ q ^ s := by
        rw [pow_succ]
        nlinarith [pow_nonneg hq0 s]
      exact mul_le_mul_of_nonneg_right hpow (by positivity)
    _ = uniformStageRegularityError s := by
      rw [← hterm s]
      simp only [uniformStageRegularityError, q]
      ring

theorem stageRegularityError_le_uniform (s j : ℕ) :
    stageRegularityError s j ≤ uniformStageRegularityError s := by
  exact sum_Ioc_exp_neg_index_le_uniform s (stageDepth s j)

theorem uniformStageRegularityError_nonneg (s : ℕ) :
    0 ≤ uniformStageRegularityError s := by
  unfold uniformStageRegularityError
  exact div_nonneg (Real.exp_pos _).le
    (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by norm_num)))

theorem tendsto_uniformStageRegularityError_zero :
    Filter.Tendsto uniformStageRegularityError Filter.atTop (𝓝 0) := by
  have hscale : Filter.Tendsto
      (fun s : ℕ => (1 / 10000 : ℝ) * (s : ℝ))
      Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num)
      tendsto_natCast_atTop_atTop
  have hnum : Filter.Tendsto
      (fun s : ℕ => Real.exp (-(s : ℝ) / 10000))
      Filter.atTop (𝓝 0) := by
    have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp hscale
    have heq :
        (fun s : ℕ => Real.exp (-(s : ℝ) / 10000)) =
          (fun s : ℕ => Real.exp (-((1 / 10000 : ℝ) * (s : ℝ)))) := by
      funext s
      congr 1
      ring
    rw [heq]
    change Filter.Tendsto
      (fun s : ℕ => Real.exp (-((1 / 10000 : ℝ) * (s : ℝ))))
      Filter.atTop (𝓝 0) at h
    exact h
  change Filter.Tendsto
    (fun s : ℕ => Real.exp (-(s : ℝ) / 10000) /
      (1 - Real.exp (-(1 : ℝ) / 10000))) Filter.atTop (𝓝 0)
  simpa using hnum.div_const (1 - Real.exp (-(1 : ℝ) / 10000))

/-- Uniform-in-stage form of the concrete regularity estimate. -/
theorem prob_stage_not_octaveRegular_le_uniform
    {s : ℕ} (hs : 2 ≤ s) {j : ℕ}
    (_hj : j ≤ Harmonic.stageCount s) :
    prob (Finset.Ioc (Harmonic.lowerScale s) (Harmonic.stageTop s j))
        (fun T => ¬ HarmonicOctaves.OctaveRegular
          (Harmonic.stageTop s j) (stageDepth s j) s T) ≤
      uniformStageRegularityError s :=
  (prob_stage_not_octaveRegular_le hs j).trans
    (stageRegularityError_le_uniform s j)

/-- Direct adapter supplying the regularity term in
`Harmonic.prob_reservoirIrregular_le` on the exact stage scales. -/
theorem prob_stage_reservoirIrregular_le
    {s : ℕ} (hs : 2 ≤ s) {j : ℕ}
    (hj : j ≤ Harmonic.stageCount s)
    (hexpect : HarmonicOctaves.normalizedOffDiagonalExpectation
      (Finset.Ioc (Harmonic.lowerScale s) (Harmonic.stageTop s j))
      (HarmonicOctaves.OctaveRegular
        (Harmonic.stageTop s j) (stageDepth s j) s) ≤
      1200 * (8 : ℝ) ^ s / Harmonic.stageTop s j) :
    prob (Finset.Ioc (Harmonic.lowerScale s) (Harmonic.stageTop s j))
        (Harmonic.ReservoirIrregular (Harmonic.stageTop s j)
          (stageDepth s j) s (Harmonic.xi s)) ≤
      uniformStageRegularityError s +
        9600 * (8 : ℝ) ^ s / Harmonic.xi s +
        1 / (Harmonic.xi s : ℝ) := by
  apply Harmonic.prob_reservoirIrregular_le
    (I := Finset.Ioc (Harmonic.lowerScale s) (Harmonic.stageTop s j))
    (D := Harmonic.stageTop s j) (R := stageDepth s j)
    (s := s) (ξ := Harmonic.xi s)
    (regularityError := uniformStageRegularityError s)
  · intro n hn
    have hn0 := (Finset.mem_Ioc.mp hn).1
    omega
  · intro n hn
    rcases Finset.mem_Ioc.mp hn with ⟨hnC, hnD⟩
    exact Finset.mem_Icc.mpr ⟨by omega, hnD⟩
  · unfold Harmonic.stageTop
    positivity
  · exact Harmonic.xi_pos s
  · exact prob_stage_not_octaveRegular_le_uniform hs hj
  · exact hexpect

end


end Erdos144.HarmonicStageRegularity
