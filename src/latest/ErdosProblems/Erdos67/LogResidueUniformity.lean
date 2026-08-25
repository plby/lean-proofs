import ErdosProblems.Erdos67.LogCRTConcentration
import ErdosProblems.Erdos67.LogProbability
import ErdosProblems.Erdos67.MRTVinogradov
import Mathlib.Algebra.BigOperators.Module

/-!
# Uniformity of residues under finite logarithmic probability

This file proves the elementary residue-equidistribution estimate needed by the
CRT concentration step.  For the normalized harmonic law on a finite interval,
the pushforward modulo a fixed positive modulus is close in `L¹` to the uniform
law.  The proof is finite Abel summation applied to centered residue indicators.
-/

open scoped BigOperators NNReal
open Finset

namespace Erdos67

noncomputable section

open FiniteEntropy

/-- The centered indicator of one residue class. -/
def centeredResidueIndicator (M : ℕ) [NeZero M] (r : ZMod M) (n : ℕ) : ℝ :=
  (if (n : ZMod M) = r then 1 else 0) - (M : ℝ)⁻¹

theorem abs_centeredResidueIndicator_le_one
    (M : ℕ) [NeZero M] (r : ZMod M) (n : ℕ) :
    |centeredResidueIndicator M r n| ≤ 1 := by
  have hM : (1 : ℝ) ≤ M := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne M)
  have hinv0 : 0 ≤ (M : ℝ)⁻¹ := by positivity
  have hinv1 : (M : ℝ)⁻¹ ≤ 1 := by
    exact (inv_le_one₀ (by positivity : (0 : ℝ) < M)).2 hM
  unfold centeredResidueIndicator
  split_ifs
  · rw [abs_of_nonneg (sub_nonneg.mpr hinv1)]
    linarith
  · rw [zero_sub, abs_neg, abs_of_nonneg hinv0]
    exact hinv1

/-- One complete residue block has zero centered mass. -/
theorem sum_range_centeredResidueIndicator
    (M : ℕ) [NeZero M] (r : ZMod M) :
    ∑ n ∈ Finset.range M, centeredResidueIndicator M r n = 0 := by
  have hfin :
      (∑ i : Fin M, centeredResidueIndicator M r i.val) =
        ∑ n ∈ Finset.range M, centeredResidueIndicator M r n := by
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro n hn
    rw [dif_pos (Finset.mem_range.mp hn)]
  rw [← hfin]
  simp only [centeredResidueIndicator]
  have hfilter :
      (Finset.univ.filter fun i : Fin M ↦ ((i.val : ℕ) : ZMod M) = r) =
        {⟨r.val, r.val_lt⟩} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · intro hi
      apply Fin.ext
      have hv := congrArg ZMod.val hi
      simpa [Nat.mod_eq_of_lt i.isLt] using hv
    · rintro rfl
      exact ZMod.natCast_zmod_val r
  have hcard :
      (Finset.univ.filter fun i : Fin M ↦ ((i.val : ℕ) : ZMod M) = r).card = 1 := by
    rw [hfilter]
    simp
  simp [hcard, Nat.cast_ne_zero.mpr (NeZero.ne M)]

/-- A prefix of a centered residue indicator has discrepancy at most one. -/
theorem abs_sum_range_centeredResidueIndicator_le_one
    (M : ℕ) [NeZero M] (r : ZMod M) (N : ℕ) :
    |∑ n ∈ Finset.range N, centeredResidueIndicator M r n| ≤ 1 := by
  let G : ℕ → ℝ := fun n ↦ centeredResidueIndicator M r n
  have hmod (n : ℕ) : G (n % M) = G n := by
    simp only [G, centeredResidueIndicator]
    have hcast : ((n % M : ℕ) : ZMod M) = (n : ZMod M) := by
      simp
    rw [hcast]
  have hblocks (B : ℕ) : ∑ n ∈ Finset.range (B * M), G n = 0 := by
    calc
      ∑ n ∈ Finset.range (B * M), G n =
          ∑ n ∈ Finset.range (B * M), G (n % M) := by
            apply Finset.sum_congr rfl
            intro n hn
            exact (hmod n).symm
      _ = (B : ℝ) * ∑ n ∈ Finset.range M, G n :=
        MRTVinogradov.sum_range_mul_mod G M B
      _ = 0 := by
        rw [show (∑ n ∈ Finset.range M, G n) = 0 by
          exact sum_range_centeredResidueIndicator M r]
        simp
  have hdecomp : N = (N / M) * M + N % M := by
    calc
      N = N % M + M * (N / M) := (Nat.mod_add_div N M).symm
      _ = (N / M) * M + N % M := by
        rw [Nat.mul_comm, Nat.add_comm]
  rw [hdecomp, Finset.sum_range_add, hblocks, zero_add]
  let t := N % M
  let base := (N / M) * M
  let hits := (Finset.range t).filter
    (fun x ↦ ((base + x : ℕ) : ZMod M) = r)
  have hMpos : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have htM : t < M := Nat.mod_lt N hMpos
  have hhits : hits.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro x hx y hy
    have hx' := Finset.mem_filter.mp hx
    have hy' := Finset.mem_filter.mp hy
    have hxM : x < M := (Finset.mem_range.mp hx'.1).trans htM
    have hyM : y < M := (Finset.mem_range.mp hy'.1).trans htM
    have hxyZ : ((base + x : ℕ) : ZMod M) = ((base + y : ℕ) : ZMod M) :=
      hx'.2.trans hy'.2.symm
    have hxyCast : (x : ZMod M) = (y : ZMod M) := by
      have hadd : (base : ZMod M) + (x : ZMod M) =
          (base : ZMod M) + (y : ZMod M) := by
        simpa only [Nat.cast_add] using hxyZ
      exact add_left_cancel hadd
    have hv := congrArg ZMod.val hxyCast
    simpa [Nat.mod_eq_of_lt hxM, Nat.mod_eq_of_lt hyM] using hv
  have htNonneg : (0 : ℝ) ≤ (t : ℝ) * (M : ℝ)⁻¹ := by positivity
  have htLeOne : (t : ℝ) * (M : ℝ)⁻¹ ≤ 1 := by
    calc
      (t : ℝ) * (M : ℝ)⁻¹ ≤ (M : ℝ) * (M : ℝ)⁻¹ := by
        apply mul_le_mul_of_nonneg_right
        · exact_mod_cast htM.le
        · positivity
      _ = 1 := mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne M))
  have hhitsNonneg : (0 : ℝ) ≤ hits.card := by
    exact_mod_cast Nat.zero_le hits.card
  have hhitsLeOne : (hits.card : ℝ) ≤ 1 := by exact_mod_cast hhits
  have htail :
      ∑ x ∈ Finset.range t, G (base + x) =
        (hits.card : ℝ) - (t : ℝ) * (M : ℝ)⁻¹ := by
    simp only [G, centeredResidueIndicator, Finset.sum_sub_distrib]
    simp [hits]
  change |∑ x ∈ Finset.range t, G (base + x)| ≤ 1
  rw [htail, abs_le]
  constructor <;> linarith

/-- The weaker block-size prefix bound, retained as a convenient compatibility form. -/
theorem abs_sum_range_centeredResidueIndicator_le
    (M : ℕ) [NeZero M] (r : ZMod M) (N : ℕ) :
    |∑ n ∈ Finset.range N, centeredResidueIndicator M r n| ≤ M := by
  calc
    |∑ n ∈ Finset.range N, centeredResidueIndicator M r n| ≤ 1 :=
      abs_sum_range_centeredResidueIndicator_le_one M r N
    _ ≤ M := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne M)

/-- Telescoping identity for forward differences on a natural interval. -/
theorem sum_Ico_sub_succ (f : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    ∑ n ∈ Finset.Ico a b, (f n - f (n + 1)) = f a - f b := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
      rw [Finset.sum_Ico_succ_top hab, ih]
      ring

/-- Abel summation for a bounded-prefix sequence against harmonic weights. -/
theorem abs_harmonic_sum_le_of_abs_prefix_le
    {L U : ℕ} (hL : 0 < L) (hLU : L ≤ U)
    (g : ℕ → ℝ) (B : ℝ) (_hB : 0 ≤ B)
    (hprefix : ∀ N, |∑ n ∈ Finset.range N, g n| ≤ B) :
    |∑ n ∈ Finset.Icc L U, (n : ℝ)⁻¹ * g n| ≤ 2 * B / L := by
  let f : ℕ → ℝ := fun n ↦ (n : ℝ)⁻¹
  let G : ℕ → ℝ := fun N ↦ ∑ n ∈ Finset.range N, g n
  have hlt : L < U + 1 := by omega
  have hab := Finset.sum_Ico_by_parts f g hlt
  have hIcc : Finset.Icc L U = Finset.Ico L (U + 1) := by
    ext n
    simp
  rw [hIcc]
  change |∑ n ∈ Finset.Ico L (U + 1), f n • g n| ≤ 2 * B / L
  rw [hab]
  simp only [Nat.add_sub_cancel, smul_eq_mul]
  have hf_nonneg (n : ℕ) : 0 ≤ f n := by
    simp [f]
  have hf_anti {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n) : f n ≤ f m := by
    simp only [f]
    exact inv_anti₀ (by exact_mod_cast hm) (by exact_mod_cast hmn)
  have hGU : |G (U + 1)| ≤ B := hprefix (U + 1)
  have hGL : |G L| ≤ B := hprefix L
  have htermU : |f U * G (U + 1)| ≤ f U * B := by
    rw [abs_mul, abs_of_nonneg (hf_nonneg U)]
    exact mul_le_mul_of_nonneg_left hGU (hf_nonneg U)
  have htermL : |f L * G L| ≤ f L * B := by
    rw [abs_mul, abs_of_nonneg (hf_nonneg L)]
    exact mul_le_mul_of_nonneg_left hGL (hf_nonneg L)
  have hsum :
      |∑ n ∈ Finset.Ico L U, (f (n + 1) - f n) * G (n + 1)| ≤
        (f L - f U) * B := by
    calc
      |∑ n ∈ Finset.Ico L U, (f (n + 1) - f n) * G (n + 1)| ≤
          ∑ n ∈ Finset.Ico L U,
            |(f (n + 1) - f n) * G (n + 1)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Finset.Ico L U, (f n - f (n + 1)) * B := by
        apply Finset.sum_le_sum
        intro n hn
        have hnpos : 0 < n := hL.trans_le (Finset.mem_Ico.mp hn).1
        have hmono : f (n + 1) ≤ f n := hf_anti hnpos (Nat.le_succ n)
        rw [abs_mul, abs_of_nonpos (sub_nonpos.mpr hmono), neg_sub]
        exact mul_le_mul_of_nonneg_left (hprefix (n + 1)) (sub_nonneg.mpr hmono)
      _ = (f L - f U) * B := by
        rw [← Finset.sum_mul, sum_Ico_sub_succ f hLU]
  let A : ℝ := f U * G (U + 1)
  let D : ℝ := f L * G L
  let S : ℝ := ∑ n ∈ Finset.Ico L U, (f (n + 1) - f n) * G (n + 1)
  change |A - D - S| ≤ 2 * B / L
  calc
    |A - D - S| ≤ |A| + |D| + |S| := by
      calc
        |A - D - S| ≤ |A - D| + |S| := abs_sub _ _
        _ ≤ (|A| + |D|) + |S| := by
          have ht := add_le_add_right (abs_sub A D) |S|
          linarith
        _ = |A| + |D| + |S| := rfl
    _ ≤ f U * B + f L * B + (f L - f U) * B := by linarith
    _ = 2 * B / L := by
      simp only [f, div_eq_mul_inv]
      ring

theorem finiteLaw_apply_eq_sum_ite
    {Ω α : Type*} [Fintype Ω] [Fintype α] [DecidableEq α]
    (p : FinProb Ω) (X : Ω → α) (a : α) :
    law p X a = ∑ ω : Ω, if X ω = a then p ω else 0 := by
  classical
  simp only [law, stdSimplex.map_coe, FunOnFinite.linearMap_apply_apply]
  rw [← Finset.sum_filter]

theorem logProbMassNN_coe_eq_sum {L U : ℕ} :
    (logProbMassNN L U : ℝ) =
      ∑ n : LogProbIndex L U, (n.1 : ℝ)⁻¹ := by
  simp [logProbMassNN, logProbHarmonicNN_coe]

theorem logProbWeightNN_coe_eq {L U : ℕ} (n : LogProbIndex L U) :
    (logProbWeightNN L U n : ℝ) =
      (n.1 : ℝ)⁻¹ / (logProbMassNN L U : ℝ) := by
  simp [logProbWeightNN, logProbHarmonicNN_coe]

/-- A single residue coordinate differs from uniform by the Abel-summation error. -/
theorem abs_logProb_residue_coordinate_sub_uniform_le
    {L U M : ℕ} [NeZero M] (hL : 0 < L) (hLU : L ≤ U) (r : ZMod M) :
    |law (logProbFiniteLaw L U hL hLU) (fun n ↦ (n.1 : ZMod M)) r -
        uniformFiniteLaw (ZMod M) r| ≤
      2 / (L * (logProbMassNN L U : ℝ)) := by
  let H : ℝ := (logProbMassNN L U : ℝ)
  have hHpos : 0 < H := by
    exact_mod_cast logProbMassNN_pos hL hLU
  have hHne : H ≠ 0 := hHpos.ne'
  have hMpos : (0 : ℝ) < M := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  have hMne : (M : ℝ) ≠ 0 := hMpos.ne'
  have hmass : H = ∑ n : LogProbIndex L U, (n.1 : ℝ)⁻¹ := by
    exact logProbMassNN_coe_eq_sum
  have hcoord :
      law (logProbFiniteLaw L U hL hLU) (fun n ↦ (n.1 : ZMod M)) r -
          uniformFiniteLaw (ZMod M) r =
        H⁻¹ * ∑ n : LogProbIndex L U,
          (n.1 : ℝ)⁻¹ * centeredResidueIndicator M r n.1 := by
    rw [finiteLaw_apply_eq_sum_ite, uniformFiniteLaw_apply, ZMod.card]
    simp only [logProbFiniteLaw_apply, logProbWeightNN_coe_eq]
    simp only [centeredResidueIndicator]
    change
      (∑ x : LogProbIndex L U,
          if (x.1 : ZMod M) = r then (x.1 : ℝ)⁻¹ / H else 0) -
          (M : ℝ)⁻¹ =
        H⁻¹ * ∑ n : LogProbIndex L U,
          (n.1 : ℝ)⁻¹ * ((if (n.1 : ZMod M) = r then 1 else 0) - (M : ℝ)⁻¹)
    have hite (n : LogProbIndex L U) :
        (if (n.1 : ZMod M) = r then (n.1 : ℝ)⁻¹ / H else 0) =
          H⁻¹ * ((n.1 : ℝ)⁻¹ *
            (if (n.1 : ZMod M) = r then 1 else 0)) := by
      by_cases hn : (n.1 : ZMod M) = r
      · simp [hn, div_eq_mul_inv]
        ring
      · simp [hn]
    simp_rw [hite]
    rw [← Finset.mul_sum]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← hmass]
    field_simp [hHne, hMne]
  rw [hcoord, abs_mul, abs_of_nonneg (inv_nonneg.mpr hHpos.le)]
  have hsumSubtype :
      (∑ n : LogProbIndex L U,
          (n.1 : ℝ)⁻¹ * centeredResidueIndicator M r n.1) =
        ∑ n ∈ Finset.Icc L U,
          (n : ℝ)⁻¹ * centeredResidueIndicator M r n := by
    exact (Finset.sum_subtype (Finset.Icc L U) (fun _ ↦ Iff.rfl)
      (fun n ↦ (n : ℝ)⁻¹ * centeredResidueIndicator M r n)).symm
  rw [hsumSubtype]
  have hab := abs_harmonic_sum_le_of_abs_prefix_le hL hLU
    (centeredResidueIndicator M r) 1 (by positivity)
    (fun N ↦ abs_sum_range_centeredResidueIndicator_le_one M r N)
  have hab' :
      |∑ n ∈ Finset.Icc L U, (n : ℝ)⁻¹ * centeredResidueIndicator M r n| ≤
        2 / L := by
    simpa using hab
  calc
    H⁻¹ *
        |∑ n ∈ Finset.Icc L U, (n : ℝ)⁻¹ * centeredResidueIndicator M r n| ≤
        H⁻¹ * (2 / L) :=
      mul_le_mul_of_nonneg_left hab' (inv_nonneg.mpr hHpos.le)
    _ = 2 / (L * (logProbMassNN L U : ℝ)) := by
      dsimp [H]
      field_simp

/-- The exact `δuniform` input for `finiteLaw_block_crt_bounded_bilinear_concentration`.

For each fixed CRT modulus `M`, the displayed bound tends to zero as the lower
endpoint tends to infinity (and the harmonic mass stays bounded below), exactly
the ordering of choices in the Elliott parameter hierarchy. -/
theorem logProbFiniteLaw_residue_l1Dist_uniform_le
    {L U M : ℕ} [NeZero M] (hL : 0 < L) (hLU : L ≤ U) :
    l1Dist
        (law (logProbFiniteLaw L U hL hLU) (fun n ↦ (n.1 : ZMod M)))
        (uniformFiniteLaw (ZMod M)) ≤
      2 * M / (L * (logProbMassNN L U : ℝ)) := by
  unfold l1Dist
  calc
    ∑ r : ZMod M,
        |law (logProbFiniteLaw L U hL hLU) (fun n ↦ (n.1 : ZMod M)) r -
          uniformFiniteLaw (ZMod M) r| ≤
        ∑ _r : ZMod M,
          2 / (L * (logProbMassNN L U : ℝ)) := by
      apply Finset.sum_le_sum
      intro r hr
      exact abs_logProb_residue_coordinate_sub_uniform_le hL hLU r
    _ = 2 * M / (L * (logProbMassNN L U : ℝ)) := by
      rw [Finset.sum_const, Finset.card_univ, ZMod.card]
      ring

/-- The residue-uniformity estimate specialized to the product modulus appearing
verbatim in `finiteLaw_block_crt_bounded_bilinear_concentration`. -/
theorem logProbFiniteLaw_crt_residue_l1Dist_uniform_le
    {L U : ℕ} (hL : 0 < L) (hLU : L ≤ U)
    {ι : Type*} [Fintype ι] (a : ι → ℕ) [NeZero (∏ i, a i)] :
    l1Dist
        (law (logProbFiniteLaw L U hL hLU)
          (fun n ↦ (n.1 : ZMod (∏ i, a i))))
        (uniformFiniteLaw (ZMod (∏ i, a i))) ≤
      2 * (∏ i, a i : ℕ) /
        (L * (logProbMassNN L U : ℝ)) := by
  exact logProbFiniteLaw_residue_l1Dist_uniform_le hL hLU

end

end Erdos67
