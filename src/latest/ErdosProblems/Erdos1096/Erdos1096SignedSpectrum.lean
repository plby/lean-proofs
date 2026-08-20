import ErdosProblems.Erdos1096.Erdos1096Core
import ErdosProblems.Erdos1096.Erdos1096Smyth

open Filter Set Polynomial
open scoped BigOperators Pointwise Topology ComplexConjugate

noncomputable section

namespace Erdos1096

def SignedSpectrum (q : ℝ) : Set ℝ :=
  {y | ∃ p : ℤ[X], (∀ i, |p.coeff i| ≤ 1) ∧
    y = p.eval₂ (algebraMap ℤ ℝ) q}

def HasAccumulation (A : Set ℝ) : Prop :=
  ∃ a : ℝ, AccPt a (Filter.principal A)

lemma finite_bounded_of_no_accumulation {A : Set ℝ} (hA : ¬ HasAccumulation A)
    (M : ℝ) : (A ∩ Set.Icc (-M) M).Finite := by
  by_contra hinf
  have hinf' : (A ∩ Set.Icc (-M) M).Infinite := hinf
  obtain ⟨a, ha, hacc⟩ :=
    hinf'.exists_accPt_of_subset_isCompact
      (isCompact_Icc : IsCompact (Set.Icc (-M) M)) inter_subset_right
  apply hA
  refine ⟨a, ?_⟩
  exact hacc.mono (Filter.principal_mono.mpr inter_subset_left)

lemma finite_of_bounded_subset_no_accumulation {A B : Set ℝ}
    (hA : ¬ HasAccumulation A) (hBA : B ⊆ A) (M : ℝ)
    (hbound : B ⊆ Set.Icc (-M) M) : B.Finite := by
  exact (finite_bounded_of_no_accumulation hA M).subset
    (fun x hx ↦ ⟨hBA hx, hbound hx⟩)

def reversedPolynomial (s : ℕ → ℤ) (n : ℕ) : ℤ[X] :=
  Polynomial.ofFn (n + 1) (fun j ↦ s (n - j.1))

lemma reversedPolynomial_coeff (s : ℕ → ℤ) (n i : ℕ) :
    (reversedPolynomial s n).coeff i = if i ≤ n then s (n - i) else 0 := by
  by_cases hi : i ≤ n
  · rw [if_pos hi]
    exact Polynomial.ofFn_coeff_eq_val_of_lt _ (by omega)
  · rw [if_neg hi]
    exact Polynomial.ofFn_coeff_eq_zero_of_ge _ (by omega)

lemma reversedPolynomial_height_one {s : ℕ → ℤ}
    (hs : ∀ i, |s i| ≤ 1) (n i : ℕ) :
    |(reversedPolynomial s n).coeff i| ≤ 1 := by
  rw [reversedPolynomial_coeff]
  split_ifs
  · exact hs _
  · norm_num

lemma eval₂_reversedPolynomial (q : ℝ) (s : ℕ → ℤ) (n : ℕ) :
    (reversedPolynomial s n).eval₂ (algebraMap ℤ ℝ) q =
      ∑ i ∈ Finset.range (n + 1), (s i : ℝ) * q ^ (n - i) := by
  rw [reversedPolynomial, Polynomial.eval₂_eq_sum_range' (algebraMap ℤ ℝ)
    (Polynomial.ofFn_natDegree_lt (by omega) (fun j : Fin (n + 1) ↦ s (n - j.1))) q]
  rw [← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ n := by simpa using hi
  rw [Polynomial.ofFn_coeff_eq_val_of_lt _ (by omega)]
  simp only [Nat.add_sub_cancel, Nat.succ_sub_succ_eq_sub]
  simp [Nat.sub_sub_self hi']

lemma reversedPolynomial_eval_mem_signedSpectrum {q : ℝ} {s : ℕ → ℤ}
    (hs : ∀ i, |s i| ≤ 1) (n : ℕ) :
    (reversedPolynomial s n).eval₂ (algebraMap ℤ ℝ) q ∈ SignedSpectrum q := by
  exact ⟨reversedPolynomial s n, reversedPolynomial_height_one hs n, rfl⟩

def expansionSignedDigits (d : ℕ → ℕ) : ℕ → ℤ
  | 0 => -1
  | n + 1 => d n

def SignedExpansion (q : ℝ) (s : ℕ → ℤ) : Prop :=
  HasSum (fun i ↦ (s i : ℝ) * q⁻¹ ^ i) 0

lemma expansionSignedDigits_height_one {d : ℕ → ℕ}
    (hd : ∀ n, d n = 0 ∨ d n = 1) (i : ℕ) :
    |expansionSignedDigits d i| ≤ 1 := by
  cases i with
  | zero => norm_num [expansionSignedDigits]
  | succ i => rcases hd i with h | h <;> simp [expansionSignedDigits, h]

lemma summable_signed_series {q : ℝ} (hq : 1 < q) {s : ℕ → ℤ}
    (hs : ∀ i, |s i| ≤ 1) :
    Summable (fun i ↦ (s i : ℝ) * q⁻¹ ^ i) := by
  have hqinv0 : 0 ≤ q⁻¹ := inv_nonneg.mpr (by linarith)
  have hqinv1 : q⁻¹ < 1 := inv_lt_one_of_one_lt₀ hq
  apply Summable.of_norm_bounded
    (summable_geometric_of_lt_one hqinv0 hqinv1)
  intro i
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hqinv0]
  have hscast : |(s i : ℝ)| ≤ 1 := by exact_mod_cast hs i
  exact mul_le_of_le_one_left (pow_nonneg hqinv0 _) hscast

lemma hasSum_expansionSignedDigits_value {q x : ℝ} (hq : 1 < q)
    {d : ℕ → ℕ} (hd : ∀ n, d n = 0 ∨ d n = 1)
    (hdsum : Tendsto (fun n ↦ ∑ i ∈ Finset.range n,
      (d i : ℝ) * q⁻¹ ^ (i + 1)) atTop (𝓝 x)) :
    HasSum (fun i ↦ (expansionSignedDigits d i : ℝ) * q⁻¹ ^ i) (-1 + x) := by
  let s := expansionSignedDigits d
  have hs : ∀ i, |s i| ≤ 1 := expansionSignedDigits_height_one hd
  have hsummable := summable_signed_series (q := q) hq hs
  rw [hsummable.hasSum_iff_tendsto_nat]
  apply (tendsto_add_atTop_iff_nat 1).mp
  have hconst : Tendsto (fun _ : ℕ ↦ (-1 : ℝ)) atTop (𝓝 (-1)) :=
    tendsto_const_nhds
  convert hconst.add hdsum using 1
  funext n
  have heq : ∀ m : ℕ,
      (∑ i ∈ Finset.range (m + 1), (s i : ℝ) * q⁻¹ ^ i) =
        -1 + ∑ i ∈ Finset.range m, (d i : ℝ) * q⁻¹ ^ (i + 1) := by
    intro m
    induction m with
    | zero => simp [s, expansionSignedDigits]
    | succ m ih =>
        calc
          (∑ i ∈ Finset.range (m + 1 + 1), (s i : ℝ) * q⁻¹ ^ i) =
              (∑ i ∈ Finset.range (m + 1), (s i : ℝ) * q⁻¹ ^ i) +
                (s (m + 1) : ℝ) * q⁻¹ ^ (m + 1) := by
            rw [Finset.sum_range_succ]
          _ = (-1 + ∑ i ∈ Finset.range m, (d i : ℝ) * q⁻¹ ^ (i + 1)) +
                (s (m + 1) : ℝ) * q⁻¹ ^ (m + 1) := by rw [ih]
          _ = -1 + ∑ i ∈ Finset.range (m + 1),
                (d i : ℝ) * q⁻¹ ^ (i + 1) := by
            rw [Finset.sum_range_succ]
            simp only [s, expansionSignedDigits, Int.cast_natCast]
            ring
  · exact heq n

lemma hasSum_expansionSignedDigits {q : ℝ} (hq : 1 < q)
    {d : ℕ → ℕ} (hd : ∀ n, d n = 0 ∨ d n = 1)
    (hdsum : Tendsto (fun n ↦ ∑ i ∈ Finset.range n,
      (d i : ℝ) * q⁻¹ ^ (i + 1)) atTop (𝓝 1)) :
    SignedExpansion q (expansionSignedDigits d) := by
  simpa [SignedExpansion] using hasSum_expansionSignedDigits_value hq hd hdsum

lemma exists_signed_expansion_of_one {q : ℝ} (hq1 : 1 < q) (hq2 : q ≤ 2) :
    ∃ s : ℕ → ℤ, (∀ i, |s i| ≤ 1) ∧ s 0 = -1 ∧ SignedExpansion q s := by
  have hone : (1 : ℝ) ≤ 1 / (q - 1) := by
    rw [le_div_iff₀ (sub_pos.mpr hq1)]
    linarith
  obtain ⟨d, hd, hdsum⟩ := exists_binary_expansion hq1 hq2 zero_le_one hone
  refine ⟨expansionSignedDigits d, expansionSignedDigits_height_one hd, rfl, ?_⟩
  exact hasSum_expansionSignedDigits hq1 hd hdsum

lemma tsum_inv_pow_succ {q : ℝ} (hq : 1 < q) :
    (∑' n : ℕ, q⁻¹ ^ (n + 1)) = 1 / (q - 1) := by
  have hq0 : q ≠ 0 := by linarith
  have hqi0 : 0 ≤ q⁻¹ := inv_nonneg.mpr (by linarith)
  have hqi1 : q⁻¹ < 1 := inv_lt_one_of_one_lt₀ hq
  rw [show (fun n : ℕ ↦ q⁻¹ ^ (n + 1)) = fun n ↦ q⁻¹ * q⁻¹ ^ n by
    funext n; rw [pow_succ, mul_comm]]
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one]
  · field_simp
  · simpa [Real.norm_eq_abs, abs_of_pos (by linarith : 0 < q)]

def lazySignedDigits (P : Set ℕ) [DecidablePred (· ∈ P)] (d : ℕ → ℕ) : ℕ → ℤ
  | 0 => -1
  | n + 1 => if n ∈ P then d n else (d n : ℤ) - 1

lemma lazySignedDigits_height_one {P : Set ℕ} [DecidablePred (· ∈ P)] {d : ℕ → ℕ}
    (hd : ∀ n, d n = 0 ∨ d n = 1) (i : ℕ) :
    |lazySignedDigits P d i| ≤ 1 := by
  cases i with
  | zero => norm_num [lazySignedDigits]
  | succ i =>
      rcases hd i with hi | hi <;> by_cases hP : i ∈ P <;>
        simp [lazySignedDigits, hi, hP]

lemma exists_lazy_signed_expansion {q : ℝ} (hq1 : 1 < q) (hq2 : q ≤ 2)
    (P : Set ℕ) [DecidablePred (· ∈ P)]
    (hPmass : 1 ≤ ∑' n : ℕ, if n ∈ P then q⁻¹ ^ (n + 1) else 0) :
    ∃ s : ℕ → ℤ, (∀ i, |s i| ≤ 1) ∧ s 0 = -1 ∧ SignedExpansion q s ∧
      (∀ n ∈ P, 0 ≤ s (n + 1)) ∧ (∀ n ∉ P, s (n + 1) ≤ 0) := by
  let a : ℕ → ℝ := fun n ↦ if n ∈ P then q⁻¹ ^ (n + 1) else 0
  let b : ℕ → ℝ := fun n ↦ if n ∈ P then 0 else q⁻¹ ^ (n + 1)
  have hqi0 : 0 ≤ q⁻¹ := inv_nonneg.mpr (by linarith)
  have hqi1 : q⁻¹ < 1 := inv_lt_one_of_one_lt₀ hq1
  have hgeom : Summable (fun n : ℕ ↦ q⁻¹ ^ (n + 1)) := by
    simpa [pow_succ, mul_comm] using
      (summable_geometric_of_lt_one hqi0 hqi1).mul_left q⁻¹
  have ha0 : ∀ n, 0 ≤ a n := by
    intro n
    simp only [a]
    split_ifs <;> positivity
  have hb0 : ∀ n, 0 ≤ b n := by
    intro n
    simp only [b]
    split_ifs <;> positivity
  have ha_le : ∀ n, a n ≤ q⁻¹ ^ (n + 1) := by
    intro n
    by_cases hP : n ∈ P
    · simp [a, hP]
    · simp [a, hP]
      exact pow_nonneg (by linarith) _
  have hb_le : ∀ n, b n ≤ q⁻¹ ^ (n + 1) := by
    intro n
    by_cases hP : n ∈ P
    · simp [b, hP]
      exact pow_nonneg (by linarith) _
    · simp [b, hP]
  have hasum : Summable a := Summable.of_nonneg_of_le ha0 ha_le hgeom
  have hbsum : Summable b := Summable.of_nonneg_of_le hb0 hb_le hgeom
  have hab (n : ℕ) : a n + b n = q⁻¹ ^ (n + 1) := by
    simp only [a, b]
    by_cases hP : n ∈ P <;> simp [hP]
  have htotal : (∑' n, a n) + ∑' n, b n = 1 / (q - 1) := by
    rw [← (hasum.tsum_add hbsum)]
    rw [show (fun n ↦ a n + b n) = fun n ↦ q⁻¹ ^ (n + 1) by
      funext n; exact hab n]
    exact tsum_inv_pow_succ hq1
  let x : ℝ := 1 + ∑' n, b n
  have hx0 : 0 ≤ x := by
    dsimp only [x]
    exact add_nonneg zero_le_one (tsum_nonneg hb0)
  have hx1 : x ≤ 1 / (q - 1) := by
    have hmass : 1 ≤ ∑' n, a n := by simpa [a] using hPmass
    dsimp only [x]
    linarith
  obtain ⟨d, hd, hdsum⟩ := exists_binary_expansion hq1 hq2 hx0 hx1
  let base : ℕ → ℤ := expansionSignedDigits d
  let c : ℕ → ℤ
    | 0 => 0
    | n + 1 => if n ∈ P then 0 else -1
  let s : ℕ → ℤ := lazySignedDigits P d
  have hbase : HasSum (fun i ↦ (base i : ℝ) * q⁻¹ ^ i) (∑' n, b n) := by
    have := hasSum_expansionSignedDigits_value hq1 hd hdsum
    simpa [base, x] using this
  have hcsum : Summable (fun i ↦ (c i : ℝ) * q⁻¹ ^ i) := by
    apply Summable.of_norm_bounded
      (summable_geometric_of_lt_one hqi0 hqi1)
    intro i
    cases i with
    | zero => simp [c]
    | succ i =>
        by_cases hP : i ∈ P
        · simp [c, hP]
          positivity
        · simp [c, hP, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < q)]
  have hctsum : (∑' i, (c i : ℝ) * q⁻¹ ^ i) = -(∑' n, b n) := by
    have hsplit := hcsum.sum_add_tsum_nat_add 1
    have htail : (∑' n, (c (n + 1) : ℝ) * q⁻¹ ^ (n + 1)) = -(∑' n, b n) := by
      rw [← tsum_neg]
      apply tsum_congr
      intro n
      by_cases hP : n ∈ P <;> simp [c, b, hP]
    calc
      (∑' i, (c i : ℝ) * q⁻¹ ^ i) =
          (∑ i ∈ Finset.range 1, (c i : ℝ) * q⁻¹ ^ i) +
            ∑' i, (c (i + 1) : ℝ) * q⁻¹ ^ (i + 1) := hsplit.symm
      _ = -(∑' n, b n) := by rw [htail]; simp [c]
  have hc : HasSum (fun i ↦ (c i : ℝ) * q⁻¹ ^ i) (-(∑' n, b n)) := by
    rw [← hctsum]
    exact hcsum.hasSum
  have hsPoint (i : ℕ) : (base i : ℝ) * q⁻¹ ^ i + (c i : ℝ) * q⁻¹ ^ i =
      (s i : ℝ) * q⁻¹ ^ i := by
    rw [← add_mul]
    congr 1
    cases i with
    | zero => norm_num [base, c, s, expansionSignedDigits, lazySignedDigits]
    | succ i =>
        by_cases hP : i ∈ P <;>
          simp [base, c, s, expansionSignedDigits, lazySignedDigits, hP] <;> ring
  have hsExp : SignedExpansion q s := by
    rw [SignedExpansion]
    convert hbase.add hc using 1
    · funext i
      exact (hsPoint i).symm
    · ring
  refine ⟨s, ?_, by simp [s, lazySignedDigits], hsExp, ?_, ?_⟩
  · intro i
    exact lazySignedDigits_height_one hd i
  · intro n hn
    rcases hd n with hd0 | hd1
    · simp [s, lazySignedDigits, hn, hd0]
    · simp [s, lazySignedDigits, hn, hd1]
  · intro n hn
    rcases hd n with hd0 | hd1
    · simp [s, lazySignedDigits, hn, hd0]
    · simp [s, lazySignedDigits, hn, hd1]

lemma exists_positive_term_with_nonpositive_tails {a : ℕ → ℝ}
    (ha : HasSum a 0) (ha0 : 0 < a 0) :
    ∃ n : ℕ, 0 < a n ∧ ∀ k : ℕ, ∑ i ∈ Finset.range k, a (n + 1 + i) ≤ 0 := by
  classical
  let S : ℕ → ℝ := fun n ↦ ∑ i ∈ Finset.range (n + 1), a i
  have hStend : Tendsto S atTop (𝓝 0) := by
    have h := ha.tendsto_sum_nat
    have hc := h.comp (tendsto_add_atTop_nat 1)
    convert hc using 1
    funext n
    simp [S, Function.comp_apply, Nat.add_comm]
  have hS0 : 0 < S 0 := by simpa [S] using ha0
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hStend) (S 0 / 2) (by linarith)
  have hlate : ∀ k, N ≤ k → S k < S 0 := by
    intro k hk
    have hkdist := hN k hk
    rw [Real.dist_eq, sub_zero, abs_lt] at hkdist
    linarith
  have hrange : (Finset.range (N + 1)).Nonempty := by simp
  obtain ⟨r, hrmem, hrmax⟩ := Finset.exists_max_image (Finset.range (N + 1)) S hrange
  have hrGlobal : ∀ k, S k ≤ S r := by
    intro k
    by_cases hk : k < N + 1
    · exact hrmax k (by simpa using hk)
    · have hkN : N ≤ k := by omega
      have hlt := hlate k hkN
      have h0mem : 0 ∈ Finset.range (N + 1) := by simp
      exact hlt.le.trans (hrmax 0 h0mem)
  let G : ℕ → Prop := fun n ↦ ∀ k, S k ≤ S n
  have hG : ∃ n, G n := ⟨r, hrGlobal⟩
  let n := Nat.find hG
  have hnG : G n := Nat.find_spec hG
  have hapos : 0 < a n := by
    by_cases hn0 : n = 0
    · simpa [hn0] using ha0
    · let m := n - 1
      have hmn : m + 1 = n := by dsimp [m]; omega
      have hstep : S n = S m + a n := by
        rw [← hmn]
        simp [S, Finset.sum_range_succ]
      by_contra hnot
      have hale : a n ≤ 0 := le_of_not_gt hnot
      have hSnm : S n ≤ S m := by linarith
      have hmnlt : m < n := by dsimp [m]; omega
      have hmG : G m := by
        intro k
        exact (hnG k).trans hSnm
      have hfind : m < Nat.find hG := by simpa [n] using hmnlt
      exact Nat.find_min hG hfind hmG
  refine ⟨n, hapos, fun k ↦ ?_⟩
  have htail : S (n + k) = S n + ∑ i ∈ Finset.range k, a (n + 1 + i) := by
    dsimp only [S]
    rw [show n + k + 1 = (n + 1) + k by omega, Finset.sum_range_add]
  have := hnG (n + k)
  linarith

lemma exists_complex_separator_of_norm_gt_one {p : ℂ} (hp : 1 < ‖p‖)
    (hpNonpos : p.re < 1 ∨ p.im ≠ 0) :
    ∃ w : ℂ, 0 < w.re ∧
      ∀ k : ℕ, ∑ i ∈ Finset.range k, (w * p⁻¹ ^ (i + 1)).re ≤ 0 := by
  have hp0 : p ≠ 0 := by
    intro h
    norm_num [h] at hp
  by_cases hpre : p.re < 1
  · refine ⟨1 - p, by simp; linarith, fun k ↦ ?_⟩
    have htel : ∑ i ∈ Finset.range k, (1 - p) * p⁻¹ ^ (i + 1) = p⁻¹ ^ k - 1 := by
      induction k with
      | zero => simp
      | succ k ih =>
          rw [Finset.sum_range_succ, ih]
          have hcancel : p * p⁻¹ ^ (k + 1) = p⁻¹ ^ k := by
            rw [pow_succ]
            calc
              p * (p⁻¹ ^ k * p⁻¹) = p⁻¹ ^ k * (p * p⁻¹) := by ring
              _ = p⁻¹ ^ k := by simp [hp0]
          rw [sub_mul, one_mul, hcancel]
          ring
    have hreSum :
        (∑ i ∈ Finset.range k, ((1 - p) * p⁻¹ ^ (i + 1)).re) =
          (∑ i ∈ Finset.range k, (1 - p) * p⁻¹ ^ (i + 1)).re := by
      simpa only [Complex.reCLM_apply] using
        (map_sum (Complex.reCLM : ℂ →L[ℝ] ℝ)
          (fun i ↦ (1 - p) * p⁻¹ ^ (i + 1)) (Finset.range k)).symm
    rw [hreSum, htel]
    calc
      (p⁻¹ ^ k - 1).re = (p⁻¹ ^ k).re - 1 := by simp
      _ ≤ ‖p⁻¹ ^ k‖ - 1 := sub_le_sub_right (Complex.re_le_norm _) 1
      _ ≤ 0 := by
        rw [norm_pow, norm_inv]
        have hinv : ‖p‖⁻¹ ≤ 1 := (inv_le_one₀ (norm_pos_iff.mpr hp0)).2 hp.le
        linarith [pow_le_one₀ (n := k) (inv_nonneg.mpr (norm_nonneg p)) hinv]
  · have hpim : p.im ≠ 0 := hpNonpos.resolve_left hpre
    let z0 : ℂ := (1 - p⁻¹) * Complex.I
    have hz0re : z0.re ≠ 0 := by
      have hnormsq : Complex.normSq p ≠ 0 := ne_of_gt (Complex.normSq_pos.mpr hp0)
      have hinvim : p⁻¹.im ≠ 0 := by
        rw [Complex.inv_im]
        exact div_ne_zero (neg_ne_zero.mpr hpim) hnormsq
      simpa [z0, Complex.mul_re] using hinvim
    let z : ℂ := if 0 < z0.re then z0 else -z0
    have hzre : 0 < z.re := by
      dsimp only [z]
      split_ifs with hpos
      · exact hpos
      · simp only [Complex.neg_re]
        exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hpos) hz0re)
    have hpinv : ‖p⁻¹‖ < 1 := by
      rw [norm_inv, inv_lt_one₀ (norm_pos_iff.mpr hp0)]
      exact hp
    have hgeom : HasSum (fun i : ℕ ↦ p⁻¹ ^ i) (1 - p⁻¹)⁻¹ :=
      hasSum_geometric_of_norm_lt_one hpinv
    have hz0sumC : HasSum (fun i : ℕ ↦ z0 * p⁻¹ ^ i) Complex.I := by
      have hmul := hgeom.mul_left z0
      have hone : 1 - p⁻¹ ≠ 0 := by
        intro h
        have : p = 1 := by
          apply inv_injective
          simpa using sub_eq_zero.mp h
        subst p
        norm_num at hp
      have hval : z0 * (1 - p⁻¹)⁻¹ = Complex.I := by
        dsimp only [z0]
        field_simp
        exact div_self (sub_ne_zero.mpr (by
          intro h
          subst p
          norm_num at hp))
      rw [← hval]
      exact hmul
    have hz0sumR : HasSum (fun i : ℕ ↦ (z0 * p⁻¹ ^ i).re) 0 := by
      simpa using Complex.hasSum_re hz0sumC
    have hzsumR : HasSum (fun i : ℕ ↦ (z * p⁻¹ ^ i).re) 0 := by
      dsimp only [z]
      split_ifs with hpos
      · exact hz0sumR
      · simpa using hz0sumR.neg
    obtain ⟨n, han, htail⟩ :=
      exists_positive_term_with_nonpositive_tails hzsumR (by simpa using hzre)
    let w : ℂ := z * p⁻¹ ^ n
    refine ⟨w, by simpa [w] using han, fun k ↦ ?_⟩
    have heq : (fun i : ℕ ↦ (w * p⁻¹ ^ (i + 1)).re) =
        fun i ↦ (z * p⁻¹ ^ (n + 1 + i)).re := by
      funext i
      dsimp only [w]
      congr 1
      rw [show n + 1 + i = n + (i + 1) by omega, pow_add]
      ring
    rw [heq]
    exact htail k

lemma signed_expansion_coefficient_eq_one_of_remove_mass_lt {q : ℝ} (hq : 1 < q)
    {P : Set ℕ} [DecidablePred (· ∈ P)] {s : ℕ → ℤ}
    (hs : ∀ i, |s i| ≤ 1) (hs0 : s 0 = -1) (hexp : SignedExpansion q s)
    (hsP : ∀ n ∈ P, 0 ≤ s (n + 1)) (hsPc : ∀ n ∉ P, s (n + 1) ≤ 0)
    {j : ℕ} (hjP : j ∈ P)
    (hmass : (∑' n : ℕ, if n ∈ P ∧ n ≠ j then q⁻¹ ^ (n + 1) else 0) < 1) :
    s (j + 1) = 1 := by
  by_contra hsj
  have hsj0 : s (j + 1) = 0 := by
    have hnonneg := hsP j hjP
    have hle : s (j + 1) ≤ 1 := le_trans (le_abs_self _) (hs (j + 1))
    omega
  let f : ℕ → ℝ := fun n ↦ (s (n + 1) : ℝ) * q⁻¹ ^ (n + 1)
  let g : ℕ → ℝ := fun n ↦ if n ∈ P ∧ n ≠ j then q⁻¹ ^ (n + 1) else 0
  have hqi0 : 0 ≤ q⁻¹ := inv_nonneg.mpr (by linarith)
  have hqi1 : q⁻¹ < 1 := inv_lt_one_of_one_lt₀ hq
  have hgeom : Summable (fun n : ℕ ↦ q⁻¹ ^ (n + 1)) := by
    simpa [pow_succ, mul_comm] using
      (summable_geometric_of_lt_one hqi0 hqi1).mul_left q⁻¹
  have hgle : ∀ n, g n ≤ q⁻¹ ^ (n + 1) := by
    intro n
    by_cases hn : n ∈ P ∧ n ≠ j
    · simp [g, hn]
    · simp [g, hn]
      exact pow_nonneg (by linarith) _
  have hg0 : ∀ n, 0 ≤ g n := by
    intro n
    simp only [g]
    split_ifs <;> positivity
  have hgsum : Summable g := Summable.of_nonneg_of_le hg0 hgle hgeom
  have hfsum : Summable f := by
    have hfull := summable_signed_series (q := q) hq hs
    have hshift := (summable_nat_add_iff 1).mpr hfull
    simpa [f, Nat.add_assoc] using hshift
  have hfg : ∀ n, f n ≤ g n := by
    intro n
    by_cases hnP : n ∈ P
    · by_cases hnj : n = j
      · subst n
        simp [f, g, hjP, hsj0]
      · rw [show g n = q⁻¹ ^ (n + 1) by simp [g, hnP, hnj]]
        dsimp only [f]
        have hcoeff : (s (n + 1) : ℝ) ≤ 1 := by
          exact_mod_cast (le_trans (le_abs_self _) (hs (n + 1)))
        exact mul_le_of_le_one_left (pow_nonneg hqi0 _) hcoeff
    · simp only [g, hnP, false_and, ↓reduceIte]
      exact mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hsPc n hnP)
        (pow_nonneg hqi0 _)
  have hftsum : ∑' n, f n = 1 := by
    have hfull := (summable_signed_series (q := q) hq hs).sum_add_tsum_nat_add 1
    have htotal := hexp.tsum_eq
    rw [htotal] at hfull
    have hEq : -1 + ∑' n, f n = 0 := by simpa [f, hs0] using hfull
    linarith
  have hle : (∑' n, f n) ≤ ∑' n, g n :=
    Summable.tsum_le_tsum hfg hfsum hgsum
  have hgmass : (∑' n, g n) < 1 := by simpa [g] using hmass
  linarith

lemma tsum_indicator_le_add_single {P Q : Set ℕ} {weight : ℕ → ℝ} {j : ℕ}
    [DecidablePred (· ∈ P)] [DecidablePred (· ∈ Q)]
    (hP : Summable (fun n : ℕ ↦ if n ∈ P then weight n else 0))
    (hQ : Summable (fun n : ℕ ↦ if n ∈ Q then weight n else 0))
    (hweight0 : ∀ n, 0 ≤ weight n)
    (hsub : ∀ n, n ∈ P → n ∈ Q ∨ n = j) :
    (∑' n : ℕ, if n ∈ P then weight n else 0) ≤
      (∑' n : ℕ, if n ∈ Q then weight n else 0) + weight j := by
  classical
  let f : ℕ → ℝ := fun n ↦ if n ∈ P then weight n else 0
  let g : ℕ → ℝ := fun n ↦
    (if n ∈ Q then weight n else 0) + if n = j then weight j else 0
  have hsingle : Summable (fun n : ℕ ↦ if n = j then weight j else 0) := by
    apply summable_of_ne_finset_zero (s := {j})
    intro n hn
    simp only [Finset.mem_singleton] at hn
    simp [hn]
  have hgsum : Summable g := hQ.add hsingle
  have hfg : ∀ n, f n ≤ g n := by
    intro n
    by_cases hnP : n ∈ P
    · rcases hsub n hnP with hnQ | hnj
      · rw [show f n = weight n by simp [f, hnP]]
        rw [show g n = weight n + (if n = j then weight j else 0) by simp [g, hnQ]]
        exact le_add_of_nonneg_right (by
          by_cases h : n = j
          · simp [h, hweight0]
          · simp [h])
      · subst n
        rw [show f j = weight j by simp [f, hnP]]
        rw [show g j = (if j ∈ Q then weight j else 0) + weight j by simp [g]]
        exact le_add_of_nonneg_left (by
          by_cases h : j ∈ Q
          · rw [if_pos h]
            exact hweight0 j
          · rw [if_neg h])
    · rw [show f n = 0 by simp [f, hnP]]
      apply add_nonneg
      · by_cases h : n ∈ Q
        · rw [if_pos h]
          exact hweight0 n
        · rw [if_neg h]
      · by_cases h : n = j
        · rw [if_pos h]
          exact hweight0 j
        · rw [if_neg h]
  have hle := Summable.tsum_le_tsum hfg hP hgsum
  have hgval : (∑' n, g n) =
      (∑' n : ℕ, if n ∈ Q then weight n else 0) + weight j := by
    rw [Summable.tsum_add hQ hsingle, tsum_ite_eq]
  change (∑' n : ℕ, if n ∈ P then weight n else 0) ≤ _ at hle
  exact hle.trans_eq hgval

lemma exists_lazy_expansion_for_separator {q : ℝ} (hq1 : 1 < q) (hq2 : q < 2)
    (a : ℕ → ℝ) :
    ∃ K : ℕ, ∃ s : ℕ → ℤ,
      (∀ i, |s i| ≤ 1) ∧ s 0 = -1 ∧ SignedExpansion q s ∧
      (∀ n, n < K ∨ a n ≤ 0 → 0 ≤ s (n + 1)) ∧
      (∀ n, ¬(n < K ∨ a n ≤ 0) → s (n + 1) ≤ 0) ∧
      (∀ j, j < K → a j < 0 → s (j + 1) = 1) := by
  classical
  let weight : ℕ → ℝ := fun n ↦ q⁻¹ ^ (n + 1)
  let P : ℕ → Set ℕ := fun K ↦ {n | n < K ∨ a n ≤ 0}
  let mass : ℕ → ℝ := fun K ↦ ∑' n : ℕ, if n ∈ P K then weight n else 0
  have hqi0 : 0 ≤ q⁻¹ := inv_nonneg.mpr (by linarith)
  have hqi1 : q⁻¹ < 1 := inv_lt_one_of_one_lt₀ hq1
  have hqi_le : q⁻¹ ≤ 1 := hqi1.le
  have hweight0 : ∀ n, 0 ≤ weight n := fun n ↦ by
    exact pow_nonneg hqi0 _
  have hweightSum : Summable weight := by
    simpa [weight, pow_succ, mul_comm] using
      (summable_geometric_of_lt_one hqi0 hqi1).mul_left q⁻¹
  have hmassSum (K : ℕ) : Summable (fun n : ℕ ↦ if n ∈ P K then weight n else 0) := by
    refine Summable.of_nonneg_of_le ?_ ?_ hweightSum
    · intro n
      split_ifs <;> positivity
    · intro n
      by_cases hn : n ∈ P K
      · simp [hn]
      · simp [hn, hweight0]
  have htotal : 1 < ∑' n, weight n := by
    rw [show (∑' n, weight n) = 1 / (q - 1) by simpa [weight] using tsum_inv_pow_succ hq1]
    rw [one_lt_div (sub_pos.mpr hq1)]
    linarith
  have hpartialTend : Tendsto (fun K ↦ ∑ n ∈ Finset.range K, weight n)
      atTop (𝓝 (∑' n, weight n)) := hweightSum.hasSum.tendsto_sum_nat
  have hevent : ∀ᶠ K in atTop, 1 < ∑ n ∈ Finset.range K, weight n :=
    hpartialTend.eventually (Ioi_mem_nhds htotal)
  rcases (eventually_atTop.1 hevent) with ⟨L, hL⟩
  have hmassL : 1 ≤ mass L := by
    have hle : (∑ n ∈ Finset.range L, weight n) ≤ mass L := by
      have heq : (∑ n ∈ Finset.range L, weight n) =
          ∑ n ∈ Finset.range L, (if n ∈ P L then weight n else 0) := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [if_pos]
        exact Or.inl (Finset.mem_range.mp hn)
      rw [heq]
      dsimp only [mass]
      apply (hmassSum L).sum_le_tsum (Finset.range L)
      · intro n hn
        positivity
    exact (hL L le_rfl).le.trans hle
  have hexK : ∃ K, 1 ≤ mass K := ⟨L, hmassL⟩
  let K := Nat.find hexK
  have hKmass : 1 ≤ mass K := Nat.find_spec hexK
  let PK : Set ℕ := P K
  have hPKmass : 1 ≤ ∑' n : ℕ, if n ∈ PK then q⁻¹ ^ (n + 1) else 0 := by
    calc
      1 ≤ mass K := hKmass
      _ = ∑' n : ℕ, if n ∈ PK then q⁻¹ ^ (n + 1) else 0 := by
        apply tsum_congr
        intro n
        by_cases hn : n ∈ P K
        · simp [mass, PK, weight, hn]
        · simp [mass, PK, weight, hn]
  obtain ⟨s, hs, hs0, hsExp, hsP, hsPc⟩ :=
    exists_lazy_signed_expansion hq1 hq2.le PK hPKmass
  have hmassStep : K ≠ 0 → mass K ≤ mass (K - 1) + weight (K - 1) := by
    intro hK0
    dsimp only [mass]
    exact tsum_indicator_le_add_single (P := P K) (Q := P (K - 1))
      (weight := weight) (j := K - 1) (hmassSum K) (hmassSum (K - 1)) hweight0
      (by
        intro n hn
        simp only [P, Set.mem_ofPred_eq] at hn ⊢
        rcases hn with hnlt | hna
        · by_cases hlt : n < K - 1
          · exact Or.inl (Or.inl hlt)
          · exact Or.inr (by omega)
        · exact Or.inl (Or.inr hna))
  have hcoeffOne {j : ℕ} (hjK : j < K) (hja : a j < 0) : s (j + 1) = 1 := by
    have hK0 : K ≠ 0 := by omega
    have hprev : mass (K - 1) < 1 := by
      have hnot : ¬ 1 ≤ mass (K - 1) := by
        intro h
        have hlt : K - 1 < K := by omega
        have : K - 1 < Nat.find hexK := by simpa [K] using hlt
        exact Nat.find_min hexK this h
      exact lt_of_not_ge hnot
    let remove : ℕ → ℝ := fun n ↦
      if n ∈ PK ∧ n ≠ j then weight n else 0
    have hjPK : j ∈ PK := by simp [PK, P, hjK]
    have hremoveSum : Summable remove := by
      refine Summable.of_nonneg_of_le ?_ ?_ hweightSum
      · intro n; simp only [remove]; split_ifs <;> positivity
      · intro n
        by_cases hn : n ∈ PK ∧ n ≠ j
        · simp [remove, hn]
        · simp [remove, hn, hweight0]
    have hmassRemove : (∑' n, remove n) = mass K - weight j := by
      have hsplit := (hmassSum K).tsum_eq_add_tsum_ite j
      have hrest : (∑' n, if n = j then 0 else if n ∈ P K then weight n else 0) =
          ∑' n, remove n := by
        apply tsum_congr
        intro n
        by_cases hnj : n = j
        · subst n; simp [remove]
        · simp [remove, PK, hnj]
      have hmassSplit : mass K = weight j + ∑' n, remove n := by
        calc
          mass K = (if j ∈ P K then weight j else 0) +
              ∑' n, if n = j then 0 else if n ∈ P K then weight n else 0 := by
                simpa only [mass] using hsplit
          _ = weight j + ∑' n, remove n := by rw [if_pos (by simpa [PK] using hjPK), hrest]
      linarith
    have hweightOrder : weight (K - 1) ≤ weight j := by
      dsimp only [weight]
      exact pow_le_pow_of_le_one hqi0 hqi_le (by omega)
    have hremoveLt : (∑' n, remove n) < 1 := by
      rw [hmassRemove]
      have hstep := hmassStep hK0
      linarith
    apply signed_expansion_coefficient_eq_one_of_remove_mass_lt hq1 hs hs0 hsExp hsP hsPc
      hjPK
    simpa [remove, PK, weight, inv_pow] using hremoveLt
  refine ⟨K, s, hs, hs0, hsExp, ?_, ?_, ?_⟩
  · intro n hn
    exact hsP n (by simpa [PK, P] using hn)
  · intro n hn
    exact hsPc n (by simpa [PK, P] using hn)
  · intro j hjK hja
    exact hcoeffOne hjK hja

lemma exists_signed_expansion_separating_at_large_conjugate {q : ℝ} {p : ℂ}
    (hq1 : 1 < q) (hq2 : q < 2) (hp : 1 < ‖p‖)
    (hpNonpos : p.re < 1 ∨ p.im ≠ 0) :
    ∃ s : ℕ → ℤ, (∀ i, |s i| ≤ 1) ∧ SignedExpansion q s ∧
      ¬ HasSum (fun i ↦ (s i : ℂ) * p⁻¹ ^ i) 0 := by
  classical
  obtain ⟨w, hwpos, hwpartial⟩ := exists_complex_separator_of_norm_gt_one hp hpNonpos
  let a : ℕ → ℝ := fun n ↦ (w * p⁻¹ ^ (n + 1)).re
  obtain ⟨K, s, hs, hs0, hsExp, hsP, hsPc, hcoeffOne⟩ :=
    exists_lazy_expansion_for_separator hq1 hq2 a
  let t : ℕ → ℝ := fun n ↦ (s (n + 1) : ℝ) * a n
  let b : ℕ → ℝ := fun n ↦ if n < K then a n else 0
  have hp0 : p ≠ 0 := by
    intro h
    norm_num [h] at hp
  have hpinv : ‖p⁻¹‖ < 1 := by
    rw [norm_inv, inv_lt_one₀ (norm_pos_iff.mpr hp0)]
    exact hp
  have htsum : Summable t := by
    apply Summable.of_norm_bounded
      ((summable_geometric_of_lt_one (norm_nonneg p⁻¹) hpinv).mul_left ‖w‖)
    intro n
    dsimp only [t, a]
    rw [Real.norm_eq_abs, abs_mul]
    have hsreal : |(s (n + 1) : ℝ)| ≤ 1 := by exact_mod_cast hs (n + 1)
    calc
      |(s (n + 1) : ℝ)| * |(w * p⁻¹ ^ (n + 1)).re| ≤
          1 * ‖w * p⁻¹ ^ (n + 1)‖ := by
        have hre : |(w * p⁻¹ ^ (n + 1)).re| ≤ ‖w * p⁻¹ ^ (n + 1)‖ := by
          simpa [Real.norm_eq_abs] using RCLike.norm_re_le_norm (w * p⁻¹ ^ (n + 1))
        exact mul_le_mul hsreal hre (abs_nonneg _) zero_le_one
      _ = ‖w‖ * ‖p⁻¹‖ ^ (n + 1) := by simp
      _ ≤ ‖w‖ * ‖p⁻¹‖ ^ n := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg w)
        exact pow_le_pow_of_le_one (norm_nonneg p⁻¹) hpinv.le (by omega)
  have hbsum : Summable b := by
    apply summable_of_ne_finset_zero (s := Finset.range K)
    intro n hn
    have hnK : ¬n < K := by simpa using hn
    simp [b, hnK]
  have htb : ∀ n, t n ≤ b n := by
    intro n
    by_cases hnK : n < K
    · rw [show b n = a n by simp [b, hnK]]
      by_cases hapos : 0 ≤ a n
      · have hsle : (s (n + 1) : ℝ) ≤ 1 := by
          exact_mod_cast (le_trans (le_abs_self _) (hs (n + 1)))
        dsimp only [t]
        nlinarith
      · have haneg : a n < 0 := lt_of_not_ge hapos
        dsimp only [t]
        rw [hcoeffOne n hnK haneg]
        norm_num
    · rw [show b n = 0 by simp [b, hnK]]
      by_cases han : a n ≤ 0
      · exact mul_nonpos_of_nonneg_of_nonpos
          (by exact_mod_cast hsP n (Or.inr han)) han
      · exact mul_nonpos_of_nonpos_of_nonneg
          (by exact_mod_cast hsPc n (not_or_intro hnK han)) (le_of_not_ge han)
  have htbound : (∑' n, t n) ≤ ∑ n ∈ Finset.range K, a n := by
    have hle := Summable.tsum_le_tsum htb htsum hbsum
    have hbval : (∑' n, b n) = ∑ n ∈ Finset.range K, a n := by
      rw [tsum_eq_sum (s := Finset.range K)]
      · apply Finset.sum_congr rfl
        intro n hn
        simp [b, Finset.mem_range.mp hn]
      · intro n hn
        have hnK : ¬n < K := by simpa using hn
        simp [b, hnK]
    simpa [hbval] using hle
  have hprefix : ∑ n ∈ Finset.range K, a n ≤ 0 := by
    simpa [a] using hwpartial K
  have hcomplexSum : Summable (fun i ↦ (s i : ℂ) * p⁻¹ ^ i) := by
    apply Summable.of_norm_bounded
      (summable_geometric_of_lt_one (norm_nonneg p⁻¹) hpinv)
    intro i
    rw [norm_mul, norm_pow]
    have hsc : ‖(s i : ℂ)‖ ≤ 1 := by
      have hscR : |(s i : ℝ)| ≤ 1 := by exact_mod_cast hs i
      simpa using hscR
    simpa using mul_le_mul_of_nonneg_right hsc (pow_nonneg (norm_nonneg p⁻¹) i)
  let Z : ℂ := ∑' i, (s i : ℂ) * p⁻¹ ^ i
  have hreal : (w * Z).re = -w.re + ∑' n, t n := by
    have hmul : (∑' i, w * ((s i : ℂ) * p⁻¹ ^ i)) = w * Z := by
      simpa [Z] using (tsum_mul_left :
        (∑' i, w * ((s i : ℂ) * p⁻¹ ^ i)) = w * ∑' i, (s i : ℂ) * p⁻¹ ^ i)
    have husum : Summable (fun i ↦ w * ((s i : ℂ) * p⁻¹ ^ i)) :=
      hcomplexSum.mul_left w
    have hre : (w * Z).re = ∑' i, (w * ((s i : ℂ) * p⁻¹ ^ i)).re := by
      rw [← hmul]
      exact (Complex.hasSum_re husum.hasSum).tsum_eq.symm
    have hsplit := ((Complex.hasSum_re husum.hasSum).summable).sum_add_tsum_nat_add 1
    have htailEq : (fun n ↦ (w * ((s (n + 1) : ℂ) * p⁻¹ ^ (n + 1))).re) = t := by
      funext n
      dsimp only [t, a]
      rw [show w * ((s (n + 1) : ℂ) * p⁻¹ ^ (n + 1)) =
          (s (n + 1) : ℝ) • (w * p⁻¹ ^ (n + 1)) by
        norm_cast; ring]
      simp
    rw [htailEq] at hsplit
    have hzero : (w * ((s 0 : ℂ) * p⁻¹ ^ 0)).re = -w.re := by simp [hs0]
    calc
      (w * Z).re = ∑' i, (w * ((s i : ℂ) * p⁻¹ ^ i)).re := hre
      _ = (w * ((s 0 : ℂ) * p⁻¹ ^ 0)).re + ∑' n, t n := by
        simpa only [Finset.sum_range_one] using hsplit.symm
      _ = -w.re + ∑' n, t n := by rw [hzero]
  have hneg : (w * Z).re < 0 := by
    rw [hreal]
    linarith
  refine ⟨s, hs, hsExp, ?_⟩
  intro hzero
  have : Z = 0 := hzero.tsum_eq
  rw [this, mul_zero, Complex.zero_re] at hneg
  exact lt_irrefl 0 hneg

lemma eval₂_reversedPolynomial_succ (q : ℝ) (s : ℕ → ℤ) (n : ℕ) :
    (reversedPolynomial s (n + 1)).eval₂ (algebraMap ℤ ℝ) q =
      q * (reversedPolynomial s n).eval₂ (algebraMap ℤ ℝ) q + s (n + 1) := by
  rw [eval₂_reversedPolynomial, eval₂_reversedPolynomial, Finset.sum_range_succ]
  simp only [Nat.sub_self, pow_zero, mul_one]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ n := by simpa using hi
  rw [show n + 1 - i = (n - i) + 1 by omega, pow_succ]
  ring

def expansionRemainder (q : ℝ) (d : ℕ → ℕ) (n : ℕ) : ℝ :=
  1 - ∑ i ∈ Finset.range n, (d i : ℝ) * (q⁻¹) ^ (i + 1)

lemma expansionRemainder_succ (q : ℝ) (d : ℕ → ℕ) (n : ℕ) :
    expansionRemainder q d (n + 1) =
      expansionRemainder q d n - (d n : ℝ) * (q⁻¹) ^ (n + 1) := by
  simp [expansionRemainder, Finset.sum_range_succ]
  ring

lemma expansion_tail_identity {q : ℝ} (hq0 : q ≠ 0) (d : ℕ → ℕ) (n : ℕ) :
    (reversedPolynomial (expansionSignedDigits d) n).eval₂ (algebraMap ℤ ℝ) q =
      -q ^ n * expansionRemainder q d n := by
  induction n with
  | zero => rw [eval₂_reversedPolynomial]; norm_num [expansionSignedDigits, expansionRemainder]
  | succ n ih =>
      rw [eval₂_reversedPolynomial_succ, ih, expansionRemainder_succ]
      simp only [expansionSignedDigits, Int.cast_natCast]
      have hcancel : q ^ (n + 1) * (q⁻¹) ^ (n + 1) = 1 := by
        rw [← mul_pow]
        simp [hq0]
      have hterm :
          q ^ (n + 1) * ((d n : ℝ) * (q⁻¹) ^ (n + 1)) = (d n : ℝ) := by
        calc
          _ = (d n : ℝ) * (q ^ (n + 1) * (q⁻¹) ^ (n + 1)) := by ring
          _ = (d n : ℝ) := by rw [hcancel, mul_one]
      have htermneg :
          -q ^ (n + 1) * ((d n : ℝ) * (q⁻¹) ^ (n + 1)) = -(d n : ℝ) := by
        rw [neg_mul, hterm]
      rw [mul_sub]
      rw [htermneg, pow_succ]
      ring

lemma reversed_tail_bound_of_signedExpansion {q : ℝ} (hq : 1 < q)
    {s : ℕ → ℤ} (hs : ∀ i, |s i| ≤ 1) (hexp : SignedExpansion q s)
    (n : ℕ) :
    |(reversedPolynomial s n).eval₂ (algebraMap ℤ ℝ) q| ≤ 1 / (q - 1) := by
  let f : ℕ → ℝ := fun i ↦ (s i : ℝ) * q⁻¹ ^ i
  have hq0 : q ≠ 0 := by linarith
  have hqi0 : 0 ≤ q⁻¹ := inv_nonneg.mpr (by linarith)
  have hqi1 : q⁻¹ < 1 := inv_lt_one_of_one_lt₀ hq
  have hfsum : Summable f := summable_signed_series (q := q) hq hs
  have htotal : ∑' i, f i = 0 := hexp.tsum_eq
  have hsplit := hfsum.sum_add_tsum_nat_add (n + 1)
  have hpartial : (∑ i ∈ Finset.range (n + 1), f i) =
      -(∑' i, f (i + (n + 1))) := by
    rw [htotal] at hsplit
    linarith
  have heval :
      (reversedPolynomial s n).eval₂ (algebraMap ℤ ℝ) q =
        q ^ n * ∑ i ∈ Finset.range (n + 1), f i := by
    rw [eval₂_reversedPolynomial, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hin : i ≤ n := by simpa using hi
    dsimp only [f]
    rw [pow_sub₀ q hq0 hin]
    simp only [inv_pow]
    ring
  have hgeom : Summable (fun i : ℕ ↦ q⁻¹ ^ (i + (n + 1))) := by
    simpa only [pow_add, mul_comm] using
      (summable_geometric_of_lt_one hqi0 hqi1).mul_left (q⁻¹ ^ (n + 1))
  have hterm_le (i : ℕ) : |f (i + (n + 1))| ≤ q⁻¹ ^ (i + (n + 1)) := by
    dsimp only [f]
    rw [abs_mul, abs_pow, abs_of_nonneg hqi0]
    have hscast : |(s (i + (n + 1)) : ℝ)| ≤ 1 := by
      exact_mod_cast hs (i + (n + 1))
    exact mul_le_of_le_one_left (pow_nonneg hqi0 _) hscast
  have htail_le : |∑' i, f (i + (n + 1))| ≤
      ∑' i : ℕ, q⁻¹ ^ (i + (n + 1)) := by
    simpa only [Real.norm_eq_abs] using
      (tsum_of_norm_bounded (f := fun i ↦ f (i + (n + 1))) hgeom.hasSum
        (fun i ↦ by simpa only [Real.norm_eq_abs] using hterm_le i))
  have hgeom_value : (∑' i : ℕ, q⁻¹ ^ (i + (n + 1))) =
      q⁻¹ ^ (n + 1) / (1 - q⁻¹) := by
    rw [show (fun i : ℕ ↦ q⁻¹ ^ (i + (n + 1))) =
        fun i ↦ q⁻¹ ^ (n + 1) * q⁻¹ ^ i by
      funext i; rw [pow_add, mul_comm]]
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one]
    · rw [div_eq_mul_inv]
    · simpa [Real.norm_eq_abs, abs_of_pos (by linarith : 0 < q)] using hqi1
  rw [heval, hpartial, abs_mul, abs_neg, abs_pow, abs_of_pos (by linarith)]
  calc
    q ^ n * |∑' i, f (i + (n + 1))| ≤
        q ^ n * (q⁻¹ ^ (n + 1) / (1 - q⁻¹)) := by
      rw [← hgeom_value]
      exact mul_le_mul_of_nonneg_left htail_le (pow_nonneg (by linarith) _)
    _ = 1 / (q - 1) := by
      have hprod : q ^ n * q⁻¹ ^ (n + 1) = q⁻¹ := by
        rw [pow_succ]
        calc
          q ^ n * (q⁻¹ ^ n * q⁻¹) = (q * q⁻¹) ^ n * q⁻¹ := by
            rw [mul_pow]
            ring
          _ = q⁻¹ := by simp [hq0]
      calc
        q ^ n * (q⁻¹ ^ (n + 1) / (1 - q⁻¹)) =
            (q ^ n * q⁻¹ ^ (n + 1)) / (1 - q⁻¹) := by ring
        _ = q⁻¹ / (1 - q⁻¹) := by rw [hprod]
        _ = 1 / (q - 1) := by field_simp

lemma summable_binary_digit_series {p : ℝ} (hp : 1 < p)
    {d : ℕ → ℕ} (hd : ∀ i, d i = 0 ∨ d i = 1) :
    Summable (fun i ↦ (d i : ℝ) * p⁻¹ ^ (i + 1)) := by
  have hp0 : 0 ≤ p⁻¹ := inv_nonneg.mpr (by linarith)
  have hp1 : p⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp
  apply Summable.of_nonneg_of_le
    (fun i ↦ mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp0 _))
    (fun i ↦ ?_)
    ((summable_geometric_of_lt_one hp0 hp1).mul_left p⁻¹)
  rcases hd i with hi | hi
  · simp [hi]
    positivity
  · simp [hi, pow_succ, mul_comm]

lemma tsum_expansionSignedDigits {p : ℝ} (hp : 1 < p)
    {d : ℕ → ℕ} (hd : ∀ i, d i = 0 ∨ d i = 1) :
    ∑' i, (expansionSignedDigits d i : ℝ) * p⁻¹ ^ i =
      -1 + ∑' i, (d i : ℝ) * p⁻¹ ^ (i + 1) := by
  let s := expansionSignedDigits d
  have hs : ∀ i, |s i| ≤ 1 := expansionSignedDigits_height_one hd
  have hsum : Summable (fun i ↦ (s i : ℝ) * p⁻¹ ^ i) :=
    summable_signed_series (q := p) hp hs
  have hsplit := hsum.sum_add_tsum_nat_add 1
  convert hsplit.symm using 1 <;>
    simp only [Finset.sum_range_one, s, expansionSignedDigits, Int.cast_negSucc,
      Int.cast_zero, pow_zero, mul_one, zero_add, Nat.zero_add, Int.cast_natCast] <;>
    norm_num

lemma exists_one_digit_of_tendsto_one {q : ℝ} {d : ℕ → ℕ}
    (hd : ∀ i, d i = 0 ∨ d i = 1)
    (hdsum : Tendsto (fun n ↦ ∑ i ∈ Finset.range n,
      (d i : ℝ) * q⁻¹ ^ (i + 1)) atTop (𝓝 1)) :
    ∃ i, d i = 1 := by
  by_contra hnone
  have hall : ∀ i, d i = 0 := by
    intro i
    rcases hd i with hi | hi
    · exact hi
    · exact (hnone ⟨i, hi⟩).elim
  have hzero : (fun n ↦ ∑ i ∈ Finset.range n,
      (d i : ℝ) * q⁻¹ ^ (i + 1)) = fun _ ↦ 0 := by
    funext n
    simp [hall]
  rw [hzero] at hdsum
  have : (0 : ℝ) = 1 := tendsto_nhds_unique tendsto_const_nhds hdsum
  norm_num at this

lemma binary_digit_tsum_ne_one_of_ne {q p : ℝ} (hq : 1 < q) (hp : 1 < p)
    (hpq : p ≠ q) {d : ℕ → ℕ} (hd : ∀ i, d i = 0 ∨ d i = 1)
    (hdsum : Tendsto (fun n ↦ ∑ i ∈ Finset.range n,
      (d i : ℝ) * q⁻¹ ^ (i + 1)) atTop (𝓝 1)) :
    (∑' i, (d i : ℝ) * p⁻¹ ^ (i + 1)) ≠ 1 := by
  have hqsum : Summable (fun i ↦ (d i : ℝ) * q⁻¹ ^ (i + 1)) :=
    summable_binary_digit_series hq hd
  have hpsum : Summable (fun i ↦ (d i : ℝ) * p⁻¹ ^ (i + 1)) :=
    summable_binary_digit_series hp hd
  have hqtsum : (∑' i, (d i : ℝ) * q⁻¹ ^ (i + 1)) = 1 := by
    exact (hqsum.hasSum_iff_tendsto_nat.mpr hdsum).tsum_eq
  obtain ⟨j, hj⟩ := exists_one_digit_of_tendsto_one hd hdsum
  rcases lt_or_gt_of_ne hpq with hp_lt_q | hq_lt_p
  · have hlt : (∑' i, (d i : ℝ) * q⁻¹ ^ (i + 1)) <
        ∑' i, (d i : ℝ) * p⁻¹ ^ (i + 1) := by
      apply Summable.tsum_lt_tsum_of_nonneg
        (fun i ↦ mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (inv_nonneg.mpr (by linarith)) _))
      · intro i
        gcongr
      · rw [hj]
        norm_num
        simpa only [inv_pow, Nat.succ_eq_add_one] using
          (pow_lt_pow_left₀
            ((inv_lt_inv₀ (by linarith) (by linarith)).2 hp_lt_q)
            (inv_nonneg.mpr (by linarith)) (Nat.succ_ne_zero j))
      · exact hpsum
    rw [hqtsum] at hlt
    exact ne_of_gt hlt
  · have hlt : (∑' i, (d i : ℝ) * p⁻¹ ^ (i + 1)) <
        ∑' i, (d i : ℝ) * q⁻¹ ^ (i + 1) := by
      apply Summable.tsum_lt_tsum_of_nonneg
        (fun i ↦ mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (inv_nonneg.mpr (by linarith)) _))
      · intro i
        gcongr
      · rw [hj]
        norm_num
        simpa only [inv_pow, Nat.succ_eq_add_one] using
          (pow_lt_pow_left₀
            ((inv_lt_inv₀ (by linarith) (by linarith)).2 hq_lt_p)
            (inv_nonneg.mpr (by linarith)) (Nat.succ_ne_zero j))
      · exact hqsum
    rw [hqtsum] at hlt
    exact ne_of_lt hlt

lemma integral_of_no_signedSpectrum_accumulation {q : ℝ}
    (hq1 : 1 < q) (hq2 : q < 2) (hno : ¬ HasAccumulation (SignedSpectrum q)) :
    IsIntegral ℤ q := by
  have hq0 : q ≠ 0 := ne_of_gt (lt_trans zero_lt_one hq1)
  have hden : 0 < q - 1 := sub_pos.mpr hq1
  have hone : (1 : ℝ) ≤ 1 / (q - 1) := by
    rw [le_div_iff₀ hden]
    linarith
  obtain ⟨d, hd, hrem⟩ :=
    exists_binary_expansion_with_remainder_bounds hq1 hq2.le zero_le_one hone
  let s : ℕ → ℤ := expansionSignedDigits d
  let f : ℕ → ℝ := fun n ↦
    (reversedPolynomial s n).eval₂ (algebraMap ℤ ℝ) q
  have hs : ∀ i, |s i| ≤ 1 := expansionSignedDigits_height_one hd
  have hfmem : ∀ n, f n ∈ SignedSpectrum q := fun n ↦
    reversedPolynomial_eval_mem_signedSpectrum hs n
  have hfabs : ∀ n, |f n| ≤ 1 / (q - 1) := by
    intro n
    have hident : f n = -q ^ n * expansionRemainder q d n := by
      simpa [f, s] using expansion_tail_identity hq0 d n
    have hrem' :
        0 ≤ expansionRemainder q d n ∧
          expansionRemainder q d n ≤ (q⁻¹) ^ n / (q - 1) := by
      simpa [expansionRemainder] using hrem n
    rw [hident]
    have habs : |-q ^ n * expansionRemainder q d n| =
        q ^ n * expansionRemainder q d n := by
      rw [abs_mul, abs_neg, abs_pow, abs_of_pos (lt_trans zero_lt_one hq1),
        abs_of_nonneg hrem'.1]
    rw [habs]
    calc
      q ^ n * expansionRemainder q d n ≤
          q ^ n * ((q⁻¹) ^ n / (q - 1)) :=
        mul_le_mul_of_nonneg_left hrem'.2 (pow_nonneg (le_trans zero_le_one hq1.le) n)
      _ = 1 / (q - 1) := by
        rw [div_eq_mul_inv, ← mul_assoc, ← mul_pow]
        simp [hq0]
  have hfinite : (Set.range f).Finite :=
    finite_of_bounded_subset_no_accumulation hno
      (by rintro _ ⟨n, rfl⟩; exact hfmem n) (1 / (q - 1))
      (by
        rintro _ ⟨n, rfl⟩
        exact (abs_le.mp (hfabs n)))
  let g : ℕ → Set.range f := fun n ↦ ⟨f n, Set.mem_range_self n⟩
  letI : Finite (Set.range f) := hfinite
  obtain ⟨m, n, hmn, heq⟩ := Finite.exists_ne_map_eq_of_infinite g
  have heq' : f m = f n := congr_arg Subtype.val heq
  have pair_integral : ∀ {a b : ℕ}, a < b → f a = f b → IsIntegral ℤ q := by
    intro a b hab heval
    let p : ℤ[X] := -(reversedPolynomial s b - reversedPolynomial s a)
    have hbdeg : (reversedPolynomial s b).natDegree ≤ b := by
      unfold reversedPolynomial
      exact Nat.lt_succ_iff.mp (Polynomial.ofFn_natDegree_lt (by omega) _)
    have hadeg : (reversedPolynomial s a).natDegree ≤ b := by
      apply le_trans _ hab.le
      unfold reversedPolynomial
      exact Nat.lt_succ_iff.mp (Polynomial.ofFn_natDegree_lt (by omega) _)
    have hpdeg : p.natDegree ≤ b := by
      have hsub := Polynomial.natDegree_sub_le_of_le hbdeg hadeg
      simpa [p] using Polynomial.natDegree_neg_le_of_le hsub
    have hpcoeff : p.coeff b = 1 := by
      simp [p, reversedPolynomial_coeff, hab.le, not_le.mpr hab,
        s, expansionSignedDigits]
    have hpmonic : p.Monic :=
      Polynomial.monic_of_natDegree_le_of_coeff_eq_one b hpdeg hpcoeff
    have hpeval : p.eval₂ (algebraMap ℤ ℝ) q = 0 := by
      simp [p, f] at heval ⊢
      linarith
    exact ⟨p, hpmonic, hpeval⟩
  rcases lt_or_gt_of_ne hmn with hlt | hgt
  · exact pair_integral hlt heq'
  · exact pair_integral hgt heq'.symm

lemma eval₂_eq_at_conjugate_of_eval₂_eq {q : ℝ} (hqint : IsIntegral ℤ q)
    {z : ℂ}
    (hz : ((minpoly ℤ q).map (algebraMap ℤ ℂ)).eval z = 0)
    {P Q : ℤ[X]}
    (hPQ : P.eval₂ (algebraMap ℤ ℝ) q = Q.eval₂ (algebraMap ℤ ℝ) q) :
    P.eval₂ (algebraMap ℤ ℂ) z = Q.eval₂ (algebraMap ℤ ℂ) z := by
  have hrootq : Polynomial.aeval q (P - Q) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_sub, hPQ, sub_self]
  obtain ⟨C, hC⟩ := minpoly.isIntegrallyClosed_dvd hqint hrootq
  have hrootz : (P - Q).eval₂ (algebraMap ℤ ℂ) z = 0 := by
    rw [hC, Polynomial.eval₂_mul]
    have hz' : (minpoly ℤ q).eval₂ (algebraMap ℤ ℂ) z = 0 := by
      simpa [Polynomial.eval₂_eq_eval_map] using hz
    rw [hz', zero_mul]
  simpa [Polynomial.eval₂_sub, sub_eq_zero] using hrootz

lemma finite_reversed_tail_range_at_conjugate {q : ℝ}
    (hqint : IsIntegral ℤ q) (hno : ¬ HasAccumulation (SignedSpectrum q))
    {z : ℂ} (hz : ((minpoly ℤ q).map (algebraMap ℤ ℂ)).eval z = 0)
    {s : ℕ → ℤ} (hs : ∀ i, |s i| ≤ 1) {M : ℝ}
    (hbound : ∀ n,
      |(reversedPolynomial s n).eval₂ (algebraMap ℤ ℝ) q| ≤ M) :
    (Set.range fun n ↦
      (reversedPolynomial s n).eval₂ (algebraMap ℤ ℂ) z).Finite := by
  let fq : ℕ → ℝ := fun n ↦
    (reversedPolynomial s n).eval₂ (algebraMap ℤ ℝ) q
  let fz : ℕ → ℂ := fun n ↦
    (reversedPolynomial s n).eval₂ (algebraMap ℤ ℂ) z
  have hqfinite : (Set.range fq).Finite :=
    finite_of_bounded_subset_no_accumulation hno
      (by
        rintro _ ⟨n, rfl⟩
        exact reversedPolynomial_eval_mem_signedSpectrum hs n)
      M
      (by
        rintro _ ⟨n, rfl⟩
        exact abs_le.mp (hbound n))
  let chooseIndex : Set.range fq → ℕ := fun y ↦ Classical.choose y.property
  have hchoose : ∀ y : Set.range fq, fq (chooseIndex y) = y := by
    intro y
    exact Classical.choose_spec y.property
  letI : Finite (Set.range fq) := hqfinite
  let F : Set.range fq → ℂ := fun y ↦ fz (chooseIndex y)
  have hFrange : (Set.range F).Finite := Set.finite_range F
  apply hFrange.subset
  rintro _ ⟨n, rfl⟩
  let y : Set.range fq := ⟨fq n, Set.mem_range_self n⟩
  refine ⟨y, ?_⟩
  have hqeq : fq (chooseIndex y) = fq n := by
    simpa [y] using hchoose y
  have hzeq : fz (chooseIndex y) = fz n := by
    apply eval₂_eq_at_conjugate_of_eval₂_eq hqint hz
    exact hqeq
  simpa [F, fz] using hzeq

lemma inv_pow_mul_eval₂_reversedPolynomial {z : ℂ} (hz0 : z ≠ 0)
    (s : ℕ → ℤ) (n : ℕ) :
    z⁻¹ ^ n * (reversedPolynomial s n).eval₂ (algebraMap ℤ ℂ) z =
      ∑ i ∈ Finset.range (n + 1), (s i : ℂ) * z⁻¹ ^ i := by
  have heval (r : ℕ) :
      (reversedPolynomial s r).eval₂ (algebraMap ℤ ℂ) z =
        ∑ i ∈ Finset.range (r + 1), (s i : ℂ) * z ^ (r - i) := by
    rw [reversedPolynomial, Polynomial.eval₂_eq_sum_range' (algebraMap ℤ ℂ)
      (Polynomial.ofFn_natDegree_lt (by omega) (fun j : Fin (r + 1) ↦ s (r - j.1))) z]
    rw [← Finset.sum_range_reflect]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i ≤ r := by simpa using hi
    rw [Polynomial.ofFn_coeff_eq_val_of_lt _ (by omega)]
    simp only [Nat.succ_sub_succ_eq_sub]
    simp [Nat.sub_sub_self hi']
  have hsucc (r : ℕ) :
      (reversedPolynomial s (r + 1)).eval₂ (algebraMap ℤ ℂ) z =
        z * (reversedPolynomial s r).eval₂ (algebraMap ℤ ℂ) z + s (r + 1) := by
    rw [heval, heval, Finset.sum_range_succ]
    simp only [Nat.sub_self, pow_zero, mul_one]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i ≤ r := by simpa using hi
    rw [show r + 1 - i = (r - i) + 1 by omega, pow_succ]
    ring
  induction n with
  | zero =>
      rw [heval]
      simp
  | succ n ih =>
      rw [hsucc, Finset.sum_range_succ]
      rw [pow_succ z⁻¹, mul_add]
      have hcancel : z⁻¹ * z = 1 := inv_mul_cancel₀ hz0
      calc
        z⁻¹ ^ n * z⁻¹ * (z *
              (reversedPolynomial s n).eval₂ (algebraMap ℤ ℂ) z) +
            z⁻¹ ^ n * z⁻¹ * (s (n + 1) : ℂ) =
            z⁻¹ ^ n * (reversedPolynomial s n).eval₂ (algebraMap ℤ ℂ) z +
              z⁻¹ ^ n * (z⁻¹ * (s (n + 1) : ℂ)) := by
          have hfirst :
              z⁻¹ ^ n * z⁻¹ *
                  (z * (reversedPolynomial s n).eval₂ (algebraMap ℤ ℂ) z) =
                z⁻¹ ^ n * (reversedPolynomial s n).eval₂ (algebraMap ℤ ℂ) z := by
            calc
              _ = z⁻¹ ^ n * ((z⁻¹ * z) *
                    (reversedPolynomial s n).eval₂ (algebraMap ℤ ℂ) z) := by ring
              _ = _ := by rw [hcancel, one_mul]
          rw [hfirst]
          ring
        _ = ∑ i ∈ Finset.range (n + 1), (s i : ℂ) * z⁻¹ ^ i +
              (s (n + 1) : ℂ) * (z⁻¹ ^ n * z⁻¹) := by
          rw [ih]
          ring

lemma hasSum_zero_of_finite_reversed_tail_range {z : ℂ} (hz : 1 < ‖z‖)
    {s : ℕ → ℤ} (hs : ∀ i, |s i| ≤ 1)
    (hfinite : (Set.range fun n ↦
      (reversedPolynomial s n).eval₂ (algebraMap ℤ ℂ) z).Finite) :
    HasSum (fun i ↦ (s i : ℂ) * z⁻¹ ^ i) 0 := by
  have hz0 : z ≠ 0 := by
    intro h
    norm_num [h] at hz
  have hinv : ‖z⁻¹‖ < 1 := by
    rw [norm_inv, inv_lt_one₀ (norm_pos_iff.mpr hz0)]
    exact hz
  have hsummable : Summable (fun i ↦ (s i : ℂ) * z⁻¹ ^ i) := by
    apply Summable.of_norm_bounded
      (summable_geometric_of_lt_one (norm_nonneg z⁻¹) hinv)
    intro i
    rw [norm_mul, norm_pow]
    have hscast : ‖(s i : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast hs i
    exact mul_le_of_le_one_left (pow_nonneg (norm_nonneg _) _) hscast
  let f : ℕ → ℂ := fun n ↦
    (reversedPolynomial s n).eval₂ (algebraMap ℤ ℂ) z
  obtain ⟨C, hC⟩ := Metric.isBounded_range_iff.mp hfinite.isCompact.isBounded
  have hC0 : 0 ≤ C := le_trans (dist_nonneg : 0 ≤ dist (f 0) (f 0)) (hC 0 0)
  have hfnorm : ∀ n, ‖f n‖ ≤ C + ‖f 0‖ := by
    intro n
    calc
      ‖f n‖ = ‖(f n - f 0) + f 0‖ := by ring_nf
      _ ≤ ‖f n - f 0‖ + ‖f 0‖ := norm_add_le _ _
      _ = dist (f n) (f 0) + ‖f 0‖ := by rw [dist_eq_norm]
      _ ≤ C + ‖f 0‖ := by
        have hCn : dist (f n) (f 0) ≤ C := by
          change dist
            ((reversedPolynomial s n).eval₂ (algebraMap ℤ ℂ) z)
            ((reversedPolynomial s 0).eval₂ (algebraMap ℤ ℂ) z) ≤ C
          exact hC n 0
        simpa [add_comm] using add_le_add_right hCn ‖f 0‖
  have hpow : Tendsto (fun n : ℕ ↦ ‖z⁻¹‖ ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hinv
  have hcap : Tendsto (fun n : ℕ ↦ ‖z⁻¹‖ ^ n * (C + ‖f 0‖)) atTop (𝓝 0) := by
    simpa using hpow.mul_const (C + ‖f 0‖)
  have hprod : Tendsto (fun n ↦ z⁻¹ ^ n * f n) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (g := fun n ↦ ‖z⁻¹‖ ^ n * (C + ‖f 0‖)) ?_ ?_ hcap
    · intro n; positivity
    · intro n
      rw [norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_left (hfnorm n) (pow_nonneg (norm_nonneg _) _)
  apply (hsummable.hasSum_iff_tendsto_nat).mpr
  apply (tendsto_add_atTop_iff_nat 1).mp
  convert hprod using 1
  funext n
  simpa [f, Nat.add_comm] using (inv_pow_mul_eval₂_reversedPolynomial hz0 s n).symm

lemma conjugate_not_positive_real_of_no_accumulation {q p : ℝ}
    (hq1 : 1 < q) (hq2 : q < 2)
    (hno : ¬ HasAccumulation (SignedSpectrum q))
    (hp1 : 1 < p) (hpq : p ≠ q)
    (hpRoot : ((minpoly ℤ q).map (algebraMap ℤ ℂ)).eval (p : ℂ) = 0) : False := by
  have hqint : IsIntegral ℤ q := integral_of_no_signedSpectrum_accumulation hq1 hq2 hno
  have hone : (1 : ℝ) ≤ 1 / (q - 1) := by
    rw [le_div_iff₀ (sub_pos.mpr hq1)]
    linarith
  obtain ⟨d, hd, hdsum⟩ := exists_binary_expansion hq1 hq2.le zero_le_one hone
  let s : ℕ → ℤ := expansionSignedDigits d
  have hs : ∀ i, |s i| ≤ 1 := expansionSignedDigits_height_one hd
  have hsExp : SignedExpansion q s := hasSum_expansionSignedDigits hq1 hd hdsum
  have hfinite : (Set.range fun n ↦
      (reversedPolynomial s n).eval₂ (algebraMap ℤ ℂ) (p : ℂ)).Finite :=
    finite_reversed_tail_range_at_conjugate hqint hno hpRoot hs
      (fun n ↦ reversed_tail_bound_of_signedExpansion hq1 hs hsExp n)
  have hpNorm : 1 < ‖(p : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    exact hp1
  have hsumC : HasSum (fun i ↦ (s i : ℂ) * (p : ℂ)⁻¹ ^ i) 0 :=
    hasSum_zero_of_finite_reversed_tail_range hpNorm hs hfinite
  have hsumR : HasSum (fun i ↦ (s i : ℝ) * p⁻¹ ^ i) 0 := by
    apply Complex.hasSum_ofReal.mp
    convert hsumC using 1
    · funext i
      norm_cast
    · rfl
  have hne : (∑' i, (s i : ℝ) * p⁻¹ ^ i) ≠ 0 := by
    rw [show (∑' i, (s i : ℝ) * p⁻¹ ^ i) =
        -1 + ∑' i, (d i : ℝ) * p⁻¹ ^ (i + 1) by
      simpa [s] using tsum_expansionSignedDigits hp1 hd]
    intro hz
    have honep : (∑' i, (d i : ℝ) * p⁻¹ ^ (i + 1)) = 1 := by linarith
    exact binary_digit_tsum_ne_one_of_ne hq1 hp1 hpq hd hdsum honep
  exact hne hsumR.tsum_eq

end Erdos1096
