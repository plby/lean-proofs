import ErdosProblems.Erdos1096.Erdos1096SignedSpectrum

open Filter Set Polynomial
open scoped BigOperators Pointwise Topology ComplexConjugate

noncomputable section

namespace Erdos1096

lemma unit_separator_prefix {p : ℂ} (hpNorm : ‖p‖ = 1) (hpNe : p ≠ 1) :
    let w : ℂ := 1 - p
    0 < w.re ∧ ∀ k : ℕ,
      ∑ i ∈ Finset.range k, (w * p⁻¹ ^ (i + 1)).re < w.re := by
  let w : ℂ := 1 - p
  have hp0 : p ≠ 0 := by
    intro hp
    simp [hp] at hpNorm
  have hpre : p.re < 1 := by
    have hle : p.re ≤ ‖p‖ := Complex.re_le_norm p
    rw [hpNorm] at hle
    exact lt_of_le_of_ne hle (by
      intro h
      have hre : p.re = 1 := h
      have him : p.im = 0 := by
        have hnormSq : Complex.normSq p = 1 := by
          rw [show Complex.normSq p = ‖p‖ ^ 2 from RCLike.normSq_eq_def' p, hpNorm]
          norm_num
        rw [Complex.normSq_apply, hre] at hnormSq
        nlinarith [sq_nonneg p.im]
      apply hpNe
      apply Complex.ext
      · simpa using hre
      · simpa using him)
  refine ⟨by simp; linarith, fun k ↦ ?_⟩
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
    (p⁻¹ ^ k - 1).re ≤ ‖p⁻¹ ^ k‖ - 1 := by
      simp only [Complex.sub_re, Complex.one_re]
      exact sub_le_sub_right (Complex.re_le_norm _) 1
    _ = 0 := by rw [norm_pow, norm_inv, hpNorm]; norm_num
    _ < (1 - p).re := by simp; linarith

lemma unit_separator_term_ne_zero {p : ℂ} (hpNorm : ‖p‖ = 1) (hpNe : p ≠ 1)
    (hpow : ∀ m : ℕ, 0 < m → p ^ m ≠ 1) (n : ℕ) :
    ((1 - p) * p⁻¹ ^ (n + 1)).re ≠ 0 := by
  have hp0 : p ≠ 0 := by
    intro hp
    simp [hp] at hpNorm
  intro hz
  let z : ℂ := (1 - p) * p⁻¹ ^ (n + 1)
  have hz' : z.re = 0 := by simpa [z] using hz
  have hzconj : conj z = -z := by
    apply Complex.ext
    · simp only [Complex.conj_re, Complex.neg_re, hz', neg_zero]
    · simp only [Complex.conj_im, Complex.neg_im]
  have hconjp : conj p = p⁻¹ := (Complex.inv_eq_conj hpNorm).symm
  have hconjz : conj z = (1 - p⁻¹) * p ^ (n + 1) := by
    simp [z, map_mul, hconjp]
  have hzsum : (1 - p) * p⁻¹ ^ (n + 1) + (1 - p⁻¹) * p ^ (n + 1) = 0 := by
    change z + (1 - p⁻¹) * p ^ (n + 1) = 0
    rw [← hconjz, hzconj, add_neg_cancel]
  have hfactor : (1 - p) * (1 - p ^ (2 * n + 1)) = 0 := by
    have hcancelSucc : p ^ (n + 1) * p⁻¹ ^ (n + 1) = 1 := by
      rw [← mul_pow]
      simp [hp0]
    have hinvPow : p⁻¹ * p ^ (n + 1) = p ^ n := by
      rw [pow_succ]
      calc
        p⁻¹ * (p ^ n * p) = p ^ n * (p⁻¹ * p) := by ring
        _ = p ^ n := by simp [hp0]
    have hterm1 : p ^ (n + 1) * ((1 - p) * p⁻¹ ^ (n + 1)) = 1 - p := by
      calc
        _ = (1 - p) * (p ^ (n + 1) * p⁻¹ ^ (n + 1)) := by ring
        _ = 1 - p := by rw [hcancelSucc, mul_one]
    have hinner : (1 - p⁻¹) * p ^ (n + 1) = (p - 1) * p ^ n := by
      rw [sub_mul, one_mul, hinvPow]
      rw [pow_succ]
      ring
    have hterm2 : p ^ (n + 1) * ((1 - p⁻¹) * p ^ (n + 1)) =
        (p - 1) * p ^ (2 * n + 1) := by
      rw [hinner]
      calc
        p ^ (n + 1) * ((p - 1) * p ^ n) = (p - 1) * (p ^ (n + 1) * p ^ n) := by ring
        _ = (p - 1) * p ^ (2 * n + 1) := by
          rw [← pow_add]
          congr 2
          omega
    calc
      (1 - p) * (1 - p ^ (2 * n + 1)) = p ^ (n + 1) *
          ((1 - p) * p⁻¹ ^ (n + 1) + (1 - p⁻¹) * p ^ (n + 1)) := by
            rw [mul_add, hterm1, hterm2]
            ring
      _ = 0 := by rw [hzsum, mul_zero]
  rcases mul_eq_zero.mp hfactor with hpone | hroot
  · exact hpNe (sub_eq_zero.mp hpone).symm
  · apply hpow (2 * n + 1) (by omega)
    exact (sub_eq_zero.mp hroot).symm

lemma exists_vertical_integer_approx {v : ℂ} {c : ℝ} (hc : 0 < c) (hv : ‖v‖ = c) :
    ∃ k : ℤ, |k| = 1 ∧ |v.im - c * k| ≤ v.re ^ 2 / c := by
  have him : |v.im| ≤ c := by
    rw [← hv]
    simpa [Real.norm_eq_abs] using RCLike.norm_im_le_norm v
  have hcircle : v.re ^ 2 + v.im ^ 2 = c ^ 2 := by
    have hsq : Complex.normSq v = c ^ 2 := by
      rw [show Complex.normSq v = ‖v‖ ^ 2 from RCLike.normSq_eq_def' v, hv]
    simpa [Complex.normSq_apply, pow_two] using hsq
  by_cases hy : 0 ≤ v.im
  · refine ⟨1, by norm_num, ?_⟩
    have hyc : v.im ≤ c := by simpa [abs_of_nonneg hy] using him
    rw [Int.cast_one, mul_one, abs_of_nonpos (sub_nonpos.mpr hyc)]
    apply (le_div_iff₀ hc).2
    nlinarith [sq_nonneg (c - v.im)]
  · refine ⟨-1, by norm_num, ?_⟩
    have hyneg : v.im < 0 := lt_of_not_ge hy
    have hyc : -v.im ≤ c := by simpa [abs_of_neg hyneg] using him
    rw [Int.cast_neg, Int.cast_one, mul_neg, mul_one, abs_of_nonneg (by linarith)]
    apply (le_div_iff₀ hc).2
    nlinarith [sq_nonneg (c + v.im)]

lemma exists_vertical_integer_approx_height_one {p w : ℂ} {s : ℤ}
    (hp : ‖p‖ = 1) (hw : w ≠ 0) (hs : |s| ≤ 1) (i : ℕ) :
    ∃ k : ℤ, |((s : ℂ) * (w * p⁻¹ ^ i)).im - ‖w‖ * k| ≤
      (((s : ℂ) * (w * p⁻¹ ^ i)).re) ^ 2 / ‖w‖ := by
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  rcases Int.abs_le_one_iff.mp hs with hs | hs | hs
  · subst s
    exact ⟨0, by simp⟩
  · subst s
    have hvnorm : ‖(1 : ℂ) * (w * p⁻¹ ^ i)‖ = ‖w‖ := by
      simp [norm_pow, norm_inv, hp]
    obtain ⟨k, -, hk⟩ := exists_vertical_integer_approx hwpos hvnorm
    exact ⟨k, by simpa using hk⟩
  · subst s
    have hvnorm : ‖(-1 : ℂ) * (w * p⁻¹ ^ i)‖ = ‖w‖ := by
      simp [norm_pow, norm_inv, hp]
    obtain ⟨k, -, hk⟩ := exists_vertical_integer_approx hwpos hvnorm
    exact ⟨k, by simpa using hk⟩

/-- Infinite pigeonhole extraction used in the unit-circle branch of the
corrected Erdős--Komornik conjugate argument. -/
lemma exists_tail_pair_same_norm_and_im_sign {S : ℕ → ℂ} {s : ℕ → ℤ}
    (hsupp : {i | s i ≠ 0}.Infinite)
    (hnorm : (Set.range fun n ↦ ‖S n‖).Finite) (N : ℕ) :
    ∃ r t : ℕ, N ≤ r ∧ r < t ∧ s r ≠ 0 ∧ s t ≠ 0 ∧
      ‖S r‖ = ‖S t‖ ∧ (0 ≤ (S r).im ↔ 0 ≤ (S t).im) := by
  let A : Set ℕ := {i | N ≤ i ∧ s i ≠ 0}
  have hA : A.Infinite := by
    have htail := hsupp.sdiff (Set.finite_Iio N)
    have heq : {i | s i ≠ 0} \ Set.Iio N = A := by
      ext i
      simp [A, and_comm, not_lt]
    simpa [heq] using htail
  let R : Set ℝ := Set.range fun n ↦ ‖S n‖
  let color : A → R × Bool := fun i ↦
    (⟨‖S i.1‖, Set.mem_range_self i.1⟩, decide (0 ≤ (S i.1).im))
  let : Infinite A := hA.to_subtype
  let : Finite R := hnorm
  obtain ⟨i, j, hij, hc⟩ := Finite.exists_ne_map_eq_of_infinite color
  have hij' : i.1 ≠ j.1 := by
    intro h
    apply hij
    exact Subtype.ext h
  have hnormij : ‖S i.1‖ = ‖S j.1‖ := by
    have h := congrArg (fun z : R × Bool ↦ z.1.1) hc
    simpa [color] using h
  have hsignij : (0 ≤ (S i.1).im ↔ 0 ≤ (S j.1).im) := by
    have h := congrArg (fun z : R × Bool ↦ z.2) hc
    change decide (0 ≤ (S i.1).im) = decide (0 ≤ (S j.1).im) at h
    exact decide_eq_decide.mp h
  rcases lt_or_gt_of_ne hij' with hijlt | hjilt
  · exact ⟨i.1, j.1, i.2.1, hijlt, i.2.2, j.2.2, hnormij, hsignij⟩
  · exact ⟨j.1, i.1, j.2.1, hjilt, j.2.2, i.2.2, hnormij.symm, hsignij.symm⟩

def unitWeightedPartialSum (p w : ℂ) (s : ℕ → ℤ) (n : ℕ) : ℂ :=
  ∑ i ∈ Finset.range (n + 1), (s i : ℂ) * (w * p⁻¹ ^ i)

lemma unitWeightedPartialSum_succ (p w : ℂ) (s : ℕ → ℤ) (n : ℕ) :
    unitWeightedPartialSum p w s (n + 1) = unitWeightedPartialSum p w s n +
      (s (n + 1) : ℂ) * (w * p⁻¹ ^ (n + 1)) := by
  simp [unitWeightedPartialSum, Finset.sum_range_succ]

lemma unitWeightedPartialSum_re_converges {p w : ℂ} {s : ℕ → ℤ} {K : ℕ}
    (hfinite : (Set.range fun n ↦ ‖unitWeightedPartialSum p w s n‖).Finite)
    (hstep : ∀ i, K < i →
      ((s i : ℂ) * (w * p⁻¹ ^ i)).re ≤ 0) :
    ∃ L : ℝ, Tendsto (fun n ↦ (unitWeightedPartialSum p w s (K + n)).re)
      atTop (𝓝 L) := by
  let S : ℕ → ℂ := unitWeightedPartialSum p w s
  obtain ⟨C, hC⟩ := hfinite.bddAbove
  have hnorm : ∀ n, ‖S n‖ ≤ C := by
    intro n
    exact hC ⟨n, rfl⟩
  let x : ℕ → ℝ := fun n ↦ (S (K + n)).re
  have hxanti : Antitone x := antitone_nat_of_succ_le (fun n ↦ by
    have hrec := unitWeightedPartialSum_succ p w s (K + n)
    have hnonpos := hstep (K + n + 1) (by omega)
    dsimp only [x, S]
    rw [show K + (n + 1) = (K + n) + 1 by omega, hrec]
    simp only [Complex.add_re]
    linarith)
  have hxbdd : BddBelow (Set.range x) := by
    refine ⟨-C, ?_⟩
    rintro _ ⟨n, rfl⟩
    have hre : |(S (K + n)).re| ≤ C := by
      exact (RCLike.norm_re_le_norm _).trans (hnorm (K + n))
    exact (abs_le.mp hre).1
  exact ⟨⨅ i, x i, tendsto_atTop_ciInf hxanti hxbdd⟩

lemma unitWeightedPartialSum_vertical_lattice_approx {p w : ℂ} {s : ℕ → ℤ}
    {r t : ℕ} {δ : ℝ} (hp : ‖p‖ = 1) (hw : w ≠ 0)
    (hs : ∀ i, |s i| ≤ 1) (hrt : r < t)
    (hnonpos : ∀ i, r < i → i ≤ t →
      ((s i : ℂ) * (w * p⁻¹ ^ i)).re ≤ 0)
    (hsmall : ∀ i, r < i → i ≤ t →
      |((s i : ℂ) * (w * p⁻¹ ^ i)).re| ≤ δ * ‖w‖) :
    ∃ k : ℤ,
      |(unitWeightedPartialSum p w s t - unitWeightedPartialSum p w s r).im -
          ‖w‖ * k| ≤
        δ * ((unitWeightedPartialSum p w s r).re -
          (unitWeightedPartialSum p w s t).re) := by
  classical
  let v : ℕ → ℂ := fun i ↦ (s i : ℂ) * (w * p⁻¹ ^ i)
  let I : Finset ℕ := Finset.Ico (r + 1) (t + 1)
  let k : ℕ → ℤ := fun i ↦ Classical.choose
    (exists_vertical_integer_approx_height_one hp hw (hs i) i)
  have hk (i : ℕ) :
      |(v i).im - ‖w‖ * k i| ≤ (v i).re ^ 2 / ‖w‖ := by
    simpa [v, k] using
      (Classical.choose_spec (exists_vertical_integer_approx_height_one hp hw (hs i) i))
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hterm (i : ℕ) (hi : i ∈ I) :
      |(v i).im - ‖w‖ * k i| ≤ δ * (-(v i).re) := by
    have hi' : i ∈ Finset.Ico (r + 1) (t + 1) := by simpa [I] using hi
    have hiBounds := Finset.mem_Ico.mp hi'
    have hir : r < i := by omega
    have hit : i ≤ t := by omega
    have hvnonpos := hnonpos i hir hit
    have hvsmall := hsmall i hir hit
    have hneg : -(v i).re ≤ δ * ‖w‖ := by
      rw [abs_of_nonpos hvnonpos] at hvsmall
      exact hvsmall
    apply (hk i).trans
    apply (div_le_iff₀ hwpos).2
    nlinarith [sq_nonneg ((v i).re)]
  have hsum : ∑ i ∈ I, v i =
      unitWeightedPartialSum p w s t - unitWeightedPartialSum p w s r := by
    simp only [I, unitWeightedPartialSum, v]
    exact Finset.sum_Ico_eq_sub _ (by omega)
  refine ⟨∑ i ∈ I, k i, ?_⟩
  have himag :
      (unitWeightedPartialSum p w s t - unitWeightedPartialSum p w s r).im -
          ‖w‖ * (∑ i ∈ I, k i : ℤ) =
        ∑ i ∈ I, ((v i).im - ‖w‖ * k i) := by
    have hreim : (∑ i ∈ I, v i).im = ∑ i ∈ I, (v i).im := by
      simpa only [Complex.imCLM_apply] using
        (map_sum (Complex.imCLM : ℂ →L[ℝ] ℝ) v I)
    rw [← hsum, hreim, Int.cast_sum]
    rw [Finset.mul_sum, Finset.sum_sub_distrib]
  rw [himag]
  calc
    |∑ i ∈ I, ((v i).im - ‖w‖ * k i)| ≤
        ∑ i ∈ I, |(v i).im - ‖w‖ * k i| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ I, δ * (-(v i).re) := by
      exact Finset.sum_le_sum fun i hi ↦ hterm i hi
    _ = δ * ((unitWeightedPartialSum p w s r).re -
          (unitWeightedPartialSum p w s t).re) := by
      rw [← Finset.mul_sum]
      have hre : (∑ i ∈ I, v i).re = ∑ i ∈ I, (v i).re := by
        simpa only [Complex.reCLM_apply] using
          (map_sum (Complex.reCLM : ℂ →L[ℝ] ℝ) v I)
      rw [hsum] at hre
      simp only [Complex.sub_re] at hre
      have hneg : ∑ i ∈ I, -(v i).re = -(∑ i ∈ I, (v i).re) := by
        rw [Finset.sum_neg_distrib]
      rw [hneg, ← hre]
      ring

lemma abs_sub_le_abs_add_of_same_sign {a b : ℝ} (h : 0 ≤ a ↔ 0 ≤ b) :
    |a - b| ≤ |a + b| := by
  by_cases ha : 0 ≤ a
  · have hb : 0 ≤ b := h.mp ha
    rw [abs_of_nonneg (add_nonneg ha hb)]
    rcases le_total a b with hab | hba
    · rw [abs_of_nonpos (sub_nonpos.mpr hab)]
      linarith
    · rw [abs_of_nonneg (sub_nonneg.mpr hba)]
      linarith
  · have ha' : a < 0 := lt_of_not_ge ha
    have hb' : b < 0 := lt_of_not_ge (mt h.mpr ha)
    rw [abs_of_neg (add_neg ha' hb')]
    rcases le_total a b with hab | hba
    · rw [abs_of_nonpos (sub_nonpos.mpr hab)]
      linarith
    · rw [abs_of_nonneg (sub_nonneg.mpr hba)]
      linarith

lemma equal_norm_chord_product {z u : ℂ} (h : ‖z‖ = ‖u‖) :
    |z.re - u.re| * |z.re + u.re| = |z.im - u.im| * |z.im + u.im| := by
  have hsq : z.re ^ 2 + z.im ^ 2 = u.re ^ 2 + u.im ^ 2 := by
    have hn : Complex.normSq z = Complex.normSq u := by
      rw [show Complex.normSq z = ‖z‖ ^ 2 from RCLike.normSq_eq_def' z,
        show Complex.normSq u = ‖u‖ ^ 2 from RCLike.normSq_eq_def' u, h]
    simpa [Complex.normSq_apply, pow_two] using hn
  rw [← abs_mul, ← abs_mul]
  rw [show (z.re - u.re) * (z.re + u.re) =
      -((z.im - u.im) * (z.im + u.im)) by nlinarith, abs_neg]

lemma same_half_circle_chord_sq_le {z u : ℂ} (hnorm : ‖z‖ = ‖u‖)
    (hsign : 0 ≤ z.im ↔ 0 ≤ u.im) :
    |z.im - u.im| ^ 2 ≤ |z.re - u.re| * |z.re + u.re| := by
  calc
    |z.im - u.im| ^ 2 = |z.im - u.im| * |z.im - u.im| := by ring
    _ ≤ |z.im - u.im| * |z.im + u.im| :=
      mul_le_mul_of_nonneg_left (abs_sub_le_abs_add_of_same_sign hsign) (abs_nonneg _)
    _ = |z.re - u.re| * |z.re + u.re| := (equal_norm_chord_product hnorm).symm

lemma unitWeightedPartialSum_norm_range_infinite {p w : ℂ} {s : ℕ → ℤ} {K : ℕ}
    (hp : ‖p‖ = 1) (hw : w ≠ 0) (hs : ∀ i, |s i| ≤ 1)
    (hsupp : {i | s i ≠ 0}.Infinite)
    (hstep : ∀ i, K < i → ((s i : ℂ) * (w * p⁻¹ ^ i)).re ≤ 0)
    (hstrict : ∀ i, K < i → s i ≠ 0 →
      ((s i : ℂ) * (w * p⁻¹ ^ i)).re < 0)
    (hstart : (unitWeightedPartialSum p w s K).re < 0) :
    (Set.range fun n ↦ ‖unitWeightedPartialSum p w s n‖).Infinite := by
  classical
  intro hfinite
  let S : ℕ → ℂ := unitWeightedPartialSum p w s
  let c : ℝ := ‖w‖
  have hc : 0 < c := by exact norm_pos_iff.mpr hw
  obtain ⟨C, hC⟩ := hfinite.bddAbove
  let B : ℝ := max 1 C
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hSnorm : ∀ n, ‖S n‖ ≤ B := by
    intro n
    exact (hC ⟨n, rfl⟩).trans (le_max_right _ _)
  have hSre (n : ℕ) : |(S n).re| ≤ B :=
    (RCLike.norm_re_le_norm _).trans (hSnorm n)
  have hSim (n : ℕ) : |(S n).im| ≤ B :=
    (RCLike.norm_im_le_norm _).trans (hSnorm n)
  let c0 : ℝ := -(S K).re
  have hc0 : 0 < c0 := by dsimp [c0, S]; linarith
  let δ : ℝ := min (c / (16 * B)) (c0 / (4 * B))
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min (div_pos hc (by positivity)) (div_pos hc0 (by positivity))
  have hδc : δ ≤ c / (16 * B) := min_le_left _ _
  have hδc0 : δ ≤ c0 / (4 * B) := min_le_right _ _
  let E : ℝ := min (δ * c / 4) (c ^ 2 / (256 * B))
  have hE : 0 < E := by
    dsimp [E]
    exact lt_min (div_pos (mul_pos hδ hc) (by norm_num))
      (div_pos (sq_pos_of_pos hc) (by positivity))
  have hEδ : E ≤ δ * c / 4 := min_le_left _ _
  have hEc : E ≤ c ^ 2 / (256 * B) := min_le_right _ _
  obtain ⟨L, hconv⟩ := unitWeightedPartialSum_re_converges hfinite hstep
  rw [Metric.tendsto_atTop] at hconv
  obtain ⟨N, hN⟩ := hconv E hE
  have hnear {i : ℕ} (hi : K + N ≤ i) : |(S i).re - L| < E := by
    have hiK : K ≤ i := le_trans (Nat.le_add_right K N) hi
    have hiN : N ≤ i - K := by omega
    have h := hN (i - K) hiN
    have hidx : K + (i - K) = i := by omega
    simpa [S, Real.dist_eq, hidx] using h
  have hxanti : Antitone (fun n ↦ (S (K + n)).re) :=
    antitone_nat_of_succ_le (fun n ↦ by
      have hrec := unitWeightedPartialSum_succ p w s (K + n)
      have hn := hstep (K + n + 1) (by omega)
      dsimp only [S]
      rw [show K + (n + 1) = (K + n) + 1 by omega, hrec]
      simp only [Complex.add_re]
      linarith)
  obtain ⟨r, t, hrN, hrt, hsr, hst, hnormrt, hsignrt⟩ :=
    exists_tail_pair_same_norm_and_im_sign hsupp hfinite (K + N)
  have hrK : K ≤ r := le_trans (Nat.le_add_right K N) hrN
  have htK : K ≤ t := hrK.trans hrt.le
  have htailmono {a b : ℕ} (ha : K ≤ a) (hab : a ≤ b) : (S b).re ≤ (S a).re := by
    have := hxanti (Nat.sub_le_sub_right hab K)
    simpa [Nat.add_sub_of_le ha, Nat.add_sub_of_le (ha.trans hab)] using this
  have hrealrt : (S t).re < (S r).re := by
    have htpos : 0 < t := lt_of_le_of_lt (Nat.zero_le r) hrt
    have htstep := hstrict t (lt_of_le_of_lt hrK hrt) hst
    have hrec := unitWeightedPartialSum_succ p w s (t - 1)
    have htEq : t - 1 + 1 = t := by omega
    have hrprev : r ≤ t - 1 := by omega
    have hmono := htailmono hrK hrprev
    rw [htEq] at hrec
    dsimp only [S] at hrec hmono ⊢
    rw [hrec]
    simp only [Complex.add_re]
    linarith
  let H : ℝ := (S r).re - (S t).re
  have hH : 0 < H := by dsimp [H]; linarith
  have hHclose : H < 2 * E := by
    have hrnear := hnear hrN
    have htnear := hnear (hrN.trans hrt.le)
    dsimp only [H]
    have htri : |(S r).re - (S t).re| ≤
        |(S r).re - L| + |(S t).re - L| := by
      calc
        |(S r).re - (S t).re| ≤ |(S r).re - L| + |L - (S t).re| :=
          abs_sub_le _ _ _
        _ = _ := by rw [abs_sub_comm L]
    rw [abs_of_pos (by linarith)] at htri
    linarith
  have hHbound : H ≤ 2 * B := by
    have hrabs := hSre r
    have htabs := hSre t
    dsimp only [H]
    have hrle : (S r).re ≤ |(S r).re| := le_abs_self _
    have htle : -(S t).re ≤ |(S t).re| := neg_le_abs _
    linarith
  have hsmall : ∀ i, r < i → i ≤ t →
      |((s i : ℂ) * (w * p⁻¹ ^ i)).re| ≤ δ * ‖w‖ := by
    intro i hri hit
    have hiN : K + N ≤ i := hrN.trans hri.le
    have him1N : K + N ≤ i - 1 := by omega
    have hinear := hnear hiN
    have him1near := hnear him1N
    have hrec := unitWeightedPartialSum_succ p w s (i - 1)
    have hiEq : i - 1 + 1 = i := by omega
    rw [hiEq] at hrec
    have htermEq : ((s i : ℂ) * (w * p⁻¹ ^ i)).re =
        (S i).re - (S (i - 1)).re := by
      dsimp only [S]
      rw [hrec]
      simp
    rw [htermEq]
    apply le_of_lt
    calc
      |(S i).re - (S (i - 1)).re| ≤
          |(S i).re - L| + |L - (S (i - 1)).re| := abs_sub_le _ _ _
      _ = |(S i).re - L| + |(S (i - 1)).re - L| := by rw [abs_sub_comm L]
      _ < 2 * E := by linarith
      _ ≤ δ * c := by
        have : 2 * E ≤ δ * c / 2 := by linarith
        linarith
      _ = δ * ‖w‖ := rfl
  obtain ⟨k, hk⟩ := unitWeightedPartialSum_vertical_lattice_approx hp hw hs hrt
    (fun i hir hit ↦ hstep i (lt_of_le_of_lt hrK hir)) hsmall
  have himsq := same_half_circle_chord_sq_le hnormrt hsignrt
  have himsmall : |(S t).im - (S r).im| < c / 4 := by
    have hxsum : |(S r).re + (S t).re| ≤ 2 * B := by
      exact (abs_add_le _ _).trans (by linarith [hSre r, hSre t])
    have hdx : |(S r).re - (S t).re| = H := abs_of_pos hH
    have hprod : H * |(S r).re + (S t).re| < c ^ 2 / 16 := by
      rw [← hdx]
      calc
        |(S r).re - (S t).re| * |(S r).re + (S t).re| ≤ H * (2 * B) := by
          rw [hdx]
          exact mul_le_mul_of_nonneg_left hxsum hH.le
        _ < (2 * E) * (2 * B) := by nlinarith
        _ ≤ c ^ 2 / 16 := by
          have hEB : E * B ≤ (c ^ 2 / (256 * B)) * B :=
            mul_le_mul_of_nonneg_right hEc hB.le
          have hcancel : c ^ 2 / (256 * B) * B = c ^ 2 / 256 := by
            field_simp [ne_of_gt hB]
          have hEB' : E * B ≤ c ^ 2 / 256 := by
            calc E * B ≤ (c ^ 2 / (256 * B)) * B := hEB
              _ = c ^ 2 / 256 := hcancel
          nlinarith
    have hsq : |(S t).im - (S r).im| ^ 2 < c ^ 2 / 16 := by
      change |(S r).im - (S t).im| ^ 2 ≤
        |(S r).re - (S t).re| * |(S r).re + (S t).re| at himsq
      rw [abs_sub_comm]
      exact lt_of_le_of_lt himsq (by simpa [hdx] using hprod)
    nlinarith [sq_nonneg (|(S t).im - (S r).im|), sq_pos_of_pos hc]
  have hk' : |(S t).im - (S r).im - c * k| ≤ δ * H := by
    simpa [S, c, H, abs_sub_comm] using hk
  have hδH : δ * H ≤ c / 8 := by
    have hδB : δ * (2 * B) ≤ c / 8 := by
      calc
        δ * (2 * B) ≤ (c / (16 * B)) * (2 * B) :=
          mul_le_mul_of_nonneg_right hδc (by positivity)
        _ = c / 8 := by
          field_simp [ne_of_gt hB]
          all_goals norm_num
    exact (mul_le_mul_of_nonneg_left hHbound hδ.le).trans hδB
  have hkabs : |c * (k : ℝ)| < c := by
    have htri : |c * (k : ℝ)| ≤ |(S t).im - (S r).im| +
        |(S t).im - (S r).im - c * k| := by
      calc
        |c * (k : ℝ)| = |((S t).im - (S r).im) -
            ((S t).im - (S r).im - c * k)| := by ring_nf
        _ = |((S t).im - (S r).im) +
            (-((S t).im - (S r).im - c * k))| := by ring
        _ ≤ |(S t).im - (S r).im| +
            |-((S t).im - (S r).im - c * k)| := abs_add_le _ _
        _ = _ := by rw [abs_neg]
    linarith
  have hkzero : k = 0 := by
    by_contra hk0
    have hkoneZ : 1 ≤ |k| := Int.one_le_abs hk0
    have hkone : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast hkoneZ
    rw [abs_mul, abs_of_pos hc] at hkabs
    nlinarith
  have himfinal : |(S t).im - (S r).im| ≤ δ * H := by
    rw [hkzero] at hk'
    simpa using hk'
  have hrneg : (S r).re ≤ (S K).re := htailmono le_rfl hrK
  have htneg : (S t).re ≤ (S K).re := htailmono le_rfl htK
  have hxsumLower : 2 * c0 ≤ |(S r).re + (S t).re| := by
    rw [abs_of_neg (by dsimp [c0] at hc0; linarith)]
    dsimp [c0]
    linarith
  have hysumUpper : |(S r).im + (S t).im| ≤ 2 * B :=
    (abs_add_le _ _).trans (by linarith [hSim r, hSim t])
  have hchord := equal_norm_chord_product hnormrt
  have hdx : |(S r).re - (S t).re| = H := abs_of_pos hH
  rw [hdx] at hchord
  have hlower : H * (2 * c0) ≤
      H * |(S r).re + (S t).re| :=
    mul_le_mul_of_nonneg_left hxsumLower hH.le
  have hupper : |(S r).im - (S t).im| * |(S r).im + (S t).im| ≤
      (δ * H) * (2 * B) := by
    have hd : |(S r).im - (S t).im| ≤ δ * H := by
      simpa [abs_sub_comm] using himfinal
    exact mul_le_mul hd hysumUpper (abs_nonneg _) (by positivity)
  have hmain : H * (2 * c0) ≤ (δ * H) * (2 * B) := by
    calc
      H * (2 * c0) ≤ H * |(S r).re + (S t).re| := hlower
      _ = |(S r).im - (S t).im| * |(S r).im + (S t).im| := hchord
      _ ≤ (δ * H) * (2 * B) := hupper
  have hδsmall : δ * (4 * B) ≤ c0 := by
    calc
      δ * (4 * B) ≤ (c0 / (4 * B)) * (4 * B) :=
        mul_le_mul_of_nonneg_right hδc0 (by positivity)
      _ = c0 := by field_simp [ne_of_gt hB]
  nlinarith

lemma exists_unit_conjugate_expansion_with_infinite_radii {q : ℝ} {p : ℂ}
    (hq1 : 1 < q) (hq2 : q < 2) (hqint : IsIntegral ℤ q)
    (hpRoot : ((minpoly ℤ q).map (algebraMap ℤ ℂ)).eval p = 0)
    (hpNorm : ‖p‖ = 1) (hpNe : p ≠ 1)
    (hpPow : ∀ m : ℕ, 0 < m → p ^ m ≠ 1) :
    ∃ s : ℕ → ℤ, (∀ i, |s i| ≤ 1) ∧ SignedExpansion q s ∧
      (Set.range fun n ↦ ‖∑ i ∈ Finset.range (n + 1),
        (s i : ℂ) * p⁻¹ ^ i‖).Infinite := by
  classical
  let w : ℂ := 1 - p
  let a : ℕ → ℝ := fun n ↦ (w * p⁻¹ ^ (n + 1)).re
  have hsep := unit_separator_prefix hpNorm hpNe
  change 0 < w.re ∧ ∀ k : ℕ, ∑ i ∈ Finset.range k, a i < w.re at hsep
  obtain ⟨hwre, hprefix⟩ := hsep
  obtain ⟨K, s, hs, hs0, hsExp, hsP, hsPc, hcoeffOne⟩ :=
    exists_lazy_expansion_for_separator hq1 hq2 a
  have hw : w ≠ 0 := by
    intro h
    change 1 - p = 0 at h
    have hp1 : (1 : ℂ) = p := sub_eq_zero.mp h
    exact hpNe hp1.symm
  have htermRe (i : ℕ) :
      ((s i : ℂ) * (w * p⁻¹ ^ i)).re =
        (s i : ℝ) * (w * p⁻¹ ^ i).re := by
    simp
  have hstep : ∀ i, K < i → ((s i : ℂ) * (w * p⁻¹ ^ i)).re ≤ 0 := by
    intro i hi
    have hi0 : 0 < i := lt_of_le_of_lt (Nat.zero_le K) hi
    let n := i - 1
    have hnK : K ≤ n := by dsimp [n]; omega
    have hin : n + 1 = i := by dsimp [n]; omega
    have haCases : a n ≤ 0 ∨ 0 < a n := le_or_gt (a n) 0
    rw [← hin, htermRe]
    change (s (n + 1) : ℝ) * a n ≤ 0
    rcases haCases with han | hap
    · exact mul_nonpos_of_nonneg_of_nonpos
        (by exact_mod_cast hsP n (Or.inr han)) han
    · have hsnonpos : s (n + 1) ≤ 0 := hsPc n (by
        simp only [not_or, not_lt]
        exact ⟨hnK, not_le.mpr hap⟩)
      exact mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hsnonpos) hap.le
  have hstrict : ∀ i, K < i → s i ≠ 0 →
      ((s i : ℂ) * (w * p⁻¹ ^ i)).re < 0 := by
    intro i hi hsi
    have hi0 : 0 < i := lt_of_le_of_lt (Nat.zero_le K) hi
    let n := i - 1
    have hnK : K ≤ n := by dsimp [n]; omega
    have hin : n + 1 = i := by dsimp [n]; omega
    have hane : a n ≠ 0 := by
      dsimp [a, w, n]
      simpa [hin] using unit_separator_term_ne_zero hpNorm hpNe hpPow (i - 1)
    rcases lt_or_gt_of_ne hane with han | hap
    · have hsnonneg : 0 ≤ s (n + 1) := hsP n (Or.inr han.le)
      have hspos : 0 < s (n + 1) := lt_of_le_of_ne hsnonneg (by simpa [hin] using hsi.symm)
      rw [← hin, htermRe]
      change (s (n + 1) : ℝ) * a n < 0
      exact mul_neg_of_pos_of_neg (by exact_mod_cast hspos) han
    · have hsnonpos : s (n + 1) ≤ 0 := hsPc n (by
        simp only [not_or, not_lt]
        exact ⟨hnK, not_le.mpr hap⟩)
      have hsneg : s (n + 1) < 0 := lt_of_le_of_ne hsnonpos (by simpa [hin] using hsi)
      rw [← hin, htermRe]
      change (s (n + 1) : ℝ) * a n < 0
      exact mul_neg_of_neg_of_pos (by exact_mod_cast hsneg) hap
  have hstart : (unitWeightedPartialSum p w s K).re < 0 := by
    have hcomplex : unitWeightedPartialSum p w s K =
        -w + ∑ n ∈ Finset.range K, (s (n + 1) : ℂ) * (w * p⁻¹ ^ (n + 1)) := by
      rw [unitWeightedPartialSum, Finset.sum_range_succ']
      simp [hs0, add_comm]
    have htailRe :
        (∑ n ∈ Finset.range K, (s (n + 1) : ℂ) * (w * p⁻¹ ^ (n + 1))).re =
          ∑ n ∈ Finset.range K, (s (n + 1) : ℝ) * a n := by
      have hmap := map_sum (Complex.reCLM : ℂ →L[ℝ] ℝ)
        (fun n ↦ (s (n + 1) : ℂ) * (w * p⁻¹ ^ (n + 1))) (Finset.range K)
      have hmap' :
          (∑ n ∈ Finset.range K,
            (s (n + 1) : ℂ) * (w * p⁻¹ ^ (n + 1))).re =
            ∑ n ∈ Finset.range K,
              ((s (n + 1) : ℂ) * (w * p⁻¹ ^ (n + 1))).re := by
        simpa only [Complex.reCLM_apply] using hmap
      rw [hmap']
      apply Finset.sum_congr rfl
      intro n hn
      rw [htermRe]
    have hsumRe : (unitWeightedPartialSum p w s K).re =
        -w.re + ∑ n ∈ Finset.range K, (s (n + 1) : ℝ) * a n := by
      rw [hcomplex]
      simp only [Complex.add_re, Complex.neg_re, htailRe]
    have htermle : ∀ n ∈ Finset.range K,
        (s (n + 1) : ℝ) * a n ≤ a n := by
      intro n hn
      have hnK : n < K := Finset.mem_range.mp hn
      by_cases han : 0 ≤ a n
      · have hsle : (s (n + 1) : ℝ) ≤ 1 := by
          exact_mod_cast (le_trans (le_abs_self _) (hs (n + 1)))
        nlinarith
      · have haneg : a n < 0 := lt_of_not_ge han
        rw [hcoeffOne n hnK haneg]
        norm_num
    have hsumle : (∑ n ∈ Finset.range K, (s (n + 1) : ℝ) * a n) ≤
        ∑ n ∈ Finset.range K, a n := Finset.sum_le_sum htermle
    rw [hsumRe]
    linarith [hprefix K]
  have hsupp : {i | s i ≠ 0}.Infinite := by
    by_contra hsuppInf
    have hsuppFin : {i | s i ≠ 0}.Finite := not_not.mp hsuppInf
    let F : Finset ℕ := hsuppFin.toFinset
    let N : ℕ := max K (F.sup id)
    have hKN : K ≤ N := le_max_left _ _
    have hzeroAfter : ∀ i, N < i → s i = 0 := by
      intro i hi
      by_contra hsi
      have hiF : i ∈ F := by simp [F, hsi]
      have hisup : i ≤ F.sup id := Finset.le_sup (f := id) hiF
      dsimp [N] at hi
      omega
    have hpartialQ :
        ∑ i ∈ Finset.range (N + 1), (s i : ℝ) * q⁻¹ ^ i = 0 := by
      calc
        ∑ i ∈ Finset.range (N + 1), (s i : ℝ) * q⁻¹ ^ i =
            ∑' i, (s i : ℝ) * q⁻¹ ^ i := by
          symm
          apply tsum_eq_sum
          intro i hi
          have hiN : N < i := by simpa using hi
          simp [hzeroAfter i hiN]
        _ = 0 := hsExp.tsum_eq
    have hrevQ : (reversedPolynomial s N).eval₂ (algebraMap ℤ ℝ) q = 0 := by
      have hformulaQR : q⁻¹ ^ N *
          (reversedPolynomial s N).eval₂ (algebraMap ℤ ℝ) q =
          ∑ i ∈ Finset.range (N + 1), (s i : ℝ) * q⁻¹ ^ i := by
        rw [eval₂_reversedPolynomial, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        have hiN : i ≤ N := by simpa using hi
        rw [pow_sub₀ q (by linarith) hiN]
        simp only [inv_pow]
        have hq0 : q ≠ 0 := ne_of_gt (lt_trans zero_lt_one hq1)
        calc
          (q ^ N)⁻¹ * ((s i : ℝ) * (q ^ N * (q ^ i)⁻¹)) =
              ((q ^ N)⁻¹ * q ^ N) * ((s i : ℝ) * (q ^ i)⁻¹) := by ring
          _ = (s i : ℝ) * (q ^ i)⁻¹ := by simp [pow_ne_zero N hq0]
      rw [hpartialQ] at hformulaQR
      exact (mul_eq_zero.mp hformulaQR).resolve_left (pow_ne_zero _ (inv_ne_zero (by linarith)))
    have hrevP : (reversedPolynomial s N).eval₂ (algebraMap ℤ ℂ) p = 0 := by
      have := eval₂_eq_at_conjugate_of_eval₂_eq hqint hpRoot
        (P := reversedPolynomial s N) (Q := 0) (by simpa using hrevQ)
      simpa using this
    have hp0 : p ≠ 0 := by
      intro hp0
      simp [hp0] at hpNorm
    have hformulaP := inv_pow_mul_eval₂_reversedPolynomial hp0 s N
    have hpartialP : ∑ i ∈ Finset.range (N + 1), (s i : ℂ) * p⁻¹ ^ i = 0 := by
      rw [hrevP, mul_zero] at hformulaP
      exact hformulaP.symm
    have hSNzero : unitWeightedPartialSum p w s N = 0 := by
      rw [unitWeightedPartialSum]
      calc
        ∑ i ∈ Finset.range (N + 1), (s i : ℂ) * (w * p⁻¹ ^ i) =
            w * ∑ i ∈ Finset.range (N + 1), (s i : ℂ) * p⁻¹ ^ i := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = 0 := by rw [hpartialP, mul_zero]
    have hmono : (unitWeightedPartialSum p w s N).re ≤
        (unitWeightedPartialSum p w s K).re := by
      have hxanti : Antitone (fun n ↦
          (unitWeightedPartialSum p w s (K + n)).re) :=
        antitone_nat_of_succ_le (fun n ↦ by
          rw [show K + (n + 1) = (K + n) + 1 by omega,
            unitWeightedPartialSum_succ]
          simp only [Complex.add_re]
          exact add_le_of_nonpos_right (hstep (K + n + 1) (by omega)))
      have hm := hxanti (Nat.zero_le (N - K))
      simpa [Nat.add_sub_of_le hKN] using hm
    rw [hSNzero] at hmono
    simp only [Complex.zero_re] at hmono
    linarith
  have hweighted := unitWeightedPartialSum_norm_range_infinite hpNorm hw hs hsupp
    hstep hstrict hstart
  refine ⟨s, hs, hsExp, ?_⟩
  intro hfinitePartial
  apply hweighted
  let T : ℕ → ℂ := fun n ↦ ∑ i ∈ Finset.range (n + 1), (s i : ℂ) * p⁻¹ ^ i
  have hnormEq (n : ℕ) : ‖unitWeightedPartialSum p w s n‖ = ‖w‖ * ‖T n‖ := by
    have hsum : unitWeightedPartialSum p w s n = w * T n := by
      dsimp only [unitWeightedPartialSum, T]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hsum, norm_mul]
  exact hfinitePartial.image (fun x ↦ ‖w‖ * x) |>.subset (by
    rintro _ ⟨n, rfl⟩
    exact ⟨‖T n‖, ⟨n, rfl⟩, (hnormEq n).symm⟩)

lemma conjugate_not_root_of_unity {q : ℝ} {p : ℂ} (hqint : IsIntegral ℤ q)
    (hq1 : 1 < q)
    (hpRoot : ((minpoly ℤ q).map (algebraMap ℤ ℂ)).eval p = 0) :
    ∀ m : ℕ, 0 < m → p ^ m ≠ 1 := by
  have hqCint : IsIntegral ℤ (q : ℂ) :=
    hqint.map (IsScalarTower.toAlgHom ℤ ℝ ℂ)
  have hminZ : minpoly ℤ (q : ℂ) = minpoly ℤ q := by
    exact minpoly.algebraMap_eq Complex.ofRealHom.injective q
  have hminQ : minpoly ℚ (q : ℂ) =
      (minpoly ℤ q).map (algebraMap ℤ ℚ) := by
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hqCint, hminZ]
  have hpRat : Polynomial.aeval p (minpoly ℚ (q : ℂ)) = 0 := by
    rw [hminQ, Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map,
      Polynomial.map_map]
    rw [← IsScalarTower.algebraMap_eq ℤ ℚ ℂ]
    exact hpRoot
  have hqCintQ : IsIntegral ℚ (q : ℂ) := hqCint.tower_top
  have hconj : IsConjRoot ℚ (q : ℂ) p :=
    isConjRoot_of_aeval_eq_zero hqCintQ hpRat
  intro m hm hpm
  let G : ℚ[X] := X ^ m - 1
  have hpG : Polynomial.aeval p G = 0 := by
    simp [G, hpm]
  have hdvdP : minpoly ℚ p ∣ G := minpoly.dvd ℚ p hpG
  have hdvdQ : minpoly ℚ (q : ℂ) ∣ G := by
    rw [hconj]
    exact hdvdP
  have hqG : Polynomial.aeval (q : ℂ) G = 0 :=
    Polynomial.aeval_eq_zero_of_dvd_aeval_eq_zero hdvdQ (minpoly.aeval ℚ (q : ℂ))
  have hqpowC : (q : ℂ) ^ m = 1 := sub_eq_zero.mp (by simpa [G] using hqG)
  have hqpowR : q ^ m = 1 := by exact_mod_cast hqpowC
  have : 1 < q ^ m := one_lt_pow₀ hq1 hm.ne'
  linarith

lemma conjugate_not_unit_of_no_accumulation {q : ℝ} {p : ℂ}
    (hq1 : 1 < q) (hq2 : q < 2)
    (hno : ¬ HasAccumulation (SignedSpectrum q))
    (hpRoot : ((minpoly ℤ q).map (algebraMap ℤ ℂ)).eval p = 0)
    (hpNorm : ‖p‖ = 1) : False := by
  have hqint := integral_of_no_signedSpectrum_accumulation hq1 hq2 hno
  have hpPow := conjugate_not_root_of_unity hqint hq1 hpRoot
  have hpNe : p ≠ 1 := by
    intro hp1
    apply hpPow 1 (by omega)
    simp [hp1]
  obtain ⟨s, hs, hsExp, hinfinite⟩ :=
    exists_unit_conjugate_expansion_with_infinite_radii hq1 hq2 hqint hpRoot
      hpNorm hpNe hpPow
  let f : ℕ → ℂ := fun n ↦
    (reversedPolynomial s n).eval₂ (algebraMap ℤ ℂ) p
  let T : ℕ → ℂ := fun n ↦
    ∑ i ∈ Finset.range (n + 1), (s i : ℂ) * p⁻¹ ^ i
  have hfiniteF : (Set.range f).Finite :=
    finite_reversed_tail_range_at_conjugate hqint hno hpRoot hs
      (fun n ↦ reversed_tail_bound_of_signedExpansion hq1 hs hsExp n)
  have hp0 : p ≠ 0 := by
    intro hp0
    simp [hp0] at hpNorm
  have hnormEq (n : ℕ) : ‖T n‖ = ‖f n‖ := by
    have hformula := inv_pow_mul_eval₂_reversedPolynomial hp0 s n
    change p⁻¹ ^ n * f n = T n at hformula
    calc
      ‖T n‖ = ‖p⁻¹ ^ n * f n‖ := congrArg norm hformula.symm
      _ = ‖p⁻¹ ^ n‖ * ‖f n‖ := norm_mul _ _
      _ = ‖f n‖ := by rw [norm_pow, norm_inv, hpNorm]; simp
  apply hinfinite
  apply (hfiniteF.image norm).subset
  rintro _ ⟨n, rfl⟩
  exact ⟨f n, ⟨n, rfl⟩, (hnormEq n).symm⟩

/-- The corrected Erdős--Komornik conjugate argument: if the signed binary
spectrum has no finite accumulation point, then the base is Pisot. -/
lemma isPisot_of_no_signedSpectrum_accumulation {q : ℝ}
    (hq1 : 1 < q) (hq2 : q < 2)
    (hno : ¬ HasAccumulation (SignedSpectrum q)) :
    IsPisot1096 q := by
  have hqint : IsIntegral ℤ q :=
    integral_of_no_signedSpectrum_accumulation hq1 hq2 hno
  refine ⟨hq1, hqint, ?_⟩
  intro z hz hzq
  by_contra hnotlt
  have hge : 1 ≤ ‖z‖ := le_of_not_gt hnotlt
  rcases hge.eq_or_lt with hunit | hlarge
  · exact conjugate_not_unit_of_no_accumulation hq1 hq2 hno hz hunit.symm
  · by_cases him : z.im = 0
    · by_cases hre : 1 < z.re
      · apply conjugate_not_positive_real_of_no_accumulation hq1 hq2 hno hre
          (by
            intro heq
            apply hzq
            apply Complex.ext
            · simpa using heq
            · simpa using him)
        have hzReal : (z.re : ℂ) = z := by
          apply Complex.ext <;> simp [him]
        rw [hzReal]
        exact hz
      · have hzReal : (z.re : ℂ) = z := by
          apply Complex.ext <;> simp [him]
        have hreal : ‖z‖ = |z.re| := by
          calc
            ‖z‖ = ‖(z.re : ℂ)‖ := congrArg norm hzReal.symm
            _ = |z.re| := by simp [Real.norm_eq_abs]
        have hzre : z.re < 1 := by
          rw [hreal] at hlarge
          rcases abs_cases z.re with habs | habs <;> rw [habs.1] at hlarge
          · linarith
          · linarith
        obtain ⟨s, hs, hsExp, hnotSum⟩ :=
          exists_signed_expansion_separating_at_large_conjugate hq1 hq2 hlarge
            (Or.inl hzre)
        have hfinite : (Set.range fun n ↦
            (reversedPolynomial s n).eval₂ (algebraMap ℤ ℂ) z).Finite :=
          finite_reversed_tail_range_at_conjugate hqint hno hz hs
            (fun n ↦ reversed_tail_bound_of_signedExpansion hq1 hs hsExp n)
        exact hnotSum (hasSum_zero_of_finite_reversed_tail_range hlarge hs hfinite)
    · obtain ⟨s, hs, hsExp, hnotSum⟩ :=
        exists_signed_expansion_separating_at_large_conjugate hq1 hq2 hlarge
          (Or.inr him)
      have hfinite : (Set.range fun n ↦
          (reversedPolynomial s n).eval₂ (algebraMap ℤ ℂ) z).Finite :=
        finite_reversed_tail_range_at_conjugate hqint hno hz hs
          (fun n ↦ reversed_tail_bound_of_signedExpansion hq1 hs hsExp n)
      exact hnotSum (hasSum_zero_of_finite_reversed_tail_range hlarge hs hfinite)

/-- A concrete interval sufficient for the signed-spectrum accumulation
theorem.  The number-theoretic input is the formalized weak Smyth bound. -/
lemma signedSpectrum_hasAccumulation_below_eleven_tenths {q : ℝ}
    (hq1 : 1 < q) (hqsmall : q < 11 / 10) :
    HasAccumulation (SignedSpectrum q) := by
  by_contra hno
  exact no_pisot_below_eleven_tenths hqsmall
    (isPisot_of_no_signedSpectrum_accumulation hq1 (by linarith) hno)

end Erdos1096
