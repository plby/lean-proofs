import ErdosProblems.Erdos228.CosineConstruction
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic

namespace Erdos228.CosineConstruction

open Set

noncomputable section

/-- Replace each real cosine frequency of a complex polynomial by the
corresponding Chebyshev polynomial. -/
def realPartChebyshevPolynomial (p : Polynomial ℂ) : Polynomial ℝ :=
  ∑ k ∈ p.support,
    Polynomial.C (p.coeff k).re * Polynomial.Chebyshev.T ℝ (k : ℤ)

theorem eval_realPartChebyshevPolynomial_cos
    (p : Polynomial ℂ)
    (hreal : ∀ k ∈ p.support, (p.coeff k).im = 0)
    (x : ℝ) :
    (realPartChebyshevPolynomial p).eval (Real.cos x) =
      (p.eval (Erdos228.unitPoint x)).re := by
  classical
  rw [realPartChebyshevPolynomial, Polynomial.eval_finsetSum,
    Polynomial.eval_eq_sum, Polynomial.sum_def]
  change (∑ k ∈ p.support,
      (Polynomial.C (p.coeff k).re * Polynomial.Chebyshev.T ℝ (k : ℤ)).eval
        (Real.cos x)) =
    Complex.reLm (∑ k ∈ p.support, p.coeff k * Erdos228.unitPoint x ^ k)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.Chebyshev.T_real_cos]
  have hpow := congrArg Complex.re (Erdos228.unitPoint_pow x k)
  have hre : (Erdos228.unitPoint x ^ k).re = Real.cos (k * x) := by
    simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      sub_zero, mul_one, add_zero] using hpow
  change (p.coeff k).re * Real.cos ((k : ℤ) * x) =
    (p.coeff k * Erdos228.unitPoint x ^ k).re
  rw [Complex.mul_re, hreal k hk, zero_mul, sub_zero, hre]
  norm_cast

theorem cosineBlockPolynomial_coeff_im (t k : ℕ) :
    ((cosineBlockPolynomial t).coeff k).im = 0 := by
  classical
  by_cases hk : k ∈ (cosineBlockPolynomial t).support
  · rw [support_cosineBlockPolynomial, mem_evenCPrime] at hk
    rcases hk with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
    · rw [coeff_cosineBlockPolynomial_first t j hj]
      rcases coeff_rudinShapiroP_eq_one_or_neg_one hj with h | h <;> simp [h]
    · rw [coeff_cosineBlockPolynomial_second t j hj]
      rcases coeff_rudinShapiroQ_eq_one_or_neg_one hj with h | h <;> simp [h]
  · have hcoeff : (cosineBlockPolynomial t).coeff k = 0 := by
      simpa [Polynomial.mem_support_iff] using hk
    simp [hcoeff]

/-- The ordinary real polynomial in `cos(2θ)` representing the cosine
block. -/
def evenCosineChebyshevPolynomial (t : ℕ) : Polynomial ℝ :=
  realPartChebyshevPolynomial (cosineBlockPolynomial t)

theorem eval_evenCosineChebyshevPolynomial (t : ℕ) (x : ℝ) :
    (evenCosineChebyshevPolynomial t).eval (Real.cos (2 * x)) =
      evenCosine t x := by
  simpa only [evenCosineChebyshevPolynomial, evenCosine] using
    eval_realPartChebyshevPolynomial_cos (cosineBlockPolynomial t)
      (fun k _ ↦ cosineBlockPolynomial_coeff_im t k) (2 * x)

theorem natDegree_evenCosineChebyshevPolynomial_le (t : ℕ) :
    (evenCosineChebyshevPolynomial t).natDegree ≤ parameterNumerator t := by
  classical
  rw [evenCosineChebyshevPolynomial, realPartChebyshevPolynomial]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  have hk' : k ∈ (cosineBlockPolynomial t).support := by simpa using hk
  have hkBound : k ≤ parameterNumerator t := by
    rw [support_cosineBlockPolynomial, mem_evenCPrime] at hk'
    rcases hk' with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
    · rw [parameterNumerator, ← two_mul_evenT,
        Nat.add_sub_assoc (Nat.one_le_iff_ne_zero.mpr (by positivity))]
      have hjle : j ≤ 2 ^ t - 1 := Nat.le_sub_one_of_lt hj
      omega
    · rw [parameterNumerator, ← two_mul_evenT,
        Nat.add_sub_assoc (Nat.one_le_iff_ne_zero.mpr (by positivity))]
      exact Nat.add_le_add_left (Nat.le_sub_one_of_lt hj) _
  calc
    (Polynomial.C ((cosineBlockPolynomial t).coeff k).re *
        Polynomial.Chebyshev.T ℝ (k : ℤ)).natDegree ≤
        (Polynomial.C ((cosineBlockPolynomial t).coeff k).re).natDegree +
          (Polynomial.Chebyshev.T ℝ (k : ℤ)).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 0 + k := by simp
    _ = k := by omega
    _ ≤ parameterNumerator t := hkBound

private theorem parameterNumerator_eq_topIndex (t : ℕ) :
    parameterNumerator t = 2 * evenT t + (2 ^ t - 1) := by
  rw [parameterNumerator, ← two_mul_evenT,
    Nat.add_sub_assoc (Nat.one_le_iff_ne_zero.mpr (by positivity))]

private theorem topIndex_mem_cosineBlock_support (t : ℕ) :
    parameterNumerator t ∈ (cosineBlockPolynomial t).support := by
  rw [parameterNumerator_eq_topIndex, support_cosineBlockPolynomial,
    mem_evenCPrime]
  right
  exact ⟨2 ^ t - 1, Nat.sub_lt (by positivity) (by norm_num), rfl⟩

theorem natDegree_evenCosineChebyshevPolynomial (t : ℕ) :
    (evenCosineChebyshevPolynomial t).natDegree = parameterNumerator t := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_evenCosineChebyshevPolynomial_le t)
  let m := parameterNumerator t
  have hm : m ∈ (cosineBlockPolynomial t).support :=
    topIndex_mem_cosineBlock_support t
  have hj : 2 ^ t - 1 < 2 ^ t := by
    have : 0 < 2 ^ t := by positivity
    omega
  have htop : ((cosineBlockPolynomial t).coeff m).re ≠ 0 := by
    rw [show m = 2 * evenT t + (2 ^ t - 1) from parameterNumerator_eq_topIndex t]
    rw [coeff_cosineBlockPolynomial_second t (2 ^ t - 1) hj]
    rcases coeff_rudinShapiroQ_eq_one_or_neg_one hj with h | h <;> simp [h]
  have hTtop : (Polynomial.Chebyshev.T ℝ (m : ℤ)).coeff m ≠ 0 := by
    have hdeg : (Polynomial.Chebyshev.T ℝ (m : ℤ)).natDegree = m := by simp
    have hc := Polynomial.coeff_natDegree
      (p := Polynomial.Chebyshev.T ℝ (m : ℤ))
    rw [hdeg] at hc
    rw [hc, Polynomial.Chebyshev.leadingCoeff_T]
    positivity
  change (evenCosineChebyshevPolynomial t).coeff m ≠ 0
  rw [evenCosineChebyshevPolynomial, realPartChebyshevPolynomial,
    Polynomial.finsetSum_coeff, Finset.sum_eq_single m]
  · rw [Polynomial.coeff_C_mul]
    exact mul_ne_zero htop hTtop
  · intro k hk hkm
    have hkBound : k ≤ m := by
      rw [support_cosineBlockPolynomial, mem_evenCPrime] at hk
      rcases hk with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
      · rw [show m = 2 * evenT t + (2 ^ t - 1) from parameterNumerator_eq_topIndex t]
        have hjle := Nat.le_sub_one_of_lt hj
        omega
      · rw [show m = 2 * evenT t + (2 ^ t - 1) from parameterNumerator_eq_topIndex t]
        exact Nat.add_le_add_left (Nat.le_sub_one_of_lt hj) _
    have hklt : k < m := lt_of_le_of_ne hkBound hkm
    have hTzero : (Polynomial.Chebyshev.T ℝ (k : ℤ)).coeff m = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by simpa using hklt)
    rw [Polynomial.coeff_C_mul, hTzero, mul_zero]
  · intro hnot
    exact (hnot hm).elim

theorem evenCosineChebyshevPolynomial_sub_C_ne_zero (t : ℕ) (c : ℝ) :
    evenCosineChebyshevPolynomial t - Polynomial.C c ≠ 0 := by
  intro hzero
  have hconst : evenCosineChebyshevPolynomial t = Polynomial.C c :=
    sub_eq_zero.mp hzero
  have hdeg := natDegree_evenCosineChebyshevPolynomial t
  rw [hconst] at hdeg
  have hmpos : 0 < parameterNumerator t := by
    rw [parameterNumerator_eq_topIndex]
    have hT : 0 < evenT t := by simp [evenT]
    omega
  simp at hdeg
  omega

/-!
This scratch file isolates the topological/combinatorial half of the root
count for the first-quadrant bad runs.  A bad run has a strict sublevel
witness.  Its two ends are weakly above the level (using maximality, or the
two quadrant endpoints), so continuity gives two distinct level contacts.
The contact pairs belonging to distinct maximal runs are disjoint and
ordered.  Consequently any finite set containing all first-quadrant contacts
has at least twice as many elements as there are runs.
-/

theorem continuous_evenCosine (t : ℕ) : Continuous (evenCosine t) := by
  unfold evenCosine Erdos228.unitPoint
  fun_prop

private abbrev FirstQuadrantRun (n t : ℕ) (gamma : ℝ) :=
  ↑(firstQuadrantRuns n t gamma)

private noncomputable def runBadWitness {n t : ℕ} {gamma : ℝ}
    (I : FirstQuadrantRun n t gamma) : ℝ :=
  Classical.choose (show BadCell n t gamma I.1.1 by
    have hI := (mem_firstQuadrantRuns.mp I.2).1
    rw [mem_dangerousRuns] at hI
    exact hI.2.2.1 I.1.1 (Finset.mem_range.mpr (hI.1.trans_lt hI.2.1))
      le_rfl hI.1)

private theorem runBadWitness_mem {n t : ℕ} {gamma : ℝ}
    (I : FirstQuadrantRun n t gamma) :
    runBadWitness I ∈ Erdos228.Intervals.gridCell n I.1.1 := by
  exact (Classical.choose_spec (show BadCell n t gamma I.1.1 by
    have hI := (mem_firstQuadrantRuns.mp I.2).1
    rw [mem_dangerousRuns] at hI
    exact hI.2.2.1 I.1.1 (Finset.mem_range.mpr (hI.1.trans_lt hI.2.1))
      le_rfl hI.1)).1

private theorem runBadWitness_lt {n t : ℕ} {gamma : ℝ}
    (I : FirstQuadrantRun n t gamma) :
    |evenCosine t (runBadWitness I)| < cosineThreshold n gamma := by
  exact (Classical.choose_spec (show BadCell n t gamma I.1.1 by
    have hI := (mem_firstQuadrantRuns.mp I.2).1
    rw [mem_dangerousRuns] at hI
    exact hI.2.2.1 I.1.1 (Finset.mem_range.mpr (hI.1.trans_lt hI.2.1))
      le_rfl hI.1)).2

private theorem left_endpoint_ge {n t : ℕ} {gamma : ℝ}
    (hzero : cosineThreshold n gamma ≤ |evenCosine t 0|)
    (I : FirstQuadrantRun n t gamma) :
    cosineThreshold n gamma ≤
      |evenCosine t (Erdos228.Intervals.gridPoint n I.1.1)| := by
  have hI := (mem_firstQuadrantRuns.mp I.2).1
  rw [mem_dangerousRuns] at hI
  have hn : 0 < n := by
    have hb : I.1.2 < 2 * n := hI.2.1
    exact Nat.pos_of_ne_zero (fun hn0 ↦ by simpa [hn0] using hb)
  by_cases ha : I.1.1 = 0
  · simpa [ha, Erdos228.Intervals.gridPoint_zero] using hzero
  · have hgood : ¬BadCell n t gamma (I.1.1 - 1) :=
      hI.2.2.2.1.resolve_left ha
    by_contra hlt
    rw [not_le] at hlt
    apply hgood
    refine ⟨Erdos228.Intervals.gridPoint n I.1.1, ?_, hlt⟩
    simp only [Erdos228.Intervals.gridCell, mem_Icc]
    constructor
    · exact (Erdos228.Intervals.gridPoint_mono (by omega)) (Nat.sub_le _ _)
    · rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr ha)]

private theorem right_endpoint_ge {n t : ℕ} {gamma : ℝ}
    (hn : 0 < n)
    (hhalf : cosineThreshold n gamma ≤ |evenCosine t (Real.pi / 2)|)
    (I : FirstQuadrantRun n t gamma) :
    cosineThreshold n gamma ≤
      |evenCosine t (Erdos228.Intervals.gridPoint n (I.1.2 + 1))| := by
  have hmem := mem_firstQuadrantRuns.mp I.2
  have hI := hmem.1
  rw [mem_dangerousRuns] at hI
  by_cases heq : 2 * (I.1.2 + 1) = n
  · have hnEven : (n : ℝ) = 2 * (I.1.2 + 1 : ℕ) := by exact_mod_cast heq.symm
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have harg : Erdos228.Intervals.gridPoint n (I.1.2 + 1) = Real.pi / 2 := by
      rw [Erdos228.Intervals.gridPoint, div_eq_iff hnR]
      rw [hnEven]
      ring
    rwa [harg]
  · have hstrict : 2 * (I.1.2 + 1) < n := lt_of_le_of_ne hmem.2 heq
    have hnotlast : I.1.2 + 1 ≠ 2 * n := by omega
    have hgood : ¬BadCell n t gamma (I.1.2 + 1) :=
      hI.2.2.2.2.resolve_left hnotlast
    by_contra hlt
    rw [not_le] at hlt
    apply hgood
    refine ⟨Erdos228.Intervals.gridPoint n (I.1.2 + 1), ?_, hlt⟩
    simp only [Erdos228.Intervals.gridCell, mem_Icc]
    exact ⟨le_rfl, (Erdos228.Intervals.gridPoint_mono hn) (by omega)⟩

private theorem exists_left_contact {n t : ℕ} {gamma : ℝ}
    (hn : 0 < n)
    (hzero : cosineThreshold n gamma ≤ |evenCosine t 0|)
    (I : FirstQuadrantRun n t gamma) :
    ∃ x ∈ Icc (Erdos228.Intervals.gridPoint n I.1.1) (runBadWitness I),
      |evenCosine t x| = cosineThreshold n gamma := by
  apply Erdos228.Intervals.exists_abs_level_between (continuous_evenCosine t)
  · exact (runBadWitness_mem I).1
  · exact Or.inr ⟨runBadWitness_lt I, left_endpoint_ge hzero I⟩

private theorem exists_right_contact {n t : ℕ} {gamma : ℝ}
    (hn : 0 < n)
    (hhalf : cosineThreshold n gamma ≤ |evenCosine t (Real.pi / 2)|)
    (I : FirstQuadrantRun n t gamma) :
    ∃ x ∈ Icc (runBadWitness I)
        (Erdos228.Intervals.gridPoint n (I.1.2 + 1)),
      |evenCosine t x| = cosineThreshold n gamma := by
  apply Erdos228.Intervals.exists_abs_level_between (continuous_evenCosine t)
  · have hw := (runBadWitness_mem I).2
    have hI := (mem_firstQuadrantRuns.mp I.2).1
    rw [mem_dangerousRuns] at hI
    exact hw.trans ((Erdos228.Intervals.gridPoint_mono hn)
      (Nat.add_le_add_right hI.1 1))
  · exact Or.inl ⟨runBadWitness_lt I, right_endpoint_ge hn hhalf I⟩

private noncomputable def leftContact {n t : ℕ} {gamma : ℝ}
    (hn : 0 < n)
    (hzero : cosineThreshold n gamma ≤ |evenCosine t 0|)
    (I : FirstQuadrantRun n t gamma) : ℝ :=
  Classical.choose (exists_left_contact hn hzero I)

private noncomputable def rightContact {n t : ℕ} {gamma : ℝ}
    (hn : 0 < n)
    (hhalf : cosineThreshold n gamma ≤ |evenCosine t (Real.pi / 2)|)
    (I : FirstQuadrantRun n t gamma) : ℝ :=
  Classical.choose (exists_right_contact hn hhalf I)

private theorem leftContact_spec {n t : ℕ} {gamma : ℝ}
    (hn : 0 < n)
    (hzero : cosineThreshold n gamma ≤ |evenCosine t 0|)
    (I : FirstQuadrantRun n t gamma) :
    leftContact hn hzero I ∈
        Icc (Erdos228.Intervals.gridPoint n I.1.1) (runBadWitness I) ∧
      |evenCosine t (leftContact hn hzero I)| = cosineThreshold n gamma :=
  Classical.choose_spec (exists_left_contact hn hzero I)

private theorem rightContact_spec {n t : ℕ} {gamma : ℝ}
    (hn : 0 < n)
    (hhalf : cosineThreshold n gamma ≤ |evenCosine t (Real.pi / 2)|)
    (I : FirstQuadrantRun n t gamma) :
    rightContact hn hhalf I ∈
        Icc (runBadWitness I) (Erdos228.Intervals.gridPoint n (I.1.2 + 1)) ∧
      |evenCosine t (rightContact hn hhalf I)| = cosineThreshold n gamma :=
  Classical.choose_spec (exists_right_contact hn hhalf I)

private theorem leftContact_lt_witness {n t : ℕ} {gamma : ℝ}
    (hn : 0 < n)
    (hzero : cosineThreshold n gamma ≤ |evenCosine t 0|)
    (I : FirstQuadrantRun n t gamma) :
    leftContact hn hzero I < runBadWitness I := by
  have hs := leftContact_spec hn hzero I
  refine hs.1.2.lt_of_ne ?_
  intro heq
  have hv := hs.2
  rw [heq] at hv
  exact (runBadWitness_lt I).ne hv

private theorem witness_lt_rightContact {n t : ℕ} {gamma : ℝ}
    (hn : 0 < n)
    (hhalf : cosineThreshold n gamma ≤ |evenCosine t (Real.pi / 2)|)
    (I : FirstQuadrantRun n t gamma) :
    runBadWitness I < rightContact hn hhalf I := by
  have hs := rightContact_spec hn hhalf I
  refine hs.1.1.lt_of_ne ?_
  intro heq
  have hv := hs.2
  rw [← heq] at hv
  exact (runBadWitness_lt I).ne hv

private noncomputable def pairedContact {n t : ℕ} {gamma : ℝ}
    (hn : 0 < n)
    (hzero : cosineThreshold n gamma ≤ |evenCosine t 0|)
    (hhalf : cosineThreshold n gamma ≤ |evenCosine t (Real.pi / 2)|) :
    FirstQuadrantRun n t gamma × Fin 2 → ℝ
  | (I, k) => if (k : ℕ) = 0 then leftContact hn hzero I else rightContact hn hhalf I

private theorem pairedContact_bounds {n t : ℕ} {gamma : ℝ}
    (hn : 0 < n)
    (hzero : cosineThreshold n gamma ≤ |evenCosine t 0|)
    (hhalf : cosineThreshold n gamma ≤ |evenCosine t (Real.pi / 2)|)
    (K : FirstQuadrantRun n t gamma) (k : Fin 2) :
    Erdos228.Intervals.gridPoint n K.1.1 ≤ pairedContact hn hzero hhalf (K, k) ∧
    pairedContact hn hzero hhalf (K, k) ≤
      Erdos228.Intervals.gridPoint n (K.1.2 + 1) := by
  by_cases hk : (k : ℕ) = 0
  · simp only [pairedContact, if_pos hk]
    refine ⟨(leftContact_spec hn hzero K).1.1, ?_⟩
    have hrun := mem_dangerousRuns.mp (mem_firstQuadrantRuns.mp K.2).1
    exact (leftContact_spec hn hzero K).1.2.trans <|
      (runBadWitness_mem K).2.trans <|
        (Erdos228.Intervals.gridPoint_mono hn) (Nat.add_le_add_right hrun.1 1)
  · simp only [pairedContact, if_neg hk]
    have hleft := (runBadWitness_mem K).1
    exact ⟨hleft.trans (rightContact_spec hn hhalf K).1.1,
      (rightContact_spec hn hhalf K).1.2⟩

private theorem pairedContact_level {n t : ℕ} {gamma : ℝ}
    (hn : 0 < n)
    (hzero : cosineThreshold n gamma ≤ |evenCosine t 0|)
    (hhalf : cosineThreshold n gamma ≤ |evenCosine t (Real.pi / 2)|)
    (K : FirstQuadrantRun n t gamma) (k : Fin 2) :
    |evenCosine t (pairedContact hn hzero hhalf (K, k))| =
      cosineThreshold n gamma := by
  by_cases hk : (k : ℕ) = 0
  · simpa only [pairedContact, if_pos hk] using (leftContact_spec hn hzero K).2
  · simpa only [pairedContact, if_neg hk] using (rightContact_spec hn hhalf K).2

private theorem pairedContact_injective {n t : ℕ} {gamma : ℝ}
    (hn : 0 < n)
    (hzero : cosineThreshold n gamma ≤ |evenCosine t 0|)
    (hhalf : cosineThreshold n gamma ≤ |evenCosine t (Real.pi / 2)|) :
    Function.Injective (pairedContact hn hzero hhalf) := by
  rintro ⟨I, i⟩ ⟨J, j⟩ hij
  have contact_bounds (K : FirstQuadrantRun n t gamma) (k : Fin 2) :
      Erdos228.Intervals.gridPoint n K.1.1 ≤ pairedContact hn hzero hhalf (K, k) ∧
      pairedContact hn hzero hhalf (K, k) ≤
        Erdos228.Intervals.gridPoint n (K.1.2 + 1) := by
    by_cases hk : (k : ℕ) = 0
    · simp only [pairedContact, if_pos hk]
      have hspec := leftContact_spec hn hzero K
      refine ⟨hspec.1.1, ?_⟩
      have hrun := mem_dangerousRuns.mp (mem_firstQuadrantRuns.mp K.2).1
      exact (leftContact_spec hn hzero K).1.2.trans <|
        (runBadWitness_mem K).2.trans <|
          (Erdos228.Intervals.gridPoint_mono hn) (Nat.add_le_add_right hrun.1 1)
    · simp only [pairedContact, if_neg hk]
      exact ⟨(runBadWitness_mem K).1.trans (rightContact_spec hn hhalf K).1.1,
        (rightContact_spec hn hhalf K).1.2⟩
  have hIJ : I = J := by
    apply Subtype.ext
    rcases lt_trichotomy I.1.1 J.1.1 with hlt | heq | hgt
    · have hI := (mem_firstQuadrantRuns.mp I.2).1
      have hJ := (mem_firstQuadrantRuns.mp J.2).1
      have hbc : I.1.2 < J.1.1 := by
        by_contra hnot
        have hmaxI := (mem_dangerousRuns.mp hI)
        have hmaxJ := (mem_dangerousRuns.mp hJ)
        have hJpos : 0 < J.1.1 := by omega
        have hpred : J.1.1 - 1 ≥ I.1.1 := by omega
        have hpred_le : J.1.1 - 1 ≤ I.1.2 := by omega
        have hbad := hmaxI.2.2.1 (J.1.1 - 1)
          (Finset.mem_range.mpr (hpred_le.trans_lt hmaxI.2.1)) hpred hpred_le
        exact hmaxJ.2.2.2.1.resolve_left (Nat.ne_of_gt hJpos) hbad
      have hsep := dangerousRuns_separated hI hJ hbc
      have hidx : I.1.2 + 1 < J.1.1 := by
        calc
          I.1.2 + 1 < (I.1.2 + 1) + 1 := Nat.lt_succ_self _
          _ ≤ J.1.1 := by simpa [Nat.add_assoc] using hsep
      have hgrid : Erdos228.Intervals.gridPoint n (I.1.2 + 1) <
          Erdos228.Intervals.gridPoint n J.1.1 :=
        Erdos228.Intervals.gridPoint_strictMono hn hidx
      have hi := pairedContact_bounds hn hzero hhalf I i
      have hj := pairedContact_bounds hn hzero hhalf J j
      rw [hij] at hi
      linarith
    · have hmaxI := mem_dangerousRuns.mp (mem_firstQuadrantRuns.mp I.2).1
      have hmaxJ := mem_dangerousRuns.mp (mem_firstQuadrantRuns.mp J.2).1
      exact Erdos228.Intervals.IsMaximalBadRun.eq_of_start_eq hmaxI hmaxJ heq
    · have hI := (mem_firstQuadrantRuns.mp I.2).1
      have hJ := (mem_firstQuadrantRuns.mp J.2).1
      have hdc : J.1.2 < I.1.1 := by
        by_contra hnot
        have hmaxI := (mem_dangerousRuns.mp hI)
        have hmaxJ := (mem_dangerousRuns.mp hJ)
        have hIpos : 0 < I.1.1 := by omega
        have hpred : I.1.1 - 1 ≥ J.1.1 := by omega
        have hpred_le : I.1.1 - 1 ≤ J.1.2 := by omega
        have hbad := hmaxJ.2.2.1 (I.1.1 - 1)
          (Finset.mem_range.mpr (hpred_le.trans_lt hmaxJ.2.1)) hpred hpred_le
        exact hmaxI.2.2.2.1.resolve_left (Nat.ne_of_gt hIpos) hbad
      have hsep := dangerousRuns_separated hJ hI hdc
      have hidx : J.1.2 + 1 < I.1.1 := by
        calc
          J.1.2 + 1 < (J.1.2 + 1) + 1 := Nat.lt_succ_self _
          _ ≤ I.1.1 := by simpa [Nat.add_assoc] using hsep
      have hgrid : Erdos228.Intervals.gridPoint n (J.1.2 + 1) <
          Erdos228.Intervals.gridPoint n I.1.1 :=
        Erdos228.Intervals.gridPoint_strictMono hn hidx
      have hi := pairedContact_bounds hn hzero hhalf I i
      have hj := pairedContact_bounds hn hzero hhalf J j
      rw [hij] at hi
      linarith
  subst J
  congr 1
  by_contra hne
  have hfin : ((i : ℕ) = 0 ∧ (j : ℕ) ≠ 0) ∨
      ((i : ℕ) ≠ 0 ∧ (j : ℕ) = 0) := by
    omega
  rcases hfin with ⟨hi, hj⟩ | ⟨hi, hj⟩
  · simp only [pairedContact, if_pos hi, if_neg hj] at hij
    exact (leftContact_lt_witness hn hzero I).trans
      (witness_lt_rightContact hn hhalf I) |>.ne hij
  · simp only [pairedContact, if_neg hi, if_pos hj] at hij
    exact (leftContact_lt_witness hn hzero I).trans
      (witness_lt_rightContact hn hhalf I) |>.ne hij.symm

/-- Every first-quadrant maximal bad run supplies two distinct contacts.
Therefore any finite set containing all such contacts has cardinality at
least twice the number of runs. -/
theorem two_mul_card_firstQuadrantRuns_le_card_contacts
    {n t : ℕ} {gamma : ℝ}
    (hn : 0 < n)
    (hzero : cosineThreshold n gamma ≤ |evenCosine t 0|)
    (hhalf : cosineThreshold n gamma ≤ |evenCosine t (Real.pi / 2)|)
    (contacts : Finset ℝ)
    (hcontacts : ∀ x, 0 ≤ x → x ≤ Real.pi / 2 →
      |evenCosine t x| = cosineThreshold n gamma → x ∈ contacts) :
    2 * (firstQuadrantRuns n t gamma).card ≤ contacts.card := by
  let f : FirstQuadrantRun n t gamma × Fin 2 → ↑contacts := fun p ↦
    ⟨pairedContact hn hzero hhalf p, by
      apply hcontacts
      · exact (show 0 ≤ Erdos228.Intervals.gridPoint n p.1.1.1 by
          exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) Real.pi_pos.le)
            (Nat.cast_nonneg _)).trans
          (pairedContact_bounds hn hzero hhalf p.1 p.2).1
      · have hp := (mem_firstQuadrantRuns.mp p.1.2).2
        have hnR : (0 : ℝ) < n := by exact_mod_cast hn
        have hcast : (2 : ℝ) * ((p.1.1.2 + 1 : ℕ) : ℝ) ≤ n := by
          exact_mod_cast hp
        apply (pairedContact_bounds hn hzero hhalf p.1 p.2).2.trans
        simp only [Erdos228.Intervals.gridPoint]
        apply (div_le_iff₀ hnR).2
        nlinarith [Real.pi_pos]
      · exact pairedContact_level hn hzero hhalf p.1 p.2
      ⟩
  have hf : Function.Injective f := fun p q hpq ↦
    pairedContact_injective hn hzero hhalf (Subtype.ext_iff.mp hpq)
  have hcard := Fintype.card_le_of_injective f hf
  simpa [Fintype.card_prod, mul_comm] using hcard

private noncomputable def polynomialAbsoluteLevelRoots
    (q : Polynomial ℝ) (level : ℝ) : Finset ℝ :=
  (q - Polynomial.C level).roots.toFinset ∪
    (q - Polynomial.C (-level)).roots.toFinset

private theorem card_polynomialAbsoluteLevelRoots_le
    (q : Polynomial ℝ) (level : ℝ) :
    (polynomialAbsoluteLevelRoots q level).card ≤ 2 * q.natDegree := by
  have hplus : (q - Polynomial.C level).roots.toFinset.card ≤ q.natDegree :=
    (Multiset.toFinset_card_le _).trans <|
      (Polynomial.card_roots' _).trans <|
        (Polynomial.natDegree_sub_le _ _).trans <| by
          simp only [max_le_iff]
          exact ⟨le_rfl, by simp⟩
  have hminus : (q - Polynomial.C (-level)).roots.toFinset.card ≤ q.natDegree :=
    (Multiset.toFinset_card_le _).trans <|
      (Polynomial.card_roots' _).trans <|
        (Polynomial.natDegree_sub_le _ _).trans <| by
          simp only [max_le_iff]
          exact ⟨le_rfl, by simp⟩
  calc
    (polynomialAbsoluteLevelRoots q level).card ≤
        (q - Polynomial.C level).roots.toFinset.card +
          (q - Polynomial.C (-level)).roots.toFinset.card :=
      Finset.card_union_le _ _
    _ ≤ q.natDegree + q.natDegree := Nat.add_le_add hplus hminus
    _ = 2 * q.natDegree := by omega

private theorem eval_mem_polynomialAbsoluteLevelRoots
    {q : Polynomial ℝ} {level x : ℝ}
    (hlevel : 0 ≤ level)
    (hplus : q - Polynomial.C level ≠ 0)
    (hminus : q - Polynomial.C (-level) ≠ 0)
    (hx : |q.eval x| = level) :
    x ∈ polynomialAbsoluteLevelRoots q level := by
  rw [abs_eq hlevel] at hx
  rw [polynomialAbsoluteLevelRoots, Finset.mem_union]
  rcases hx with hx | hx
  · left
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hplus, Polynomial.IsRoot.def]
    simp [hx]
  · right
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hminus, Polynomial.IsRoot.def]
    simp [hx]

/-- Polynomial form of the root count.  If `evenCosine t` is represented as
`q(cos(2θ))`, then injectivity of cosine on `[0,π]` sends the two contacts
of every first-quadrant run to distinct roots of `q ± threshold`. -/
theorem card_firstQuadrantRuns_le_polynomial_degree
    {n t : ℕ} {gamma : ℝ}
    (hn : 0 < n)
    (hlevel : 0 ≤ cosineThreshold n gamma)
    (hzero : cosineThreshold n gamma ≤ |evenCosine t 0|)
    (hhalf : cosineThreshold n gamma ≤ |evenCosine t (Real.pi / 2)|)
    (q : Polynomial ℝ)
    (hq : ∀ x, q.eval (Real.cos (2 * x)) = evenCosine t x)
    (hplus : q - Polynomial.C (cosineThreshold n gamma) ≠ 0)
    (hminus : q - Polynomial.C (-cosineThreshold n gamma) ≠ 0) :
    (firstQuadrantRuns n t gamma).card ≤ q.natDegree := by
  let roots := polynomialAbsoluteLevelRoots q (cosineThreshold n gamma)
  let f : FirstQuadrantRun n t gamma × Fin 2 → ↑roots := fun p ↦
    ⟨Real.cos (2 * pairedContact hn hzero hhalf p), by
      apply eval_mem_polynomialAbsoluteLevelRoots hlevel hplus hminus
      rw [hq]
      exact pairedContact_level hn hzero hhalf p.1 p.2⟩
  have hcos_inj : Set.InjOn (fun x : ℝ ↦ Real.cos (2 * x))
      (Icc 0 (Real.pi / 2)) := by
    intro x hx y hy hxy
    have h2x : 2 * x ∈ Icc (0 : ℝ) Real.pi := by
      constructor
      · exact mul_nonneg (by norm_num) hx.1
      · calc
          2 * x ≤ 2 * (Real.pi / 2) := mul_le_mul_of_nonneg_left hx.2 (by norm_num)
          _ = Real.pi := by ring
    have h2y : 2 * y ∈ Icc (0 : ℝ) Real.pi := by
      constructor
      · exact mul_nonneg (by norm_num) hy.1
      · calc
          2 * y ≤ 2 * (Real.pi / 2) := mul_le_mul_of_nonneg_left hy.2 (by norm_num)
          _ = Real.pi := by ring
    have := Real.injOn_cos h2x h2y hxy
    linarith
  have hf : Function.Injective f := by
    intro p r hpr
    apply pairedContact_injective hn hzero hhalf
    apply hcos_inj
    · constructor
      · exact (show 0 ≤ Erdos228.Intervals.gridPoint n p.1.1.1 by
          exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) Real.pi_pos.le)
            (Nat.cast_nonneg _)).trans
          (pairedContact_bounds hn hzero hhalf p.1 p.2).1
      · have hp := (mem_firstQuadrantRuns.mp p.1.2).2
        have hnR : (0 : ℝ) < n := by exact_mod_cast hn
        have hcast : (2 : ℝ) * ((p.1.1.2 + 1 : ℕ) : ℝ) ≤ n := by
          exact_mod_cast hp
        apply (pairedContact_bounds hn hzero hhalf p.1 p.2).2.trans
        simp only [Erdos228.Intervals.gridPoint]
        apply (div_le_iff₀ hnR).2
        nlinarith [Real.pi_pos]
    · constructor
      · exact (show 0 ≤ Erdos228.Intervals.gridPoint n r.1.1.1 by
          exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) Real.pi_pos.le)
            (Nat.cast_nonneg _)).trans
          (pairedContact_bounds hn hzero hhalf r.1 r.2).1
      · have hr := (mem_firstQuadrantRuns.mp r.1.2).2
        have hnR : (0 : ℝ) < n := by exact_mod_cast hn
        have hcast : (2 : ℝ) * ((r.1.1.2 + 1 : ℕ) : ℝ) ≤ n := by
          exact_mod_cast hr
        apply (pairedContact_bounds hn hzero hhalf r.1 r.2).2.trans
        simp only [Erdos228.Intervals.gridPoint]
        apply (div_le_iff₀ hnR).2
        nlinarith [Real.pi_pos]
    · exact Subtype.ext_iff.mp hpr
  have hcard := Fintype.card_le_of_injective f hf
  have hrootcard : roots.card ≤ 2 * q.natDegree :=
    card_polynomialAbsoluteLevelRoots_le q (cosineThreshold n gamma)
  have htwice : 2 * (firstQuadrantRuns n t gamma).card ≤ 2 * q.natDegree := by
    calc
      2 * (firstQuadrantRuns n t gamma).card = Fintype.card (FirstQuadrantRun n t gamma × Fin 2) := by
        simp [Fintype.card_prod, mul_comm]
      _ ≤ Fintype.card ↑roots := hcard
      _ = roots.card := Fintype.card_coe _
      _ ≤ 2 * q.natDegree := hrootcard
  omega

/-- The exact numerical consequence needed by the cosine construction once
its Chebyshev polynomial is supplied. -/
theorem card_firstQuadrantRuns_le_parameterNumerator_of_polynomial
    {n t : ℕ} {gamma : ℝ}
    (hn : 0 < n)
    (hlevel : 0 ≤ cosineThreshold n gamma)
    (hzero : cosineThreshold n gamma ≤ |evenCosine t 0|)
    (hhalf : cosineThreshold n gamma ≤ |evenCosine t (Real.pi / 2)|)
    (q : Polynomial ℝ)
    (hq : ∀ x, q.eval (Real.cos (2 * x)) = evenCosine t x)
    (hplus : q - Polynomial.C (cosineThreshold n gamma) ≠ 0)
    (hminus : q - Polynomial.C (-cosineThreshold n gamma) ≠ 0)
    (hdegree : q.natDegree ≤ parameterNumerator t) :
    (firstQuadrantRuns n t gamma).card ≤ parameterNumerator t :=
  (card_firstQuadrantRuns_le_polynomial_degree hn hlevel hzero hhalf q hq hplus hminus).trans
    hdegree

/-- The finite-contact/root-count conclusion specialized to the actual
Rudin--Shapiro cosine block. -/
theorem card_firstQuadrantRuns_le_parameterNumerator
    {n t : ℕ} {gamma : ℝ}
    (hn : 0 < n)
    (hlevel : 0 ≤ cosineThreshold n gamma)
    (hzero : cosineThreshold n gamma ≤ |evenCosine t 0|)
    (hhalf : cosineThreshold n gamma ≤ |evenCosine t (Real.pi / 2)|) :
    (firstQuadrantRuns n t gamma).card ≤ parameterNumerator t := by
  apply card_firstQuadrantRuns_le_parameterNumerator_of_polynomial
    hn hlevel hzero hhalf (evenCosineChebyshevPolynomial t)
  · exact eval_evenCosineChebyshevPolynomial t
  · exact evenCosineChebyshevPolynomial_sub_C_ne_zero t _
  · exact evenCosineChebyshevPolynomial_sub_C_ne_zero t _
  · exact natDegree_evenCosineChebyshevPolynomial_le t

private theorem rudinShapiro_eval_one_oddIndex (k : ℕ) :
    (rudinShapiroP (2 * k + 1)).eval 1 = (2 ^ (k + 1) : ℂ) ∧
      (rudinShapiroQ (2 * k + 1)).eval 1 = 0 := by
  induction k with
  | zero => norm_num [eval_rudinShapiroP_succ, eval_rudinShapiroQ_succ]
  | succ k ih =>
      have hPnext :
          (rudinShapiroP ((2 * k + 1) + 1)).eval 1 = (2 ^ (k + 1) : ℂ) := by
        rw [eval_rudinShapiroP_succ, ih.1, ih.2]
        simp
      have hQnext :
          (rudinShapiroQ ((2 * k + 1) + 1)).eval 1 = (2 ^ (k + 1) : ℂ) := by
        rw [eval_rudinShapiroQ_succ, ih.1, ih.2]
        simp
      rw [show 2 * (k + 1) + 1 = ((2 * k + 1) + 1) + 1 by omega]
      constructor
      · calc
          (rudinShapiroP (((2 * k + 1) + 1) + 1)).eval 1 =
              (rudinShapiroP ((2 * k + 1) + 1)).eval 1 +
                1 ^ (2 ^ ((2 * k + 1) + 1)) *
                  (rudinShapiroQ ((2 * k + 1) + 1)).eval 1 :=
            eval_rudinShapiroP_succ _ _
          _ = (2 ^ (k + 1 + 1) : ℂ) := by
            rw [hPnext, hQnext]
            push_cast
            simp [pow_succ]
            ring
      · calc
          (rudinShapiroQ (((2 * k + 1) + 1) + 1)).eval 1 =
              (rudinShapiroP ((2 * k + 1) + 1)).eval 1 -
                1 ^ (2 ^ ((2 * k + 1) + 1)) *
                  (rudinShapiroQ ((2 * k + 1) + 1)).eval 1 :=
            eval_rudinShapiroQ_succ _ _
          _ = 0 := by rw [hPnext, hQnext]; ring

private theorem rudinShapiro_eval_neg_one_oddIndex (k : ℕ) :
    (rudinShapiroP (2 * k + 1)).eval (-1) = 0 ∧
      (rudinShapiroQ (2 * k + 1)).eval (-1) = (2 ^ (k + 1) : ℂ) := by
  induction k with
  | zero => norm_num [eval_rudinShapiroP_succ, eval_rudinShapiroQ_succ]
  | succ k ih =>
      have heven₁ : Even (2 ^ (2 * k + 1)) := by
        refine ⟨2 ^ (2 * k), ?_⟩
        simp [pow_succ, two_mul]
        ring
      have heven₂ : Even (2 ^ ((2 * k + 1) + 1)) := by
        refine ⟨2 ^ (2 * k + 1), ?_⟩
        simp [pow_succ, two_mul]
        ring
      have hPnext :
          (rudinShapiroP ((2 * k + 1) + 1)).eval (-1) = (2 ^ (k + 1) : ℂ) := by
        rw [eval_rudinShapiroP_succ, heven₁.neg_one_pow, ih.1, ih.2]
        ring
      have hQnext :
          (rudinShapiroQ ((2 * k + 1) + 1)).eval (-1) = -(2 ^ (k + 1) : ℂ) := by
        rw [eval_rudinShapiroQ_succ, heven₁.neg_one_pow, ih.1, ih.2]
        ring
      rw [show 2 * (k + 1) + 1 = ((2 * k + 1) + 1) + 1 by omega]
      constructor
      · calc
          (rudinShapiroP (((2 * k + 1) + 1) + 1)).eval (-1) =
              (rudinShapiroP ((2 * k + 1) + 1)).eval (-1) +
                (-1) ^ (2 ^ ((2 * k + 1) + 1)) *
                  (rudinShapiroQ ((2 * k + 1) + 1)).eval (-1) :=
            eval_rudinShapiroP_succ _ _
          _ = 0 := by rw [heven₂.neg_one_pow, hPnext, hQnext]; ring
      · calc
          (rudinShapiroQ (((2 * k + 1) + 1) + 1)).eval (-1) =
              (rudinShapiroP ((2 * k + 1) + 1)).eval (-1) -
                (-1) ^ (2 ^ ((2 * k + 1) + 1)) *
                  (rudinShapiroQ ((2 * k + 1) + 1)).eval (-1) :=
            eval_rudinShapiroQ_succ _ _
          _ = (2 ^ (k + 1 + 1) : ℂ) := by
            rw [heven₂.neg_one_pow, hPnext, hQnext]
            push_cast
            simp [pow_succ]
            ring

end

end Erdos228.CosineConstruction
