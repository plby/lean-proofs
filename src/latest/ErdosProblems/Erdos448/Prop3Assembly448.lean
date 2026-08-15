import ErdosProblems.Erdos448.Basic
import ErdosProblems.Erdos448.Prop2Scale448
import ErdosProblems.Erdos448.Prop3ShiftedMean448
import ErdosProblems.Erdos448.FirstShiftedSmall448
import ErdosProblems.Erdos448.Prop3ClosePair448
import ErdosProblems.Erdos448.Prop3CutoffShell448
import ErdosProblems.Erdos448.Prop3W2Close448
import ErdosProblems.Erdos448.NaturalGridConcentration448
import ErdosProblems.Erdos448.Prop4Summation448

open scoped BigOperators
open Finset

namespace Erdos448Prop3Assembly

/-- Positive integers strictly below `x`. -/
def positiveBelow (x : ℕ) : Finset ℕ := Finset.Ico 1 x

/-- Largest reduced dyadic scale compatible with a product below `x`.
The subtraction converts the strict bound `< x` to a power bound by
`x - 1`. -/
def sqrtScaleCutoff (x : ℕ) : ℕ := Nat.log 2 (x - 1) / 2

/-- Arithmetic core of the square-root scale cutoff.  If the first reduced
factor is in the `k`th half-open dyadic block and is the smaller of the two
reduced factors, then divisibility into `n < x` forces
`k ≤ floor(log₂(x-1)/2)`. -/
lemma reducedScale_le_sqrtScaleCutoff
    {x n d d' t k : ℕ} (hnPos : 0 < n) (hnLt : n < x)
    (htPos : 0 < t) (hprod : d * d' * t ∣ n)
    (hdLower : 2 ^ k ≤ d) (hdd' : d < d') :
    k ≤ sqrtScaleCutoff x := by
  have hbaseProd : 2 ^ (2 * k) ≤ d * d' := by
    rw [two_mul, pow_add]
    exact Nat.mul_le_mul hdLower (hdLower.trans hdd'.le)
  have hone : 1 ≤ t := htPos
  have hscaleProd : 2 ^ (2 * k) ≤ d * d' * t := by
    calc
      2 ^ (2 * k) ≤ d * d' := hbaseProd
      _ = d * d' * 1 := by simp
      _ ≤ d * d' * t := Nat.mul_le_mul_left _ hone
  have hprodLeN : d * d' * t ≤ n := Nat.le_of_dvd hnPos hprod
  have hnPred : n ≤ x - 1 := by omega
  have hpowPred : 2 ^ (2 * k) ≤ x - 1 :=
    hscaleProd.trans (hprodLeN.trans hnPred)
  have hlog : 2 * k ≤ Nat.log 2 (x - 1) :=
    Nat.le_log_of_pow_le (by omega) hpowPred
  unfold sqrtScaleCutoff
  omega

lemma divisors_eq_positiveBelow_filter_dvd {x n : ℕ}
    (hn : n ∈ positiveBelow x) :
    n.divisors = (positiveBelow x).filter fun d ↦ d ∣ n := by
  ext d
  have hnPos : 0 < n := (Finset.mem_Ico.mp hn).1
  have hnLt : n < x := (Finset.mem_Ico.mp hn).2
  simp only [Nat.mem_divisors, Finset.mem_filter, positiveBelow,
    Finset.mem_Ico]
  constructor
  · rintro ⟨hd, hn0⟩
    have hdPos : 0 < d := Nat.pos_of_dvd_of_pos hd hnPos
    exact ⟨⟨hdPos, (Nat.le_of_dvd hnPos hd).trans_lt hnLt⟩, hd⟩
  · rintro ⟨⟨hdPos, _⟩, hd⟩
    exact ⟨hd, Nat.ne_of_gt hnPos⟩

/-- Exact finite factorization of a divisor sum.  This is the elementary
reindexing used each time an ET convolution variable is extracted. -/
theorem sum_divisors_reindex (x : ℕ) (F : ℕ → ℕ → ℝ) :
    (∑ n ∈ positiveBelow x, ∑ d ∈ n.divisors, F n d) =
      ∑ d ∈ positiveBelow x,
        ∑ m ∈ (positiveBelow x).filter (fun m ↦ d * m < x),
          F (d * m) d := by
  classical
  calc
    (∑ n ∈ positiveBelow x, ∑ d ∈ n.divisors, F n d) =
        ∑ n ∈ positiveBelow x,
          ∑ d ∈ (positiveBelow x).filter (fun d ↦ d ∣ n), F n d := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [divisors_eq_positiveBelow_filter_dvd hn]
    _ = ∑ d ∈ positiveBelow x,
          ∑ n ∈ (positiveBelow x).filter (fun n ↦ d ∣ n), F n d := by
      simp_rw [Finset.sum_filter]
      rw [Finset.sum_comm]
    _ = ∑ d ∈ positiveBelow x,
          ∑ m ∈ (positiveBelow x).filter (fun m ↦ d * m < x),
            F (d * m) d := by
      apply Finset.sum_congr rfl
      intro d hd
      let S : Finset ℕ := (positiveBelow x).filter fun n ↦ d ∣ n
      let T : Finset ℕ := (positiveBelow x).filter fun m ↦ d * m < x
      have hdPos : 0 < d := (Finset.mem_Ico.mp hd).1
      change (∑ n ∈ S, F n d) = ∑ m ∈ T, F (d * m) d
      refine Finset.sum_bij' (fun n _ ↦ n / d) (fun m _ ↦ d * m) ?_ ?_ ?_ ?_ ?_
      · intro n hn
        have hn' := Finset.mem_filter.mp hn
        have hnIco := Finset.mem_Ico.mp hn'.1
        have hnDiv := hn'.2
        have hquotPos : 0 < n / d :=
          Nat.div_pos (Nat.le_of_dvd hnIco.1 hnDiv) hdPos
        have hquotLt : n / d < x := (Nat.div_le_self n d).trans_lt hnIco.2
        have hmul : d * (n / d) < x := by
          simpa [Nat.mul_div_cancel' hnDiv] using hnIco.2
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_Ico.mpr ⟨hquotPos, hquotLt⟩, hmul⟩
      · intro m hm
        have hm' := Finset.mem_filter.mp hm
        have hmIco := Finset.mem_Ico.mp hm'.1
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_Ico.mpr ⟨Nat.mul_pos hdPos hmIco.1, hm'.2⟩,
            dvd_mul_right d m⟩
      · intro n hn
        have hnDiv := (Finset.mem_filter.mp hn).2
        exact Nat.mul_div_cancel' hnDiv
      · intro m hm
        exact Nat.mul_div_cancel_left m hdPos
      · intro n hn
        have hnDiv := (Finset.mem_filter.mp hn).2
        rw [Nat.mul_div_cancel' hnDiv]

/-! ### The exact three-range bookkeeping in Proposition 3 -/

/-- The three ranges in the second mean-value estimate in the proof of
Erdős--Tenenbaum Proposition 3. -/
inductive ScaleRegime
  | long
  | middle
  | short
  deriving DecidableEq

/-- Classify the remaining length `z`.  The boundary conventions agree with
the three cases in the paper: `thetaPow ≤ z`, `sigma ≤ z < thetaPow`, and
`z < sigma`. -/
def scaleRegime (sigma thetaPow z : ℕ) : ScaleRegime :=
  if thetaPow ≤ z then .long else if sigma ≤ z then .middle else .short

lemma scaleRegime_eq_long_iff (sigma thetaPow z : ℕ) :
    scaleRegime sigma thetaPow z = .long ↔ thetaPow ≤ z := by
  by_cases hlong : thetaPow ≤ z
  · simp [scaleRegime, hlong]
  · by_cases hmiddle : sigma ≤ z
    · simp [scaleRegime, hlong, hmiddle]
    · simp [scaleRegime, hlong, hmiddle]

lemma scaleRegime_eq_middle_iff (sigma thetaPow z : ℕ) :
    scaleRegime sigma thetaPow z = .middle ↔
      sigma ≤ z ∧ z < thetaPow := by
  simp only [scaleRegime]
  by_cases hlong : thetaPow ≤ z
  · simp [hlong]
  · simp [hlong, Nat.lt_of_not_ge hlong]

lemma scaleRegime_eq_short_iff (sigma thetaPow z : ℕ) :
    scaleRegime sigma thetaPow z = .short ↔
      z < sigma ∧ z < thetaPow := by
  by_cases hlong : thetaPow ≤ z
  · simp [scaleRegime, hlong]
  · have hztheta : z < thetaPow := Nat.lt_of_not_ge hlong
    by_cases hmiddle : sigma ≤ z
    · simp [scaleRegime, hlong, hmiddle, hztheta]
    · have hzsigma : z < sigma := Nat.lt_of_not_ge hmiddle
      simp [scaleRegime, hlong, hmiddle, hztheta, hzsigma]

/-- The contribution of one of the three remaining-length regimes. -/
def regimeContribution { ι : Type* } [DecidableEq ι]
    (I : Finset ι) (sigma thetaPow : ℕ) (z : ι → ℕ)
    (weight : ι → ℝ) (r : ScaleRegime) : ℝ :=
  ∑ i ∈ I.filter (fun i ↦ scaleRegime sigma thetaPow (z i) = r), weight i

/-- Exact `A+B+C` decomposition.  This is deliberately independent of the
analytic estimates: every reindexed quadruple belongs to exactly one range. -/
theorem sum_eq_regimeContributions { ι : Type* } [DecidableEq ι]
    (I : Finset ι) (sigma thetaPow : ℕ) (z : ι → ℕ)
    (weight : ι → ℝ) :
    (∑ i ∈ I, weight i) =
      regimeContribution I sigma thetaPow z weight .long +
      regimeContribution I sigma thetaPow z weight .middle +
      regimeContribution I sigma thetaPow z weight .short := by
  classical
  simp only [regimeContribution, Finset.sum_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  cases scaleRegime sigma thetaPow (z i) <;> simp

/-- The common factor in the one-scale estimate (17) of the writeup. -/
noncomputable def oneScaleCommon
    (Ctheta : ℝ) (x sigma k : ℕ) (y : ℝ) : ℝ :=
  Ctheta * (x : ℝ) * (Real.log (sigma : ℝ)).rpow (-y) *
    (k : ℝ).rpow ((y - 3) / 2)

/-- Assembly of the exact one-scale bound from the three analytic range
estimates.  `hreindex` is supplied by repeated use of
`sum_divisors_reindex`; `hLong`, `hMiddle`, and `hShort` are precisely the
three mean-value obligations.  No analytic fact is hidden in this lemma. -/
theorem et_prop3_one_scale_of_three_estimates
    { ι : Type* } [DecidableEq ι]
    (f : ℕ → ℝ) (I : Finset ι) (z : ι → ℕ) (weight : ι → ℝ)
    (x sigma theta k : ℕ) (y L Ctheta : ℝ)
    (hreindex : (∑ n ∈ positiveBelow x, f n) = ∑ i ∈ I, weight i)
    (hLong : regimeContribution I sigma (theta ^ k) z weight .long ≤
      oneScaleCommon Ctheta x sigma k y *
        (k : ℝ).rpow ((y - 1) / 2))
    (hMiddle : regimeContribution I sigma (theta ^ k) z weight .middle ≤
      oneScaleCommon Ctheta x sigma k y * L.rpow ((y - 1) / 2))
    (hShort : regimeContribution I sigma (theta ^ k) z weight .short ≤
      oneScaleCommon Ctheta x sigma k y *
        ((Real.log (sigma : ℝ)).rpow (y / 2) * L.rpow (-1 / 2))) :
    (∑ n ∈ positiveBelow x, f n) ≤
      Ctheta * (x : ℝ) * (Real.log (sigma : ℝ)).rpow (-y) *
        (k : ℝ).rpow ((y - 3) / 2) *
          ((k : ℝ).rpow ((y - 1) / 2) + L.rpow ((y - 1) / 2) +
            (Real.log (sigma : ℝ)).rpow (y / 2) * L.rpow (-1 / 2)) := by
  rw [hreindex, sum_eq_regimeContributions I sigma (theta ^ k) z weight]
  calc
    regimeContribution I sigma (theta ^ k) z weight .long +
          regimeContribution I sigma (theta ^ k) z weight .middle +
          regimeContribution I sigma (theta ^ k) z weight .short
        ≤ oneScaleCommon Ctheta x sigma k y *
              (k : ℝ).rpow ((y - 1) / 2) +
            oneScaleCommon Ctheta x sigma k y * L.rpow ((y - 1) / 2) +
            oneScaleCommon Ctheta x sigma k y *
              ((Real.log (sigma : ℝ)).rpow (y / 2) * L.rpow (-1 / 2)) :=
      add_le_add (add_le_add hLong hMiddle) hShort
    _ = Ctheta * (x : ℝ) * (Real.log (sigma : ℝ)).rpow (-y) *
          (k : ℝ).rpow ((y - 3) / 2) *
            ((k : ℝ).rpow ((y - 1) / 2) + L.rpow ((y - 1) / 2) +
              (Real.log (sigma : ℝ)).rpow (y / 2) * L.rpow (-1 / 2)) := by
      simp only [oneScaleCommon]
      ring

/-! ### Reindexing the corrected specialized `f_k` -/

open Erdos448Scratch.Prop2Scale

/-- The corrected Proposition 2 and Proposition 3 developments use two
equivalent finite presentations of truncated big Omega. -/
lemma omegaBelowNat_eq_truncatedOmega (n B : ℕ) :
    omegaBelowNat n B = Prop3ClosePair448.truncatedOmega n B := by
  unfold omegaBelowNat Prop3ClosePair448.truncatedOmega
  rw [Nat.support_factorization, ← Nat.toFinset_factors]
  simp_rw [← Nat.primeFactorsList_count_eq]
  rw [Finset.sum_filter_count_eq_countP]
  exact List.countP_eq_length_filter

/-- The source index set for the first moment of the corrected
`normalizedExpandedScaleMoment`. -/
def expandedScaleSourceIndices (x k : ℕ) :
    Finset (Σ _n : ℕ, ((ℕ × ℕ) × ℕ)) :=
  (positiveBelow x).sigma fun n ↦ expandedScaleTriples n k

/-- Candidate positive triples `(d,d',t)` below the first-moment cutoff. -/
def positiveTriplesBelow (x : ℕ) : Finset ((ℕ × ℕ) × ℕ) :=
  ((positiveBelow x).product (positiveBelow x)).product (positiveBelow x)

/-- The fully factorized indices `(d,d',t,m)`, with
`n = d*d'*t*m < x`. -/
abbrev expandedScaleBaseCondition (k : ℕ) (q : ((ℕ × ℕ) × ℕ)) : Prop :=
  q.1.1 ≠ q.1.2 ∧ q.1.1 < 2 * q.1.2 ∧ q.1.2 < 2 * q.1.1 ∧
    2 ^ k < q.1.1 ∧ q.1.1 ≤ 2 ^ (k + 1)

def expandedScaleFactorIndices (x k : ℕ) :
    Finset (((ℕ × ℕ) × ℕ) × ℕ) :=
  ((positiveTriplesBelow x).product (positiveBelow x)).filter fun r ↦
    let d := r.1.1.1
    let d' := r.1.1.2
    let t := r.1.2
    let m := r.2
    expandedScaleBaseCondition k r.1 ∧ d * d' * t * m < x

/-- The three factor variables before the complementary multiplier `m` is
inserted. -/
def expandedScaleBaseTriples (x k : ℕ) :
    Finset ((ℕ × ℕ) × ℕ) :=
  (positiveTriplesBelow x).filter (expandedScaleBaseCondition k)

/-- The product `d*d'*t` attached to an expanded triple. -/
def expandedTripleProduct (q : ((ℕ × ℕ) × ℕ)) : ℕ :=
  q.1.1 * q.1.2 * q.2

/-- Extract the complementary factor `m` from a source pair `(n,(d,d',t))`. -/
def sourceToFactor (s : Σ _n : ℕ, ((ℕ × ℕ) × ℕ)) :
    (((ℕ × ℕ) × ℕ) × ℕ) :=
  (s.2, s.1 / expandedTripleProduct s.2)

/-- Reconstruct `n` from the four factor variables. -/
def factorToSource (r : (((ℕ × ℕ) × ℕ) × ℕ)) :
    Σ _n : ℕ, ((ℕ × ℕ) × ℕ) :=
  ⟨expandedTripleProduct r.1 * r.2, r.1⟩

lemma expandedTripleProduct_pos_of_sourceMem
    {x k : ℕ} {s : Σ _n : ℕ, ((ℕ × ℕ) × ℕ)}
    (hs : s ∈ expandedScaleSourceIndices x k) :
    0 < expandedTripleProduct s.2 := by
  have hq := (Finset.mem_sigma.mp hs).2
  rcases mem_expandedScaleTriples_iff.mp hq with
    ⟨hd, hd', ht, _hne, _hforward, _hbackward, _hlower, _hupper, _hprod⟩
  exact Nat.mul_pos (Nat.mul_pos (Nat.pos_of_mem_divisors hd)
    (Nat.pos_of_mem_divisors hd')) (Nat.pos_of_mem_divisors ht)

lemma sourceToFactor_mem {x k : ℕ}
    {s : Σ _n : ℕ, ((ℕ × ℕ) × ℕ)}
    (hs : s ∈ expandedScaleSourceIndices x k) :
    sourceToFactor s ∈ expandedScaleFactorIndices x k := by
  rcases Finset.mem_sigma.mp hs with ⟨hn, hq⟩
  have hnIco := Finset.mem_Ico.mp hn
  rcases mem_expandedScaleTriples_iff.mp hq with
    ⟨hd, hd', ht, hne, hforward, hbackward, hlower, hupper, hprod⟩
  have hDpos : 0 < expandedTripleProduct s.2 :=
    expandedTripleProduct_pos_of_sourceMem hs
  have hmPos : 0 < s.1 / expandedTripleProduct s.2 :=
    Nat.div_pos (Nat.le_of_dvd hnIco.1 hprod) hDpos
  have hmLt : s.1 / expandedTripleProduct s.2 < x :=
    (Nat.div_le_self _ _).trans_lt hnIco.2
  have hdLt : s.2.1.1 < x :=
    (Nat.divisor_le hd).trans_lt hnIco.2
  have hd'Lt : s.2.1.2 < x :=
    (Nat.divisor_le hd').trans_lt hnIco.2
  have htLt : s.2.2 < x :=
    (Nat.divisor_le ht).trans_lt hnIco.2
  rw [expandedScaleFactorIndices, Finset.mem_filter]
  refine ⟨?_, ?_⟩
  · exact Finset.mem_product.mpr
      ⟨Finset.mem_product.mpr
        ⟨Finset.mem_product.mpr
          ⟨Finset.mem_Ico.mpr ⟨Nat.pos_of_mem_divisors hd, hdLt⟩,
            Finset.mem_Ico.mpr ⟨Nat.pos_of_mem_divisors hd', hd'Lt⟩⟩,
          Finset.mem_Ico.mpr ⟨Nat.pos_of_mem_divisors ht, htLt⟩⟩,
        Finset.mem_Ico.mpr ⟨hmPos, hmLt⟩⟩
  · dsimp [sourceToFactor, expandedTripleProduct]
    refine ⟨?_, ?_⟩
    · exact ⟨hne, hforward, hbackward, hlower, hupper⟩
    simpa [expandedTripleProduct] using
      (show expandedTripleProduct s.2 *
          (s.1 / expandedTripleProduct s.2) = s.1 from
        Nat.mul_div_cancel' hprod).trans_lt hnIco.2

lemma factorToSource_mem {x k : ℕ}
    {r : (((ℕ × ℕ) × ℕ) × ℕ)}
    (hr : r ∈ expandedScaleFactorIndices x k) :
    factorToSource r ∈ expandedScaleSourceIndices x k := by
  rcases Finset.mem_filter.mp hr with ⟨hrange, hcond⟩
  rcases Finset.mem_product.mp hrange with ⟨htriple, hm⟩
  rcases Finset.mem_product.mp htriple with ⟨hpair, ht⟩
  rcases Finset.mem_product.mp hpair with ⟨hd, hd'⟩
  rcases hcond with ⟨hbase, hprodLt⟩
  rcases hbase with ⟨hne, hforward, hbackward, hlower, hupper⟩
  have hdPos := (Finset.mem_Ico.mp hd).1
  have hd'Pos := (Finset.mem_Ico.mp hd').1
  have htPos := (Finset.mem_Ico.mp ht).1
  have hmPos := (Finset.mem_Ico.mp hm).1
  have hnPos : 0 < expandedTripleProduct r.1 * r.2 := by
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hdPos hd'Pos) htPos) hmPos
  have hnNe := Nat.ne_of_gt hnPos
  rw [expandedScaleSourceIndices, Finset.mem_sigma]
  refine ⟨Finset.mem_Ico.mpr ⟨hnPos, ?_⟩, ?_⟩
  · simpa [factorToSource, expandedTripleProduct] using hprodLt
  · rw [mem_expandedScaleTriples_iff]
    refine ⟨?_, ?_, ?_, hne, hforward, hbackward, hlower, hupper, ?_⟩
    · apply Nat.mem_divisors.mpr
      refine ⟨⟨r.1.1.2 * r.1.2 * r.2, ?_⟩, hnNe⟩
      simp only [factorToSource, expandedTripleProduct]
      ring
    · apply Nat.mem_divisors.mpr
      refine ⟨⟨r.1.1.1 * r.1.2 * r.2, ?_⟩, hnNe⟩
      simp only [factorToSource, expandedTripleProduct]
      ring
    · apply Nat.mem_divisors.mpr
      refine ⟨⟨r.1.1.1 * r.1.1.2 * r.2, ?_⟩, hnNe⟩
      simp only [factorToSource, expandedTripleProduct]
      ring
    · exact dvd_mul_right (expandedTripleProduct r.1) r.2

lemma factorToSource_sourceToFactor {x k : ℕ}
    {s : Σ _n : ℕ, ((ℕ × ℕ) × ℕ)}
    (hs : s ∈ expandedScaleSourceIndices x k) :
    factorToSource (sourceToFactor s) = s := by
  apply Sigma.ext
  · exact Nat.mul_div_cancel'
      ((mem_expandedScaleTriples_iff.mp (Finset.mem_sigma.mp hs).2).2.2.2.2.2.2.2.2)
  · rfl

lemma sourceToFactor_factorToSource {x k : ℕ}
    {r : (((ℕ × ℕ) × ℕ) × ℕ)}
    (hr : r ∈ expandedScaleFactorIndices x k) :
    sourceToFactor (factorToSource r) = r := by
  rcases Finset.mem_filter.mp hr with ⟨hrange, _hcond⟩
  rcases Finset.mem_product.mp hrange with ⟨htriple, hm⟩
  rcases Finset.mem_product.mp htriple with ⟨hpair, ht⟩
  rcases Finset.mem_product.mp hpair with ⟨hd, hd'⟩
  have hDpos : 0 < expandedTripleProduct r.1 := by
    exact Nat.mul_pos
      (Nat.mul_pos (Finset.mem_Ico.mp hd).1 (Finset.mem_Ico.mp hd').1)
      (Finset.mem_Ico.mp ht).1
  apply Prod.ext
  · rfl
  · exact Nat.mul_div_cancel_left r.2 hDpos

/-- The source summand before factor extraction. -/
noncomputable def expandedScaleSourceWeight
    (omegaBelow : ℕ → ℕ → ℕ) (k : ℕ)
    (s : Σ _n : ℕ, ((ℕ × ℕ) × ℕ)) : ℝ :=
  ((1 : ℝ) / 2) ^ omegaBelow (s.2.1.1 * s.2.2) (2 ^ k) /
    (s.1.divisors.card : ℝ)

/-- The same summand in factorized coordinates. -/
noncomputable def expandedScaleFactorWeight
    (omegaBelow : ℕ → ℕ → ℕ) (k : ℕ)
    (r : (((ℕ × ℕ) × ℕ) × ℕ)) : ℝ :=
  ((1 : ℝ) / 2) ^ omegaBelow (r.1.1.1 * r.1.2) (2 ^ k) /
    ((expandedTripleProduct r.1 * r.2).divisors.card : ℝ)

/-- The numerator weight, separated from the complementary `m`-sum. -/
noncomputable def expandedScaleTripleWeight
    (omegaBelow : ℕ → ℕ → ℕ) (k : ℕ)
    (q : ((ℕ × ℕ) × ℕ)) : ℝ :=
  ((1 : ℝ) / 2) ^ omegaBelow (q.1.1 * q.2) (2 ^ k)

lemma expandedScaleTripleWeight_nonneg
    (omegaBelow : ℕ → ℕ → ℕ) (k : ℕ)
    (q : ((ℕ × ℕ) × ℕ)) :
    0 ≤ expandedScaleTripleWeight omegaBelow k q := by
  unfold expandedScaleTripleWeight
  positivity

lemma expandedScaleTripleWeight_omegaBelowNat_eq
    (k : ℕ) (q : ((ℕ × ℕ) × ℕ)) :
    expandedScaleTripleWeight omegaBelowNat k q =
      Prop3ClosePair448.halfTruncatedOmegaWeight
        (q.1.1 * q.2) (2 ^ k) := by
  unfold expandedScaleTripleWeight Prop3ClosePair448.halfTruncatedOmegaWeight
  rw [omegaBelowNat_eq_truncatedOmega]

/-- On positive factor triples, the corrected Proposition 2 numerator
splits into exactly the weighted-`t` and close-pair factors consumed by the
second and third HR applications. -/
lemma expandedScaleTripleWeight_omegaBelowNat_mul
    {x k : ℕ} {q : ((ℕ × ℕ) × ℕ)}
    (hq : q ∈ expandedScaleBaseTriples x k) :
    expandedScaleTripleWeight omegaBelowNat k q =
      Prop3WeightedT448.omegaWeight k q.1.1 *
        Prop3WeightedT448.omegaWeight k q.2 := by
  rw [expandedScaleTripleWeight_omegaBelowNat_eq,
    Prop3ClosePair448.halfTruncatedOmegaWeight_two_pow]
  have hqrange := (Finset.mem_filter.mp hq).1
  rcases Finset.mem_product.mp hqrange with ⟨hpair, ht⟩
  rcases Finset.mem_product.mp hpair with ⟨hd, hd'⟩
  exact Prop3WeightedT448.omegaWeight_mul
    (Nat.ne_of_gt (Finset.mem_Ico.mp hd).1)
    (Nat.ne_of_gt (Finset.mem_Ico.mp ht).1)

/-- Exact regrouping of the factorized first moment with `m` innermost. -/
theorem expandedScaleFactorWeight_sum_eq_triple_m_sum
    (omegaBelow : ℕ → ℕ → ℕ) (x k : ℕ) :
    (∑ r ∈ expandedScaleFactorIndices x k,
        expandedScaleFactorWeight omegaBelow k r) =
      ∑ q ∈ expandedScaleBaseTriples x k,
        expandedScaleTripleWeight omegaBelow k q *
          ∑ m ∈ (positiveBelow x).filter
              (fun m ↦ expandedTripleProduct q * m < x),
            1 / ((expandedTripleProduct q * m).divisors.card : ℝ) := by
  classical
  unfold expandedScaleFactorIndices
  simp only [expandedScaleFactorWeight, expandedScaleTripleWeight]
  rw [Finset.sum_filter]
  calc
    _ = ∑ q ∈ positiveTriplesBelow x, ∑ m ∈ positiveBelow x,
          if expandedScaleBaseCondition k q ∧
              q.1.1 * q.1.2 * q.2 * m < x then
            ((1 : ℝ) / 2) ^ omegaBelow (q.1.1 * q.2) (2 ^ k) /
              ((expandedTripleProduct q * m).divisors.card : ℝ)
          else 0 := by
      exact Finset.sum_product (positiveTriplesBelow x) (positiveBelow x) _
    _ = ∑ q ∈ expandedScaleBaseTriples x k,
          ((1 : ℝ) / 2) ^ omegaBelow (q.1.1 * q.2) (2 ^ k) *
            ∑ m ∈ (positiveBelow x).filter
                (fun m ↦ expandedTripleProduct q * m < x),
              1 / ((expandedTripleProduct q * m).divisors.card : ℝ) := by
      unfold expandedScaleBaseTriples
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro q hq
      by_cases hbase : expandedScaleBaseCondition k q
      · rw [if_pos hbase]
        simp_rw [and_iff_right hbase]
        rw [Finset.sum_filter, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m hm
        by_cases hprod : q.1.1 * q.1.2 * q.2 * m < x
        · simp [hprod, expandedTripleProduct, div_eq_mul_inv]
        · simp [hprod, expandedTripleProduct]
      · simp [hbase]

lemma expandedScaleSourceWeight_toFactor
    (omegaBelow : ℕ → ℕ → ℕ) {x k : ℕ}
    {s : Σ _n : ℕ, ((ℕ × ℕ) × ℕ)}
    (hs : s ∈ expandedScaleSourceIndices x k) :
    expandedScaleSourceWeight omegaBelow k s =
      expandedScaleFactorWeight omegaBelow k (sourceToFactor s) := by
  unfold expandedScaleSourceWeight expandedScaleFactorWeight sourceToFactor
  simp only [expandedTripleProduct]
  rw [Nat.mul_div_cancel'
    ((mem_expandedScaleTriples_iff.mp (Finset.mem_sigma.mp hs).2).2.2.2.2.2.2.2.2)]

/-- Exact factorization of the first moment of the corrected specialized
`f_k(1/2,n)`. -/
theorem normalizedExpandedScaleMoment_sum_reindex
    (omegaBelow : ℕ → ℕ → ℕ) (x k : ℕ) :
    (∑ n ∈ positiveBelow x, normalizedExpandedScaleMoment omegaBelow n k) =
      ∑ r ∈ expandedScaleFactorIndices x k,
        expandedScaleFactorWeight omegaBelow k r := by
  classical
  calc
    (∑ n ∈ positiveBelow x, normalizedExpandedScaleMoment omegaBelow n k) =
        ∑ s ∈ expandedScaleSourceIndices x k,
          expandedScaleSourceWeight omegaBelow k s := by
      unfold expandedScaleSourceIndices
      rw [Finset.sum_sigma]
      apply Finset.sum_congr rfl
      intro n hn
      unfold normalizedExpandedScaleMoment expandedScaleMass
      rw [Finset.sum_div]
      rfl
    _ = ∑ r ∈ expandedScaleFactorIndices x k,
          expandedScaleFactorWeight omegaBelow k r := by
      refine Finset.sum_bij' (fun s hs ↦ sourceToFactor s)
        (fun r hr ↦ factorToSource r) ?_ ?_ ?_ ?_ ?_
      · exact fun s hs ↦ sourceToFactor_mem hs
      · exact fun r hr ↦ factorToSource_mem hr
      · exact fun s hs ↦ factorToSource_sourceToFactor hs
      · exact fun r hr ↦ sourceToFactor_factorToSource hr
      · exact fun s hs ↦ expandedScaleSourceWeight_toFactor omegaBelow hs

/-- The first shifted-mean step, stated on the exact finite cutoff produced
by the reindexing.  A cutoff wrapper around the concrete HR theorem supplies
`hshifted`. -/
theorem normalizedExpandedScaleMoment_sum_le_of_shifted
    (omegaBelow : ℕ → ℕ → ℕ) (x k : ℕ)
    (shiftedBound : ((ℕ × ℕ) × ℕ) → ℝ)
    (hshifted : ∀ q ∈ expandedScaleBaseTriples x k,
      (∑ m ∈ (positiveBelow x).filter
          (fun m ↦ expandedTripleProduct q * m < x),
        1 / ((expandedTripleProduct q * m).divisors.card : ℝ)) ≤
          shiftedBound q) :
    (∑ n ∈ positiveBelow x, normalizedExpandedScaleMoment omegaBelow n k) ≤
      ∑ q ∈ expandedScaleBaseTriples x k,
        expandedScaleTripleWeight omegaBelow k q * shiftedBound q := by
  rw [normalizedExpandedScaleMoment_sum_reindex,
    expandedScaleFactorWeight_sum_eq_triple_m_sum]
  exact Finset.sum_le_sum fun q hq ↦
    mul_le_mul_of_nonneg_left (hshifted q hq)
      (expandedScaleTripleWeight_nonneg omegaBelow k q)

lemma expandedTripleProduct_pos_of_baseMem {x k : ℕ}
    {q : ((ℕ × ℕ) × ℕ)} (hq : q ∈ expandedScaleBaseTriples x k) :
    0 < expandedTripleProduct q := by
  have hqrange := (Finset.mem_filter.mp hq).1
  rcases Finset.mem_product.mp hqrange with ⟨hpair, ht⟩
  rcases Finset.mem_product.mp hpair with ⟨hd, hd'⟩
  exact Nat.mul_pos
    (Nat.mul_pos (Finset.mem_Ico.mp hd).1 (Finset.mem_Ico.mp hd').1)
    (Finset.mem_Ico.mp ht).1

/-- The explicit bound supplied by the checked first shifted reciprocal
mean, at the exact strict-product cutoff. -/
noncomputable def concreteFirstShiftedBound (x : ℕ)
    (q : ((ℕ × ℕ) × ℕ)) : ℝ :=
  Prop3ShiftedMean448.shiftedReciprocalMeanConstant *
      ((x ⌈/⌉ expandedTripleProduct q : ℕ) : ℝ) *
    Prop3ShiftedMean448.sharpShiftedReciprocalWeight (expandedTripleProduct q) /
      Real.sqrt (Real.log
        (2 * ((x ⌈/⌉ expandedTripleProduct q : ℕ) : ℝ)))

/-- The corrected `f_k` first moment after applying the actual checked first
Halberstam--Richert output.  The only side condition says that each ceiling
cutoff is at least three; the complementary tiny-cutoff cases belong to the
short-range estimate. -/
theorem normalizedExpandedScaleMoment_sum_le_concrete_first_shifted
    (omegaBelow : ℕ → ℕ → ℕ) (x k : ℕ)
    (hcut : ∀ q ∈ expandedScaleBaseTriples x k,
      3 ≤ x ⌈/⌉ expandedTripleProduct q) :
    (∑ n ∈ positiveBelow x, normalizedExpandedScaleMoment omegaBelow n k) ≤
      ∑ q ∈ expandedScaleBaseTriples x k,
        expandedScaleTripleWeight omegaBelow k q * concreteFirstShiftedBound x q := by
  apply normalizedExpandedScaleMoment_sum_le_of_shifted
  intro q hq
  have hDpos := expandedTripleProduct_pos_of_baseMem hq
  calc
    (∑ m ∈ (positiveBelow x).filter
          (fun m ↦ expandedTripleProduct q * m < x),
        1 / ((expandedTripleProduct q * m).divisors.card : ℝ)) ≤
        ∑ m ∈ (Finset.range x).filter
            (fun m ↦ expandedTripleProduct q * m < x),
          1 / ((expandedTripleProduct q * m).divisors.card : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro m hm
        have hm' := Finset.mem_filter.mp hm
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr (Finset.mem_Ico.mp hm'.1).2, hm'.2⟩
      · intro m hm hnot
        positivity
    _ ≤ concreteFirstShiftedBound x q := by
      exact Prop3ShiftedMean448.shifted_reciprocal_divisor_mean_sharp_mul_cutoff
        (expandedTripleProduct q) (expandedTripleProduct q) x hDpos (hcut q hq)

/-- The first shifted bound with the one- and two-term cutoffs handled
elementarily. -/
noncomputable def concreteFirstShiftedBoundAll (x : ℕ)
    (q : ((ℕ × ℕ) × ℕ)) : ℝ :=
  if 3 ≤ x ⌈/⌉ expandedTripleProduct q then concreteFirstShiftedBound x q
  else (x ⌈/⌉ expandedTripleProduct q : ℕ)

/-- All-cutoff first-shifted bound which retains the multiplicative shift
weight in the tiny-cutoff case. -/
noncomputable def concreteWeightedFirstShiftedBoundAll (x : ℕ)
    (q : ((ℕ × ℕ) × ℕ)) : ℝ :=
  if 3 ≤ x ⌈/⌉ expandedTripleProduct q then concreteFirstShiftedBound x q
  else Prop3ShiftedMean448.sharpShiftedReciprocalWeight
    (expandedTripleProduct q)

lemma one_div_card_divisors_le_sharpShiftedWeight {q : ℕ} (hq : q ≠ 0) :
    (1 : ℝ) / (q.divisors.card : ℝ) ≤
      Prop3ShiftedMean448.sharpShiftedReciprocalWeight q := by
  rw [Prop3ShiftedMean448.sharpShiftedReciprocalWeight, if_neg hq]
  have hprod : (1 : ℝ) ≤
      ∏ p ∈ q.primeFactors,
        Prop3ShiftedMean448.sharpLocalCorrection p := by
    exact Finset.one_le_prod fun p hp ↦
      Prop3ShiftedMean448.one_le_sharpLocalCorrection
        (Nat.prime_of_mem_primeFactors hp)
  have hdiv : 0 ≤ (1 : ℝ) / (q.divisors.card : ℝ) := by positivity
  calc
    (1 : ℝ) / (q.divisors.card : ℝ) =
        (1 / (q.divisors.card : ℝ)) * 1 := by ring
    _ ≤ (1 / (q.divisors.card : ℝ)) *
        ∏ p ∈ q.primeFactors,
          Prop3ShiftedMean448.sharpLocalCorrection p :=
      mul_le_mul_of_nonneg_left hprod hdiv

lemma positive_m_reciprocal_sum_le_concreteWeightedFirstShiftedBoundAll
    {x : ℕ} {q : ((ℕ × ℕ) × ℕ)}
    (hq : 0 < expandedTripleProduct q) :
    (∑ m ∈ (positiveBelow x).filter
        (fun m ↦ expandedTripleProduct q * m < x),
      1 / ((expandedTripleProduct q * m).divisors.card : ℝ)) ≤
      concreteWeightedFirstShiftedBoundAll x q := by
  let Q := expandedTripleProduct q
  have hsub : (positiveBelow x).filter (fun m ↦ Q * m < x) ⊆
      (Finset.range x).filter (fun m ↦ Q * m < x) := by
    intro m hm
    have hm' := Finset.mem_filter.mp hm
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Finset.mem_Ico.mp hm'.1).2, hm'.2⟩
  calc
    (∑ m ∈ (positiveBelow x).filter (fun m ↦ Q * m < x),
        1 / ((Q * m).divisors.card : ℝ)) ≤
        ∑ m ∈ (Finset.range x).filter (fun m ↦ Q * m < x),
          1 / ((Q * m).divisors.card : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro m hm hnot
      positivity
    _ ≤ concreteWeightedFirstShiftedBoundAll x q := by
      by_cases hlarge : 3 ≤ x ⌈/⌉ Q
      · rw [concreteWeightedFirstShiftedBoundAll, if_pos hlarge]
        exact Prop3ShiftedMean448.shifted_reciprocal_divisor_mean_sharp_mul_cutoff
          Q Q x hq hlarge
      · rw [concreteWeightedFirstShiftedBoundAll, if_neg hlarge]
        have hz : x ⌈/⌉ Q < 3 := Nat.lt_of_not_ge hlarge
        have hcutSub : (Finset.range x).filter (fun m ↦ Q * m < x) ⊆
            Finset.range (x ⌈/⌉ Q) := by
          intro m hm
          exact (Prop3ShiftedMean448.mem_range_ceilDiv_iff_mul_lt hq).2
            (Finset.mem_filter.mp hm).2
        have hsmall : (Finset.range x).filter (fun m ↦ Q * m < x) ⊆
            ({0, 1} : Finset ℕ) := by
          intro m hm
          have hmz := Finset.mem_range.mp (hcutSub hm)
          simp only [Finset.mem_insert, Finset.mem_singleton]
          omega
        calc
          (∑ m ∈ (Finset.range x).filter (fun m ↦ Q * m < x),
              1 / ((Q * m).divisors.card : ℝ)) ≤
              ∑ m ∈ ({0, 1} : Finset ℕ),
                1 / ((Q * m).divisors.card : ℝ) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg hsmall
            intro m hm hnot
            positivity
          _ = 1 / (Q.divisors.card : ℝ) := by simp
          _ ≤ Prop3ShiftedMean448.sharpShiftedReciprocalWeight Q :=
            one_div_card_divisors_le_sharpShiftedWeight hq.ne'

/-- The first-shifted bound with the genuinely empty outer `t` tail kept
equal to zero. -/
noncomputable def activeConcreteWeightedFirstShiftedBoundAll (x : ℕ)
    (q : ((ℕ × ℕ) × ℕ)) : ℝ :=
  if expandedTripleProduct q < x then
    concreteWeightedFirstShiftedBoundAll x q
  else 0

lemma positive_m_reciprocal_sum_le_activeWeightedFirstShiftedBoundAll
    {x : ℕ} {q : ((ℕ × ℕ) × ℕ)}
    (hq : 0 < expandedTripleProduct q) :
    (∑ m ∈ (positiveBelow x).filter
        (fun m ↦ expandedTripleProduct q * m < x),
      1 / ((expandedTripleProduct q * m).divisors.card : ℝ)) ≤
      activeConcreteWeightedFirstShiftedBoundAll x q := by
  by_cases hactive : expandedTripleProduct q < x
  · rw [activeConcreteWeightedFirstShiftedBoundAll, if_pos hactive]
    exact positive_m_reciprocal_sum_le_concreteWeightedFirstShiftedBoundAll hq
  · rw [activeConcreteWeightedFirstShiftedBoundAll, if_neg hactive]
    have hempty : (positiveBelow x).filter
        (fun m ↦ expandedTripleProduct q * m < x) = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      rintro ⟨m, hm⟩
      have hmPos := (Finset.mem_Ico.mp (Finset.mem_filter.mp hm).1).1
      have hprod := (Finset.mem_filter.mp hm).2
      have hle : expandedTripleProduct q ≤ expandedTripleProduct q * m := by
        simpa using Nat.mul_le_mul_left (expandedTripleProduct q)
          (show 1 ≤ m by omega)
      exact hactive (hle.trans_lt hprod)
    rw [hempty]
    simp

/-- Unconditional application of the checked first shifted reciprocal mean;
small ceiling cutoffs are bounded by their number of terms. -/
theorem normalizedExpandedScaleMoment_sum_le_concrete_first_shifted_all
    (omegaBelow : ℕ → ℕ → ℕ) (x k : ℕ) :
    (∑ n ∈ positiveBelow x, normalizedExpandedScaleMoment omegaBelow n k) ≤
      ∑ q ∈ expandedScaleBaseTriples x k,
        expandedScaleTripleWeight omegaBelow k q *
          concreteFirstShiftedBoundAll x q := by
  apply normalizedExpandedScaleMoment_sum_le_of_shifted
  intro q hq
  have hDpos := expandedTripleProduct_pos_of_baseMem hq
  by_cases hlarge : 3 ≤ x ⌈/⌉ expandedTripleProduct q
  · rw [concreteFirstShiftedBoundAll, if_pos hlarge]
    calc
      (∑ m ∈ (positiveBelow x).filter
            (fun m ↦ expandedTripleProduct q * m < x),
          1 / ((expandedTripleProduct q * m).divisors.card : ℝ)) ≤
          ∑ m ∈ (Finset.range x).filter
              (fun m ↦ expandedTripleProduct q * m < x),
            1 / ((expandedTripleProduct q * m).divisors.card : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro m hm
          have hm' := Finset.mem_filter.mp hm
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_range.mpr (Finset.mem_Ico.mp hm'.1).2, hm'.2⟩
        · intro m hm hnot
          positivity
      _ ≤ concreteFirstShiftedBound x q := by
        exact Prop3ShiftedMean448.shifted_reciprocal_divisor_mean_sharp_mul_cutoff
          (expandedTripleProduct q) (expandedTripleProduct q) x hDpos hlarge
  · rw [concreteFirstShiftedBoundAll, if_neg hlarge]
    let M := (positiveBelow x).filter
      (fun m ↦ expandedTripleProduct q * m < x)
    have hterm : ∀ m ∈ M,
        1 / ((expandedTripleProduct q * m).divisors.card : ℝ) ≤ 1 := by
      intro m hm
      have hmPos : 0 < m :=
        (Finset.mem_Ico.mp (Finset.mem_filter.mp hm).1).1
      have hnNe : expandedTripleProduct q * m ≠ 0 :=
        Nat.mul_ne_zero hDpos.ne' hmPos.ne'
      have hcardPos : 0 < (expandedTripleProduct q * m).divisors.card :=
        Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hnNe⟩
      have hone : (1 : ℝ) ≤
          ((expandedTripleProduct q * m).divisors.card : ℝ) := by
        exact_mod_cast hcardPos
      exact (div_le_one (by exact_mod_cast hcardPos)).2 hone
    have hMsub : M ⊆ Finset.range (x ⌈/⌉ expandedTripleProduct q) := by
      intro m hm
      exact (Prop3ShiftedMean448.mem_range_ceilDiv_iff_mul_lt hDpos).2
        (Finset.mem_filter.mp hm).2
    calc
      (∑ m ∈ (positiveBelow x).filter
            (fun m ↦ expandedTripleProduct q * m < x),
          1 / ((expandedTripleProduct q * m).divisors.card : ℝ)) =
          ∑ m ∈ M,
            1 / ((expandedTripleProduct q * m).divisors.card : ℝ) := rfl
      _ ≤ ∑ m ∈ M, (1 : ℝ) := Finset.sum_le_sum hterm
      _ = (M.card : ℝ) := by simp
      _ ≤ (x ⌈/⌉ expandedTripleProduct q : ℕ) := by
        have hcardNat : M.card ≤ x ⌈/⌉ expandedTripleProduct q := by
          simpa using Finset.card_le_card hMsub
        exact_mod_cast hcardNat

/-- The exact natural residual length `ceil(x/(dd'))` used to select the
second mean-value regime after `d,d'` have been fixed. -/
def expandedScaleResidualLength (x : ℕ)
    (r : (((ℕ × ℕ) × ℕ) × ℕ)) : ℕ :=
  x ⌈/⌉ (r.1.1.1 * r.1.1.2)

/-- One of the actual three contributions for the corrected specialized
`normalizedExpandedScaleMoment`. -/
noncomputable def expandedScaleRegimeContribution
    (omegaBelow : ℕ → ℕ → ℕ) (x k : ℕ)
    (regime : ScaleRegime) : ℝ :=
  regimeContribution (expandedScaleFactorIndices x k) 2 (2 ^ k)
    (expandedScaleResidualLength x) (expandedScaleFactorWeight omegaBelow k)
    regime

/-- Exact `A_k+B_k+C_k` identity for the corrected `f_k`. -/
theorem normalizedExpandedScaleMoment_sum_eq_three_regimes
    (omegaBelow : ℕ → ℕ → ℕ) (x k : ℕ) :
    (∑ n ∈ positiveBelow x, normalizedExpandedScaleMoment omegaBelow n k) =
      expandedScaleRegimeContribution omegaBelow x k .long +
      expandedScaleRegimeContribution omegaBelow x k .middle +
      expandedScaleRegimeContribution omegaBelow x k .short := by
  rw [normalizedExpandedScaleMoment_sum_reindex]
  exact sum_eq_regimeContributions (expandedScaleFactorIndices x k) 2 (2 ^ k)
    (expandedScaleResidualLength x) (expandedScaleFactorWeight omegaBelow k)

/-- The literal logarithm `L = log(2*x*2^(1-2k))` in specialized
Erdős--Tenenbaum Proposition 3. -/
noncomputable def specializedOneScaleLog (x k : ℕ) : ℝ :=
  Real.log (2 * (x : ℝ) * (2 : ℝ) ^ (1 - 2 * (k : ℝ)))

/-- The common factor in Proposition 3 after setting
`sigma = theta = 2` and `y = 1/2`. -/
noncomputable def specializedOneScaleCommon (C : ℝ) (x k : ℕ) : ℝ :=
  C * (x : ℝ) * (Real.log 2) ^ (-(1 : ℝ) / 2) *
    (k : ℝ) ^ (-(5 : ℝ) / 4)

/-- Concrete specialized Proposition 3 assembly for the corrected `f_k`.
The three hypotheses are exactly the remaining long-, middle-, and
short-range analytic estimates; the left side is no longer an abstract
function but `normalizedExpandedScaleMoment` from the corrected Proposition
2 development. -/
theorem normalizedExpandedScaleMoment_one_scale_bound
    (omegaBelow : ℕ → ℕ → ℕ) (C : ℝ) (x k : ℕ)
    (hLong : expandedScaleRegimeContribution omegaBelow x k .long ≤
      specializedOneScaleCommon C x k *
        (k : ℝ) ^ (-(1 : ℝ) / 4))
    (hMiddle : expandedScaleRegimeContribution omegaBelow x k .middle ≤
      specializedOneScaleCommon C x k *
        (specializedOneScaleLog x k) ^ (-(1 : ℝ) / 4))
    (hShort : expandedScaleRegimeContribution omegaBelow x k .short ≤
      specializedOneScaleCommon C x k *
        ((Real.log 2) ^ ((1 : ℝ) / 4) *
          (specializedOneScaleLog x k) ^ (-(1 : ℝ) / 2))) :
    (∑ n ∈ positiveBelow x, normalizedExpandedScaleMoment omegaBelow n k) ≤
      C * (x : ℝ) * (Real.log 2) ^ (-(1 : ℝ) / 2) *
        (k : ℝ) ^ (-(5 : ℝ) / 4) *
          ((k : ℝ) ^ (-(1 : ℝ) / 4) +
            (specializedOneScaleLog x k) ^ (-(1 : ℝ) / 4) +
            (Real.log 2) ^ ((1 : ℝ) / 4) *
              (specializedOneScaleLog x k) ^ (-(1 : ℝ) / 2)) := by
  rw [normalizedExpandedScaleMoment_sum_eq_three_regimes]
  calc
    expandedScaleRegimeContribution omegaBelow x k .long +
          expandedScaleRegimeContribution omegaBelow x k .middle +
          expandedScaleRegimeContribution omegaBelow x k .short ≤
        specializedOneScaleCommon C x k * (k : ℝ) ^ (-(1 : ℝ) / 4) +
          specializedOneScaleCommon C x k *
            (specializedOneScaleLog x k) ^ (-(1 : ℝ) / 4) +
          specializedOneScaleCommon C x k *
            ((Real.log 2) ^ ((1 : ℝ) / 4) *
              (specializedOneScaleLog x k) ^ (-(1 : ℝ) / 2)) :=
      add_le_add (add_le_add hLong hMiddle) hShort
    _ = C * (x : ℝ) * (Real.log 2) ^ (-(1 : ℝ) / 2) *
          (k : ℝ) ^ (-(5 : ℝ) / 4) *
            ((k : ℝ) ^ (-(1 : ℝ) / 4) +
              (specializedOneScaleLog x k) ^ (-(1 : ℝ) / 4) +
              (Real.log 2) ^ ((1 : ℝ) / 4) *
                (specializedOneScaleLog x k) ^ (-(1 : ℝ) / 2)) := by
      simp only [specializedOneScaleCommon]
      ring

/-! ### Exact half-open formal-bin scale -/

/-- Normalization of the half-open scale mass introduced by the formal-bin
Proposition 2 wrapper. -/
noncomputable def normalizedFormalExpandedScaleMoment
    (omegaAtLogScale : ℕ → ℕ → ℕ) (n k : ℕ) : ℝ :=
  formalExpandedScaleMass omegaAtLogScale n k / (n.divisors.card : ℝ)

abbrev formalExpandedBaseCondition (k : ℕ)
    (q : ((ℕ × ℕ) × ℕ)) : Prop :=
  q.1.1 * q.2 ≠ q.1.2 * q.2 ∧
    q.1.1 * q.2 < 2 * (q.1.2 * q.2) ∧
    q.1.2 * q.2 < 2 * (q.1.1 * q.2) ∧
    2 ^ k ≤ q.1.1 * q.2 ∧ q.1.1 * q.2 < 2 ^ (k + 1) ∧
    2 ^ k ≤ q.1.2 * q.2 ∧ q.1.2 * q.2 < 2 ^ (k + 1)

def formalExpandedSourceIndices (x k : ℕ) :
    Finset (Σ _n : ℕ, ((ℕ × ℕ) × ℕ)) :=
  (positiveBelow x).sigma fun n ↦ formalExpandedScaleTriples n k

def formalExpandedFactorIndices (x k : ℕ) :
    Finset ((((ℕ × ℕ) × ℕ) × ℕ)) :=
  ((positiveTriplesBelow x).product (positiveBelow x)).filter fun r ↦
    formalExpandedBaseCondition k r.1 ∧ expandedTripleProduct r.1 * r.2 < x

lemma formalSourceToFactor_mem {x k : ℕ}
    {s : Σ _n : ℕ, ((ℕ × ℕ) × ℕ)}
    (hs : s ∈ formalExpandedSourceIndices x k) :
    sourceToFactor s ∈ formalExpandedFactorIndices x k := by
  rcases Finset.mem_sigma.mp hs with ⟨hn, hq⟩
  have hnIco := Finset.mem_Ico.mp hn
  rcases mem_formalExpandedScaleTriples_iff.mp hq with
    ⟨hd, hd', ht, hne, hforward, hbackward, hdlower, hdupper,
      hd'lower, hd'upper, hprod⟩
  have hDpos : 0 < expandedTripleProduct s.2 := by
    exact Nat.mul_pos (Nat.mul_pos (Nat.pos_of_mem_divisors hd)
      (Nat.pos_of_mem_divisors hd')) (Nat.pos_of_mem_divisors ht)
  have hmPos : 0 < s.1 / expandedTripleProduct s.2 :=
    Nat.div_pos (Nat.le_of_dvd hnIco.1 hprod) hDpos
  have hmLt : s.1 / expandedTripleProduct s.2 < x :=
    (Nat.div_le_self _ _).trans_lt hnIco.2
  have hdLt := (Nat.divisor_le hd).trans_lt hnIco.2
  have hd'Lt := (Nat.divisor_le hd').trans_lt hnIco.2
  have htLt := (Nat.divisor_le ht).trans_lt hnIco.2
  rw [formalExpandedFactorIndices, Finset.mem_filter]
  refine ⟨?_, ?_⟩
  · exact Finset.mem_product.mpr
      ⟨Finset.mem_product.mpr
        ⟨Finset.mem_product.mpr
          ⟨Finset.mem_Ico.mpr ⟨Nat.pos_of_mem_divisors hd, hdLt⟩,
            Finset.mem_Ico.mpr ⟨Nat.pos_of_mem_divisors hd', hd'Lt⟩⟩,
          Finset.mem_Ico.mpr ⟨Nat.pos_of_mem_divisors ht, htLt⟩⟩,
        Finset.mem_Ico.mpr ⟨hmPos, hmLt⟩⟩
  · refine ⟨⟨hne, hforward, hbackward, hdlower, hdupper,
      hd'lower, hd'upper⟩, ?_⟩
    exact (Nat.mul_div_cancel' hprod).trans_lt hnIco.2

lemma formalFactorToSource_mem {x k : ℕ}
    {r : ((((ℕ × ℕ) × ℕ) × ℕ))}
    (hr : r ∈ formalExpandedFactorIndices x k) :
    factorToSource r ∈ formalExpandedSourceIndices x k := by
  rcases Finset.mem_filter.mp hr with ⟨hrange, hcond⟩
  rcases Finset.mem_product.mp hrange with ⟨htriple, hm⟩
  rcases Finset.mem_product.mp htriple with ⟨hpair, ht⟩
  rcases Finset.mem_product.mp hpair with ⟨hd, hd'⟩
  rcases hcond with ⟨hbase, hprodLt⟩
  rcases hbase with ⟨hne, hforward, hbackward, hdlower, hdupper,
    hd'lower, hd'upper⟩
  have hdPos := (Finset.mem_Ico.mp hd).1
  have hd'Pos := (Finset.mem_Ico.mp hd').1
  have htPos := (Finset.mem_Ico.mp ht).1
  have hmPos := (Finset.mem_Ico.mp hm).1
  have hnPos : 0 < expandedTripleProduct r.1 * r.2 :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hdPos hd'Pos) htPos) hmPos
  have hnNe := Nat.ne_of_gt hnPos
  rw [formalExpandedSourceIndices, Finset.mem_sigma]
  refine ⟨Finset.mem_Ico.mpr ⟨hnPos, hprodLt⟩, ?_⟩
  rw [mem_formalExpandedScaleTriples_iff]
  refine ⟨?_, ?_, ?_, hne, hforward, hbackward, hdlower, hdupper,
    hd'lower, hd'upper, dvd_mul_right (expandedTripleProduct r.1) r.2⟩
  · exact Nat.mem_divisors.mpr
      ⟨⟨r.1.1.2 * r.1.2 * r.2, by simp [factorToSource, expandedTripleProduct]; ring⟩,
        hnNe⟩
  · exact Nat.mem_divisors.mpr
      ⟨⟨r.1.1.1 * r.1.2 * r.2, by simp [factorToSource, expandedTripleProduct]; ring⟩,
        hnNe⟩
  · exact Nat.mem_divisors.mpr
      ⟨⟨r.1.1.1 * r.1.1.2 * r.2, by simp [factorToSource, expandedTripleProduct]; ring⟩,
        hnNe⟩

noncomputable def formalExpandedSourceWeight
    (omegaAtLogScale : ℕ → ℕ → ℕ) (k : ℕ)
    (s : Σ _n : ℕ, ((ℕ × ℕ) × ℕ)) : ℝ :=
  ((1 : ℝ) / 2) ^ omegaAtLogScale (s.2.1.1 * s.2.2) k /
    (s.1.divisors.card : ℝ)

noncomputable def formalExpandedFactorWeight
    (omegaAtLogScale : ℕ → ℕ → ℕ) (k : ℕ)
    (r : ((((ℕ × ℕ) × ℕ) × ℕ))) : ℝ :=
  ((1 : ℝ) / 2) ^ omegaAtLogScale (r.1.1.1 * r.1.2) k /
    ((expandedTripleProduct r.1 * r.2).divisors.card : ℝ)

lemma formalSourceWeight_toFactor
    (omegaAtLogScale : ℕ → ℕ → ℕ) {x k : ℕ}
    {s : Σ _n : ℕ, ((ℕ × ℕ) × ℕ)}
    (hs : s ∈ formalExpandedSourceIndices x k) :
    formalExpandedSourceWeight omegaAtLogScale k s =
      formalExpandedFactorWeight omegaAtLogScale k (sourceToFactor s) := by
  unfold formalExpandedSourceWeight formalExpandedFactorWeight sourceToFactor
  simp only [expandedTripleProduct]
  rw [Nat.mul_div_cancel'
    ((mem_formalExpandedScaleTriples_iff.mp (Finset.mem_sigma.mp hs).2).2.2.2.2.2.2.2.2.2.2)]

/-- Exact finite reindex for the half-open formal-bin scale mass. -/
theorem normalizedFormalExpandedScaleMoment_sum_reindex
    (omegaAtLogScale : ℕ → ℕ → ℕ) (x k : ℕ) :
    (∑ n ∈ positiveBelow x,
      normalizedFormalExpandedScaleMoment omegaAtLogScale n k) =
      ∑ r ∈ formalExpandedFactorIndices x k,
        formalExpandedFactorWeight omegaAtLogScale k r := by
  classical
  calc
    (∑ n ∈ positiveBelow x,
        normalizedFormalExpandedScaleMoment omegaAtLogScale n k) =
        ∑ s ∈ formalExpandedSourceIndices x k,
          formalExpandedSourceWeight omegaAtLogScale k s := by
      unfold formalExpandedSourceIndices
      rw [Finset.sum_sigma]
      apply Finset.sum_congr rfl
      intro n hn
      unfold normalizedFormalExpandedScaleMoment formalExpandedScaleMass
      rw [Finset.sum_div]
      rfl
    _ = ∑ r ∈ formalExpandedFactorIndices x k,
          formalExpandedFactorWeight omegaAtLogScale k r := by
      refine Finset.sum_bij' (fun s hs ↦ sourceToFactor s)
        (fun r hr ↦ factorToSource r) ?_ ?_ ?_ ?_ ?_
      · exact fun s hs ↦ formalSourceToFactor_mem hs
      · exact fun r hr ↦ formalFactorToSource_mem hr
      · intro s hs
        apply Sigma.ext
        · exact Nat.mul_div_cancel'
            ((mem_formalExpandedScaleTriples_iff.mp
              (Finset.mem_sigma.mp hs).2).2.2.2.2.2.2.2.2.2.2)
        · rfl
      · intro r hr
        have hrange := (Finset.mem_filter.mp hr).1
        rcases Finset.mem_product.mp hrange with ⟨htriple, hm⟩
        rcases Finset.mem_product.mp htriple with ⟨hpair, ht⟩
        rcases Finset.mem_product.mp hpair with ⟨hd, hd'⟩
        apply Prod.ext
        · rfl
        · exact Nat.mul_div_cancel_left r.2
            (Nat.mul_pos
              (Nat.mul_pos (Finset.mem_Ico.mp hd).1 (Finset.mem_Ico.mp hd').1)
              (Finset.mem_Ico.mp ht).1)
      · exact fun s hs ↦ formalSourceWeight_toFactor omegaAtLogScale hs

/-- The residual `m`-length after the two reduced divisor variables have
been fixed in the exact half-open-bin expansion. -/
def formalExpandedScaleResidualLength (x : ℕ)
    (r : (((ℕ × ℕ) × ℕ) × ℕ)) : ℕ :=
  x ⌈/⌉ (r.1.1.1 * r.1.1.2)

/-- Long-, middle-, or short-residual contribution for the exact formal
half-open-bin scale. -/
noncomputable def formalExpandedScaleRegimeContribution
    (omegaAtLogScale : ℕ → ℕ → ℕ) (x k : ℕ)
    (regime : ScaleRegime) : ℝ :=
  regimeContribution (formalExpandedFactorIndices x k) 2 (2 ^ k)
    (formalExpandedScaleResidualLength x)
    (formalExpandedFactorWeight omegaAtLogScale k) regime

/-- Exact `A_k+B_k+C_k` decomposition for the formal half-open-bin scale.
This is a partition of the actual factor-indexed moment, not an abstract
surrogate. -/
theorem normalizedFormalExpandedScaleMoment_sum_eq_three_regimes
    (omegaAtLogScale : ℕ → ℕ → ℕ) (x k : ℕ) :
    (∑ n ∈ positiveBelow x,
      normalizedFormalExpandedScaleMoment omegaAtLogScale n k) =
      formalExpandedScaleRegimeContribution omegaAtLogScale x k .long +
      formalExpandedScaleRegimeContribution omegaAtLogScale x k .middle +
      formalExpandedScaleRegimeContribution omegaAtLogScale x k .short := by
  rw [normalizedFormalExpandedScaleMoment_sum_reindex]
  exact sum_eq_regimeContributions (formalExpandedFactorIndices x k) 2 (2 ^ k)
    (formalExpandedScaleResidualLength x)
    (formalExpandedFactorWeight omegaAtLogScale k)

/-- Specialized Proposition 3 assembly on the exact half-open formal-bin
scale.  The hypotheses isolate precisely the three analytic estimates; all
finite reindexing and regime bookkeeping is discharged here. -/
theorem normalizedFormalExpandedScaleMoment_one_scale_bound
    (omegaAtLogScale : ℕ → ℕ → ℕ) (C : ℝ) (x k : ℕ)
    (hLong : formalExpandedScaleRegimeContribution omegaAtLogScale x k .long ≤
      specializedOneScaleCommon C x k *
        (k : ℝ) ^ (-(1 : ℝ) / 4))
    (hMiddle : formalExpandedScaleRegimeContribution omegaAtLogScale x k .middle ≤
      specializedOneScaleCommon C x k *
        (specializedOneScaleLog x k) ^ (-(1 : ℝ) / 4))
    (hShort : formalExpandedScaleRegimeContribution omegaAtLogScale x k .short ≤
      specializedOneScaleCommon C x k *
        ((Real.log 2) ^ ((1 : ℝ) / 4) *
          (specializedOneScaleLog x k) ^ (-(1 : ℝ) / 2))) :
    (∑ n ∈ positiveBelow x,
      normalizedFormalExpandedScaleMoment omegaAtLogScale n k) ≤
      C * (x : ℝ) * (Real.log 2) ^ (-(1 : ℝ) / 2) *
        (k : ℝ) ^ (-(5 : ℝ) / 4) *
          ((k : ℝ) ^ (-(1 : ℝ) / 4) +
            (specializedOneScaleLog x k) ^ (-(1 : ℝ) / 4) +
            (Real.log 2) ^ ((1 : ℝ) / 4) *
              (specializedOneScaleLog x k) ^ (-(1 : ℝ) / 2)) := by
  rw [normalizedFormalExpandedScaleMoment_sum_eq_three_regimes]
  calc
    formalExpandedScaleRegimeContribution omegaAtLogScale x k .long +
          formalExpandedScaleRegimeContribution omegaAtLogScale x k .middle +
          formalExpandedScaleRegimeContribution omegaAtLogScale x k .short ≤
        specializedOneScaleCommon C x k * (k : ℝ) ^ (-(1 : ℝ) / 4) +
          specializedOneScaleCommon C x k *
            (specializedOneScaleLog x k) ^ (-(1 : ℝ) / 4) +
          specializedOneScaleCommon C x k *
            ((Real.log 2) ^ ((1 : ℝ) / 4) *
              (specializedOneScaleLog x k) ^ (-(1 : ℝ) / 2)) :=
      add_le_add (add_le_add hLong hMiddle) hShort
    _ = C * (x : ℝ) * (Real.log 2) ^ (-(1 : ℝ) / 2) *
          (k : ℝ) ^ (-(5 : ℝ) / 4) *
            ((k : ℝ) ^ (-(1 : ℝ) / 4) +
              (specializedOneScaleLog x k) ^ (-(1 : ℝ) / 4) +
              (Real.log 2) ^ ((1 : ℝ) / 4) *
                (specializedOneScaleLog x k) ^ (-(1 : ℝ) / 2)) := by
      simp only [specializedOneScaleCommon]
      ring

/-! ### Authoritative reduced formal scale -/

/-- Normalized expanded mass on the dyadic scale of the smaller reduced
gcd coordinate.  This is the scale used by the corrected Proposition 2. -/
noncomputable def normalizedReducedFormalExpandedScaleMoment
    (omegaAtLogScale : ℕ → ℕ → ℕ) (n k : ℕ) : ℝ :=
  reducedFormalExpandedScaleMass omegaAtLogScale n k /
    (n.divisors.card : ℝ)

abbrev reducedFormalExpandedBaseCondition (k : ℕ)
    (q : ((ℕ × ℕ) × ℕ)) : Prop :=
  q.1.1 < q.1.2 ∧ q.1.1 < 2 * q.1.2 ∧ q.1.2 < 2 * q.1.1 ∧
    2 ^ k ≤ q.1.1 ∧ q.1.1 < 2 ^ (k + 1)

def reducedFormalExpandedSourceIndices (x k : ℕ) :
    Finset (Σ _n : ℕ, ((ℕ × ℕ) × ℕ)) :=
  (positiveBelow x).sigma fun n ↦ reducedFormalExpandedScaleTriples n k

def reducedFormalExpandedFactorIndices (x k : ℕ) :
    Finset ((((ℕ × ℕ) × ℕ) × ℕ)) :=
  ((positiveTriplesBelow x).product (positiveBelow x)).filter fun r ↦
    reducedFormalExpandedBaseCondition k r.1 ∧
      expandedTripleProduct r.1 * r.2 < x

/-- The reduced-scale triples before the complementary multiplier is
inserted.  This is the exact outer index set for the first shifted mean. -/
def reducedFormalExpandedBaseTriples (x k : ℕ) :
    Finset ((ℕ × ℕ) × ℕ) :=
  (positiveTriplesBelow x).filter (reducedFormalExpandedBaseCondition k)

lemma reducedFormalSourceToFactor_mem {x k : ℕ}
    {s : Σ _n : ℕ, ((ℕ × ℕ) × ℕ)}
    (hs : s ∈ reducedFormalExpandedSourceIndices x k) :
    sourceToFactor s ∈ reducedFormalExpandedFactorIndices x k := by
  rcases Finset.mem_sigma.mp hs with ⟨hn, hq⟩
  have hnIco := Finset.mem_Ico.mp hn
  rcases mem_reducedFormalExpandedScaleTriples_iff.mp hq with
    ⟨hd, hd', ht, hdd', hforward, hbackward, hdlower, hdupper, hprod⟩
  have hDpos : 0 < expandedTripleProduct s.2 :=
    Nat.mul_pos (Nat.mul_pos (Nat.pos_of_mem_divisors hd)
      (Nat.pos_of_mem_divisors hd')) (Nat.pos_of_mem_divisors ht)
  have hmPos : 0 < s.1 / expandedTripleProduct s.2 :=
    Nat.div_pos (Nat.le_of_dvd hnIco.1 hprod) hDpos
  have hmLt : s.1 / expandedTripleProduct s.2 < x :=
    (Nat.div_le_self _ _).trans_lt hnIco.2
  have hdLt := (Nat.divisor_le hd).trans_lt hnIco.2
  have hd'Lt := (Nat.divisor_le hd').trans_lt hnIco.2
  have htLt := (Nat.divisor_le ht).trans_lt hnIco.2
  rw [reducedFormalExpandedFactorIndices, Finset.mem_filter]
  refine ⟨?_, ?_⟩
  · exact Finset.mem_product.mpr
      ⟨Finset.mem_product.mpr
        ⟨Finset.mem_product.mpr
          ⟨Finset.mem_Ico.mpr ⟨Nat.pos_of_mem_divisors hd, hdLt⟩,
            Finset.mem_Ico.mpr ⟨Nat.pos_of_mem_divisors hd', hd'Lt⟩⟩,
          Finset.mem_Ico.mpr ⟨Nat.pos_of_mem_divisors ht, htLt⟩⟩,
        Finset.mem_Ico.mpr ⟨hmPos, hmLt⟩⟩
  · exact ⟨⟨hdd', hforward, hbackward, hdlower, hdupper⟩,
      (Nat.mul_div_cancel' hprod).trans_lt hnIco.2⟩

lemma reducedFormalFactorToSource_mem {x k : ℕ}
    {r : ((((ℕ × ℕ) × ℕ) × ℕ))}
    (hr : r ∈ reducedFormalExpandedFactorIndices x k) :
    factorToSource r ∈ reducedFormalExpandedSourceIndices x k := by
  rcases Finset.mem_filter.mp hr with ⟨hrange, hbase, hprodLt⟩
  rcases Finset.mem_product.mp hrange with ⟨htriple, hm⟩
  rcases Finset.mem_product.mp htriple with ⟨hpair, ht⟩
  rcases Finset.mem_product.mp hpair with ⟨hd, hd'⟩
  rcases hbase with ⟨hdd', hforward, hbackward, hdlower, hdupper⟩
  have hdPos := (Finset.mem_Ico.mp hd).1
  have hd'Pos := (Finset.mem_Ico.mp hd').1
  have htPos := (Finset.mem_Ico.mp ht).1
  have hmPos := (Finset.mem_Ico.mp hm).1
  have hnPos : 0 < expandedTripleProduct r.1 * r.2 :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hdPos hd'Pos) htPos) hmPos
  have hnNe := Nat.ne_of_gt hnPos
  rw [reducedFormalExpandedSourceIndices, Finset.mem_sigma]
  refine ⟨Finset.mem_Ico.mpr ⟨hnPos, hprodLt⟩, ?_⟩
  rw [mem_reducedFormalExpandedScaleTriples_iff]
  refine ⟨?_, ?_, ?_, hdd', hforward, hbackward, hdlower, hdupper,
    dvd_mul_right (expandedTripleProduct r.1) r.2⟩
  · exact Nat.mem_divisors.mpr
      ⟨⟨r.1.1.2 * r.1.2 * r.2, by
          simp [factorToSource, expandedTripleProduct]; ring⟩, hnNe⟩
  · exact Nat.mem_divisors.mpr
      ⟨⟨r.1.1.1 * r.1.2 * r.2, by
          simp [factorToSource, expandedTripleProduct]; ring⟩, hnNe⟩
  · exact Nat.mem_divisors.mpr
      ⟨⟨r.1.1.1 * r.1.1.2 * r.2, by
          simp [factorToSource, expandedTripleProduct]; ring⟩, hnNe⟩

noncomputable def reducedFormalExpandedSourceWeight
    (omegaAtLogScale : ℕ → ℕ → ℕ) (k : ℕ)
    (s : Σ _n : ℕ, ((ℕ × ℕ) × ℕ)) : ℝ :=
  ((1 : ℝ) / 2) ^ omegaAtLogScale (s.2.1.1 * s.2.2) k /
    (s.1.divisors.card : ℝ)

noncomputable def reducedFormalExpandedFactorWeight
    (omegaAtLogScale : ℕ → ℕ → ℕ) (k : ℕ)
    (r : ((((ℕ × ℕ) × ℕ) × ℕ))) : ℝ :=
  ((1 : ℝ) / 2) ^ omegaAtLogScale (r.1.1.1 * r.1.2) k /
    ((expandedTripleProduct r.1 * r.2).divisors.card : ℝ)

lemma reducedFormalSourceWeight_toFactor
    (omegaAtLogScale : ℕ → ℕ → ℕ) {x k : ℕ}
    {s : Σ _n : ℕ, ((ℕ × ℕ) × ℕ)}
    (hs : s ∈ reducedFormalExpandedSourceIndices x k) :
    reducedFormalExpandedSourceWeight omegaAtLogScale k s =
      reducedFormalExpandedFactorWeight omegaAtLogScale k
        (sourceToFactor s) := by
  unfold reducedFormalExpandedSourceWeight reducedFormalExpandedFactorWeight
    sourceToFactor
  simp only [expandedTripleProduct]
  have hprod : s.2.1.1 * s.2.1.2 * s.2.2 ∣ s.1 :=
    (mem_reducedFormalExpandedScaleTriples_iff.mp
      (Finset.mem_sigma.mp hs).2).2.2.2.2.2.2.2.2
  rw [Nat.mul_div_cancel' hprod]

/-- Exact factorization reindex for the authoritative reduced scale. -/
theorem normalizedReducedFormalExpandedScaleMoment_sum_reindex
    (omegaAtLogScale : ℕ → ℕ → ℕ) (x k : ℕ) :
    (∑ n ∈ positiveBelow x,
      normalizedReducedFormalExpandedScaleMoment omegaAtLogScale n k) =
      ∑ r ∈ reducedFormalExpandedFactorIndices x k,
        reducedFormalExpandedFactorWeight omegaAtLogScale k r := by
  classical
  calc
    (∑ n ∈ positiveBelow x,
        normalizedReducedFormalExpandedScaleMoment omegaAtLogScale n k) =
        ∑ s ∈ reducedFormalExpandedSourceIndices x k,
          reducedFormalExpandedSourceWeight omegaAtLogScale k s := by
      unfold reducedFormalExpandedSourceIndices
      rw [Finset.sum_sigma]
      apply Finset.sum_congr rfl
      intro n hn
      unfold normalizedReducedFormalExpandedScaleMoment
        reducedFormalExpandedScaleMass
      rw [Finset.sum_div]
      rfl
    _ = ∑ r ∈ reducedFormalExpandedFactorIndices x k,
          reducedFormalExpandedFactorWeight omegaAtLogScale k r := by
      refine Finset.sum_bij' (fun s hs ↦ sourceToFactor s)
        (fun r hr ↦ factorToSource r) ?_ ?_ ?_ ?_ ?_
      · exact fun s hs ↦ reducedFormalSourceToFactor_mem hs
      · exact fun r hr ↦ reducedFormalFactorToSource_mem hr
      · intro s hs
        apply Sigma.ext
        · have hprod : s.2.1.1 * s.2.1.2 * s.2.2 ∣ s.1 :=
            (mem_reducedFormalExpandedScaleTriples_iff.mp
              (Finset.mem_sigma.mp hs).2).2.2.2.2.2.2.2.2
          exact Nat.mul_div_cancel' hprod
        · rfl
      · intro r hr
        have hrange := (Finset.mem_filter.mp hr).1
        rcases Finset.mem_product.mp hrange with ⟨htriple, hm⟩
        rcases Finset.mem_product.mp htriple with ⟨hpair, ht⟩
        rcases Finset.mem_product.mp hpair with ⟨hd, hd'⟩
        apply Prod.ext
        · rfl
        · exact Nat.mul_div_cancel_left r.2
            (Nat.mul_pos
              (Nat.mul_pos (Finset.mem_Ico.mp hd).1
                (Finset.mem_Ico.mp hd').1)
              (Finset.mem_Ico.mp ht).1)
      · exact fun s hs ↦
          reducedFormalSourceWeight_toFactor omegaAtLogScale hs

/-- Exact regrouping of the authoritative reduced-scale factor sum, with
the complementary multiplier `m` innermost. -/
theorem reducedFormalExpandedFactorWeight_sum_eq_triple_m_sum
    (omegaAtLogScale : ℕ → ℕ → ℕ) (x k : ℕ) :
    (∑ r ∈ reducedFormalExpandedFactorIndices x k,
        reducedFormalExpandedFactorWeight omegaAtLogScale k r) =
      ∑ q ∈ reducedFormalExpandedBaseTriples x k,
        ((1 : ℝ) / 2) ^ omegaAtLogScale (q.1.1 * q.2) k *
          ∑ m ∈ (positiveBelow x).filter
              (fun m ↦ expandedTripleProduct q * m < x),
            1 / ((expandedTripleProduct q * m).divisors.card : ℝ) := by
  classical
  unfold reducedFormalExpandedFactorIndices
  simp only [reducedFormalExpandedFactorWeight]
  rw [Finset.sum_filter]
  calc
    _ = ∑ q ∈ positiveTriplesBelow x, ∑ m ∈ positiveBelow x,
          if reducedFormalExpandedBaseCondition k q ∧
              expandedTripleProduct q * m < x then
            ((1 : ℝ) / 2) ^ omegaAtLogScale (q.1.1 * q.2) k /
              ((expandedTripleProduct q * m).divisors.card : ℝ)
          else 0 := by
      exact Finset.sum_product (positiveTriplesBelow x) (positiveBelow x) _
    _ = ∑ q ∈ reducedFormalExpandedBaseTriples x k,
          ((1 : ℝ) / 2) ^ omegaAtLogScale (q.1.1 * q.2) k *
            ∑ m ∈ (positiveBelow x).filter
                (fun m ↦ expandedTripleProduct q * m < x),
              1 / ((expandedTripleProduct q * m).divisors.card : ℝ) := by
      unfold reducedFormalExpandedBaseTriples
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro q hq
      by_cases hbase : reducedFormalExpandedBaseCondition k q
      · rw [if_pos hbase]
        simp_rw [and_iff_right hbase]
        rw [Finset.sum_filter, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m hm
        by_cases hprod : expandedTripleProduct q * m < x
        · simp [hprod, div_eq_mul_inv]
        · simp [hprod]
      · simp [hbase]

lemma expandedTripleProduct_pos_of_reducedBaseMem {x k : ℕ}
    {q : ((ℕ × ℕ) × ℕ)}
    (hq : q ∈ reducedFormalExpandedBaseTriples x k) :
    0 < expandedTripleProduct q := by
  have hqrange := (Finset.mem_filter.mp hq).1
  rcases Finset.mem_product.mp hqrange with ⟨hpair, ht⟩
  rcases Finset.mem_product.mp hpair with ⟨hd, hd'⟩
  exact Nat.mul_pos
    (Nat.mul_pos (Finset.mem_Ico.mp hd).1 (Finset.mem_Ico.mp hd').1)
    (Finset.mem_Ico.mp ht).1

/-- The first shifted reciprocal-divisor estimate for every reduced-scale
triple.  The tiny ceiling cutoffs are handled by the same elementary
cardinality argument as in the historical-scale wrapper above. -/
theorem normalizedReducedFormalExpandedScaleMoment_sum_le_first_shifted
    (omegaAtLogScale : ℕ → ℕ → ℕ) (x k : ℕ) :
    (∑ n ∈ positiveBelow x,
      normalizedReducedFormalExpandedScaleMoment omegaAtLogScale n k) ≤
      ∑ q ∈ reducedFormalExpandedBaseTriples x k,
        ((1 : ℝ) / 2) ^ omegaAtLogScale (q.1.1 * q.2) k *
          concreteFirstShiftedBoundAll x q := by
  rw [normalizedReducedFormalExpandedScaleMoment_sum_reindex,
    reducedFormalExpandedFactorWeight_sum_eq_triple_m_sum]
  apply Finset.sum_le_sum
  intro q hq
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hDpos := expandedTripleProduct_pos_of_reducedBaseMem hq
  by_cases hlarge : 3 ≤ x ⌈/⌉ expandedTripleProduct q
  · rw [concreteFirstShiftedBoundAll, if_pos hlarge]
    calc
      (∑ m ∈ (positiveBelow x).filter
            (fun m ↦ expandedTripleProduct q * m < x),
          1 / ((expandedTripleProduct q * m).divisors.card : ℝ)) ≤
          ∑ m ∈ (Finset.range x).filter
              (fun m ↦ expandedTripleProduct q * m < x),
            1 / ((expandedTripleProduct q * m).divisors.card : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro m hm
          have hm' := Finset.mem_filter.mp hm
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_range.mpr (Finset.mem_Ico.mp hm'.1).2, hm'.2⟩
        · intro m hm hnot
          positivity
      _ ≤ concreteFirstShiftedBound x q := by
        exact Prop3ShiftedMean448.shifted_reciprocal_divisor_mean_sharp_mul_cutoff
          (expandedTripleProduct q) (expandedTripleProduct q) x hDpos hlarge
  · rw [concreteFirstShiftedBoundAll, if_neg hlarge]
    let M := (positiveBelow x).filter
      (fun m ↦ expandedTripleProduct q * m < x)
    have hterm : ∀ m ∈ M,
        1 / ((expandedTripleProduct q * m).divisors.card : ℝ) ≤ 1 := by
      intro m hm
      have hmPos : 0 < m :=
        (Finset.mem_Ico.mp (Finset.mem_filter.mp hm).1).1
      have hnNe : expandedTripleProduct q * m ≠ 0 :=
        Nat.mul_ne_zero hDpos.ne' hmPos.ne'
      have hcardPos : 0 < (expandedTripleProduct q * m).divisors.card :=
        Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hnNe⟩
      have hone : (1 : ℝ) ≤
          ((expandedTripleProduct q * m).divisors.card : ℝ) := by
        exact_mod_cast hcardPos
      exact (div_le_one (by exact_mod_cast hcardPos)).2 hone
    have hMsub : M ⊆ Finset.range (x ⌈/⌉ expandedTripleProduct q) := by
      intro m hm
      exact (Prop3ShiftedMean448.mem_range_ceilDiv_iff_mul_lt hDpos).2
        (Finset.mem_filter.mp hm).2
    calc
      (∑ m ∈ (positiveBelow x).filter
            (fun m ↦ expandedTripleProduct q * m < x),
          1 / ((expandedTripleProduct q * m).divisors.card : ℝ)) =
          ∑ m ∈ M,
            1 / ((expandedTripleProduct q * m).divisors.card : ℝ) := rfl
      _ ≤ ∑ m ∈ M, (1 : ℝ) := Finset.sum_le_sum hterm
      _ = (M.card : ℝ) := by simp
      _ ≤ (x ⌈/⌉ expandedTripleProduct q : ℕ) := by
        have hcardNat : M.card ≤ x ⌈/⌉ expandedTripleProduct q := by
          simpa using Finset.card_le_card hMsub
        exact_mod_cast hcardNat

/-- The natural-grid numerator is exactly the truncated-Omega weight used
by the two later mean-value estimates. -/
lemma naturalGrid_half_weight_eq_omegaWeight (n k : ℕ) :
    ((1 : ℝ) / 2) ^
        NaturalGridConcentration448.omegaAtLogScale n k =
      Prop3WeightedT448.omegaWeight k n := by
  have hcount :
      (n.primeFactorsList.filter
          (fun p : ℕ ↦ (p : ℝ) < ((2 ^ k : ℕ) : ℝ))).length =
        (n.primeFactorsList.filter (fun p : ℕ ↦ p < 2 ^ k)).length := by
    norm_cast
  change ((1 : ℝ) / 2) ^
      (n.primeFactorsList.filter
        (fun p : ℕ ↦ (p : ℝ) < ((2 ^ k : ℕ) : ℝ))).length =
    (2 : ℝ) ^ (-((n.primeFactorsList.filter
      (fun p : ℕ ↦ p < 2 ^ k)).length : ℤ))
  rw [hcount, zpow_neg, zpow_natCast]
  rw [one_div, inv_pow]

lemma naturalGrid_half_weight_mul_of_reducedBaseMem
    {x k : ℕ} {q : ((ℕ × ℕ) × ℕ)}
    (hq : q ∈ reducedFormalExpandedBaseTriples x k) :
    ((1 : ℝ) / 2) ^
        NaturalGridConcentration448.omegaAtLogScale (q.1.1 * q.2) k =
      Prop3WeightedT448.omegaWeight k q.1.1 *
        Prop3WeightedT448.omegaWeight k q.2 := by
  rw [naturalGrid_half_weight_eq_omegaWeight]
  have hqrange := (Finset.mem_filter.mp hq).1
  rcases Finset.mem_product.mp hqrange with ⟨hpair, ht⟩
  rcases Finset.mem_product.mp hpair with ⟨hd, hd'⟩
  exact Prop3WeightedT448.omegaWeight_mul
    (Nat.ne_of_gt (Finset.mem_Ico.mp hd).1)
    (Nat.ne_of_gt (Finset.mem_Ico.mp ht).1)

lemma reducedFormalFactor_scale_le_sqrtScaleCutoff {x k : ℕ}
    {r : ((((ℕ × ℕ) × ℕ) × ℕ))}
    (hr : r ∈ reducedFormalExpandedFactorIndices x k) :
    k ≤ sqrtScaleCutoff x := by
  rcases Finset.mem_filter.mp hr with ⟨hrange, hbase, hprodLt⟩
  rcases Finset.mem_product.mp hrange with ⟨htriple, hm⟩
  rcases Finset.mem_product.mp htriple with ⟨hpair, ht⟩
  rcases Finset.mem_product.mp hpair with ⟨hd, hd'⟩
  rcases hbase with ⟨hdd', hforward, hbackward, hdlower, hdupper⟩
  have hdPos := (Finset.mem_Ico.mp hd).1
  have hd'Pos := (Finset.mem_Ico.mp hd').1
  have htPos := (Finset.mem_Ico.mp ht).1
  have hmPos := (Finset.mem_Ico.mp hm).1
  exact reducedScale_le_sqrtScaleCutoff
    (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hdPos hd'Pos) htPos) hmPos)
    hprodLt htPos (dvd_mul_right (expandedTripleProduct r.1) r.2)
    hdlower hdd'

/-- There are no factor tuples above the exact square-root cutoff. -/
lemma reducedFormalExpandedFactorIndices_eq_empty_of_cutoff_lt
    {x k : ℕ} (hk : sqrtScaleCutoff x < k) :
    reducedFormalExpandedFactorIndices x k = ∅ := by
  apply Finset.not_nonempty_iff_eq_empty.mp
  rintro ⟨r, hr⟩
  exact (Nat.not_le_of_gt hk)
    (reducedFormalFactor_scale_le_sqrtScaleCutoff hr)

/-- Exact zero tail for the averaged reduced-scale moment. -/
theorem normalizedReducedFormalExpandedScaleMoment_sum_eq_zero_of_cutoff_lt
    (omegaAtLogScale : ℕ → ℕ → ℕ) {x k : ℕ}
    (hk : sqrtScaleCutoff x < k) :
    (∑ n ∈ positiveBelow x,
      normalizedReducedFormalExpandedScaleMoment omegaAtLogScale n k) = 0 := by
  rw [normalizedReducedFormalExpandedScaleMoment_sum_reindex,
    reducedFormalExpandedFactorIndices_eq_empty_of_cutoff_lt hk]
  simp

def reducedFormalExpandedScaleResidualLength (x : ℕ)
    (r : (((ℕ × ℕ) × ℕ) × ℕ)) : ℕ :=
  x ⌈/⌉ (r.1.1.1 * r.1.1.2)

noncomputable def reducedFormalExpandedScaleRegimeContribution
    (omegaAtLogScale : ℕ → ℕ → ℕ) (x k : ℕ)
    (regime : ScaleRegime) : ℝ :=
  regimeContribution (reducedFormalExpandedFactorIndices x k) 2 (2 ^ k)
    (reducedFormalExpandedScaleResidualLength x)
    (reducedFormalExpandedFactorWeight omegaAtLogScale k) regime

lemma reducedFormalExpandedShortFilter_eq_empty (x k : ℕ) :
    (reducedFormalExpandedFactorIndices x k).filter (fun r ↦
      scaleRegime 2 (2 ^ k)
        (reducedFormalExpandedScaleResidualLength x r) = .short) = ∅ := by
  apply Finset.not_nonempty_iff_eq_empty.mp
  rintro ⟨r, hr⟩
  rcases Finset.mem_filter.mp hr with ⟨hrIndex, hrShort⟩
  rcases Finset.mem_filter.mp hrIndex with ⟨hrange, hbase, hprodLt⟩
  rcases Finset.mem_product.mp hrange with ⟨htriple, hm⟩
  rcases Finset.mem_product.mp htriple with ⟨hpair, ht⟩
  rcases Finset.mem_product.mp hpair with ⟨hd, hd'⟩
  have hdPos := (Finset.mem_Ico.mp hd).1
  have hd'Pos := (Finset.mem_Ico.mp hd').1
  have htPos := (Finset.mem_Ico.mp ht).1
  have hmPos := (Finset.mem_Ico.mp hm).1
  have hApos : 0 < r.1.1.1 * r.1.1.2 := Nat.mul_pos hdPos hd'Pos
  have hAlt : r.1.1.1 * r.1.1.2 < x := by
    calc
      r.1.1.1 * r.1.1.2 =
          r.1.1.1 * r.1.1.2 * 1 * 1 := by simp
      _ ≤ r.1.1.1 * r.1.1.2 * r.1.2 * r.2 :=
        Nat.mul_le_mul
          (Nat.mul_le_mul_left _ (show 1 ≤ r.1.2 by omega))
          (show 1 ≤ r.2 by omega)
      _ < x := hprodLt
  have honeMem :
      1 ∈ Finset.range (x ⌈/⌉ (r.1.1.1 * r.1.1.2)) :=
    (Prop3ShiftedMean448.mem_range_ceilDiv_iff_mul_lt hApos).2
      (by simpa using hAlt)
  have htwoLe : 2 ≤ x ⌈/⌉ (r.1.1.1 * r.1.1.2) := by
    have := Finset.mem_range.mp honeMem
    omega
  have hshort := (scaleRegime_eq_short_iff 2 (2 ^ k)
    (reducedFormalExpandedScaleResidualLength x r)).mp hrShort
  exact (Nat.not_lt_of_ge htwoLe) hshort.1

theorem reducedFormalExpandedScaleRegimeContribution_short_eq_zero
    (omegaAtLogScale : ℕ → ℕ → ℕ) (x k : ℕ) :
    reducedFormalExpandedScaleRegimeContribution
        omegaAtLogScale x k .short = 0 := by
  unfold reducedFormalExpandedScaleRegimeContribution regimeContribution
  rw [reducedFormalExpandedShortFilter_eq_empty]
  simp

noncomputable def reducedFormalTripleMRegimeContribution
    (omegaAtLogScale : ℕ → ℕ → ℕ) (x k : ℕ)
    (regime : ScaleRegime) : ℝ :=
  ∑ q ∈ (reducedFormalExpandedBaseTriples x k).filter (fun q ↦
      scaleRegime 2 (2 ^ k) (x ⌈/⌉ (q.1.1 * q.1.2)) = regime),
    ((1 : ℝ) / 2) ^ omegaAtLogScale (q.1.1 * q.2) k *
      ∑ m ∈ (positiveBelow x).filter
          (fun m ↦ expandedTripleProduct q * m < x),
        1 / ((expandedTripleProduct q * m).divisors.card : ℝ)

/-- Exact per-regime regrouping, with no analytic estimate. -/
theorem reducedFormalExpandedScaleRegimeContribution_eq_triple_m
    (omegaAtLogScale : ℕ → ℕ → ℕ) (x k : ℕ)
    (regime : ScaleRegime) :
    reducedFormalExpandedScaleRegimeContribution
        omegaAtLogScale x k regime =
      reducedFormalTripleMRegimeContribution
        omegaAtLogScale x k regime := by
  classical
  unfold reducedFormalExpandedScaleRegimeContribution regimeContribution
  rw [Finset.sum_filter]
  unfold reducedFormalExpandedFactorIndices
  rw [Finset.sum_filter]
  have hproduct := Finset.sum_product (positiveTriplesBelow x)
    (positiveBelow x) (fun a ↦
      if reducedFormalExpandedBaseCondition k a.1 ∧
          expandedTripleProduct a.1 * a.2 < x then
        if scaleRegime 2 (2 ^ k)
            (reducedFormalExpandedScaleResidualLength x a) = regime then
          reducedFormalExpandedFactorWeight omegaAtLogScale k a
        else 0
      else 0)
  change (∑ a ∈ positiveTriplesBelow x ×ˢ positiveBelow x,
      if reducedFormalExpandedBaseCondition k a.1 ∧
          expandedTripleProduct a.1 * a.2 < x then
        if scaleRegime 2 (2 ^ k)
            (reducedFormalExpandedScaleResidualLength x a) = regime then
          reducedFormalExpandedFactorWeight omegaAtLogScale k a
        else 0
      else 0) = _
  rw [hproduct]
  unfold reducedFormalTripleMRegimeContribution
  unfold reducedFormalExpandedBaseTriples
  rw [Finset.filter_filter]
  conv_rhs => rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hbase : reducedFormalExpandedBaseCondition k q
  · by_cases hreg :
        scaleRegime 2 (2 ^ k) (x ⌈/⌉ (q.1.1 * q.1.2)) = regime
    · rw [if_pos ⟨hbase, hreg⟩]
      rw [Finset.mul_sum, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro m hm
      by_cases hprod : expandedTripleProduct q * m < x
      · rw [if_pos ⟨hbase, hprod⟩]
        rw [show reducedFormalExpandedScaleResidualLength x (q, m) =
            x ⌈/⌉ (q.1.1 * q.1.2) by rfl, if_pos hreg, if_pos hprod]
        unfold reducedFormalExpandedFactorWeight
        simp only [div_eq_mul_inv, one_mul]
      · rw [if_neg]
        · rw [if_neg hprod]
        · intro h
          exact hprod h.2
    · rw [if_neg]
      · apply Finset.sum_eq_zero
        intro m hm
        by_cases hprod : expandedTripleProduct q * m < x
        · rw [if_pos ⟨hbase, hprod⟩]
          rw [show reducedFormalExpandedScaleResidualLength x (q, m) =
              x ⌈/⌉ (q.1.1 * q.1.2) by rfl, if_neg hreg]
        · rw [if_neg]
          intro h
          exact hprod h.2
      · intro h
        exact hreg h.2
  · rw [if_neg]
    · apply Finset.sum_eq_zero
      intro m hm
      rw [if_neg]
      intro h
      exact hbase h.1
    · intro h
      exact hbase h.1

/-- Per-regime first shifted estimate, retaining the sharp multiplicative
weight even when the inner cutoff has fewer than three terms. -/
theorem reducedFormalExpandedScaleRegimeContribution_le_weighted_first_shifted
    (omegaAtLogScale : ℕ → ℕ → ℕ) (x k : ℕ)
    (regime : ScaleRegime) :
    reducedFormalExpandedScaleRegimeContribution
        omegaAtLogScale x k regime ≤
      ∑ q ∈ (reducedFormalExpandedBaseTriples x k).filter (fun q ↦
          scaleRegime 2 (2 ^ k) (x ⌈/⌉ (q.1.1 * q.1.2)) = regime),
        ((1 : ℝ) / 2) ^ omegaAtLogScale (q.1.1 * q.2) k *
          concreteWeightedFirstShiftedBoundAll x q := by
  rw [reducedFormalExpandedScaleRegimeContribution_eq_triple_m]
  unfold reducedFormalTripleMRegimeContribution
  apply Finset.sum_le_sum
  intro q hq
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact positive_m_reciprocal_sum_le_concreteWeightedFirstShiftedBoundAll
    (expandedTripleProduct_pos_of_reducedBaseMem
      (Finset.mem_filter.mp hq).1)

theorem reducedFormalExpandedScaleRegimeContribution_le_active_first_shifted
    (omegaAtLogScale : ℕ → ℕ → ℕ) (x k : ℕ)
    (regime : ScaleRegime) :
    reducedFormalExpandedScaleRegimeContribution
        omegaAtLogScale x k regime ≤
      ∑ q ∈ (reducedFormalExpandedBaseTriples x k).filter (fun q ↦
          scaleRegime 2 (2 ^ k) (x ⌈/⌉ (q.1.1 * q.1.2)) = regime),
        ((1 : ℝ) / 2) ^ omegaAtLogScale (q.1.1 * q.2) k *
          activeConcreteWeightedFirstShiftedBoundAll x q := by
  rw [reducedFormalExpandedScaleRegimeContribution_eq_triple_m]
  unfold reducedFormalTripleMRegimeContribution
  apply Finset.sum_le_sum
  intro q hq
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact positive_m_reciprocal_sum_le_activeWeightedFirstShiftedBoundAll
    (expandedTripleProduct_pos_of_reducedBaseMem
      (Finset.mem_filter.mp hq).1)

/-- Positive strict multiplication cutoffs are precisely half-open ceiling
intervals. -/
lemma positiveBelow_filter_mul_lt_eq_Ico_ceilDiv
    {A x : ℕ} (hA : 0 < A) :
    (positiveBelow x).filter (fun t ↦ A * t < x) =
      Finset.Ico 1 (x ⌈/⌉ A) := by
  ext t
  simp only [Finset.mem_filter, positiveBelow, Finset.mem_Ico]
  have hceil : t < x ⌈/⌉ A ↔ A * t < x := by
    simpa [Finset.mem_range] using
      (Prop3ShiftedMean448.mem_range_ceilDiv_iff_mul_lt
        (x := x) (m := t) hA)
  constructor
  · rintro ⟨⟨htPos, htx⟩, hprod⟩
    exact ⟨htPos, hceil.2 hprod⟩
  · rintro ⟨htPos, htceil⟩
    have hprod := hceil.1 htceil
    have honeA : 1 ≤ A := hA
    have htx : t < x := by
      calc
        t = 1 * t := by simp
        _ ≤ A * t := Nat.mul_le_mul_right t honeA
        _ < x := hprod
    exact ⟨⟨htPos, htx⟩, hprod⟩

lemma ceilDiv_le_div_add_one {x q : ℕ} (hq : 0 < q) :
    x ⌈/⌉ q ≤ x / q + 1 := by
  apply (ceilDiv_le_iff_le_mul hq).2
  have hmod : x % q ≤ q := (Nat.mod_lt x hq).le
  calc
    x = q * (x / q) + x % q := by
      simpa [Nat.mul_comm] using (Nat.div_add_mod x q).symm
    _ ≤ q * (x / q) + q := Nat.add_le_add_left hmod _
    _ = q * (x / q + 1) := by ring

lemma cast_ceilDiv_le_two_mul_div {x q : ℕ}
    (hq : 0 < q) (hqx : q < x) :
    ((x ⌈/⌉ q : ℕ) : ℝ) ≤ 2 * (x : ℝ) / (q : ℝ) := by
  have hnat := ceilDiv_le_div_add_one (x := x) hq
  have hcast : ((x ⌈/⌉ q : ℕ) : ℝ) ≤ ((x / q : ℕ) : ℝ) + 1 := by
    exact_mod_cast hnat
  have hfloor : ((x / q : ℕ) : ℝ) ≤ (x : ℝ) / (q : ℝ) :=
    Nat.cast_div_le
  have hratio : (1 : ℝ) < (x : ℝ) / (q : ℝ) := by
    rw [one_lt_div (by exact_mod_cast hq)]
    exact_mod_cast hqx
  calc
    ((x ⌈/⌉ q : ℕ) : ℝ) ≤ ((x / q : ℕ) : ℝ) + 1 := hcast
    _ ≤ (x : ℝ) / (q : ℝ) + 1 := by linarith
    _ ≤ 2 * ((x : ℝ) / (q : ℝ)) := by linarith
    _ = 2 * (x : ℝ) / (q : ℝ) := by ring

abbrev reducedFormalPairBaseCondition (k : ℕ) (p : ℕ × ℕ) : Prop :=
  p.1 < p.2 ∧ p.1 < 2 * p.2 ∧ p.2 < 2 * p.1 ∧
    2 ^ k ≤ p.1 ∧ p.1 < 2 ^ (k + 1)

lemma two_pow_two_k_le_pair_product {k : ℕ} {p : ℕ × ℕ}
    (hbase : reducedFormalPairBaseCondition k p) :
    (2 : ℝ) ^ (2 * k) ≤ (p.1 * p.2 : ℕ) := by
  have hnat : 2 ^ (2 * k) ≤ p.1 * p.2 := by
    rw [two_mul, pow_add]
    exact Nat.mul_le_mul hbase.2.2.2.1
      (hbase.2.2.2.1.trans hbase.1.le)
  exact_mod_cast hnat

def reducedFormalPairRegimeIndices (x k : ℕ) (regime : ScaleRegime) :
    Finset (ℕ × ℕ) :=
  ((positiveBelow x).product (positiveBelow x)).filter (fun p ↦
    reducedFormalPairBaseCondition k p ∧
      scaleRegime 2 (2 ^ k) (x ⌈/⌉ (p.1 * p.2)) = regime)

/-- The exact post-first-shift expression with `(d,d')` outside and the
active `t` cutoff inside. -/
noncomputable def reducedFormalPairTFirstShiftedContribution
    (x k : ℕ) (regime : ScaleRegime) : ℝ :=
  ∑ p ∈ reducedFormalPairRegimeIndices x k regime,
    Prop3WeightedT448.omegaWeight k p.1 *
      ∑ t ∈ Finset.Ico 1 (x ⌈/⌉ (p.1 * p.2)),
        Prop3WeightedT448.omegaWeight k t *
          concreteWeightedFirstShiftedBoundAll x (p, t)

/-- Exact transposition from reduced triples to the weighted `t` sum. -/
theorem naturalGrid_active_first_shifted_eq_pair_t
    (x k : ℕ) (regime : ScaleRegime) :
    (∑ q ∈ (reducedFormalExpandedBaseTriples x k).filter (fun q ↦
        scaleRegime 2 (2 ^ k) (x ⌈/⌉ (q.1.1 * q.1.2)) = regime),
      ((1 : ℝ) / 2) ^
          NaturalGridConcentration448.omegaAtLogScale (q.1.1 * q.2) k *
        activeConcreteWeightedFirstShiftedBoundAll x q) =
      reducedFormalPairTFirstShiftedContribution x k regime := by
  classical
  unfold reducedFormalExpandedBaseTriples positiveTriplesBelow
  rw [Finset.filter_filter]
  conv_lhs => rw [Finset.sum_filter]
  let P := (positiveBelow x).product (positiveBelow x)
  let f : (((ℕ × ℕ) × ℕ)) → ℝ := fun a ↦
    if reducedFormalExpandedBaseCondition k a ∧
        scaleRegime 2 (2 ^ k) (x ⌈/⌉ (a.1.1 * a.1.2)) = regime then
      ((1 : ℝ) / 2) ^
          NaturalGridConcentration448.omegaAtLogScale (a.1.1 * a.2) k *
        activeConcreteWeightedFirstShiftedBoundAll x a
    else 0
  change (∑ a ∈ P ×ˢ positiveBelow x, f a) = _
  rw [Finset.sum_product P (positiveBelow x) f]
  dsimp only [P, f]
  unfold reducedFormalPairTFirstShiftedContribution
    reducedFormalPairRegimeIndices
  conv_rhs => rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  have hdPos : 0 < p.1 :=
    (Finset.mem_Ico.mp (Finset.mem_product.mp hp).1).1
  have hd'Pos : 0 < p.2 :=
    (Finset.mem_Ico.mp (Finset.mem_product.mp hp).2).1
  have hApos : 0 < p.1 * p.2 := Nat.mul_pos hdPos hd'Pos
  by_cases hbase : reducedFormalPairBaseCondition k p
  · by_cases hreg :
        scaleRegime 2 (2 ^ k) (x ⌈/⌉ (p.1 * p.2)) = regime
    · rw [if_pos ⟨hbase, hreg⟩]
      have hcond (t : ℕ) :
          reducedFormalExpandedBaseCondition k (p, t) ∧
            scaleRegime 2 (2 ^ k) (x ⌈/⌉ (p.1 * p.2)) = regime :=
        ⟨hbase, hreg⟩
      simp_rw [if_pos (hcond _)]
      rw [Finset.mul_sum]
      simp_rw [activeConcreteWeightedFirstShiftedBoundAll, mul_ite,
        mul_zero]
      rw [← Finset.sum_filter]
      change (∑ t ∈ (positiveBelow x).filter
          (fun t ↦ p.1 * p.2 * t < x),
        ((1 : ℝ) / 2) ^
            NaturalGridConcentration448.omegaAtLogScale (p.1 * t) k *
          concreteWeightedFirstShiftedBoundAll x (p, t)) = _
      rw [positiveBelow_filter_mul_lt_eq_Ico_ceilDiv hApos]
      apply Finset.sum_congr rfl
      intro t ht
      have htPos := (Finset.mem_Ico.mp ht).1
      rw [naturalGrid_half_weight_eq_omegaWeight,
        Prop3WeightedT448.omegaWeight_mul hdPos.ne'
          (show t ≠ 0 by omega)]
      ring
    · rw [if_neg]
      · apply Finset.sum_eq_zero
        intro t ht
        rw [if_neg]
        intro h
        exact hreg h.2
      · intro h
        exact hreg h.2
  · rw [if_neg]
    · apply Finset.sum_eq_zero
      intro t ht
      rw [if_neg]
      intro h
      exact hbase h.1
    · intro h
      exact hbase h.1

/-- Checked reduction of either nonempty analytic regime to its literal
pair/weighted-`t` convolution. -/
theorem naturalGrid_reduced_regime_le_pair_t
    (x k : ℕ) (regime : ScaleRegime) :
    reducedFormalExpandedScaleRegimeContribution
        NaturalGridConcentration448.omegaAtLogScale x k regime ≤
      reducedFormalPairTFirstShiftedContribution x k regime := by
  calc
    reducedFormalExpandedScaleRegimeContribution
        NaturalGridConcentration448.omegaAtLogScale x k regime ≤
      ∑ q ∈ (reducedFormalExpandedBaseTriples x k).filter (fun q ↦
          scaleRegime 2 (2 ^ k) (x ⌈/⌉ (q.1.1 * q.1.2)) = regime),
        ((1 : ℝ) / 2) ^
            NaturalGridConcentration448.omegaAtLogScale (q.1.1 * q.2) k *
          activeConcreteWeightedFirstShiftedBoundAll x q :=
      reducedFormalExpandedScaleRegimeContribution_le_active_first_shifted
        NaturalGridConcentration448.omegaAtLogScale x k regime
    _ = reducedFormalPairTFirstShiftedContribution x k regime :=
      naturalGrid_active_first_shifted_eq_pair_t x k regime

/-- Cartesian presentation of the exact formal close-pair range used by
the third mean-value estimate. -/
def formalClosePairIndices (k : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Ico (2 ^ k) (2 ^ (k + 1))).product
      (Finset.Icc 1 (2 ^ (k + 2)))).filter (fun p ↦
    p.2 ≠ p.1 ∧ p.1 < 2 * p.2 ∧ p.2 < 2 * p.1)

noncomputable def formalClosePairCartesianMean
    (w : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ p ∈ formalClosePairIndices k,
    Prop3WeightedT448.omegaWeight k p.1 * w (p.1 * p.2)

lemma formalClosePairCartesianMean_eq
    (w : ℕ → ℝ) (k : ℕ) :
    formalClosePairCartesianMean w k =
      Prop3ClosePair448.formalDyadicClosePairMean w k := by
  classical
  unfold formalClosePairCartesianMean formalClosePairIndices
    Prop3ClosePair448.formalDyadicClosePairMean
  rw [Finset.sum_filter]
  let D := Finset.Ico (2 ^ k) (2 ^ (k + 1))
  let E := Finset.Icc 1 (2 ^ (k + 2))
  let f : ℕ × ℕ → ℝ := fun p ↦
    if p.2 ≠ p.1 ∧ p.1 < 2 * p.2 ∧ p.2 < 2 * p.1 then
      Prop3WeightedT448.omegaWeight k p.1 * w (p.1 * p.2)
    else 0
  change (∑ p ∈ D ×ˢ E, f p) = _
  rw [Finset.sum_product D E f]
  dsimp only [D, E, f]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d' hd'
  by_cases hclose : d' ≠ d ∧ d < 2 * d' ∧ d' < 2 * d
  · rw [if_pos hclose, if_pos hclose]
    rw [Prop3ClosePair448.halfTruncatedOmegaWeight_two_pow]
  · rw [if_neg hclose, if_neg hclose]

lemma reducedFormalPairRegimeIndices_subset_formalClosePairIndices
    {x k : ℕ} {regime : ScaleRegime} :
    reducedFormalPairRegimeIndices x k regime ⊆ formalClosePairIndices k := by
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hprange, hcond⟩
  rcases hcond with ⟨hbase, hreg⟩
  rcases hbase with ⟨hdd', hforward, hbackward, hdlower, hdupper⟩
  rcases Finset.mem_product.mp hprange with ⟨hd, hd'⟩
  have hd'Pos := (Finset.mem_Ico.mp hd').1
  have hd'Upper : p.2 ≤ 2 ^ (k + 2) := by
    have htwo : 2 * p.1 ≤ 2 * (2 ^ (k + 1) - 1) := by omega
    have hpstep : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by
      rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
      omega
    omega
  rw [formalClosePairIndices, Finset.mem_filter]
  exact ⟨Finset.mem_product.mpr
      ⟨Finset.mem_Ico.mpr ⟨hdlower, hdupper⟩,
        Finset.mem_Icc.mpr ⟨hd'Pos, hd'Upper⟩⟩,
    ⟨Nat.ne_of_gt hdd', hforward, hbackward⟩⟩

/-- Every restricted residual regime is dominated by the full formal
close-pair mean for a nonnegative outer weight. -/
theorem reducedFormalPairRegimeWeightSum_le_formalClosePairMean
    (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n)
    (x k : ℕ) (regime : ScaleRegime) :
    (∑ p ∈ reducedFormalPairRegimeIndices x k regime,
      Prop3WeightedT448.omegaWeight k p.1 * w (p.1 * p.2)) ≤
      Prop3ClosePair448.formalDyadicClosePairMean w k := by
  rw [← formalClosePairCartesianMean_eq]
  unfold formalClosePairCartesianMean
  apply Finset.sum_le_sum_of_subset_of_nonneg
    reducedFormalPairRegimeIndices_subset_formalClosePairIndices
  intro p hp hnot
  exact mul_nonneg (Prop3WeightedT448.omegaWeight_nonneg k p.1)
    (hw _)

/-- Generic outer assembly: a uniform pointwise bound for the inner
`t`-convolution is summed by the formal close-pair mean. -/
theorem reducedFormalPairInnerSum_le_closePairMean
    (inner : ℕ × ℕ → ℝ) (w : ℕ → ℝ) (F : ℝ)
    (hF : 0 ≤ F) (hw : ∀ n, 0 ≤ w n)
    (x k : ℕ) (regime : ScaleRegime)
    (hinner : ∀ p ∈ reducedFormalPairRegimeIndices x k regime,
      inner p ≤ F * w (p.1 * p.2)) :
    (∑ p ∈ reducedFormalPairRegimeIndices x k regime,
      Prop3WeightedT448.omegaWeight k p.1 * inner p) ≤
      F * Prop3ClosePair448.formalDyadicClosePairMean w k := by
  calc
    (∑ p ∈ reducedFormalPairRegimeIndices x k regime,
        Prop3WeightedT448.omegaWeight k p.1 * inner p) ≤
      ∑ p ∈ reducedFormalPairRegimeIndices x k regime,
        Prop3WeightedT448.omegaWeight k p.1 *
          (F * w (p.1 * p.2)) := by
      apply Finset.sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_left (hinner p hp)
        (Prop3WeightedT448.omegaWeight_nonneg k p.1)
    _ = F * ∑ p ∈ reducedFormalPairRegimeIndices x k regime,
        Prop3WeightedT448.omegaWeight k p.1 * w (p.1 * p.2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ ≤ F * Prop3ClosePair448.formalDyadicClosePairMean w k :=
      mul_le_mul_of_nonneg_left
        (reducedFormalPairRegimeWeightSum_le_formalClosePairMean
          w hw x k regime) hF

theorem normalizedReducedFormalExpandedScaleMoment_sum_eq_three_regimes
    (omegaAtLogScale : ℕ → ℕ → ℕ) (x k : ℕ) :
    (∑ n ∈ positiveBelow x,
      normalizedReducedFormalExpandedScaleMoment omegaAtLogScale n k) =
      reducedFormalExpandedScaleRegimeContribution omegaAtLogScale x k .long +
      reducedFormalExpandedScaleRegimeContribution omegaAtLogScale x k .middle +
      reducedFormalExpandedScaleRegimeContribution omegaAtLogScale x k .short := by
  rw [normalizedReducedFormalExpandedScaleMoment_sum_reindex]
  exact sum_eq_regimeContributions
    (reducedFormalExpandedFactorIndices x k) 2 (2 ^ k)
    (reducedFormalExpandedScaleResidualLength x)
    (reducedFormalExpandedFactorWeight omegaAtLogScale k)

theorem normalizedReducedFormalExpandedScaleMoment_one_scale_bound
    (omegaAtLogScale : ℕ → ℕ → ℕ) (C : ℝ) (x k : ℕ)
    (hLong : reducedFormalExpandedScaleRegimeContribution
      omegaAtLogScale x k .long ≤ specializedOneScaleCommon C x k *
        (k : ℝ) ^ (-(1 : ℝ) / 4))
    (hMiddle : reducedFormalExpandedScaleRegimeContribution
      omegaAtLogScale x k .middle ≤ specializedOneScaleCommon C x k *
        (specializedOneScaleLog x k) ^ (-(1 : ℝ) / 4))
    (hShort : reducedFormalExpandedScaleRegimeContribution
      omegaAtLogScale x k .short ≤ specializedOneScaleCommon C x k *
        ((Real.log 2) ^ ((1 : ℝ) / 4) *
          (specializedOneScaleLog x k) ^ (-(1 : ℝ) / 2))) :
    (∑ n ∈ positiveBelow x,
      normalizedReducedFormalExpandedScaleMoment omegaAtLogScale n k) ≤
      C * (x : ℝ) * (Real.log 2) ^ (-(1 : ℝ) / 2) *
        (k : ℝ) ^ (-(5 : ℝ) / 4) *
          ((k : ℝ) ^ (-(1 : ℝ) / 4) +
            (specializedOneScaleLog x k) ^ (-(1 : ℝ) / 4) +
            (Real.log 2) ^ ((1 : ℝ) / 4) *
              (specializedOneScaleLog x k) ^ (-(1 : ℝ) / 2)) := by
  rw [normalizedReducedFormalExpandedScaleMoment_sum_eq_three_regimes]
  calc
    reducedFormalExpandedScaleRegimeContribution omegaAtLogScale x k .long +
          reducedFormalExpandedScaleRegimeContribution omegaAtLogScale x k .middle +
          reducedFormalExpandedScaleRegimeContribution omegaAtLogScale x k .short ≤
        specializedOneScaleCommon C x k * (k : ℝ) ^ (-(1 : ℝ) / 4) +
          specializedOneScaleCommon C x k *
            (specializedOneScaleLog x k) ^ (-(1 : ℝ) / 4) +
          specializedOneScaleCommon C x k *
            ((Real.log 2) ^ ((1 : ℝ) / 4) *
              (specializedOneScaleLog x k) ^ (-(1 : ℝ) / 2)) :=
      add_le_add (add_le_add hLong hMiddle) hShort
    _ = C * (x : ℝ) * (Real.log 2) ^ (-(1 : ℝ) / 2) *
          (k : ℝ) ^ (-(5 : ℝ) / 4) *
            ((k : ℝ) ^ (-(1 : ℝ) / 4) +
              (specializedOneScaleLog x k) ^ (-(1 : ℝ) / 4) +
              (Real.log 2) ^ ((1 : ℝ) / 4) *
                (specializedOneScaleLog x k) ^ (-(1 : ℝ) / 2)) := by
      simp only [specializedOneScaleCommon]
      ring

/-- The authoritative one-scale assembly needs only the long and middle
estimates: the short residual regime is empty. -/
theorem normalizedReducedFormalExpandedScaleMoment_one_scale_bound_two_regimes
    (omegaAtLogScale : ℕ → ℕ → ℕ) {C : ℝ} (hC : 0 ≤ C)
    (x k : ℕ) (hL : 0 ≤ specializedOneScaleLog x k)
    (hLong : reducedFormalExpandedScaleRegimeContribution
      omegaAtLogScale x k .long ≤ specializedOneScaleCommon C x k *
        (k : ℝ) ^ (-(1 : ℝ) / 4))
    (hMiddle : reducedFormalExpandedScaleRegimeContribution
      omegaAtLogScale x k .middle ≤ specializedOneScaleCommon C x k *
        (specializedOneScaleLog x k) ^ (-(1 : ℝ) / 4)) :
    (∑ n ∈ positiveBelow x,
      normalizedReducedFormalExpandedScaleMoment omegaAtLogScale n k) ≤
      C * (x : ℝ) * (Real.log 2) ^ (-(1 : ℝ) / 2) *
        (k : ℝ) ^ (-(5 : ℝ) / 4) *
          ((k : ℝ) ^ (-(1 : ℝ) / 4) +
            (specializedOneScaleLog x k) ^ (-(1 : ℝ) / 4) +
            (Real.log 2) ^ ((1 : ℝ) / 4) *
              (specializedOneScaleLog x k) ^ (-(1 : ℝ) / 2)) := by
  apply normalizedReducedFormalExpandedScaleMoment_one_scale_bound
    omegaAtLogScale C x k hLong hMiddle
  rw [reducedFormalExpandedScaleRegimeContribution_short_eq_zero]
  have hcommon : 0 ≤ specializedOneScaleCommon C x k := by
    unfold specializedOneScaleCommon
    positivity
  exact mul_nonneg hcommon
    (mul_nonneg
      (Real.rpow_nonneg (Real.log_nonneg (by norm_num)) _)
      (Real.rpow_nonneg hL _))

/-! ### Natural-grid Proposition 2 consumer -/

/-- The exact close-pair term appearing in the finite Cauchy package. -/
noncomputable def naturalGridSelectedPairTerm (K n : ℕ) : ℝ :=
  (5 / 2 : ℝ) *
    (Erdos448.selectedDyadicUnorderedPairCount
      (NaturalGridConcentration448.naturalGridSelectedDivisors K n) : ℝ) /
    (n.divisors.card : ℝ)

lemma naturalGrid_reducedFormalBinWeightProperty {K : ℕ} (hK : 0 < K) :
    ReducedFormalBinWeightProperty
      (NaturalGridConcentration448.naturalGridGood K)
      NaturalGridConcentration448.omegaAtLogScale
      (NaturalGridConcentration448.naturalGridWeightConstant K) := by
  intro d k hgood hk hkd
  simpa [formalScaleCoefficient,
    NaturalGridConcentration448.naturalGridWeight] using
    (NaturalGridConcentration448.one_le_naturalGridWeight_of_good
      hK hk hkd hgood)

/-- Converting `n < x` to the exact common reduced-scale cutoff. -/
lemma log_four_le_sqrtScaleCutoff {n x : ℕ}
    (hnPos : 0 < n) (hnLt : n < x) :
    Nat.log 4 n ≤ sqrtScaleCutoff x := by
  have hpowN : 4 ^ Nat.log 4 n ≤ n :=
    Nat.pow_log_le_self 4 hnPos.ne'
  have hnPred : n ≤ x - 1 := by omega
  have hpowPred : 2 ^ (2 * Nat.log 4 n) ≤ x - 1 := by
    rw [← four_pow_eq_two_pow_two_mul]
    exact hpowN.trans hnPred
  have hlog : 2 * Nat.log 4 n ≤ Nat.log 2 (x - 1) :=
    Nat.le_log_of_pow_le (by omega) hpowPred
  unfold sqrtScaleCutoff
  omega

lemma Icc_one_log_four_subset_sqrtScaleCutoff {n x : ℕ}
    (hnPos : 0 < n) (hnLt : n < x) :
    Finset.Icc 1 (Nat.log 4 n) ⊆
      Finset.Icc 1 (sqrtScaleCutoff x) := by
  intro k hk
  have hk' := Finset.mem_Icc.mp hk
  exact Finset.mem_Icc.mpr
    ⟨hk'.1, hk'.2.trans (log_four_le_sqrtScaleCutoff hnPos hnLt)⟩

/-- The moving logarithm in Proposition 3 dominates the reflected distance
to the final square-root scale cutoff. -/
lemma specializedOneScaleLog_lower_bound
    {x k : ℕ} (hx : 3 ≤ x)
    (hk : k ∈ Finset.Icc 1 (sqrtScaleCutoff x)) :
    Real.log 2 * (sqrtScaleCutoff x + 1 - k : ℕ) ≤
      specializedOneScaleLog x k := by
  let M := sqrtScaleCutoff x
  have hM : 2 * M ≤ Nat.log 2 (x - 1) := by
    dsimp [M, sqrtScaleCutoff]
    omega
  have hxPred : x - 1 ≠ 0 := by omega
  have hpow : 2 ^ (2 * M) ≤ x - 1 := by
    exact (Nat.pow_le_pow_right (by omega) hM).trans
      (Nat.pow_log_le_self 2 hxPred)
  have hpowX : 2 ^ (2 * M) ≤ x := hpow.trans (by omega)
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogLower : ((2 * M : ℕ) : ℝ) * Real.log 2 ≤
      Real.log (x : ℝ) := by
    rw [← Real.log_pow]
    apply Real.log_le_log
    · positivity
    · exact_mod_cast hpowX
  have hL : specializedOneScaleLog x k =
      Real.log (x : ℝ) + (2 - 2 * (k : ℝ)) * Real.log 2 := by
    unfold specializedOneScaleLog
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by norm_num) (by positivity),
      Real.log_rpow (by norm_num)]
    ring
  have hkM : k ≤ M := (Finset.mem_Icc.mp hk).2
  have hcastSub : ((M + 1 - k : ℕ) : ℝ) = (M : ℝ) + 1 - k := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    rfl
  rw [hL, show sqrtScaleCutoff x = M by rfl, hcastSub]
  push_cast at hlogLower
  have hgap : 0 ≤ ((M : ℝ) + 1 - k) * Real.log 2 := by
    have hkMR : (k : ℝ) ≤ (M : ℝ) + 1 := by
      exact_mod_cast (show k ≤ M + 1 by omega)
    apply mul_nonneg
    · linarith
    · exact hlog2.le
  nlinarith

/-- Pointwise Proposition 2, enlarged to the common square-root cutoff for
all `n < x`. -/
theorem naturalGridSelectedPairTerm_le_common_scale_sum
    {K x n : ℕ} (hK : 0 < K) (hn : n ∈ positiveBelow x) :
    naturalGridSelectedPairTerm K n ≤
      (5 / 2 : ℝ) *
        NaturalGridConcentration448.naturalGridWeightConstant K *
        ∑ k ∈ Finset.Icc 1 (sqrtScaleCutoff x),
          (k : ℝ) ^ (2 / 5 : ℝ) *
            normalizedReducedFormalExpandedScaleMoment
              NaturalGridConcentration448.omegaAtLogScale n k := by
  classical
  let D := NaturalGridConcentration448.naturalGridSelectedDivisors K n
  have hnPos : 0 < n := (Finset.mem_Ico.mp hn).1
  have hnLt : n < x := (Finset.mem_Ico.mp hn).2
  have hD : D ⊆ n.divisors :=
    NaturalGridConcentration448.naturalGridSelectedDivisors_subset K n
  have hselected : ∀ d ∈ D,
      NaturalGridConcentration448.naturalGridGood K d := by
    intro d hd
    exact (Finset.mem_filter.mp hd).2
  have hProp2 :=
    five_halves_normalizedSelectedPairs_le_reducedScaleIccSum
      hnPos.ne' hD (NaturalGridConcentration448.naturalGridGood K)
      hselected NaturalGridConcentration448.omegaAtLogScale
      (NaturalGridConcentration448.naturalGridWeightConstant K)
      (NaturalGridConcentration448.naturalGridWeightConstant_pos K).le
      (naturalGrid_reducedFormalBinWeightProperty hK)
  have hsub := Icc_one_log_four_subset_sqrtScaleCutoff hnPos hnLt
  have htermNonneg : ∀ k : ℕ,
      0 ≤ (5 / 2 : ℝ) *
        NaturalGridConcentration448.naturalGridWeightConstant K *
        (k : ℝ) ^ (2 / 5 : ℝ) *
          normalizedReducedFormalExpandedScaleMoment
            NaturalGridConcentration448.omegaAtLogScale n k := by
    intro k
    apply mul_nonneg
    · apply mul_nonneg
      · exact mul_nonneg (by norm_num)
          (NaturalGridConcentration448.naturalGridWeightConstant_pos K).le
      · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    · unfold normalizedReducedFormalExpandedScaleMoment
        reducedFormalExpandedScaleMass
      exact div_nonneg (by positivity) (Nat.cast_nonneg _)
  change (5 / 2 : ℝ) *
      (Erdos448.selectedDyadicUnorderedPairCount D : ℝ) /
        (n.divisors.card : ℝ) ≤ _
  calc
    (5 / 2 : ℝ) *
          (Erdos448.selectedDyadicUnorderedPairCount D : ℝ) /
            (n.divisors.card : ℝ) ≤
        (5 / 2 : ℝ) *
          (∑ k ∈ Finset.Icc 1 (Nat.log 4 n),
            formalScaleCoefficient
                (NaturalGridConcentration448.naturalGridWeightConstant K) k *
              reducedFormalExpandedScaleMass
                NaturalGridConcentration448.omegaAtLogScale n k) /
            (n.divisors.card : ℝ) := hProp2
    _ = ∑ k ∈ Finset.Icc 1 (Nat.log 4 n),
          (5 / 2 : ℝ) *
            NaturalGridConcentration448.naturalGridWeightConstant K *
            (k : ℝ) ^ (2 / 5 : ℝ) *
              normalizedReducedFormalExpandedScaleMoment
                NaturalGridConcentration448.omegaAtLogScale n k := by
      rw [Finset.mul_sum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k hk
      unfold formalScaleCoefficient
        normalizedReducedFormalExpandedScaleMoment
      ring
    _ ≤ ∑ k ∈ Finset.Icc 1 (sqrtScaleCutoff x),
          (5 / 2 : ℝ) *
            NaturalGridConcentration448.naturalGridWeightConstant K *
            (k : ℝ) ^ (2 / 5 : ℝ) *
              normalizedReducedFormalExpandedScaleMoment
                NaturalGridConcentration448.omegaAtLogScale n k := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro k hk hnot
      exact htermNonneg k
    _ = (5 / 2 : ℝ) *
        NaturalGridConcentration448.naturalGridWeightConstant K *
        ∑ k ∈ Finset.Icc 1 (sqrtScaleCutoff x),
          (k : ℝ) ^ (2 / 5 : ℝ) *
            normalizedReducedFormalExpandedScaleMoment
              NaturalGridConcentration448.omegaAtLogScale n k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring

/-- Aggregated finite Proposition 2 with one common scale interval, ready
for Proposition 4. -/
theorem naturalGridSelectedPair_firstMoment_le_common_scale_sum
    {K x : ℕ} (hK : 0 < K) (hx : 0 < x) :
    (∑ n ∈ Finset.range x, naturalGridSelectedPairTerm K n) ≤
      ((5 / 2 : ℝ) *
        NaturalGridConcentration448.naturalGridWeightConstant K) *
        ∑ k ∈ Finset.Icc 1 (sqrtScaleCutoff x),
          (k : ℝ) ^ (2 / 5 : ℝ) *
            (∑ n ∈ positiveBelow x,
              normalizedReducedFormalExpandedScaleMoment
                NaturalGridConcentration448.omegaAtLogScale n k) := by
  classical
  have hrange : Finset.range x = insert 0 (positiveBelow x) := by
    ext n
    simp [positiveBelow]
    omega
  rw [hrange, Finset.sum_insert (by simp [positiveBelow])]
  have hzero : naturalGridSelectedPairTerm K 0 = 0 := by
    simp [naturalGridSelectedPairTerm,
      NaturalGridConcentration448.naturalGridSelectedDivisors]
  rw [hzero, zero_add]
  calc
    (∑ n ∈ positiveBelow x, naturalGridSelectedPairTerm K n) ≤
        ∑ n ∈ positiveBelow x,
          ((5 / 2 : ℝ) *
            NaturalGridConcentration448.naturalGridWeightConstant K *
            ∑ k ∈ Finset.Icc 1 (sqrtScaleCutoff x),
              (k : ℝ) ^ (2 / 5 : ℝ) *
                normalizedReducedFormalExpandedScaleMoment
                  NaturalGridConcentration448.omegaAtLogScale n k) := by
      exact Finset.sum_le_sum fun n hn ↦
        naturalGridSelectedPairTerm_le_common_scale_sum hK hn
    _ = ((5 / 2 : ℝ) *
          NaturalGridConcentration448.naturalGridWeightConstant K) *
        ∑ k ∈ Finset.Icc 1 (sqrtScaleCutoff x),
          (k : ℝ) ^ (2 / 5 : ℝ) *
            (∑ n ∈ positiveBelow x,
              normalizedReducedFormalExpandedScaleMoment
                NaturalGridConcentration448.omegaAtLogScale n k) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]

/-- The explicit fixed-`K` constant obtained after feeding the common-scale
Proposition 2 bound and the specialized one-scale estimate into Proposition
4. -/
noncomputable def naturalGridProp4Constant (K : ℕ) (C₀ : ℝ) : ℝ :=
  Erdos448.prop4SummationConstant
    ((2 / 5 : ℝ) + (-(5 : ℝ) / 4)) (-(1 : ℝ) / 4)
    (Real.log 2) ((Real.log 2) ^ ((1 : ℝ) / 4))
    (((5 / 2 : ℝ) *
        NaturalGridConcentration448.naturalGridWeightConstant K) *
      (C₀ * (Real.log 2) ^ (-(1 : ℝ) / 2)))

lemma naturalGridProp4Constant_nonneg (K : ℕ) {C₀ : ℝ}
    (hC₀ : 0 ≤ C₀) : 0 ≤ naturalGridProp4Constant K C₀ := by
  unfold naturalGridProp4Constant
  apply Erdos448.prop4SummationConstant_nonneg
  · exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  · exact Real.rpow_nonneg (Real.log_nonneg (by norm_num)) _
  · exact mul_nonneg
      (mul_nonneg (by norm_num)
        (NaturalGridConcentration448.naturalGridWeightConstant_pos K).le)
      (mul_nonneg hC₀
        (Real.rpow_nonneg (Real.log_nonneg (by norm_num)) _))

/-- Complete finite Proposition-4 consumer.  Its only hypothesis is the
specialized one-scale analytic estimate on the authoritative reduced mass;
the selector, normalization, common cutoff, moving-log lower bound, and
all exponent arithmetic are discharged here. -/
theorem naturalGridSelectedPair_firstMoment_le_of_one_scale
    {K x : ℕ} (hK : 0 < K) (hx : 3 ≤ x) {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hOneScale : ∀ k ∈ Finset.Icc 1 (sqrtScaleCutoff x),
      (∑ n ∈ positiveBelow x,
        normalizedReducedFormalExpandedScaleMoment
          NaturalGridConcentration448.omegaAtLogScale n k) ≤
        C₀ * (x : ℝ) * (Real.log 2) ^ (-(1 : ℝ) / 2) *
          (k : ℝ) ^ (-(5 : ℝ) / 4) *
            ((k : ℝ) ^ (-(1 : ℝ) / 4) +
              (specializedOneScaleLog x k) ^ (-(1 : ℝ) / 4) +
              (Real.log 2) ^ ((1 : ℝ) / 4) *
                (specializedOneScaleLog x k) ^ (-(1 : ℝ) / 2))) :
    (∑ n ∈ Finset.range x, naturalGridSelectedPairTerm K n) ≤
      naturalGridProp4Constant K C₀ * (x : ℝ) := by
  let A : ℝ := (5 / 2 : ℝ) *
    NaturalGridConcentration448.naturalGridWeightConstant K
  let B : ℝ := C₀ * (Real.log 2) ^ (-(1 : ℝ) / 2)
  let C : ℝ := (Real.log 2) ^ ((1 : ℝ) / 4)
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (by norm_num)
      (NaturalGridConcentration448.naturalGridWeightConstant_pos K).le
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg hC₀ (Real.rpow_nonneg hlog2.le _)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact Real.rpow_nonneg hlog2.le _
  have hProp2 :
      (∑ n ∈ Finset.range x, naturalGridSelectedPairTerm K n) ≤
        A * ∑ k ∈ Finset.Icc 1 (sqrtScaleCutoff x),
          (k : ℝ) ^ (2 / 5 : ℝ) *
            (∑ n ∈ positiveBelow x,
              normalizedReducedFormalExpandedScaleMoment
                NaturalGridConcentration448.omegaAtLogScale n k) := by
    simpa only [A] using
      naturalGridSelectedPair_firstMoment_le_common_scale_sum hK
        (by omega : 0 < x)
  have hProp3 : ∀ k ∈ Finset.Icc 1 (sqrtScaleCutoff x),
      (∑ n ∈ positiveBelow x,
        normalizedReducedFormalExpandedScaleMoment
          NaturalGridConcentration448.omegaAtLogScale n k) ≤
        B * (x : ℝ) * (k : ℝ) ^ (-(5 : ℝ) / 4) *
          ((k : ℝ) ^ (-(1 : ℝ) / 4) +
            (specializedOneScaleLog x k) ^ (-(1 : ℝ) / 4) +
            C * (specializedOneScaleLog x k) ^ (-(1 : ℝ) / 2)) := by
    intro k hk
    convert hOneScale k hk using 1 <;> dsimp [B, C] <;> ring
  have hfinal := Erdos448.prop4_of_prop2_prop3_at
    (c := (2 / 5 : ℝ)) (q := (-(5 : ℝ) / 4))
    (b := (-(1 : ℝ) / 4)) (δ := Real.log 2)
    (C := C) (A := A) (B := B)
    (by norm_num : (2 / 5 : ℝ) + (-(5 : ℝ) / 4) < 0)
    (by norm_num : (-(1 : ℝ) / 4) < 0)
    (by norm_num :
      ((2 / 5 : ℝ) + (-(5 : ℝ) / 4)) + (-(1 : ℝ) / 4) < -1)
    (by norm_num :
      ((2 / 5 : ℝ) + (-(5 : ℝ) / 4)) - 1 / 2 < -1)
    hlog2 hC hA hB
    (∑ n ∈ Finset.range x, naturalGridSelectedPairTerm K n)
    (fun k ↦ ∑ n ∈ positiveBelow x,
      normalizedReducedFormalExpandedScaleMoment
        NaturalGridConcentration448.omegaAtLogScale n k)
    (specializedOneScaleLog x) (sqrtScaleCutoff x) x
    (fun k hk ↦ specializedOneScaleLog_lower_bound hx hk)
    hProp2 hProp3
  simpa [naturalGridProp4Constant, A, B, C] using hfinal

/-- End-to-end finite assembly stated directly with the three analytic
regime estimates.  Replacing these three inputs by the concrete HR bounds
is the sole remaining analytic connection. -/
theorem naturalGridSelectedPair_firstMoment_le_of_three_regimes
    {K x : ℕ} (hK : 0 < K) (hx : 3 ≤ x) {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hLong : ∀ k ∈ Finset.Icc 1 (sqrtScaleCutoff x),
      reducedFormalExpandedScaleRegimeContribution
        NaturalGridConcentration448.omegaAtLogScale x k .long ≤
          specializedOneScaleCommon C₀ x k *
            (k : ℝ) ^ (-(1 : ℝ) / 4))
    (hMiddle : ∀ k ∈ Finset.Icc 1 (sqrtScaleCutoff x),
      reducedFormalExpandedScaleRegimeContribution
        NaturalGridConcentration448.omegaAtLogScale x k .middle ≤
          specializedOneScaleCommon C₀ x k *
            (specializedOneScaleLog x k) ^ (-(1 : ℝ) / 4))
    (hShort : ∀ k ∈ Finset.Icc 1 (sqrtScaleCutoff x),
      reducedFormalExpandedScaleRegimeContribution
        NaturalGridConcentration448.omegaAtLogScale x k .short ≤
          specializedOneScaleCommon C₀ x k *
            ((Real.log 2) ^ ((1 : ℝ) / 4) *
              (specializedOneScaleLog x k) ^ (-(1 : ℝ) / 2))) :
    (∑ n ∈ Finset.range x, naturalGridSelectedPairTerm K n) ≤
      naturalGridProp4Constant K C₀ * (x : ℝ) := by
  apply naturalGridSelectedPair_firstMoment_le_of_one_scale hK hx hC₀
  intro k hk
  exact normalizedReducedFormalExpandedScaleMoment_one_scale_bound
    NaturalGridConcentration448.omegaAtLogScale C₀ x k
    (hLong k hk) (hMiddle k hk) (hShort k hk)

/-- Final finite Prop2--Prop4 consumer with only the two nonempty analytic
regimes. -/
theorem naturalGridSelectedPair_firstMoment_le_of_two_regimes
    {K x : ℕ} (hK : 0 < K) (hx : 3 ≤ x) {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hLong : ∀ k ∈ Finset.Icc 1 (sqrtScaleCutoff x),
      reducedFormalExpandedScaleRegimeContribution
        NaturalGridConcentration448.omegaAtLogScale x k .long ≤
          specializedOneScaleCommon C₀ x k *
            (k : ℝ) ^ (-(1 : ℝ) / 4))
    (hMiddle : ∀ k ∈ Finset.Icc 1 (sqrtScaleCutoff x),
      reducedFormalExpandedScaleRegimeContribution
        NaturalGridConcentration448.omegaAtLogScale x k .middle ≤
          specializedOneScaleCommon C₀ x k *
            (specializedOneScaleLog x k) ^ (-(1 : ℝ) / 4)) :
    (∑ n ∈ Finset.range x, naturalGridSelectedPairTerm K n) ≤
      naturalGridProp4Constant K C₀ * (x : ℝ) := by
  apply naturalGridSelectedPair_firstMoment_le_of_one_scale hK hx hC₀
  intro k hk
  have hLlower := specializedOneScaleLog_lower_bound hx hk
  have hL : 0 ≤ specializedOneScaleLog x k := by
    have hleft : 0 ≤ Real.log 2 *
        (sqrtScaleCutoff x + 1 - k : ℕ) := by positivity
    exact hleft.trans hLlower
  exact normalizedReducedFormalExpandedScaleMoment_one_scale_bound_two_regimes
    NaturalGridConcentration448.omegaAtLogScale hC₀ x k hL
    (hLong k hk) (hMiddle k hk)

/-- Direct consumer for the concrete post-first-shift pair/`t` sums. -/
theorem naturalGridSelectedPair_firstMoment_le_of_pair_t
    {K x : ℕ} (hK : 0 < K) (hx : 3 ≤ x) {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hLong : ∀ k ∈ Finset.Icc 1 (sqrtScaleCutoff x),
      reducedFormalPairTFirstShiftedContribution x k .long ≤
        specializedOneScaleCommon C₀ x k *
          (k : ℝ) ^ (-(1 : ℝ) / 4))
    (hMiddle : ∀ k ∈ Finset.Icc 1 (sqrtScaleCutoff x),
      reducedFormalPairTFirstShiftedContribution x k .middle ≤
        specializedOneScaleCommon C₀ x k *
          (specializedOneScaleLog x k) ^ (-(1 : ℝ) / 4)) :
    (∑ n ∈ Finset.range x, naturalGridSelectedPairTerm K n) ≤
      naturalGridProp4Constant K C₀ * (x : ℝ) := by
  apply naturalGridSelectedPair_firstMoment_le_of_two_regimes hK hx hC₀
  · intro k hk
    exact (naturalGrid_reduced_regime_le_pair_t x k .long).trans
      (hLong k hk)
  · intro k hk
    exact (naturalGrid_reduced_regime_le_pair_t x k .middle).trans
      (hMiddle k hk)

/-- Eventual wrapper around the finite two-regime consumer. -/
theorem naturalGridSelectedPair_eventually_linear_of_two_regimes
    {K : ℕ} (hK : 0 < K) {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hAnalytic : ∀ᶠ x : ℕ in Filter.atTop,
      3 ≤ x ∧
      (∀ k ∈ Finset.Icc 1 (sqrtScaleCutoff x),
        reducedFormalExpandedScaleRegimeContribution
          NaturalGridConcentration448.omegaAtLogScale x k .long ≤
            specializedOneScaleCommon C₀ x k *
              (k : ℝ) ^ (-(1 : ℝ) / 4)) ∧
      (∀ k ∈ Finset.Icc 1 (sqrtScaleCutoff x),
        reducedFormalExpandedScaleRegimeContribution
          NaturalGridConcentration448.omegaAtLogScale x k .middle ≤
            specializedOneScaleCommon C₀ x k *
              (specializedOneScaleLog x k) ^ (-(1 : ℝ) / 4))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x : ℕ in Filter.atTop,
      (∑ n ∈ Finset.range x, naturalGridSelectedPairTerm K n) ≤
        C * (x : ℝ) := by
  refine ⟨naturalGridProp4Constant K C₀,
    naturalGridProp4Constant_nonneg K hC₀, ?_⟩
  filter_upwards [hAnalytic] with x hx
  exact naturalGridSelectedPair_firstMoment_le_of_two_regimes
    hK hx.1 hC₀ hx.2.1 hx.2.2

theorem naturalGridSelectedPair_eventually_linear_of_pair_t
    {K : ℕ} (hK : 0 < K) {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hAnalytic : ∀ᶠ x : ℕ in Filter.atTop,
      3 ≤ x ∧
      (∀ k ∈ Finset.Icc 1 (sqrtScaleCutoff x),
        reducedFormalPairTFirstShiftedContribution x k .long ≤
          specializedOneScaleCommon C₀ x k *
            (k : ℝ) ^ (-(1 : ℝ) / 4)) ∧
      (∀ k ∈ Finset.Icc 1 (sqrtScaleCutoff x),
        reducedFormalPairTFirstShiftedContribution x k .middle ≤
          specializedOneScaleCommon C₀ x k *
            (specializedOneScaleLog x k) ^ (-(1 : ℝ) / 4))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x : ℕ in Filter.atTop,
      (∑ n ∈ Finset.range x, naturalGridSelectedPairTerm K n) ≤
        C * (x : ℝ) := by
  refine ⟨naturalGridProp4Constant K C₀,
    naturalGridProp4Constant_nonneg K hC₀, ?_⟩
  filter_upwards [hAnalytic] with x hx
  exact naturalGridSelectedPair_firstMoment_le_of_pair_t
    hK hx.1 hC₀ hx.2.1 hx.2.2

/-! ### Unconditional analytic discharge -/

lemma concreteWeightedFirstShiftedBoundAll_eq_cutoff
    (x : ℕ) (p : ℕ × ℕ) (t : ℕ) :
    concreteWeightedFirstShiftedBoundAll x (p, t) =
      FirstShiftedSmall448.weightedFirstShiftedBoundAll x
        ((p.1 * p.2) * t) := by
  rfl

lemma reducedFormalPair_product_pos {x k : ℕ} {regime : ScaleRegime}
    {p : ℕ × ℕ} (hp : p ∈ reducedFormalPairRegimeIndices x k regime) :
    0 < p.1 * p.2 := by
  have hpRange := (Finset.mem_filter.mp hp).1
  rcases Finset.mem_product.mp hpRange with ⟨hd, hd'⟩
  exact Nat.mul_pos (Finset.mem_Ico.mp hd).1 (Finset.mem_Ico.mp hd').1

lemma reducedFormalPair_product_lt_two_pow {x k : ℕ}
    {regime : ScaleRegime} {p : ℕ × ℕ}
    (hp : p ∈ reducedFormalPairRegimeIndices x k regime) :
    p.1 * p.2 < 2 ^ (2 * k + 3) := by
  have hbase := (Finset.mem_filter.mp hp).2.1
  have hd'Pos : 0 < p.2 := by omega
  have hpowPos : 0 < 2 ^ (k + 1) := by positivity
  have hd'Upper : p.2 < 2 ^ (k + 2) := by
    calc
      p.2 < 2 * p.1 := hbase.2.2.1
      _ < 2 * 2 ^ (k + 1) :=
        Nat.mul_lt_mul_of_pos_left hbase.2.2.2.2 (by omega)
      _ = 2 ^ (k + 2) := by
        rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
        omega
  calc
    p.1 * p.2 < 2 ^ (k + 1) * p.2 :=
      Nat.mul_lt_mul_of_pos_right hbase.2.2.2.2 hd'Pos
    _ < 2 ^ (k + 1) * 2 ^ (k + 2) :=
      Nat.mul_lt_mul_of_pos_left hd'Upper hpowPos
    _ = 2 ^ (2 * k + 3) := by
      rw [← pow_add]
      congr 1
      omega

lemma ceilDiv_base_lt_of_two_le {x q z : ℕ} (hq : 0 < q)
    (hzEq : z = x ⌈/⌉ q) (hz : 2 ≤ z) : q < x := by
  by_contra hnot
  have hxq : x ≤ q := Nat.le_of_not_gt hnot
  have hceil : x ⌈/⌉ q ≤ 1 := by
    rw [ceilDiv_le_iff_le_mul hq]
    simpa using hxq
  omega

/-- The logarithmic scale in Proposition 3 is at most six times the number
of residual dyadic shells.  The harmless factor six absorbs both the
close-pair width and the five endpoint powers of two. -/
lemma specializedOneScaleLog_le_six_shellHeight
    {x k : ℕ} {p : ℕ × ℕ}
    (hp : p ∈ reducedFormalPairRegimeIndices x k .middle) :
    specializedOneScaleLog x k ≤
      6 * (Prop3CutoffShell448.shellHeight
        (x ⌈/⌉ (p.1 * p.2)) : ℝ) := by
  let q := p.1 * p.2
  let z := x ⌈/⌉ q
  let J := Prop3CutoffShell448.shellHeight z
  have hq : 0 < q := reducedFormalPair_product_pos hp
  have hreg := (Finset.mem_filter.mp hp).2.2
  have hz : 2 ≤ z := by
    rw [scaleRegime_eq_middle_iff] at hreg
    exact hreg.1
  have hqUpper : q < 2 ^ (2 * k + 3) :=
    reducedFormalPair_product_lt_two_pow hp
  have hxqz : x ≤ q * z := by
    dsimp [z]
    exact (ceilDiv_le_iff_le_mul hq).1 le_rfl
  have hzPow : z ≤ 2 ^ J := by
    dsimp [J]
    exact Prop3CutoffShell448.le_pow_shellHeight hz
  have hqzPow : q * z < 2 ^ (2 * k + 3 + J) := by
    calc
      q * z < 2 ^ (2 * k + 3) * z :=
        Nat.mul_lt_mul_of_pos_right hqUpper (by omega)
      _ ≤ 2 ^ (2 * k + 3) * 2 ^ J :=
        Nat.mul_le_mul_left _ hzPow
      _ = 2 ^ (2 * k + 3 + J) := by rw [← pow_add]
  have hxPow : x ≤ 2 ^ (2 * k + 3 + J) := hxqz.trans hqzPow.le
  have hxPos : 0 < x := by
    have hqx : q < x := ceilDiv_base_lt_of_two_le hq rfl hz
    omega
  have hlogX : Real.log (x : ℝ) ≤
      ((2 * k + 3 + J : ℕ) : ℝ) * Real.log 2 := by
    rw [← Real.log_pow]
    apply Real.log_le_log
    · positivity
    · exact_mod_cast hxPow
  have hL : specializedOneScaleLog x k =
      Real.log (x : ℝ) + (2 - 2 * (k : ℝ)) * Real.log 2 := by
    unfold specializedOneScaleLog
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by norm_num) (by positivity),
      Real.log_rpow (by norm_num)]
    ring
  have hlogTwoLe : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hJ : 1 ≤ J := Prop3CutoffShell448.one_le_shellHeight
  have hpre : specializedOneScaleLog x k ≤
      ((J : ℝ) + 5) * Real.log 2 := by
    rw [hL]
    push_cast at hlogX
    nlinarith
  calc
    specializedOneScaleLog x k ≤
        ((J : ℝ) + 5) * Real.log 2 := hpre
    _ ≤ ((J : ℝ) + 5) * 1 := by
      gcongr
    _ ≤ 6 * (J : ℝ) := by
      norm_num
      exact_mod_cast (show J + 5 ≤ 6 * J by omega)
    _ = _ := by rfl

lemma shellHeight_rpow_neg_quarter_le_six_mul
    {L : ℝ} {J : ℕ} (hL : 0 < L) (hJ : 1 ≤ J)
    (hLJ : L ≤ 6 * (J : ℝ)) :
    (J : ℝ) ^ (-(1 : ℝ) / 4) ≤
      6 * L ^ (-(1 : ℝ) / 4) := by
  have h6J : 0 < 6 * (J : ℝ) := by positivity
  have hp := Real.rpow_le_rpow_of_nonpos hL hLJ
    (by norm_num : (-(1 : ℝ) / 4) ≤ 0)
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 6)
      (by positivity : (0 : ℝ) ≤ (J : ℝ))] at hp
  have hp' := mul_le_mul_of_nonneg_left hp
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 6) (1 / 4 : ℝ))
  have hcancel : (6 : ℝ) ^ (1 / 4 : ℝ) *
      ((6 : ℝ) ^ (-(1 : ℝ) / 4) *
        (J : ℝ) ^ (-(1 : ℝ) / 4)) =
      (J : ℝ) ^ (-(1 : ℝ) / 4) := by
    rw [← mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 6)]
    norm_num
  have hsix : (6 : ℝ) ^ (1 / 4 : ℝ) ≤ 6 :=
    Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)
  calc
    (J : ℝ) ^ (-(1 : ℝ) / 4) =
        (6 : ℝ) ^ (1 / 4 : ℝ) *
          ((6 : ℝ) ^ (-(1 : ℝ) / 4) *
            (J : ℝ) ^ (-(1 : ℝ) / 4)) := hcancel.symm
    _ ≤ (6 : ℝ) ^ (1 / 4 : ℝ) *
        L ^ (-(1 : ℝ) / 4) := hp'
    _ ≤ 6 * L ^ (-(1 : ℝ) / 4) :=
      mul_le_mul_of_nonneg_right hsix (Real.rpow_nonneg hL.le _)

lemma reducedFormalPair_ceilDiv_le_scale
    {x k : ℕ} {regime : ScaleRegime} {p : ℕ × ℕ}
    (hp : p ∈ reducedFormalPairRegimeIndices x k regime)
    (hz : 2 ≤ x ⌈/⌉ (p.1 * p.2)) :
    ((x ⌈/⌉ (p.1 * p.2) : ℕ) : ℝ) ≤
      2 * (x : ℝ) / (2 : ℝ) ^ (2 * k) := by
  have hq : 0 < p.1 * p.2 := reducedFormalPair_product_pos hp
  have hqx : p.1 * p.2 < x := ceilDiv_base_lt_of_two_le hq rfl hz
  have hscale := two_pow_two_k_le_pair_product
    (Finset.mem_filter.mp hp).2.1
  calc
    ((x ⌈/⌉ (p.1 * p.2) : ℕ) : ℝ) ≤
        2 * (x : ℝ) / (p.1 * p.2 : ℕ) :=
      cast_ceilDiv_le_two_mul_div hq hqx
    _ ≤ 2 * (x : ℝ) / (2 : ℝ) ^ (2 * k) := by
      apply div_le_div_of_nonneg_left
      · positivity
      · positivity
      · exact hscale

lemma secondCorrectionWeight_nonneg (k n : ℕ) :
    0 ≤ Prop3WeightedT448.hybridCorrectionWeight
      Prop3WeightedT448.sharpShiftedReciprocalWeightAF
      (Prop3WeightedT448.omegaWeightAF k) n := by
  simpa using Prop3W2Close448.secondCorrectionWeightAF_nonneg k n

/-- Fully concrete long-range pair/`t` estimate, before the final
close-pair mean is inserted. -/
theorem reducedFormalPairTFirstShiftedContribution_long_le
    (x k : ℕ) (hk : 1 ≤ k) :
    reducedFormalPairTFirstShiftedContribution x k .long ≤
      (12 * Prop3CutoffShell448.cutoffShellConstant * (x : ℝ) /
          (2 : ℝ) ^ (2 * k) * (k : ℝ) ^ (-(1 : ℝ) / 4)) *
        Prop3ClosePair448.formalDyadicClosePairMean
          (Prop3WeightedT448.hybridCorrectionWeight
            Prop3WeightedT448.sharpShiftedReciprocalWeightAF
            (Prop3WeightedT448.omegaWeightAF k)) k := by
  unfold reducedFormalPairTFirstShiftedContribution
  apply reducedFormalPairInnerSum_le_closePairMean
    (inner := fun p ↦ ∑ t ∈ Finset.Ico 1 (x ⌈/⌉ (p.1 * p.2)),
      Prop3WeightedT448.omegaWeight k t *
        concreteWeightedFirstShiftedBoundAll x (p, t))
    (w := Prop3WeightedT448.hybridCorrectionWeight
      Prop3WeightedT448.sharpShiftedReciprocalWeightAF
      (Prop3WeightedT448.omegaWeightAF k))
  · exact mul_nonneg
      (div_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num)
            Prop3CutoffShell448.cutoffShellConstant_nonneg)
          (Nat.cast_nonneg x))
        (pow_nonneg (by norm_num) _))
      (Real.rpow_nonneg (Nat.cast_nonneg k) _)
  · exact secondCorrectionWeight_nonneg k
  · intro p hp
    let q := p.1 * p.2
    let z := x ⌈/⌉ q
    have hq : 0 < q := reducedFormalPair_product_pos hp
    have hreg := (Finset.mem_filter.mp hp).2.2
    have hlong : 2 ^ k ≤ z :=
      (scaleRegime_eq_long_iff 2 (2 ^ k) z).mp hreg
    have hz : 2 ≤ z := by
      have htwo : 2 ≤ 2 ^ k := by
        have := Nat.pow_le_pow_right (by norm_num : 0 < 2) hk
        simpa using this
      exact htwo.trans hlong
    have hshell := Prop3CutoffShell448.cutoffFirstShiftedSum_long_le
      hq rfl hk hlong
    have hzBound : (z : ℝ) ≤
        2 * (x : ℝ) / (2 : ℝ) ^ (2 * k) := by
      simpa [q, z] using reducedFormalPair_ceilDiv_le_scale hp (by simpa [q, z] using hz)
    have hrest : 0 ≤ Prop3CutoffShell448.cutoffShellConstant *
        Prop3WeightedT448.hybridCorrectionWeight
          Prop3WeightedT448.sharpShiftedReciprocalWeightAF
          (Prop3WeightedT448.omegaWeightAF k) q *
        (k : ℝ) ^ (-(1 : ℝ) / 4) := by
      exact mul_nonneg
        (mul_nonneg Prop3CutoffShell448.cutoffShellConstant_nonneg
          (secondCorrectionWeight_nonneg k q))
        (Real.rpow_nonneg (Nat.cast_nonneg k) _)
    calc
      (∑ t ∈ Finset.Ico 1 (x ⌈/⌉ (p.1 * p.2)),
          Prop3WeightedT448.omegaWeight k t *
            concreteWeightedFirstShiftedBoundAll x (p, t)) =
          Prop3CutoffShell448.cutoffFirstShiftedSum x q k := by
        unfold Prop3CutoffShell448.cutoffFirstShiftedSum
        simp only [q, concreteWeightedFirstShiftedBoundAll_eq_cutoff]
      _ ≤ Prop3CutoffShell448.cutoffShellConstant * (z : ℝ) *
          Prop3WeightedT448.hybridCorrectionWeight
            Prop3WeightedT448.sharpShiftedReciprocalWeightAF
            (Prop3WeightedT448.omegaWeightAF k) q *
          (k : ℝ) ^ (-(1 : ℝ) / 4) := hshell
      _ ≤ Prop3CutoffShell448.cutoffShellConstant *
          (2 * (x : ℝ) / (2 : ℝ) ^ (2 * k)) *
          Prop3WeightedT448.hybridCorrectionWeight
            Prop3WeightedT448.sharpShiftedReciprocalWeightAF
            (Prop3WeightedT448.omegaWeightAF k) q *
          (k : ℝ) ^ (-(1 : ℝ) / 4) := by
        have hm := mul_le_mul_of_nonneg_right hzBound hrest
        calc
          _ = (z : ℝ) *
              (Prop3CutoffShell448.cutoffShellConstant *
                Prop3WeightedT448.hybridCorrectionWeight
                  Prop3WeightedT448.sharpShiftedReciprocalWeightAF
                  (Prop3WeightedT448.omegaWeightAF k) q *
                (k : ℝ) ^ (-(1 : ℝ) / 4)) := by ring
          _ ≤ (2 * (x : ℝ) / (2 : ℝ) ^ (2 * k)) *
              (Prop3CutoffShell448.cutoffShellConstant *
                Prop3WeightedT448.hybridCorrectionWeight
                  Prop3WeightedT448.sharpShiftedReciprocalWeightAF
                  (Prop3WeightedT448.omegaWeightAF k) q *
                (k : ℝ) ^ (-(1 : ℝ) / 4)) := hm
          _ = _ := by ring
      _ ≤ (12 * Prop3CutoffShell448.cutoffShellConstant * (x : ℝ) /
            (2 : ℝ) ^ (2 * k) * (k : ℝ) ^ (-(1 : ℝ) / 4)) *
          Prop3WeightedT448.hybridCorrectionWeight
            Prop3WeightedT448.sharpShiftedReciprocalWeightAF
            (Prop3WeightedT448.omegaWeightAF k) (p.1 * p.2) := by
        let R : ℝ := Prop3CutoffShell448.cutoffShellConstant *
            (x : ℝ) / (2 : ℝ) ^ (2 * k) *
            (k : ℝ) ^ (-(1 : ℝ) / 4) *
            Prop3WeightedT448.hybridCorrectionWeight
              Prop3WeightedT448.sharpShiftedReciprocalWeightAF
              (Prop3WeightedT448.omegaWeightAF k) q
        have hR : 0 ≤ R := by
          dsimp [R]
          exact mul_nonneg
            (mul_nonneg
              (div_nonneg
                (mul_nonneg Prop3CutoffShell448.cutoffShellConstant_nonneg
                  (Nat.cast_nonneg x))
                (pow_nonneg (by norm_num) _))
              (Real.rpow_nonneg (Nat.cast_nonneg k) _))
            (secondCorrectionWeight_nonneg k q)
        have hmul := mul_le_mul_of_nonneg_right
          (show (2 : ℝ) ≤ 12 by norm_num) hR
        calc
          _ = 2 * R := by simp [q, R]; ring
          _ ≤ 12 * R := hmul
          _ = _ := by simp [q, R]; ring

/-- Fully concrete middle-range pair/`t` estimate. -/
theorem reducedFormalPairTFirstShiftedContribution_middle_le
    (x k : ℕ) (hk : 1 ≤ k) (hL : 0 < specializedOneScaleLog x k) :
    reducedFormalPairTFirstShiftedContribution x k .middle ≤
      (12 * Prop3CutoffShell448.cutoffShellConstant * (x : ℝ) /
          (2 : ℝ) ^ (2 * k) *
          (specializedOneScaleLog x k) ^ (-(1 : ℝ) / 4)) *
        Prop3ClosePair448.formalDyadicClosePairMean
          (Prop3WeightedT448.hybridCorrectionWeight
            Prop3WeightedT448.sharpShiftedReciprocalWeightAF
            (Prop3WeightedT448.omegaWeightAF k)) k := by
  unfold reducedFormalPairTFirstShiftedContribution
  apply reducedFormalPairInnerSum_le_closePairMean
    (inner := fun p ↦ ∑ t ∈ Finset.Ico 1 (x ⌈/⌉ (p.1 * p.2)),
      Prop3WeightedT448.omegaWeight k t *
        concreteWeightedFirstShiftedBoundAll x (p, t))
    (w := Prop3WeightedT448.hybridCorrectionWeight
      Prop3WeightedT448.sharpShiftedReciprocalWeightAF
      (Prop3WeightedT448.omegaWeightAF k))
  · exact mul_nonneg
      (div_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num)
            Prop3CutoffShell448.cutoffShellConstant_nonneg)
          (Nat.cast_nonneg x))
        (pow_nonneg (by norm_num) _))
      (Real.rpow_nonneg hL.le _)
  · exact secondCorrectionWeight_nonneg k
  · intro p hp
    let q := p.1 * p.2
    let z := x ⌈/⌉ q
    let J := Prop3CutoffShell448.shellHeight z
    have hq : 0 < q := reducedFormalPair_product_pos hp
    have hreg := (Finset.mem_filter.mp hp).2.2
    have hzData := (scaleRegime_eq_middle_iff 2 (2 ^ k) z).mp hreg
    have hz : 2 ≤ z := hzData.1
    have hmiddle : z < 2 ^ k := hzData.2
    have hshell := Prop3CutoffShell448.cutoffFirstShiftedSum_middle_le
      hq rfl hz hk hmiddle
    have hzBound : (z : ℝ) ≤
        2 * (x : ℝ) / (2 : ℝ) ^ (2 * k) := by
      simpa [q, z] using reducedFormalPair_ceilDiv_le_scale hp (by simpa [q, z] using hz)
    have hJ : 1 ≤ J := Prop3CutoffShell448.one_le_shellHeight
    have hLJ : specializedOneScaleLog x k ≤ 6 * (J : ℝ) := by
      simpa [q, z, J] using specializedOneScaleLog_le_six_shellHeight hp
    have hpow : (J : ℝ) ^ (-(1 : ℝ) / 4) ≤
        6 * (specializedOneScaleLog x k) ^ (-(1 : ℝ) / 4) :=
      shellHeight_rpow_neg_quarter_le_six_mul hL hJ hLJ
    have hW : 0 ≤ Prop3WeightedT448.hybridCorrectionWeight
        Prop3WeightedT448.sharpShiftedReciprocalWeightAF
        (Prop3WeightedT448.omegaWeightAF k) q :=
      secondCorrectionWeight_nonneg k q
    calc
      (∑ t ∈ Finset.Ico 1 (x ⌈/⌉ (p.1 * p.2)),
          Prop3WeightedT448.omegaWeight k t *
            concreteWeightedFirstShiftedBoundAll x (p, t)) =
          Prop3CutoffShell448.cutoffFirstShiftedSum x q k := by
        unfold Prop3CutoffShell448.cutoffFirstShiftedSum
        simp only [q, concreteWeightedFirstShiftedBoundAll_eq_cutoff]
      _ ≤ Prop3CutoffShell448.cutoffShellConstant * (z : ℝ) *
          Prop3WeightedT448.hybridCorrectionWeight
            Prop3WeightedT448.sharpShiftedReciprocalWeightAF
            (Prop3WeightedT448.omegaWeightAF k) q *
          (J : ℝ) ^ (-(1 : ℝ) / 4) := hshell
      _ ≤ Prop3CutoffShell448.cutoffShellConstant *
          (2 * (x : ℝ) / (2 : ℝ) ^ (2 * k)) *
          Prop3WeightedT448.hybridCorrectionWeight
            Prop3WeightedT448.sharpShiftedReciprocalWeightAF
            (Prop3WeightedT448.omegaWeightAF k) q *
          (6 * (specializedOneScaleLog x k) ^ (-(1 : ℝ) / 4)) := by
        have hJpow : 0 ≤ (J : ℝ) ^ (-(1 : ℝ) / 4) :=
          Real.rpow_nonneg (Nat.cast_nonneg J) _
        have hscaleNonneg : 0 ≤
            2 * (x : ℝ) / (2 : ℝ) ^ (2 * k) := by positivity
        have hzStep := mul_le_mul_of_nonneg_right hzBound
          (mul_nonneg
            (mul_nonneg Prop3CutoffShell448.cutoffShellConstant_nonneg hW)
            hJpow)
        have hpowStep := mul_le_mul_of_nonneg_left hpow
          (mul_nonneg
            (mul_nonneg Prop3CutoffShell448.cutoffShellConstant_nonneg
              hscaleNonneg) hW)
        calc
          _ = (z : ℝ) *
              (Prop3CutoffShell448.cutoffShellConstant *
                Prop3WeightedT448.hybridCorrectionWeight
                  Prop3WeightedT448.sharpShiftedReciprocalWeightAF
                  (Prop3WeightedT448.omegaWeightAF k) q *
                (J : ℝ) ^ (-(1 : ℝ) / 4)) := by ring
          _ ≤ (2 * (x : ℝ) / (2 : ℝ) ^ (2 * k)) *
              (Prop3CutoffShell448.cutoffShellConstant *
                Prop3WeightedT448.hybridCorrectionWeight
                  Prop3WeightedT448.sharpShiftedReciprocalWeightAF
                  (Prop3WeightedT448.omegaWeightAF k) q *
                (J : ℝ) ^ (-(1 : ℝ) / 4)) := hzStep
          _ = Prop3CutoffShell448.cutoffShellConstant *
              (2 * (x : ℝ) / (2 : ℝ) ^ (2 * k)) *
              Prop3WeightedT448.hybridCorrectionWeight
                Prop3WeightedT448.sharpShiftedReciprocalWeightAF
                (Prop3WeightedT448.omegaWeightAF k) q *
              (J : ℝ) ^ (-(1 : ℝ) / 4) := by ring
          _ ≤ _ := hpowStep
      _ = (12 * Prop3CutoffShell448.cutoffShellConstant * (x : ℝ) /
            (2 : ℝ) ^ (2 * k) *
            (specializedOneScaleLog x k) ^ (-(1 : ℝ) / 4)) *
          Prop3WeightedT448.hybridCorrectionWeight
            Prop3WeightedT448.sharpShiftedReciprocalWeightAF
            (Prop3WeightedT448.omegaWeightAF k) (p.1 * p.2) := by
        simp [q]
        ring

/-- Uniform constant in the unconditional reduced one-scale estimate. -/
noncomputable def concreteReducedOneScaleConstant : ℝ :=
  12 * Prop3CutoffShell448.cutoffShellConstant *
    Prop3W2Close448.secondFormalClosePairConstant /
      (Real.log 2) ^ (-(1 : ℝ) / 2)

lemma concreteReducedOneScaleConstant_nonneg :
    0 ≤ concreteReducedOneScaleConstant := by
  unfold concreteReducedOneScaleConstant
  exact div_nonneg
    (mul_nonneg
      (mul_nonneg (by norm_num)
        Prop3CutoffShell448.cutoffShellConstant_nonneg)
      Prop3W2Close448.secondFormalClosePairConstant_nonneg)
    (Real.rpow_nonneg (Real.log_nonneg (by norm_num)) _)

lemma log_two_rpow_half_mul_neg_half :
    (Real.log 2) ^ ((1 : ℝ) / 2) *
      (Real.log 2) ^ (-(1 : ℝ) / 2) = 1 := by
  rw [← Real.rpow_add (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
  norm_num

/-- The long residual range satisfies the exact one-scale bound with no
remaining analytic hypotheses. -/
theorem reducedFormalPairTFirstShiftedContribution_long_unconditional
    (x k : ℕ) (hk : 1 ≤ k) :
    reducedFormalPairTFirstShiftedContribution x k .long ≤
      specializedOneScaleCommon concreteReducedOneScaleConstant x k *
        (k : ℝ) ^ (-(1 : ℝ) / 4) := by
  have hfirst := reducedFormalPairTFirstShiftedContribution_long_le x k hk
  have hclose :=
    Prop3W2Close448.formalDyadicClosePairMean_secondCorrection_le k hk
  let P : ℝ := (2 : ℝ) ^ (2 * k)
  let U : ℝ := (k : ℝ) ^ (-(1 : ℝ) / 4)
  let V : ℝ := (k : ℝ) ^ (-(5 : ℝ) / 4)
  have hF : 0 ≤ 12 * Prop3CutoffShell448.cutoffShellConstant *
      (x : ℝ) / P * U := by
    dsimp [P, U]
    exact mul_nonneg
      (div_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num)
            Prop3CutoffShell448.cutoffShellConstant_nonneg)
          (Nat.cast_nonneg x))
        (pow_nonneg (by norm_num) _))
      (Real.rpow_nonneg (Nat.cast_nonneg k) _)
  have hP : 0 < P := by dsimp [P]; positivity
  calc
    reducedFormalPairTFirstShiftedContribution x k .long ≤
        (12 * Prop3CutoffShell448.cutoffShellConstant * (x : ℝ) /
            P * U) *
          Prop3ClosePair448.formalDyadicClosePairMean
            (Prop3WeightedT448.hybridCorrectionWeight
              Prop3WeightedT448.sharpShiftedReciprocalWeightAF
              (Prop3WeightedT448.omegaWeightAF k)) k := by
      simpa [P, U] using hfirst
    _ ≤ (12 * Prop3CutoffShell448.cutoffShellConstant * (x : ℝ) /
            P * U) *
          (Prop3W2Close448.secondFormalClosePairConstant * P * V) :=
      mul_le_mul_of_nonneg_left (by simpa [P, V] using hclose) hF
    _ = 12 * Prop3CutoffShell448.cutoffShellConstant *
          Prop3W2Close448.secondFormalClosePairConstant * (x : ℝ) *
          V * U := by
      field_simp [hP.ne']
    _ = specializedOneScaleCommon concreteReducedOneScaleConstant x k *
          (k : ℝ) ^ (-(1 : ℝ) / 4) := by
      unfold specializedOneScaleCommon concreteReducedOneScaleConstant
      have hlogPow : (Real.log 2) ^ (-(1 : ℝ) / 2) ≠ 0 :=
        ne_of_gt (Real.rpow_pos_of_pos
          (Real.log_pos (by norm_num : (1 : ℝ) < 2)) _)
      dsimp [V, U]
      field_simp [hlogPow]

/-- The middle residual range satisfies the moving-log one-scale bound
unconditionally. -/
theorem reducedFormalPairTFirstShiftedContribution_middle_unconditional
    (x k : ℕ) (hk : 1 ≤ k)
    (hL : 0 < specializedOneScaleLog x k) :
    reducedFormalPairTFirstShiftedContribution x k .middle ≤
      specializedOneScaleCommon concreteReducedOneScaleConstant x k *
        (specializedOneScaleLog x k) ^ (-(1 : ℝ) / 4) := by
  have hfirst := reducedFormalPairTFirstShiftedContribution_middle_le x k hk hL
  have hclose :=
    Prop3W2Close448.formalDyadicClosePairMean_secondCorrection_le k hk
  let P : ℝ := (2 : ℝ) ^ (2 * k)
  let U : ℝ := (specializedOneScaleLog x k) ^ (-(1 : ℝ) / 4)
  let V : ℝ := (k : ℝ) ^ (-(5 : ℝ) / 4)
  have hF : 0 ≤ 12 * Prop3CutoffShell448.cutoffShellConstant *
      (x : ℝ) / P * U := by
    dsimp [P, U]
    exact mul_nonneg
      (div_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num)
            Prop3CutoffShell448.cutoffShellConstant_nonneg)
          (Nat.cast_nonneg x))
        (pow_nonneg (by norm_num) _))
      (Real.rpow_nonneg hL.le _)
  have hP : 0 < P := by dsimp [P]; positivity
  calc
    reducedFormalPairTFirstShiftedContribution x k .middle ≤
        (12 * Prop3CutoffShell448.cutoffShellConstant * (x : ℝ) /
            P * U) *
          Prop3ClosePair448.formalDyadicClosePairMean
            (Prop3WeightedT448.hybridCorrectionWeight
              Prop3WeightedT448.sharpShiftedReciprocalWeightAF
              (Prop3WeightedT448.omegaWeightAF k)) k := by
      simpa [P, U] using hfirst
    _ ≤ (12 * Prop3CutoffShell448.cutoffShellConstant * (x : ℝ) /
            P * U) *
          (Prop3W2Close448.secondFormalClosePairConstant * P * V) :=
      mul_le_mul_of_nonneg_left (by simpa [P, V] using hclose) hF
    _ = 12 * Prop3CutoffShell448.cutoffShellConstant *
          Prop3W2Close448.secondFormalClosePairConstant * (x : ℝ) *
          V * U := by
      field_simp [hP.ne']
    _ = specializedOneScaleCommon concreteReducedOneScaleConstant x k *
          (specializedOneScaleLog x k) ^ (-(1 : ℝ) / 4) := by
      unfold specializedOneScaleCommon concreteReducedOneScaleConstant
      have hlogPow : (Real.log 2) ^ (-(1 : ℝ) / 2) ≠ 0 :=
        ne_of_gt (Real.rpow_pos_of_pos
          (Real.log_pos (by norm_num : (1 : ℝ) < 2)) _)
      dsimp [V, U]
      field_simp [hlogPow]

lemma specializedOneScaleLog_pos_of_mem
    {x k : ℕ} (hx : 3 ≤ x)
    (hk : k ∈ Finset.Icc 1 (sqrtScaleCutoff x)) :
    0 < specializedOneScaleLog x k := by
  have hlower := specializedOneScaleLog_lower_bound hx hk
  have hgap : 1 ≤ sqrtScaleCutoff x + 1 - k := by
    have hkM := (Finset.mem_Icc.mp hk).2
    omega
  have hpos : 0 < Real.log 2 *
      (sqrtScaleCutoff x + 1 - k : ℕ) := by positivity
  exact hpos.trans_le hlower

/-- Unconditional eventual linear first moment for the natural-grid
selected close-pair term.  This is the complete Prop2--Prop4 package used
by the final Erdős 448 argument. -/
theorem naturalGridSelectedPair_eventually_linear
    {K : ℕ} (hK : 0 < K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x : ℕ in Filter.atTop,
      (∑ n ∈ Finset.range x, naturalGridSelectedPairTerm K n) ≤
        C * (x : ℝ) := by
  apply naturalGridSelectedPair_eventually_linear_of_pair_t
    hK concreteReducedOneScaleConstant_nonneg
  filter_upwards [Filter.eventually_ge_atTop (3 : ℕ)] with x hx
  refine ⟨hx, ?_, ?_⟩
  · intro k hk
    exact reducedFormalPairTFirstShiftedContribution_long_unconditional
      x k (Finset.mem_Icc.mp hk).1
  · intro k hk
    exact reducedFormalPairTFirstShiftedContribution_middle_unconditional
      x k (Finset.mem_Icc.mp hk).1
      (specializedOneScaleLog_pos_of_mem hx hk)

theorem naturalGridSelectedPair_eventually_linear_all_K :
    ∀ K : ℕ, 0 < K →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x : ℕ in Filter.atTop,
        (∑ n ∈ Finset.range x, naturalGridSelectedPairTerm K n) ≤
          C * (x : ℝ) := by
  intro K hK
  exact naturalGridSelectedPair_eventually_linear hK

end Erdos448Prop3Assembly

#print axioms Erdos448Prop3Assembly.normalizedExpandedScaleMoment_sum_reindex
#print axioms Erdos448Prop3Assembly.normalizedExpandedScaleMoment_one_scale_bound
#print axioms Erdos448Prop3Assembly.normalizedFormalExpandedScaleMoment_sum_reindex
#print axioms Erdos448Prop3Assembly.normalizedFormalExpandedScaleMoment_one_scale_bound
#print axioms Erdos448Prop3Assembly.normalizedReducedFormalExpandedScaleMoment_sum_reindex
#print axioms Erdos448Prop3Assembly.normalizedReducedFormalExpandedScaleMoment_sum_eq_zero_of_cutoff_lt
#print axioms Erdos448Prop3Assembly.normalizedReducedFormalExpandedScaleMoment_one_scale_bound
#print axioms Erdos448Prop3Assembly.reducedFormalExpandedScaleRegimeContribution_short_eq_zero
#print axioms Erdos448Prop3Assembly.reducedFormalExpandedScaleRegimeContribution_eq_triple_m
#print axioms Erdos448Prop3Assembly.reducedFormalExpandedScaleRegimeContribution_le_active_first_shifted
#print axioms Erdos448Prop3Assembly.naturalGrid_reduced_regime_le_pair_t
#print axioms Erdos448Prop3Assembly.reducedFormalPairRegimeWeightSum_le_formalClosePairMean
#print axioms Erdos448Prop3Assembly.naturalGridSelectedPair_firstMoment_le_common_scale_sum
#print axioms Erdos448Prop3Assembly.naturalGridSelectedPair_firstMoment_le_of_one_scale
#print axioms Erdos448Prop3Assembly.naturalGridSelectedPair_firstMoment_le_of_three_regimes
#print axioms Erdos448Prop3Assembly.naturalGridSelectedPair_firstMoment_le_of_two_regimes
#print axioms Erdos448Prop3Assembly.naturalGridSelectedPair_eventually_linear_all_K
