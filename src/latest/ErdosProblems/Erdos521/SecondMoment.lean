/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The second-moment step for Erdős Problem 521.
Informal proof: the 29 April 2026 working note, Section 7; Rob Sneiderman.
Formal proof: Codex, using the repository's verified indicator-count inequality.
https://web.math.pmf.unizg.hr/~vjekovac/files/Erdos_521_Kac.pdf
-/
import ErdosProblems.Erdos521.RecordProbability
import ErdosProblems.Erdos1165.SecondMoment

namespace Erdos521

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

/-- The strictly ordered part of the record-pair probability. -/
def orderedRecordWeight (q : ℕ → ℝ) (i j : ℕ) : ℝ :=
  if i < j then q i * q (j - i - 1) else 0

theorem sum_orderedRecordWeight_le_square (q : ℕ → ℝ) (hq : ∀ i, 0 ≤ q i) (N : ℕ) :
    ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, orderedRecordWeight q i j ≤
      (∑ i ∈ Finset.range N, q i) ^ 2 := by
  let pairs := (Finset.range N ×ˢ Finset.range N).filter fun p ↦ p.1 < p.2
  let encode : ℕ × ℕ → ℕ × ℕ := fun p ↦ (p.1, p.2 - p.1 - 1)
  let weight : ℕ × ℕ → ℝ := fun p ↦ q p.1 * q p.2
  have hinj : Set.InjOn encode pairs := by
    rintro ⟨i, j⟩ hp ⟨i', j'⟩ hp' heq
    have hij : i < j := (Finset.mem_filter.mp hp).2
    have hij' : i' < j' := (Finset.mem_filter.mp hp').2
    simp only [encode, Prod.mk.injEq] at heq
    apply Prod.ext <;> dsimp <;> omega
  have hsub : pairs.image encode ⊆ Finset.range N ×ˢ Finset.range N := by
    intro p hp
    obtain ⟨⟨i, j⟩, hij, rfl⟩ := Finset.mem_image.mp hp
    simp only [pairs, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hij
    simp only [encode, Finset.mem_product, Finset.mem_range]
    omega
  calc
    ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, orderedRecordWeight q i j =
        ∑ p ∈ pairs, weight (encode p) := by
      simp only [pairs, Finset.sum_filter, orderedRecordWeight, weight, encode]
      rw [Finset.sum_product]
    _ = ∑ p ∈ pairs.image encode, weight p := by rw [Finset.sum_image hinj]
    _ ≤ ∑ p ∈ Finset.range N ×ˢ Finset.range N, weight p := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro p _ _
      exact mul_nonneg (hq p.1) (hq p.2)
    _ = (∑ i ∈ Finset.range N, q i) ^ 2 := by
      simp only [weight, Finset.sum_product, pow_two, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]

noncomputable def recordProbability (ν : Measure (ℝ × ℝ)) [IsProbabilityMeasure ν]
    (m : ℕ) : ℝ := (Measure.infinitePi fun _ : ℕ ↦ ν).real (pairRecord m)

noncomputable def recordProbabilitySum (ν : Measure (ℝ × ℝ)) [IsProbabilityMeasure ν]
    (N : ℕ) : ℝ := ∑ i ∈ Finset.range N, recordProbability ν i

theorem recordProbability_nonneg (ν : Measure (ℝ × ℝ)) [IsProbabilityMeasure ν] (m : ℕ) :
    0 ≤ recordProbability ν m := measureReal_nonneg

theorem recordProbabilitySum_nonneg (ν : Measure (ℝ × ℝ)) [IsProbabilityMeasure ν] (N : ℕ) :
    0 ≤ recordProbabilitySum ν N :=
  Finset.sum_nonneg fun i _ ↦ recordProbability_nonneg ν i

theorem pairRecord_inter_measureReal (ν : Measure (ℝ × ℝ)) [IsProbabilityMeasure ν]
    (i j : ℕ) (hij : i < j) :
    (Measure.infinitePi fun _ : ℕ ↦ ν).real (pairRecord i ∩ pairRecord j) =
      recordProbability ν i * recordProbability ν (j - i - 1) := by
  simp only [measureReal_def, pairRecord_inter_measure ν i j hij,
    ENNReal.toReal_mul, recordProbability]

/-- The finite double-sum bound used by Kochen–Stone. -/
theorem record_pairSum_le (ν : Measure (ℝ × ℝ)) [IsProbabilityMeasure ν] (N : ℕ) :
    (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
      (Measure.infinitePi fun _ : ℕ ↦ ν).real (pairRecord i ∩ pairRecord j)) ≤
      recordProbabilitySum ν N + 2 * recordProbabilitySum ν N ^ 2 := by
  let q := recordProbability ν
  let W := orderedRecordWeight q
  have hpoint (i j : ℕ) :
      (Measure.infinitePi fun _ : ℕ ↦ ν).real (pairRecord i ∩ pairRecord j) ≤
        (if i = j then q i else 0) + W i j + W j i := by
    rcases lt_trichotomy i j with hij | rfl | hji
    · rw [pairRecord_inter_measureReal ν i j hij]
      simp [W, orderedRecordWeight, hij, Nat.not_lt.mpr hij.le, hij.ne, q]
    · simp [W, orderedRecordWeight, q, recordProbability]
    · rw [Set.inter_comm, pairRecord_inter_measureReal ν j i hji]
      simp [W, orderedRecordWeight, hji, Nat.not_lt.mpr hji.le, hji.ne', q]
  have hdiag : (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
      if i = j then q i else 0) = recordProbabilitySum ν N := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [hi, q]
  have hswap : (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, W j i) =
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, W i j := by
    rw [Finset.sum_comm]
  have hw : (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, W i j) ≤
      recordProbabilitySum ν N ^ 2 :=
    sum_orderedRecordWeight_le_square q (recordProbability_nonneg ν) N
  calc
    (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
      (Measure.infinitePi fun _ : ℕ ↦ ν).real (pairRecord i ∩ pairRecord j)) ≤
        ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
          ((if i = j then q i else 0) + W i j + W j i) :=
      Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ hpoint i j
    _ = recordProbabilitySum ν N +
        2 * (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, W i j) := by
      simp only [Finset.sum_add_distrib, hdiag, hswap]
      ring
    _ ≤ recordProbabilitySum ν N + 2 * recordProbabilitySum ν N ^ 2 := by
      linarith

/-- At least one record at or after `T`. -/
def recordTail (T : ℕ) : Set (ℕ → ℝ × ℝ) := ⋃ n, ⋃ (_ : T ≤ n), pairRecord n

theorem measurableSet_recordTail (T : ℕ) : MeasurableSet (recordTail T) :=
  MeasurableSet.iUnion fun n ↦ MeasurableSet.iUnion fun _ ↦ measurableSet_pairRecord n

theorem antitone_recordTail : Antitone recordTail := by
  intro T U hTU ω hω
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hω
  obtain ⟨hUn, hrecord⟩ := Set.mem_iUnion.mp hn
  exact Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr ⟨hTU.trans hUn, hrecord⟩⟩

/-- A uniform positive lower bound for every tail union. Its constant is
irrelevant to the zero-one upgrade; the proof uses only the finite indicator
second-moment inequality and divergence of the record-probability sum. -/
theorem recordTail_measureReal_lower (ν : Measure (ℝ × ℝ)) [IsProbabilityMeasure ν]
    (hdiv : Tendsto (recordProbabilitySum ν) atTop atTop) (T : ℕ) :
    (1 / 12 : ℝ) ≤ (Measure.infinitePi fun _ : ℕ ↦ ν).real (recordTail T) := by
  let μ := Measure.infinitePi fun _ : ℕ ↦ ν
  obtain ⟨N, hTN, hlarge⟩ := ((eventually_ge_atTop T).and
    (tendsto_atTop.mp hdiv (2 * recordProbabilitySum ν T + 1))).exists
  let S := recordProbabilitySum ν N
  have hS : 1 ≤ S := by linarith [recordProbabilitySum_nonneg ν T]
  have hSpos : 0 < S := lt_of_lt_of_le zero_lt_one hS
  have hfirst : S / 2 ≤ ∑ i ∈ Finset.Ico T N, μ.real (pairRecord i) := by
    have hid : (∑ i ∈ Finset.Ico T N, μ.real (pairRecord i)) =
        S - recordProbabilitySum ν T := by
      exact Finset.sum_Ico_eq_sub _ hTN
    rw [hid]
    dsimp only [S]
    linarith
  have hsub : Finset.Ico T N ⊆ Finset.range N := by
    intro i hi
    exact Finset.mem_range.mpr (Finset.mem_Ico.mp hi).2
  have hsecond : (∑ i ∈ Finset.Ico T N, ∑ j ∈ Finset.Ico T N,
      μ.real (pairRecord i ∩ pairRecord j)) ≤ 3 * S ^ 2 := by
    calc
      (∑ i ∈ Finset.Ico T N, ∑ j ∈ Finset.Ico T N,
        μ.real (pairRecord i ∩ pairRecord j)) ≤
          ∑ i ∈ Finset.Ico T N, ∑ j ∈ Finset.range N,
            μ.real (pairRecord i ∩ pairRecord j) := by
        apply Finset.sum_le_sum
        intro i _
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ measureReal_nonneg
      _ ≤ ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
            μ.real (pairRecord i ∩ pairRecord j) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro i _ _
        exact Finset.sum_nonneg fun _ _ ↦ measureReal_nonneg
      _ ≤ S + 2 * S ^ 2 := record_pairSum_le ν N
      _ ≤ 3 * S ^ 2 := by nlinarith [sq_nonneg (S - 1)]
  have hmoment := Erdos1165.SecondMoment.indicatorCount_union_lower_mul (mu := μ)
    (Finset.Ico T N) pairRecord (fun i _ ↦ measurableSet_pairRecord i)
    (show 0 ≤ S / 2 by positivity) hfirst hsecond
  have hfinite : (1 / 12 : ℝ) ≤ μ.real (⋃ i ∈ Finset.Ico T N, pairRecord i) := by
    have hscale : (1 / 12 : ℝ) * S ^ 2 ≤
        μ.real (⋃ i ∈ Finset.Ico T N, pairRecord i) * S ^ 2 := by
      nlinarith
    exact (mul_le_mul_iff_of_pos_right (sq_pos_of_pos hSpos)).mp hscale
  apply hfinite.trans
  apply measureReal_mono (h₂ := measure_ne_top μ (recordTail T))
  intro ω hω
  obtain ⟨i, hω⟩ := Set.mem_iUnion.mp hω
  obtain ⟨hi, hrecord⟩ := Set.mem_iUnion.mp hω
  exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨(Finset.mem_Ico.mp hi).1, hrecord⟩⟩

/-- Divergence of the one-time record-probability sum forces positive
probability of infinitely many records. This proves the needed special case
of the Kochen–Stone step, rather than assuming a Borel–Cantelli theorem for
the dependent record events. -/
theorem pairInfiniteRecords_measure_lower (ν : Measure (ℝ × ℝ)) [IsProbabilityMeasure ν]
    (hdiv : Tendsto (recordProbabilitySum ν) atTop atTop) :
    ENNReal.ofReal (1 / 12 : ℝ) ≤
      (Measure.infinitePi fun _ : ℕ ↦ ν) pairInfiniteRecords := by
  let μ := Measure.infinitePi fun _ : ℕ ↦ ν
  have hid : pairInfiniteRecords = ⋂ T, recordTail T := by
    ext ω
    simp [pairInfiniteRecords, InfiniteRecords, recordTail, pairRecord]
  rw [hid, antitone_recordTail.measure_iInter
    (fun T ↦ (measurableSet_recordTail T).nullMeasurableSet)
    ⟨0, measure_ne_top μ (recordTail 0)⟩]
  exact le_iInf fun T ↦ ENNReal.ofReal_le_of_le_toReal
    (recordTail_measureReal_lower ν hdiv T)

/-- The complete probabilistic record theorem once the explicit survival
series has been shown to diverge. No analytic root-count input is used. -/
theorem pairInfiniteRecords_measure_one_of_divergence
    (ν : Measure (ℝ × ℝ)) [IsProbabilityMeasure ν]
    (hdiv : Tendsto (recordProbabilitySum ν) atTop atTop) :
    (Measure.infinitePi fun _ : ℕ ↦ ν) pairInfiniteRecords = 1 := by
  rcases pairInfiniteRecords_zero_one ν with hzero | hone
  · have h := pairInfiniteRecords_measure_lower ν hdiv
    rw [hzero] at h
    norm_num at h
  · exact hone

end Erdos521
