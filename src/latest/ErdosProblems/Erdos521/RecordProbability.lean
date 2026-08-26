/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Probability identities for the cone records in Erdős Problem 521.
Informal proof: the 29 April 2026 working note, Section 7; Rob Sneiderman.
Formal proof: Codex.
https://web.math.pmf.unizg.hr/~vjekovac/files/Erdos_521_Kac.pdf
-/
import ErdosProblems.Erdos521.ZeroOne

namespace Erdos521

open Filter MeasureTheory MeasurableSpace ProbabilityTheory

/-- The event that time `m` is a cone record. -/
def pairRecord (m : ℕ) : Set (ℕ → ℝ × ℝ) :=
  {ω | ConeRecord (fun i ↦ (ω i).1) (fun i ↦ (ω i).2) m}

theorem measurableSet_pairRecord (m : ℕ) : MeasurableSet (pairRecord m) :=
  measurableSet_pairConeRecord m

/-- The sigma-algebra of a single coordinate. -/
abbrev coordinateSigma (i : ℕ) : MeasurableSpace (ℕ → ℝ × ℝ) :=
  MeasurableSpace.comap (fun ω ↦ ω i) inferInstance

theorem coordinateSigma_le (i : ℕ) :
    coordinateSigma i ≤ (inferInstance : MeasurableSpace (ℕ → ℝ × ℝ)) :=
  (measurable_pi_apply i).comap_le

/-- A record at time `m` only depends on the first `m+1` increments. -/
theorem measurableSet_pairRecord_prefix (m : ℕ) :
    MeasurableSet[⨆ i ≤ m, coordinateSigma i] (pairRecord m) := by
  let : MeasurableSpace (ℕ → ℝ × ℝ) := ⨆ i ≤ m, coordinateSigma i
  have heval (i : ℕ) (hi : i ≤ m) : Measurable (fun ω : ℕ → ℝ × ℝ ↦ ω i) :=
    measurable_iff_comap_le.mpr (le_iSup_of_le i (le_iSup_of_le hi le_rfl))
  have hfst (n : ℕ) (hn : n ≤ m + 1) :
      Measurable (fun ω : ℕ → ℝ × ℝ ↦ prefixSum (fun i ↦ (ω i).1) n) := by
    exact Finset.measurable_sum _ fun i hi ↦
      (heval i (by have := Finset.mem_range.mp hi; omega)).fst
  have hsnd (n : ℕ) (hn : n ≤ m + 1) :
      Measurable (fun ω : ℕ → ℝ × ℝ ↦ prefixSum (fun i ↦ (ω i).2) n) := by
    exact Finset.measurable_sum _ fun i hi ↦
      (heval i (by have := Finset.mem_range.mp hi; omega)).snd
  simp only [pairRecord, ConeRecord, Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro k
  apply MeasurableSet.iInter
  intro hk
  have ha := (hfst (m + 1) le_rfl).sub (hfst k (by omega))
  have hb := (hsnd (m + 1) le_rfl).sub (hsnd k (by omega))
  simp only [inCone_iff, Set.ofPred_and]
  exact (measurableSet_le measurable_const (ha.add hb)).inter
    (measurableSet_le measurable_const (ha.sub hb))

/-- Deleting `r` terms is measurable with respect to the tail starting at `r`. -/
theorem measurable_shift_tail (r : ℕ) :
    @Measurable (ℕ → ℝ × ℝ) (ℕ → ℝ × ℝ)
      (⨆ i ≥ r, coordinateSigma i) inferInstance (shift r) := by
  rw [measurable_iff_comap_le]
  change MeasurableSpace.comap (fun (ω : ℕ → ℝ × ℝ) (i : ℕ) ↦ ω (r + i))
    (MeasurableSpace.pi : MeasurableSpace (ℕ → ℝ × ℝ)) ≤ _
  rw [MeasurableSpace.comap_process_pi]
  exact iSup_le fun i ↦ le_iSup_of_le (r + i) (le_iSup_of_le (by omega) le_rfl)

/-- Independence of the first block record from an arbitrary measurable event
in the remaining increments. -/
theorem indepSet_pairRecord_shift (ν : Measure (ℝ × ℝ)) [IsProbabilityMeasure ν]
    (m : ℕ) (E : Set (ℕ → ℝ × ℝ)) (hE : MeasurableSet E) :
    IndepSet (pairRecord m) (shift (m + 1) ⁻¹' E)
      (Measure.infinitePi fun _ : ℕ ↦ ν) := by
  have hind : iIndep coordinateSigma (Measure.infinitePi fun _ : ℕ ↦ ν) :=
    iIndepFun_infinitePi (P := fun _ : ℕ ↦ ν) (fun _ ↦ measurable_id)
  have hdisj : Disjoint (Set.Iic m) (Set.Ici (m + 1)) := by
    apply Set.disjoint_left.mpr
    intro i hi hj
    simp only [Set.mem_Iic, Set.mem_Ici] at hi hj
    omega
  have hblocks := indep_iSup_of_disjoint coordinateSigma_le hind hdisj
  exact hblocks.indepSet_of_measurableSet (measurableSet_pairRecord_prefix m)
    (hE.preimage (measurable_shift_tail (m + 1)))

theorem pairRecord_inter_eq (m l : ℕ) (hml : m < l) :
    pairRecord m ∩ pairRecord l =
      pairRecord m ∩ shift (m + 1) ⁻¹' pairRecord (l - m - 1) := by
  ext ω
  simp only [Set.mem_inter_iff, pairRecord, Set.mem_ofPred_eq, Set.mem_preimage]
  rw [coneRecord_decomposition _ _ m l hml]
  apply and_congr_right
  intro _
  have hlen : l = (m + 1) + (l - m - 1) := by omega
  nth_rw 1 [hlen]
  exact coneRecordFrom_iff_shift _ _ (m + 1) (l - m - 1)

/-- The exact two-time record probability. This is an equality, not an
independence assertion about the two overlapping record events. -/
theorem pairRecord_inter_measure (ν : Measure (ℝ × ℝ)) [IsProbabilityMeasure ν]
    (m l : ℕ) (hml : m < l) :
    (Measure.infinitePi fun _ : ℕ ↦ ν) (pairRecord m ∩ pairRecord l) =
      (Measure.infinitePi fun _ : ℕ ↦ ν) (pairRecord m) *
        (Measure.infinitePi fun _ : ℕ ↦ ν) (pairRecord (l - m - 1)) := by
  rw [pairRecord_inter_eq m l hml]
  rw [(indepSet_pairRecord_shift ν m _ (measurableSet_pairRecord _)).measure_inter_eq_mul]
  rw [(measurePreserving_shift ν (m + 1)).measure_preimage
    (measurableSet_pairRecord _).nullMeasurableSet]

theorem pairInfiniteRecords_eq_limsup :
    pairInfiniteRecords = limsup pairRecord atTop := by
  ext ω
  simp [pairInfiniteRecords, InfiniteRecords, pairRecord, limsup_eq_iInf_iSup_of_nat]

end Erdos521
