/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Finite-prefix zero-one argument for Erdős Problem 521.
Informal proof: Rob Sneiderman.
Formal proof: Codex.
https://github.com/Robby955/erdos-521-zero-one
-/
import ErdosProblems.Erdos521.Records
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.ZeroOne

namespace Erdos521

open Filter MeasureTheory MeasurableSpace ProbabilityTheory

/-- Delete the first `r` terms of a sequence. -/
def shift {α : Type*} (r : ℕ) (ω : ℕ → α) : ℕ → α := fun i ↦ ω (r + i)

theorem shift_add {α : Type*} (r s : ℕ) (ω : ℕ → α) :
    shift s (shift r ω) = shift (r + s) ω := by
  funext i
  simp [shift, Nat.add_assoc]

@[fun_prop]
theorem measurable_shift {α : Type*} [MeasurableSpace α] (r : ℕ) :
    Measurable (shift (α := α) r) := by
  exact measurable_pi_lambda _ fun i ↦ measurable_pi_apply (r + i)

theorem measurePreserving_shift {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (r : ℕ) :
    MeasurePreserving (shift r) (Measure.infinitePi fun _ : ℕ ↦ ν)
      (Measure.infinitePi fun _ : ℕ ↦ ν) := by
  refine ⟨measurable_shift r, ?_⟩
  exact Measure.map_infinitePi_infinitePi_of_inj (fun a b h ↦ Nat.add_left_cancel h)

/-- For an iid sequence, a measurable event that is preserved by deleting any
finite prefix has probability zero or one. The event itself need not be a
pointwise tail event: its union over all restarts is a tail representative. -/
theorem measure_zero_or_one_of_shift_closed {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (E : Set (ℕ → α))
    (hE : MeasurableSet E) (hshift : ∀ r, E ⊆ shift r ⁻¹' E) :
    (Measure.infinitePi fun _ : ℕ ↦ ν) E = 0 ∨
      (Measure.infinitePi fun _ : ℕ ↦ ν) E = 1 := by
  let μ := Measure.infinitePi fun _ : ℕ ↦ ν
  let B : ℕ → Set (ℕ → α) := fun r ↦ shift r ⁻¹' E
  let C : Set (ℕ → α) := ⋃ r, B r
  have hBmeasure (r : ℕ) : μ (B r) = μ E :=
    (measurePreserving_shift ν r).measure_preimage hE.nullMeasurableSet
  have hBae (r : ℕ) : E =ᵐ[μ] B r :=
    ae_eq_of_subset_of_measure_ge (hshift r) (hBmeasure r).le
      hE.nullMeasurableSet (measure_ne_top μ (B r))
  have hEae : E =ᵐ[μ] C := by
    have hu : (⋃ _ : ℕ, E) =ᵐ[μ] ⋃ r, B r :=
      Filter.EventuallyEq.countable_iUnion hBae
    simpa only [Set.iUnion_const] using hu
  have hBmono : Monotone B := by
    intro r s hrs ω hω
    have hs := hshift (s - r) hω
    change shift (s - r) (shift r ω) ∈ E at hs
    change shift s ω ∈ E
    simpa only [shift_add, Nat.add_sub_of_le hrs] using hs
  have hCtail (n : ℕ) : C = ⋃ r, B (n + r) := by
    apply Set.Subset.antisymm
    · intro ω hω
      obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hω
      exact Set.mem_iUnion.mpr ⟨r, hBmono (Nat.le_add_left r n) hr⟩
    · intro ω hω
      obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hω
      exact Set.mem_iUnion.mpr ⟨n + r, hr⟩
  let coord : ℕ → MeasurableSpace (ℕ → α) :=
    fun i ↦ MeasurableSpace.comap (fun ω ↦ ω i) inferInstance
  have hcoord (i : ℕ) : coord i ≤ (inferInstance : MeasurableSpace (ℕ → α)) :=
    (measurable_pi_apply i).comap_le
  have hCmeas : MeasurableSet[limsup coord atTop] C := by
    rw [limsup_eq_iInf_iSup_of_nat, measurableSet_iInf]
    intro n
    rw [hCtail n]
    apply MeasurableSet.iUnion
    intro r
    apply hE.preimage
    rw [measurable_iff_comap_le]
    change MeasurableSpace.comap (fun (ω : ℕ → α) (i : ℕ) ↦ ω (n + r + i))
      (MeasurableSpace.pi : MeasurableSpace (ℕ → α)) ≤ _
    rw [MeasurableSpace.comap_process_pi]
    apply iSup_le
    intro i
    exact le_iSup_of_le (n + r + i) (le_iSup_of_le (by omega) le_rfl)
  have hind : iIndep coord μ :=
    iIndepFun_infinitePi (P := fun _ : ℕ ↦ ν) (fun _ ↦ measurable_id)
  have hzeroone := measure_zero_or_one_of_measurableSet_limsup_atTop hcoord hind hCmeas
  simpa only [← measure_congr hEae] using hzeroone

/-- Infinite cone records for a sequence of planar increments. -/
def pairInfiniteRecords : Set (ℕ → ℝ × ℝ) :=
  {ω | InfiniteRecords (fun i ↦ (ω i).1) (fun i ↦ (ω i).2)}

theorem measurableSet_pairConeRecord (m : ℕ) :
    MeasurableSet {ω : ℕ → ℝ × ℝ | ConeRecord (fun i ↦ (ω i).1) (fun i ↦ (ω i).2) m} := by
  unfold ConeRecord InCone prefixSum
  measurability

theorem measurableSet_pairInfiniteRecords : MeasurableSet pairInfiniteRecords := by
  have heq : pairInfiniteRecords = ⋂ N : ℕ, ⋃ m : ℕ, ⋃ (_ : N ≤ m),
      {ω : ℕ → ℝ × ℝ | ConeRecord (fun i ↦ (ω i).1) (fun i ↦ (ω i).2) m} := by
    ext ω
    simp [pairInfiniteRecords, InfiniteRecords]
  rw [heq]
  exact MeasurableSet.iInter fun N ↦ MeasurableSet.iUnion fun m ↦
    MeasurableSet.iUnion fun _ ↦ measurableSet_pairConeRecord m

/-- The finite-prefix zero-one upgrade for cone records, for every iid planar
increment law. Positive probability must still be proved separately. -/
theorem pairInfiniteRecords_zero_one (ν : Measure (ℝ × ℝ)) [IsProbabilityMeasure ν] :
    (Measure.infinitePi fun _ : ℕ ↦ ν) pairInfiniteRecords = 0 ∨
      (Measure.infinitePi fun _ : ℕ ↦ ν) pairInfiniteRecords = 1 := by
  apply measure_zero_or_one_of_shift_closed ν pairInfiniteRecords
    measurableSet_pairInfiniteRecords
  intro r ω hω
  exact InfiniteRecords.shift hω r

end Erdos521
