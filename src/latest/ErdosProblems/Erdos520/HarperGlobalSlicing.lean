import ErdosProblems.Erdos520.HarperFiniteSlicing

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology

namespace Erdos
namespace Problem520

/-!
# Global lattice slicing

The finite slicing lemma is stated inside a coordinate box.  Here we exhaust
the finite-dimensional path space by increasing symmetric boxes.  This
removes the box without a tail error: a cellwise comparison on every lattice
cell controls the whole barrier directly.
-/

/-- Constant-radius coordinate boxes exhaust a finite-dimensional real
coordinate space. -/
theorem iUnion_harperCoordinateBox_natCast_eq_univ (n : ℕ) :
    (⋃ m : ℕ, harperCoordinateBox (fun _ : Fin n ↦ (m : ℝ))) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro omega
  obtain ⟨m, hm⟩ := exists_nat_ge (∑ i : Fin n, |omega i|)
  rw [Set.mem_iUnion]
  refine ⟨m, mem_harperCoordinateBox.mpr (fun i ↦ ?_)⟩
  exact (Finset.single_le_sum (fun j _hj ↦ abs_nonneg (omega j))
    (Finset.mem_univ i)).trans hm

/-- Intersecting a fixed set with the increasing natural-radius boxes
exhausts that set. -/
theorem iUnion_inter_harperCoordinateBox_natCast_eq
    {n : ℕ} (s : Set (Fin n → ℝ)) :
    (⋃ m : ℕ, s ∩ harperCoordinateBox (fun _ : Fin n ↦ (m : ℝ))) = s := by
  rw [← Set.inter_iUnion, iUnion_harperCoordinateBox_natCast_eq_univ,
    Set.inter_univ]

/-- Global Harper slicing.  Unlike the boxed lemma, this has no truncation
remainder: the increasing-box limit is taken exactly under the finite source
measure. -/
theorem measureReal_barrier_le_expandedBarrier_of_latticeCell
    {n : ℕ} (P Q : Measure (Fin n → ℝ))
    [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (C : ℝ) (hC : 0 ≤ C)
    {delta lower upper : Fin n → ℝ}
    (hdelta : ∀ i, 0 < delta i)
    (hcell : ∀ z : Fin n → ℤ,
      P.real (harperLatticeIocCell delta z) ≤
        C * Q.real (harperLatticeIocCell delta z)) :
    P.real (harperPartialSumBarrierSet lower upper) ≤
      C * Q.real
        (harperExpandedPartialSumBarrierSet lower upper delta) := by
  let s : ℕ → Set (Fin n → ℝ) := fun m ↦
    harperPartialSumBarrierSet lower upper ∩
      harperCoordinateBox (fun _ : Fin n ↦ (m : ℝ))
  have hsMono : Monotone s := by
    intro a b hab omega homega
    refine ⟨homega.1, mem_harperCoordinateBox.mpr (fun i ↦ ?_)⟩
    exact (mem_harperCoordinateBox.mp homega.2 i).trans (by exact_mod_cast hab)
  have hsUnion : (⋃ m : ℕ, s m) =
      harperPartialSumBarrierSet lower upper := by
    simpa only [s] using!
      iUnion_inter_harperCoordinateBox_natCast_eq
        (harperPartialSumBarrierSet lower upper)
  have hmeasure : Tendsto (fun m ↦ P (s m)) atTop
      (nhds (P (harperPartialSumBarrierSet lower upper))) := by
    simpa only [hsUnion] using!
      (tendsto_measure_iUnion_atTop (μ := P) hsMono)
  have hreal : Tendsto (fun m ↦ P.real (s m)) atTop
      (nhds (P.real (harperPartialSumBarrierSet lower upper))) := by
    exact (ENNReal.tendsto_toReal
      (measure_ne_top P (harperPartialSumBarrierSet lower upper))).comp hmeasure
  apply le_of_tendsto hreal
  filter_upwards [] with m
  exact measureReal_inter_barrier_box_le_expandedBarrier
    P Q C hC hdelta (fun z _hz ↦ hcell z)

end Problem520
end Erdos
