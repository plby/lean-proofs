import ErdosProblems.Erdos1148.OrbitAtomEntropy
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Counting visits to the exceptional atom of a modular partition -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory

lemma FiniteMeasurablePartition.mem_atom_iff_eq {X ι : Type*} [MeasurableSpace X]
    (P : FiniteMeasurablePartition X ι) {x : X} {a : ι} (hx : x ∈ P.atom a) (b : ι) :
    x ∈ P.atom b ↔ a = b := by
  constructor
  · intro hb
    by_contra hne
    exact Set.disjoint_left.mp (P.disjoint_atom hne) hx hb
  · intro h
    simpa only [h] using hx

def exceptionalVisitSet (P : FineModularPartition) (k : ℕ) : Set ModularOrbitSpace :=
  (modularRightTranslate (diagonalFlow ((k + 1 : ℕ) : ℝ))) ⁻¹' P.partition.atom none

lemma measurableSet_exceptionalVisitSet (P : FineModularPartition) (k : ℕ) :
    MeasurableSet (exceptionalVisitSet P k) :=
  (P.partition.measurable_atom none).preimage (continuous_modularRightTranslate _).measurable

noncomputable def exceptionalVisitCount (P : FineModularPartition) (n : ℕ)
    (x : ModularOrbitSpace) : ℝ :=
  ∑ k ∈ Finset.range n, (exceptionalVisitSet P k).indicator (fun _ => (1 : ℝ)) x

lemma exceptionalVisitCount_nonneg (P : FineModularPartition) (n : ℕ) (x : ModularOrbitSpace) :
    0 ≤ exceptionalVisitCount P n x := by
  classical
  apply Finset.sum_nonneg
  intro k _
  exact Set.indicator_nonneg (fun _ _ => zero_le_one) x

lemma measurable_exceptionalVisitCount (P : FineModularPartition) (n : ℕ) :
    Measurable (exceptionalVisitCount P n) :=
  Finset.measurable_sum _ (fun k _ =>
    measurable_const.indicator (measurableSet_exceptionalVisitSet P k))

lemma integrable_exceptionalVisitCount (P : FineModularPartition)
    (μ : Measure ModularOrbitSpace) [IsFiniteMeasure μ] (n : ℕ) :
    Integrable (exceptionalVisitCount P n) μ :=
  integrable_finsetSum _ (fun k _ => (integrable_const (1 : ℝ)).indicator
    (measurableSet_exceptionalVisitSet P k))

theorem integral_exceptionalVisitCount (P : FineModularPartition)
    (μ : Measure ModularOrbitSpace) [IsFiniteMeasure μ]
    (hinv : ∀ t : ℝ, Measure.map (modularRightTranslate (diagonalFlow t)) μ = μ) (n : ℕ) :
    (∫ x, exceptionalVisitCount P n x ∂μ) = (n : ℝ) * μ.real (P.partition.atom none) := by
  unfold exceptionalVisitCount
  rw [integral_finsetSum _ (fun k _ => (integrable_const (1 : ℝ)).indicator
    (measurableSet_exceptionalVisitSet P k))]
  have hterm (k : ℕ) : (∫ x, (exceptionalVisitSet P k).indicator (fun _ => (1 : ℝ)) x ∂μ) =
      μ.real (P.partition.atom none) := by
    have h := integral_indicator_const (μ := μ) (1 : ℝ) (measurableSet_exceptionalVisitSet P k)
    simp only [smul_eq_mul, mul_one] at h
    rw [h]
    exact modular_flow_measureReal_preimage μ hinv _ _
  simp only [hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

theorem exceptionalVisitCount_of_mem_orbitAtom (P : FineModularPartition) {n : ℕ}
    {w : Fin (n + 1) → Option (Fin P.size)} {x : ModularOrbitSpace}
    (hx : x ∈ P.partition.orbitAtom modularTimeOne (n + 1) w) :
    exceptionalVisitCount P n x = (exceptionalWordStepCount w : ℝ) := by
  classical
  unfold exceptionalVisitCount exceptionalWordStepCount
  rw [Finset.natCast_card_filter]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k + 1 < n + 1 := by have := Finset.mem_range.mp hk; omega
  have hword := hx ⟨k + 1, hk'⟩
  rw [modularTimeOne_iterate] at hword
  have heq : x ∈ exceptionalVisitSet P k ↔ orbitWordLabel w (k + 1) = none := by
    simpa only [exceptionalVisitSet, Set.mem_preimage, orbitWordLabel, dif_pos hk'] using
      P.partition.mem_atom_iff_eq hword none
  simp only [Set.indicator_apply, heq]

end Erdos1148.DukeArithmetic
