import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-! # Finite-time avoidance of a positive-measure set in an ergodic system -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory Measure Filter
open scoped ENNReal Topology

def finiteOrbitAvoidance {X : Type*} (f : X → X) (U : Set X) (n : ℕ) : Set X :=
  {x | ∀ k < n, f^[k] x ∉ U}

def infiniteOrbitAvoidance {X : Type*} (f : X → X) (U : Set X) : Set X :=
  {x | ∀ k : ℕ, f^[k] x ∉ U}

variable {X : Type*} [MeasurableSpace X] {f : X → X} {U : Set X} {μ : Measure X}

lemma measurableSet_finiteOrbitAvoidance (hf : Measurable f) (hU : MeasurableSet U) (n : ℕ) :
    MeasurableSet (finiteOrbitAvoidance f U n) := by
  simp only [finiteOrbitAvoidance, Set.ofPred_forall]
  exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
    hU.compl.preimage (hf.iterate k)

lemma measurableSet_infiniteOrbitAvoidance (hf : Measurable f) (hU : MeasurableSet U) :
    MeasurableSet (infiniteOrbitAvoidance f U) := by
  simp only [infiniteOrbitAvoidance, Set.ofPred_forall]
  exact MeasurableSet.iInter fun k => hU.compl.preimage (hf.iterate k)

lemma infiniteOrbitAvoidance_eq_iInter :
    infiniteOrbitAvoidance f U = ⋂ n : ℕ, finiteOrbitAvoidance f U n := by
  ext x
  simp only [infiniteOrbitAvoidance, finiteOrbitAvoidance, Set.mem_setOf_eq, Set.mem_iInter]
  exact ⟨fun h _ k _ => h k, fun h k => h (k + 1) k (Nat.lt_succ_self k)⟩

theorem _root_.Ergodic.infiniteOrbitAvoidance_null [IsFiniteMeasure μ] (hf : _root_.Ergodic f μ)
    (hU : MeasurableSet U) (hpos : 0 < μ U) : μ (infiniteOrbitAvoidance f U) = 0 := by
  have hm := measurableSet_infiniteOrbitAvoidance hf.measurable hU
  have hsub : infiniteOrbitAvoidance f U ⊆ f ⁻¹' infiniteOrbitAvoidance f U := by
    intro x hx k
    simpa only [Function.iterate_succ_apply] using hx (k + 1)
  have heq : μ (f ⁻¹' infiniteOrbitAvoidance f U) = μ (infiniteOrbitAvoidance f U) := by
    rw [← Measure.map_apply hf.measurable hm, hf.map_eq]
  have hae := (ae_eq_of_subset_of_measure_ge hsub heq.le hm.nullMeasurableSet
    (measure_ne_top _ _)).symm
  have hzero : μ (infiniteOrbitAvoidance f U) = 0 ∨ μ (infiniteOrbitAvoidance f U)ᶜ = 0 := by
    simpa using hf.quasiErgodic.ae_empty_or_univ₀ hm.nullMeasurableSet hae
  rcases hzero with h | h
  · exact h
  · have hUsub : U ⊆ (infiniteOrbitAvoidance f U)ᶜ := by
      intro x hx ha
      exact ha 0 hx
    exact (hpos.ne' (measure_mono_null hUsub h)).elim

theorem _root_.Ergodic.finiteOrbitAvoidance_mass_tendsto_zero [IsFiniteMeasure μ]
    (hf : _root_.Ergodic f μ) (hU : MeasurableSet U) (hpos : 0 < μ U) :
    Tendsto (fun n : ℕ => μ (finiteOrbitAvoidance f U n)) atTop (𝓝 0) := by
  have hanti : Antitone (finiteOrbitAvoidance f U) := by
    intro n m hnm x hx k hk
    exact hx k (hk.trans_le hnm)
  have hlim := tendsto_measure_iInter_atTop (μ := μ)
    (fun n => (measurableSet_finiteOrbitAvoidance hf.measurable hU n).nullMeasurableSet)
    hanti (by exact ⟨0, measure_ne_top μ _⟩)
  rwa [← infiniteOrbitAvoidance_eq_iInter, hf.infiniteOrbitAvoidance_null hU hpos] at hlim

end Erdos1148.DukeArithmetic
