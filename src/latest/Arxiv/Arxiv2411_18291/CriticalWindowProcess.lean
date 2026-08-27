import Arxiv.Arxiv2411_18291.StoppedIncrementConcentration

/-!
# Predictable stopping inside a critical interval

For a fixed start time, increments are retained while the process stays
above the lower boundary and the auxiliary good events continue to hold.
Any required upper boundary can be included in those good events.
On any such trajectory the retained increments telescope exactly.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {Ω : Type*}

def windowActive (A : ℕ → Ω → ℝ) (G : ℕ → Set Ω) (l : ℝ) (s i : ℕ) : Set Ω :=
  {ω | s ≤ i ∧ (∀ k ≤ i, ω ∈ G k) ∧ ∀ k, s ≤ k → k ≤ i → l ≤ A k ω}

variable {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℕ mΩ}
variable {A : ℕ → Ω → ℝ} {G : ℕ → Set Ω} {l : ℝ} {s i j : ℕ} {ω : Ω}

theorem windowActive_measurableSet
    (hA : ∀ k ≤ i, StronglyMeasurable[ℱ k] (A k))
    (hG : ∀ k ≤ i, MeasurableSet[ℱ k] (G k)) :
    MeasurableSet[ℱ i] (windowActive A G l s i) := by
  by_cases hsi : s ≤ i
  · have hprefix : MeasurableSet[ℱ i] {ω | ∀ k ≤ i, ω ∈ G k} := by
      simp only [Set.ofPred_forall]
      exact MeasurableSet.iInter fun k => MeasurableSet.iInter fun hk =>
        ℱ.mono hk _ (hG k hk)
    have hwindow : MeasurableSet[ℱ i]
        {ω | ∀ k, s ≤ k → k ≤ i → l ≤ A k ω} := by
      simp only [Set.ofPred_forall]
      refine MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
        MeasurableSet.iInter fun hk => ?_
      have hkA := ((hA k hk).mono (ℱ.mono hk)).measurable
      exact measurableSet_le measurable_const hkA
    simpa only [windowActive, hsi, true_and, Set.ofPred_and] using hprefix.inter hwindow
  · have heq : windowActive A G l s i = ∅ := by
      ext ω
      simp [windowActive, hsi]
    rw [heq]
    exact @MeasurableSet.empty Ω (ℱ i)

theorem windowActive_current (h : ω ∈ windowActive A G l s i) :
    ω ∈ G i ∧ l ≤ A i ω :=
  ⟨h.2.1 i le_rfl, h.2.2 i h.1 le_rfl⟩

theorem windowActive_sum_eq (hsj : s ≤ j)
    (hG : ∀ k < j, ω ∈ G k)
    (hwindow : ∀ k, s ≤ k → k < j → l ≤ A k ω) :
    (∑ i ∈ range j, (windowActive A G l s i).indicator
      (fun ω => A (i + 1) ω - A i ω) ω) = A j ω - A s ω := by
  classical
  revert hG hwindow
  induction j, hsj using Nat.le_induction with
  | base =>
    intro _ _
    rw [sub_self]
    apply sum_eq_zero
    intro i hi
    apply Set.indicator_of_notMem
    intro h
    exact (Nat.not_le_of_lt (mem_range.mp hi)) h.1
  | succ j hsj ih =>
    intro hG hwindow
    have hmem : ω ∈ windowActive A G l s j :=
      ⟨hsj, fun k hk => hG k (by omega), fun k hsk hk => hwindow k hsk (by omega)⟩
    rw [sum_range_succ, Set.indicator_of_mem hmem]
    rw [ih (fun k hk => hG k (by omega)) (fun k hsk hk => hwindow k hsk (by omega))]
    ring

end Arxiv2411_18291
