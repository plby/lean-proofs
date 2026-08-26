/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Regularity
import ErdosProblems.Erdos547b.EC2
import Mathlib.Tactic

/-!
# Source-faithful almost-all-target root cleaning

Double counting gives a root atypical to only a small fraction of targets.
It does not require a root simultaneously typical to every target, nor an
inequality involving the regularity upper bound times the error parameter.
-/

open scoped BigOperators SimpleGraph
noncomputable section

namespace Erdos547b.ZhaoSourceRootIncidence

open Finset SimpleGraph

variable {V I : Type*} [DecidableEq V] [DecidableEq I]

def badTargets (J : Finset I) (bad : I → Finset V) (z : V) : Finset I :=
  J.filter fun j => z ∈ bad j

def manyBadRoots (A : Finset V) (J : Finset I) (bad : I → Finset V)
    (δ : ℝ) : Finset V :=
  A.filter fun z => δ * J.card < ((badTargets J bad z).card : ℝ)

/-- The exact incidence identity, before any real-valued estimate. -/
theorem sum_card_badTargets (A : Finset V) (J : Finset I) (bad : I → Finset V) :
    ∑ z ∈ A, (badTargets J bad z).card =
      ∑ j ∈ J, (A.filter fun z => z ∈ bad j).card := by
  simp only [badTargets, Finset.card_filter]
  exact Finset.sum_comm

/-- A square-error Markov bound, independent of the number of targets. -/
theorem card_manyBadRoots_le
    (A : Finset V) (J : Finset I) (bad : I → Finset V)
    (ε δ : ℝ) (hδ : 0 < δ) (hεδ : ε ≤ δ ^ 2)
    (hbad : ∀ j ∈ J, ((bad j).card : ℝ) ≤ ε * A.card) :
    ((manyBadRoots A J bad δ).card : ℝ) ≤ δ * A.card := by
  by_cases hJ : J = ∅
  · simp only [hJ, manyBadRoots, badTargets, Finset.filter_empty,
      Finset.card_empty, Nat.cast_zero, mul_zero, lt_self_iff_false,
      Finset.filter_false]
    positivity
  have hJpos : (0 : ℝ) < J.card := by
    exact_mod_cast Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hJ)
  let B := manyBadRoots A J bad δ
  by_cases hB : B.Nonempty
  · have hsumStrict :
        ∑ _z ∈ B, δ * J.card < ∑ z ∈ B, ((badTargets J bad z).card : ℝ) := by
      apply Finset.sum_lt_sum_of_nonempty hB
      intro z hz
      exact (Finset.mem_filter.mp hz).2
    have hsumSubset :
        ∑ z ∈ B, ((badTargets J bad z).card : ℝ) ≤
          ∑ z ∈ A, ((badTargets J bad z).card : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => by positivity)
    have hdouble :
        ∑ z ∈ A, ((badTargets J bad z).card : ℝ) =
          ∑ j ∈ J, ((A.filter fun z => z ∈ bad j).card : ℝ) := by
      exact_mod_cast sum_card_badTargets A J bad
    have hsumBound :
        ∑ j ∈ J, ((A.filter fun z => z ∈ bad j).card : ℝ) ≤
          ∑ _j ∈ J, ε * A.card := by
      apply Finset.sum_le_sum
      intro j hj
      apply le_trans ?_ (hbad j hj)
      exact_mod_cast Finset.card_le_card
        (show (A.filter fun z => z ∈ bad j) ⊆ bad j from fun _ hz =>
          (Finset.mem_filter.mp hz).2)
    have htotal : (B.card : ℝ) * (δ * J.card) < (J.card : ℝ) * (ε * A.card) := by
      simp only [Finset.sum_const, nsmul_eq_mul] at hsumStrict hsumBound
      linarith only [hsumStrict, hsumSubset, hdouble, hsumBound]
    have hscale := mul_le_mul_of_nonneg_right hεδ
      (show (0 : ℝ) ≤ (J.card : ℝ) * A.card by positivity)
    have hmain : (B.card : ℝ) * (δ * J.card) <
        (δ * A.card) * (δ * J.card) := by
      nlinarith only [htotal, hscale]
    exact ((mul_lt_mul_iff_left₀ (mul_pos hδ hJpos)).mp hmain).le
  · have hBempty : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hB
    change (B.card : ℝ) ≤ _
    rw [hBempty, Finset.card_empty, Nat.cast_zero]
    positivity

/-- A reservoir larger than the exceptional-root budget contains a root
with few bad targets. The retained targets avoid its bad incidences. -/
theorem exists_root_few_badTargets
    (A pool : Finset V) (J : Finset I) (bad : I → Finset V)
    (ε δ : ℝ) (hδ : 0 < δ) (hεδ : ε ≤ δ ^ 2)
    (hbad : ∀ j ∈ J, ((bad j).card : ℝ) ≤ ε * A.card)
    (hpool : pool ⊆ A) (hpoolCard : δ * A.card < pool.card) :
    ∃ z ∈ pool, ((badTargets J bad z).card : ℝ) ≤ δ * J.card ∧
      ∀ j ∈ J \ badTargets J bad z, z ∉ bad j := by
  have hcount := card_manyBadRoots_le A J bad ε δ hδ hεδ hbad
  have hless : (manyBadRoots A J bad δ).card < pool.card := by
    exact_mod_cast hcount.trans_lt hpoolCard
  obtain ⟨z, hz, hzbad⟩ := Finset.exists_mem_notMem_of_card_lt_card hless
  refine ⟨z, hz, ?_, ?_⟩
  · apply le_of_not_gt
    intro h
    exact hzbad (Finset.mem_filter.mpr ⟨hpool hz, h⟩)
  · intro j hj hbadj
    exact (Finset.mem_sdiff.mp hj).2
      (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hj).1, hbadj⟩)

/-- The regular-pair specialization used for the upper source witnesses. -/
theorem exists_root_upperTypical_most
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A pool : Finset V) (J : Finset I) (target : I → Finset V)
    (ε δ : ℝ) (hδ : 0 < δ) (hεδ : ε ≤ δ ^ 2)
    (huniform : ∀ j ∈ J, G.IsUniform ε A (target j))
    (hpool : pool ⊆ A) (hpoolCard : δ * A.card < pool.card) :
    ∃ z ∈ pool, ∃ D ⊆ J,
      (D.card : ℝ) ≤ δ * J.card ∧
      ∀ j ∈ J \ D, (Erdos547EC2.degreeInto G z (target j) : ℝ) ≤
        (G.edgeDensity A (target j) + ε) * (target j).card := by
  let bad := fun j => upperAtypicalVertices G ε A (target j)
  have hbad : ∀ j ∈ J, ((bad j).card : ℝ) ≤ ε * A.card := by
    intro j hj
    simpa only [mul_comm] using (huniform j hj).card_upperAtypicalVertices_le
  obtain ⟨z, hz, hcount, hgood⟩ :=
    exists_root_few_badTargets A pool J bad ε δ hδ hεδ hbad hpool hpoolCard
  refine ⟨z, hz, badTargets J bad z, Finset.filter_subset _ _, hcount, ?_⟩
  intro j hj
  apply le_of_not_gt
  intro hdeg
  exact hgood j hj (Finset.mem_filter.mpr ⟨hpool hz, hdeg⟩)

/-- Truncating a row on its bad targets has the precise capacity cost
used in the subsequent matching allocation. -/
theorem sum_le_truncated_add_budget
    (J D : Finset I) (w : I → ℝ) (δ N : ℝ)
    (hD : D ⊆ J) (hcard : (D.card : ℝ) ≤ δ * J.card)
    (hN : 0 ≤ N) (hw : ∀ j ∈ D, w j ≤ N) :
    ∑ j ∈ J, w j ≤ (∑ j ∈ J \ D, w j) + δ * J.card * N := by
  have hsum : ∑ j ∈ D, w j ≤ (D.card : ℝ) * N := by
    simpa only [nsmul_eq_mul] using Finset.sum_le_card_nsmul D w N hw
  have hscaled := mul_le_mul_of_nonneg_right hcard hN
  have hsplit := Finset.sum_sdiff hD (f := w)
  linarith only [hsum, hscaled, hsplit]

end Erdos547b.ZhaoSourceRootIncidence

#print axioms Erdos547b.ZhaoSourceRootIncidence.sum_card_badTargets
#print axioms Erdos547b.ZhaoSourceRootIncidence.card_manyBadRoots_le
#print axioms Erdos547b.ZhaoSourceRootIncidence.exists_root_few_badTargets
#print axioms Erdos547b.ZhaoSourceRootIncidence.exists_root_upperTypical_most
#print axioms Erdos547b.ZhaoSourceRootIncidence.sum_le_truncated_add_budget
