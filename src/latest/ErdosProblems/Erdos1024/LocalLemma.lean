/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A finite asymmetric local lemma

This is a cardinality-level local lemma for a uniform finite probability
space.  The hypothesis is phrased for the actual neighbor set occurring in
each conditioning family.  That slightly strengthened form avoids any
symmetry assumption on `dep` and is exactly what the two-event-type
application for Erdős Problem 1024 verifies.
-/

open scoped BigOperators

namespace Erdos1024
namespace LocalLemma

variable {Omega ι : Type*}

/-- Uniform probability on a nonempty finite type. -/
noncomputable def uniformProbability [Fintype Omega] (s : Finset Omega) : ℝ :=
  (s.card : ℝ) / Fintype.card Omega

/-- Outcomes avoiding every event indexed by `S`. -/
def avoiding [Fintype Omega] [DecidableEq Omega] [DecidableEq ι]
    (event : ι → Finset Omega) (S : Finset ι) : Finset Omega :=
  Finset.univ.filter fun omega ↦ ∀ i ∈ S, omega ∉ event i

section Elementary

variable [Fintype Omega] [Nonempty Omega] [DecidableEq Omega]

lemma card_pos : 0 < (Fintype.card Omega : ℝ) := by
  exact_mod_cast Fintype.card_pos

lemma uniformProbability_nonneg (s : Finset Omega) :
    0 ≤ uniformProbability s := by
  exact div_nonneg (by positivity) card_pos.le

lemma uniformProbability_mono {s t : Finset Omega} (hst : s ⊆ t) :
    uniformProbability s ≤ uniformProbability t := by
  unfold uniformProbability
  exact div_le_div_of_nonneg_right
    (by exact_mod_cast Finset.card_le_card hst) card_pos.le

lemma uniformProbability_univ :
    uniformProbability (Finset.univ : Finset Omega) = 1 := by
  simp [uniformProbability, ne_of_gt card_pos]

lemma uniformProbability_pos_iff_nonempty (s : Finset Omega) :
    0 < uniformProbability s ↔ s.Nonempty := by
  constructor
  · intro h
    rw [uniformProbability, div_pos_iff] at h
    rcases h with h | h
    · exact Finset.card_pos.mp (by exact_mod_cast h.1)
    · exfalso
      linarith [card_pos (Omega := Omega)]
  · intro hs
    exact div_pos (by exact_mod_cast hs.card_pos) card_pos

end Elementary

section Avoiding

variable [Fintype Omega] [Nonempty Omega] [DecidableEq Omega]
variable [Fintype ι] [DecidableEq ι]
variable (event : ι → Finset Omega)

@[simp] lemma avoiding_empty : avoiding event ∅ = Finset.univ := by
  ext
  simp [avoiding]

lemma avoiding_mono {S T : Finset ι} (hST : S ⊆ T) :
    avoiding event T ⊆ avoiding event S := by
  intro omega homega
  simp only [avoiding, Finset.mem_filter, Finset.mem_univ, true_and] at homega ⊢
  intro i hi
  exact homega i (hST hi)

lemma avoiding_insert (i : ι) (S : Finset ι) :
    avoiding event (insert i S) = avoiding event S \ event i := by
  ext omega
  simp [avoiding, and_comm]

lemma avoiding_partition (i : ι) (S : Finset ι) :
    avoiding event S =
      avoiding event (insert i S) ∪ (event i ∩ avoiding event S) := by
  ext omega
  by_cases h : omega ∈ event i <;> simp [avoiding, h]

lemma uniformProbability_avoiding_partition (i : ι) (S : Finset ι) :
    uniformProbability (avoiding event S) =
      uniformProbability (avoiding event (insert i S)) +
        uniformProbability (event i ∩ avoiding event S) := by
  rw [congrArg uniformProbability (avoiding_partition event i S)]
  unfold uniformProbability
  rw [Finset.card_union_of_disjoint]
  · push_cast
    ring
  · rw [Finset.disjoint_left]
    intro omega homegaAvoid homegaEvent
    rw [avoiding_insert] at homegaAvoid
    exact (Finset.mem_sdiff.mp homegaAvoid).2 (Finset.mem_inter.mp homegaEvent).1

end Avoiding

section Asymmetric

variable [Fintype Omega] [Nonempty Omega] [DecidableEq Omega]
variable [Fintype ι] [DecidableEq ι]

/--
Finite asymmetric Lovász local lemma.

The hypothesis `h_event` is the usual local-lemma product criterion, stated
for the neighbors of `i` actually present in an arbitrary conditioning set
`S`.  `h_indep` says that event `i` is independent of simultaneous avoidance
of any collection of non-neighbors.
-/
theorem exists_avoiding_of_asymmetric
    (event : ι → Finset Omega) (dep : ι → ι → Prop) [DecidableRel dep]
    (x : ι → ℝ)
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
    (h_event : ∀ i (S : Finset ι), i ∉ S →
      uniformProbability (event i) ≤
        x i * ∏ j ∈ S.filter (dep i), (1 - x j))
    (h_indep : ∀ i S, (∀ j ∈ S, ¬ dep i j) →
      uniformProbability (event i ∩ avoiding event S) =
        uniformProbability (event i) * uniformProbability (avoiding event S)) :
    ∃ omega : Omega, ∀ i, omega ∉ event i := by
  have hfactor0 (i : ι) : 0 ≤ 1 - x i := sub_nonneg.mpr (hx1 i).le

  /- The standard inductive conditional estimate, written without division
  so it remains meaningful before positivity of all denominators is known. -/
  have conditional : ∀ S : Finset ι, ∀ i ∉ S,
      uniformProbability (event i ∩ avoiding event S) ≤
        x i * uniformProbability (avoiding event S) := by
    intro S
    induction S using Finset.strongInduction with
    | H S ih =>
      intro i hiS
      let N : Finset ι := S.filter (dep i)
      let F : Finset ι := S.filter fun j ↦ ¬ dep i j
      have hNF : S = N ∪ F := by
        ext j
        by_cases hj : dep i j <;> simp [N, F, hj]
      have hNsub : N ⊆ S := Finset.filter_subset _ _
      have hFsub : F ⊆ S := Finset.filter_subset _ _
      have hNFdisj : Disjoint N F := by
        rw [Finset.disjoint_left]
        intro j hjN hjF
        exact (Finset.mem_filter.mp hjF).2 (Finset.mem_filter.mp hjN).2
      have hF_nonNeighbor (j : ι) (hj : j ∈ F) : ¬ dep i j :=
        (Finset.mem_filter.mp hj).2
      have havoidSub : avoiding event S ⊆ avoiding event F :=
        avoiding_mono event hFsub
      have heventSub : event i ∩ avoiding event S ⊆
          event i ∩ avoiding event F :=
        Finset.inter_subset_inter (fun _ hmem ↦ hmem) havoidSub
      have hnum : uniformProbability (event i ∩ avoiding event S) ≤
          uniformProbability (event i) * uniformProbability (avoiding event F) := by
        calc
          uniformProbability (event i ∩ avoiding event S) ≤
              uniformProbability (event i ∩ avoiding event F) :=
            uniformProbability_mono heventSub
          _ = uniformProbability (event i) * uniformProbability (avoiding event F) :=
            h_indep i F hF_nonNeighbor

      /- Successively insert the neighbors in `T`.  At every insertion the
      strong induction hypothesis loses at most the corresponding factor
      `1 - x j`. -/
      have hproduct : ∀ T : Finset ι, T ⊆ N →
          (∏ j ∈ T, (1 - x j)) * uniformProbability (avoiding event F) ≤
            uniformProbability (avoiding event (T ∪ F)) := by
        intro T hTN
        induction T using Finset.induction with
        | empty =>
          simp
        | @insert j T hjT hT =>
          have hjN : j ∈ N := hTN (Finset.mem_insert_self j T)
          have hTN' : T ⊆ N := fun k hk ↦ hTN (Finset.mem_insert_of_mem hk)
          have hjF : j ∉ F := by
            exact fun h ↦ Finset.disjoint_left.mp hNFdisj hjN h
          have hjTF : j ∉ T ∪ F := by simp [hjT, hjF]
          have hTFsub : T ∪ F ⊆ S := by
            intro k hk
            rcases Finset.mem_union.mp hk with hk | hk
            · exact hNsub (hTN' hk)
            · exact hFsub hk
          have hstrictTF : T ∪ F ⊂ S := by
            apply Finset.ssubset_iff_subset_ne.mpr
            refine ⟨hTFsub, ?_⟩
            intro heq
            apply hjTF
            rw [heq]
            exact hNsub hjN
          have hcond := ih (T ∪ F) hstrictTF j hjTF
          have hstep : (1 - x j) * uniformProbability (avoiding event (T ∪ F)) ≤
              uniformProbability (avoiding event (insert j (T ∪ F))) := by
            have hpart := uniformProbability_avoiding_partition event j (T ∪ F)
            nlinarith
          calc
            (∏ k ∈ insert j T, (1 - x k)) *
                uniformProbability (avoiding event F) =
                (1 - x j) *
                  ((∏ k ∈ T, (1 - x k)) *
                    uniformProbability (avoiding event F)) := by
              rw [Finset.prod_insert hjT]
              ring
            _ ≤ (1 - x j) * uniformProbability (avoiding event (T ∪ F)) :=
              mul_le_mul_of_nonneg_left (hT hTN') (hfactor0 j)
            _ ≤ uniformProbability (avoiding event (insert j (T ∪ F))) := hstep
            _ = uniformProbability (avoiding event (insert j T ∪ F)) := by
              congr 2
              ext k
              simp [or_assoc, or_left_comm]

      have hprodN : (∏ j ∈ N, (1 - x j)) *
          uniformProbability (avoiding event F) ≤
            uniformProbability (avoiding event S) := by
        simpa [hNF] using hproduct N (fun _ hmem ↦ hmem)
      have hevent := h_event i S hiS
      change uniformProbability (event i) ≤
        x i * ∏ j ∈ N, (1 - x j) at hevent
      calc
        uniformProbability (event i ∩ avoiding event S) ≤
            uniformProbability (event i) * uniformProbability (avoiding event F) := hnum
        _ ≤ (x i * ∏ j ∈ N, (1 - x j)) *
              uniformProbability (avoiding event F) := by
            exact mul_le_mul_of_nonneg_right hevent
              (uniformProbability_nonneg (avoiding event F))
        _ = x i * ((∏ j ∈ N, (1 - x j)) *
              uniformProbability (avoiding event F)) := by ring
        _ ≤ x i * uniformProbability (avoiding event S) :=
          mul_le_mul_of_nonneg_left hprodN (hx0 i)

  have avoiding_pos : ∀ S : Finset ι,
      0 < uniformProbability (avoiding event S) := by
    intro S
    induction S using Finset.induction with
    | empty =>
      rw [avoiding_empty, uniformProbability_univ]
      norm_num
    | @insert i S hi ih =>
      have hcond := conditional S i hi
      have hpart := uniformProbability_avoiding_partition event i S
      have hfactor : 0 < 1 - x i := sub_pos.mpr (hx1 i)
      nlinarith

  have hall := avoiding_pos (Finset.univ : Finset ι)
  have hnonempty : (avoiding event (Finset.univ : Finset ι)).Nonempty :=
    (uniformProbability_pos_iff_nonempty _).mp hall
  obtain ⟨omega, homega⟩ := hnonempty
  refine ⟨omega, fun i ↦ ?_⟩
  simp only [avoiding, Finset.mem_filter, Finset.mem_univ, true_and] at homega
  exact homega i trivial

end Asymmetric

end LocalLemma
end Erdos1024

#print axioms Erdos1024.LocalLemma.exists_avoiding_of_asymmetric
