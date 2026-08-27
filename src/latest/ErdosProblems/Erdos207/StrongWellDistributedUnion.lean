/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.StrongWellDistributed
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Joint inclusion in the union of the master families

Strong well-distributedness prescribes separately the initial family and the
later family.  A prescribed set contained in their union can be partitioned
according to which of its members belong to the initial family.  Summing over
all such partitions gives the natural point weight which is the sum of the
two individual point weights.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

/-- Point weight for a triangle which may be supplied either by the initial
family or by the later family. -/
def masterUnionTriangleWeight
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (k : Fin (ell + 1)) (p : ℝ≥0)
    (T : TripleOn V) : ℝ≥0 :=
  (Fintype.card V : ℝ≥0)⁻¹ +
    p / ((W.U (W.truncatedLevel k T)).card : ℝ≥0)

/-- The product of the union weights is exactly the sum over all ways of
assigning the prescribed triangles to the initial and later families. -/
lemma setWeight_masterUnionTriangleWeight_eq_sum
    {V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (k : Fin (ell + 1)) (p : ℝ≥0)
    (T : TripleSystemOn V) :
    setWeight (masterUnionTriangleWeight W k p) T =
      ∑ S ∈ T.powerset,
        (Fintype.card V : ℝ≥0)⁻¹ ^ S.card *
          laterTriangleScale W k p (T \ S) := by
  classical
  unfold setWeight masterUnionTriangleWeight
  rw [Finset.prod_add]
  apply sum_congr rfl
  intro S hS
  simp only [laterTriangleScale]
  rw [prod_const]

/-- Inclusion in `initial ∪ later` implies one of the disjoint prescribed
events appearing in the definition of strong well-distributedness. -/
lemma subset_union_implies_strongDistributionEvent_partition
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V]
    (initial later : Ω → TripleSystemOn V)
    (T : TripleSystemOn V) (ω : Ω)
    (hT : T ⊆ initial ω ∪ later ω) :
    ∃ S ∈ T.powerset,
      StrongDistributionEvent initial later S (T \ S) ∅ ω := by
  classical
  let S := T ∩ initial ω
  refine ⟨S, mem_powerset.mpr inter_subset_left, ?_⟩
  refine ⟨inter_subset_right, ?_, by simp⟩
  intro U hU
  obtain ⟨hUT, hUS⟩ := mem_sdiff.mp hU
  have hUunion := hT hUT
  rw [mem_union] at hUunion
  exact hUunion.resolve_left fun hUI ↦ hUS (by
    exact mem_inter.mpr ⟨hUT, hUI⟩)

/-- Strong well-distributedness gives a joint-inclusion estimate for the
union of the two selected master families.  The factor `2^|T|` is the cost
of forgetting which family supplied each prescribed triangle. -/
theorem IsStronglyWellDistributed.probability_subset_union_le
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Ω} {W : Vortex V ell} {k : Fin (ell + 1)}
    {initial later : Ω → TripleSystemOn V}
    {p C b : ℝ≥0}
    (h : IsStronglyWellDistributed L W k initial later p C b)
    (T : TripleSystemOn V) :
    L.probability (fun ω ↦ T ⊆ initial ω ∪ later ω) ≤
      ((2 : ℝ≥0) ^ T.card) *
        (C ^ T.card *
          (setWeight (masterUnionTriangleWeight W k p) T + b)) := by
  classical
  let Event : TripleSystemOn V → Ω → Prop := fun S ω ↦
    StrongDistributionEvent initial later S (T \ S) ∅ ω
  have hmono :
      L.probability (fun ω ↦ T ⊆ initial ω ∪ later ω) ≤
        L.probability (fun ω ↦ ∃ S ∈ T.powerset, Event S ω) := by
    apply L.probability_mono
    intro ω hT
    simpa only [Event] using
      subset_union_implies_strongDistributionEvent_partition
        initial later T ω hT
  have hpart : ∀ S ∈ T.powerset,
      L.probability (Event S) ≤
        C ^ T.card *
          (setWeight (masterUnionTriangleWeight W k p) T + b) := by
    intro S hS
    have hST : S ⊆ T := mem_powerset.mp hS
    have hdisj : Disjoint S (T \ S) := by
      rw [Finset.disjoint_left]
      intro U hUS hUTS
      exact (mem_sdiff.mp hUTS).2 hUS
    have hraw := h S (T \ S) ∅ hdisj
    have hcard : S.card + (T \ S).card = T.card := by
      rw [card_sdiff_of_subset hST]
      have hcardST : S.card ≤ T.card := card_le_card hST
      omega
    have hraw' : L.probability (Event S) ≤
        C ^ T.card *
          ((Fintype.card V : ℝ≥0)⁻¹ ^ S.card *
              laterTriangleScale W k p (T \ S) + b) := by
      simpa only [Event, card_empty, add_zero, pow_zero, one_mul, hcard]
        using hraw
    apply hraw'.trans
    gcongr
    rw [setWeight_masterUnionTriangleWeight_eq_sum]
    exact single_le_sum (fun U _hU ↦
      show (0 : ℝ≥0) ≤
        (Fintype.card V : ℝ≥0)⁻¹ ^ U.card *
          laterTriangleScale W k p (T \ U) from zero_le) hS
  calc
    L.probability (fun ω ↦ T ⊆ initial ω ∪ later ω) ≤
        L.probability (fun ω ↦ ∃ S ∈ T.powerset, Event S ω) := hmono
    _ ≤ ∑ S ∈ T.powerset, L.probability (Event S) :=
      L.probability_exists_le T.powerset Event
    _ ≤ ∑ _S ∈ T.powerset,
        C ^ T.card *
          (setWeight (masterUnionTriangleWeight W k p) T + b) := by
      exact sum_le_sum fun S hS ↦ hpart S hS
    _ = ((2 : ℝ≥0) ^ T.card) *
        (C ^ T.card *
          (setWeight (masterUnionTriangleWeight W k p) T + b)) := by
      simp

/-- On a bounded-size prescribed family, an additive error no larger than
the product weight can be absorbed into one fixed joint-inclusion constant. -/
theorem IsStronglyWellDistributed.probability_subset_union_le_product
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Ω} {W : Vortex V ell} {k : Fin (ell + 1)}
    {initial later : Ω → TripleSystemOn V}
    {p C b : ℝ≥0}
    (h : IsStronglyWellDistributed L W k initial later p C b)
    {d : ℕ} (hC : 1 ≤ C) (T : TripleSystemOn V)
    (hcard : T.card ≤ d)
    (hb : b ≤ setWeight (masterUnionTriangleWeight W k p) T) :
    L.probability (fun ω ↦ T ⊆ initial ω ∪ later ω) ≤
      (2 * (2 * C) ^ d) *
        setWeight (masterUnionTriangleWeight W k p) T := by
  have hbase := h.probability_subset_union_le T
  have hweight :
      setWeight (masterUnionTriangleWeight W k p) T + b ≤
        2 * setWeight (masterUnionTriangleWeight W k p) T := by
    calc
      setWeight (masterUnionTriangleWeight W k p) T + b ≤
          setWeight (masterUnionTriangleWeight W k p) T +
            setWeight (masterUnionTriangleWeight W k p) T :=
        add_le_add (le_refl _) hb
      _ = 2 * setWeight (masterUnionTriangleWeight W k p) T := by ring
  have htwoC : 1 ≤ 2 * C := by
    calc
      (1 : ℝ≥0) ≤ 2 := by norm_num
      _ ≤ 2 * C := by
        simpa using mul_le_mul_of_nonneg_left hC (show (0 : ℝ≥0) ≤ 2 from zero_le)
  have hpow : (2 * C) ^ T.card ≤ (2 * C) ^ d :=
    pow_le_pow_right₀ htwoC hcard
  calc
    L.probability (fun ω ↦ T ⊆ initial ω ∪ later ω) ≤
        ((2 : ℝ≥0) ^ T.card) *
          (C ^ T.card *
            (setWeight (masterUnionTriangleWeight W k p) T + b)) := hbase
    _ ≤ ((2 : ℝ≥0) ^ T.card) *
        (C ^ T.card *
          (2 * setWeight (masterUnionTriangleWeight W k p) T)) := by
      gcongr
    _ = (2 * (2 * C) ^ T.card) *
        setWeight (masterUnionTriangleWeight W k p) T := by
      rw [mul_pow]
      ring
    _ ≤ (2 * (2 * C) ^ d) *
        setWeight (masterUnionTriangleWeight W k p) T := by
      gcongr

end

end Erdos207
