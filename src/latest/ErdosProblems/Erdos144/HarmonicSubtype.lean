/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ErdosProblems.Erdos144.Harmonic

/-!
# Transporting the harmonic model to a subtype index set

The harmonic model is naturally stated using subsets of a finite set
`I : Finset ℕ`, whereas the CRT occupancy model is indexed by the finite type
`I`.  This file proves the exact change-of-index identity between those two
representations, including equality of every individual Bernoulli weight.
-/

open scoped BigOperators Classical

namespace Erdos144.HarmonicSubtype

noncomputable section

/-- The canonical embedding of the subtype associated to a finite set. -/
def valueEmbedding (I : Finset ℕ) : ↥I ↪ ℕ where
  toFun := Subtype.val
  inj' := Subtype.val_injective

/-- Lift a subset of `I` to a finset of elements of the subtype `I`. -/
def lift (I U : Finset ℕ) : Finset ↥I :=
  I.attach.filter fun i ↦ i.val ∈ U

@[simp] theorem mem_lift {I U : Finset ℕ} (i : ↥I) :
    i ∈ lift I U ↔ i.val ∈ U := by
  simp [lift]

@[simp] theorem map_valueEmbedding_univ (I : Finset ℕ) :
    (Finset.univ : Finset ↥I).map (valueEmbedding I) = I := by
  ext n
  simp [valueEmbedding]

theorem map_lift {I U : Finset ℕ} (hUI : U ⊆ I) :
    (lift I U).map (valueEmbedding I) = U := by
  ext n
  constructor
  · intro hn
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hn
    exact (mem_lift i).mp hi
  · intro hn
    let i : ↥I := ⟨n, hUI hn⟩
    exact Finset.mem_map.mpr ⟨i, (mem_lift i).mpr hn, rfl⟩

@[simp] theorem image_value_eq_map (I : Finset ℕ) (T : Finset ↥I) :
    T.image Subtype.val = T.map (valueEmbedding I) := by
  exact (Finset.map_eq_image (valueEmbedding I) T).symm

/-- Changing from the subtype index set to its set of values preserves each
individual Bernoulli product weight exactly. -/
theorem bernoulli_weight_image_value
    (I : Finset ℕ) (p : ℕ → ℝ) (T : Finset ↥I) :
    Erdos697.Bernoulli.weight I p (T.image Subtype.val) =
      Erdos697.Bernoulli.weight (Finset.univ : Finset ↥I)
        (fun i ↦ p i.val) T := by
  rw [image_value_eq_map]
  unfold Erdos697.Bernoulli.weight
  have hdiff :
      I \ T.map (valueEmbedding I) =
        ((Finset.univ : Finset ↥I) \ T).map (valueEmbedding I) := by
    rw [Finset.map_sdiff, map_valueEmbedding_univ]
  rw [hdiff]
  simp [Finset.prod_map, valueEmbedding]

/-- Generic exact event transport from the harmonic model on `I` to the
Bernoulli model indexed by the finite subtype `I`. -/
theorem prob_eq_subtype_sum (I : Finset ℕ)
    (P : Finset ℕ → Prop) [DecidablePred P] :
    HarmonicProb.prob I P =
      ∑ T ∈ (Finset.univ : Finset ↥I).powerset.filter
          (fun T ↦ P (T.image Subtype.val)),
        Erdos697.Bernoulli.weight (Finset.univ : Finset ↥I)
          (fun i ↦ HarmonicProb.param i.val) T := by
  classical
  unfold HarmonicProb.prob HarmonicProb.weight
  symm
  refine Finset.sum_bij (fun T _ ↦ T.image Subtype.val) ?_ ?_ ?_ ?_
  · intro T hT
    rw [Finset.mem_filter] at hT ⊢
    refine ⟨?_, hT.2⟩
    rw [Finset.mem_powerset]
    intro n hn
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hn
    exact i.property
  · intro T₁ _hT₁ T₂ _hT₂ hEq
    exact Finset.image_injective Subtype.val_injective hEq
  · intro U hU
    rw [Finset.mem_filter, Finset.mem_powerset] at hU
    let T := lift I U
    have hmap : T.image Subtype.val = U := by
      rw [image_value_eq_map]
      exact map_lift hU.1
    refine ⟨T, ?_, hmap⟩
    rw [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.subset_univ T, hmap ▸ hU.2⟩
  · intro T _hT
    exact (bernoulli_weight_image_value I HarmonicProb.param T).symm

/-- The exact transport needed for the bounded equal-subsum event. -/
theorem boundedEqualSubsum_prob_eq_subtype_sum (I : Finset ℕ) (L : ℕ) :
    HarmonicProb.prob I
        (fun T ↦ Harmonic.HasEqualSubsums T ∧ T.card ≤ L) =
      ∑ T ∈ (Finset.univ : Finset ↥I).powerset.filter
          (fun T ↦
            Harmonic.HasEqualSubsums (T.image Subtype.val) ∧ T.card ≤ L),
        Erdos697.Bernoulli.weight (Finset.univ : Finset ↥I)
          (fun i ↦ 1 / (i.val : ℝ)) T := by
  classical
  have hcard : ∀ T : Finset ↥I,
      (T.image Subtype.val).card = T.card := fun T ↦
    Finset.card_image_iff.mpr Subtype.val_injective.injOn
  simpa only [HarmonicProb.param, hcard] using
    (prob_eq_subtype_sum I
      (fun T ↦ Harmonic.HasEqualSubsums T ∧ T.card ≤ L))

end

end Erdos144.HarmonicSubtype
