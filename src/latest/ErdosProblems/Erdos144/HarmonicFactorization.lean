/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ErdosProblems.Erdos144.HarmonicProb
import ErdosProblems.Erdos144.HarmonicBlocks

/-!
# Factorization of finite harmonic Bernoulli blocks

This file records the elementary independence identities used when a random
set already exposed on one finite block is extended by a fresh, disjoint
block.  Everything is an identity or inequality between finite sums.
-/

open scoped BigOperators

namespace Erdos144.HarmonicFactorization

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The Bernoulli weight factors over two disjoint coordinate blocks. -/
theorem bernoulli_weight_union {I J B F : Finset ℕ} {p : ℕ → ℝ}
    (hIJ : Disjoint I J) (hBI : B ⊆ I) (hFJ : F ⊆ J) :
    Erdos697.Bernoulli.weight (I ∪ J) p (B ∪ F) =
      Erdos697.Bernoulli.weight I p B *
        Erdos697.Bernoulli.weight J p F := by
  have hBF : Disjoint B F := by
    rw [Finset.disjoint_left]
    intro x hxB hxF
    exact Finset.disjoint_left.mp hIJ (hBI hxB) (hFJ hxF)
  have hcomp : (I ∪ J) \ (B ∪ F) = (I \ B) ∪ (J \ F) := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨hxI | hxJ, hxBF⟩
      · exact Or.inl ⟨hxI, fun hxB ↦ hxBF (Or.inl hxB)⟩
      · exact Or.inr ⟨hxJ, fun hxF ↦ hxBF (Or.inr hxF)⟩
    · rintro (⟨hxI, hxB⟩ | ⟨hxJ, hxF⟩)
      · exact ⟨Or.inl hxI, fun hxBF ↦ hxBF.elim hxB (fun hxF ↦
          Finset.disjoint_left.mp hIJ hxI (hFJ hxF))⟩
      · exact ⟨Or.inr hxJ, fun hxBF ↦ hxBF.elim (fun hxB' ↦
          Finset.disjoint_left.mp hIJ (hBI hxB') hxJ) hxF⟩
  have hcompDisj : Disjoint (I \ B) (J \ F) :=
    hIJ.mono (Finset.sdiff_subset.trans (subset_refl I))
      (Finset.sdiff_subset.trans (subset_refl J))
  unfold Erdos697.Bernoulli.weight
  rw [Finset.prod_union hBF, hcomp, Finset.prod_union hcompDisj]
  ring

/-- Harmonic specialization of `bernoulli_weight_union`. -/
theorem harmonic_weight_union {I J B F : Finset ℕ}
    (hIJ : Disjoint I J) (hBI : B ⊆ I) (hFJ : F ⊆ J) :
    HarmonicProb.weight (I ∪ J) (B ∪ F) =
      HarmonicProb.weight I B * HarmonicProb.weight J F := by
  exact bernoulli_weight_union hIJ hBI hFJ

/-- On powersets of disjoint blocks, taking the union is injective. -/
theorem union_injective_on_powersets {I J : Finset ℕ} (hIJ : Disjoint I J) :
    Set.InjOn (fun q : Finset ℕ × Finset ℕ ↦ q.1 ∪ q.2)
      (↑(I.powerset ×ˢ J.powerset) : Set (Finset ℕ × Finset ℕ)) := by
  intro q hq r hr hqr
  have hqI : q.1 ⊆ I := Finset.mem_powerset.mp (Finset.mem_product.mp hq).1
  have hqJ : q.2 ⊆ J := Finset.mem_powerset.mp (Finset.mem_product.mp hq).2
  have hrI : r.1 ⊆ I := Finset.mem_powerset.mp (Finset.mem_product.mp hr).1
  have hrJ : r.2 ⊆ J := Finset.mem_powerset.mp (Finset.mem_product.mp hr).2
  change q.1 ∪ q.2 = r.1 ∪ r.2 at hqr
  apply Prod.ext
  · ext x
    constructor
    · intro hx
      have : x ∈ r.1 ∪ r.2 := by rw [← hqr]; exact Finset.mem_union_left _ hx
      rcases Finset.mem_union.mp this with hxR | hxR
      · exact hxR
      · exact False.elim (Finset.disjoint_left.mp hIJ (hqI hx) (hrJ hxR))
    · intro hx
      have : x ∈ q.1 ∪ q.2 := by rw [hqr]; exact Finset.mem_union_left _ hx
      rcases Finset.mem_union.mp this with hxQ | hxQ
      · exact hxQ
      · exact False.elim (Finset.disjoint_left.mp hIJ (hrI hx) (hqJ hxQ))
  · ext x
    constructor
    · intro hx
      have : x ∈ r.1 ∪ r.2 := by rw [← hqr]; exact Finset.mem_union_right _ hx
      rcases Finset.mem_union.mp this with hxR | hxR
      · exact False.elim (Finset.disjoint_left.mp hIJ (hrI hxR) (hqJ hx))
      · exact hxR
    · intro hx
      have : x ∈ q.1 ∪ q.2 := by rw [hqr]; exact Finset.mem_union_right _ hx
      rcases Finset.mem_union.mp this with hxQ | hxQ
      · exact False.elim (Finset.disjoint_left.mp hIJ (hqI hxQ) (hrJ hx))
      · exact hxQ

/-- Every subset of a union of disjoint blocks has a unique old/fresh
decomposition.  This is the finite sample-space form of independence. -/
theorem sum_powerset_union {I J : Finset ℕ} (hIJ : Disjoint I J)
    (f : Finset ℕ → ℝ) :
    (∑ T ∈ (I ∪ J).powerset, f T) =
      ∑ B ∈ I.powerset, ∑ F ∈ J.powerset, f (B ∪ F) := by
  have hbij :
      (∑ q ∈ I.powerset ×ˢ J.powerset, f (q.1 ∪ q.2)) =
        ∑ T ∈ (I ∪ J).powerset, f T := by
    apply Finset.sum_bij (fun q _ ↦ q.1 ∪ q.2)
    · intro q hq
      rw [Finset.mem_powerset]
      exact Finset.union_subset_union
        (Finset.mem_powerset.mp (Finset.mem_product.mp hq).1)
        (Finset.mem_powerset.mp (Finset.mem_product.mp hq).2)
    · intro q hq r hr h
      exact union_injective_on_powersets hIJ hq hr h
    · intro T hT
      refine ⟨(T ∩ I, T ∩ J), ?_, ?_⟩
      · rw [Finset.mem_product]
        exact ⟨Finset.mem_powerset.mpr Finset.inter_subset_right,
          Finset.mem_powerset.mpr Finset.inter_subset_right⟩
      · ext x
        have hxsub := Finset.mem_powerset.mp hT
        simp only [Finset.mem_union, Finset.mem_inter]
        aesop
    · intro q hq
      rfl
  rw [← hbij, Finset.sum_product]

/-- Filtered form of `sum_powerset_union`. -/
theorem sum_filter_powerset_union {I J : Finset ℕ} (hIJ : Disjoint I J)
    (P : Finset ℕ → Prop) [DecidablePred P] (f : Finset ℕ → ℝ) :
    (∑ T ∈ (I ∪ J).powerset.filter P, f T) =
      ∑ B ∈ I.powerset,
        ∑ F ∈ J.powerset.filter (fun F ↦ P (B ∪ F)), f (B ∪ F) := by
  rw [Finset.sum_filter, sum_powerset_union hIJ]
  apply Finset.sum_congr rfl
  intro B hB
  rw [Finset.sum_filter]

/-- Exact old-block/fresh-block conditional probability formula. -/
theorem prob_union_eq_sum_conditionals {I J : Finset ℕ}
    (hIJ : Disjoint I J) (P : Finset ℕ → Prop) [DecidablePred P] :
    HarmonicProb.prob (I ∪ J) P =
      ∑ B ∈ I.powerset, HarmonicProb.weight I B *
        HarmonicProb.prob J (fun F ↦ P (B ∪ F)) := by
  rw [HarmonicProb.prob, sum_filter_powerset_union hIJ]
  apply Finset.sum_congr rfl
  intro B hB
  rw [HarmonicProb.prob, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro F hF
  rw [harmonic_weight_union hIJ (Finset.mem_powerset.mp hB)
    (Finset.mem_powerset.mp (Finset.mem_filter.mp hF).1)]

/-- Writing a filtered probability as a full powerset sum with a zero-one
indicator. -/
theorem sum_ite_weight_eq_prob (s : Finset ℕ) (P : Finset ℕ → Prop)
    [DecidablePred P] :
    (∑ T ∈ s.powerset, if P T then HarmonicProb.weight s T else 0) =
      HarmonicProb.prob s P := by
  rw [HarmonicProb.prob, Finset.sum_filter]

/-- The probability of an explicitly listed family of exact samples is the
sum of their weights.  The finset representation already records that the
samples are pairwise distinct. -/
theorem prob_mem_sampleFamily {s : Finset ℕ} {E : Finset (Finset ℕ)}
    (hE : E ⊆ s.powerset) :
    HarmonicProb.prob s (fun T ↦ T ∈ E) =
      ∑ T ∈ E, HarmonicProb.weight s T := by
  have hfilter : s.powerset.filter (fun T ↦ T ∈ E) = E := by
    ext T
    constructor
    · intro hT
      exact (Finset.mem_filter.mp hT).2
    · intro hT
      exact Finset.mem_filter.mpr ⟨hE hT, hT⟩
  rw [HarmonicProb.prob, hfilter]

/-! ## One fresh-block step -/

/-- The exact finite recurrence before the exceptional histories are bounded.

`Success` is assumed monotone.  For every old history which is both bad and
regular, `Fresh B` describes a fresh event of probability at least `q`, and
that event forces success after adjoining the new block.  The conclusion
charges a regular bad history only `1-q`, while an irregular bad history is
charged the full unit mass. -/
theorem extension_bad_bound
    {I J : Finset ℕ} (hIJ : Disjoint I J)
    (hI : ∀ n ∈ I, 1 ≤ n) (hJ : ∀ n ∈ J, 1 ≤ n)
    (Success Irregular : Finset ℕ → Prop)
    (Fresh : Finset ℕ → Finset ℕ → Prop)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hmono : ∀ ⦃S T : Finset ℕ⦄, S ⊆ T → Success S → Success T)
    (hforce : ∀ B ∈ I.powerset, ¬ Success B → ¬ Irregular B →
      ∀ F, Fresh B F → Success (B ∪ F))
    (hfresh : ∀ B ∈ I.powerset, ¬ Success B → ¬ Irregular B →
      q ≤ HarmonicProb.prob J (Fresh B)) :
    HarmonicProb.prob (I ∪ J) (fun T ↦ ¬ Success T) ≤
      (1 - q) * HarmonicProb.prob I (fun B ↦ ¬ Success B) +
        q * HarmonicProb.prob I (fun B ↦ ¬ Success B ∧ Irregular B) := by
  rw [prob_union_eq_sum_conditionals hIJ]
  calc
    (∑ B ∈ I.powerset, HarmonicProb.weight I B *
        HarmonicProb.prob J (fun F ↦ ¬ Success (B ∪ F))) ≤
      ∑ B ∈ I.powerset,
        ((1 - q) * (if ¬ Success B then HarmonicProb.weight I B else 0) +
          q * (if ¬ Success B ∧ Irregular B then
            HarmonicProb.weight I B else 0)) := by
      apply Finset.sum_le_sum
      intro B hB
      have hwB : 0 ≤ HarmonicProb.weight I B :=
        HarmonicProb.weight_nonneg hI
      by_cases hsuccess : Success B
      · have hzero :
          HarmonicProb.prob J (fun F ↦ ¬ Success (B ∪ F)) = 0 := by
          unfold HarmonicProb.prob
          apply Finset.sum_eq_zero
          intro F hF
          exfalso
          exact (Finset.mem_filter.mp hF).2
            (hmono Finset.subset_union_left hsuccess)
        simp [hsuccess, hzero]
      · by_cases hirregular : Irregular B
        · have hcond :
            HarmonicProb.prob J (fun F ↦ ¬ Success (B ∪ F)) ≤ 1 :=
              HarmonicProb.prob_le_one J _ hJ
          simp only [hsuccess, not_false_eq_true, if_true, hirregular,
            and_self]
          calc
            HarmonicProb.weight I B *
                HarmonicProb.prob J (fun F ↦ ¬ Success (B ∪ F)) ≤
              HarmonicProb.weight I B * 1 :=
                mul_le_mul_of_nonneg_left hcond hwB
            _ = (1 - q) * HarmonicProb.weight I B +
                q * HarmonicProb.weight I B := by ring
        · have hsubset :
            HarmonicProb.prob J (fun F ↦ ¬ Success (B ∪ F)) ≤
              HarmonicProb.prob J (fun F ↦ ¬ Fresh B F) := by
              apply HarmonicProb.prob_mono J _ _ hJ
              intro F hbad hFresh
              exact hbad (hforce B hB hsuccess hirregular F hFresh)
          have hnot :
              HarmonicProb.prob J (fun F ↦ ¬ Fresh B F) =
                1 - HarmonicProb.prob J (Fresh B) :=
            HarmonicProb.prob_not J (Fresh B)
          have hcond :
              HarmonicProb.prob J (fun F ↦ ¬ Success (B ∪ F)) ≤
                1 - q := by
            rw [hnot] at hsubset
            linarith [hfresh B hB hsuccess hirregular]
          simp only [hsuccess, not_false_eq_true, if_true, hirregular,
            and_false]
          convert (mul_le_mul_of_nonneg_left hcond hwB) using 1 <;>
            simp [hirregular] <;> ring
    _ = (1 - q) * HarmonicProb.prob I (fun B ↦ ¬ Success B) +
        q * HarmonicProb.prob I (fun B ↦ ¬ Success B ∧ Irregular B) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        sum_ite_weight_eq_prob, sum_ite_weight_eq_prob]

/-- One-step bad-event recurrence after bounding the mass of exceptional old
histories by `delta`.  This is the affine estimate
`b' ≤ (1-q)b + q*delta` used in the block iteration. -/
theorem extension_bad_bound_of_irregular_mass
    {I J : Finset ℕ} (hIJ : Disjoint I J)
    (hI : ∀ n ∈ I, 1 ≤ n) (hJ : ∀ n ∈ J, 1 ≤ n)
    (Success Irregular : Finset ℕ → Prop)
    (Fresh : Finset ℕ → Finset ℕ → Prop)
    (q delta : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hmono : ∀ ⦃S T : Finset ℕ⦄, S ⊆ T → Success S → Success T)
    (hforce : ∀ B ∈ I.powerset, ¬ Success B → ¬ Irregular B →
      ∀ F, Fresh B F → Success (B ∪ F))
    (hfresh : ∀ B ∈ I.powerset, ¬ Success B → ¬ Irregular B →
      q ≤ HarmonicProb.prob J (Fresh B))
    (hirregular :
      HarmonicProb.prob I (fun B ↦ ¬ Success B ∧ Irregular B) ≤ delta) :
    HarmonicProb.prob (I ∪ J) (fun T ↦ ¬ Success T) ≤
      (1 - q) * HarmonicProb.prob I (fun B ↦ ¬ Success B) + q * delta := by
  calc
    HarmonicProb.prob (I ∪ J) (fun T ↦ ¬ Success T) ≤
        (1 - q) * HarmonicProb.prob I (fun B ↦ ¬ Success B) +
          q * HarmonicProb.prob I (fun B ↦ ¬ Success B ∧ Irregular B) :=
      extension_bad_bound hIJ hI hJ Success Irregular Fresh q hq0 hq1
        hmono hforce hfresh
    _ ≤ (1 - q) * HarmonicProb.prob I (fun B ↦ ¬ Success B) +
        q * delta := by
      gcongr

/-- Sample-family form of the one-step recurrence.  For each regular bad old
history, `Samples B` is an explicit disjoint family of fresh exact samples;
membership in any one of them forces success, and their total fresh-block
weight is at least `q`. -/
theorem extension_bad_bound_of_sampleFamilies
    {I J : Finset ℕ} (hIJ : Disjoint I J)
    (hI : ∀ n ∈ I, 1 ≤ n) (hJ : ∀ n ∈ J, 1 ≤ n)
    (Success Irregular : Finset ℕ → Prop)
    (Samples : Finset ℕ → Finset (Finset ℕ))
    (q delta : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hmono : ∀ ⦃S T : Finset ℕ⦄, S ⊆ T → Success S → Success T)
    (hSamples : ∀ B ∈ I.powerset, Samples B ⊆ J.powerset)
    (hforce : ∀ B ∈ I.powerset, ¬ Success B → ¬ Irregular B →
      ∀ F ∈ Samples B, Success (B ∪ F))
    (hmass : ∀ B ∈ I.powerset, ¬ Success B → ¬ Irregular B →
      q ≤ HarmonicProb.prob J (fun F ↦ F ∈ Samples B))
    (hirregular :
      HarmonicProb.prob I (fun B ↦ ¬ Success B ∧ Irregular B) ≤ delta) :
    HarmonicProb.prob (I ∪ J) (fun T ↦ ¬ Success T) ≤
      (1 - q) * HarmonicProb.prob I (fun B ↦ ¬ Success B) + q * delta := by
  apply extension_bad_bound_of_irregular_mass hIJ hI hJ Success Irregular
    (fun B F ↦ F ∈ Samples B) q delta hq0 hq1 hmono
  · intro B hB hbad hregular F hF
    exact hforce B hB hbad hregular F hF
  · intro B hB hbad hregular
    have h := hmass B hB hbad hregular
    unfold HarmonicProb.prob at h ⊢
    calc
      q ≤ _ := h
      _ = _ := by
        apply Finset.sum_congr
        · ext F
          simp
        · intro F hF
          rfl
  · exact hirregular

end

end Erdos144.HarmonicFactorization
