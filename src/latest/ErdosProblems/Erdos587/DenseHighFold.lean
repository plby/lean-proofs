import ErdosProblems.Erdos587.HighFoldModels

/-!
Dense high-fold sumsets contain standardized proper GAPs. This transfers the
already proved mixed-filling theorem to the high-fold models, retaining the
coordinate multiplier bounds needed to compare larger dilations.
-/

open scoped Pointwise

namespace Erdos587.CFP

theorem highFold_subset_dilate_of_subset (A : Finset ℤ) (Q : GeneralizedAP)
    (hAQ : A ⊆ Q.carrier) (h : ℕ) : h • A ⊆ (Q.dilate h).carrier := by
  rw [← Q.nsmul_carrier]
  exact Finset.nsmul_subset_nsmul_left hAQ

/-- A bounded additional number of unrestricted summands fills a proper
standardized GAP. The summands here may repeat; this is not yet a subset-sum
containment theorem. -/
theorem exists_standardized_GAP_in_highFold_sumset
    (A : Finset ℤ) (Q : GeneralizedAP) (h D : ℕ) (hD : 0 < D)
    (hAQ : A ⊆ Q.carrier) (hproper : Q.TProper h)
    (hdense : (Q.dilate h).boxCard ≤ D * (h • A).card) :
    let q := nvDenseCount D Q.rank
    let F := GeneralizedAP.nvStandardSideFactor (Q.dilate h) D q
    ∃ S : GeneralizedAP, S.rank = Q.rank ∧ S.Proper ∧
      S.carrier ⊆ (q * h) • A ∧
      S.StepMultipliersBoundedByConstant Q (2 * q * F) ∧
      ∀ i : Fin S.rank, ∀ j : Fin Q.rank, i.val = j.val →
        S.length i = h * Q.length j / F := by
  let P := Q.dilate h
  let q := nvDenseCount D Q.rank
  let Xs := List.replicate q (h • A)
  have hlen : Xs.length = nvDenseCount D P.rank := by simp [Xs, q, P]
  have hsub : ∀ X ∈ Xs, X ⊆ P.carrier := by
    intro X hX
    have heq : X = h • A := (List.mem_replicate.mp hX).2
    rw [heq]
    exact highFold_subset_dilate_of_subset A Q hAQ h
  have hden : ∀ X ∈ Xs, P.boxCard ≤ D * X.card := by
    intro X hX
    have heq : X = h • A := (List.mem_replicate.mp hX).2
    rw [heq]
    exact hdense
  obtain ⟨R, hrank, hrproper, hrstep, hrexc, hrside, hrsub, hrcard⟩ :=
    P.exists_large_proper_GAP_of_dense_different_summands_proper
      D hD hproper Xs hlen hsub hden
  have hout : GeneralizedAP.DenseProperOutput P D Xs R :=
    ⟨hrank, hrproper, hrstep, hrexc, hrside, hrsub, hrcard⟩
  obtain ⟨S, hstandard, huniform⟩ := hout.exists_uniformStandard hD
  obtain ⟨hSrank, hSproper, _hSstep, hSsides, hSsub, _hScard⟩ := hstandard
  refine ⟨S, hSrank, hSproper, ?_, ?_, ?_⟩
  · simpa only [Xs, nvFinsetListSum_replicate, ← mul_nsmul, Nat.mul_comm] using hSsub
  · intro i j hij
    simpa only [Xs, List.length_replicate, P, GeneralizedAP.dilate] using huniform i j hij
  · intro i j hij
    simpa only [Xs, List.length_replicate, P, GeneralizedAP.dilate] using hSsides i j hij

theorem standardized_side_pos {L F h : ℕ} (hL : 0 < L) (hF : 0 < F) (hscale : F ≤ h) :
    0 < h * L / F := by
  apply Nat.div_pos
  · have hmul : h ≤ h * L := by
      calc
        h = h * 1 := by simp
        _ ≤ h * L := Nat.mul_le_mul_left h (by omega)
    exact hscale.trans hmul
  · exact hF

theorem standardized_side_lower {L F h : ℕ} (hL : 0 < L) (hF : 0 < F)
    (hscale : F ≤ h) : h * L ≤ 2 * F * (h * L / F) := by
  have hp := standardized_side_pos hL hF hscale
  have hu := Nat.lt_mul_div_succ (h * L) hF
  nlinarith

/-- A noncollapsed proper standardized output has nonzero multipliers on
every coordinate, in addition to the uniform upper bound. -/
theorem standardized_step_multiplier_nonzero
    (Q S : GeneralizedAP) (hS : S.Proper) (hpos : ∀ i, 0 < S.length i)
    (B : ℕ) (hstep : S.StepMultipliersBoundedByConstant Q B)
    (i : Fin S.rank) (j : Fin Q.rank) (hij : i.val = j.val) :
    ∃ a : ℤ, a ≠ 0 ∧ |a| ≤ (B : ℤ) ∧ S.step i = a * Q.step j := by
  obtain ⟨a, ha, habs⟩ := hstep i j hij
  refine ⟨a, ?_, habs, ha⟩
  intro haz
  have hs := S.step_ne_zero_of_proper_length_pos hS (hpos i)
  apply hs
  rw [ha, haz, zero_mul]

end Erdos587.CFP
