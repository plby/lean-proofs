/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos622.ShiftedWindowCount
import ErdosProblems.Erdos622.CompactBoundedForest

/-!
# The small-transfer finish for the forward compact orientation

This module isolates the finite union bound used when the number of vertices
transferred from the original left part is at most one sixty-fourth of the
normalized left-cover size.  In this range the balanced-side matching and the
opposite bounded-internal forest suffice; the original-side forest can be the
empty forest.
-/

namespace Erdos622
namespace ForwardSmallFinish

open Filter Finset Real Set

attribute [local instance] Classical.propDecidable

noncomputable section

private lemma matching_floor_induce_internalGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {A S : Finset V} {u : ℝ}
    (hu : 0 ≤ u)
    (h : RandomCover.HasMatchingAtLeast (internalGraph G A) S u) :
    ContainsLinearForestWith (G.induce (S : Set V))
      (restrictedPart S A) ⌊u⌋₊ := by
  apply RandomCover.HasMatchingAtLeast.induce_internalGraph
  obtain ⟨N, hNmatching, hNS, hNcard⟩ := h
  exact ⟨N, hNmatching, hNS, (Nat.floor_le hu).trans hNcard⟩

/-- In the small-transfer arm, three exceptional events suffice: failure of
the balanced-side matching, failure of the opposite bounded-internal forest,
and failure of the transfer set to be balanced. -/
theorem small_transfer_goodSample_count
    {n : ℕ} {delta margin sigma rho alpha kappa eps : ℝ}
    (G : SimpleGraph (Fin (2 * n)))
    {A B T A₀ B₀ C : Finset (Fin (2 * n))} {right : ℕ}
    (hn : 0 < n) (hsigma : 0 < sigma)
    (htwoSigma : 2 * sigma ≤ rho)
    (hcut : IsCut A B) (hTA : T ⊆ A)
    (hA₀ : A₀ = A \ T) (hB₀ : B₀ = B ∪ T)
    (hA₀card : A₀.card = n) (hTcard : T.card = A.card - n)
    (hkappa : kappa = ((A.card - n : ℕ) : ℝ) / Real.sqrt n)
    (halpha : 0 < alpha) (hkappaAlpha : kappa ≤ alpha / 64)
    (hleftCap : (alpha / 4 - sigma) * Real.sqrt n ≤
      (Nat.floor ((1 / 4 - eps) * (C.card : ℝ)) : ℝ))
    (hrightCap : (1 / alpha - sigma) * Real.sqrt n ≤ right)
    (hthresholdNonneg : 0 ≤ (1 / 4 - eps) * (C.card : ℝ))
    (hwindowRaw :
      ((1 / 2 : ℝ) + margin / 2) * (2 : ℝ) ^ (2 * n) ≤
        (almostBipartiteCount (Finset.univ : Finset (Fin (2 * n)))
          (fun S ↦ BinomialCLT.standardizedBinomialPoint (2 * n)
            ((S ∩ B₀).card + (n - (S ∩ A₀).card)) ∈
              Set.Icc
                (-((max (alpha / 4 - kappa) (15 * kappa) - rho) *
                  Real.sqrt 2))
                ((max (1 / alpha) kappa - rho) * Real.sqrt 2)) : ℝ))
    (hmatchingBad :
      ((((Finset.univ : Finset (Fin (2 * n))).powerset.filter fun S ↦
        ¬ RandomCover.HasMatchingAtLeast (internalGraph G A₀) S
          ((1 / 4 - eps) * C.card)).card : ℝ)) ≤
        delta * (2 : ℝ) ^ (2 * n))
    {JB : SimpleGraph (Fin (2 * n))}
    (hJBG : JB ≤ G) (hJBsupp : JB.support ⊆ (B₀ : Set (Fin (2 * n))))
    (hrightBad :
      ((((Finset.univ : Finset (Fin (2 * n))).powerset.filter
        fun S : Finset (Fin (2 * n)) ↦
        ¬ ContainsLinearForestWith (JB.induce (S : Set (Fin (2 * n))))
          Finset.univ right).card : ℝ)) ≤
        delta * (2 : ℝ) ^ (2 * n))
    (htransferBad :
      ((((Finset.univ : Finset (Fin (2 * n))).powerset.filter fun S ↦
        sigma / 2 * (Nat.sqrt n : ℝ) ≤
          |SamplingSuitable.intersectionCount T S - (T.card : ℝ) / 2|).card : ℝ)) ≤
        delta * (2 : ℝ) ^ (2 * n)) :
    ((1 / 2 : ℝ) + margin / 2) * (2 : ℝ) ^ (2 * n) -
        3 * delta * (2 : ℝ) ^ (2 * n) ≤
      (almostBipartiteCount (Finset.univ : Finset (Fin (2 * n)))
        (fun S ↦ IsKGoodSample G A B S 0) : ℝ) := by
  let left : ℕ := Nat.floor ((1 / 4 - eps) * (C.card : ℝ))
  let P : Finset (Fin (2 * n)) → Prop := fun S ↦
    BinomialCLT.standardizedBinomialPoint (2 * n)
      ((S ∩ B₀).card + (n - (S ∩ A₀).card)) ∈
        Set.Icc
          (-((max (alpha / 4 - kappa) (15 * kappa) - rho) * Real.sqrt 2))
          ((max (1 / alpha) kappa - rho) * Real.sqrt 2)
  let F₁ : Finset (Fin (2 * n)) → Prop := fun S ↦
    ¬ RandomCover.HasMatchingAtLeast (internalGraph G A₀) S
      ((1 / 4 - eps) * C.card)
  let F₃ : Finset (Fin (2 * n)) → Prop := fun S ↦
    ¬ ContainsLinearForestWith (JB.induce (S : Set (Fin (2 * n))))
      Finset.univ right
  let F₄ : Finset (Fin (2 * n)) → Prop := fun S ↦
    sigma / 2 * (Nat.sqrt n : ℝ) ≤
      |SamplingSuitable.intersectionCount T S - (T.card : ℝ) / 2|
  let Failure : Finset (Fin (2 * n)) → Prop := fun S ↦ F₁ S ∨ F₃ S ∨ F₄ S
  have h13 := almostBipartiteCount_or_le
    (Finset.univ : Finset (Fin (2 * n))) F₁ F₃
  have h134 := almostBipartiteCount_or_le
    (Finset.univ : Finset (Fin (2 * n))) (fun S ↦ F₁ S ∨ F₃ S) F₄
  have hfailure :
      (almostBipartiteCount (Finset.univ : Finset (Fin (2 * n))) Failure : ℝ) ≤
        3 * delta * (2 : ℝ) ^ (2 * n) := by
    have h13R :
        (almostBipartiteCount (Finset.univ : Finset (Fin (2 * n)))
          (fun S ↦ F₁ S ∨ F₃ S) : ℝ) ≤
        (almostBipartiteCount (Finset.univ : Finset (Fin (2 * n))) F₁ : ℝ) +
          almostBipartiteCount (Finset.univ : Finset (Fin (2 * n))) F₃ := by
      exact_mod_cast h13
    have h134R :
        (almostBipartiteCount (Finset.univ : Finset (Fin (2 * n))) Failure : ℝ) ≤
        (almostBipartiteCount (Finset.univ : Finset (Fin (2 * n)))
          (fun S ↦ F₁ S ∨ F₃ S) : ℝ) +
          almostBipartiteCount (Finset.univ : Finset (Fin (2 * n))) F₄ := by
      have h134R' :
          (almostBipartiteCount (Finset.univ : Finset (Fin (2 * n)))
            (fun S ↦ (F₁ S ∨ F₃ S) ∨ F₄ S) : ℝ) ≤
          (almostBipartiteCount (Finset.univ : Finset (Fin (2 * n)))
            (fun S ↦ F₁ S ∨ F₃ S) : ℝ) +
          almostBipartiteCount (Finset.univ : Finset (Fin (2 * n))) F₄ := by
        exact_mod_cast h134
      simpa only [Failure, or_assoc] using h134R'
    calc
      _ ≤ (almostBipartiteCount (Finset.univ : Finset (Fin (2 * n)))
            (fun S ↦ F₁ S ∨ F₃ S) : ℝ) +
          almostBipartiteCount (Finset.univ : Finset (Fin (2 * n))) F₄ := h134R
      _ ≤ ((almostBipartiteCount (Finset.univ : Finset (Fin (2 * n))) F₁ : ℝ) +
          almostBipartiteCount (Finset.univ : Finset (Fin (2 * n))) F₃) +
          almostBipartiteCount (Finset.univ : Finset (Fin (2 * n))) F₄ :=
        by simpa only [add_comm] using (add_le_add_right h13R
          (almostBipartiteCount (Finset.univ : Finset (Fin (2 * n))) F₄ : ℝ))
      _ ≤ (delta * (2 : ℝ) ^ (2 * n) + delta * (2 : ℝ) ^ (2 * n)) +
          delta * (2 : ℝ) ^ (2 * n) := by
        gcongr
        · simpa only [F₁, almostBipartiteCount, almostBipartiteEvent] using hmatchingBad
        · simpa only [F₃, almostBipartiteCount, almostBipartiteEvent] using hrightBad
        · simpa only [F₄, almostBipartiteCount, almostBipartiteEvent] using htransferBad
      _ = _ := by ring
  suffices hres :
      ((1 / 2 : ℝ) + margin / 2) * (2 : ℝ) ^ (2 * n) -
          3 * delta * (2 : ℝ) ^ Fintype.card (Fin (2 * n)) ≤
        (almostBipartiteCount (Finset.univ : Finset (Fin (2 * n)))
          (fun S ↦ IsKGoodSample G A B S 0) : ℝ) by
    simpa only [Fintype.card_fin] using hres
  apply AlmostBipartiteRegimeCounts.goodSample_count_of_window_failure
    (A := A) (B := B) G P Failure
      (((1 / 2 : ℝ) + margin / 2) * (2 : ℝ) ^ (2 * n))
      (3 * delta) _ (by simpa [P] using hwindowRaw)
      (by simpa only [Fintype.card_fin] using hfailure)
  intro S _hS hPS hnot
  have hn₁ : ¬ F₁ S := by intro h; exact hnot (Or.inl h)
  have hn₃ : ¬ F₃ S := by intro h; exact hnot (Or.inr (Or.inl h))
  have hn₄ : ¬ F₄ S := by intro h; exact hnot (Or.inr (Or.inr h))
  have hleft : ContainsLinearForestWith (G.induce (S : Set (Fin (2 * n))))
      (restrictedPart S A₀) left := by
    exact matching_floor_induce_internalGraph hthresholdNonneg
      (by simpa only [F₁, not_not, left] using hn₁)
  have hright : ContainsLinearForestWith (G.induce (S : Set (Fin (2 * n))))
      (restrictedPart S B₀) right :=
    ContainsLinearForestWith.mono_induce_of_support hJBG hJBsupp
      (by simpa [F₃] using hn₃)
  have hxA : (S ∩ A₀).card ≤ A₀.card :=
    Finset.card_le_card Finset.inter_subset_right
  have hx : (S ∩ A₀).card ≤ n := by omega
  have htransfer := CompactBoundedForest.balancing_transfer_deviation
    hsigma.le hTcard (by simpa [F₄] using hn₄)
  have hwindows :=
    AlmostBipartiteRegimeCounts.shrunken_capacity_window_small_transfer_nat_bounds
      hn hx halpha hkappa hkappaAlpha hsigma.le
      htwoSigma htransfer (by simpa [P] using hPS)
      (by simpa [left] using hleftCap) hrightCap
  apply TwoLargeForest.IsKGoodSample.of_balanced_transfer_three_forests
    hcut hTA hA₀ hB₀ hleft
      (ContainsLinearForestWith.zero _ _) hright
  · simpa [left] using hwindows.1
  · exact hwindows.2

end
end ForwardSmallFinish
end Erdos622
