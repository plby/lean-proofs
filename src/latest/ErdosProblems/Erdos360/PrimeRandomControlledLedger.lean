/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos360.PrimeRandomAssembly

/-!
# A controlled-cardinality prime/random ledger for Erdos 360

The random assembly must not use a fixed fraction of an arbitrarily large
colour class: in a very unbalanced colouring the sum of those selected
elements can exceed the target.  This file records the source-faithful
repair.  Before divisor extraction, choose exactly `M` elements of the large
colour class.  Extraction is then applied to that set.  Its output has the
upper bound `M`, while the extraction-loss estimate gives the lower bound
`Q`.  These two bounds respectively pay for the upper-sum and unused-mass
ends of the argument.

The first part is independent of every asymptotic choice.  The second part
is the general controlled constructor, parameterized by the number `ell` of
random pools and by the exact-multiple modulus `h`.  Eventual numerical
specializations belong in the downstream parameter-ledger module.
-/

namespace Erdos360

open Filter
open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-! ## Controlled pigeonhole and extraction -/

/-- A pigeonhole class contains any prescribed number `M` of elements as
soon as `colors * M <= |Y|`. -/
lemma exists_controlled_integerColorClass
    {n colors M : ℕ} (hcolors : 0 < colors)
    (Y : Finset (BelowTarget n)) (c : BelowTarget n → Fin colors)
    (hM : colors * M ≤ Y.card) :
    ∃ i : Fin colors, ∃ W : Finset ℕ,
      W ⊆ integerColorClass Y c i ∧ W.card = M := by
  obtain ⟨i, hi⟩ := exists_large_integerColorClass hcolors Y c
  have hMclass : M ≤ (integerColorClass Y c i).card := by
    have hmul : colors * M ≤
        colors * (integerColorClass Y c i).card := hM.trans hi
    exact Nat.le_of_mul_le_mul_left hmul hcolors
  obtain ⟨W, hW, hWcard⟩ := Finset.exists_subset_card_eq hMclass
  exact ⟨i, W, hW, hWcard⟩

/-- Finite reduction with a controlled-cardinality class selected before
divisor extraction.  This is the exact replacement for applying extraction
to the entire, possibly oversized, pigeonhole class. -/
theorem forcesTarget_of_controlled_extracted_colorClass_completion
    {n colors M B L K : ℕ}
    (hcolors : 0 < colors) (hB : 0 < B)
    (Y : Finset (BelowTarget n)) (hM : colors * M ≤ Y.card)
    (hcomplete : ∀ (c : BelowTarget n → Fin colors) (i : Fin colors)
        (W : Finset ℕ) (d : ℕ) (Z : Finset ℕ),
      W ⊆ integerColorClass Y c i → W.card = M →
      0 < d → d ≤ B →
      (∀ z ∈ Z, d * z ∈ W) →
      W.card - Z.card ≤ L * Nat.log 2 B + K * B →
      (∀ e : ℕ, 1 < e → d * e ≤ B →
        L + K * e ≤ (Z.filter fun z ↦ ¬e ∣ z).card) →
      d ∣ n ∧ n / d ∈ Z.subsetSum) :
    ForcesTarget n colors := by
  apply forcesTarget_of_scaled_colorClass_completion Y
  intro c
  obtain ⟨i, W, hW, hWcard⟩ :=
    exists_controlled_integerColorClass hcolors Y c hM
  obtain ⟨d, Z, hd, hdB, hscale, hloss, hdiverse⟩ :=
    exists_divisorExtraction B L K hB W
  obtain ⟨hdn, hquot⟩ :=
    hcomplete c i W d Z hW hWcard hd hdB hscale hloss hdiverse
  exact ⟨i, d, Z, hd, hdn, fun z hz ↦ hW (hscale z hz), hquot⟩

/-! ## Deterministic cardinal and endpoint estimates -/

lemma card_le_of_positive_scale_subset
    {d : ℕ} {Z W : Finset ℕ} (hd : 0 < d)
    (hscale : ∀ z ∈ Z, d * z ∈ W) : Z.card ≤ W.card := by
  apply Finset.card_le_card_of_injOn (fun z ↦ d * z)
  · exact hscale
  · intro a ha b hb hab
    exact Nat.eq_of_mul_eq_mul_left hd hab

lemma extracted_card_lower_of_controlled_loss
    {M Q loss d : ℕ} {Z W : Finset ℕ}
    (hd : 0 < d) (hWcard : W.card = M)
    (hscale : ∀ z ∈ Z, d * z ∈ W)
    (hloss : W.card - Z.card ≤ loss)
    (hroom : Q + loss ≤ M) : Q ≤ Z.card := by
  have hZW : Z.card ≤ W.card :=
    card_le_of_positive_scale_subset hd hscale
  rw [hWcard] at hZW hloss
  omega

/-! ## General controlled-cardinality random constructor -/

/-- Monotonicity estimate needed for the unused part of a controlled class.
The selected pools are bounded using the pre-extraction cap `M`, while all
of the post-extraction set `Z` remains available at the terminal step. -/
lemma controlled_remaining_card_lower
    {ell h M Q z : ℕ} (hQz : Q ≤ z) (hzM : z ≤ M) :
    Q - ell * (M / h) ≤ z - ell * (z / h) := by
  have hdiv : z / h ≤ M / h := Nat.div_le_div_right hzM
  exact (Nat.sub_le_sub_right hQz (ell * (M / h))).trans
    (Nat.sub_le_sub_left (Nat.mul_le_mul_left ell hdiv) z)

/-- General controlled-cardinality wrapper around the checked iterated
random theorem.  It is parameterized by the source's eventual fixed `ell`
and `h` (normally `h = 8*ell`) and makes no claim about the eventual choice
of those constants.  In particular it remains valid when the ordinary
growth target is weakened by the exact constant loss supplied by the local
inverse theorem. -/
noncomputable def controlledRandomPreLevInput
    {n colors y B L K M Q : ℕ} {Y : Finset (BelowTarget n)}
    {c : BelowTarget n → Fin colors} {i : Fin colors}
    {W Z : Finset ℕ} {d h ell k diversity nzero diameter : ℕ}
    (hY : ∀ x ∈ Y, y < x.1 ∧ x.1 ≤ 2 * y)
    (hW : W ⊆ integerColorClass Y c i) (hWcard : W.card = M)
    (hd : 0 < d) (hdB : d ≤ B) (hh : 0 < h)
    (hscale : ∀ z ∈ Z, d * z ∈ W)
    (hloss : W.card - Z.card ≤ L * Nat.log 2 B + K * B)
    (hdiverse : ∀ e : ℕ, 1 < e → d * e ≤ B →
      L + K * e ≤ (Z.filter fun z ↦ ¬e ∣ z).card)
    (hlossRoom : Q + (L * Nat.log 2 B + K * B) ≤ M)
    (hkL : k + (h - 1) ≤ L)
    (hlarge : k + (2 * y / d) / (B / d + 1) + (h - 1) ≤ Q)
    (hcount : ell + 2 ≤ h)
    (hprobability : ∀ j < ell,
      RandomDiversity.exactSplitFailureMass (2 * y / d)
        (M / h) (h - j) (RandomDiversity.residualDiversity k h j) < 1)
    (hdiversity : ∀ j < ell,
      diversity ≤ RandomDiversity.residualDiversity k h j /
        (2 * (h - j)))
    (hordinary : ∀ P : Finset ℕ,
      P ⊆ lowerPart Z (Z.card % h) → P.card = Z.card / h →
      DiverseSampling.DiverseNat P diversity →
      Nonempty (CFPOrdinaryGrowthCertificate P nzero diameter))
    (hnzero : 3 ≤ nzero)
    (hlev : 2 * ((diameter - 1) ⌈/⌉ (nzero - 2)) ≤ ell)
    (hwidth : 2 * y ≤ ell * (nzero - 1) + 1)
    (hsum : ell * (M / h) * (2 * y / d) < n / d)
    (hunused : n / d ≤
      (y / d + 1) * (Q - ell * (M / h))) :
    CFPRandomPreLevInput n d y Z := by
  have hscaleClass : ∀ z ∈ Z,
      d * z ∈ integerColorClass Y c i := fun z hz ↦ hW (hscale z hz)
  have hZrange : Z ⊆ Finset.Icc 1 (2 * y / d) :=
    extracted_dyadic_quotient_Icc hY hd hscaleClass
  have hZupper : Z.card ≤ M := by
    simpa [hWcard] using card_le_of_positive_scale_subset hd hscale
  have hZlower : Q ≤ Z.card :=
    extracted_card_lower_of_controlled_loss hd hWcard hscale hloss
      hlossRoom
  have hs : Z.card / h ≤ M / h := Nat.div_le_div_right hZupper
  apply randomPreLevInput_of_trimmed_extraction_general
    (h := h) (ell := ell) (k := k) (diversity := diversity)
    (nzero := nzero) (diameter := diameter) hh hZrange hdiverse hkL
  · apply (show k + (2 * y / d) / (B / d + 1) ≤ Q - (h - 1) by
      omega).trans
    have hmod := Nat.mod_lt Z.card hh
    have hdecomp := Nat.mod_add_div Z.card h
    omega
  · exact hcount
  · intro j hj
    apply (show RandomDiversity.exactSplitFailureMass (2 * y / d)
        (Z.card / h) (h - j)
        (RandomDiversity.residualDiversity k h j) ≤
      RandomDiversity.exactSplitFailureMass (2 * y / d)
        (M / h) (h - j)
        (RandomDiversity.residualDiversity k h j) by
      unfold RandomDiversity.exactSplitFailureMass
      have hfac : (h - j) * (Z.card / h) + 1 ≤
          (h - j) * (M / h) + 1 :=
        Nat.add_le_add_right (Nat.mul_le_mul_left (h - j) hs) 1
      gcongr
      unfold RandomDiversity.complementDiversityTailBound
      positivity).trans_lt (hprobability j hj)
  · exact hdiversity
  · exact hordinary
  · exact hnzero
  · exact hlev
  · exact hwidth
  · exact (Nat.mul_le_mul_right (2 * y / d)
      (Nat.mul_le_mul_left ell hs)).trans_lt hsum
  · exact hunused.trans <| Nat.mul_le_mul_left (y / d + 1)
      (controlled_remaining_card_lower hZlower hZupper)
  · have hnDivPos : 0 < n / d :=
      (Nat.zero_le (ell * (M / h) * (2 * y / d))).trans_lt hsum
    have hprodPos : 0 < (y / d + 1) * (Q - ell * (M / h)) :=
      hnDivPos.trans_le hunused
    have hremPos : 0 < Q - ell * (M / h) :=
      Nat.pos_of_mul_pos_left hprodPos
    have hQpos : 0 < Q := hremPos.trans_le (Nat.sub_le Q _)
    exact Finset.card_pos.mp (hQpos.trans_le hZlower)

end Erdos360

#print axioms Erdos360.forcesTarget_of_controlled_extracted_colorClass_completion
#print axioms Erdos360.controlledRandomPreLevInput
