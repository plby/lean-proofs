import ErdosProblems.Erdos796.StructuralReductionBridge
import ErdosProblems.Erdos796.BoxPruningError
import ErdosProblems.Erdos796.OverlapPruningError
import ErdosProblems.Erdos796.NormalFormCounting
import ErdosProblems.Erdos796.TailBudgetBound
import ErdosProblems.Erdos796.SmallPrimeBudget
import ErdosProblems.Erdos796.SmallPrimeError

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Assembly of the finite structural upper bound

This file combines the finite pruning estimates.  No limiting argument is
used here: every loss is recorded in the natural-valued function
`structuralError`.
-/

namespace Erdos796

open scoped BigOperators
open Filter

namespace StructuralFiniteBound

open PruningScales PruningArithmetic PruningPartition
  SplitNormalCounting LargeMultiplierPruning NormalFormCounting
  SmoothAugmentation TriplePruning SmallPrimeBudget

/-! ## Elementary subset and survivor lemmas -/

/-- Admissibility is inherited by finite subsets. -/
theorem admissible_of_subset
    {n : ℕ} {A B : Finset ℕ} (hBA : B ⊆ A)
    (hA : Admissible n A) : Admissible n B := by
  constructor
  · exact hBA.trans hA.1
  · intro m
    exact (Finset.card_le_card (by
      intro ab hab
      have hab' := Finset.mem_filter.mp hab
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_product.mpr
          ⟨hBA (Finset.mem_product.mp hab'.1).1,
            hBA (Finset.mem_product.mp hab'.1).2⟩,
        hab'.2⟩)).trans (hA.2 m)

/-- The set left after removing all elements with three factors above `Y`. -/
noncomputable def survivors (Y : ℕ) (A : Finset ℕ) : Finset ℕ :=
  A \ badElements Y A

@[simp] theorem mem_survivors {Y a : ℕ} {A : Finset ℕ} :
    a ∈ survivors Y A ↔ a ∈ A ∧ ¬HasThreeLargeFactors Y a := by
  classical
  constructor
  · intro ha
    have ha' := Finset.mem_sdiff.mp ha
    refine ⟨ha'.1, ?_⟩
    intro hbad
    exact ha'.2 (mem_badElements.mpr ⟨ha'.1, hbad⟩)
  · rintro ⟨ha, hno⟩
    exact Finset.mem_sdiff.mpr ⟨ha, by
      intro hbad
      exact hno (mem_badElements.mp hbad).2⟩

theorem survivors_subset (Y : ℕ) (A : Finset ℕ) :
    survivors Y A ⊆ A := by
  intro a ha
  exact (mem_survivors.mp ha).1

theorem survivors_admissible
    {n Y : ℕ} {A : Finset ℕ} (hA : Admissible n A) :
    Admissible n (survivors Y A) :=
  admissible_of_subset (survivors_subset Y A) hA

theorem card_eq_bad_add_survivors (Y : ℕ) (A : Finset ℕ) :
    A.card = (badElements Y A).card + (survivors Y A).card := by
  have h := Finset.card_sdiff_add_card_eq_card (badElements_subset Y A)
  simpa [survivors, Nat.add_comm] using! h.symm

/-! ## Four-way cover of the split normal form -/

/-- The split form is covered by the repeated-prime piece, the low-multiplier
small-prime piece, the unrestricted large-multiplier piece, and the
large-first-prime tail piece. -/
theorem splitNormalPiece_subset_budgetPieces
    (n Y Z W : ℕ) (A : Finset ℕ) :
    splitNormalPiece Y Z A ⊆
      splitRepeatedPrimePiece Y Z A ∪
        lowMultiplierSmallPrimePiece n Y Z W A ∪
          splitAnyLargeMultiplierPiece n Y Z W A ∪
            splitTailPiece n Y Z W A := by
  intro a ha
  have ha' := mem_splitNormalPiece.mp ha
  simp only [Finset.mem_union]
  by_cases hqr : splitQ a = splitR a
  · exact Or.inl <| Or.inl <| Or.inl <|
      mem_splitRepeatedPrimePiece.mpr ⟨ha'.1, ha'.2, hqr⟩
  · by_cases hs : splitS a < W
    · by_cases hq : splitQ a ≤ n.sqrt
      · exact Or.inl <| Or.inl <| Or.inr <|
          mem_lowMultiplierSmallPrimePiece.mpr
            ⟨ha'.1, ha'.2, hqr, hq, hs⟩
      · exact Or.inr <|
          mem_splitTailPiece.mpr
            ⟨ha'.1, ha'.2, Nat.lt_of_not_ge hq, hqr, hs⟩
    · exact Or.inl <| Or.inr <|
        mem_splitAnyLargeMultiplierPiece.mpr
          ⟨ha'.1, ha'.2, hqr, Nat.le_of_not_gt hs⟩

/-- Cardinal form of the four-way split cover. -/
theorem card_splitNormalPiece_le_budgetPieces
    (n Y Z W : ℕ) (A : Finset ℕ) :
    (splitNormalPiece Y Z A).card ≤
      (splitRepeatedPrimePiece Y Z A).card +
        (lowMultiplierSmallPrimePiece n Y Z W A).card +
          (splitAnyLargeMultiplierPiece n Y Z W A).card +
            (splitTailPiece n Y Z W A).card := by
  let P₁ := splitRepeatedPrimePiece Y Z A
  let P₂ := lowMultiplierSmallPrimePiece n Y Z W A
  let P₃ := splitAnyLargeMultiplierPiece n Y Z W A
  let P₄ := splitTailPiece n Y Z W A
  have hsub : splitNormalPiece Y Z A ⊆ P₁ ∪ P₂ ∪ P₃ ∪ P₄ := by
    simpa [P₁, P₂, P₃, P₄] using!
      splitNormalPiece_subset_budgetPieces n Y Z W A
  calc
    (splitNormalPiece Y Z A).card ≤ (P₁ ∪ P₂ ∪ P₃ ∪ P₄).card :=
      Finset.card_le_card hsub
    _ ≤ (P₁ ∪ P₂ ∪ P₃).card + P₄.card :=
      Finset.card_union_le _ _
    _ ≤ ((P₁ ∪ P₂).card + P₃.card) + P₄.card :=
      Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ ((P₁.card + P₂.card) + P₃.card) + P₄.card :=
      Nat.add_le_add_right
        (Nat.add_le_add_right (Finset.card_union_le _ _) _) _
    _ = (splitRepeatedPrimePiece Y Z A).card +
        (lowMultiplierSmallPrimePiece n Y Z W A).card +
          (splitAnyLargeMultiplierPiece n Y Z W A).card +
            (splitTailPiece n Y Z W A).card := rfl

/-! ## Natural forms of the two real complete-box estimates -/

theorem card_badElements_le_badPruningError
    {n : ℕ} {A : Finset ℕ} (hA : Admissible n A)
    (hY : 2 ≤ Y n) :
    (badElements (Y n) A).card ≤
      BoxPruningError.badPruningError n := by
  have hreal := card_badElements_le_dyadicPruning hA hY
  have hmajor : ((badElements (Y n) A).card : ℝ) ≤
      BoxPruningError.badPruningMajorant n := by
    change ((badElements (Y n) A).card : ℝ) ≤
      (((Nat.log 2 n + 1) ^ 3 : ℕ) : ℝ) *
        ((4 * (n : ℝ)) /
          Tripartite.realFourthRoot ((Y n : ℝ) / 2))
    exact hreal
  have hceil : BoxPruningError.badPruningMajorant n ≤
      (BoxPruningError.badPruningError n : ℝ) := by
    unfold BoxPruningError.badPruningError
    exact Nat.le_ceil (BoxPruningError.badPruningMajorant n)
  exact_mod_cast hmajor.trans hceil

theorem card_splitAnyLargeMultiplierPiece_le_largeMultiplierError
    {n : ℕ} {A : Finset ℕ} (hA : Admissible n A)
    (hW : 2 ≤ W n) (hWZ : W n ≤ Z n) (hZY : Z n ≤ Y n) :
    (splitAnyLargeMultiplierPiece n (Y n) (Z n) (W n) A).card ≤
      BoxPruningError.largeMultiplierError n := by
  have hreal := card_splitAnyLargeMultiplierPiece_le_dyadicPruning
    hA hW hWZ hZY
  have hmajor :
      ((splitAnyLargeMultiplierPiece n (Y n) (Z n) (W n) A).card : ℝ) ≤
        BoxPruningError.largeMultiplierMajorant n := by
    change
      ((splitAnyLargeMultiplierPiece n (Y n) (Z n) (W n) A).card : ℝ) ≤
        (((Nat.log 2 n + 1) ^ 3 : ℕ) : ℝ) *
          ((4 * (n : ℝ)) /
            Tripartite.realFourthRoot ((W n : ℝ) / 2))
    exact hreal
  have hceil : BoxPruningError.largeMultiplierMajorant n ≤
      (BoxPruningError.largeMultiplierError n : ℝ) := by
    unfold BoxPruningError.largeMultiplierError
    exact Nat.le_ceil (BoxPruningError.largeMultiplierMajorant n)
  exact_mod_cast hmajor.trans hceil

/-! ## The assembled error and pointwise finite theorem -/

/-- Every term not absorbed into the compatible cofactor model. -/
noncomputable def structuralError (n : ℕ) : ℕ :=
  BoxPruningError.badPruningError n +
    Y n ^ 6 +
    2 * (Nat.primeCounting n.sqrt * Y n ^ 4) +
    Nat.primeCounting n.sqrt ^ 2 +
    W n ^ 2 * Nat.ceil (KsmallReal n) +
    BoxPruningError.largeMultiplierError n +
    R n ^ 4 +
    OverlapPruningError.overlapError n

/-- Finite structural estimate at any `n` for which the chosen scales have
the displayed order and the largest cofactor range lies below `sqrt n`. -/
theorem admissible_card_le_G_add_structuralError
    {n : ℕ} {A : Finset ℕ} (hA : Admissible n A)
    (hZ : 2 ≤ Z n) (hZY : Z n ≤ Y n)
    (hW : 2 ≤ W n) (hWZ : W n ≤ Z n)
    (hRY : R n = Y n ^ 4) (hRsqrt : R n ≤ n.sqrt) :
    A.card ≤ G n + structuralError n := by
  let S := survivors (Y n) A
  have hS : Admissible n S := by
    simpa [S] using! (survivors_admissible (Y := Y n) hA)
  have hno : ∀ a ∈ S, ¬HasThreeLargeFactors (Y n) a := by
    intro a ha
    exact (mem_survivors.mp (by simpa [S] using! ha)).2
  have hY : 2 ≤ Y n := hZ.trans hZY
  have hdecomp :
      A.card = (badElements (Y n) A).card + S.card := by
    simpa [S] using! card_eq_bad_add_survivors (Y n) A
  have hpart :
      S.card = (ySmoothPiece (Y n) S).card +
        (smoothNormalPiece (Y n) (Z n) S).card +
          (splitNormalPiece (Y n) (Z n) S).card :=
    card_eq_sum_three_pieces_of_subset_positiveIcc
      hS.1 hZ hZY hno
  have hbad : (badElements (Y n) A).card ≤
      BoxPruningError.badPruningError n :=
    card_badElements_le_badPruningError hA hY
  have hySmooth : (ySmoothPiece (Y n) S).card ≤ Y n ^ 6 := by
    have hsub := ySmoothPiece_subset_powSix hY
      (fun a ha => (mem_positiveIcc.mp (hS.1 ha)).1) hno
    have hcard := Finset.card_le_card hsub
    simpa [positiveIcc] using! hcard
  have hsmooth :
      (smoothNormalPiece (Y n) (Z n) S).card ≤
        Nat.primeCounting n.sqrt * Y n ^ 4 +
          ∑ q ∈ largePrimes n,
            (smoothCofactorFiber S (Y n ^ 4) (Z n) q).card :=
    card_smoothNormalPiece_le hS
  have hsplit :
      (splitNormalPiece (Y n) (Z n) S).card ≤
        (splitRepeatedPrimePiece (Y n) (Z n) S).card +
          (lowMultiplierSmallPrimePiece n (Y n) (Z n) (W n) S).card +
            (splitAnyLargeMultiplierPiece n (Y n) (Z n) (W n) S).card +
              (splitTailPiece n (Y n) (Z n) (W n) S).card :=
    card_splitNormalPiece_le_budgetPieces n (Y n) (Z n) (W n) S
  have hrepeated :
      (splitRepeatedPrimePiece (Y n) (Z n) S).card ≤
        Nat.primeCounting n.sqrt * Y n ^ 4 :=
    card_splitRepeatedPrimePiece_le hS
  have hsmall :
      (lowMultiplierSmallPrimePiece n (Y n) (Z n) (W n) S).card ≤
        Nat.primeCounting n.sqrt ^ 2 +
          W n ^ 2 * Nat.ceil (KsmallReal n) :=
    card_lowMultiplierSmallPrimePiece_le hS hWZ hZY
  have hlarge :
      (splitAnyLargeMultiplierPiece n (Y n) (Z n) (W n) S).card ≤
        BoxPruningError.largeMultiplierError n :=
    card_splitAnyLargeMultiplierPiece_le_largeMultiplierError
      hS hW hWZ hZY
  have htail :
      (splitTailPiece n (Y n) (Z n) (W n) S).card ≤
        primeTailScore n (Z n) +
          OverlapPruningError.overlapError n := by
    simpa [OverlapPruningError.overlapError] using!
      (TailBudgetBound.card_splitTailPiece_le_primeTailScore_add_overlap
        (n := n) (Y := Y n) (Z := Z n) (W := W n) hS hWZ)
  have hYfour : Y n ^ 4 ≤ n.sqrt := by
    rw [← hRY]
    exact hRsqrt
  have hjoint :
      (∑ q ∈ largePrimes n,
          (smoothCofactorFiber S (Y n ^ 4) (Z n) q).card) +
        primeTailScore n (Z n) ≤ G n + R n ^ 4 := by
    simpa [hRY] using!
      (smooth_plus_primeTail_le_G_add_cleaning
        (R := Y n ^ 4) (Z := Z n) hS hYfour)
  dsimp [structuralError]
  omega

/-- The scale choices satisfy the finite bound uniformly for all sufficiently
large `n`.  This is the exact `UniformStructuralUpperBound` needed by the
generic structural-reduction bridge. -/
theorem uniformStructuralUpperBound :
    UniformStructuralUpperBound structuralError := by
  filter_upwards [eventually_scale_order,
      eventually_pruning_scale_hypotheses] with n hord hscale
  rcases hscale with ⟨hZ, hZY, hRY, hRsqrt, hWZ⟩
  have hW : 2 ≤ W n := by omega
  intro A hA
  exact admissible_card_le_G_add_structuralError
    hA hZ hZY hW hWZ hRY hRsqrt

/-! ## Negligibility and the structural reduction -/

/-- Every term in the finite structural error is negligible on the
second-order scale. -/
theorem structuralError_negligible :
    NegligibleNatError structuralError := by
  have hbad := BoxPruningError.badPruningError_negligible
  have hy := ElementaryPruningErrors.Y_pow_six_negligible
  have hprime :=
    ElementaryPruningErrors.primeCounting_sqrt_mul_Y_pow_four_negligible
  have hprimeTwo : Tendsto
      (fun n : ℕ =>
        ((2 * (Nat.primeCounting n.sqrt * Y n ^ 4) : ℕ) : ℝ) /
          secondOrderScale n)
      atTop (nhds 0) := by
    have h := hprime.const_mul (2 : ℝ)
    have heq :
        (fun n : ℕ =>
          (2 : ℝ) *
            (((Nat.primeCounting n.sqrt * Y n ^ 4 : ℕ) : ℝ) /
              secondOrderScale n)) =ᶠ[atTop]
        (fun n : ℕ =>
          ((2 * (Nat.primeCounting n.sqrt * Y n ^ 4) : ℕ) : ℝ) /
            secondOrderScale n) := by
      exact Eventually.of_forall fun n => by
        push_cast
        ring
    simpa only [mul_zero] using! h.congr' heq
  have hprimeSq :=
    ElementaryPruningErrors.primeCounting_sqrt_sq_negligible
  have hsmall := SmallPrimeError.smallPrimeError_negligible
  have hlarge := BoxPruningError.largeMultiplierError_negligible
  have hclean := ElementaryPruningErrors.R_pow_four_negligible
  have hoverlap := OverlapPruningError.overlapError_negligible
  have hsum :=
    ((((((hbad.add hy).add hprimeTwo).add hprimeSq).add hsmall).add
      hlarge).add hclean).add hoverlap
  have hsumZero : Tendsto
      (fun n : ℕ =>
        (BoxPruningError.badPruningError n : ℝ) / secondOrderScale n +
          ((Y n ^ 6 : ℕ) : ℝ) / secondOrderScale n +
          (2 * (Nat.primeCounting n.sqrt * Y n ^ 4) : ℕ) /
            secondOrderScale n +
          ((Nat.primeCounting n.sqrt ^ 2 : ℕ) : ℝ) /
            secondOrderScale n +
          (SmallPrimeError.smallPrimeError n : ℝ) / secondOrderScale n +
          (BoxPruningError.largeMultiplierError n : ℝ) /
            secondOrderScale n +
          ((R n ^ 4 : ℕ) : ℝ) / secondOrderScale n +
          (OverlapPruningError.overlapError n : ℝ) /
            secondOrderScale n)
      atTop (nhds 0) := by
    simpa only [add_zero] using! hsum
  unfold NegligibleNatError
  apply hsumZero.congr'
  exact Eventually.of_forall fun n => by
    unfold structuralError SmallPrimeError.smallPrimeError
    push_cast
    ring

/-- The unconditional structural reduction supplied by the finite pruning
argument and the explicit scale choices. -/
theorem structuralReduction : StructuralReduction :=
  structuralReduction_of_uniform_upper_bound
    uniformStructuralUpperBound structuralError_negligible

end StructuralFiniteBound

end Erdos796
