import ErdosProblems.Erdos4.FGKMTMaskedFourier
import ErdosProblems.Erdos4.FGKMTTranslatedEdges
import ErdosProblems.Erdos4.AffineWeights

/-! Actual translated integer weights and their exact anchored unit-ratio values. -/

open scoped BigOperators

namespace Erdos4.FGKMT

open Classical LocalOrthogonality AnchoredFourierAverage ProductCharacterEncoding

section OneFamily

variable {P : Type*} [Fintype P] [DecidableEq P] {k : ℕ}
    (ell : P → ℕ) [∀ l, Fact (ell l).Prime]

noncomputable def translatedResidueState (h : Fin k → ℕ) (Y n p : ℕ) (l : P) : Option (Fin k) :=
  AffineWeights.state (fun i => (h i : ZMod (ell l)))
    ((n : ZMod (ell l)) - Y) (p : ZMod (ell l))

noncomputable def rationalTranslatedAmplitude (b : ℝ) (R : ℕ)
    (h : Fin k → ℕ) (Y p n : ℕ) : ℝ :=
  ∑ a : P → Option (Fin k), rationalCoefficient b R ell a *
    ∏ l, extendedBasis (ell l : ℝ) (a l) (translatedResidueState ell h Y n p l)

noncomputable def translatedSmallMask (h : Fin k → ℕ) (Y p n : ℕ) : ℝ :=
  ∏ l, if (∀ i, (n : ZMod (ell l)) - Y + (h i : ZMod (ell l)) * p ≠ 0) then 1 else 0

theorem translatedSmallMask_nonneg (h : Fin k → ℕ) (Y p n : ℕ) :
    0 ≤ translatedSmallMask ell h Y p n := by
  apply Finset.prod_nonneg
  intro l _
  split_ifs <;> norm_num

theorem translatedResidueState_anchor (h : Fin k → ℕ)
    (hinj : ∀ l, Function.Injective (fun i => (h i : ZMod (ell l))))
    (Y p q : ℕ) (hshift : ∀ i, h i * p ≤ Y)
    (hp : ∀ l, (p : ZMod (ell l)) ≠ 0) (hq : ∀ l, (q : ZMod (ell l)) ≠ 0)
    (j : Fin k) (u : ∀ l, (ZMod (ell l))ˣ)
    (hu : ∀ l, (u l : ZMod (ell l)) = (p : ZMod (ell l)) / q) (l : P) :
    translatedResidueState ell h Y (q + Y - h j * p) p l =
      RootStates.rootState (Finset.univ.erase j)
        (AnchorRoots.anchorRoot (fun i => (h i : ZMod (ell l))) j) (u l) := by
  have hle : h j * p ≤ q + Y := by have hh := hshift j; omega
  have hc : ((q + Y - h j * p : ℕ) : ZMod (ell l)) - Y =
      (q : ZMod (ell l)) - (h j : ZMod (ell l)) * p := by
    rw [Nat.cast_sub hle, Nat.cast_add, Nat.cast_mul]
    ring
  unfold translatedResidueState
  rw [hc]
  exact AffineWeights.state_at_anchor _ (hinj l) j _ _ (hp l) (hq l) (u l) (hu l)

theorem rationalTranslatedAmplitude_anchor (b : ℝ) (R : ℕ) (h : Fin k → ℕ)
    (hinj : ∀ l, Function.Injective (fun i => (h i : ZMod (ell l))))
    (Y p q : ℕ) (hshift : ∀ i, h i * p ≤ Y)
    (hp : ∀ l, (p : ZMod (ell l)) ≠ 0) (hq : ∀ l, (q : ZMod (ell l)) ≠ 0)
    (j : Fin k) (u : ∀ l, (ZMod (ell l))ˣ)
    (hu : ∀ l, (u l : ZMod (ell l)) = (p : ZMod (ell l)) / q) :
    rationalTranslatedAmplitude ell b R h Y p (q + Y - h j * p) =
      rationalUnitAmplitude ell b R (fun l i => (h i : ZMod (ell l))) j u := by
  unfold rationalTranslatedAmplitude rationalUnitAmplitude
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  apply Finset.prod_congr rfl
  intro l _
  rw [translatedResidueState_anchor ell h hinj Y p q hshift hp hq j u hu l]

theorem translatedSmallMask_anchor (h : Fin k → ℕ) (Y p q : ℕ)
    (hshift : ∀ i, h i * p ≤ Y) (hq : ∀ l, (q : ZMod (ell l)) ≠ 0)
    (j : Fin k) (u : ∀ l, (ZMod (ell l))ˣ)
    (hu : ∀ l, (u l : ZMod (ell l)) = (p : ZMod (ell l)) / q) :
    translatedSmallMask ell h Y p (q + Y - h j * p) =
      smallProductRealMask ell (fun l i => (h i : ZMod (ell l))) j u := by
  unfold translatedSmallMask smallProductRealMask
  apply Finset.prod_congr rfl
  intro l _
  have heq : ∀ i,
      ((q + Y - h j * p : ℕ) : ZMod (ell l)) - Y + (h i : ZMod (ell l)) * p =
        (q : ZMod (ell l)) * (1 + ((h i : ZMod (ell l)) - h j) * (u l : ZMod (ell l))) := by
    intro i
    rw [translated_anchor_residue h hshift j i (ell l), hu l]
    field_simp [hq l]
  have hpred : (∀ i, ((q + Y - h j * p : ℕ) : ZMod (ell l)) - Y +
      (h i : ZMod (ell l)) * p ≠ 0) ↔
        SmallAnchorGood (fun i => (h i : ZMod (ell l))) j (u l) := by
    unfold SmallAnchorGood
    apply forall_congr'
    intro i
    rw [heq i, mul_ne_zero_iff]
    exact ⟨And.right, fun hh => ⟨hq l, hh⟩⟩
  simp only [hpred]

theorem unitPoint_natCast_ne_zero (n : ℕ) (hn : n.Coprime (modulus ell)) (l : P) :
    (n : ZMod (ell l)) ≠ 0 := by
  rw [← AffineWeights.unitPoint_coe ell n hn l]
  exact Units.ne_zero _

theorem unitPoint_ratio_coe (p q : ℕ) (hp : p.Coprime (modulus ell))
    (hq : q.Coprime (modulus ell)) (l : P) :
    ((unitPoint ell p hp / unitPoint ell q hq) l : ZMod (ell l)) =
      (p : ZMod (ell l)) / q := by
  simp only [Pi.div_apply, Units.val_div_eq_div_val, AffineWeights.unitPoint_coe]

end OneFamily

variable {P Q : Type*} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q] {k : ℕ}
    (ell₀ : P → ℕ) (ell₁ : Q → ℕ)
    [∀ l, Fact (ell₀ l).Prime] [∀ l, Fact (ell₁ l).Prime]

noncomputable def maskedTranslatedWeight (b : ℝ) (R : ℕ)
    (h : Fin k → ℕ) (Y p n : ℕ) : ℝ :=
  translatedSmallMask ell₀ h Y p n * rationalTranslatedAmplitude ell₁ b R h Y p n ^ 2

theorem maskedTranslatedWeight_nonneg (b : ℝ) (R : ℕ)
    (h : Fin k → ℕ) (Y p n : ℕ) : 0 ≤ maskedTranslatedWeight ell₀ ell₁ b R h Y p n :=
  mul_nonneg (translatedSmallMask_nonneg ell₀ h Y p n) (sq_nonneg _)

theorem maskedTranslatedWeight_anchor (b : ℝ) (R : ℕ) (h : Fin k → ℕ)
    (hinj : ∀ l, Function.Injective (fun i => (h i : ZMod (ell₁ l))))
    (Y p q : ℕ) (hshift : ∀ i, h i * p ≤ Y)
    (hp : p.Coprime (modulus (Sum.elim ell₀ ell₁)))
    (hq : q.Coprime (modulus (Sum.elim ell₀ ell₁))) (j : Fin k) :
    maskedTranslatedWeight ell₀ ell₁ b R h Y p (q + Y - h j * p) =
      maskedUnitWeight ell₀ ell₁ b R
        (fun l i => (h i : ZMod (ell₀ l))) (fun l i => (h i : ZMod (ell₁ l))) j
        (unitPoint (Sum.elim ell₀ ell₁) p hp / unitPoint (Sum.elim ell₀ ell₁) q hq) := by
  let u := unitPoint (Sum.elim ell₀ ell₁) p hp / unitPoint (Sum.elim ell₀ ell₁) q hq
  have hsmall := translatedSmallMask_anchor ell₀ h Y p q hshift
    (fun l => unitPoint_natCast_ne_zero (Sum.elim ell₀ ell₁) q hq (.inl l)) j
    (fun l => u (.inl l))
    (fun l => unitPoint_ratio_coe (Sum.elim ell₀ ell₁) p q hp hq (.inl l))
  have hlarge := rationalTranslatedAmplitude_anchor ell₁ b R h hinj Y p q hshift
    (fun l => unitPoint_natCast_ne_zero (Sum.elim ell₀ ell₁) p hp (.inr l))
    (fun l => unitPoint_natCast_ne_zero (Sum.elim ell₀ ell₁) q hq (.inr l)) j
    (fun l => u (.inr l))
    (fun l => unitPoint_ratio_coe (Sum.elim ell₀ ell₁) p q hp hq (.inr l))
  change translatedSmallMask ell₀ h Y p (q + Y - h j * p) *
    rationalTranslatedAmplitude ell₁ b R h Y p (q + Y - h j * p) ^ 2 =
      smallProductRealMask ell₀ (fun l i => (h i : ZMod (ell₀ l))) j (fun l => u (.inl l)) *
        rationalUnitAmplitude ell₁ b R (fun l i => (h i : ZMod (ell₁ l))) j
          (fun l => u (.inr l)) ^ 2
  rw [hsmall, hlarge]

end Erdos4.FGKMT
