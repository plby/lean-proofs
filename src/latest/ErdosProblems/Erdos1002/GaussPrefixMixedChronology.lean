import ErdosProblems.Erdos1002.GaussPrefixDeepestCylinder
import Mathlib.Data.Fintype.Sort

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Global chronology for labeled mixed Gauss-prefix tuples

The mixed factorial expansion is indexed label by label, so injectivity is
initially available only inside each label.  This file supplies the finite
global chronology used by the early/late argument:

* a tuple with a repeated depth across two disjoint labels has identically
  zero literal character;
* every globally injective tuple admits an increasing enumeration by depth;
* a nonzero Fourier family has a last nonzero occurrence, and global gap
  separation makes every other nonzero carrier lie the prescribed gap
  before it.
-/

open Filter MeasureTheory Set
open scoped BigOperators Topology

namespace Erdos1002

noncomputable section

local instance gaussPrefixMixedChronologyPropDecidable (P : Prop) :
    Decidable P := Classical.propDecidable P

variable {ι : Type*} [Fintype ι]

/-- Global injectivity of the selected depth over all labeled occurrences,
not merely inside each label's embedding. -/
def IsGloballyInjectiveMixedDepthTuple
    (N : ℕ) (k : ι → ℕ) (F : GaussPrefixMixedDepthTuple N k) : Prop :=
  Function.Injective
    (fun z : GaussPrefixMixedOccurrence k ↦ (F z.1 z.2 : ℕ))

/-- Global deterministic gap separation, stated intrinsically in terms of
depth rather than a chosen enumeration. -/
def IsGloballyGapSeparatedMixedDepthTuple
    (N gap : ℕ) (k : ι → ℕ)
    (F : GaussPrefixMixedDepthTuple N k) : Prop :=
  ∀ z z' : GaussPrefixMixedOccurrence k,
    (F z.1 z.2 : ℕ) < (F z'.1 z'.2 : ℕ) →
      (F z.1 z.2 : ℕ) + gap ≤ (F z'.1 z'.2 : ℕ)

/-- Repeating one depth across disjoint labels contributes exactly zero.
Thus all nonzero terms in the mixed factorial expansion may be restricted
to globally injective depth tuples before sorting. -/
theorem gaussPrefixMarkedMixedTupleCharacter_eq_zero_of_not_globalInjective
    (N : ℕ) (B : ι → Set (ℝ × ℝ × ℝ))
    (hdisjoint : ∀ i i', i ≠ i' → Disjoint (B i) (B i'))
    (k : ι → ℕ) (h : ∀ i, Fin (k i) → ℤ)
    (F : GaussPrefixMixedDepthTuple N k)
    (hnot : ¬ IsGloballyInjectiveMixedDepthTuple N k F)
    (x : ℝ) :
    gaussPrefixMarkedMixedTupleCharacter N B k h F x = 0 := by
  classical
  unfold IsGloballyInjectiveMixedDepthTuple Function.Injective at hnot
  push_neg at hnot
  obtain ⟨⟨i, a⟩, ⟨i', b⟩, heq, hne⟩ := hnot
  have hii : i ≠ i' := by
    intro hii
    subst i'
    have hab : a = b := (F i).injective (Subtype.ext heq)
    subst b
    exact hne rfl
  let Eia : Prop := x ∈ gaussPrefixMarkedEvent N (B i) (F i a)
  let Eib : Prop := x ∈ gaussPrefixMarkedEvent N (B i') (F i' b)
  by_cases ha : Eia
  · by_cases hb : Eib
    · have hpa := (selectedGaussPrefixWord_data_of_mem ha).2.2.2
      have hpb := (selectedGaussPrefixWord_data_of_mem hb).2.2.2
      have hpa' :
          gaussPrefixMarkedPoint N (F i' b)
              (selectedGaussPrefixWord (F i' b) x) x ∈ B i := by
        rw [heq] at hpa
        exact hpa
      exact (Set.disjoint_left.mp (hdisjoint i i' hii) hpa' hpb).elim
    · unfold gaussPrefixMarkedMixedTupleCharacter
      apply Finset.prod_eq_zero (Finset.mem_univ i')
      apply Finset.prod_eq_zero (Finset.mem_univ b)
      dsimp only [Eib] at hb
      unfold gaussPrefixMarkedDepthCharacter
      rw [if_neg hb]
  · unfold gaussPrefixMarkedMixedTupleCharacter
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    apply Finset.prod_eq_zero (Finset.mem_univ a)
    dsimp only [Eia] at ha
    unfold gaussPrefixMarkedDepthCharacter
    rw [if_neg ha]

/-- Cardinality of the dependent occurrence type. -/
theorem card_gaussPrefixMixedOccurrence (k : ι → ℕ) :
    Fintype.card (GaussPrefixMixedOccurrence k) = ∑ i, k i := by
  simp [GaussPrefixMixedOccurrence]

/-- A globally injective mixed tuple can be enumerated in strictly
increasing depth order. -/
theorem exists_strictMono_mixedOccurrenceEquiv
    (N : ℕ) (k : ι → ℕ) (F : GaussPrefixMixedDepthTuple N k)
    (hInjective : IsGloballyInjectiveMixedDepthTuple N k F) :
    ∃ e : Fin (Fintype.card (GaussPrefixMixedOccurrence k)) ≃
        GaussPrefixMixedOccurrence k,
      StrictMono (fun j ↦ (F (e j).1 (e j).2 : ℕ)) := by
  let depth : GaussPrefixMixedOccurrence k → ℕ :=
    fun z ↦ (F z.1 z.2 : ℕ)
  let rangeEquiv : GaussPrefixMixedOccurrence k ≃ Set.range depth :=
    Equiv.ofInjective depth hInjective
  let hcard : Fintype.card (Set.range depth) =
      Fintype.card (GaussPrefixMixedOccurrence k) :=
    (Fintype.card_congr rangeEquiv).symm
  let eRange := Fintype.orderIsoFinOfCardEq (Set.range depth) hcard
  let e : Fin (Fintype.card (GaussPrefixMixedOccurrence k)) ≃
      GaussPrefixMixedOccurrence k := eRange.toEquiv.trans rangeEquiv.symm
  refine ⟨e, ?_⟩
  intro a b hab
  have hrange : eRange a < eRange b := eRange.strictMono hab
  have ha : depth (rangeEquiv.symm (eRange a)) = (eRange a : ℕ) :=
    congrArg Subtype.val (rangeEquiv.apply_symm_apply (eRange a))
  have hb : depth (rangeEquiv.symm (eRange b)) = (eRange b : ℕ) :=
    congrArg Subtype.val (rangeEquiv.apply_symm_apply (eRange b))
  change depth (rangeEquiv.symm (eRange a)) <
    depth (rangeEquiv.symm (eRange b))
  rw [ha, hb]
  exact hrange

/-- Every nonzero finite sequence has a last nonzero index. -/
theorem exists_last_nonzero_fin
    {r : ℕ} (a : Fin r → ℤ) (hnonzero : ∃ i, a i ≠ 0) :
    ∃ i : Fin r, a i ≠ 0 ∧ ∀ j : Fin r, i < j → a j = 0 := by
  classical
  let S : Finset (Fin r) := Finset.univ.filter fun i ↦ a i ≠ 0
  have hSne : S.Nonempty := by
    obtain ⟨i, hi⟩ := hnonzero
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  let i : Fin r := S.max' hSne
  have hi : a i ≠ 0 := (Finset.mem_filter.mp (S.max'_mem hSne)).2
  refine ⟨i, hi, ?_⟩
  intro j hij
  by_contra hj
  have hjS : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩
  have hjle : j ≤ i := S.le_max' j hjS
  exact (not_le_of_gt hij) hjle

/-- Intrinsic last-carrier selection.  For a globally injective and
gap-separated tuple, there is a last nonzero Fourier occurrence, and every
other nonzero occurrence lies at least `gap` depths before it.  Later
occurrences are allowed, but necessarily carry Fourier weight zero; these
are precisely the future block in the late-case mixing argument. -/
theorem exists_lastNonzeroOccurrence_with_gap
    (N gap : ℕ) (k : ι → ℕ)
    (h : ∀ i, Fin (k i) → ℤ)
    (F : GaussPrefixMixedDepthTuple N k)
    (hInjective : IsGloballyInjectiveMixedDepthTuple N k F)
    (hSeparated : IsGloballyGapSeparatedMixedDepthTuple N gap k F)
    (hnonzero : ∃ z : GaussPrefixMixedOccurrence k, h z.1 z.2 ≠ 0) :
    ∃ z₀ : GaussPrefixMixedOccurrence k,
      h z₀.1 z₀.2 ≠ 0 ∧
        ∀ z : GaussPrefixMixedOccurrence k, z ≠ z₀ →
          h z.1 z.2 ≠ 0 →
            (F z.1 z.2 : ℕ) + gap ≤ (F z₀.1 z₀.2 : ℕ) := by
  obtain ⟨e, heStrict⟩ :=
    exists_strictMono_mixedOccurrenceEquiv N k F hInjective
  have hnonzeroFin : ∃ j, h (e j).1 (e j).2 ≠ 0 := by
    obtain ⟨z, hz⟩ := hnonzero
    refine ⟨e.symm z, ?_⟩
    rw [e.apply_symm_apply]
    exact hz
  obtain ⟨s, hs, hsLast⟩ :=
    exists_last_nonzero_fin (fun j ↦ h (e j).1 (e j).2) hnonzeroFin
  refine ⟨e s, hs, ?_⟩
  intro z hzNe hzCoeff
  let j : Fin (Fintype.card (GaussPrefixMixedOccurrence k)) := e.symm z
  have hjCoeff : h (e j).1 (e j).2 ≠ 0 := by
    have hej : e j = z := by
      dsimp only [j]
      exact e.apply_symm_apply z
    rw [hej]
    exact hzCoeff
  have hjsNe : j ≠ s := by
    intro hjs
    apply hzNe
    calc
      z = e j := by
        dsimp only [j]
        exact (e.apply_symm_apply z).symm
      _ = e s := congrArg e hjs
  have hnotSltJ : ¬ s < j := by
    intro hsltj
    exact hjCoeff (hsLast j hsltj)
  have hjs : j < s :=
    lt_of_le_of_ne (le_of_not_gt hnotSltJ) hjsNe
  have hdepthLt : (F z.1 z.2 : ℕ) < (F (e s).1 (e s).2 : ℕ) := by
    have hstrict := heStrict hjs
    have hej : e j = z := by
      dsimp only [j]
      exact e.apply_symm_apply z
    change (F (e j).1 (e j).2 : ℕ) <
      (F (e s).1 (e s).2 : ℕ) at hstrict
    rw [hej] at hstrict
    exact hstrict
  exact hSeparated z (e s) hdepthLt

/-! ## Exact prefix/future product split -/

/-- Product of the literal occurrence characters whose depths are no later
than the split depth `m`. -/
def gaussPrefixMarkedMixedPrefixCharacter
    (N : ℕ) (B : ι → Set (ℝ × ℝ × ℝ)) (k : ι → ℕ)
    (h : ∀ i, Fin (k i) → ℤ) (F : GaussPrefixMixedDepthTuple N k)
    (m : ℕ) (x : ℝ) : ℂ :=
  ∏ z ∈ (Finset.univ : Finset (GaussPrefixMixedOccurrence k)).filter
      (fun z ↦ (F z.1 z.2 : ℕ) ≤ m),
    gaussPrefixMarkedDepthCharacter N (B z.1) (F z.1 z.2)
      (h z.1 z.2) x

/-- Signed terminal-denominator carrier belonging only to occurrences no
later than the split depth.  Later zero Fourier modes are absent from this
sum, so it is constant on a depth-`m` cylinder. -/
def gaussPrefixMarkedMixedPrefixCarrier
    (N : ℕ) (k : ι → ℕ) (h : ∀ i, Fin (k i) → ℤ)
    (F : GaussPrefixMixedDepthTuple N k) (m : ℕ) (x : ℝ) : ℝ :=
  ∑ z ∈ (Finset.univ : Finset (GaussPrefixMixedOccurrence k)).filter
      (fun z ↦ (F z.1 z.2 : ℕ) ≤ m),
    (h z.1 z.2 : ℝ) *
      (cfTerminalDenominator
        (selectedGaussPrefixWord (F z.1 z.2) x).1 : ℝ)

private theorem oscillatoryPhase_add_chronology (K M x : ℝ) :
    oscillatoryPhase (K + M) x =
      oscillatoryPhase K x * oscillatoryPhase M x := by
  unfold oscillatoryPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem prod_oscillatoryPhase_finset_eq_sum
    {α : Type*} (S : Finset α) (K : α → ℝ) (x : ℝ) :
    ∏ z ∈ S, oscillatoryPhase (K z) x =
      oscillatoryPhase (∑ z ∈ S, K z) x := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [oscillatoryPhase]
  | @insert z S hz ih =>
      rw [Finset.prod_insert hz, Finset.sum_insert hz, ih,
        ← oscillatoryPhase_add_chronology]

/-- On the simultaneous prefix event, the literal prefix product is exactly
one oscillatory phase with the prefix carrier. -/
theorem gaussPrefixMarkedMixedPrefixCharacter_eq_oscillatoryPhase
    {N : ℕ} {B : ι → Set (ℝ × ℝ × ℝ)} {k : ι → ℕ}
    {h : ∀ i, Fin (k i) → ℤ} {F : GaussPrefixMixedDepthTuple N k}
    {m : ℕ} {x : ℝ}
    (hxUnit : x ∈ Ioo (0 : ℝ) 1)
    (hxNonterm : ∀ r : ℕ, (gaussMap^[r]) x ≠ 0)
    (hxEvents : ∀ z : GaussPrefixMixedOccurrence k,
      (F z.1 z.2 : ℕ) ≤ m →
        x ∈ gaussPrefixMarkedEvent N (B z.1) (F z.1 z.2)) :
    gaussPrefixMarkedMixedPrefixCharacter N B k h F m x =
      oscillatoryPhase
        ((N : ℝ) * gaussPrefixMarkedMixedPrefixCarrier N k h F m x) x := by
  classical
  let S := (Finset.univ : Finset (GaussPrefixMixedOccurrence k)).filter
    (fun z ↦ (F z.1 z.2 : ℕ) ≤ m)
  let K : GaussPrefixMixedOccurrence k → ℝ := fun z ↦
    (N : ℝ) * ((h z.1 z.2 : ℝ) *
      (cfTerminalDenominator
        (selectedGaussPrefixWord (F z.1 z.2) x).1 : ℝ))
  have hone (z : GaussPrefixMixedOccurrence k) (hz : z ∈ S) :
      gaussPrefixMarkedDepthCharacter N (B z.1) (F z.1 z.2)
          (h z.1 z.2) x = oscillatoryPhase (K z) x := by
    have hzDepth : (F z.1 z.2 : ℕ) ≤ m :=
      (Finset.mem_filter.mp hz).2
    simpa only [K, mul_assoc] using!
      gaussPrefixMarkedDepthCharacter_eq_oscillatoryPhase
        hxUnit hxNonterm (hxEvents z hzDepth)
  unfold gaussPrefixMarkedMixedPrefixCharacter
  change (∏ z ∈ S,
    gaussPrefixMarkedDepthCharacter N (B z.1) (F z.1 z.2)
      (h z.1 z.2) x) = _
  calc
    (∏ z ∈ S,
      gaussPrefixMarkedDepthCharacter N (B z.1) (F z.1 z.2)
        (h z.1 z.2) x) =
        ∏ z ∈ S, oscillatoryPhase (K z) x := by
      apply Finset.prod_congr rfl
      intro z hz
      exact hone z hz
    _ = oscillatoryPhase (∑ z ∈ S, K z) x :=
      prod_oscillatoryPhase_finset_eq_sum S K x
    _ = oscillatoryPhase
        ((N : ℝ) * gaussPrefixMarkedMixedPrefixCarrier N k h F m x) x := by
      congr 2
      unfold gaussPrefixMarkedMixedPrefixCarrier K
      rw [Finset.mul_sum]

/-- The prefix carrier is constant on every depth-`m` cylinder, with no
hypothesis on occurrences after `m`. -/
theorem gaussPrefixMarkedMixedPrefixCarrier_eq_on_deeperCylinder
    (N : ℕ) (k : ι → ℕ) (h : ∀ i, Fin (k i) → ℤ)
    (F : GaussPrefixMixedDepthTuple N k) {m : ℕ}
    (w : PositiveDigitWord m) {x y : ℝ}
    (hxUnit : x ∈ Ico (0 : ℝ) 1) (hyUnit : y ∈ Ico (0 : ℝ) 1)
    (hx : x ∈ positivePrefixCylinder m w)
    (hy : y ∈ positivePrefixCylinder m w) :
    gaussPrefixMarkedMixedPrefixCarrier N k h F m x =
      gaussPrefixMarkedMixedPrefixCarrier N k h F m y := by
  classical
  unfold gaussPrefixMarkedMixedPrefixCarrier
  apply Finset.sum_congr rfl
  intro z hz
  have hzDepth : (F z.1 z.2 : ℕ) ≤ m :=
    (Finset.mem_filter.mp hz).2
  have hselected := selectedGaussPrefixWord_eq_on_deeperCylinder
    hzDepth w hxUnit hyUnit hx hy
  rw [hselected]

/-- Named representative value of the prefix carrier on an exact-depth
cylinder. -/
def exactDepthCylinderMixedPrefixCarrier
    (N : ℕ) (k : ι → ℕ) (h : ∀ i, Fin (k i) → ℤ)
    (F : GaussPrefixMixedDepthTuple N k) {m : ℕ}
    (w : ExactDepthBoundedPositiveWord N m) : ℝ :=
  gaussPrefixMarkedMixedPrefixCarrier N k h F m
    (gaussPrefixRepresentative w.1.1)

theorem gaussPrefixMarkedMixedPrefixCarrier_eq_exactDepthCylinder
    (N : ℕ) (k : ι → ℕ) (h : ∀ i, Fin (k i) → ℤ)
    (F : GaussPrefixMixedDepthTuple N k) {m : ℕ}
    (w : ExactDepthBoundedPositiveWord N m) {x : ℝ}
    (hxUnit : x ∈ Ico (0 : ℝ) 1)
    (hx : x ∈ exactDepthBoundedCylinder w) :
    gaussPrefixMarkedMixedPrefixCarrier N k h F m x =
      exactDepthCylinderMixedPrefixCarrier N k h F w := by
  have hrepMem : gaussPrefixRepresentative w.1.1 ∈
      positivePrefixCylinder m w.toPositive :=
    gaussPrefixRepresentative_mem w.1.2.2.1
  have hrepUnit : gaussPrefixRepresentative w.1.1 ∈ Ico (0 : ℝ) 1 := by
    have hrepIoo : gaussPrefixRepresentative w.1.1 ∈ Ioo (0 : ℝ) 1 := by
      unfold gaussPrefixRepresentative
      exact gaussInverseWord_mem_Ioo w.1.2.2.1 (by norm_num)
    exact ⟨hrepIoo.1.le, hrepIoo.2⟩
  exact gaussPrefixMarkedMixedPrefixCarrier_eq_on_deeperCylinder
    N k h F w.toPositive hxUnit hrepUnit hx hrepMem

private theorem half_le_abs_sum_finset_of_dominant
    {α : Type*} [DecidableEq α] (S : Finset α) (term : α → ℝ) (z₀ : α)
    (hz₀ : z₀ ∈ S) {Q : ℝ}
    (hmain : Q ≤ |term z₀|)
    (hrest : ∑ z ∈ S.erase z₀, |term z| ≤ Q / 2) :
    Q / 2 ≤ |∑ z ∈ S, term z| := by
  classical
  let rest : ℝ := ∑ z ∈ S.erase z₀, term z
  have hdecomp : term z₀ + rest = ∑ z ∈ S, term z :=
    Finset.add_sum_erase S term hz₀
  have hrestAbs : |rest| ≤ Q / 2 := by
    calc
      |rest| ≤ ∑ z ∈ S.erase z₀, |term z| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ Q / 2 := hrest
  have htriangle : |term z₀| ≤ |∑ z ∈ S, term z| + |rest| := by
    calc
      |term z₀| = |(∑ z ∈ S, term z) - rest| := by
        rw [← hdecomp]
        ring_nf
      _ ≤ |∑ z ∈ S, term z| + |rest| := abs_sub _ _
  linarith

/-- Deterministic non-cancellation for the *prefix* carrier at the last
nonzero mode.  Occurrences after the split do not appear and require no
depth hypothesis. -/
theorem half_terminalDenominator_le_abs_exactDepthCylinderMixedPrefixCarrier_of_gap
    (N : ℕ) (k : ι → ℕ) (h : ∀ i, Fin (k i) → ℤ)
    (F : GaussPrefixMixedDepthTuple N k) {m gap : ℕ}
    (w : ExactDepthBoundedPositiveWord N m)
    (z₀ : GaussPrefixMixedOccurrence k)
    (hdepth : (F z₀.1 z₀.2 : ℕ) = m)
    (hcoeff : h z₀.1 z₀.2 ≠ 0)
    (hgap : ∀ z : GaussPrefixMixedOccurrence k, z ≠ z₀ →
      h z.1 z.2 ≠ 0 → (F z.1 z.2 : ℕ) + gap ≤ m)
    (hweightBudget :
      2 * (∑ z ∈
          ((Finset.univ : Finset (GaussPrefixMixedOccurrence k)).filter
            (fun z ↦ (F z.1 z.2 : ℕ) ≤ m)).erase z₀,
        |(h z.1 z.2 : ℝ)|) ≤ ((2 ^ (gap / 2) : ℕ) : ℝ)) :
    (cfTerminalDenominator w.1.1 : ℝ) / 2 ≤
      |exactDepthCylinderMixedPrefixCarrier N k h F w| := by
  classical
  let S : Finset (GaussPrefixMixedOccurrence k) :=
    (Finset.univ : Finset (GaussPrefixMixedOccurrence k)).filter
      (fun z ↦ (F z.1 z.2 : ℕ) ≤ m)
  let representative : ℝ := gaussPrefixRepresentative w.1.1
  let q : GaussPrefixMixedOccurrence k → ℝ := fun z ↦
    (cfTerminalDenominator
      (selectedGaussPrefixWord (F z.1 z.2) representative).1 : ℝ)
  let weight : GaussPrefixMixedOccurrence k → ℝ :=
    fun z ↦ |(h z.1 z.2 : ℝ)|
  let term : GaussPrefixMixedOccurrence k → ℝ := fun z ↦
    (h z.1 z.2 : ℝ) * q z
  let P : ℝ := ((2 ^ (gap / 2) : ℕ) : ℝ)
  let Q : ℝ := (cfTerminalDenominator w.1.1 : ℝ)
  have hrepMem : representative ∈ positivePrefixCylinder m w.toPositive := by
    exact gaussPrefixRepresentative_mem w.1.2.2.1
  have hrepUnit : representative ∈ Ico (0 : ℝ) 1 := by
    have hrepIoo : representative ∈ Ioo (0 : ℝ) 1 := by
      dsimp only [representative]
      unfold gaussPrefixRepresentative
      exact gaussInverseWord_mem_Ioo w.1.2.2.1 (by norm_num)
    exact ⟨hrepIoo.1.le, hrepIoo.2⟩
  have hz₀S : z₀ ∈ S := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ z₀, hdepth.le⟩
  have hdenominatorLatest :
      cfTerminalDenominator
          (selectedGaussPrefixWord (F z₀.1 z₀.2 : ℕ) representative).1 =
        cfTerminalDenominator w.1.1 := by
    have hselected :
        selectedGaussPrefixWord (F z₀.1 z₀.2 : ℕ) representative =
          positiveDigitWordTake (F z₀.1 z₀.2 : ℕ)
            hdepth.le w.toPositive :=
      selectedGaussPrefixWord_eq_positiveDigitWordTake
        hdepth.le w.toPositive hrepUnit hrepMem
    rw [hselected]
    simp only [positiveDigitWordTake, hdepth]
    change cfTerminalDenominator (w.1.1.take m) =
      cfTerminalDenominator w.1.1
    rw [List.take_of_length_le]
    rw [w.2]
  have habsCoeff : (1 : ℝ) ≤ |(h z₀.1 z₀.2 : ℝ)| := by
    have hnat : 1 ≤ (h z₀.1 z₀.2).natAbs :=
      Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hcoeff)
    calc
      (1 : ℝ) ≤ ((h z₀.1 z₀.2).natAbs : ℝ) := by
        exact_mod_cast hnat
      _ = |(h z₀.1 z₀.2 : ℝ)| := by simp
  have hmain : Q ≤ |term z₀| := by
    dsimp only [term, q, Q]
    rw [hdenominatorLatest, abs_mul,
      abs_of_nonneg (show 0 ≤ (cfTerminalDenominator w.1.1 : ℝ) by
        positivity)]
    simpa only [one_mul] using!
      (mul_le_mul_of_nonneg_right habsCoeff
        (show 0 ≤ (cfTerminalDenominator w.1.1 : ℝ) by positivity))
  have hP : 0 < P := by
    dsimp only [P]
    positivity
  have hQ : 0 ≤ Q := by
    dsimp only [Q]
    positivity
  have hscale : ∀ z ∈ S.erase z₀,
      weight z = 0 ∨ P * q z ≤ Q := by
    intro z hz
    have hzS := (Finset.mem_erase.mp hz).2
    have hzNe := (Finset.mem_erase.mp hz).1
    have hzDepth : (F z.1 z.2 : ℕ) ≤ m :=
      (Finset.mem_filter.mp hzS).2
    by_cases hzero : h z.1 z.2 = 0
    · left
      dsimp only [weight]
      simp only [hzero, Int.cast_zero, abs_zero]
    right
    have hgapz := hgap z hzNe hzero
    have hexponent : gap / 2 ≤ (m - (F z.1 z.2 : ℕ)) / 2 := by
      omega
    have hpow : 2 ^ (gap / 2) ≤
        2 ^ ((m - (F z.1 z.2 : ℕ)) / 2) :=
      Nat.pow_le_pow_right (by norm_num) hexponent
    have hselected :
        selectedGaussPrefixWord (F z.1 z.2 : ℕ) representative =
          positiveDigitWordTake (F z.1 z.2 : ℕ) hzDepth w.toPositive :=
      selectedGaussPrefixWord_eq_positiveDigitWordTake
        hzDepth w.toPositive hrepUnit hrepMem
    have hgrowth :=
      pow_two_depthGap_mul_cfTerminalDenominator_take_le
        (F z.1 z.2 : ℕ) hzDepth w.toPositive
    have hmul :
        2 ^ (gap / 2) *
            cfTerminalDenominator
              (selectedGaussPrefixWord (F z.1 z.2) representative).1 ≤
          cfTerminalDenominator w.1.1 := by
      rw [hselected]
      exact (Nat.mul_le_mul_right _ hpow).trans hgrowth
    dsimp only [P, q, Q]
    exact_mod_cast hmul
  have htwo : 2 * (∑ z ∈ S.erase z₀, weight z * q z) ≤ Q :=
    two_mul_sum_weight_mul_le_of_common_scale (S.erase z₀) weight q
      hP hQ (fun z _hz ↦ abs_nonneg _) hscale (by
        simpa only [S, weight, P] using! hweightBudget)
  have hrest : ∑ z ∈ S.erase z₀, |term z| ≤ Q / 2 := by
    have hrewrite :
        (∑ z ∈ S.erase z₀, |term z|) =
          ∑ z ∈ S.erase z₀, weight z * q z := by
      apply Finset.sum_congr rfl
      intro z _hz
      dsimp only [term, weight]
      rw [abs_mul, abs_of_nonneg (show 0 ≤ q z by
        dsimp only [q]
        positivity)]
    rw [hrewrite]
    linarith
  change Q / 2 ≤ |∑ z ∈ S, term z|
  apply half_le_abs_sum_finset_of_dominant S term z₀ hz₀S hmain
  simpa using! hrest

/-- Complementary product over occurrences strictly after the split. -/
def gaussPrefixMarkedMixedFutureCharacter
    (N : ℕ) (B : ι → Set (ℝ × ℝ × ℝ)) (k : ι → ℕ)
    (h : ∀ i, Fin (k i) → ℤ) (F : GaussPrefixMixedDepthTuple N k)
    (m : ℕ) (x : ℝ) : ℂ :=
  ∏ z ∈ (Finset.univ : Finset (GaussPrefixMixedOccurrence k)).filter
      (fun z ↦ ¬ (F z.1 z.2 : ℕ) ≤ m),
    gaussPrefixMarkedDepthCharacter N (B z.1) (F z.1 z.2)
      (h z.1 z.2) x

/-- The labeled mixed tuple character splits exactly at every deterministic
depth.  This is a finite-product identity, before any approximation or
mixing estimate. -/
theorem gaussPrefixMarkedMixedTupleCharacter_eq_prefix_mul_future
    (N : ℕ) (B : ι → Set (ℝ × ℝ × ℝ)) (k : ι → ℕ)
    (h : ∀ i, Fin (k i) → ℤ) (F : GaussPrefixMixedDepthTuple N k)
    (m : ℕ) (x : ℝ) :
    gaussPrefixMarkedMixedTupleCharacter N B k h F x =
      gaussPrefixMarkedMixedPrefixCharacter N B k h F m x *
        gaussPrefixMarkedMixedFutureCharacter N B k h F m x := by
  classical
  unfold gaussPrefixMarkedMixedTupleCharacter
  unfold gaussPrefixMarkedMixedPrefixCharacter
  unfold gaussPrefixMarkedMixedFutureCharacter
  rw [← Fintype.prod_sigma']
  exact (Finset.prod_filter_mul_prod_filter_not
    (Finset.univ : Finset (GaussPrefixMixedOccurrence k))
    (fun z ↦ (F z.1 z.2 : ℕ) ≤ m)
    (fun z ↦ gaussPrefixMarkedDepthCharacter N (B z.1)
      (F z.1 z.2) (h z.1 z.2) x)).symm

/-- Simultaneous literal event carried by all occurrences after `m`. -/
def gaussPrefixMarkedMixedFutureEvent
    (N : ℕ) (B : ι → Set (ℝ × ℝ × ℝ)) (k : ι → ℕ)
    (F : GaussPrefixMixedDepthTuple N k) (m : ℕ) : Set ℝ :=
  {x | ∀ z : GaussPrefixMixedOccurrence k,
    m < (F z.1 z.2 : ℕ) →
      x ∈ gaussPrefixMarkedEvent N (B z.1) (F z.1 z.2)}

theorem measurableSet_gaussPrefixMarkedMixedFutureEvent
    (N : ℕ) {B : ι → Set (ℝ × ℝ × ℝ)}
    (hB : ∀ i, MeasurableSet (B i)) (k : ι → ℕ)
    (F : GaussPrefixMixedDepthTuple N k) (m : ℕ) :
    MeasurableSet (gaussPrefixMarkedMixedFutureEvent N B k F m) := by
  have heq : gaussPrefixMarkedMixedFutureEvent N B k F m =
      ⋂ z : GaussPrefixMixedOccurrence k,
        if m < (F z.1 z.2 : ℕ) then
          gaussPrefixMarkedEvent N (B z.1) (F z.1 z.2)
        else Set.univ := by
    ext x
    unfold gaussPrefixMarkedMixedFutureEvent
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    change (∀ z : GaussPrefixMixedOccurrence k,
        m < (F z.1 z.2 : ℕ) →
          x ∈ gaussPrefixMarkedEvent N (B z.1) (F z.1 z.2)) ↔
      ∀ z : GaussPrefixMixedOccurrence k,
        x ∈ if m < (F z.1 z.2 : ℕ) then
          gaussPrefixMarkedEvent N (B z.1) (F z.1 z.2)
        else Set.univ
    constructor
    · intro hall z
      by_cases hz : m < (F z.1 z.2 : ℕ)
      · simpa only [if_pos hz] using! hall z hz
      · simp only [if_neg hz, Set.mem_univ]
    · intro hall z hz
      have hzmem := hall z
      simpa only [if_pos hz] using! hzmem
  rw [heq]
  apply MeasurableSet.iInter
  intro z
  split_ifs
  · exact measurableSet_gaussPrefixMarkedEvent N (F z.1 z.2) (hB z.1)
  · exact MeasurableSet.univ

/-- If every occurrence after `m` has Fourier weight zero, the future
character is exactly the complex indicator of the simultaneous future
event. -/
theorem gaussPrefixMarkedMixedFutureCharacter_eq_indicator_of_modes_zero
    (N : ℕ) (B : ι → Set (ℝ × ℝ × ℝ)) (k : ι → ℕ)
    (h : ∀ i, Fin (k i) → ℤ) (F : GaussPrefixMixedDepthTuple N k)
    (m : ℕ)
    (hzero : ∀ z : GaussPrefixMixedOccurrence k,
      m < (F z.1 z.2 : ℕ) → h z.1 z.2 = 0)
    (x : ℝ) :
    gaussPrefixMarkedMixedFutureCharacter N B k h F m x =
      (gaussPrefixMarkedMixedFutureEvent N B k F m).indicator
        (fun _ ↦ (1 : ℂ)) x := by
  classical
  by_cases hall : ∀ z : GaussPrefixMixedOccurrence k,
      m < (F z.1 z.2 : ℕ) →
        x ∈ gaussPrefixMarkedEvent N (B z.1) (F z.1 z.2)
  · have hxEvent : x ∈ gaussPrefixMarkedMixedFutureEvent N B k F m := hall
    rw [Set.indicator_of_mem hxEvent]
    unfold gaussPrefixMarkedMixedFutureCharacter
    apply Finset.prod_eq_one
    intro z hz
    have hzLate : m < (F z.1 z.2 : ℕ) := by
      have hzNot := (Finset.mem_filter.mp hz).2
      omega
    rw [hzero z hzLate,
      gaussPrefixMarkedDepthCharacter_zero,
      if_pos (hall z hzLate)]
  · have hxNot : x ∉ gaussPrefixMarkedMixedFutureEvent N B k F m := hall
    rw [Set.indicator_of_notMem hxNot]
    push_neg at hall
    obtain ⟨z, hzLate, hzNot⟩ := hall
    unfold gaussPrefixMarkedMixedFutureCharacter
    apply Finset.prod_eq_zero
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ z, by omega⟩
    · rw [hzero z hzLate,
        gaussPrefixMarkedDepthCharacter_zero, if_neg hzNot]

theorem gaussPrefixMarkedMixedTupleCharacter_eq_prefix_mul_futureIndicator
    (N : ℕ) (B : ι → Set (ℝ × ℝ × ℝ)) (k : ι → ℕ)
    (h : ∀ i, Fin (k i) → ℤ) (F : GaussPrefixMixedDepthTuple N k)
    (m : ℕ)
    (hzero : ∀ z : GaussPrefixMixedOccurrence k,
      m < (F z.1 z.2 : ℕ) → h z.1 z.2 = 0)
    (x : ℝ) :
    gaussPrefixMarkedMixedTupleCharacter N B k h F x =
      gaussPrefixMarkedMixedPrefixCharacter N B k h F m x *
        (gaussPrefixMarkedMixedFutureEvent N B k F m).indicator
          (fun _ ↦ (1 : ℂ)) x := by
  rw [gaussPrefixMarkedMixedTupleCharacter_eq_prefix_mul_future]
  rw [gaussPrefixMarkedMixedFutureCharacter_eq_indicator_of_modes_zero
    N B k h F m hzero]

end

end Erdos1002
