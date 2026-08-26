import ErdosProblems.Erdos1002.ChronologicalShortTupleCounting
import ErdosProblems.Erdos1002.GaussPrefixAnnularDepthBoxes

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Collision and short-gap densities for annular depth tuples

The labeled product of logarithmic depth boxes has the correct product
density.  To pass to a strict chronological order, two deterministic
exceptional families must be removed:

* assignments with a collision between two labeled occurrences;
* injective assignments whose chronological ordering contains a gap
  shorter than the chosen separation scale.

Both have `O(H^(r-1))` rather than `O(H^r)` possibilities when all depths
are bounded by `H`.  This file proves the collision estimate first, with a
literal injective code that records the colliding pair and deletes one
redundant coordinate.
-/

open Filter Set Finset
open scoped BigOperators Topology

namespace Erdos1002

noncomputable section

local instance gaussPrefixAnnularTupleDensityPropDecidable (P : Prop) :
    Decidable P := Classical.propDecidable P

set_option maxHeartbeats 800000

/-! ## A general collision code for finite boxes -/

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- Noninjective elements of a finite dependent product box. -/
def NoninjectiveBoxAssignment (boxes : σ → Finset ℕ) :=
  {f : σ → ℕ // f ∈
    (Fintype.piFinset boxes).filter
      (fun g ↦ ¬ Function.Injective g)}

noncomputable instance noninjectiveBoxAssignmentFintype
    (boxes : σ → Finset ℕ) :
    Fintype (NoninjectiveBoxAssignment boxes) := by
  classical
  unfold NoninjectiveBoxAssignment
  infer_instance

/-- A chosen unequal pair on which a noninjective box assignment agrees. -/
def BoxCollisionWitnessData {boxes : σ → Finset ℕ}
    (F : NoninjectiveBoxAssignment boxes) :=
  {p : σ × σ // p.1 ≠ p.2 ∧ F.1 p.1 = F.1 p.2}

noncomputable def boxCollisionWitnessData {boxes : σ → Finset ℕ}
    (F : NoninjectiveBoxAssignment boxes) :
    BoxCollisionWitnessData F :=
  Classical.choice (by
    classical
    have hmem := Finset.mem_filter.mp F.2
    have hnot := hmem.2
    unfold Function.Injective at hnot
    push_neg at hnot
    rcases hnot with ⟨i, j, heq, hne⟩
    exact ⟨⟨(i, j), hne, heq⟩⟩)

/-- The collision witness, with the first coordinate packaged as an
element distinct from the deleted second coordinate. -/
noncomputable def boxCollisionWitness {boxes : σ → Finset ℕ}
    (F : NoninjectiveBoxAssignment boxes) :
    Σ j : σ, {i : σ // i ≠ j} :=
  ⟨(boxCollisionWitnessData F).1.2,
    ⟨(boxCollisionWitnessData F).1.1,
      (boxCollisionWitnessData F).2.1⟩⟩

theorem boxCollisionWitness_eq {boxes : σ → Finset ℕ}
    (F : NoninjectiveBoxAssignment boxes) :
    F.1 (boxCollisionWitness F).2.1 =
      F.1 (boxCollisionWitness F).1 :=
  (boxCollisionWitnessData F).2.2

/-- Code space obtained by deleting the second coordinate of a chosen
collision. -/
abbrev BoxCollisionCode (σ : Type*) [Fintype σ] (H : ℕ) :=
  Σ j : σ, {i : σ // i ≠ j} × ({z : σ // z ≠ j} → Fin H)

/-- Decode the deleted coordinate by copying the equal retained
coordinate. -/
def decodeBoxCollisionCode {H : ℕ}
    (c : BoxCollisionCode σ H) : σ → Fin H :=
  fun z ↦ if hz : z = c.1 then
    c.2.2 ⟨c.2.1.1, c.2.1.2⟩
  else
    c.2.2 ⟨z, hz⟩

/-- Literal collision code for a box whose entries are all below `H`. -/
noncomputable def noninjectiveBoxAssignmentCode
    {boxes : σ → Finset ℕ} {H : ℕ}
    (hbound : ∀ i n, n ∈ boxes i → n < H)
    (F : NoninjectiveBoxAssignment boxes) :
    BoxCollisionCode σ H :=
  ⟨(boxCollisionWitness F).1,
    (boxCollisionWitness F).2,
    fun z ↦ ⟨F.1 z.1, hbound z.1 (F.1 z.1) (by
      have hmem : ∀ i, F.1 i ∈ boxes i := by
        have hbox := (Finset.mem_filter.mp F.2).1
        simpa only [Fintype.mem_piFinset] using! hbox
      exact hmem z.1)⟩⟩

theorem decode_noninjectiveBoxAssignmentCode
    {boxes : σ → Finset ℕ} {H : ℕ}
    (hbound : ∀ i n, n ∈ boxes i → n < H)
    (F : NoninjectiveBoxAssignment boxes) (z : σ) :
    (decodeBoxCollisionCode
      (noninjectiveBoxAssignmentCode hbound F) z).1 = F.1 z := by
  unfold decodeBoxCollisionCode noninjectiveBoxAssignmentCode
  dsimp only
  split_ifs with hz
  · rw [hz]
    exact boxCollisionWitness_eq F
  · rfl

theorem noninjectiveBoxAssignmentCode_injective
    {boxes : σ → Finset ℕ} {H : ℕ}
    (hbound : ∀ i n, n ∈ boxes i → n < H) :
    Function.Injective (noninjectiveBoxAssignmentCode hbound) := by
  intro F G hFG
  apply Subtype.ext
  funext z
  have hdecode :=
    congrArg (fun c ↦ (decodeBoxCollisionCode c z).1) hFG
  change
    (decodeBoxCollisionCode
        (noninjectiveBoxAssignmentCode hbound F) z).1 =
      (decodeBoxCollisionCode
        (noninjectiveBoxAssignmentCode hbound G) z).1 at hdecode
  rw [decode_noninjectiveBoxAssignmentCode hbound F z,
    decode_noninjectiveBoxAssignmentCode hbound G z] at hdecode
  exact hdecode

theorem card_boxCollisionCode (H : ℕ) :
    Fintype.card (BoxCollisionCode σ H) =
      ∑ _j : σ,
        (Fintype.card σ - 1) * H ^ (Fintype.card σ - 1) := by
  simp [BoxCollisionCode, Fintype.card_sigma, Fintype.card_prod,
    Fintype.card_subtype_compl]

/-- Uniform collision bound for an arbitrary finite dependent box. -/
theorem card_noninjectiveBoxAssignment_le
    {boxes : σ → Finset ℕ} {H : ℕ}
    (hbound : ∀ i n, n ∈ boxes i → n < H) :
    Fintype.card (NoninjectiveBoxAssignment boxes) ≤
      Fintype.card σ * Fintype.card σ *
        H ^ (Fintype.card σ - 1) := by
  calc
    Fintype.card (NoninjectiveBoxAssignment boxes) ≤
        Fintype.card (BoxCollisionCode σ H) :=
      Fintype.card_le_of_injective _
        (noninjectiveBoxAssignmentCode_injective hbound)
    _ = ∑ _j : σ,
        (Fintype.card σ - 1) * H ^ (Fintype.card σ - 1) :=
      card_boxCollisionCode H
    _ ≤ ∑ _j : σ,
        Fintype.card σ * H ^ (Fintype.card σ - 1) := by
      apply Finset.sum_le_sum
      intro _j _hj
      exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    _ = _ := by simp [mul_assoc]

/-- Finset form of the same bound. -/
theorem card_filter_not_injective_piFinset_le
    {boxes : σ → Finset ℕ} {H : ℕ}
    (hbound : ∀ i n, n ∈ boxes i → n < H) :
    ((Fintype.piFinset boxes).filter
      (fun f ↦ ¬ Function.Injective f)).card ≤
        Fintype.card σ * Fintype.card σ *
          H ^ (Fintype.card σ - 1) := by
  rw [← Fintype.card_coe]
  exact card_noninjectiveBoxAssignment_le hbound

/-! ## A literal short-gap code for chronological natural tuples -/

/-- A chronological natural tuple, once a common strict upper bound is
given, regarded as a chronological tuple in the finite interval
`Fin H`. -/
def naturalTupleAsFin {r H : ℕ} (t : Fin r → ℕ)
    (hbound : ∀ i, t i < H) : Fin r → Fin H :=
  fun i ↦ ⟨t i, hbound i⟩

theorem naturalTupleAsFin_chronological {r H : ℕ}
    (t : Fin r → ℕ) (hbound : ∀ i, t i < H)
    (hchron : IsChronologicalNatTuple t) :
    IsChronologicalTuple (naturalTupleAsFin t hbound) := by
  intro i j hij
  exact hchron i j hij

theorem exists_short_pair_of_not_separated_nat
    {r gap : ℕ} {t : Fin r → ℕ}
    (ht : ¬ IsSeparatedNatTuple gap t) :
    ∃ i j : Fin r, i < j ∧ ¬ t i + gap ≤ t j := by
  by_contra h
  push_neg at h
  exact ht (fun i j hij ↦ h i j hij)

/-- Subtype of the short members of a finite natural tuple family. -/
abbrev NaturalShortMember {r gap : ℕ}
    (tuples : Finset (Fin r → ℕ)) :=
  {t // t ∈ shortNatTupleFamily gap tuples}

/-- A short tuple together with a chosen short pair and the full finite
tuple.  Keeping the equality to the original tuple in the data makes
the resulting code visibly reversible. -/
def NaturalShortWitnessData
    {r H gap : ℕ} {tuples : Finset (Fin r → ℕ)}
    (t : NaturalShortMember (gap := gap) tuples) :=
  {w : ChronologicalShortWitness r H gap //
    ∀ a, (w.2.2.1 a).1 = t.1 a}

noncomputable def naturalShortWitnessData
    {r H gap : ℕ} {tuples : Finset (Fin r → ℕ)}
    (hchron : ∀ t ∈ tuples, IsChronologicalNatTuple t)
    (hbound : ∀ t ∈ tuples, ∀ i, t i < H)
    (t : NaturalShortMember (gap := gap) tuples) :
    NaturalShortWitnessData (H := H) t :=
  Classical.choice (by
    have htmem := (mem_shortNatTupleFamily_iff.mp t.2).1
    have htshort := (mem_shortNatTupleFamily_iff.mp t.2).2
    rcases exists_short_pair_of_not_separated_nat htshort with
      ⟨i, j, hij, hbad⟩
    let bound : ∀ a, t.1 a < H := hbound t.1 htmem
    let tf : Fin r → Fin H := naturalTupleAsFin t.1 bound
    have hchronFin : IsChronologicalTuple tf :=
      naturalTupleAsFin_chronological t.1 bound
        (hchron t.1 htmem)
    refine ⟨⟨⟨i, j, ⟨tf, hchronFin, hij, ?_⟩⟩, ?_⟩⟩
    · exact hbad
    · intro a
      rfl)

noncomputable def naturalShortWitness
    {r H gap : ℕ} {tuples : Finset (Fin r → ℕ)}
    (hchron : ∀ t ∈ tuples, IsChronologicalNatTuple t)
    (hbound : ∀ t ∈ tuples, ∀ i, t i < H)
    (t : NaturalShortMember (gap := gap) tuples) :
    ChronologicalShortWitness r H gap :=
  (naturalShortWitnessData hchron hbound t).1

theorem naturalShortWitness_tuple_val
    {r H gap : ℕ} {tuples : Finset (Fin r → ℕ)}
    (hchron : ∀ t ∈ tuples, IsChronologicalNatTuple t)
    (hbound : ∀ t ∈ tuples, ∀ i, t i < H)
    (t : NaturalShortMember (gap := gap) tuples) (a : Fin r) :
    ((naturalShortWitness hchron hbound t).2.2.1 a).1 =
      t.1 a := by
  exact (naturalShortWitnessData hchron hbound t).2 a

theorem naturalShortWitness_injective
    {r H gap : ℕ} {tuples : Finset (Fin r → ℕ)}
    (hchron : ∀ t ∈ tuples, IsChronologicalNatTuple t)
    (hbound : ∀ t ∈ tuples, ∀ i, t i < H) :
    Function.Injective
      (naturalShortWitness (gap := gap) hchron hbound) := by
  intro t u htu
  apply Subtype.ext
  funext a
  calc
    t.1 a =
        ((naturalShortWitness hchron hbound t).2.2.1 a).1 :=
      (naturalShortWitness_tuple_val hchron hbound t a).symm
    _ = ((naturalShortWitness hchron hbound u).2.2.1 a).1 := by
      rw [htu]
    _ = u.1 a :=
      naturalShortWitness_tuple_val hchron hbound u a

theorem card_chronologicalShortWitness_le (r H gap : ℕ) :
    Fintype.card (ChronologicalShortWitness r H gap) ≤
      r * r * (gap * H ^ (r - 1)) := by
  calc
    Fintype.card (ChronologicalShortWitness r H gap) =
        ∑ i : Fin r, ∑ j : Fin r,
          Fintype.card
            (ChronologicalShortPair (L := H) gap i j) := by
      simp [ChronologicalShortWitness]
    _ ≤ ∑ _i : Fin r, ∑ _j : Fin r,
        gap * H ^ (r - 1) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact card_chronologicalShortPair_le gap i j
    _ = _ := by
      simp [mul_assoc]

/-- Every short chronological tuple is injectively encoded by a short
pair and the remaining `r - 1` coordinates. -/
theorem card_shortNatTupleFamily_le_of_bounded
    {r H gap : ℕ} {tuples : Finset (Fin r → ℕ)}
    (hchron : ∀ t ∈ tuples, IsChronologicalNatTuple t)
    (hbound : ∀ t ∈ tuples, ∀ i, t i < H) :
    (shortNatTupleFamily gap tuples).card ≤
      r * r * (gap * H ^ (r - 1)) := by
  calc
    (shortNatTupleFamily gap tuples).card =
        Fintype.card
          (NaturalShortMember (gap := gap) tuples) := by
      simpa only using!
        (Fintype.card_coe
          (shortNatTupleFamily gap tuples)).symm
    _ ≤ Fintype.card
        (ChronologicalShortWitness r H gap) :=
      Fintype.card_le_of_injective _
        (naturalShortWitness_injective hchron hbound)
    _ ≤ _ := card_chronologicalShortWitness_le r H gap

/-! ## Application to logarithmic annular boxes -/

/-- One more than the rounded depth corresponding to the terminal time
endpoint `1`. -/
def annularDepthAmbientSize (N : ℕ) : ℕ :=
  gaussLogDepthEndpoint N 1 + 1

/-- Its real size is asymptotic to `log N / gaussRoofMean`. -/
theorem tendsto_annularDepthAmbientSize_div_log :
    Tendsto
      (fun N ↦ (annularDepthAmbientSize N : ℝ) /
        Real.log (N : ℝ))
      atTop (nhds (1 / gaussRoofMean)) := by
  have hmain :=
    tendsto_natCeil_const_mul_scale_div
      (fun N : ℕ ↦ Real.log (N : ℝ))
      tendsto_log_natCast_atTop
      (show (0 : ℝ) ≤ 1 by norm_num)
      gaussRoofMean_pos
  have hone : Tendsto
      (fun N : ℕ ↦ (1 : ℝ) / Real.log (N : ℝ))
      atTop (nhds 0) :=
    (tendsto_const_nhds : Tendsto
      (fun _N : ℕ ↦ (1 : ℝ)) atTop (nhds 1)).div_atTop
        tendsto_log_natCast_atTop
  have hsum := hmain.add hone
  have hsum' : Tendsto
      (fun N : ℕ ↦
        (⌈(1 : ℝ) * Real.log (N : ℝ) / gaussRoofMean⌉₊ : ℝ) /
            Real.log (N : ℝ) +
          1 / Real.log (N : ℝ))
      atTop (nhds (1 / gaussRoofMean)) := by
    simpa only [add_zero] using! hsum
  apply hsum'.congr'
  filter_upwards
    [tendsto_log_natCast_atTop.eventually_gt_atTop 0] with N hlog
  unfold annularDepthAmbientSize gaussLogDepthEndpoint
  push_cast
  field_simp [ne_of_gt hlog]

/-- The elementary logarithmic ratio along natural numbers tends to
zero. -/
theorem tendsto_log_natCast_div_natCast_zero :
    Tendsto
      (fun N : ℕ ↦ Real.log (N : ℝ) / (N : ℝ))
      atTop (nhds 0) := by
  have hreal :
      Tendsto (fun x : ℝ ↦ Real.log x / x) atTop (nhds 0) := by
    have h :=
      (isLittleO_log_rpow_atTop
        (r := (1 : ℝ)) zero_lt_one).tendsto_div_nhds_zero
    simpa only [Real.rpow_one] using! h
  exact hreal.comp tendsto_natCast_atTop_atTop

/-- Therefore the common logarithmic depth bound is `o(N)`. -/
theorem tendsto_annularDepthAmbientSize_div_natCast_zero :
    Tendsto
      (fun N : ℕ ↦ (annularDepthAmbientSize N : ℝ) / (N : ℝ))
      atTop (nhds 0) := by
  have hmul :=
    tendsto_annularDepthAmbientSize_div_log.mul
      tendsto_log_natCast_div_natCast_zero
  have hmul' : Tendsto
      (fun N : ℕ ↦
        (annularDepthAmbientSize N : ℝ) / Real.log (N : ℝ) *
          (Real.log (N : ℝ) / (N : ℝ)))
      atTop (nhds 0) := by
    simpa only [mul_zero] using! hmul
  apply hmul'.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hlog : Real.log (N : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast hN))
  field_simp [hlog]

/-- In particular every logarithmic depth in the interior annular boxes
lies inside the literal finite depth range for all sufficiently large
`N`. -/
theorem eventually_annularDepthAmbientSize_le_nat :
    ∀ᶠ N : ℕ in atTop, annularDepthAmbientSize N ≤ N := by
  have hlt : ∀ᶠ N : ℕ in atTop,
      (annularDepthAmbientSize N : ℝ) / (N : ℝ) < 1 :=
    tendsto_annularDepthAmbientSize_div_natCast_zero.eventually
      (show {x : ℝ | x < 1} ∈ nhds 0 by
        exact Iio_mem_nhds zero_lt_one)
  filter_upwards [hlt, eventually_ge_atTop 1] with N hratio hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
  have hreal : (annularDepthAmbientSize N : ℝ) < (N : ℝ) :=
    (div_lt_one hNpos).mp hratio
  have hnat : annularDepthAmbientSize N < N := by
    exact_mod_cast hreal
  exact hnat.le

/-- Every member of a nonterminal annular time box is below the common
ambient logarithmic depth bound. -/
theorem annularOccurrenceParityDepthBox_lt_ambient
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (htime : ∀ i : AnnularGridIndex grid,
      0 < k i → i.time.1 < grid)
    {N : ℕ} (hN : 1 < N)
    (z : GaussPrefixMixedOccurrence k) (q : ℕ)
    (hq : q ∈ annularOccurrenceParityDepthBox N k z) :
    q < annularDepthAmbientSize N := by
  have hlog : 0 < Real.log (N : ℝ) := by
    apply Real.log_pos
    exact_mod_cast hN
  have hqUpper :
      q < annularTimeDepthUpper N grid z.1 := by
    have hq' :
        (annularTimeDepthLower N grid z.1 ≤ q ∧
            q < annularTimeDepthUpper N grid z.1) ∧
          q % 2 = (annularGridDepthParity z.1).1 := by
      simpa only [annularOccurrenceParityDepthBox,
        annularTimeParityDepthBox, parityIco, Finset.mem_filter,
        Finset.mem_Ico] using! hq
    exact hq'.1.2
  have hzactive : 0 < k z.1 := by
    have hz := z.2.isLt
    omega
  have hindex : z.1.time.1 + 1 ≤ grid :=
    Nat.succ_le_iff.mpr (htime z.1 hzactive)
  have htimeUpper :
      intervalGridPoint 0 1 grid (z.1.time.1 + 1) ≤ 1 :=
    (intervalGridPoint_mem_Icc zero_le_one hgrid hindex).2
  have hrounded :
      annularTimeDepthUpper N grid z.1 ≤
        gaussLogDepthEndpoint N 1 := by
    apply Nat.ceil_mono
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right htimeUpper hlog.le)
      gaussRoofMean_pos.le
  unfold annularDepthAmbientSize
  omega

/-- Injective and noninjective parts of the labeled annular box. -/
def injectiveAnnularOccurrenceAssignmentBox
    (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ) :
    Finset (GaussPrefixMixedOccurrence k → ℕ) :=
  (annularOccurrenceAssignmentBox N k).filter Function.Injective

def noninjectiveAnnularOccurrenceAssignmentBox
    (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ) :
    Finset (GaussPrefixMixedOccurrence k → ℕ) :=
  (annularOccurrenceAssignmentBox N k).filter
    (fun f ↦ ¬ Function.Injective f)

/-- The normalized collision count vanishes at every positive mixed
factorial order. -/
theorem tendsto_noninjectiveAnnularOccurrenceAssignmentBox_density_zero
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i : AnnularGridIndex grid,
      0 < k i → i.time.1 < grid) :
    Tendsto
      (fun N ↦
        ((noninjectiveAnnularOccurrenceAssignmentBox N k).card : ℝ) /
          (Real.log (N : ℝ)) ^ MixedOccurrenceCount k)
      atTop (nhds 0) := by
  let r := MixedOccurrenceCount k
  let H : ℕ → ℕ := annularDepthAmbientSize
  let upper : ℕ → ℝ := fun N ↦
    ((r * r : ℕ) : ℝ) *
      ((H N : ℝ) / Real.log (N : ℝ)) ^ (r - 1) *
        (1 / Real.log (N : ℝ))
  have hH :=
    tendsto_annularDepthAmbientSize_div_log
  have hrecip : Tendsto
      (fun N : ℕ ↦ (1 : ℝ) / Real.log (N : ℝ))
      atTop (nhds 0) :=
    (tendsto_const_nhds : Tendsto
      (fun _N : ℕ ↦ (1 : ℝ)) atTop (nhds 1)).div_atTop
        tendsto_log_natCast_atTop
  have hupper : Tendsto upper atTop (nhds 0) := by
    have hraw :=
      ((tendsto_const_nhds : Tendsto
        (fun _N : ℕ ↦ ((r * r : ℕ) : ℝ))
          atTop (nhds ((r * r : ℕ) : ℝ))).mul
        (hH.pow (r - 1))).mul hrecip
    simpa only [upper, mul_zero] using! hraw
  apply squeeze_zero'
  · exact Eventually.of_forall fun N ↦ by positivity
  · filter_upwards
      [eventually_ge_atTop 2,
        tendsto_log_natCast_atTop.eventually_gt_atTop 0] with N hN hlog
    have hcardNat :
        (noninjectiveAnnularOccurrenceAssignmentBox N k).card ≤
          r * r * H N ^ (r - 1) := by
      let boxes : GaussPrefixMixedOccurrence k → Finset ℕ :=
        annularOccurrenceParityDepthBox N k
      have hbound : ∀ z q, q ∈ boxes z →
          q < annularDepthAmbientSize N :=
        fun z q hq ↦
          annularOccurrenceParityDepthBox_lt_ambient
            hgrid k htime hN z q hq
      have hgeneric :=
        card_filter_not_injective_piFinset_le
          (σ := GaussPrefixMixedOccurrence k)
          (boxes := boxes)
          (H := annularDepthAmbientSize N) hbound
      calc
        (noninjectiveAnnularOccurrenceAssignmentBox N k).card =
            ((Fintype.piFinset boxes).filter
              (fun f ↦ ¬ Function.Injective f)).card := by
          congr 1
        _ ≤ Fintype.card (GaussPrefixMixedOccurrence k) *
              Fintype.card (GaussPrefixMixedOccurrence k) *
                annularDepthAmbientSize N ^
                  (Fintype.card (GaussPrefixMixedOccurrence k) - 1) :=
          hgeneric
        _ = r * r * H N ^ (r - 1) := rfl
    have hcardReal :
        ((noninjectiveAnnularOccurrenceAssignmentBox N k).card : ℝ) ≤
          ((r * r * H N ^ (r - 1) : ℕ) : ℝ) := by
      exact Nat.cast_le.mpr hcardNat
    have hdiv := div_le_div_of_nonneg_right hcardReal
      (pow_nonneg hlog.le r)
    calc
      ((noninjectiveAnnularOccurrenceAssignmentBox N k).card : ℝ) /
          Real.log (N : ℝ) ^ r ≤
        ((r * r * H N ^ (r - 1) : ℕ) : ℝ) /
          Real.log (N : ℝ) ^ r := hdiv
      _ = upper N := by
        dsimp only [upper, H, r]
        rw [show MixedOccurrenceCount k =
          (MixedOccurrenceCount k - 1) + 1 by omega, pow_succ]
        push_cast
        rw [div_pow]
        field_simp [ne_of_gt hlog]
  · exact hupper

/-- Removing collisions preserves the product density. -/
theorem tendsto_injectiveAnnularOccurrenceAssignmentBox_density
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i : AnnularGridIndex grid,
      0 < k i → i.time.1 < grid) :
    Tendsto
      (fun N ↦
        ((injectiveAnnularOccurrenceAssignmentBox N k).card : ℝ) /
          (Real.log (N : ℝ)) ^ MixedOccurrenceCount k)
      atTop (nhds (annularOccurrenceTimeDensity k)) := by
  have hall :=
    tendsto_annularOccurrenceAssignmentBox_card_div_log_pow
      hgrid k htime
  have hbad :=
    tendsto_noninjectiveAnnularOccurrenceAssignmentBox_density_zero
      hgrid k hr htime
  have hsub := hall.sub hbad
  have hsub' : Tendsto
      (fun N ↦
        ((annularOccurrenceAssignmentBox N k).card : ℝ) /
            (Real.log (N : ℝ)) ^ MixedOccurrenceCount k -
          ((noninjectiveAnnularOccurrenceAssignmentBox N k).card : ℝ) /
            (Real.log (N : ℝ)) ^ MixedOccurrenceCount k)
      atTop (nhds (annularOccurrenceTimeDensity k)) := by
    simpa only [sub_zero] using! hsub
  apply hsub'.congr'
  filter_upwards
    [tendsto_log_natCast_atTop.eventually_gt_atTop 0] with N hlog
  have hcard :=
    Finset.card_filter_add_card_filter_not
      (s := annularOccurrenceAssignmentBox N k)
      (p := Function.Injective)
  have hcardReal :
      ((injectiveAnnularOccurrenceAssignmentBox N k).card : ℝ) +
          ((noninjectiveAnnularOccurrenceAssignmentBox N k).card : ℝ) =
        ((annularOccurrenceAssignmentBox N k).card : ℝ) := by
    exact_mod_cast hcard
  unfold injectiveAnnularOccurrenceAssignmentBox
    noninjectiveAnnularOccurrenceAssignmentBox at hcardReal ⊢
  rw [← hcardReal]
  ring

/-! ## Exact sum over canonical chronological orders -/

/-- Globally injective mixed tuples satisfying all labeled annular
time-box and parity restrictions.  The restriction is expressed through
the tuple's canonical order so that its fibers are literally the families
used by the analytic argument. -/
def eligibleAnnularGloballyInjectiveMixedTuples
    (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ) :
    Finset (GloballyInjectiveMixedDepthTuple N k) := by
  classical
  exact Finset.univ.filter fun F ↦
    ∀ j,
      fixedOrderMixedTimes N k
          (canonicalMixedOccurrenceOrder N k F) F j ∈
        annularOccurrenceDepthBoxes N k
          (canonicalMixedOccurrenceOrder N k F j) ∧
      fixedOrderMixedTimes N k
          (canonicalMixedOccurrenceOrder N k F) F j % 2 =
        (annularOccurrenceParity k
          (canonicalMixedOccurrenceOrder N k F j)).1

/-- Total number of chronological tuples across all canonical occurrence
orders.  The order remains tagged in this sum; two different label orders
are never identified merely because their sorted natural-valued vectors
coincide. -/
def totalCanonicalAnnularGridTupleCard
    (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ) : ℕ :=
  ∑ e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k,
    (canonicalAnnularGridTupleFamily N k e).card

/-- Each eligible globally injective tuple belongs to exactly one
canonical-order summand. -/
theorem totalCanonicalAnnularGridTupleCard_eq_eligible_card
    (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ) :
    totalCanonicalAnnularGridTupleCard N k =
      (eligibleAnnularGloballyInjectiveMixedTuples N k).card := by
  classical
  let order :
      GloballyInjectiveMixedDepthTuple N k →
        (Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k) :=
    canonicalMixedOccurrenceOrder N k
  have hfiber :
      (eligibleAnnularGloballyInjectiveMixedTuples N k).card =
        ∑ e :
            Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k,
          ((eligibleAnnularGloballyInjectiveMixedTuples N k).filter
            (fun F ↦ order F = e)).card := by
    have hraw := Finset.card_eq_sum_card_fiberwise
      (s := eligibleAnnularGloballyInjectiveMixedTuples N k)
      (t := (Finset.univ :
        Finset (Fin (MixedOccurrenceCount k) ≃
          GaussPrefixMixedOccurrence k)))
      (f := order) (by
        intro F _hF
        change order F ∈ (Finset.univ :
          Finset (Fin (MixedOccurrenceCount k) ≃
            GaussPrefixMixedOccurrence k))
        simp)
    simpa only [Finset.sum_filter, Finset.sum_const_zero,
      Finset.sum_add_distrib, Finset.mem_univ, if_true,
      Finset.filter_filter, and_self] using! hraw
  rw [hfiber]
  unfold totalCanonicalAnnularGridTupleCard
  apply Finset.sum_congr rfl
  intro e _he
  unfold canonicalAnnularGridTupleFamily
  rw [card_canonicalMixedOrderParityBoxTimes]
  congr 1
  ext F
  simp only [eligibleAnnularGloballyInjectiveMixedTuples,
    canonicalMixedOrderClass, Finset.mem_filter, Finset.mem_univ,
    true_and, order]
  constructor
  · rintro ⟨horder, hbox⟩
    refine ⟨?_, horder⟩
    simpa only [horder] using! hbox
  · rintro ⟨hbox, horder⟩
    refine ⟨horder, ?_⟩
    simpa only [horder] using! hbox

/-! ## Exact eligible-tuple/assignment bijection -/

abbrev EligibleAnnularTupleSubtype
    (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ) :=
  {F // F ∈ eligibleAnnularGloballyInjectiveMixedTuples N k}

abbrev InjectiveAnnularAssignmentSubtype
    (N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ) :=
  {f // f ∈ injectiveAnnularOccurrenceAssignmentBox N k}

/-- Forget the embedding wrappers in one eligible globally injective
mixed tuple. -/
noncomputable def eligibleAnnularDepthAssignment
    (N : ℕ) {grid : ℕ} (k : AnnularGridIndex grid → ℕ)
    (F : EligibleAnnularTupleSubtype N k) :
    InjectiveAnnularAssignmentSubtype N k := by
  let f : GaussPrefixMixedOccurrence k → ℕ :=
    fun z ↦ (F.1.1 z.1 z.2 : ℕ)
  refine ⟨f, ?_⟩
  apply Finset.mem_filter.mpr
  constructor
  · apply Fintype.mem_piFinset.mpr
    intro z
    have hEligible := (Finset.mem_filter.mp F.2).2
    let e := canonicalMixedOccurrenceOrder N k F.1
    let j : Fin (MixedOccurrenceCount k) := e.symm z
    have hj := hEligible j
    have hej : e j = z := e.apply_symm_apply z
    have hdepth :
        fixedOrderMixedTimes N k e F.1 j = f z := by
      change (F.1.1 (e j).1 (e j).2 : ℕ) =
        (F.1.1 z.1 z.2 : ℕ)
      rw [hej]
    have hbox :
        f z ∈ annularOccurrenceDepthBoxes N k z := by
      rw [← hdepth, ← hej]
      exact hj.1
    have hparity :
        f z % 2 = (annularOccurrenceParity k z).1 := by
      rw [← hdepth, ← hej]
      exact hj.2
    simpa only [annularOccurrenceParityDepthBox,
      annularTimeParityDepthBox, parityIco, Finset.mem_filter,
      annularOccurrenceDepthBoxes, annularOccurrenceParity] using!
        And.intro hbox hparity
  · exact F.1.2

theorem eligibleAnnularDepthAssignment_injective
    (N : ℕ) {grid : ℕ} (k : AnnularGridIndex grid → ℕ) :
    Function.Injective (eligibleAnnularDepthAssignment N k) := by
  intro F G hFG
  apply Subtype.ext
  apply Subtype.ext
  funext i
  apply Function.Embedding.ext
  intro j
  apply Subtype.ext
  have h :=
    congrFun (congrArg Subtype.val hFG)
      (⟨i, j⟩ : GaussPrefixMixedOccurrence k)
  exact h

/-- Reconstruct all labelwise embeddings from an injective assignment,
provided every selected depth is at most the literal cutoff. -/
noncomputable def globallyInjectiveTupleOfAnnularAssignment
    (N : ℕ) {grid : ℕ} (k : AnnularGridIndex grid → ℕ)
    (G : InjectiveAnnularAssignmentSubtype N k)
    (hbound : ∀ z, G.1 z ≤ N) :
    GloballyInjectiveMixedDepthTuple N k := by
  let F : GaussPrefixMixedDepthTuple N k := fun i ↦
    { toFun := fun j ↦ ⟨G.1 ⟨i, j⟩, by
        simp only [Finset.mem_Icc]
        exact ⟨Nat.zero_le _, hbound ⟨i, j⟩⟩⟩
      inj' := by
        intro a b hab
        have hGinj := (Finset.mem_filter.mp G.2).2
        have hsigma :
            (⟨i, a⟩ : GaussPrefixMixedOccurrence k) = ⟨i, b⟩ :=
          hGinj (congrArg Subtype.val hab)
        exact ((Sigma.mk.inj_iff.mp hsigma).2).eq }
  refine ⟨F, ?_⟩
  intro z z' hzz
  have hGinj := (Finset.mem_filter.mp G.2).2
  exact hGinj hzz

theorem globallyInjectiveTupleOfAnnularAssignment_depth
    (N : ℕ) {grid : ℕ} (k : AnnularGridIndex grid → ℕ)
    (G : InjectiveAnnularAssignmentSubtype N k)
    (hbound : ∀ z, G.1 z ≤ N)
    (z : GaussPrefixMixedOccurrence k) :
    ((globallyInjectiveTupleOfAnnularAssignment
        N k G hbound).1 z.1 z.2 : ℕ) = G.1 z := by
  rfl

theorem globallyInjectiveTupleOfAnnularAssignment_eligible
    (N : ℕ) {grid : ℕ} (k : AnnularGridIndex grid → ℕ)
    (G : InjectiveAnnularAssignmentSubtype N k)
    (hbound : ∀ z, G.1 z ≤ N) :
    globallyInjectiveTupleOfAnnularAssignment N k G hbound ∈
      eligibleAnnularGloballyInjectiveMixedTuples N k := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  intro j
  let F :=
    globallyInjectiveTupleOfAnnularAssignment N k G hbound
  let e := canonicalMixedOccurrenceOrder N k F
  have hmemAll :
      ∀ z, G.1 z ∈ annularOccurrenceParityDepthBox N k z :=
    Fintype.mem_piFinset.mp (Finset.mem_filter.mp G.2).1
  have hz := hmemAll (e j)
  have hz' :
      G.1 (e j) ∈ annularOccurrenceDepthBoxes N k (e j) ∧
        G.1 (e j) % 2 =
          (annularOccurrenceParity k (e j)).1 := by
    simpa only [annularOccurrenceParityDepthBox,
      annularTimeParityDepthBox, parityIco, Finset.mem_filter,
      annularOccurrenceDepthBoxes, annularOccurrenceParity] using! hz
  simpa only [fixedOrderMixedTimes,
    globallyInjectiveTupleOfAnnularAssignment_depth] using! hz'

theorem eligibleAnnularDepthAssignment_surjective_of_bound
    (N : ℕ) {grid : ℕ} (k : AnnularGridIndex grid → ℕ)
    (hbound : ∀ z q,
      q ∈ annularOccurrenceParityDepthBox N k z → q ≤ N) :
    Function.Surjective (eligibleAnnularDepthAssignment N k) := by
  intro G
  have hGall :
      ∀ z, G.1 z ∈ annularOccurrenceParityDepthBox N k z :=
    Fintype.mem_piFinset.mp (Finset.mem_filter.mp G.2).1
  have hGN : ∀ z, G.1 z ≤ N :=
    fun z ↦ hbound z (G.1 z) (hGall z)
  let F := globallyInjectiveTupleOfAnnularAssignment N k G hGN
  have hFelig :
      F ∈ eligibleAnnularGloballyInjectiveMixedTuples N k :=
    globallyInjectiveTupleOfAnnularAssignment_eligible N k G hGN
  refine ⟨⟨F, hFelig⟩, ?_⟩
  apply Subtype.ext
  funext z
  exact globallyInjectiveTupleOfAnnularAssignment_depth N k G hGN z

/-- Exact cardinal equality once every logarithmic box lies below `N`. -/
theorem eligible_card_eq_injective_card_of_bound
    (N : ℕ) {grid : ℕ} (k : AnnularGridIndex grid → ℕ)
    (hbound : ∀ z q,
      q ∈ annularOccurrenceParityDepthBox N k z → q ≤ N) :
    (eligibleAnnularGloballyInjectiveMixedTuples N k).card =
      (injectiveAnnularOccurrenceAssignmentBox N k).card := by
  rw [← Fintype.card_coe, ← Fintype.card_coe]
  exact Fintype.card_congr (Equiv.ofBijective
    (eligibleAnnularDepthAssignment N k)
    ⟨eligibleAnnularDepthAssignment_injective N k,
      eligibleAnnularDepthAssignment_surjective_of_bound N k hbound⟩)

/-- The exact total density across all tagged canonical chronological
orders. -/
theorem tendsto_totalCanonicalAnnularGridTupleCard_density
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i : AnnularGridIndex grid,
      0 < k i → i.time.1 < grid) :
    Tendsto
      (fun N ↦ (totalCanonicalAnnularGridTupleCard N k : ℝ) /
        (Real.log (N : ℝ)) ^ MixedOccurrenceCount k)
      atTop (nhds (annularOccurrenceTimeDensity k)) := by
  have hinjective :=
    tendsto_injectiveAnnularOccurrenceAssignmentBox_density
      hgrid k hr htime
  apply hinjective.congr'
  filter_upwards
    [eventually_ge_atTop 2,
      eventually_annularDepthAmbientSize_le_nat] with N hN hambient
  have hbound : ∀ z q,
      q ∈ annularOccurrenceParityDepthBox N k z → q ≤ N := by
    intro z q hq
    exact (annularOccurrenceParityDepthBox_lt_ambient
      hgrid k htime hN z q hq).le.trans hambient
  rw [totalCanonicalAnnularGridTupleCard_eq_eligible_card,
    eligible_card_eq_injective_card_of_bound N k hbound]

/-! ## Short-gap density across all canonical orders -/

/-- Every coordinate of a chronological annular tuple lies in the common
logarithmic ambient depth range. -/
theorem canonicalAnnularGridTupleFamily_lt_ambient
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (htime : ∀ i : AnnularGridIndex grid,
      0 < k i → i.time.1 < grid)
    {N : ℕ} (hN : 1 < N)
    (e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k)
    (t : Fin (MixedOccurrenceCount k) → ℕ)
    (ht : t ∈ canonicalAnnularGridTupleFamily N k e)
    (j : Fin (MixedOccurrenceCount k)) :
    t j < annularDepthAmbientSize N := by
  rcases mem_canonicalMixedOrderParityBoxTimes_iff.mp ht with
    ⟨F, _horder, hbox, hFt⟩
  have hmem :
      t j ∈ annularOccurrenceParityDepthBox N k (e j) := by
    have hj := hbox j
    rw [← hFt]
    simpa only [annularOccurrenceParityDepthBox,
      annularTimeParityDepthBox, parityIco, Finset.mem_filter,
      annularOccurrenceDepthBoxes, annularOccurrenceParity] using! hj
  exact annularOccurrenceParityDepthBox_lt_ambient
    hgrid k htime hN (e j) (t j) hmem

/-- Total number of tuples with at least one short chronological gap,
summed over all tagged canonical label orders. -/
def totalShortCanonicalAnnularGridTupleCard
    (gap N : ℕ) {grid : ℕ}
    (k : AnnularGridIndex grid → ℕ) : ℕ :=
  ∑ e : Fin (MixedOccurrenceCount k) ≃ GaussPrefixMixedOccurrence k,
    (shortNatTupleFamily gap
      (canonicalAnnularGridTupleFamily N k e)).card

/-- Literal `gap · H^(r-1)` bound for the total short family.  The
constant is exactly the number of canonical label orders times the
reversible short-pair code size. -/
theorem totalShortCanonicalAnnularGridTupleCard_le
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (htime : ∀ i : AnnularGridIndex grid,
      0 < k i → i.time.1 < grid)
    {N : ℕ} (hN : 1 < N) (gap : ℕ) :
    totalShortCanonicalAnnularGridTupleCard gap N k ≤
      Fintype.card
          (Fin (MixedOccurrenceCount k) ≃
            GaussPrefixMixedOccurrence k) *
        (MixedOccurrenceCount k * MixedOccurrenceCount k *
          (gap *
            annularDepthAmbientSize N ^
              (MixedOccurrenceCount k - 1))) := by
  unfold totalShortCanonicalAnnularGridTupleCard
  calc
    ∑ e : Fin (MixedOccurrenceCount k) ≃
          GaussPrefixMixedOccurrence k,
        (shortNatTupleFamily gap
          (canonicalAnnularGridTupleFamily N k e)).card ≤
      ∑ _e : Fin (MixedOccurrenceCount k) ≃
          GaussPrefixMixedOccurrence k,
        MixedOccurrenceCount k * MixedOccurrenceCount k *
          (gap *
            annularDepthAmbientSize N ^
              (MixedOccurrenceCount k - 1)) := by
        apply Finset.sum_le_sum
        intro e he
        exact card_shortNatTupleFamily_le_of_bounded
          (fun t ht ↦
            canonicalAnnularGridTupleFamily_chronological
              N k e t ht)
          (fun t ht j ↦
            canonicalAnnularGridTupleFamily_lt_ambient
              hgrid k htime hN e t ht j)
    _ = _ := by
      simp

/-- Any separation scale that is `o(log N)` makes the total short-gap
family negligible after the `r`th logarithmic normalization. -/
theorem tendsto_totalShortCanonicalAnnularGridTupleCard_density_zero
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i : AnnularGridIndex grid,
      0 < k i → i.time.1 < grid)
    (gap : ℕ → ℕ)
    (hgapRatio : Tendsto
      (fun N ↦ (gap N : ℝ) / Real.log (N : ℝ))
      atTop (nhds 0)) :
    Tendsto
      (fun N ↦
        (totalShortCanonicalAnnularGridTupleCard
          (gap N) N k : ℝ) /
            Real.log (N : ℝ) ^ MixedOccurrenceCount k)
      atTop (nhds 0) := by
  let r := MixedOccurrenceCount k
  let H : ℕ → ℕ := annularDepthAmbientSize
  let C : ℕ :=
    Fintype.card
      (Fin (MixedOccurrenceCount k) ≃
        GaussPrefixMixedOccurrence k) * r * r
  let upper : ℕ → ℝ := fun N ↦
    (C : ℝ) *
      ((gap N : ℝ) / Real.log (N : ℝ)) *
      (((H N : ℝ) / Real.log (N : ℝ)) ^ (r - 1))
  have hupper : Tendsto upper atTop (nhds 0) := by
    have hraw :=
      ((tendsto_const_nhds : Tendsto
        (fun _N : ℕ ↦ (C : ℝ)) atTop (nhds (C : ℝ))).mul
          hgapRatio).mul
        (tendsto_annularDepthAmbientSize_div_log.pow (r - 1))
    simpa only [upper, H, mul_zero, zero_mul] using! hraw
  apply squeeze_zero'
  · exact Eventually.of_forall fun N ↦ by positivity
  · filter_upwards
      [eventually_ge_atTop 2,
        tendsto_log_natCast_atTop.eventually_gt_atTop 0] with
      N hN hlog
    have hcardNat :=
      totalShortCanonicalAnnularGridTupleCard_le
        hgrid k htime hN (gap N)
    have hcardReal :
        (totalShortCanonicalAnnularGridTupleCard
            (gap N) N k : ℝ) ≤
          (C : ℝ) * (gap N : ℝ) *
            (H N : ℝ) ^ (r - 1) := by
      have hcast :
          (totalShortCanonicalAnnularGridTupleCard
              (gap N) N k : ℝ) ≤
            ((Fintype.card
                (Fin (MixedOccurrenceCount k) ≃
                  GaussPrefixMixedOccurrence k) *
              (MixedOccurrenceCount k * MixedOccurrenceCount k *
                (gap N *
                  annularDepthAmbientSize N ^
                    (MixedOccurrenceCount k - 1))) : ℕ) : ℝ) :=
        Nat.cast_le.mpr hcardNat
      simpa only [C, H, r, Nat.cast_mul, Nat.cast_pow,
        mul_assoc] using! hcast
    have hdiv := div_le_div_of_nonneg_right hcardReal
      (pow_nonneg hlog.le r)
    calc
      (totalShortCanonicalAnnularGridTupleCard
          (gap N) N k : ℝ) /
          Real.log (N : ℝ) ^ r ≤
        ((C : ℝ) * (gap N : ℝ) *
            (H N : ℝ) ^ (r - 1)) /
          Real.log (N : ℝ) ^ r := hdiv
      _ = upper N := by
        have hpow :
            Real.log (N : ℝ) ^ r =
              Real.log (N : ℝ) ^ (r - 1) *
                Real.log (N : ℝ) := by
          conv_lhs => rw [show r = (r - 1) + 1 by omega]
          exact pow_succ _ _
        dsimp only [upper]
        rw [hpow, div_pow]
        field_simp [ne_of_gt hlog]
  · exact hupper

/-- The common annular depth horizon itself diverges. -/
theorem tendsto_annularDepthAmbientSize_atTop :
    Tendsto annularDepthAmbientSize atTop atTop := by
  have hcore :
      Tendsto (fun N : ℕ ↦ gaussLogDepthEndpoint N 1)
        atTop atTop := by
    unfold gaussLogDepthEndpoint
    apply tendsto_nat_ceil_atTop.comp
    simpa only [one_mul] using!
      tendsto_log_natCast_atTop.atTop_div_const
        gaussRoofMean_pos
  exact Filter.tendsto_atTop_mono
    (fun N ↦ Nat.le_add_right
      (gaussLogDepthEndpoint N 1) 1) hcore

/-- Explicit separation gap: the square root of the logarithmic ambient
depth horizon. -/
def annularSeparationGap (N : ℕ) : ℕ :=
  Nat.sqrt (annularDepthAmbientSize N)

theorem tendsto_annularSeparationGap_atTop :
    Tendsto annularSeparationGap atTop atTop :=
  tendsto_natSqrt_atTop.comp
    tendsto_annularDepthAmbientSize_atTop

theorem tendsto_annularSeparationGap_div_log_zero :
    Tendsto
      (fun N ↦ (annularSeparationGap N : ℝ) /
        Real.log (N : ℝ))
      atTop (nhds 0) := by
  have hratio :=
    tendsto_natSqrt_div_self_zero.comp
      tendsto_annularDepthAmbientSize_atTop
  have hmul :=
    hratio.mul tendsto_annularDepthAmbientSize_div_log
  have hmul' : Tendsto
      (fun N ↦
        ((Nat.sqrt (annularDepthAmbientSize N) : ℝ) /
            (annularDepthAmbientSize N : ℝ)) *
          ((annularDepthAmbientSize N : ℝ) /
            Real.log (N : ℝ)))
      atTop (nhds 0) := by
    simpa only [zero_mul] using! hmul
  apply hmul'.congr'
  filter_upwards
    [tendsto_log_natCast_atTop.eventually_gt_atTop 0] with N hlog
  unfold annularSeparationGap
  have hH : (annularDepthAmbientSize N : ℝ) ≠ 0 := by
    exact_mod_cast (show annularDepthAmbientSize N ≠ 0 by
      unfold annularDepthAmbientSize
      omega)
  field_simp [hH, ne_of_gt hlog]

/-- Fully explicit short-density theorem used by the annular
factorial-moment assembly. -/
theorem
    tendsto_totalShortCanonicalAnnularGridTupleCard_sqrt_density_zero
    {grid : ℕ} (hgrid : 0 < grid)
    (k : AnnularGridIndex grid → ℕ)
    (hr : 0 < MixedOccurrenceCount k)
    (htime : ∀ i : AnnularGridIndex grid,
      0 < k i → i.time.1 < grid) :
    Tendsto
      (fun N ↦
        (totalShortCanonicalAnnularGridTupleCard
          (annularSeparationGap N) N k : ℝ) /
            Real.log (N : ℝ) ^ MixedOccurrenceCount k)
      atTop (nhds 0) :=
  tendsto_totalShortCanonicalAnnularGridTupleCard_density_zero
    hgrid k hr htime annularSeparationGap
      tendsto_annularSeparationGap_div_log_zero

end

end Erdos1002
