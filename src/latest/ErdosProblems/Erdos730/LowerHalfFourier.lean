/- leanprover/lean4:v4.33.0  mathlib db584cd6 (master, the commit the v4.33.0 tag is cut from) -/
import ErdosProblems.Erdos730.DigitBoxes
import ErdosProblems.Erdos730.FixedDepthFourier

/-!
# Erdős 730: the concrete lower-half box on the Fourier surface

`Erdos730DigitBoxes` constructs the permitted residues from fixed-length
base-`p` digit lists, while `Erdos730FixedDepthFourier` factors Fourier
coefficients over dependent digit tuples.  This file proves that these are
literally the same finite set and transfers the sharp interval-box `L¹`
estimate to the concrete lower-half residue box used by the event ledger.
-/

namespace Erdos730.LowerHalfFourier

open DigitBoxes FixedDepthFourier
open scoped ZMod

noncomputable section

/-- Every coordinate uses the consecutive permitted interval
`{0, ..., (p+1)/2-1}`. -/
def lowerHalfDigitIntervals (p d : ℕ) : Fin d → Finset ℕ :=
  fun _ ↦ Finset.range (halfDigitCount p)

/-- Natural base-`p` value of a dependent tuple of permitted digits. -/
def lowerHalfTupleValue {p d : ℕ}
    (x : DigitTuple (lowerHalfDigitIntervals p d)) : ℕ :=
  Nat.ofDigits p (List.ofFn fun i : Fin d ↦ (x i : ℕ))

/-- The tuple presentation of the permitted residue box. -/
def lowerHalfTupleResidues (p d : ℕ) : Finset (ZMod (p ^ d)) :=
  (Finset.univ : Finset (DigitTuple (lowerHalfDigitIntervals p d))).image
    fun x ↦ (lowerHalfTupleValue x : ZMod (p ^ d))

theorem lowerHalfTuple_list_mem_fixedLengthDigits
    {p d : ℕ} (hp : 3 ≤ p)
    (x : DigitTuple (lowerHalfDigitIntervals p d)) :
    List.ofFn (fun i : Fin d ↦ (x i : ℕ)) ∈
      List.fixedLengthDigits (one_lt_halfDigitCount hp) d := by
  rw [List.mem_fixedLengthDigits_iff (one_lt_halfDigitCount hp)]
  refine ⟨List.length_ofFn, ?_⟩
  intro a ha
  rw [List.mem_ofFn'] at ha
  rcases ha with ⟨i, rfl⟩
  exact Finset.mem_range.mp (x i).property

theorem lowerHalfTupleValue_eq_ofDigits
    {p d : ℕ} (x : DigitTuple (lowerHalfDigitIntervals p d)) :
    lowerHalfTupleValue x =
      Nat.ofDigits p (List.ofFn fun i : Fin d ↦ (x i : ℕ)) := by
  rfl

theorem lowerHalfTupleValue_lt_pow
    {p d : ℕ} (hp : 3 ≤ p)
    (x : DigitTuple (lowerHalfDigitIntervals p d)) :
    lowerHalfTupleValue x < p ^ d := by
  rw [lowerHalfTupleValue_eq_ofDigits]
  have hmem := lowerHalfTuple_list_mem_fixedLengthDigits hp x
  have hdigits := (List.mem_fixedLengthDigits_iff
    (one_lt_halfDigitCount hp)).mp hmem
  have hlt := Nat.ofDigits_lt_base_pow_length (by omega) fun a ha ↦
    (hdigits.2 a ha).trans_le (halfDigitCount_le (by omega))
  simpa [lowerHalfTupleValue, hdigits.1] using hlt

theorem lowerHalfTupleResidues_subset (p d : ℕ) (hp : 3 ≤ p) :
    lowerHalfTupleResidues p d ⊆ lowerHalfResidues p d := by
  intro z hz
  rw [lowerHalfTupleResidues, Finset.mem_image] at hz
  rcases hz with ⟨x, _hx, rfl⟩
  rw [lowerHalfResidues, Finset.mem_image]
  refine ⟨lowerHalfTupleValue x, ?_, rfl⟩
  rw [lowerHalfResiduesNat, dif_pos (one_lt_halfDigitCount hp),
    Finset.mem_image]
  refine ⟨List.ofFn (fun i : Fin d ↦ (x i : ℕ)),
    lowerHalfTuple_list_mem_fixedLengthDigits hp x, ?_⟩
  exact (lowerHalfTupleValue_eq_ofDigits x).symm

theorem lowerHalfTupleResidueMap_injective
    {p d : ℕ} (hp : 3 ≤ p) :
    Function.Injective
      (fun x : DigitTuple (lowerHalfDigitIntervals p d) ↦
        (lowerHalfTupleValue x : ZMod (p ^ d))) := by
  intro x y hxy
  have hxlt := lowerHalfTupleValue_lt_pow hp x
  have hylt := lowerHalfTupleValue_lt_pow hp y
  have hval := congrArg ZMod.val hxy
  have hnat : lowerHalfTupleValue x = lowerHalfTupleValue y := by
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt hxlt,
      Nat.mod_eq_of_lt hylt] using hval
  have hlist : List.ofFn (fun i : Fin d ↦ (x i : ℕ)) =
      List.ofFn (fun i : Fin d ↦ (y i : ℕ)) := by
    apply Nat.ofDigits_inj_of_len_eq (by omega : 1 < p)
      (by simp)
    · intro a ha
      have hmem := lowerHalfTuple_list_mem_fixedLengthDigits hp x
      exact ((List.mem_fixedLengthDigits_iff
        (one_lt_halfDigitCount hp)).mp hmem).2 a ha |>.trans_le
          (halfDigitCount_le (by omega))
    · intro a ha
      have hmem := lowerHalfTuple_list_mem_fixedLengthDigits hp y
      exact ((List.mem_fixedLengthDigits_iff
        (one_lt_halfDigitCount hp)).mp hmem).2 a ha |>.trans_le
          (halfDigitCount_le (by omega))
    · simpa only [← lowerHalfTupleValue_eq_ofDigits] using hnat
  have hfun : (fun i : Fin d ↦ (x i : ℕ)) =
      fun i : Fin d ↦ (y i : ℕ) := List.ofFn_injective hlist
  funext i
  exact Subtype.ext (congrFun hfun i)

theorem lowerHalfTupleResidues_card
    {p d : ℕ} (hp : 3 ≤ p) :
    (lowerHalfTupleResidues p d).card = halfDigitCount p ^ d := by
  rw [lowerHalfTupleResidues,
    Finset.card_image_iff.mpr (lowerHalfTupleResidueMap_injective hp).injOn,
    Finset.card_univ]
  change Fintype.card
      ((i : Fin d) → (lowerHalfDigitIntervals p d i)) =
    halfDigitCount p ^ d
  rw [Fintype.card_pi]
  simp only [Fintype.card_coe]
  simp [lowerHalfDigitIntervals]

/-- The list-based and tuple-based presentations are exactly equal. -/
theorem lowerHalfTupleResidues_eq_lowerHalfResidues
    {p d : ℕ} (hp : 3 ≤ p) :
    lowerHalfTupleResidues p d = lowerHalfResidues p d := by
  apply Finset.eq_of_subset_of_card_le (lowerHalfTupleResidues_subset p d hp)
  rw [lowerHalfResidues_card hp, lowerHalfTupleResidues_card hp]

/-! ## Transfer to the tuple Fourier transform -/

theorem lowerHalfDigitIntervals_isInterval
    {p d : ℕ} (hp : 3 ≤ p) :
    IsIntervalDigitBox p (lowerHalfDigitIntervals p d) := by
  intro i
  refine ⟨0, halfDigitCount p, ?_, halfDigitCount_le (by omega)⟩
  change Finset.range (halfDigitCount p) =
    Finset.Ico 0 (0 + halfDigitCount p)
  rw [Nat.zero_add, Finset.range_eq_Ico]

theorem lowerHalfTupleValue_cast_eq_sum
    {p d : ℕ} (x : DigitTuple (lowerHalfDigitIntervals p d)) :
    (lowerHalfTupleValue x : ZMod (p ^ d)) =
      ∑ i : Fin d,
        (((x i : ℕ) * p ^ (i : ℕ) : ℕ) : ZMod (p ^ d)) := by
  simp only [lowerHalfTupleValue, Nat.ofDigits_eq_sum_mapIdx,
    List.mapIdx_eq_ofFn, List.get_ofFn, List.length_ofFn,
    Fin.val_cast, List.sum_ofFn, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  congr 3

theorem dft_finsetIndicator_eq_phaseSum
    {Q : ℕ} [NeZero Q] (A : Finset (ZMod Q)) (h : ZMod Q) :
    ZMod.dft (finsetIndicator A) h =
      ∑ z ∈ A, ZMod.stdAddChar (-(z * h)) := by
  rw [ZMod.dft_apply]
  simp [finsetIndicator]

theorem lowerHalfTuple_phase_eq
    {p d : ℕ} [NeZero (p ^ d)] (h : ZMod (p ^ d))
    (x : DigitTuple (lowerHalfDigitIntervals p d)) :
    ZMod.stdAddChar
        (-((lowerHalfTupleValue x : ZMod (p ^ d)) * h)) =
      ZMod.stdAddChar
        (∑ i : Fin d,
          digitPhase (lowerHalfDigitIntervals p d) h i (x i)) := by
  congr 1
  rw [lowerHalfTupleValue_cast_eq_sum]
  simp only [digitPhase, Nat.cast_mul, Nat.cast_pow]
  rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-- The DFT of the concrete lower-half indicator is exactly the product
coefficient used by the digitwise Fourier induction. -/
theorem dft_lowerHalfResidues_eq_digitBoxFourierCoeff
    {p d : ℕ} [NeZero (p ^ d)] (hp : 3 ≤ p) (h : ZMod (p ^ d)) :
    ZMod.dft (finsetIndicator (lowerHalfResidues p d)) h =
      digitBoxFourierCoeff (lowerHalfDigitIntervals p d) h := by
  rw [← lowerHalfTupleResidues_eq_lowerHalfResidues hp,
    dft_finsetIndicator_eq_phaseSum, lowerHalfTupleResidues]
  rw [Finset.sum_image (lowerHalfTupleResidueMap_injective hp).injOn]
  simp only [digitBoxFourierCoeff]
  apply Finset.sum_congr rfl
  intro x _hx
  exact lowerHalfTuple_phase_eq h x

/-- Sharp concrete `L¹` estimate for the Fourier transform of the permitted
lower-half digit box. -/
theorem dft_lowerHalfResidues_l1_le
    {p d : ℕ} [NeZero (p ^ d)] (hp : 3 ≤ p) :
    (∑ h : ZMod (p ^ d),
      ‖ZMod.dft (finsetIndicator (lowerHalfResidues p d)) h‖) ≤
      (p : ℝ) ^ d * (3 + Real.log p) ^ d := by
  letI : NeZero p := ⟨by omega⟩
  simp_rw [dft_lowerHalfResidues_eq_digitBoxFourierCoeff hp]
  exact digitBoxFourierCoeff_interval_l1_le (by omega)
    (lowerHalfDigitIntervals p d) (lowerHalfDigitIntervals_isInterval hp)

#print axioms lowerHalfTupleResidues_eq_lowerHalfResidues
#print axioms dft_lowerHalfResidues_eq_digitBoxFourierCoeff
#print axioms dft_lowerHalfResidues_l1_le

end

end Erdos730.LowerHalfFourier
