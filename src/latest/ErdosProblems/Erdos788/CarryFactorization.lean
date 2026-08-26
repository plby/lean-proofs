import ErdosProblems.Erdos788.UpperGraph
import ErdosProblems.Erdos788.FiniteCounting

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The base-`p` carry lift

This file transfers a finite-field sum palette to an ordinary integer sum
palette.  We use little-endian, fixed-length base-`p` words.  Once the
coordinatewise residue of a raw digit sum is fixed, its ordinary value is
determined by one overflow bit in each coordinate.
-/

namespace Erdos788

open Finset

/-- The ordinary sum graph on the interval `[0, N)`. -/
def intSumGraph (N : ℕ) (B : Finset ℕ) : SimpleGraph (Fin N) :=
  SimpleGraph.fromRel fun x y ↦ x.val + y.val ∈ B

@[simp]
theorem intSumGraph_adj {N : ℕ} {B : Finset ℕ} {x y : Fin N} :
    (intSumGraph N B).Adj x y ↔ x ≠ y ∧ x.val + y.val ∈ B := by
  simp [intSumGraph, add_comm]

/-- A fixed-length word of base-`p` digits. -/
abbrev DigitWord (p k : ℕ) := Fin k → Fin p

/-- Interpret an arbitrary length-`k` natural word in base `p`. -/
def rawWordValue (p : ℕ) {k : ℕ} (d : Fin k → ℕ) : ℕ :=
  Nat.ofDigits p (List.ofFn d)

/-- Interpret a bounded digit word in base `p`. -/
def digitWordValue (p k : ℕ) (w : DigitWord p k) : ℕ :=
  rawWordValue p fun i ↦ (w i).val

theorem digitWordValue_lt_pow {p k : ℕ} (hp : 1 < p) (w : DigitWord p k) :
    digitWordValue p k w < p ^ k := by
  have h := Nat.ofDigits_lt_base_pow_length hp (l := List.ofFn fun i ↦ (w i).val)
    (by
      intro d hd
      simp only [List.mem_ofFn] at hd
      obtain ⟨i, rfl⟩ := hd
      exact (w i).isLt)
  simpa [digitWordValue, rawWordValue] using! h

/-- The value map, with its range proof bundled into `Fin (p^k)`. -/
def digitWordToFin {p k : ℕ} (hp : 1 < p) : DigitWord p k → Fin (p ^ k) :=
  fun w ↦ ⟨digitWordValue p k w, digitWordValue_lt_pow hp w⟩

theorem digitWordToFin_injective {p k : ℕ} (hp : 1 < p) :
    Function.Injective (digitWordToFin (k := k) hp) := by
  intro a b hab
  have hvalue : digitWordValue p k a = digitWordValue p k b :=
    congrArg Fin.val hab
  have hlists : List.ofFn (fun i ↦ (a i).val) =
      List.ofFn (fun i ↦ (b i).val) := by
    apply Nat.ofDigits_inj_of_len_eq hp (by simp)
    · intro d hd
      simp only [List.mem_ofFn] at hd
      obtain ⟨i, rfl⟩ := hd
      exact (a i).isLt
    · intro d hd
      simp only [List.mem_ofFn] at hd
      obtain ⟨i, rfl⟩ := hd
      exact (b i).isLt
    · exact hvalue
  have hfun : (fun i ↦ (a i).val) = fun i ↦ (b i).val :=
    List.ofFn_injective hlists
  funext i
  exact Fin.ext (congrFun hfun i)

theorem digitWordToFin_bijective {p k : ℕ} (hp : 1 < p) :
    Function.Bijective (digitWordToFin (k := k) hp) := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨digitWordToFin_injective hp, ?_⟩
  simp [DigitWord]

/-- Fixed-length base-`p` expansion as an equivalence. -/
noncomputable def digitWordEquiv {p k : ℕ} (hp : 1 < p) :
    DigitWord p k ≃ Fin (p ^ k) :=
  Equiv.ofBijective (digitWordToFin (k := k) hp) (digitWordToFin_bijective hp)

@[simp]
theorem digitWordEquiv_apply_val {p k : ℕ} (hp : 1 < p) (w : DigitWord p k) :
    (digitWordEquiv hp w).val = digitWordValue p k w :=
  rfl

@[simp]
theorem digitWordEquiv_symm_value {p k : ℕ} (hp : 1 < p) (x : Fin (p ^ k)) :
    digitWordValue p k ((digitWordEquiv hp).symm x) = x.val := by
  change (digitWordEquiv hp ((digitWordEquiv hp).symm x)).val = x.val
  exact congrArg Fin.val ((digitWordEquiv hp).apply_symm_apply x)

/-- Send a bounded natural digit to its residue class, coordinatewise. -/
def wordResidue (p k : ℕ) (w : DigitWord p k) : FFVec p k :=
  fun i ↦ ((w i).val : ZMod p)

theorem wordResidue_injective {p k : ℕ} :
    Function.Injective (wordResidue p k) := by
  intro a b hab
  funext i
  apply Fin.ext
  have hi := congrFun hab i
  have hval := congrArg ZMod.val hi
  simpa [wordResidue, ZMod.val_natCast_of_lt (a i).isLt,
    ZMod.val_natCast_of_lt (b i).isLt] using! hval

/-- The residue-vector labeling of the integer interval `[0,p^k)`. -/
noncomputable def integerResidue {p k : ℕ} (hp : 1 < p) :
    Fin (p ^ k) → FFVec p k :=
  fun x ↦ wordResidue p k ((digitWordEquiv hp).symm x)

theorem integerResidue_injective {p k : ℕ} (hp : 1 < p) :
    Function.Injective (integerResidue (k := k) hp) :=
  (wordResidue_injective (p := p) (k := k)).comp (digitWordEquiv hp).symm.injective

/-- Pairs of digit words having a prescribed coordinatewise residue sum. -/
def ResiduePair (p k : ℕ) (s : FFVec p k) :=
  {q : DigitWord p k × DigitWord p k //
    wordResidue p k q.1 + wordResidue p k q.2 = s}

noncomputable instance residuePairFintype (p k : ℕ) (s : FFVec p k) :
    Fintype (ResiduePair p k s) :=
  Fintype.ofInjective (fun q : ResiduePair p k s ↦ q.val) Subtype.val_injective

/-- The ordinary value of a pair of digit words. -/
def residuePairValue {p k : ℕ} {s : FFVec p k} (q : ResiduePair p k s) : ℕ :=
  digitWordValue p k q.val.1 + digitWordValue p k q.val.2

/-- All ordinary sums arising above one fixed residue vector. -/
noncomputable def residueSumFibre (p k : ℕ) (s : FFVec p k) : Finset ℕ :=
  Finset.univ.image (residuePairValue : ResiduePair p k s → ℕ)

/-- The raw overflow bit at one coordinate. -/
def rawOverflow {p k : ℕ} {s : FFVec p k} (q : ResiduePair p k s)
    (i : Fin k) : Bool :=
  Bool.ofNat (((q.val.1 i).val + (q.val.2 i).val) / p)

/-- Recover an ordinary raw digit word from a residue vector and overflow bits. -/
def decodeRawSum (p : ℕ) {k : ℕ} (s : FFVec p k) (c : Fin k → Bool) : ℕ :=
  rawWordValue p fun i ↦ (s i).val + p * (c i).toNat

theorem digitWordValue_add {p k : ℕ} (a b : DigitWord p k) :
    digitWordValue p k a + digitWordValue p k b =
      rawWordValue p (fun i ↦ (a i).val + (b i).val) := by
  unfold digitWordValue rawWordValue
  rw [Nat.ofDigits_add_ofDigits_eq_ofDigits_zipWith_of_length_eq (by simp)]
  congr 1
  apply List.ext_get (by simp)
  intro n h₁ h₂
  simp

theorem rawOverflow_toNat {p k : ℕ} (hp : 1 < p) {s : FFVec p k}
    (q : ResiduePair p k s) (i : Fin k) :
    (rawOverflow q i).toNat = ((q.val.1 i).val + (q.val.2 i).val) / p := by
  have hq : ((q.val.1 i).val + (q.val.2 i).val) / p ≤ 1 :=
    one_bit_raw_carry (p := p) (Nat.zero_lt_of_lt hp)
    (q.val.1 i).isLt (q.val.2 i).isLt
  have hcases : ((q.val.1 i).val + (q.val.2 i).val) / p = 0 ∨
      ((q.val.1 i).val + (q.val.2 i).val) / p = 1 :=
    Nat.le_one_iff_eq_zero_or_eq_one.mp hq
  rcases hcases with hzero | hone
  · simp [rawOverflow, hzero]
  · simp [rawOverflow, hone]

theorem residuePair_raw_digit {p k : ℕ} (hp : 1 < p) {s : FFVec p k}
    (q : ResiduePair p k s) (i : Fin k) :
    (q.val.1 i).val + (q.val.2 i).val =
      (s i).val + p * (rawOverflow q i).toNat := by
  have hres : (((q.val.1 i).val + (q.val.2 i).val : ℕ) : ZMod p) = s i := by
    rw [Nat.cast_add]
    simpa [wordResidue, Pi.add_apply] using! congrFun q.property i
  have hmod : ((q.val.1 i).val + (q.val.2 i).val) % p = (s i).val := by
    calc
      ((q.val.1 i).val + (q.val.2 i).val) % p =
          ((((q.val.1 i).val + (q.val.2 i).val : ℕ) : ZMod p)).val := by
            rw [ZMod.val_natCast]
      _ = (s i).val := congrArg ZMod.val hres
  rw [← Nat.mod_add_div ((q.val.1 i).val + (q.val.2 i).val) p,
    hmod, rawOverflow_toNat hp q i]

theorem residuePairValue_factor {p k : ℕ} (hp : 1 < p) {s : FFVec p k}
    (q : ResiduePair p k s) :
    residuePairValue q = decodeRawSum p s (rawOverflow q) := by
  rw [residuePairValue, digitWordValue_add]
  unfold decodeRawSum
  congr 2
  funext i
  exact residuePair_raw_digit hp q i

theorem residueSumFibre_card_le {p k : ℕ} (hp : 1 < p) (s : FFVec p k) :
    (residueSumFibre p k s).card ≤ 2 ^ k := by
  classical
  exact carry_description_bound k
    (residuePairValue : ResiduePair p k s → ℕ)
    (rawOverflow : ResiduePair p k s → Fin k → Bool)
    (decodeRawSum p s) (residuePairValue_factor hp)

/-- The integer palette obtained by taking every ordinary sum above `S`. -/
noncomputable def carryPalette (p k : ℕ) (S : Finset (FFVec p k)) : Finset ℕ :=
  S.biUnion (residueSumFibre p k)

theorem carryPalette_card_le {p k : ℕ} (hp : 1 < p) (S : Finset (FFVec p k)) :
    (carryPalette p k S).card ≤ 2 ^ k * S.card := by
  classical
  calc
    (carryPalette p k S).card ≤ S.card * 2 ^ k :=
      Finset.card_biUnion_le_card_mul S (residueSumFibre p k) (2 ^ k)
        (fun s _ ↦ residueSumFibre_card_le hp s)
    _ = 2 ^ k * S.card := Nat.mul_comm _ _

theorem carryPalette_subset_range {p k : ℕ} (hp : 1 < p)
    (S : Finset (FFVec p k)) :
    carryPalette p k S ⊆ Finset.range (2 * p ^ k - 1) := by
  classical
  intro z hz
  rcases Finset.mem_biUnion.mp hz with ⟨s, hs, hzs⟩
  rw [residueSumFibre] at hzs
  rcases Finset.mem_image.mp hzs with ⟨q, _hq, rfl⟩
  rw [Finset.mem_range]
  change digitWordValue p k q.val.1 + digitWordValue p k q.val.2 < 2 * p ^ k - 1
  have ha := digitWordValue_lt_pow hp q.val.1
  have hb := digitWordValue_lt_pow hp q.val.2
  have hpow : 0 < p ^ k := Nat.pow_pos (by omega)
  omega

theorem digitWord_sum_mem_carryPalette {p k : ℕ} (S : Finset (FFVec p k))
    (a b : DigitWord p k)
    (hab : wordResidue p k a + wordResidue p k b ∈ S) :
    digitWordValue p k a + digitWordValue p k b ∈ carryPalette p k S := by
  classical
  apply Finset.mem_biUnion.mpr
  refine ⟨wordResidue p k a + wordResidue p k b, hab, ?_⟩
  rw [residueSumFibre]
  apply Finset.mem_image.mpr
  let q : ResiduePair p k (wordResidue p k a + wordResidue p k b) :=
    ⟨(a, b), rfl⟩
  exact ⟨q, Finset.mem_univ q, rfl⟩

theorem integer_sum_mem_carryPalette {p k : ℕ} (hp : 1 < p)
    (S : Finset (FFVec p k)) (x y : Fin (p ^ k))
    (hxy : integerResidue hp x + integerResidue hp y ∈ S) :
    x.val + y.val ∈ carryPalette p k S := by
  have hmem := digitWord_sum_mem_carryPalette S
    ((digitWordEquiv hp).symm x) ((digitWordEquiv hp).symm y) hxy
  simpa [integerResidue] using! hmem

/-- Exact carry lift from a group sum palette to an integer sum palette. -/
theorem carry_lift (p k : ℕ) (hp : 1 < p) (S : Finset (FFVec p k)) :
    ∃ B : Finset ℕ,
      B ⊆ Finset.range (2 * p ^ k - 1) ∧
      B.card ≤ 2 ^ k * S.card ∧
      (intSumGraph (p ^ k) B).indepNum ≤ (groupSumGraph S).indepNum := by
  classical
  letI : NeZero p := ⟨by omega⟩
  refine ⟨carryPalette p k S, carryPalette_subset_range hp S,
    carryPalette_card_le hp S, ?_⟩
  obtain ⟨A, hA⟩ :=
    (intSumGraph (p ^ k) (carryPalette p k S)).exists_isNIndepSet_indepNum
  let C : Finset (FFVec p k) := A.image (integerResidue hp)
  have hCind : (groupSumGraph S).IsIndepSet (C : Set (FFVec p k)) := by
    intro u hu v hv huv hadj
    change u ∈ C at hu
    change v ∈ C at hv
    rcases Finset.mem_image.mp hu with ⟨x, hx, rfl⟩
    rcases Finset.mem_image.mp hv with ⟨y, hy, rfl⟩
    have hxy : x ≠ y := by
      intro h
      exact huv (congrArg (integerResidue hp) h)
    have hsum : integerResidue hp x + integerResidue hp y ∈ S :=
      (groupSumGraph_adj.mp hadj).2
    have hB := integer_sum_mem_carryPalette hp S x y hsum
    exact hA.isIndepSet hx hy hxy (intSumGraph_adj.mpr ⟨hxy, hB⟩)
  calc
    (intSumGraph (p ^ k) (carryPalette p k S)).indepNum = A.card :=
      hA.card_eq.symm
    _ = C.card := by
      symm
      exact Finset.card_image_of_injective A (integerResidue_injective hp)
    _ ≤ (groupSumGraph S).indepNum := hCind.card_le_indepNum

end Erdos788
