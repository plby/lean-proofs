/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.GAPBuilders
import ErdosProblems.Erdos186.CFP.SProper

/-!
# The Bilu--Freiman small-doubling interface

This file records the exact finite statement used as Lemma 2.18 in
Conlon--Fox--Pham.  Its mathematical input is the combination of Theorems
1.2 and 1.3 of Bilu's exposition of Freiman's theorem.

For positive integers `s` and `d` and a positive real `delta`, the result
says that there is a constant `C` such that every nonempty finite set of
integers `A` satisfying

`|A + A| <= 2 ^ (d + 1 - delta) * |A|`

has its double sumset in an `s`-proper GAP `P`.  The volume of `P` is at
most `C * |A + A|`, and the first `d` displayed directions of `P` carry at
least a `1 / C` proportion of its volume.

The convention that `A` is nonempty is logically necessary.  Every GAP in
the finite API has positive volume, whereas the double sumset of the empty
set is empty.  The theorem is normally stated in the literature under the
standard additive-combinatorics convention that the finite set is nonempty.

The deep uniform existence assertion is isolated as `BiluFreimanStatement`.
The rest of this file is unconditional: it defines first-coordinate
truncation and the integer carrier, proves their basic laws, packages the
precise conclusion, proves that the conclusion is impossible for the empty
set, and verifies the complete singleton case.  No result in this file
assumes `BiluFreimanStatement`.
-/

namespace Erdos186

open scoped BigOperators

namespace GAP

variable {ambient rank : ℕ}

/-! ## The first displayed directions of a GAP -/

/-- The GAP obtained by retaining the first `d` displayed directions.

The offset is unchanged.  Its rank is definitionally `min rank d`, which is
the precise meaning of "dimension at most `d` corresponding to the first
`d` dimensions" in CFP Lemma 2.18.
-/
def firstDimensions (P : GAP ambient rank) (d : ℕ) : GAP ambient (min rank d) where
  offset := P.offset
  steps := fun i ↦ P.steps ⟨i, i.isLt.trans_le (min_le_left rank d)⟩
  widths := fun i ↦ P.widths ⟨i, i.isLt.trans_le (min_le_left rank d)⟩
  width_pos := fun i ↦ P.width_pos ⟨i, i.isLt.trans_le (min_le_left rank d)⟩

@[simp]
theorem firstDimensions_offset (P : GAP ambient rank) (d : ℕ) :
    (P.firstDimensions d).offset = P.offset := rfl

@[simp]
theorem firstDimensions_steps (P : GAP ambient rank) (d : ℕ)
    (i : Fin (min rank d)) :
    (P.firstDimensions d).steps i =
      P.steps ⟨i, i.isLt.trans_le (min_le_left rank d)⟩ := rfl

@[simp]
theorem firstDimensions_widths (P : GAP ambient rank) (d : ℕ)
    (i : Fin (min rank d)) :
    (P.firstDimensions d).widths i =
      P.widths ⟨i, i.isLt.trans_le (min_le_left rank d)⟩ := rfl

/-- The volume of the first directions is the corresponding prefix product. -/
theorem volume_firstDimensions (P : GAP ambient rank) (d : ℕ) :
    (P.firstDimensions d).volume =
      ∏ i : Fin (min rank d),
        P.widths ⟨i, i.isLt.trans_le (min_le_left rank d)⟩ := rfl

/-- Index of a direction occurring after the first `d` displayed
directions. -/
def remainingIndex (rank d : ℕ) (i : Fin (rank - min rank d)) : Fin rank :=
  Fin.cast (Nat.add_sub_of_le (min_le_left rank d))
    (Fin.natAdd (min rank d) i)

@[simp]
theorem remainingIndex_val (rank d : ℕ) (i : Fin (rank - min rank d)) :
    (remainingIndex rank d i : ℕ) = min rank d + i := rfl

/-- The complementary tail of a GAP after its first `d` directions.

The offset is zero, so adding a prefix point and a tail point has the
original offset exactly once.
-/
def remainingDimensions (P : GAP ambient rank) (d : ℕ) :
    GAP ambient (rank - min rank d) where
  offset := 0
  steps := fun i ↦ P.steps (remainingIndex rank d i)
  widths := fun i ↦ P.widths (remainingIndex rank d i)
  width_pos := fun i ↦ P.width_pos (remainingIndex rank d i)

@[simp]
theorem remainingDimensions_offset (P : GAP ambient rank) (d : ℕ) :
    (P.remainingDimensions d).offset = 0 := rfl

@[simp]
theorem remainingDimensions_steps (P : GAP ambient rank) (d : ℕ)
    (i : Fin (rank - min rank d)) :
    (P.remainingDimensions d).steps i = P.steps (remainingIndex rank d i) := rfl

@[simp]
theorem remainingDimensions_widths (P : GAP ambient rank) (d : ℕ)
    (i : Fin (rank - min rank d)) :
    (P.remainingDimensions d).widths i = P.widths (remainingIndex rank d i) := rfl

/-- The displayed volume factors exactly into the first directions and the
complementary tail. -/
theorem volume_eq_firstDimensions_mul_remainingDimensions
    (P : GAP ambient rank) (d : ℕ) :
    P.volume =
      (P.firstDimensions d).volume * (P.remainingDimensions d).volume := by
  have hkl : min rank d + (rank - min rank d) = rank :=
    Nat.add_sub_of_le (min_le_left rank d)
  have hprod := Fin.prod_univ_add
    (fun i : Fin (min rank d + (rank - min rank d)) ↦
      P.widths (Fin.cast hkl i))
  rw [volume, volume, volume]
  calc
    (∏ i : Fin rank, P.widths i) =
        ∏ i : Fin (min rank d + (rank - min rank d)),
          P.widths (Fin.cast hkl i) :=
      (Fin.prod_congr' P.widths hkl).symm
    _ = (∏ i : Fin (min rank d),
          P.widths (Fin.cast hkl (Fin.castAdd (rank - min rank d) i))) *
        ∏ i : Fin (rank - min rank d),
          P.widths (Fin.cast hkl (Fin.natAdd (min rank d) i)) := hprod
    _ = (∏ i : Fin (min rank d),
          P.widths ⟨i, i.isLt.trans_le (min_le_left rank d)⟩) *
        ∏ i : Fin (rank - min rank d),
          P.widths (remainingIndex rank d i) := by
      rfl

/-- Every GAP in this API has positive displayed volume. -/
theorem volume_pos (P : GAP ambient rank) : 0 < P.volume := by
  rw [volume]
  exact Finset.prod_pos fun i _ ↦ P.width_pos i

/-- Dilation is multiplicative.  This exact presentation identity is the
coefficient-box bridge used to pass from a Freiman order `2s` container to
an `s`-proper container for the double sumset. -/
theorem dilate_dilate (P : GAP ambient rank) (a b : ℕ) :
    (P.dilate a).dilate b = P.dilate (b * a) := by
  rw [GAP.mk.injEq]
  refine ⟨?_, rfl, ?_⟩
  · funext j
    simp [GAP.dilate, mul_assoc]
  · funext i
    have hw : 1 ≤ P.widths i := P.width_pos i
    simp only [dilate_widths]
    have hsub : a * (P.widths i - 1) + 1 - 1 =
        a * (P.widths i - 1) := by omega
    rw [hsub]
    simp [mul_assoc]

/-- The sum of two displayed points belongs to the doubled GAP. -/
theorem add_mem_dilate_two (P : GAP ambient rank)
    {x y : LatticePoint ambient} (hx : x ∈ P.carrier)
    (hy : y ∈ P.carrier) : x + y ∈ (P.dilate 2).carrier := by
  rw [mem_carrier_iff] at hx hy ⊢
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  let c : (P.dilate 2).Coord := fun i ↦
    ⟨(a i : ℕ) + (b i : ℕ), by
      have ha := (a i).isLt
      have hb := (b i).isLt
      simp only [dilate_widths]
      omega⟩
  refine ⟨c, ?_⟩
  funext j
  simp only [coordPoint, dilate_offset, Pi.add_apply, c]
  push_cast
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]
  simp only [dilate_steps]
  ring

end GAP

namespace CFP.BiluFreiman

open GAPBuilders

/-! ## Finite integer sumsets and integer carriers -/

/-- The pointwise sumset of two finite integer sets. -/
def sumset (A B : Finset ℤ) : Finset ℤ :=
  A.biUnion fun a ↦ B.image fun b ↦ a + b

/-- The double sumset `A + A`, denoted `2A` in the papers. -/
def twoA (A : Finset ℤ) : Finset ℤ := sumset A A

@[simp]
theorem mem_sumset_iff {A B : Finset ℤ} {z : ℤ} :
    z ∈ sumset A B ↔ ∃ a ∈ A, ∃ b ∈ B, a + b = z := by
  classical
  simp only [sumset, Finset.mem_biUnion, Finset.mem_image]

@[simp]
theorem mem_twoA_iff {A : Finset ℤ} {z : ℤ} :
    z ∈ twoA A ↔ ∃ a ∈ A, ∃ b ∈ A, a + b = z :=
  mem_sumset_iff

@[simp]
theorem twoA_empty : twoA (∅ : Finset ℤ) = ∅ := by
  simp [twoA, sumset]

@[simp]
theorem twoA_singleton (a : ℤ) : twoA ({a} : Finset ℤ) = {a + a} := by
  classical
  ext z
  simp [mem_twoA_iff, eq_comm]

/-- Regard an integer as a point of the one-dimensional integer lattice. -/
def integerPoint (z : ℤ) : LatticePoint 1 := fun _ ↦ z

/-- Read the unique coordinate of a one-dimensional lattice point. -/
def pointInteger (x : LatticePoint 1) : ℤ := x 0

@[simp]
theorem pointInteger_integerPoint (z : ℤ) : pointInteger (integerPoint z) = z := rfl

@[simp]
theorem integerPoint_pointInteger (x : LatticePoint 1) :
    integerPoint (pointInteger x) = x := by
  funext i
  exact congrFun rfl 0 |>.trans (congrArg x (Subsingleton.elim 0 i))

/-- The carrier of a one-dimensional lattice GAP, read as a finite set of
ordinary integers. -/
def integerCarrier {r : ℕ} (P : GAP 1 r) : Finset ℤ :=
  P.carrier.image pointInteger

@[simp]
theorem mem_integerCarrier_iff {r : ℕ} {P : GAP 1 r} {z : ℤ} :
    z ∈ integerCarrier P ↔ integerPoint z ∈ P.carrier := by
  classical
  constructor
  · intro hz
    obtain ⟨x, hx, hxz⟩ := Finset.mem_image.mp hz
    have hzx : integerPoint z = x := by
      rw [← hxz, integerPoint_pointInteger]
    simpa [hzx] using hx
  · intro hz
    exact Finset.mem_image.mpr ⟨integerPoint z, hz, rfl⟩

/-- Passing between `ℤ` and the one-dimensional lattice preserves the
carrier cardinality. -/
@[simp]
theorem card_integerCarrier {r : ℕ} (P : GAP 1 r) :
    (integerCarrier P).card = P.carrier.card := by
  classical
  exact Finset.card_image_of_injective P.carrier fun x y h ↦ by
    rw [← integerPoint_pointInteger x, ← integerPoint_pointInteger y, h]

/-! ## Exact packaging of CFP Lemma 2.18 -/

/-- A witness for the conclusion of CFP Lemma 2.18 with natural-number
constant `C`.  The last inequality is the division-free form of
`|first d dimensions| ≥ C⁻¹ |P|`.
-/
structure Witness (s d C : ℕ) (A : Finset ℤ) where
  rank : ℕ
  rank_pos : 0 < rank
  progression : GAP 1 rank
  sProper : progression.SProper s
  twoA_subset : twoA A ⊆ integerCarrier progression
  volume_le : progression.volume ≤ C * (twoA A).card
  volume_le_mul_firstDimensions :
    progression.volume ≤ C * (progression.firstDimensions d).volume

namespace Witness

variable {s d C : ℕ} {A : Finset ℤ} (W : Witness s d C A)

/-- The prefix progression in the conclusion has rank at most `d`. -/
theorem firstDimensions_rank_le : min W.rank d ≤ d := min_le_right _ _

/-- The tail after the first `d` directions has uniformly bounded volume:
this is the rank/volume alternative in a directly usable form. -/
theorem remainingDimensions_volume_le :
    (W.progression.remainingDimensions d).volume ≤ C := by
  have hfactor := W.progression.volume_eq_firstDimensions_mul_remainingDimensions d
  have hmul :
      (W.progression.remainingDimensions d).volume *
          (W.progression.firstDimensions d).volume ≤
        C * (W.progression.firstDimensions d).volume := by
    simpa [hfactor, mul_comm] using W.volume_le_mul_firstDimensions
  exact Nat.le_of_mul_le_mul_right hmul
    (W.progression.firstDimensions d).volume_pos

/-- An `s`-proper witness is an ordinary proper GAP when `s` is positive. -/
theorem proper (hs : 0 < s) : W.progression.Proper :=
  GAP.SProper.proper W.sProper hs

/-- For positive `s`, the displayed volume is also the actual carrier
cardinality. -/
theorem card_integerCarrier_eq_volume (hs : 0 < s) :
    (integerCarrier W.progression).card = W.progression.volume := by
  rw [card_integerCarrier, W.progression.card_carrier_eq_volume (W.proper hs)]

end Witness

/-! ## Bridge from Bilu's sorted Freiman container -/

/-- The strong coefficient-box form of an `F_s` progression used in Bilu's
geometric proof: the `s`-fold coefficient dilation is proper.  This implies
the usual Freiman-isomorphism condition and is exactly what Bilu obtains by
injectivity on the enlarged convex body. -/
def IsFsProgression {r : ℕ} (P : GAP 1 r) (s : ℕ) : Prop :=
  (P.dilate s).Proper

/-- A source-faithful, sorted container output of Bilu Theorems 1.2--1.3.
`volumeConstant`, `tailBound`, and `rankBound` are uniform parameters; the
last two fields express the ordering of the displayed widths and the fact
that every direction after the first `d` has uniformly bounded width. -/
structure SortedFsContainer
    (s d volumeConstant tailBound rankBound : ℕ) (A : Finset ℤ) where
  rank : ℕ
  rank_pos : 0 < rank
  progression : GAP 1 rank
  fsProgression : IsFsProgression progression (2 * s)
  A_subset : A ⊆ integerCarrier progression
  volume_le : progression.volume ≤ volumeConstant * A.card
  rank_le : rank ≤ rankBound
  widths_sorted :
    ∀ i j : Fin rank, (i : ℕ) ≤ (j : ℕ) →
      progression.widths j ≤ progression.widths i
  tail_width_le :
    ∀ i : Fin rank, d ≤ (i : ℕ) → progression.widths i ≤ tailBound
  volumeConstant_pos : 0 < volumeConstant
  tailBound_pos : 0 < tailBound

namespace SortedFsContainer

variable {s d volumeConstant tailBound rankBound : ℕ} {A : Finset ℤ}
    (S : SortedFsContainer s d volumeConstant tailBound rankBound A)

/-- The GAP which contains the double sumset. -/
def doubled : GAP 1 S.rank := S.progression.dilate 2

/-- Its uniform witness constant.  The first term controls total volume;
the second controls the volume in directions after the first `d`. -/
def witnessConstant
    (_S : SortedFsContainer s d volumeConstant tailBound rankBound A) : ℕ :=
  max (3 ^ rankBound * volumeConstant) ((3 * tailBound) ^ rankBound)

theorem witnessConstant_pos : 0 < S.witnessConstant := by
  rw [witnessConstant]
  exact lt_of_lt_of_le
    (Nat.mul_pos (pow_pos (by omega : 0 < (3 : ℕ)) _) S.volumeConstant_pos)
    (le_max_left _ _)

/-- An `F_{2s}` progression becomes `s`-proper after doubling. -/
theorem dilate_two_sProper : S.doubled.SProper s := by
  apply S.doubled.sProper_of_dilate_proper s
  have h := S.fsProgression
  rw [IsFsProgression] at h
  simpa [doubled, GAP.dilate_dilate, mul_comm, mul_left_comm, mul_assoc] using h

/-- Every nonempty set injects into its own double sumset by translation by
one fixed element. -/
theorem card_le_twoA (hA : A.Nonempty) : A.card ≤ (twoA A).card := by
  classical
  obtain ⟨a₀, ha₀⟩ := hA
  let T : Finset ℤ := A.image fun a ↦ a + a₀
  have hTcard : T.card = A.card := by
    change (A.image fun a ↦ a + a₀).card = A.card
    exact Finset.card_image_of_injective A fun x y hxy ↦ add_right_cancel hxy
  have hTsub : T ⊆ twoA A := by
    intro z hz
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
    exact mem_twoA_iff.mpr ⟨a, ha, a₀, ha₀, rfl⟩
  rw [← hTcard]
  exact Finset.card_le_card hTsub

/-- The strict slack in the exponent used to invoke Bilu's source theorem.
Starting from the weak doubling inequality at exponent
`d + 1 - delta`, the intermediate exponent `d + 1 - delta / 2`
gives a strict inequality, as required in Bilu Theorem 1.2. -/
theorem doubling_lt_half_delta_slack {delta : ℝ}
    (hA : A.Nonempty) (hdelta : 0 < delta)
    (hdouble : ((twoA A).card : ℝ) ≤
      Real.rpow 2 ((d : ℝ) + 1 - delta) * (A.card : ℝ)) :
    ((twoA A).card : ℝ) <
      Real.rpow 2 ((d : ℝ) + 1 - delta / 2) * (A.card : ℝ) := by
  have hexponent : (d : ℝ) + 1 - delta < (d : ℝ) + 1 - delta / 2 := by
    linarith
  have hrpow :
      Real.rpow 2 ((d : ℝ) + 1 - delta) <
        Real.rpow 2 ((d : ℝ) + 1 - delta / 2) :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hexponent
  exact hdouble.trans_lt
    (mul_lt_mul_of_pos_right hrpow (by exact_mod_cast Finset.card_pos.mpr hA))

/-- The slack exponent still lies strictly below `d + 1`.  This is the
numerical input which makes Bilu Theorem 1.3 bound every sorted width after
the first `d` directions. -/
theorem half_delta_slack_lt_next_dimension {delta : ℝ}
    (hdelta : 0 < delta) :
    Real.rpow 2 ((d : ℝ) + 1 - delta / 2) <
      Real.rpow 2 ((d : ℝ) + 1) := by
  apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
  linarith

/-- The double sumset is contained in the doubled Bilu progression. -/
theorem twoA_subset_dilate_two :
    twoA A ⊆ integerCarrier S.doubled := by
  intro z hz
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_twoA_iff.mp hz
  have haP : integerPoint a ∈ S.progression.carrier :=
    mem_integerCarrier_iff.mp (S.A_subset ha)
  have hbP : integerPoint b ∈ S.progression.carrier :=
    mem_integerCarrier_iff.mp (S.A_subset hb)
  rw [mem_integerCarrier_iff]
  have hadd := S.progression.add_mem_dilate_two haP hbP
  have heq : integerPoint a + integerPoint b = integerPoint (a + b) := by
    funext i
    rfl
  change integerPoint (a + b) ∈ (S.progression.dilate 2).carrier
  rw [← heq]
  exact hadd

/-- Coarse total-volume bound for the doubled progression. -/
theorem doubled_volume_le (hA : A.Nonempty) :
    S.doubled.volume ≤ S.witnessConstant * (twoA A).card := by
  have hrpow : 3 ^ S.rank ≤ 3 ^ rankBound :=
    pow_le_pow_right' (by omega : 1 ≤ (3 : ℕ)) S.rank_le
  calc
    S.doubled.volume ≤ 3 ^ S.rank * S.progression.volume := by
      simpa [doubled] using S.progression.volume_dilate_le 2
    _ ≤ 3 ^ rankBound * S.progression.volume :=
      Nat.mul_le_mul_right S.progression.volume hrpow
    _ ≤ 3 ^ rankBound * (volumeConstant * A.card) :=
      Nat.mul_le_mul_left _ S.volume_le
    _ = (3 ^ rankBound * volumeConstant) * A.card := by ring
    _ ≤ (3 ^ rankBound * volumeConstant) * (twoA A).card :=
      Nat.mul_le_mul_left _ (card_le_twoA hA)
    _ ≤ S.witnessConstant * (twoA A).card :=
      Nat.mul_le_mul_right _ (le_max_left _ _)

/-- The volume in all directions after the first `d` is uniformly bounded
after doubling.  This is the precise conversion of Bilu's bounded sorted
tail widths into the prefix-volume inequality used by CFP. -/
theorem doubled_remainingDimensions_volume_le :
    (S.doubled.remainingDimensions d).volume ≤
      (3 * tailBound) ^ rankBound := by
  rw [GAP.volume]
  calc
    (∏ i : Fin (S.rank - min S.rank d),
        (S.doubled.remainingDimensions d).widths i) ≤
        ∏ _i : Fin (S.rank - min S.rank d), (3 * tailBound) := by
      apply Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _)
      intro i _hi
      rw [GAP.remainingDimensions_widths]
      have hdi : d ≤ (GAP.remainingIndex S.rank d i : ℕ) := by
        rw [GAP.remainingIndex_val]
        by_cases hdr : d ≤ S.rank
        · have hmin : min S.rank d = d := min_eq_right hdr
          omega
        · have hrd : S.rank ≤ d := Nat.le_of_not_ge hdr
          have hmin : min S.rank d = S.rank := min_eq_left hrd
          have hi := i.isLt
          omega
      calc
        S.doubled.widths (GAP.remainingIndex S.rank d i) ≤
            3 * S.progression.widths (GAP.remainingIndex S.rank d i) := by
          simpa [doubled] using
            S.progression.dilate_width_le 2 (GAP.remainingIndex S.rank d i)
        _ ≤ 3 * tailBound :=
          Nat.mul_le_mul_left 3 (S.tail_width_le _ hdi)
    _ = (3 * tailBound) ^ (S.rank - min S.rank d) := by simp
    _ ≤ (3 * tailBound) ^ rankBound := by
      apply pow_le_pow_right'
      · have := S.tailBound_pos
        omega
      · exact (Nat.sub_le _ _).trans S.rank_le

/-- The doubled container's total volume is controlled by its first `d`
displayed directions. -/
theorem doubled_volume_le_mul_firstDimensions :
    S.doubled.volume ≤
      S.witnessConstant * (S.doubled.firstDimensions d).volume := by
  have htail :
      (S.doubled.remainingDimensions d).volume ≤ S.witnessConstant :=
    S.doubled_remainingDimensions_volume_le.trans (le_max_right _ _)
  have hmul := Nat.mul_le_mul_left
    (S.doubled.firstDimensions d).volume htail
  rw [S.doubled.volume_eq_firstDimensions_mul_remainingDimensions d]
  simpa [mul_comm] using hmul

/-- Assemble the exact CFP witness from a sorted Bilu container. -/
theorem exists_witness_of_sorted_fsContainer (hA : A.Nonempty) :
    Nonempty (Witness s d S.witnessConstant A) := by
  exact ⟨
    { rank := S.rank
      rank_pos := S.rank_pos
      progression := S.doubled
      sProper := S.dilate_two_sProper
      twoA_subset := S.twoA_subset_dilate_two
      volume_le := S.doubled_volume_le hA
      volume_le_mul_firstDimensions :=
        S.doubled_volume_le_mul_firstDimensions }⟩

end SortedFsContainer

/-- The sole source-level target left by the bridge: the existence of a
uniform sorted `F_{2s}` container with linear volume, bounded rank, and
bounded widths after direction `d`.  Bilu Theorems 1.2--1.3 imply this
statement after choosing a doubling constant strictly between
`2^(d+1-delta)` and `2^(d+1)` and treating the bounded-cardinality cases.

No theorem in this file assumes this proposition implicitly. -/
def SortedFsContainerStatement : Prop :=
  ∀ s d : ℕ, 0 < s → 0 < d →
    ∀ delta : ℝ, 0 < delta →
      ∃ volumeConstant tailBound rankBound : ℕ,
        0 < volumeConstant ∧ 0 < tailBound ∧
        ∀ A : Finset ℤ, A.Nonempty →
          ((twoA A).card : ℝ) ≤
              Real.rpow 2 ((d : ℝ) + 1 - delta) * (A.card : ℝ) →
            Nonempty
              (SortedFsContainer s d volumeConstant tailBound rankBound A)

/-- The exact uniform Bilu--Freiman assertion used by CFP.

The constant is taken in `ℕ`, which is equivalent to the usual unspecified
positive real constant after enlarging it.  Nonemptiness is explicit for the
reason documented by `not_witness_empty` below.
-/
def BiluFreimanStatement : Prop :=
  ∀ s d : ℕ, 0 < s → 0 < d →
    ∀ delta : ℝ, 0 < delta →
      ∃ C : ℕ, 0 < C ∧
        ∀ A : Finset ℤ, A.Nonempty →
          ((twoA A).card : ℝ) ≤
              Real.rpow 2 ((d : ℝ) + 1 - delta) * (A.card : ℝ) →
            Nonempty (Witness s d C A)

/-- The complete, unconditional bridge from the source-level sorted
container theorem to the exact CFP Bilu--Freiman interface.  Thus the only
remaining mathematical input is `SortedFsContainerStatement` itself, i.e.
Bilu's Theorems 1.2--1.3 and their bounded-cardinality cleanup. -/
theorem biluFreimanStatement_of_sortedFsContainer
    (hsource : SortedFsContainerStatement) : BiluFreimanStatement := by
  intro s d hs hd delta hdelta
  obtain ⟨volumeConstant, tailBound, rankBound,
      hvolumeConstant, htailBound, hcontainers⟩ :=
    hsource s d hs hd delta hdelta
  let C : ℕ :=
    max (3 ^ rankBound * volumeConstant) ((3 * tailBound) ^ rankBound)
  have hC : 0 < C := by
    dsimp [C]
    exact lt_of_lt_of_le
      (Nat.mul_pos (pow_pos (by omega : 0 < (3 : ℕ)) _) hvolumeConstant)
      (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro A hA hdouble
  obtain ⟨S⟩ := hcontainers A hA hdouble
  simpa [C, SortedFsContainer.witnessConstant] using
    S.exists_witness_of_sorted_fsContainer hA

/-! ## Boundary cases -/

/-- The volume comparison makes a Bilu--Freiman witness for the empty set
impossible.  This formally justifies the nonempty-set convention in
`BiluFreimanStatement`.
-/
theorem not_witness_empty (s d C : ℕ) :
    ¬ Nonempty (Witness s d C (∅ : Finset ℤ)) := by
  rintro ⟨W⟩
  have hpos := W.progression.volume_pos
  have hzero : W.progression.volume ≤ 0 := by
    simpa using W.volume_le
  omega

/-- The singleton point GAP, read back as integers, has the expected
singleton carrier. -/
@[simp]
theorem integerCarrier_pointGAP (z : ℤ) :
    integerCarrier (pointGAP (integerPoint z)) = {z} := by
  classical
  ext x
  rw [mem_integerCarrier_iff, pointGAP_carrier]
  simp only [Finset.mem_singleton]
  constructor
  · intro h
    have h0 := congrFun h 0
    simpa [integerPoint] using h0
  · rintro rfl
    rfl

/-- Every singleton has a complete Bilu--Freiman witness with `C = 1`.
This includes higher properness of every order and the exact prefix-volume
comparison for every positive requested dimension.
-/
theorem witness_singleton (s d : ℕ) (hd : 0 < d) (a : ℤ) :
    Nonempty (Witness s d 1 ({a} : Finset ℤ)) := by
  let P : GAP 1 1 := pointGAP (integerPoint (a + a))
  have hP_sProper : P.SProper s :=
    P.sProper_of_dilate_proper s (pointGAP_dilate_proper _ _)
  have hd1 : 1 ≤ d := hd
  let W : Witness s d 1 ({a} : Finset ℤ) :=
    { rank := 1
      rank_pos := by omega
      progression := P
      sProper := hP_sProper
      twoA_subset := by simp [P]
      volume_le := by simp [P, pointGAP, rankOne, GAP.volume]
      volume_le_mul_firstDimensions := by
        simp [P, pointGAP, rankOne, GAP.volume, GAP.firstDimensions] }
  exact ⟨W⟩

/-- Uniform singleton-only version of the Bilu--Freiman theorem. -/
theorem singleton_family (s d : ℕ) (hd : 0 < d) :
    ∃ C : ℕ, 0 < C ∧
      ∀ A : Finset ℤ, A.card = 1 → Nonempty (Witness s d C A) := by
  refine ⟨1, by omega, ?_⟩
  intro A hA
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hA
  exact witness_singleton s d hd a

/-! ## The complete two-point case -/

/-- The double sumset of two distinct integers is the expected three-term
arithmetic progression. -/
theorem twoA_pair {a b : ℤ} (hab : a ≠ b) :
    twoA ({a, b} : Finset ℤ) = {a + a, a + b, b + b} := by
  classical
  ext z
  simp only [mem_twoA_iff, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨x, (rfl | rfl), y, (rfl | rfl), rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inl (by ring))
    · exact Or.inr (Or.inr rfl)
  · intro hz
    rcases hz with rfl | rfl | rfl
    · exact ⟨a, Or.inl rfl, a, Or.inl rfl, rfl⟩
    · exact ⟨a, Or.inl rfl, b, Or.inr rfl, rfl⟩
    · exact ⟨b, Or.inr rfl, b, Or.inr rfl, rfl⟩

/-- Two distinct integers have a three-element double sumset. -/
@[simp]
theorem card_twoA_pair {a b : ℤ} (hab : a ≠ b) :
    (twoA ({a, b} : Finset ℤ)).card = 3 := by
  rw [twoA_pair hab]
  have h₁ : a + a ≠ a + b := by omega
  have h₂ : a + a ≠ b + b := by omega
  have h₃ : a + b ≠ b + b := by omega
  simp [h₁, h₂, h₃]

/-- Every two-element integer set has a Bilu--Freiman witness with the
optimal constant `C = 1`: its double sumset is a proper rank-one
three-term progression. -/
theorem witness_pair (s d : ℕ) (hd : 0 < d) {a b : ℤ} (hab : a ≠ b) :
    Nonempty (Witness s d 1 ({a, b} : Finset ℤ)) := by
  let P : GAP 1 1 := rankOne (integerPoint (a + a)) (integerPoint (b - a)) 2
  have hstep : integerPoint (b - a) ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    simp [integerPoint] at h0
    omega
  have hP_sProper : P.SProper s :=
    P.sProper_of_dilate_proper s (dilate_rankOne_proper 2 s hstep)
  let W : Witness s d 1 ({a, b} : Finset ℤ) :=
    { rank := 1
      rank_pos := by omega
      progression := P
      sProper := hP_sProper
      twoA_subset := by
        intro z hz
        rw [twoA_pair hab] at hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rw [mem_integerCarrier_iff, mem_rankOne_carrier_iff]
        rcases hz with hz | hz | hz
        · refine ⟨0, by omega, ?_⟩
          subst z
          simp
        · refine ⟨1, by omega, ?_⟩
          subst z
          funext j
          simp [rankOnePoint, integerPoint]
        · refine ⟨2, by omega, ?_⟩
          subst z
          funext j
          simp [rankOnePoint, integerPoint]
          ring
      volume_le := by
        simp [P, rankOne, GAP.volume, card_twoA_pair hab]
      volume_le_mul_firstDimensions := by
        have hmin : min 1 d = 1 := min_eq_left hd
        simp [P, rankOne, GAP.volume, GAP.firstDimensions, hmin] }
  exact ⟨W⟩

/-- Uniform Bilu--Freiman witnesses for all sets of cardinality at most
two.  This is the first nontrivial finite-cardinality boundary case of the
general inverse theorem. -/
theorem card_le_two_family (s d : ℕ) (hd : 0 < d) :
    ∃ C : ℕ, 0 < C ∧
      ∀ A : Finset ℤ, A.Nonempty → A.card ≤ 2 →
        Nonempty (Witness s d C A) := by
  refine ⟨1, by omega, ?_⟩
  intro A hA hcard
  have hcard_pos : 0 < A.card := Finset.card_pos.mpr hA
  have h : A.card = 1 ∨ A.card = 2 := by omega
  rcases h with h | h
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h
    exact witness_singleton s d hd a
  · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp h
    exact witness_pair s d hd hab

end CFP.BiluFreiman
end Erdos186
