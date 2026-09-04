import ErdosProblems.Erdos788.FiniteCounting
import ErdosProblems.Erdos788.FiniteField
import Mathlib.Data.Finset.Sum
import Mathlib.NumberTheory.Bertrand

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Ordered suffix-slack designs

This file formalizes the ordered weak design used in the upper bound for
Erdős Problem 788.  Rows are divided recursively into a first block of
ceiling half the remaining rows and a suffix of floor half the remaining
rows.  Each block is an affine-graph design over a prime field, and distinct
blocks use disjoint coordinate types.
-/

open scoped BigOperators
open Function

namespace Erdos788

/-- A total predecessor index.  In the only place where it is used, `j` lies
in `range i.val`, so this is definitionally the row with natural index `j`. -/
def priorIndex {r : ℕ} (i : Fin r) (j : ℕ) : Fin r :=
  ⟨min j i.val, lt_of_le_of_lt (min_le_right _ _) i.isLt⟩

@[simp]
theorem priorIndex_val_of_lt {r j : ℕ} (i : Fin r) (hj : j < i.val) :
    (priorIndex i j).val = j := by
  simp [priorIndex, min_eq_left hj.le]

/-- The contribution of one earlier row to the overlap excess. -/
def overlapCost {Coord : Type*} [DecidableEq Coord]
    (S T : Finset Coord) : ℕ :=
  2 ^ (S ∩ T).card - 1

/-- An ordered family of `ell`-sets whose overlap excess at row `i` fits in
the unused suffix after `i`. -/
structure SuffixDesign (ell r : ℕ) where
  Coord : Type
  [instFintypeCoord : Fintype Coord]
  [instDecidableEqCoord : DecidableEq Coord]
  row : Fin r → Finset Coord
  row_card : ∀ i, (row i).card = ell
  suffix_slack : ∀ i : Fin r,
    (∑ j ∈ Finset.range i.val, overlapCost (row i) (row (priorIndex i j))) ≤
      r - 1 - i.val

namespace SuffixDesign

/-- Cardinality of the coordinate type carried by a suffix design. -/
def coordCard {ell r : ℕ} (D : SuffixDesign ell r) : ℕ :=
  @Fintype.card D.Coord D.instFintypeCoord

theorem coordCard_transport {ell r s : ℕ} (h : r = s)
    (D : SuffixDesign ell r) : (h ▸ D).coordCard = D.coordCard := by
  subst s
  rfl

theorem overlapCost_map {Coord Coord' : Type*}
    [DecidableEq Coord] [DecidableEq Coord']
    (f : Coord ↪ Coord') (S T : Finset Coord) :
    overlapCost (S.map f) (T.map f) = overlapCost S T := by
  rw [overlapCost, overlapCost, ← Finset.map_inter]
  simp

theorem overlapCost_map_inl_inr {Coord Coord' : Type*}
    [DecidableEq Coord] [DecidableEq Coord']
    (S : Finset Coord) (T : Finset Coord') :
    overlapCost (S.map Embedding.inl) (T.map Embedding.inr) = 0 := by
  have hdisj : Disjoint (S.map Embedding.inl) (T.map Embedding.inr) :=
    Finset.disjoint_map_inl_map_inr S T
  rw [overlapCost, Finset.disjoint_iff_inter_eq_empty.mp hdisj]
  simp

theorem overlapCost_comm {Coord : Type*} [DecidableEq Coord]
    (S T : Finset Coord) : overlapCost S T = overlapCost T S := by
  simp only [overlapCost, Finset.inter_comm]

theorem overlapCost_map_inr_inl {Coord Coord' : Type*}
    [DecidableEq Coord] [DecidableEq Coord']
    (S : Finset Coord) (T : Finset Coord') :
    overlapCost (T.map Embedding.inr) (S.map Embedding.inl) = 0 := by
  rw [overlapCost_comm, overlapCost_map_inl_inr]

theorem overlapCost_le_one_of_inter_card_le_one
    {Coord : Type*} [DecidableEq Coord] {S T : Finset Coord}
    (hcard : (S ∩ T).card ≤ 1) : overlapCost S T ≤ 1 := by
  have hcases : (S ∩ T).card = 0 ∨ (S ∩ T).card = 1 := by omega
  rcases hcases with hzero | hone
  · simp [overlapCost, hzero]
  · simp [overlapCost, hone]

/-- The unique design on no rows. -/
def empty (ell : ℕ) : SuffixDesign ell 0 where
  Coord := Empty
  row := Fin.elim0
  row_card := fun i ↦ Fin.elim0 i
  suffix_slack := fun i ↦ Fin.elim0 i

@[simp]
theorem empty_coordCard (ell : ℕ) : (empty ell).coordCard = 0 :=
  rfl

/-- A block design in which distinct rows meet in at most one coordinate. -/
structure UnitIntersectionBlock (ell m : ℕ) where
  Coord : Type
  [instFintypeCoord : Fintype Coord]
  [instDecidableEqCoord : DecidableEq Coord]
  row : Fin m → Finset Coord
  row_card : ∀ i, (row i).card = ell
  inter_card_le_one : ∀ {i j}, i ≠ j → (row i ∩ row j).card ≤ 1

/-- The first `m` coefficient pairs in a `q` by `q` square, embedded in the
prime field. -/
noncomputable def affineCoeffEmbedding
    (q m : ℕ) [Fact q.Prime] (hm : m ≤ q * q) :
    Fin m ↪ ZMod q × ZMod q where
  toFun t :=
    let uv : Fin q × Fin q := finProdFinEquiv.symm (Fin.castLE hm t)
    ((uv.1.val : ZMod q), (uv.2.val : ZMod q))
  inj' := by
    intro s t hst
    let us : Fin q × Fin q := finProdFinEquiv.symm (Fin.castLE hm s)
    let ut : Fin q × Fin q := finProdFinEquiv.symm (Fin.castLE hm t)
    change ((us.1.val : ZMod q), (us.2.val : ZMod q)) =
      ((ut.1.val : ZMod q), (ut.2.val : ZMod q)) at hst
    have hstFst : (us.1.val : ZMod q) = (ut.1.val : ZMod q) :=
      congrArg Prod.fst hst
    have hstSnd : (us.2.val : ZMod q) = (ut.2.val : ZMod q) :=
      congrArg Prod.snd hst
    have hfst : us.1 = ut.1 := by
      apply Fin.ext
      exact CharP.natCast_injOn_Iio (ZMod q) q us.1.isLt ut.1.isLt hstFst
    have hsnd : us.2 = ut.2 := by
      apply Fin.ext
      exact CharP.natCast_injOn_Iio (ZMod q) q us.2.isLt ut.2.isLt hstSnd
    have huv : us = ut := Prod.ext hfst hsnd
    exact Fin.castLE_injective hm (finProdFinEquiv.symm.injective huv)

/-- The graph, over the first `ell` field elements, of the affine function
with coefficient pair assigned to row `t`. -/
noncomputable def affineRow
    (ell q m : ℕ) [Fact q.Prime] (hm : m ≤ q * q)
    (t : Fin m) : Finset (Fin ell × ZMod q) :=
  (Finset.univ : Finset (Fin ell)).map
    { toFun := fun x ↦
        (x, (affineCoeffEmbedding q m hm t).1 * (x.val : ZMod q) +
          (affineCoeffEmbedding q m hm t).2)
      inj' := fun _ _ h ↦ congrArg Prod.fst h }

@[simp]
theorem card_affineRow
    (ell q m : ℕ) [Fact q.Prime] (hm : m ≤ q * q) (t : Fin m) :
    (affineRow ell q m hm t).card = ell := by
  simp [affineRow]

theorem mem_affineRow_iff
    {ell q m : ℕ} [Fact q.Prime] {hm : m ≤ q * q}
    {t : Fin m} {z : Fin ell × ZMod q} :
    z ∈ affineRow ell q m hm t ↔
      z.2 = (affineCoeffEmbedding q m hm t).1 * (z.1.val : ZMod q) +
        (affineCoeffEmbedding q m hm t).2 := by
  simp only [affineRow, Finset.mem_map, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨x, rfl⟩
    rfl
  · intro hz
    refine ⟨z.1, ?_⟩
    exact Prod.ext rfl hz.symm

/-- Distinct affine rows meet in at most one coordinate. -/
theorem affineRow_inter_card_le_one
    {ell q m : ℕ} [Fact q.Prime] (hellq : ell ≤ q)
    (hm : m ≤ q * q) {s t : Fin m} (hst : s ≠ t) :
    (affineRow ell q m hm s ∩ affineRow ell q m hm t).card ≤ 1 := by
  rw [Finset.card_le_one_iff]
  intro u v hu hv
  have huS := mem_affineRow_iff.mp (Finset.mem_inter.mp hu).1
  have huT := mem_affineRow_iff.mp (Finset.mem_inter.mp hu).2
  have hvS := mem_affineRow_iff.mp (Finset.mem_inter.mp hv).1
  have hvT := mem_affineRow_iff.mp (Finset.mem_inter.mp hv).2
  have hcoeff : affineCoeffEmbedding q m hm s ≠
      affineCoeffEmbedding q m hm t := by
    exact fun h ↦ hst ((affineCoeffEmbedding q m hm).injective h)
  have huvCast : (u.1.val : ZMod q) = (v.1.val : ZMod q) :=
    affine_graph_eq_unique hcoeff (huS.symm.trans huT) (hvS.symm.trans hvT)
  have huvVal : u.1.val = v.1.val :=
    CharP.natCast_injOn_Iio (ZMod q) q
      (u.1.isLt.trans_le hellq) (v.1.isLt.trans_le hellq) huvCast
  have huvFirst : u.1 = v.1 := Fin.ext huvVal
  apply Prod.ext huvFirst
  rw [huS, hvS, huvFirst]

/-- The affine graph construction as a unit-intersection block. -/
noncomputable def affineBlock
    (ell q m : ℕ) [Fact q.Prime] (hellq : ell ≤ q)
    (hm : m ≤ q * q) : UnitIntersectionBlock ell m where
  Coord := Fin ell × ZMod q
  row := affineRow ell q m hm
  row_card := card_affineRow ell q m hm
  inter_card_le_one := affineRow_inter_card_le_one hellq hm

/-- Cardinality of the coordinate type carried by a unit-intersection block. -/
def UnitIntersectionBlock.coordCard {ell m : ℕ}
    (B : UnitIntersectionBlock ell m) : ℕ :=
  @Fintype.card B.Coord B.instFintypeCoord

@[simp]
theorem card_affineBlock_coord
    (ell q m : ℕ) [Fact q.Prime] (hellq : ell ≤ q)
    (hm : m ≤ q * q) :
    (affineBlock ell q m hellq hm).coordCard = ell * q := by
  change Fintype.card (Fin ell × ZMod q) = ell * q
  simp

/-- The Bertrand threshold for a block.  `sqrt m + 1` is the integer ceiling
needed to guarantee at least `m` coefficient pairs. -/
def blockPrimeThreshold (ell m : ℕ) : ℕ :=
  max 2 (max ell (Nat.sqrt m + 1))

theorem blockPrimeThreshold_pos (ell m : ℕ) :
    0 < blockPrimeThreshold ell m := by
  simp [blockPrimeThreshold]

/-- A deterministic (via classical choice) prime in the Bertrand interval. -/
noncomputable def blockPrime (ell m : ℕ) : ℕ :=
  Classical.choose
    (bertrand_interface (blockPrimeThreshold ell m)
      (Nat.ne_of_gt (blockPrimeThreshold_pos ell m)))

theorem blockPrime_prime (ell m : ℕ) : (blockPrime ell m).Prime :=
  (Classical.choose_spec
    (bertrand_interface (blockPrimeThreshold ell m)
      (Nat.ne_of_gt (blockPrimeThreshold_pos ell m)))).1

theorem blockPrimeThreshold_lt (ell m : ℕ) :
    blockPrimeThreshold ell m < blockPrime ell m :=
  (Classical.choose_spec
    (bertrand_interface (blockPrimeThreshold ell m)
      (Nat.ne_of_gt (blockPrimeThreshold_pos ell m)))).2.1

theorem blockPrime_le_twice_threshold (ell m : ℕ) :
    blockPrime ell m ≤ 2 * blockPrimeThreshold ell m :=
  (Classical.choose_spec
    (bertrand_interface (blockPrimeThreshold ell m)
      (Nat.ne_of_gt (blockPrimeThreshold_pos ell m)))).2.2

theorem ell_le_blockPrime (ell m : ℕ) : ell ≤ blockPrime ell m := by
  have hEll : ell ≤ blockPrimeThreshold ell m := by
    simp [blockPrimeThreshold]
  exact hEll.trans (blockPrimeThreshold_lt ell m).le

theorem blockSize_le_blockPrime_sq (ell m : ℕ) :
    m ≤ blockPrime ell m * blockPrime ell m := by
  have hsqrt : Nat.sqrt m + 1 ≤ blockPrimeThreshold ell m := by
    simp [blockPrimeThreshold]
  have hq : Nat.sqrt m + 1 ≤ blockPrime ell m :=
    hsqrt.trans (blockPrimeThreshold_lt ell m).le
  have hm : m < (Nat.sqrt m + 1) * (Nat.sqrt m + 1) :=
    Nat.lt_succ_sqrt m
  exact hm.le.trans (Nat.mul_le_mul hq hq)

/-- The affine block selected for the recursive construction. -/
noncomputable def chosenAffineBlock (ell m : ℕ) :
    UnitIntersectionBlock ell m := by
  letI : Fact (blockPrime ell m).Prime := ⟨blockPrime_prime ell m⟩
  exact affineBlock ell (blockPrime ell m) m
    (ell_le_blockPrime ell m) (blockSize_le_blockPrime_sq ell m)

theorem chosenAffineBlock_coordCard (ell m : ℕ) :
    (chosenAffineBlock ell m).coordCard = ell * blockPrime ell m := by
  let : Fact (blockPrime ell m).Prime := ⟨blockPrime_prime ell m⟩
  exact card_affineBlock_coord ell (blockPrime ell m) m
    (ell_le_blockPrime ell m) (blockSize_le_blockPrime_sq ell m)

theorem chosenAffineBlock_coordCard_le (ell m : ℕ) :
    (chosenAffineBlock ell m).coordCard ≤
      2 * ell * blockPrimeThreshold ell m := by
  rw [chosenAffineBlock_coordCard]
  have h := Nat.mul_le_mul_left ell (blockPrime_le_twice_threshold ell m)
  simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using! h

section Prepend

variable {ell m t : ℕ} (B : UnitIntersectionBlock ell m)
  (D : SuffixDesign ell t)

local instance blockFintypeCoord : Fintype B.Coord := B.instFintypeCoord
local instance blockDecidableEqCoord : DecidableEq B.Coord := B.instDecidableEqCoord
local instance suffixFintypeCoord : Fintype D.Coord := D.instFintypeCoord
local instance suffixDecidableEqCoord : DecidableEq D.Coord := D.instDecidableEqCoord

/-- Put a unit-intersection block before an already constructed suffix,
tagging the two coordinate universes by the two summands. -/
noncomputable def prependRow (i : Fin (m + t)) :
    Finset (B.Coord ⊕ D.Coord) := by
  letI := B.instDecidableEqCoord
  letI := D.instDecidableEqCoord
  exact if hi : i.val < m then
    (B.row ⟨i.val, hi⟩).map Embedding.inl
  else
    (D.row ⟨i.val - m, by omega⟩).map Embedding.inr

theorem prependRow_of_lt (i : Fin (m + t)) (hi : i.val < m) :
    prependRow B D i = (B.row ⟨i.val, hi⟩).map Embedding.inl := by
  let := B.instDecidableEqCoord
  let := D.instDecidableEqCoord
  simp [prependRow, hi]

theorem prependRow_of_ge (i : Fin (m + t)) (hi : m ≤ i.val) :
    prependRow B D i =
      (D.row ⟨i.val - m, by omega⟩).map Embedding.inr := by
  let := B.instDecidableEqCoord
  let := D.instDecidableEqCoord
  simp [prependRow, Nat.not_lt.mpr hi]

theorem card_prependRow (i : Fin (m + t)) :
    (prependRow B D i).card = ell := by
  let := B.instDecidableEqCoord
  let := D.instDecidableEqCoord
  by_cases hi : i.val < m
  · rw [prependRow_of_lt B D i hi, Finset.card_map, B.row_card]
  · rw [prependRow_of_ge B D i (Nat.le_of_not_gt hi), Finset.card_map,
      D.row_card]

/-- The first-block/suffix splice preserves the suffix-slack inequalities
provided the suffix has at least `m-1` rows. -/
theorem prepend_suffix_slack (hblock : m - 1 ≤ t) (i : Fin (m + t)) :
    (∑ j ∈ Finset.range i.val,
      overlapCost (prependRow B D i) (prependRow B D (priorIndex i j))) ≤
      m + t - 1 - i.val := by
  let := B.instDecidableEqCoord
  let := D.instDecidableEqCoord
  by_cases hi : i.val < m
  · have hunit : ∀ j ∈ Finset.range i.val,
        overlapCost (prependRow B D i) (prependRow B D (priorIndex i j)) ≤ 1 := by
      intro j hj
      have hji : j < i.val := Finset.mem_range.mp hj
      have hjm : (priorIndex i j).val < m := by
        rw [priorIndex_val_of_lt i hji]
        omega
      rw [prependRow_of_lt B D i hi,
        prependRow_of_lt B D (priorIndex i j) hjm,
        overlapCost_map]
      apply overlapCost_le_one_of_inter_card_le_one
      apply B.inter_card_le_one
      intro heq
      have hval := congrArg Fin.val heq
      have hij : i.val = j := by
        simpa [priorIndex_val_of_lt i hji] using! hval
      omega
    calc
      (∑ j ∈ Finset.range i.val,
          overlapCost (prependRow B D i) (prependRow B D (priorIndex i j)))
          ≤ (Finset.range i.val).card :=
        sum_of_unit_costs_le_card (Finset.range i.val) _ hunit
      _ = i.val := Finset.card_range i.val
      _ ≤ m + t - 1 - i.val := by
        have hlocal := local_row_has_suffix_slack hi hblock
        omega
  · have him : m ≤ i.val := Nat.le_of_not_gt hi
    let k : ℕ := i.val - m
    have hk : k < t := by
      dsimp [k]
      omega
    let ik : Fin t := ⟨k, hk⟩
    have hi_eq : i.val = m + k := by
      dsimp [k]
      omega
    have hfirst :
        (∑ j ∈ Finset.range m,
          overlapCost (prependRow B D i) (prependRow B D (priorIndex i j))) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hjm : j < m := Finset.mem_range.mp hj
      have hji : j < i.val := hjm.trans_le him
      have hpj : (priorIndex i j).val < m := by
        rw [priorIndex_val_of_lt i hji]
        exact hjm
      rw [prependRow_of_ge B D i him,
        prependRow_of_lt B D (priorIndex i j) hpj,
        overlapCost_map_inr_inl]
    have hsecond :
        (∑ j ∈ Finset.range k,
          overlapCost (prependRow B D i)
            (prependRow B D (priorIndex i (m + j)))) =
        (∑ j ∈ Finset.range k,
          overlapCost (D.row ik) (D.row (priorIndex ik j))) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjk : j < k := Finset.mem_range.mp hj
      have hmji : m + j < i.val := by omega
      have hpriorGe : m ≤ (priorIndex i (m + j)).val := by
        rw [priorIndex_val_of_lt i hmji]
        omega
      rw [prependRow_of_ge B D i him,
        prependRow_of_ge B D (priorIndex i (m + j)) hpriorGe,
        overlapCost_map]
      have hleft :
          (⟨i.val - m, by omega⟩ : Fin t) = ik := by
        apply Fin.ext
        rfl
      have hright :
          (⟨(priorIndex i (m + j)).val - m, by omega⟩ : Fin t) =
            priorIndex ik j := by
        apply Fin.ext
        change (priorIndex i (m + j)).val - m = (priorIndex ik j).val
        rw [priorIndex_val_of_lt i hmji, priorIndex_val_of_lt ik hjk]
        omega
      rw [hleft, hright]
    rw [hi_eq, Finset.sum_range_add, hfirst, hsecond, zero_add]
    have hD := D.suffix_slack ik
    dsimp [ik] at hD ⊢
    omega

/-- Prepend a unit-intersection block to a suffix design. -/
noncomputable def prepend (hblock : m - 1 ≤ t) : SuffixDesign ell (m + t) := by
  letI := B.instFintypeCoord
  letI := B.instDecidableEqCoord
  letI := D.instFintypeCoord
  letI := D.instDecidableEqCoord
  exact
    { Coord := B.Coord ⊕ D.Coord
      row := prependRow B D
      row_card := card_prependRow B D
      suffix_slack := prepend_suffix_slack (B := B) (D := D) hblock }

theorem prepend_coordCard (hblock : m - 1 ≤ t) :
    (prepend (B := B) (D := D) hblock).coordCard =
      B.coordCard + D.coordCard := by
  change Fintype.card (B.Coord ⊕ D.Coord) =
    @Fintype.card B.Coord B.instFintypeCoord +
      @Fintype.card D.Coord D.instFintypeCoord
  let := B.instFintypeCoord
  let := D.instFintypeCoord
  exact Fintype.card_sum

end Prepend

/-- Ceiling half and floor half of the remaining rows. -/
def firstBlockSize (r : ℕ) : ℕ := (r + 1) / 2

def suffixSize (r : ℕ) : ℕ := r / 2

theorem firstBlockSize_add_suffixSize (r : ℕ) :
    firstBlockSize r + suffixSize r = r := by
  simp only [firstBlockSize, suffixSize]
  omega

theorem firstBlockSize_pred_le_suffixSize (r : ℕ) :
    firstBlockSize r - 1 ≤ suffixSize r := by
  simp only [firstBlockSize, suffixSize]
  omega

theorem suffixSize_lt {r : ℕ} (hr : 0 < r) : suffixSize r < r := by
  simp only [suffixSize]
  omega

/-- The recursive ordered construction.  The first ceiling-half block is an
affine graph block, and the floor-half suffix is constructed recursively. -/
noncomputable def build (ell : ℕ) (r : ℕ) : SuffixDesign ell r :=
  if hr : r = 0 then
    hr ▸ empty ell
  else
    let m := firstBlockSize r
    let t := suffixSize r
    have hsum : m + t = r := firstBlockSize_add_suffixSize r
    hsum ▸ prepend (B := chosenAffineBlock ell m) (D := build ell t)
      (firstBlockSize_pred_le_suffixSize r)
termination_by r
decreasing_by exact suffixSize_lt (Nat.pos_of_ne_zero hr)

theorem build_coordCard_eq {ell r : ℕ} (hr : 0 < r) :
    (build ell r).coordCard =
      (chosenAffineBlock ell (firstBlockSize r)).coordCard +
        (build ell (suffixSize r)).coordCard := by
  rw [build]
  simp only [dif_neg (Nat.ne_of_gt hr)]
  rw [coordCard_transport]
  rw [prepend_coordCard]

/-- A convenient explicit cap for the coordinate cost of the first block. -/
def designBlockCap (ell r : ℕ) : ℕ :=
  2 * ell * (ell + Nat.sqrt r + 3)

/-- A deliberately simple quantitative coordinate bound.  It is slightly
coarser than the paper's geometric-series estimate by a logarithmic factor,
but remains `r^(1/2+o(1))` and is sufficient for the final exponent. -/
def designCoordBound (ell r : ℕ) : ℕ :=
  designBlockCap ell r * (Nat.log 2 r + 1)

theorem firstBlockSize_le {r : ℕ} (hr : 0 < r) :
    firstBlockSize r ≤ r := by
  simp only [firstBlockSize]
  omega

theorem chosenAffineBlock_coordCard_le_designBlockCap
    (ell : ℕ) {r : ℕ} (hr : 0 < r) :
    (chosenAffineBlock ell (firstBlockSize r)).coordCard ≤
      designBlockCap ell r := by
  refine (chosenAffineBlock_coordCard_le ell (firstBlockSize r)).trans ?_
  have hsqrt : Nat.sqrt (firstBlockSize r) ≤ Nat.sqrt r :=
    Nat.sqrt_le_sqrt (firstBlockSize_le hr)
  have hthreshold : blockPrimeThreshold ell (firstBlockSize r) ≤
      ell + Nat.sqrt r + 3 := by
    simp only [blockPrimeThreshold]
    apply max_le
    · omega
    · apply max_le
      · omega
      · omega
  exact Nat.mul_le_mul_left (2 * ell) hthreshold

theorem designBlockCap_suffix_le (ell r : ℕ) :
    designBlockCap ell (suffixSize r) ≤ designBlockCap ell r := by
  unfold designBlockCap suffixSize
  exact Nat.mul_le_mul_left (2 * ell)
    (Nat.add_le_add_right
      (Nat.add_le_add_left (Nat.sqrt_le_sqrt (Nat.div_le_self r 2)) ell) 3)

theorem log_suffix_add_one {r : ℕ} (hr : 2 ≤ r) :
    Nat.log 2 (suffixSize r) + 1 = Nat.log 2 r := by
  rw [suffixSize, Nat.log_div_base]
  have hlog : 0 < Nat.log 2 r := Nat.log_pos Nat.one_lt_two hr
  omega

/-- Explicit size estimate for the recursive suffix-slack design. -/
theorem build_coordCard_le_designCoordBound (ell r : ℕ) :
    (build ell r).coordCard ≤ designCoordBound ell r := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
      by_cases hr0 : r = 0
      · subst r
        simp [build, designCoordBound]
      have hr : 0 < r := Nat.pos_of_ne_zero hr0
      by_cases hr1 : r = 1
      · subst r
        rw [build_coordCard_eq (by norm_num : 0 < 1)]
        have hblock :=
          chosenAffineBlock_coordCard_le_designBlockCap ell
            (by norm_num : 0 < 1)
        simpa [firstBlockSize, suffixSize, build, designCoordBound,
          designBlockCap] using! hblock
      have hr2 : 2 ≤ r := by omega
      have htlt : suffixSize r < r := suffixSize_lt hr
      have hsuffix := ih (suffixSize r) htlt
      have hblock := chosenAffineBlock_coordCard_le_designBlockCap ell hr
      rw [build_coordCard_eq hr]
      calc
        (chosenAffineBlock ell (firstBlockSize r)).coordCard +
            (build ell (suffixSize r)).coordCard ≤
            designBlockCap ell r + designCoordBound ell (suffixSize r) :=
          Nat.add_le_add hblock hsuffix
        _ ≤ designBlockCap ell r +
            designBlockCap ell r * Nat.log 2 r := by
          apply Nat.add_le_add_left
          rw [designCoordBound, log_suffix_add_one hr2]
          exact Nat.mul_le_mul_right _ (designBlockCap_suffix_le ell r)
        _ = designCoordBound ell r := by
          rw [designCoordBound]
          ring

/-- Scale below which the remaining logarithmic number of blocks is charged
to the `ell^2 log ell` tail. -/
def designTailScale (ell : ℕ) : ℕ :=
  16 * (ell + 3) ^ 2

/-- The real-valued sharp bound used in the final asymptotic parameter
calculation. -/
noncomputable def designStrongBound (ell r : ℕ) : ℝ :=
  10 * ell * Real.sqrt r +
    10 * ell * (ell + 3) * (Nat.log 2 (designTailScale ell) + 1)

theorem natSqrt_firstBlockSize_le {r : ℕ} (hr : 2 ≤ r) :
    (Nat.sqrt (firstBlockSize r) : ℝ) ≤
      (7 / 8 : ℝ) * Real.sqrt r := by
  calc
    (Nat.sqrt (firstBlockSize r) : ℝ) ≤
        Real.sqrt (firstBlockSize r : ℝ) :=
      Real.nat_sqrt_le_real_sqrt
    _ ≤ (7 / 8 : ℝ) * Real.sqrt r := by
      apply Real.sqrt_le_iff.mpr
      constructor
      · positivity
      · have hmNat : 4 * firstBlockSize r ≤ 3 * r := by
          simp only [firstBlockSize]
          omega
        have hm : (4 : ℝ) * firstBlockSize r ≤ 3 * r := by
          exact_mod_cast hmNat
        rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ r)]
        norm_num at hm ⊢
        nlinarith

theorem natSqrt_suffixSize_le {r : ℕ} (hr : 2 ≤ r) :
    (Nat.sqrt (suffixSize r) : ℝ) ≤
      (3 / 4 : ℝ) * Real.sqrt r := by
  calc
    (Nat.sqrt (suffixSize r) : ℝ) ≤ Real.sqrt (suffixSize r : ℝ) :=
      Real.nat_sqrt_le_real_sqrt
    _ ≤ (3 / 4 : ℝ) * Real.sqrt r := by
      apply Real.sqrt_le_iff.mpr
      constructor
      · positivity
      · have htNat : 2 * suffixSize r ≤ r := by
          simp only [suffixSize]
          omega
        have ht : (2 : ℝ) * suffixSize r ≤ r := by
          exact_mod_cast htNat
        rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ r)]
        norm_num at ht ⊢
        nlinarith

theorem realSqrt_suffixSize_le {r : ℕ} (hr : 2 ≤ r) :
    Real.sqrt (suffixSize r : ℝ) ≤
      (3 / 4 : ℝ) * Real.sqrt r := by
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · have htNat : 2 * suffixSize r ≤ r := by
      simp only [suffixSize]
      omega
    have ht : (2 : ℝ) * suffixSize r ≤ r := by
      exact_mod_cast htNat
    rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ r)]
    norm_num at ht ⊢
    nlinarith

theorem quarter_sqrt_ge_of_designTailScale_le
    {ell r : ℕ} (hlarge : designTailScale ell ≤ r) :
    (ell + 3 : ℝ) ≤ (1 / 4 : ℝ) * Real.sqrt r := by
  rw [← sq_le_sq₀ (by positivity : (0 : ℝ) ≤ ell + 3)
    (by positivity : (0 : ℝ) ≤ (1 / 4 : ℝ) * Real.sqrt r)]
  rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ r)]
  have hlargeR : (designTailScale ell : ℝ) ≤ r := by
    exact_mod_cast hlarge
  rw [designTailScale] at hlargeR
  norm_num at hlargeR ⊢
  nlinarith

theorem chosenAffineBlock_coordCard_real_le_of_large
    (ell : ℕ) {r : ℕ} (hlarge : designTailScale ell ≤ r) :
    ((chosenAffineBlock ell (firstBlockSize r)).coordCard : ℝ) ≤
      (9 / 4 : ℝ) * ell * Real.sqrt r := by
  have hscalePos : 0 < designTailScale ell := by
    simp [designTailScale]
  have hr2 : 2 ≤ r := by
    have hsq : 1 ≤ (ell + 3) ^ 2 :=
      one_le_pow₀ (by omega : 1 ≤ ell + 3)
    have : 2 ≤ designTailScale ell := by
      rw [designTailScale]
      omega
    exact this.trans hlarge
  have hthreshold : blockPrimeThreshold ell (firstBlockSize r) ≤
      (ell + 3) + Nat.sqrt (firstBlockSize r) := by
    simp only [blockPrimeThreshold]
    apply max_le
    · omega
    · apply max_le <;> omega
  have hblockNat :
      (chosenAffineBlock ell (firstBlockSize r)).coordCard ≤
        2 * ell * ((ell + 3) + Nat.sqrt (firstBlockSize r)) :=
    (chosenAffineBlock_coordCard_le ell (firstBlockSize r)).trans
      (Nat.mul_le_mul_left (2 * ell) hthreshold)
  have hblock :
      ((chosenAffineBlock ell (firstBlockSize r)).coordCard : ℝ) ≤
        2 * ell * ((ell + 3 : ℝ) + Nat.sqrt (firstBlockSize r)) := by
    exact_mod_cast hblockNat
  have hsum : (ell + 3 : ℝ) + Nat.sqrt (firstBlockSize r) ≤
      (9 / 8 : ℝ) * Real.sqrt r := by
    nlinarith [quarter_sqrt_ge_of_designTailScale_le hlarge,
      natSqrt_firstBlockSize_le hr2]
  calc
    ((chosenAffineBlock ell (firstBlockSize r)).coordCard : ℝ) ≤
        2 * ell * ((ell + 3 : ℝ) + Nat.sqrt (firstBlockSize r)) := hblock
    _ ≤ 2 * ell * ((9 / 8 : ℝ) * Real.sqrt r) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (9 / 4 : ℝ) * ell * Real.sqrt r := by ring

theorem designCoordBound_le_tail_of_lt
    (ell : ℕ) {r : ℕ} (hsmall : r < designTailScale ell) :
    designCoordBound ell r ≤
      10 * ell * (ell + 3) * (Nat.log 2 (designTailScale ell) + 1) := by
  have hsqrt : Nat.sqrt r < 4 * (ell + 3) := by
    apply Nat.sqrt_lt'.2
    have hsquare : (4 * (ell + 3)) ^ 2 = designTailScale ell := by
      rw [designTailScale]
      ring
    rwa [hsquare]
  have hcap : designBlockCap ell r ≤ 10 * ell * (ell + 3) := by
    rw [designBlockCap]
    have hsum : ell + Nat.sqrt r + 3 ≤ 5 * (ell + 3) := by omega
    calc
      2 * ell * (ell + Nat.sqrt r + 3) ≤
          2 * ell * (5 * (ell + 3)) := Nat.mul_le_mul_left _ hsum
      _ = 10 * ell * (ell + 3) := by ring
  have hlog : Nat.log 2 r + 1 ≤
      Nat.log 2 (designTailScale ell) + 1 :=
    Nat.add_le_add_right (Nat.log_monotone hsmall.le) 1
  rw [designCoordBound]
  exact Nat.mul_le_mul hcap hlog

/-- The recursive construction has the paper's required
`O(ell*sqrt r + ell^2*log ell)` size, with explicit constants. -/
theorem build_coordCard_le_designStrongBound (ell r : ℕ) :
    ((build ell r).coordCard : ℝ) ≤ designStrongBound ell r := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
      by_cases hsmall : r < designTailScale ell
      · have hnat := (build_coordCard_le_designCoordBound ell r).trans
          (designCoordBound_le_tail_of_lt ell hsmall)
        have hreal : ((build ell r).coordCard : ℝ) ≤
            10 * ell * (ell + 3) *
              (Nat.log 2 (designTailScale ell) + 1) := by
          exact_mod_cast hnat
        rw [designStrongBound]
        exact hreal.trans (le_add_of_nonneg_left (by positivity))
      · have hlarge : designTailScale ell ≤ r := Nat.le_of_not_gt hsmall
        have hr : 0 < r := (show 0 < designTailScale ell by
          simp [designTailScale]).trans_le hlarge
        have hr2 : 2 ≤ r := by
          have hsq : 1 ≤ (ell + 3) ^ 2 :=
            one_le_pow₀ (by omega : 1 ≤ ell + 3)
          have : 2 ≤ designTailScale ell := by
            rw [designTailScale]
            omega
          exact this.trans hlarge
        have htlt : suffixSize r < r := suffixSize_lt hr
        have hsuffix := ih (suffixSize r) htlt
        have hblock := chosenAffineBlock_coordCard_real_le_of_large ell hlarge
        rw [designStrongBound] at hsuffix ⊢
        rw [build_coordCard_eq hr]
        push_cast
        have hsqrt := realSqrt_suffixSize_le hr2
        have hscaled : 10 * (ell : ℝ) * Real.sqrt (suffixSize r) ≤
            10 * ell * ((3 / 4 : ℝ) * Real.sqrt r) :=
          mul_le_mul_of_nonneg_left hsqrt (by positivity)
        calc
          ((chosenAffineBlock ell (firstBlockSize r)).coordCard : ℝ) +
              ((build ell (suffixSize r)).coordCard : ℝ) ≤
              (9 / 4 : ℝ) * ell * Real.sqrt r +
                (10 * ell * Real.sqrt (suffixSize r) +
                  10 * ell * (ell + 3) *
                    (Nat.log 2 (designTailScale ell) + 1)) :=
            add_le_add hblock hsuffix
          _ ≤ 10 * ell * Real.sqrt r +
                10 * ell * (ell + 3) *
                  (Nat.log 2 (designTailScale ell) + 1) := by
            have hnonneg : 0 ≤ (ell : ℝ) * Real.sqrt r := by positivity
            nlinarith

end SuffixDesign

end Erdos788
