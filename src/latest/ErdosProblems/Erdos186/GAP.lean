import Mathlib

/-!
# Generalized arithmetic progressions in integer lattices

This file contains the elementary, finite GAP interface used in the
formalization of Erdős problem 186.  The first parameter is the dimension of
the ambient lattice and the second is the rank of the progression.

Widths are required to be positive.  Thus the coefficient box is never empty
(including in rank zero), and its cardinality is exactly the product of the
widths.
-/

namespace Erdos186

/-- The integer lattice of dimension `d`. -/
abbrev LatticePoint (d : ℕ) := Fin d → ℤ

/-- A rank-`r` generalized arithmetic progression in `ℤ^d`.

Its displayed points are
`offset + ∑ i, n i • steps i`, with `0 ≤ n i < widths i`.
-/
structure GAP (d r : ℕ) where
  offset : LatticePoint d
  steps : Fin r → LatticePoint d
  widths : Fin r → ℕ
  width_pos : ∀ i, 0 < widths i

namespace GAP

variable {d r : ℕ}

/-- The finite box of admissible GAP coordinates. -/
abbrev Coord (P : GAP d r) := (i : Fin r) → Fin (P.widths i)

/-- The all-zero coordinate tuple. -/
def zeroCoord (P : GAP d r) : P.Coord :=
  fun i => ⟨0, P.width_pos i⟩

/-- Evaluation of a coordinate tuple in the ambient lattice. -/
def coordPoint (P : GAP d r) (n : P.Coord) : LatticePoint d :=
  fun j => P.offset j + ∑ i, (n i : ℤ) * P.steps i j

/-- The finite carrier of a GAP. -/
def carrier (P : GAP d r) : Finset (LatticePoint d) :=
  Finset.univ.image P.coordPoint

/-- The volume of a GAP presentation: the cardinality of its coefficient box. -/
def volume (P : GAP d r) : ℕ :=
  ∏ i, P.widths i

/-- A GAP is proper when its displayed parameterization is injective. -/
def Proper (P : GAP d r) : Prop :=
  Function.Injective P.coordPoint

/-- A GAP is homogeneous when its offset lies in the integer span of its steps. -/
def Homogeneous (P : GAP d r) : Prop :=
  ∃ z : Fin r → ℤ, P.offset = fun j => ∑ i, z i * P.steps i j

@[simp]
theorem mem_carrier_iff {P : GAP d r} {x : LatticePoint d} :
    x ∈ P.carrier ↔ ∃ n : P.Coord, P.coordPoint n = x := by
  simp [carrier]

@[simp]
theorem coordPoint_mem_carrier (P : GAP d r) (n : P.Coord) :
    P.coordPoint n ∈ P.carrier := by
  exact mem_carrier_iff.mpr ⟨n, rfl⟩

/-- The carrier cardinality is at most the displayed volume, with no
properness assumption. -/
theorem card_carrier_le_volume (P : GAP d r) :
    P.carrier.card ≤ P.volume := by
  rw [carrier, volume]
  calc
    (Finset.univ.image P.coordPoint).card ≤ Finset.univ.card :=
      Finset.card_image_le
    _ = ∏ i, P.widths i := by simp

/-- A proper presentation identifies the coordinate box with the carrier. -/
noncomputable def coordinateEquiv (P : GAP d r) (hP : P.Proper) :
    P.Coord ≃ {x // x ∈ P.carrier} where
  toFun n := ⟨P.coordPoint n, P.coordPoint_mem_carrier n⟩
  invFun x := Classical.choose (mem_carrier_iff.mp x.property)
  left_inv n := by
    apply hP
    exact Classical.choose_spec
      (mem_carrier_iff.mp (P.coordPoint_mem_carrier n))
  right_inv x := by
    apply Subtype.ext
    exact Classical.choose_spec (mem_carrier_iff.mp x.property)

/-- The coordinate map on a proper GAP. -/
noncomputable def coordinateMap (P : GAP d r) (hP : P.Proper) :
    {x // x ∈ P.carrier} → P.Coord :=
  (P.coordinateEquiv hP).symm

@[simp]
theorem coordinateMap_coordPoint (P : GAP d r) (hP : P.Proper) (n : P.Coord) :
    P.coordinateMap hP ⟨P.coordPoint n, P.coordPoint_mem_carrier n⟩ = n := by
  exact (P.coordinateEquiv hP).symm_apply_apply n

@[simp]
theorem coordPoint_coordinateMap (P : GAP d r) (hP : P.Proper)
    (x : {x // x ∈ P.carrier}) :
    P.coordPoint (P.coordinateMap hP x) = x := by
  exact congrArg Subtype.val ((P.coordinateEquiv hP).apply_symm_apply x)

/-- Properness makes volume equal actual carrier cardinality. -/
theorem card_carrier_eq_volume (P : GAP d r) (hP : P.Proper) :
    P.carrier.card = P.volume := by
  rw [volume]
  calc
    P.carrier.card = Fintype.card {x // x ∈ P.carrier} := by simp
    _ = Fintype.card P.Coord := Fintype.card_congr (P.coordinateEquiv hP).symm
    _ = ∏ i, P.widths i := by simp

/-- The GAP envelope of a sum of exactly `k` displayed points.  In each
coordinate, the sum ranges from zero through `k * (width - 1)`. -/
def dilate (k : ℕ) (P : GAP d r) : GAP d r where
  offset := fun j => (k : ℤ) * P.offset j
  steps := P.steps
  widths := fun i => k * (P.widths i - 1) + 1
  width_pos := fun _ => Nat.zero_lt_succ _

@[simp]
theorem dilate_offset (k : ℕ) (P : GAP d r) :
    (P.dilate k).offset = fun j => (k : ℤ) * P.offset j := rfl

@[simp]
theorem dilate_steps (k : ℕ) (P : GAP d r) :
    (P.dilate k).steps = P.steps := rfl

@[simp]
theorem dilate_widths (k : ℕ) (P : GAP d r) (i : Fin r) :
    (P.dilate k).widths i = k * (P.widths i - 1) + 1 := rfl

@[simp]
theorem dilate_zero_carrier (P : GAP d r) :
    (P.dilate 0).carrier = {0} := by
  ext x
  simp only [mem_carrier_iff, Finset.mem_singleton]
  constructor
  · rintro ⟨n, rfl⟩
    ext j
    have hn : ∀ i, (n i : ℕ) = 0 := by
      intro i
      have hi := (n i).isLt
      have hi' : (n i : ℕ) < 1 := by
        simpa only [dilate_widths, zero_mul, zero_add] using hi
      omega
    simp [coordPoint, dilate, hn]
  · rintro rfl
    let n : (P.dilate 0).Coord := fun i => ⟨0, by simp⟩
    refine ⟨n, ?_⟩
    ext j
    simp [coordPoint, dilate, n]

@[simp]
theorem volume_dilate (k : ℕ) (P : GAP d r) :
    (P.dilate k).volume = ∏ i, (k * (P.widths i - 1) + 1) := rfl

/-- Each dilated width is bounded by `(k+1)` times the old width. -/
theorem dilate_width_le (k : ℕ) (P : GAP d r) (i : Fin r) :
    (P.dilate k).widths i ≤ (k + 1) * P.widths i := by
  change k * (P.widths i - 1) + 1 ≤ (k + 1) * P.widths i
  have hw : 1 ≤ P.widths i := P.width_pos i
  calc
    k * (P.widths i - 1) + 1 ≤ k * P.widths i + 1 :=
      Nat.add_le_add_right (Nat.mul_le_mul_left k (Nat.sub_le _ _)) 1
    _ ≤ k * P.widths i + P.widths i := Nat.add_le_add_left hw _
    _ = (k + 1) * P.widths i := by rw [Nat.add_mul, one_mul]

/-- The coarse polynomial volume bound for a dilation. -/
theorem volume_dilate_le (k : ℕ) (P : GAP d r) :
    (P.dilate k).volume ≤ (k + 1) ^ r * P.volume := by
  rw [volume_dilate, volume]
  calc
    (∏ i, (k * (P.widths i - 1) + 1)) ≤
        ∏ i, ((k + 1) * P.widths i) :=
      Finset.prod_le_prod (fun _ _ => Nat.zero_le _) fun i _ => P.dilate_width_le k i
    _ = (k + 1) ^ r * ∏ i, P.widths i := by
      rw [Finset.prod_mul_distrib]
      simp

/-- All subset sums of a finite set in an additive commutative monoid. -/
def subsetSums {α : Type*} [DecidableEq α] [AddCommMonoid α]
    (A : Finset α) : Finset α :=
  A.powerset.image fun S => ∑ x ∈ S, x

@[simp]
theorem mem_subsetSums_iff {α : Type*} [DecidableEq α] [AddCommMonoid α]
    {A : Finset α} {x : α} :
    x ∈ subsetSums A ↔ ∃ S ⊆ A, ∑ y ∈ S, y = x := by
  simp [subsetSums]

@[simp]
theorem zero_mem_subsetSums {α : Type*} [DecidableEq α] [AddCommMonoid α]
    (A : Finset α) :
    0 ∈ subsetSums A := by
  exact mem_subsetSums_iff.mpr ⟨∅, Finset.empty_subset _, by simp⟩

theorem card_subsetSums_le_pow_two {α : Type*} [DecidableEq α] [AddCommMonoid α]
    (A : Finset α) :
    (subsetSums A).card ≤ 2 ^ A.card := by
  rw [subsetSums]
  calc
    (A.powerset.image fun S => ∑ x ∈ S, x).card ≤ A.powerset.card :=
      Finset.card_image_le
    _ = 2 ^ A.card := Finset.card_powerset A

/-- The sum of `S` lies in the `|S|`-fold GAP envelope whenever every
summand lies in the original GAP.  No properness is needed: choose one
displayed representation for each summand. -/
theorem sum_mem_dilate_of_subset (P : GAP d r)
    {A S : Finset (LatticePoint d)}
    (hA : A ⊆ P.carrier) (hS : S ⊆ A) :
    (∑ x ∈ S, x) ∈ (P.dilate S.card).carrier := by
  classical
  let repr : LatticePoint d → P.Coord := fun x =>
    if hx : x ∈ S then
      Classical.choose (mem_carrier_iff.mp (hA (hS hx)))
    else P.zeroCoord
  have repr_spec (x : LatticePoint d) (hx : x ∈ S) : P.coordPoint (repr x) = x := by
    rw [show repr x = Classical.choose (mem_carrier_iff.mp (hA (hS hx))) by
      simp [repr, hx]]
    exact Classical.choose_spec (mem_carrier_iff.mp (hA (hS hx)))
  let total : Fin r → ℕ := fun i => ∑ x ∈ S, (repr x i : ℕ)
  have total_lt (i : Fin r) : total i < S.card * (P.widths i - 1) + 1 := by
    have hterm (x : LatticePoint d) (_hx : x ∈ S) :
        (repr x i : ℕ) ≤ P.widths i - 1 := by
      have hi := (repr x i).isLt
      omega
    calc
      total i ≤ ∑ _x ∈ S, (P.widths i - 1) := by
        exact Finset.sum_le_sum fun x hx => hterm x hx
      _ = S.card * (P.widths i - 1) := by simp
      _ < S.card * (P.widths i - 1) + 1 := Nat.lt_succ_self _
  let n : (P.dilate S.card).Coord := fun i => ⟨total i, total_lt i⟩
  refine mem_carrier_iff.mpr ⟨n, ?_⟩
  ext j
  have hdouble :
      (∑ i, (∑ x ∈ S, (repr x i : ℤ)) * P.steps i j) =
        ∑ x ∈ S, ∑ i, (repr x i : ℤ) * P.steps i j := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
  simp only [coordPoint, dilate, n, total, Finset.sum_apply]
  push_cast
  rw [hdouble]
  rw [show (S.card : ℤ) * P.offset j = ∑ _x ∈ S, P.offset j by simp]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  simpa only [coordPoint] using congrArg (fun y => y j) (repr_spec x hx)

/-- The finite union of all GAP envelopes involving at most `m` summands. -/
def sumDilationUnion (m : ℕ) (P : GAP d r) : Finset (LatticePoint d) :=
  (Finset.range (m + 1)).biUnion fun k => (P.dilate k).carrier

theorem mem_sumDilationUnion_of_mem_dilate (P : GAP d r) {m k : ℕ}
    (hk : k ≤ m) {x : LatticePoint d} (hx : x ∈ (P.dilate k).carrier) :
    x ∈ P.sumDilationUnion m := by
  rw [sumDilationUnion, Finset.mem_biUnion]
  exact ⟨k, Finset.mem_range.mpr (Nat.lt_succ_of_le hk), hx⟩

/-- Subset sums of a set contained in `P` lie in the union of the first
`|A|+1` fixed-cardinality dilation envelopes. -/
theorem subsetSums_subset_sumDilationUnion (P : GAP d r)
    {A : Finset (LatticePoint d)} (hA : A ⊆ P.carrier) :
    subsetSums A ⊆ P.sumDilationUnion A.card := by
  intro x hx
  rw [mem_subsetSums_iff] at hx
  obtain ⟨S, hS, rfl⟩ := hx
  exact P.mem_sumDilationUnion_of_mem_dilate
    (Finset.card_le_card hS) (P.sum_mem_dilate_of_subset hA hS)

/-- A general cardinal bound for the union of fixed-cardinality dilation
envelopes. -/
theorem card_sumDilationUnion_le_sum_volume (m : ℕ) (P : GAP d r) :
    (P.sumDilationUnion m).card ≤ ∑ k ∈ Finset.range (m + 1), (P.dilate k).volume := by
  rw [sumDilationUnion]
  exact Finset.card_biUnion_le.trans
    (Finset.sum_le_sum fun k _ => (P.dilate k).card_carrier_le_volume)

/-- Consequently, subset sums of a set in a GAP have polynomially bounded
cardinality (with a harmless extra factor for the possible subset sizes). -/
theorem card_subsetSums_le_sum_volume (P : GAP d r)
    {A : Finset (LatticePoint d)} (hA : A ⊆ P.carrier) :
    (subsetSums A).card ≤ ∑ k ∈ Finset.range (A.card + 1), (P.dilate k).volume := by
  exact (Finset.card_le_card (P.subsetSums_subset_sumDilationUnion hA)).trans
    (P.card_sumDilationUnion_le_sum_volume A.card)

end GAP
end Erdos186
