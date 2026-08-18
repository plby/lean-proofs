/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.GAP

/-!
# Minimal-volume fixed-rank bounding progressions for finite integer sets

This file supplies the bounding-box construction used in the
Conlon--Fox--Pham argument.  A rank-`d` bounding GAP for a finite set
`A ⊆ ℤ` is a `GAP 1 d` whose carrier contains the canonical copy of `A`
in the one-dimensional integer lattice.

For every positive rank such presentations exist.  Indeed, a symmetric
integer interval containing `A` can be put in the first GAP coordinate and
the remaining coordinates can be padded with width one.  We then use the
well-ordering of `ℕ` to choose a presentation of least displayed volume.
No finiteness assertion about the collection of all GAP presentations is
needed.

The minimizing presentation need not be supplied with a proof of properness.
When properness is available, its unique coordinate representation gives the
usual identification map from `A` to `ℤ^d`; this map is injective.
-/

namespace Erdos186.CFP.BoundingBox

open scoped BigOperators

/-! ## Integers as points of the one-dimensional lattice -/

/-- The canonical copy of an integer in `LatticePoint 1`. -/
def intPoint (z : ℤ) : LatticePoint 1 :=
  fun _ ↦ z

@[simp]
theorem intPoint_apply (z : ℤ) (i : Fin 1) : intPoint z i = z :=
  rfl

theorem intPoint_injective : Function.Injective intPoint := by
  intro x y h
  exact congrFun h 0

@[simp]
theorem intPoint_inj {x y : ℤ} : intPoint x = intPoint y ↔ x = y :=
  intPoint_injective.eq_iff

/-! ## Bounding GAPs -/

/-- A rank-`d` GAP in the integers contains every point of `A`. -/
def IsBoundingGAP {d : ℕ} (A : Finset ℤ) (P : GAP 1 d) : Prop :=
  ∀ z : {z // z ∈ A}, intPoint z ∈ P.carrier

/-- A rank-`d` GAP together with its bounding property. -/
structure BoundingGAP (A : Finset ℤ) (d : ℕ) where
  progression : GAP 1 d
  bounds : IsBoundingGAP A progression

namespace BoundingGAP

variable {A : Finset ℤ} {d : ℕ}

theorem mem_carrier (B : BoundingGAP A d) {z : ℤ} (hz : z ∈ A) :
    intPoint z ∈ B.progression.carrier :=
  B.bounds ⟨z, hz⟩

theorem zero_mem_carrier (B : BoundingGAP A d) (hzero : 0 ∈ A) :
    0 ∈ B.progression.carrier := by
  change intPoint 0 ∈ B.progression.carrier
  exact B.mem_carrier hzero

/-- Every bounding GAP has positive displayed volume. -/
theorem volume_pos (B : BoundingGAP A d) : 0 < B.progression.volume := by
  rw [GAP.volume]
  exact Finset.prod_pos fun i _ ↦ B.progression.width_pos i

/-! ## Identification in a proper presentation -/

/-- The integral coordinate vector of an element of the bounded set in a
proper bounding presentation. -/
noncomputable def identificationMap (B : BoundingGAP A d)
    (hproper : B.progression.Proper) :
    {z // z ∈ A} → (Fin d → ℤ) :=
  fun z i ↦
    (B.progression.coordinateMap hproper
      ⟨intPoint z, B.bounds z⟩ i : ℕ)

/-- The coordinate used by the identification map evaluates back to the
original integer point. -/
@[simp]
theorem coordPoint_coordinateMap (B : BoundingGAP A d)
    (hproper : B.progression.Proper) (z : {z // z ∈ A}) :
    B.progression.coordPoint
        (B.progression.coordinateMap hproper ⟨intPoint z, B.bounds z⟩) =
      intPoint z := by
  exact B.progression.coordPoint_coordinateMap hproper
    ⟨intPoint z, B.bounds z⟩

@[simp]
theorem identificationMap_apply (B : BoundingGAP A d)
    (hproper : B.progression.Proper) (z : {z // z ∈ A}) (i : Fin d) :
    B.identificationMap hproper z i =
      (B.progression.coordinateMap hproper
        ⟨intPoint z, B.bounds z⟩ i : ℕ) :=
  rfl

/-- Proper GAP coordinates identify distinct elements of `A`. -/
theorem identificationMap_injective (B : BoundingGAP A d)
    (hproper : B.progression.Proper) :
    Function.Injective (B.identificationMap hproper) := by
  intro x y hxy
  have hcoord :
      B.progression.coordinateMap hproper ⟨intPoint x, B.bounds x⟩ =
        B.progression.coordinateMap hproper ⟨intPoint y, B.bounds y⟩ := by
    funext i
    apply Fin.ext
    have hi := congrFun hxy i
    simp only [identificationMap_apply] at hi
    exact Int.ofNat_inj.mp hi
  apply Subtype.ext
  apply intPoint_injective
  rw [← B.coordPoint_coordinateMap hproper x,
    ← B.coordPoint_coordinateMap hproper y, hcoord]

end BoundingGAP

/-! ## An explicit padded interval -/

/-- A radius which bounds the absolute value of every member of `A`.
The sum is chosen instead of a maximum to make the empty-set case harmless. -/
def radius (A : Finset ℤ) : ℕ :=
  ∑ z ∈ A, z.natAbs

theorem natAbs_le_radius {A : Finset ℤ} {z : ℤ} (hz : z ∈ A) :
    z.natAbs ≤ radius A := by
  rw [radius]
  exact Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hz

/-- The interval `[-R,R]` in the first coordinate, padded by `tailRank`
width-one coordinates.  Its total rank is `tailRank + 1`. -/
def paddedInterval (tailRank R : ℕ) : GAP 1 tailRank.succ where
  offset := intPoint (-(R : ℤ))
  steps := Fin.cases (intPoint 1) (fun _ ↦ 0)
  widths := Fin.cases (2 * R + 1) (fun _ ↦ 1)
  width_pos := Fin.cases (Nat.zero_lt_succ (2 * R))
    (fun _ ↦ Nat.zero_lt_succ 0)

@[simp]
theorem paddedInterval_offset (tailRank R : ℕ) :
    (paddedInterval tailRank R).offset = intPoint (-(R : ℤ)) :=
  rfl

@[simp]
theorem paddedInterval_width_zero (tailRank R : ℕ) :
    (paddedInterval tailRank R).widths 0 = 2 * R + 1 :=
  rfl

@[simp]
theorem paddedInterval_volume (tailRank R : ℕ) :
    (paddedInterval tailRank R).volume = 2 * R + 1 := by
  simp [GAP.volume, paddedInterval, Fin.prod_univ_succ]

/-- Every integer whose absolute value is at most `R` belongs to the explicit
padded interval. -/
theorem intPoint_mem_paddedInterval {tailRank R : ℕ} {z : ℤ}
    (hz : z.natAbs ≤ R) :
    intPoint z ∈ (paddedInterval tailRank R).carrier := by
  have habs : (z.natAbs : ℤ) ≤ (R : ℤ) := by exact_mod_cast hz
  have hupper : z ≤ (R : ℤ) := Int.le_natAbs.trans habs
  have hlower : -(R : ℤ) ≤ z := by
    rcases Int.natAbs_eq z with hz' | hz'
    · rw [hz']
      omega
    · rw [hz']
      omega
  have hnonneg : 0 ≤ z + (R : ℤ) := by omega
  have hltInt : z + (R : ℤ) < (2 * R + 1 : ℕ) := by
    exact_mod_cast (show z + (R : ℤ) < (2 * R + 1 : ℕ) by omega)
  have hlt : (z + (R : ℤ)).toNat < 2 * R + 1 := by
    have hltInt' := hltInt
    rw [← Int.toNat_of_nonneg hnonneg] at hltInt'
    exact_mod_cast hltInt'
  let n : (paddedInterval tailRank R).Coord :=
    Fin.cases ⟨(z + (R : ℤ)).toNat, hlt⟩
      (fun _ ↦ ⟨0, by simp [paddedInterval]⟩)
  refine GAP.mem_carrier_iff.mpr ⟨n, ?_⟩
  funext j
  change -(R : ℤ) + ∑ i : Fin tailRank.succ,
      ((n i : ℕ) : ℤ) *
        (paddedInterval tailRank R).steps i j = z
  rw [Fin.sum_univ_succ]
  simp [paddedInterval, n]
  change -(R : ℤ) + ((z + (R : ℤ)).toNat : ℤ) = z
  rw [Int.toNat_of_nonneg hnonneg]
  omega

theorem isBoundingGAP_paddedInterval (A : Finset ℤ) (tailRank : ℕ) :
    IsBoundingGAP A (paddedInterval tailRank (radius A)) := by
  rintro ⟨z, hz⟩
  exact intPoint_mem_paddedInterval (natAbs_le_radius hz)

/-- Positive-rank bounding presentations always exist. -/
theorem boundingGAP_nonempty (A : Finset ℤ) {d : ℕ} (hd : 0 < d) :
    Nonempty (BoundingGAP A d) := by
  cases d with
  | zero => omega
  | succ tailRank =>
      exact ⟨⟨paddedInterval tailRank (radius A),
        isBoundingGAP_paddedInterval A tailRank⟩⟩

/-! ## The least-volume bounding presentation -/

/-- The natural number `v` occurs as the volume of a rank-`d` bounding GAP. -/
def HasBoundingVolume (A : Finset ℤ) (d v : ℕ) : Prop :=
  ∃ B : BoundingGAP A d, B.progression.volume = v

theorem exists_boundingVolume (A : Finset ℤ) {d : ℕ} (hd : 0 < d) :
    ∃ v, HasBoundingVolume A d v := by
  let B : BoundingGAP A d := Classical.choice (boundingGAP_nonempty A hd)
  exact ⟨B.progression.volume, B, rfl⟩

/-- The least displayed volume of a rank-`d` GAP containing `A`. -/
noncomputable def minimalBoundingVolume (A : Finset ℤ) (d : ℕ)
    (hd : 0 < d) : ℕ :=
  by
    classical
    exact Nat.find (exists_boundingVolume A hd)

theorem minimalBoundingVolume_attained (A : Finset ℤ) (d : ℕ)
    (hd : 0 < d) :
    HasBoundingVolume A d (minimalBoundingVolume A d hd) :=
  by
    classical
    exact Nat.find_spec (exists_boundingVolume A hd)

/-- A canonical choice of a least-volume rank-`d` GAP containing `A`. -/
noncomputable def dBoundingBox (A : Finset ℤ) (d : ℕ) (hd : 0 < d) :
    BoundingGAP A d :=
  Classical.choose (minimalBoundingVolume_attained A d hd)

/-- Alias emphasizing the optimizing property of `dBoundingBox`. -/
noncomputable abbrev minimalBoundingGAP (A : Finset ℤ) (d : ℕ)
    (hd : 0 < d) : BoundingGAP A d :=
  dBoundingBox A d hd

theorem dBoundingBox_volume_eq (A : Finset ℤ) (d : ℕ) (hd : 0 < d) :
    (dBoundingBox A d hd).progression.volume = minimalBoundingVolume A d hd :=
  Classical.choose_spec (minimalBoundingVolume_attained A d hd)

theorem dBoundingBox_bounds (A : Finset ℤ) (d : ℕ) (hd : 0 < d) :
    IsBoundingGAP A (dBoundingBox A d hd).progression :=
  (dBoundingBox A d hd).bounds

theorem dBoundingBox_mem_carrier (A : Finset ℤ) (d : ℕ) (hd : 0 < d)
    {z : ℤ} (hz : z ∈ A) :
    intPoint z ∈ (dBoundingBox A d hd).progression.carrier :=
  (dBoundingBox A d hd).mem_carrier hz

theorem dBoundingBox_zero_mem (A : Finset ℤ) (d : ℕ) (hd : 0 < d)
    (hzero : 0 ∈ A) :
    0 ∈ (dBoundingBox A d hd).progression.carrier :=
  (dBoundingBox A d hd).zero_mem_carrier hzero

/-- The selected bounding GAP has no larger displayed volume than any other
rank-`d` GAP containing `A`. -/
theorem dBoundingBox_minimal (A : Finset ℤ) (d : ℕ) (hd : 0 < d)
    (P : GAP 1 d) (hP : IsBoundingGAP A P) :
    (dBoundingBox A d hd).progression.volume ≤ P.volume := by
  classical
  rw [dBoundingBox_volume_eq]
  exact Nat.find_min' (exists_boundingVolume A hd) ⟨⟨P, hP⟩, rfl⟩

theorem dBoundingBox_minimal' (A : Finset ℤ) (d : ℕ) (hd : 0 < d)
    (B : BoundingGAP A d) :
    (dBoundingBox A d hd).progression.volume ≤ B.progression.volume :=
  dBoundingBox_minimal A d hd B.progression B.bounds

theorem dBoundingBox_volume_pos (A : Finset ℤ) (d : ℕ) (hd : 0 < d) :
    0 < (dBoundingBox A d hd).progression.volume :=
  (dBoundingBox A d hd).volume_pos

/-- The explicit symmetric interval gives a concrete upper bound for the
minimal volume. -/
theorem dBoundingBox_volume_le_radius (A : Finset ℤ) (d : ℕ)
    (hd : 0 < d) :
    (dBoundingBox A d hd).progression.volume ≤ 2 * radius A + 1 := by
  cases d with
  | zero => omega
  | succ tailRank =>
      simpa using
        dBoundingBox_minimal A (tailRank + 1) (by omega)
          (paddedInterval tailRank (radius A))
          (isBoundingGAP_paddedInterval A tailRank)

/-! ## Comparison lemmas -/

/-- Enlarging the finite set cannot decrease the least possible bounding
volume (at fixed positive rank). -/
theorem dBoundingBox_volume_mono {A B : Finset ℤ} (d : ℕ) (hd : 0 < d)
    (hBA : B ⊆ A) :
    (dBoundingBox B d hd).progression.volume ≤
      (dBoundingBox A d hd).progression.volume := by
  apply dBoundingBox_minimal B d hd (dBoundingBox A d hd).progression
  intro z
  exact dBoundingBox_mem_carrier A d hd (hBA z.property)

/-- The one-sided interval `[0,n)` in the first coordinate, padded by
`tailRank` width-one coordinates. -/
def initialInterval (tailRank n : ℕ) (hn : 0 < n) : GAP 1 tailRank.succ where
  offset := 0
  steps := Fin.cases (intPoint 1) (fun _ ↦ 0)
  widths := Fin.cases n (fun _ ↦ 1)
  width_pos := Fin.cases hn (fun _ ↦ Nat.zero_lt_succ 0)

@[simp]
theorem initialInterval_volume (tailRank n : ℕ) (hn : 0 < n) :
    (initialInterval tailRank n hn).volume = n := by
  simp [GAP.volume, initialInterval, Fin.prod_univ_succ]

/-- Every integer in `[0,n)` belongs to the explicit one-sided padded
interval. -/
theorem intPoint_mem_initialInterval {tailRank n : ℕ} (hn : 0 < n) {z : ℤ}
    (hz0 : 0 ≤ z) (hzn : z < (n : ℤ)) :
    intPoint z ∈ (initialInterval tailRank n hn).carrier := by
  have hzcast : ((z.toNat : ℕ) : ℤ) = z := Int.toNat_of_nonneg hz0
  have hzlt : z.toNat < n := by
    exact_mod_cast (hzcast.symm ▸ hzn)
  let c : (initialInterval tailRank n hn).Coord :=
    Fin.cases ⟨z.toNat, hzlt⟩
      (fun _ ↦ ⟨0, by simp [initialInterval]⟩)
  refine GAP.mem_carrier_iff.mpr ⟨c, ?_⟩
  funext j
  change (0 : ℤ) + ∑ i : Fin tailRank.succ,
      ((c i : ℕ) : ℤ) *
        (initialInterval tailRank n hn).steps i j = z
  rw [Fin.sum_univ_succ]
  simp [initialInterval, c]
  change ((z.toNat : ℕ) : ℤ) = z
  exact hzcast

theorem isBoundingGAP_initialInterval {A : Finset ℤ} {n : ℕ} (hn : 0 < n)
    (hA : ∀ z ∈ A, 0 ≤ z ∧ z < (n : ℤ)) (tailRank : ℕ) :
    IsBoundingGAP A (initialInterval tailRank n hn) := by
  rintro ⟨z, hz⟩
  exact intPoint_mem_initialInterval hn (hA z hz).1 (hA z hz).2

/-- If `0 ∈ A ⊆ [0,n)`, the least-volume positive-rank bounding GAP has
volume at most `n`.  The `0 ∈ A` hypothesis is essential at `n = 0`: for an
empty set every GAP still has positive displayed volume. -/
theorem dBoundingBox_volume_le_of_mem_Ico (A : Finset ℤ) (d n : ℕ)
    (hd : 0 < d) (hzero : 0 ∈ A)
    (hA : ∀ z ∈ A, 0 ≤ z ∧ z < (n : ℤ)) :
    (dBoundingBox A d hd).progression.volume ≤ n := by
  have hn : 0 < n := by
    have := (hA 0 hzero).2
    exact_mod_cast this
  cases d with
  | zero => omega
  | succ tailRank =>
      simpa using
        dBoundingBox_minimal A tailRank.succ (by omega)
          (initialInterval tailRank n hn)
          (isBoundingGAP_initialInterval hn hA tailRank)

end Erdos186.CFP.BoundingBox
