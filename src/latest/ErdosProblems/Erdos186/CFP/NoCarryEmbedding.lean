/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Witness
import ErdosProblems.Erdos186.CFP.SProper

/-!
# A bounded no-carry embedding of an integer lattice into the integers

For a base `b`, `hornerEncode d b` sends

`(x 0, ..., x (d-1))`

to `x 0 + b * x 1 + ... + b^(d-1) * x (d-1)`.  It is an additive map.
Although no additive embedding `ℤ^d → ℤ` exists when `d > 1`, this map is
injective on every set whose pairwise coordinate differences have absolute
value strictly less than `b`.  Taking

`b = 2 * s * R + 1`

therefore reflects all additive relations between sums of at most `s` points
whose coordinates have absolute value at most `R`.  The final section applies
this with the canonical coordinate radius of a finite set.
-/

namespace Erdos186.CFP.NoCarryEmbedding

open scoped BigOperators

/-! ## The mixed-radix homomorphism -/

/-- Signed Horner encoding in base `b`.  Signed digits are intentional: the
no-carry argument below only uses a bound on their absolute values. -/
def hornerEncode : (d : ℕ) → ℕ → LatticePoint d → ℤ
  | 0, _, _ => 0
  | d + 1, b, x =>
      x 0 + (b : ℤ) * hornerEncode d b (fun i => x i.succ)

@[simp]
theorem hornerEncode_zero_dim (b : ℕ) (x : LatticePoint 0) :
    hornerEncode 0 b x = 0 := rfl

@[simp]
theorem hornerEncode_succ (d b : ℕ) (x : LatticePoint (d + 1)) :
    hornerEncode (d + 1) b x =
      x 0 + (b : ℤ) * hornerEncode d b (fun i => x i.succ) := rfl

@[simp]
theorem hornerEncode_zero (d b : ℕ) :
    hornerEncode d b (0 : LatticePoint d) = 0 := by
  induction d with
  | zero => rfl
  | succ d ih =>
      rw [hornerEncode_succ]
      change 0 + (b : ℤ) * hornerEncode d b 0 = 0
      simp [ih]

@[simp]
theorem hornerEncode_add (d b : ℕ) (x y : LatticePoint d) :
    hornerEncode d b (x + y) = hornerEncode d b x + hornerEncode d b y := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [hornerEncode_succ, hornerEncode_succ, hornerEncode_succ]
      have htail :
          (fun i : Fin d => (x + y) i.succ) =
            (fun i : Fin d => x i.succ) + (fun i : Fin d => y i.succ) := rfl
      rw [htail, ih]
      simp only [Pi.add_apply]
      ring

/-- `hornerEncode` as an additive homomorphism. -/
def hornerHom (d b : ℕ) : LatticePoint d →+ ℤ where
  toFun := hornerEncode d b
  map_zero' := hornerEncode_zero d b
  map_add' := hornerEncode_add d b

/-- Lattice-valued form of the signed Horner homomorphism. -/
def hornerLatticeHom (d b : ℕ) : LatticePoint d →+ LatticePoint 1 where
  toFun x := fun _ ↦ hornerHom d b x
  map_zero' := by ext i; exact (hornerHom d b).map_zero
  map_add' x y := by ext i; exact (hornerHom d b).map_add x y

@[simp]
theorem hornerLatticeHom_apply (d b : ℕ) (x : LatticePoint d) (i : Fin 1) :
    hornerLatticeHom d b x i = hornerEncode d b x := rfl

@[simp]
theorem hornerHom_apply (d b : ℕ) (x : LatticePoint d) :
    hornerHom d b x = hornerEncode d b x := rfl

@[simp]
theorem hornerEncode_neg (d b : ℕ) (x : LatticePoint d) :
    hornerEncode d b (-x) = -hornerEncode d b x := by
  exact (hornerHom d b).map_neg x

@[simp]
theorem hornerEncode_sub (d b : ℕ) (x y : LatticePoint d) :
    hornerEncode d b (x - y) = hornerEncode d b x - hornerEncode d b y := by
  exact (hornerHom d b).map_sub x y

theorem hornerEncode_sum {ι : Type*} (d b : ℕ) (S : Finset ι)
    (f : ι → LatticePoint d) :
    hornerEncode d b (∑ i ∈ S, f i) =
      ∑ i ∈ S, hornerEncode d b (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih => simp [ha, hornerEncode_add, ih]

/-! ## The no-carry uniqueness lemma -/

/-- A multiple of a positive integer base whose absolute value is smaller
than that base must vanish. -/
theorem eq_zero_of_dvd_of_natAbs_lt {b : ℕ} {z : ℤ}
    (_hb : 0 < b) (hdiv : (b : ℤ) ∣ z) (hz : z.natAbs < b) : z = 0 := by
  obtain ⟨k, rfl⟩ := hdiv
  by_cases hk : k = 0
  · simp [hk]
  exfalso
  rw [Int.natAbs_mul, Int.natAbs_natCast] at hz
  have hkpos : 0 < k.natAbs := Int.natAbs_pos.mpr hk
  have hble : b ≤ b * k.natAbs := by
    calc
      b = b * 1 := by simp
      _ ≤ b * k.natAbs := Nat.mul_le_mul_left b hkpos
  exact (not_lt_of_ge hble) hz

/-- If every digit has absolute value strictly less than the positive base,
a zero Horner encoding has only zero digits. -/
theorem eq_zero_of_hornerEncode_eq_zero :
    ∀ {d b : ℕ} (x : LatticePoint d),
      0 < b →
      (∀ i, (x i).natAbs < b) →
      hornerEncode d b x = 0 →
      x = 0 := by
  intro d
  induction d with
  | zero =>
      intro b x _hb _hx _henc
      funext i
      exact Fin.elim0 i
  | succ d ih =>
      intro b x hb hx henc
      let tail : LatticePoint d := fun i => x i.succ
      change x 0 + (b : ℤ) * hornerEncode d b tail = 0 at henc
      have hdiv : (b : ℤ) ∣ x 0 := by
        refine ⟨-hornerEncode d b tail, ?_⟩
        rw [mul_neg]
        exact eq_neg_of_add_eq_zero_left henc
      have hx0 : x 0 = 0 :=
        eq_zero_of_dvd_of_natAbs_lt hb hdiv (hx 0)
      have hbne : (b : ℤ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
      have htail_enc : hornerEncode d b tail = 0 := by
        rw [hx0, zero_add] at henc
        exact (mul_eq_zero.mp henc).resolve_left hbne
      have htail : tail = 0 :=
        ih tail hb (fun i => hx i.succ) htail_enc
      funext i
      refine Fin.cases hx0 (fun j => ?_) i
      exact congrFun htail j

/-- The Horner encoding reflects equality whenever every coordinate of the
difference lies in the open interval `(-b,b)`. -/
theorem eq_of_hornerEncode_eq_of_natAbs_sub_lt {d b : ℕ}
    {x y : LatticePoint d} (hb : 0 < b)
    (hbound : ∀ i, (x i - y i).natAbs < b)
    (henc : hornerEncode d b x = hornerEncode d b y) :
    x = y := by
  have hzero : hornerEncode d b (x - y) = 0 := by
    rw [hornerEncode_sub, henc, sub_self]
  have hxy : x - y = 0 :=
    eq_zero_of_hornerEncode_eq_zero (x - y) hb (by simpa using hbound) hzero
  exact sub_eq_zero.mp hxy

/-- The symmetric coordinate window of radius `M`. -/
def coordinateWindow (d M : ℕ) : Set (LatticePoint d) :=
  {x | ∀ i, (x i).natAbs ≤ M}

/-- Finite version of the symmetric coordinate window. -/
noncomputable def coordinateFinset (d M : ℕ) : Finset (LatticePoint d) :=
  Fintype.piFinset fun _ : Fin d ↦
    Finset.Icc (-(M : ℤ)) (M : ℤ)

@[simp]
theorem card_coordinateFinset (d M : ℕ) :
    (coordinateFinset d M).card = (2 * M + 1) ^ d := by
  simp only [coordinateFinset, Fintype.card_piFinset, Int.card_Icc,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  omega

@[simp]
theorem mem_coordinateWindow {d M : ℕ} {x : LatticePoint d} :
    x ∈ coordinateWindow d M ↔ ∀ i, (x i).natAbs ≤ M :=
  Iff.rfl

/-- Coordinate windows are monotone in their radius. -/
theorem coordinateWindow_mono {d M N : ℕ} (hMN : M ≤ N) :
    coordinateWindow d M ⊆ coordinateWindow d N := by
  intro x hx i
  exact (hx i).trans hMN

/-- The set-theoretic coordinate window is carried by its finite box. -/
theorem mem_coordinateFinset_of_mem_coordinateWindow
    {d M : ℕ} {x : LatticePoint d}
    (hx : x ∈ coordinateWindow d M) : x ∈ coordinateFinset d M := by
  rw [coordinateFinset]
  simp only [Fintype.mem_piFinset, Finset.mem_Icc]
  intro i
  have hcast : ((x i).natAbs : ℤ) ≤ (M : ℤ) := by
    exact_mod_cast hx i
  have habs : |x i| ≤ (M : ℤ) := by
    simpa only [Int.abs_eq_natAbs] using hcast
  exact abs_le.mp habs

/-- A base larger than twice the window radius makes the Horner map
injective on the whole symmetric coordinate window. -/
theorem hornerLatticeHom_injOn_coordinateWindow {d b M : ℕ}
    (hb : 0 < b) (hwidth : 2 * M < b) :
    Set.InjOn (hornerLatticeHom d b) (coordinateWindow d M) := by
  intro x hx y hy hxy
  apply eq_of_hornerEncode_eq_of_natAbs_sub_lt hb
  · intro i
    calc
      (x i - y i).natAbs ≤ (x i).natAbs + (y i).natAbs :=
        Int.natAbs_sub_le _ _
      _ ≤ M + M := Nat.add_le_add (hx i) (hy i)
      _ = 2 * M := by omega
      _ < b := hwidth
  · exact congrFun hxy 0

/-! ## Bounded sums -/

/-- Coordinatewise triangle inequality for a finite lattice sum. -/
theorem natAbs_sum_coord_le_card_mul {d : ℕ} {S : Finset (LatticePoint d)}
    {R : ℕ} (hR : ∀ x ∈ S, ∀ i, (x i).natAbs ≤ R) (i : Fin d) :
    ((∑ x ∈ S, x) i).natAbs ≤ S.card * R := by
  calc
    ((∑ x ∈ S, x) i).natAbs = (∑ x ∈ S, x i).natAbs := by simp
    _ ≤ ∑ x ∈ S, (x i).natAbs := Int.natAbs_sum_le _ _
    _ ≤ ∑ _x ∈ S, R := Finset.sum_le_sum fun x hx => hR x hx i
    _ = S.card * R := by simp

/-- Explicit base large enough to distinguish two sums of at most `s`
points with coordinate radius `R`. -/
def relationBase (s R : ℕ) : ℕ := 2 * s * R + 1

@[simp]
theorem relationBase_pos (s R : ℕ) : 0 < relationBase s R := by
  simp [relationBase]

theorem natAbs_sub_sum_coord_lt_relationBase {d s R : ℕ}
    {S T : Finset (LatticePoint d)}
    (hS : S.card ≤ s) (hT : T.card ≤ s)
    (hR : ∀ x ∈ S ∪ T, ∀ i, (x i).natAbs ≤ R) (i : Fin d) :
    (((∑ x ∈ S, x) i) - ((∑ x ∈ T, x) i)).natAbs < relationBase s R := by
  have hRS : ∀ x ∈ S, ∀ j, (x j).natAbs ≤ R := by
    intro x hx
    exact hR x (Finset.mem_union_left T hx)
  have hRT : ∀ x ∈ T, ∀ j, (x j).natAbs ≤ R := by
    intro x hx
    exact hR x (Finset.mem_union_right S hx)
  calc
    (((∑ x ∈ S, x) i) - ((∑ x ∈ T, x) i)).natAbs ≤
        ((∑ x ∈ S, x) i).natAbs + ((∑ x ∈ T, x) i).natAbs :=
      Int.natAbs_sub_le _ _
    _ ≤ S.card * R + T.card * R :=
      Nat.add_le_add
        (natAbs_sum_coord_le_card_mul hRS i)
        (natAbs_sum_coord_le_card_mul hRT i)
    _ ≤ s * R + s * R :=
      Nat.add_le_add (Nat.mul_le_mul_right R hS) (Nat.mul_le_mul_right R hT)
    _ = 2 * s * R := by ring
    _ < relationBase s R := Nat.lt_succ_self _

/-- No-carry reflection for two bounded finite sums.  The reverse implication
is just additivity; the forward implication is the substantive statement. -/
theorem sum_hornerEncode_eq_iff {d s R : ℕ}
    {S T : Finset (LatticePoint d)}
    (hS : S.card ≤ s) (hT : T.card ≤ s)
    (hR : ∀ x ∈ S ∪ T, ∀ i, (x i).natAbs ≤ R) :
    (∑ x ∈ S, hornerEncode d (relationBase s R) x) =
          ∑ x ∈ T, hornerEncode d (relationBase s R) x ↔
      ∑ x ∈ S, x = ∑ x ∈ T, x := by
  rw [← hornerEncode_sum, ← hornerEncode_sum]
  constructor
  · intro h
    apply eq_of_hornerEncode_eq_of_natAbs_sub_lt (relationBase_pos s R) _ h
    intro i
    exact natAbs_sub_sum_coord_lt_relationBase hS hT hR i
  · exact fun h => congrArg _ h

/-! ## The canonical embedding attached to a finite set -/

/-- The largest absolute value of any coordinate occurring in `A`. -/
def coordinateRadius {d : ℕ} (A : Finset (LatticePoint d)) : ℕ :=
  A.sup fun x => Finset.univ.sup fun i => (x i).natAbs

theorem natAbs_le_coordinateRadius {d : ℕ} {A : Finset (LatticePoint d)}
    {x : LatticePoint d} (hx : x ∈ A) (i : Fin d) :
    (x i).natAbs ≤ coordinateRadius A := by
  exact (Finset.le_sup (s := Finset.univ) (f := fun j : Fin d => (x j).natAbs)
    (Finset.mem_univ i)).trans
      (Finset.le_sup (s := A)
        (f := fun y : LatticePoint d => Finset.univ.sup fun j => (y j).natAbs) hx)

/-- The canonical base which reflects relations between sums of at most `s`
elements of `A`. -/
def noCarryBase {d : ℕ} (A : Finset (LatticePoint d)) (s : ℕ) : ℕ :=
  relationBase s (coordinateRadius A)

/-- The canonical bounded no-carry homomorphism associated to `A` and `s`. -/
def noCarryHom {d : ℕ} (A : Finset (LatticePoint d)) (s : ℕ) :
    LatticePoint d →+ ℤ :=
  hornerHom d (noCarryBase A s)

/-- The canonical no-carry homomorphism with its integer value represented
in the repository's one-dimensional lattice type. -/
def noCarryLatticeHom {d : ℕ} (A : Finset (LatticePoint d)) (s : ℕ) :
    LatticePoint d →+ LatticePoint 1 where
  toFun x := fun _ ↦ noCarryHom A s x
  map_zero' := by ext i; exact (noCarryHom A s).map_zero
  map_add' x y := by ext i; exact (noCarryHom A s).map_add x y

@[simp]
theorem noCarryLatticeHom_apply {d : ℕ}
    (A : Finset (LatticePoint d)) (s : ℕ) (x : LatticePoint d)
    (i : Fin 1) :
    noCarryLatticeHom A s x i = noCarryHom A s x := rfl

@[simp]
theorem noCarryHom_apply {d : ℕ} (A : Finset (LatticePoint d)) (s : ℕ)
    (x : LatticePoint d) :
    noCarryHom A s x = hornerEncode d (noCarryBase A s) x := rfl

/-- The canonical map reflects every relation between two subset sums of at
most `s` elements of `A`. -/
theorem subset_sum_relation_iff {d s : ℕ} {A S T : Finset (LatticePoint d)}
    (hSA : S ⊆ A) (hTA : T ⊆ A) (hS : S.card ≤ s) (hT : T.card ≤ s) :
    (∑ x ∈ S, noCarryHom A s x) = ∑ x ∈ T, noCarryHom A s x ↔
      ∑ x ∈ S, x = ∑ x ∈ T, x := by
  apply sum_hornerEncode_eq_iff hS hT
  intro x hx i
  rcases Finset.mem_union.mp hx with hx | hx
  · exact natAbs_le_coordinateRadius (hSA hx) i
  · exact natAbs_le_coordinateRadius (hTA hx) i

/-- Subset sums using at most `s` summands. -/
def boundedSubsetSums {α : Type*} [DecidableEq α] [AddCommMonoid α]
    (A : Finset α) (s : ℕ) : Finset α :=
  (A.powerset.filter fun S => S.card ≤ s).image fun S => ∑ x ∈ S, x

@[simp]
theorem mem_boundedSubsetSums_iff {α : Type*} [DecidableEq α]
    [AddCommMonoid α] {A : Finset α} {s : ℕ} {x : α} :
    x ∈ boundedSubsetSums A s ↔
      ∃ S ⊆ A, S.card ≤ s ∧ ∑ y ∈ S, y = x := by
  rw [boundedSubsetSums, Finset.mem_image]
  constructor
  · rintro ⟨S, hS, rfl⟩
    rw [Finset.mem_filter, Finset.mem_powerset] at hS
    exact ⟨S, hS.1, hS.2, rfl⟩
  · rintro ⟨S, hSA, hScard, rfl⟩
    exact ⟨S, by simp [hSA, hScard], rfl⟩

/-- The no-carry map is injective on all bounded subset sums.  This is the
set-level reflection statement used in transport arguments. -/
theorem noCarryHom_injOn_boundedSubsetSums {d s : ℕ}
    (A : Finset (LatticePoint d)) :
    Set.InjOn (noCarryHom A s) (boundedSubsetSums A s : Set (LatticePoint d)) := by
  intro x hx y hy hxy
  obtain ⟨S, hSA, hScard, rfl⟩ := mem_boundedSubsetSums_iff.mp hx
  obtain ⟨T, hTA, hTcard, rfl⟩ := mem_boundedSubsetSums_iff.mp hy
  apply (subset_sum_relation_iff hSA hTA hScard hTcard).mp
  simpa only [map_sum] using hxy

/-- Lattice-valued form of bounded no-carry injectivity. -/
theorem noCarryLatticeHom_injOn_boundedSubsetSums {d s : ℕ}
    (A : Finset (LatticePoint d)) :
    Set.InjOn (noCarryLatticeHom A s)
      (boundedSubsetSums A s : Set (LatticePoint d)) := by
  intro x hx y hy hxy
  apply noCarryHom_injOn_boundedSubsetSums A hx hy
  exact congrFun hxy 0

/-- Consequently encoding does not change the number of bounded subset sums. -/
theorem card_image_noCarryHom_boundedSubsetSums {d s : ℕ}
    (A : Finset (LatticePoint d)) :
    ((boundedSubsetSums A s).image (noCarryHom A s)).card =
      (boundedSubsetSums A s).card := by
  exact Finset.card_image_iff.mpr (noCarryHom_injOn_boundedSubsetSums A)

/-- Subset sums of a set of at most `s` elements are among the bounded
subset sums of any containing set. -/
theorem subsetSums_subset_boundedSubsetSums {d s : ℕ}
    {A R : Finset (LatticePoint d)} (hRA : R ⊆ A) (hRcard : R.card ≤ s) :
    GAP.subsetSums R ⊆ boundedSubsetSums A s := by
  intro x hx
  obtain ⟨S, hSR, hsum⟩ := GAP.mem_subsetSums_iff.mp hx
  exact mem_boundedSubsetSums_iff.mpr
    ⟨S, hSR.trans hRA, (Finset.card_le_card hSR).trans hRcard, hsum⟩

/-- Every sum of at most `s` members of `A` lies in the coordinate window
of radius `s * coordinateRadius A`, and hence in any larger window. -/
theorem boundedSubsetSums_subset_coordinateWindow {d s M : ℕ}
    (A : Finset (LatticePoint d))
    (hM : s * coordinateRadius A ≤ M) :
    (boundedSubsetSums A s : Set (LatticePoint d)) ⊆
      coordinateWindow d M := by
  intro x hx
  obtain ⟨S, hSA, hScard, hsum⟩ := mem_boundedSubsetSums_iff.mp hx
  rw [← hsum]
  intro i
  calc
    ((∑ y ∈ S, y) i).natAbs ≤ S.card * coordinateRadius A :=
      natAbs_sum_coord_le_card_mul
        (fun y hy j ↦ natAbs_le_coordinateRadius (hSA hy) j) i
    _ ≤ s * coordinateRadius A := Nat.mul_le_mul_right _ hScard
    _ ≤ M := hM

/-- The original set itself lies in every coordinate window whose radius is
at least its canonical coordinate radius. -/
theorem subset_coordinateWindow {d M : ℕ}
    (A : Finset (LatticePoint d))
    (hM : coordinateRadius A ≤ M) :
    (A : Set (LatticePoint d)) ⊆ coordinateWindow d M := by
  intro x hx i
  exact (natAbs_le_coordinateRadius hx i).trans hM

/-! ## Homogenized positive encoding

The linear encoding above is the cleanest form of no-carry reflection, but
it need not take positive values after translating a box.  We now add a
leading digit `1` and shift every remaining digit by the coordinate radius.
The leading digit records the number of summands.  Consequently the affine
encoding reflects precisely the equal-length additive relations used by a
Freiman homomorphism.
-/

/-- Add a leading homogeneous coordinate and shift all original coordinates
into the nonnegative interval `[0, 2R]`. -/
def homogenize {d : ℕ} (R : ℕ) (x : LatticePoint d) : LatticePoint (d + 1) :=
  Fin.cases 1 (fun i => x i + (R : ℤ))

@[simp]
theorem homogenize_zero {d : ℕ} (R : ℕ) (x : LatticePoint d) :
    homogenize R x 0 = 1 := rfl

@[simp]
theorem homogenize_succ {d : ℕ} (R : ℕ) (x : LatticePoint d) (i : Fin d) :
    homogenize R x i.succ = x i + (R : ℤ) := by
  simp [homogenize]

theorem homogenize_injective {d R : ℕ} :
    Function.Injective (homogenize (d := d) R) := by
  intro x y hxy
  funext i
  have h := congrFun hxy i.succ
  simpa using h

/-- A uniform absolute-value bound for the homogeneous digits of a member of
`A`. -/
theorem natAbs_homogenize_le {d : ℕ} {A : Finset (LatticePoint d)}
    {x : LatticePoint d} (hx : x ∈ A) (i : Fin (d + 1)) :
    (homogenize (coordinateRadius A) x i).natAbs ≤
      2 * coordinateRadius A + 1 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [homogenize]
  · rw [homogenize_succ]
    calc
      (x j + (coordinateRadius A : ℤ)).natAbs ≤
          (x j).natAbs + ((coordinateRadius A : ℤ)).natAbs :=
        Int.natAbs_add_le _ _
      _ = (x j).natAbs + coordinateRadius A := by simp
      _ ≤ coordinateRadius A + coordinateRadius A :=
        Nat.add_le_add_right (natAbs_le_coordinateRadius hx j) _
      _ ≤ 2 * coordinateRadius A + 1 := by omega

/-- The explicit base for the homogeneous encoding. -/
def homogeneousBase {d : ℕ} (A : Finset (LatticePoint d)) (s : ℕ) : ℕ :=
  relationBase s (2 * coordinateRadius A + 1)

/-- Positive affine mixed-radix encoding.  It is not a group homomorphism:
its leading digit records one summand. -/
def homogeneousEncode {d : ℕ} (A : Finset (LatticePoint d)) (s : ℕ)
    (x : LatticePoint d) : ℤ :=
  hornerEncode (d + 1) (homogeneousBase A s)
    (homogenize (coordinateRadius A) x)

theorem hornerEncode_nonneg_of_nonneg :
    ∀ {d b : ℕ} (x : LatticePoint d),
      (∀ i, 0 ≤ x i) → 0 ≤ hornerEncode d b x := by
  intro d
  induction d with
  | zero => intro b x _; simp
  | succ d ih =>
      intro b x hx
      rw [hornerEncode_succ]
      exact add_nonneg (hx 0)
        (mul_nonneg (Int.natCast_nonneg b) (ih _ (fun i => hx i.succ)))

theorem homogenize_nonneg {d : ℕ} {A : Finset (LatticePoint d)}
    {x : LatticePoint d} (hx : x ∈ A) (i : Fin (d + 1)) :
    0 ≤ homogenize (coordinateRadius A) x i := by
  refine Fin.cases (by simp [homogenize]) (fun j => ?_) i
  rw [homogenize_succ]
  have h := natAbs_le_coordinateRadius hx j
  have hcast : ((x j).natAbs : ℤ) ≤ (coordinateRadius A : ℤ) := by
    exact_mod_cast h
  have habs : |x j| ≤ (coordinateRadius A : ℤ) := by
    simpa only [Int.abs_eq_natAbs] using hcast
  have hlower := (abs_le.mp habs).1
  omega

/-- Every encoded member of `A` is a positive integer. -/
theorem homogeneousEncode_pos {d s : ℕ} {A : Finset (LatticePoint d)}
    {x : LatticePoint d} (hx : x ∈ A) :
    0 < homogeneousEncode A s x := by
  rw [homogeneousEncode, hornerEncode_succ, homogenize_zero]
  have htail :
      0 ≤ hornerEncode d (homogeneousBase A s)
        (fun i => homogenize (coordinateRadius A) x i.succ) :=
    hornerEncode_nonneg_of_nonneg _ (fun i => homogenize_nonneg hx i.succ)
  positivity

/-- Coordinatewise bound for a sum of homogeneous vectors. -/
theorem natAbs_sum_homogenize_coord_le {d : ℕ}
    {A S : Finset (LatticePoint d)} {R : ℕ}
    (hSA : S ⊆ A)
    (hR : ∀ x ∈ A, ∀ i : Fin (d + 1), (homogenize R x i).natAbs ≤ 2 * R + 1)
    (i : Fin (d + 1)) :
    ((∑ x ∈ S, homogenize R x) i).natAbs ≤ S.card * (2 * R + 1) := by
  calc
    ((∑ x ∈ S, homogenize R x) i).natAbs =
        (∑ x ∈ S, homogenize R x i).natAbs := by simp
    _ ≤ ∑ x ∈ S, (homogenize R x i).natAbs := Int.natAbs_sum_le _ _
    _ ≤ ∑ _x ∈ S, (2 * R + 1) :=
      Finset.sum_le_sum fun x hx => hR x (hSA hx) i
    _ = S.card * (2 * R + 1) := by simp

theorem natAbs_sub_sum_homogenize_lt {d s : ℕ}
    {A S T : Finset (LatticePoint d)}
    (hSA : S ⊆ A) (hTA : T ⊆ A)
    (hS : S.card ≤ s) (hT : T.card ≤ s) (i : Fin (d + 1)) :
    (((∑ x ∈ S, homogenize (coordinateRadius A) x) i) -
        ((∑ x ∈ T, homogenize (coordinateRadius A) x) i)).natAbs <
      homogeneousBase A s := by
  let R := coordinateRadius A
  have hRS := natAbs_sum_homogenize_coord_le hSA
    (fun x hx j => natAbs_homogenize_le hx j) i
  have hRT := natAbs_sum_homogenize_coord_le hTA
    (fun x hx j => natAbs_homogenize_le hx j) i
  calc
    (((∑ x ∈ S, homogenize R x) i) -
        ((∑ x ∈ T, homogenize R x) i)).natAbs ≤
      ((∑ x ∈ S, homogenize R x) i).natAbs +
        ((∑ x ∈ T, homogenize R x) i).natAbs := Int.natAbs_sub_le _ _
    _ ≤ S.card * (2 * R + 1) + T.card * (2 * R + 1) :=
      Nat.add_le_add hRS hRT
    _ ≤ s * (2 * R + 1) + s * (2 * R + 1) :=
      Nat.add_le_add
        (Nat.mul_le_mul_right (2 * R + 1) hS)
        (Nat.mul_le_mul_right (2 * R + 1) hT)
    _ = 2 * s * (2 * R + 1) := by ring
    _ < homogeneousBase A s := Nat.lt_succ_self _

theorem sum_add_const_int {α : Type*} (S : Finset α) (f : α → ℤ) (c : ℤ) :
    (∑ x ∈ S, (f x + c)) = (∑ x ∈ S, f x) + (S.card : ℤ) * c := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert x S hx ih =>
      simp only [Finset.sum_insert hx, Finset.card_insert_of_notMem hx, Nat.cast_add,
        Nat.cast_one, ih]
      ring

/-- The precise Freiman property of the positive affine encoding: two
bounded sums have equal encodings iff they contain equally many terms and
have the same lattice sum. -/
theorem sum_homogeneousEncode_eq_iff {d s : ℕ}
    {A S T : Finset (LatticePoint d)}
    (hSA : S ⊆ A) (hTA : T ⊆ A)
    (hS : S.card ≤ s) (hT : T.card ≤ s) :
    (∑ x ∈ S, homogeneousEncode A s x) =
          ∑ x ∈ T, homogeneousEncode A s x ↔
      S.card = T.card ∧ ∑ x ∈ S, x = ∑ x ∈ T, x := by
  have hsumS :
      (∑ x ∈ S, homogeneousEncode A s x) =
        hornerEncode (d + 1) (homogeneousBase A s)
          (∑ x ∈ S, homogenize (coordinateRadius A) x) := by
    symm
    exact hornerEncode_sum _ _ _ _
  have hsumT :
      (∑ x ∈ T, homogeneousEncode A s x) =
        hornerEncode (d + 1) (homogeneousBase A s)
          (∑ x ∈ T, homogenize (coordinateRadius A) x) := by
    symm
    exact hornerEncode_sum _ _ _ _
  rw [hsumS, hsumT]
  constructor
  · intro henc
    have hhom :
        (∑ x ∈ S, homogenize (coordinateRadius A) x) =
          ∑ x ∈ T, homogenize (coordinateRadius A) x := by
      apply eq_of_hornerEncode_eq_of_natAbs_sub_lt
        (relationBase_pos s (2 * coordinateRadius A + 1)) _ henc
      exact natAbs_sub_sum_homogenize_lt hSA hTA hS hT
    have hcard : S.card = T.card := by
      have hzero := congrFun hhom 0
      simpa [homogenize] using hzero
    refine ⟨hcard, ?_⟩
    funext i
    have hi := congrFun hhom i.succ
    simp only [Finset.sum_apply, homogenize_succ] at hi
    rw [sum_add_const_int, sum_add_const_int] at hi
    rw [hcard] at hi
    have hi' : (∑ x ∈ S, x i) = ∑ x ∈ T, x i := add_right_cancel hi
    simpa only [Finset.sum_apply] using hi'
  · rintro ⟨hcard, hsum⟩
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [homogenize, hcard]
    · have hj := congrFun hsum j
      simp only [Finset.sum_apply, homogenize_succ]
      rw [sum_add_const_int, sum_add_const_int]
      rw [hcard]
      have hj' : (∑ x ∈ S, x j) = ∑ x ∈ T, x j := by
        simpa only [Finset.sum_apply] using hj
      rw [hj']

/-- Endpoint of the finite positive interval containing the homogeneous
encoding of `A`. -/
def encodedEndpoint {d : ℕ} (A : Finset (LatticePoint d)) (s : ℕ) : ℕ :=
  A.sup fun x => (homogeneousEncode A s x).toNat

/-- The homogeneous image is genuinely a finite set of positive integers in
an explicit interval. -/
theorem homogeneousEncode_mem_Icc {d s : ℕ}
    {A : Finset (LatticePoint d)} {x : LatticePoint d} (hx : x ∈ A) :
    homogeneousEncode A s x ∈
      Finset.Icc (1 : ℤ) (encodedEndpoint A s : ℤ) := by
  rw [Finset.mem_Icc]
  constructor
  · exact homogeneousEncode_pos hx
  · have hnonneg : 0 ≤ homogeneousEncode A s x := (homogeneousEncode_pos hx).le
    have hsup : (homogeneousEncode A s x).toNat ≤ encodedEndpoint A s :=
      Finset.le_sup (s := A) (f := fun y => (homogeneousEncode A s y).toNat) hx
    rw [← Int.toNat_of_nonneg hnonneg]
    exact_mod_cast hsup

/-- At positive relation order, homogenized encoding is injective on the
original finite set. -/
theorem homogeneousEncode_injectiveOn {d s : ℕ}
    (A : Finset (LatticePoint d)) (hs : 0 < s) :
    Set.InjOn (homogeneousEncode A s) A := by
  intro x hx y hy hxy
  have hrel := (sum_homogeneousEncode_eq_iff
    (S := {x}) (T := {y}) (A := A)
    (by simpa using hx) (by simpa using hy)
    (by simpa using (Nat.succ_le_iff.mpr hs))
    (by simpa using (Nat.succ_le_iff.mpr hs))).mp
  have : (∑ z ∈ ({x} : Finset (LatticePoint d)), homogeneousEncode A s z) =
      ∑ z ∈ ({y} : Finset (LatticePoint d)), homogeneousEncode A s z := by
    simpa using hxy
  simpa using (hrel this).2

/-- Encoding preserves the cardinality of `A` whenever at least one summand
is allowed. -/
theorem card_image_homogeneousEncode {d s : ℕ}
    (A : Finset (LatticePoint d)) (hs : 0 < s) :
    (A.image (homogeneousEncode A s)).card = A.card := by
  exact Finset.card_image_iff.mpr (homogeneousEncode_injectiveOn A hs)

/-! ## The exact GAP projection obstruction -/

/-- Apply an additive homomorphism to the offset and directions of a GAP. -/
def mapGAP {d e r : ℕ} (f : LatticePoint d →+ LatticePoint e)
    (P : GAP d r) : GAP e r where
  offset := f P.offset
  steps := fun i => f (P.steps i)
  widths := P.widths
  width_pos := P.width_pos

/-- Evaluation commutes with applying an additive homomorphism to a GAP. -/
@[simp]
theorem mapGAP_coordPoint {d e r : ℕ}
    (f : LatticePoint d →+ LatticePoint e) (P : GAP d r)
    (n : (mapGAP f P).Coord) :
    (mapGAP f P).coordPoint n = f (P.coordPoint n) := by
  have hpoint : P.coordPoint n =
      P.offset + ∑ i, (n i : ℤ) • P.steps i := by
    ext j
    simp only [GAP.coordPoint, Pi.add_apply, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul]
  rw [hpoint, map_add, map_sum]
  simp only [map_zsmul]
  ext j
  simp only [GAP.coordPoint, mapGAP, Pi.add_apply, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]

/-- The carrier of a mapped GAP is the pointwise image of the original
carrier. -/
theorem mapGAP_carrier {d e r : ℕ}
    (f : LatticePoint d →+ LatticePoint e) (P : GAP d r) :
    (mapGAP f P).carrier = P.carrier.image f := by
  ext x
  simp only [GAP.mem_carrier_iff, Finset.mem_image]
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨P.coordPoint n, ⟨n, rfl⟩,
      (mapGAP_coordPoint f P n).symm⟩
  · rintro ⟨y, ⟨n, rfl⟩, rfl⟩
    exact ⟨n, mapGAP_coordPoint f P n⟩

/-- Mapping commutes exactly with natural dilation of a GAP. -/
theorem mapGAP_dilate {d e r : ℕ}
    (f : LatticePoint d →+ LatticePoint e) (P : GAP d r) (k : ℕ) :
    mapGAP f (P.dilate k) = (mapGAP f P).dilate k := by
  rw [GAP.mk.injEq]
  refine ⟨?_, rfl, rfl⟩
  funext j
  have hmap := f.map_zsmul (k : ℤ) P.offset
  change f ((k : ℤ) • P.offset) j = (k : ℤ) * f P.offset j
  simpa only [Pi.smul_apply, smul_eq_mul] using congrFun hmap j

/-! ## Source-shaped lifting of a target progression

The Appendix proof of the higher-dimensional CFP theorem starts with a GAP
in the encoded one-dimensional target, chooses bounded preimages of its
offset and directions, and then forms the GAP with those lifted data.  This
is the reverse direction from `mapGAP`: properness of the target presentation
automatically implies properness of every such lift.  The genuinely
arithmetic remaining obligation is to choose the preimages inside a window
on which the mixed-radix homomorphism is injective.
-/

/-- Replace the offset and directions of a target GAP by chosen source
preimages, retaining its coefficient box. -/
def liftGAP {d e r : ℕ} (P : GAP e r) (offsetLift : LatticePoint d)
    (stepLift : Fin r → LatticePoint d) : GAP d r where
  offset := offsetLift
  steps := stepLift
  widths := P.widths
  width_pos := P.width_pos

/-- Chosen preimages make the mapped lifted presentation exactly the target
presentation, not merely equal at the level of carriers. -/
theorem mapGAP_liftGAP {d e r : ℕ}
    (f : LatticePoint d →+ LatticePoint e) (P : GAP e r)
    (offsetLift : LatticePoint d) (stepLift : Fin r → LatticePoint d)
    (hoffset : f offsetLift = P.offset)
    (hsteps : ∀ i, f (stepLift i) = P.steps i) :
    mapGAP f (liftGAP P offsetLift stepLift) = P := by
  rw [GAP.mk.injEq]
  exact ⟨hoffset, funext hsteps, rfl⟩

/-- Properness reflects from a mapped GAP to the original presentation.  No
global injectivity of the ambient homomorphism is required in this
direction. -/
theorem proper_of_mapGAP_proper {d e r : ℕ}
    (f : LatticePoint d →+ LatticePoint e) (P : GAP d r)
    (hproper : (mapGAP f P).Proper) : P.Proper := by
  intro a b hab
  let a' : (mapGAP f P).Coord := a
  let b' : (mapGAP f P).Coord := b
  have hmapped : (mapGAP f P).coordPoint a' =
      (mapGAP f P).coordPoint b' := by
    rw [mapGAP_coordPoint, mapGAP_coordPoint]
    exact congrArg f hab
  have hcoord := hproper hmapped
  funext i
  apply Fin.ext
  exact congrArg Fin.val (congrFun hcoord i)

/-- A target-proper presentation remains proper after choosing arbitrary
preimages of its presentation data. -/
theorem liftGAP_proper_of_target_proper {d e r : ℕ}
    (f : LatticePoint d →+ LatticePoint e) (P : GAP e r)
    (offsetLift : LatticePoint d) (stepLift : Fin r → LatticePoint d)
    (hoffset : f offsetLift = P.offset)
    (hsteps : ∀ i, f (stepLift i) = P.steps i)
    (hproper : P.Proper) :
    (liftGAP P offsetLift stepLift).Proper := by
  apply proper_of_mapGAP_proper f
  rwa [mapGAP_liftGAP f P offsetLift stepLift hoffset hsteps]

/-- The source Appendix needs properness at the enlarged scale.  Mapping
commutes with dilation, so target dilate properness reflects to the lifted
dilate as soon as the chosen data really are preimages. -/
theorem liftGAP_dilate_proper_of_target {d e r k : ℕ}
    (f : LatticePoint d →+ LatticePoint e) (P : GAP e r)
    (offsetLift : LatticePoint d) (stepLift : Fin r → LatticePoint d)
    (hoffset : f offsetLift = P.offset)
    (hsteps : ∀ i, f (stepLift i) = P.steps i)
    (hproper : (P.dilate k).Proper) :
    ((liftGAP P offsetLift stepLift).dilate k).Proper := by
  apply proper_of_mapGAP_proper f
  rw [mapGAP_dilate, mapGAP_liftGAP f P offsetLift stepLift hoffset hsteps]
  exact hproper

/-- The canonical lift of a centered target presentation: lift the
directions and reconstruct the offset from the same radius vector. -/
def centeredLiftGAP {d e r : ℕ} (P : GAP e r) (radii : Fin r → ℕ)
    (_hcentered : P.Centered radii) (stepLift : Fin r → LatticePoint d) :
    GAP d r :=
  liftGAP P (fun j ↦ -∑ i, (radii i : ℤ) * stepLift i j) stepLift

/-- Reconstructing the offset from the target center makes the centered lift
map exactly to the target GAP. -/
theorem mapGAP_centeredLiftGAP {d e r : ℕ}
    (f : LatticePoint d →+ LatticePoint e) (P : GAP e r)
    (radii : Fin r → ℕ) (hcentered : P.Centered radii)
    (stepLift : Fin r → LatticePoint d)
    (hsteps : ∀ i, f (stepLift i) = P.steps i) :
    mapGAP f (centeredLiftGAP P radii hcentered stepLift) = P := by
  apply mapGAP_liftGAP
  · rw [hcentered.offset_eq]
    have hsource :
        (fun j ↦ -∑ i, (radii i : ℤ) * stepLift i j) =
          -∑ i, (radii i : ℤ) • stepLift i := by
      ext j
      simp only [Pi.neg_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [hsource, map_neg, map_sum]
    simp_rw [map_zsmul, hsteps]
    ext j
    simp only [Pi.neg_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  · exact hsteps

/-- The centered target radius vector also centers the lifted presentation.
In particular, symmetry and homogeneity need no separate pullback argument. -/
theorem centeredLiftGAP_centered {d e r : ℕ}
    (P : GAP e r) (radii : Fin r → ℕ) (hcentered : P.Centered radii)
    (stepLift : Fin r → LatticePoint d) :
    (centeredLiftGAP P radii hcentered stepLift).Centered radii := by
  exact ⟨hcentered.widths_eq, rfl⟩

/-- A deliberately coarse coordinate bound for a centered GAP.  The factor
three avoids signed-cast case splits and is ample for the Appendix choice of
the mixed-radix base. -/
theorem centered_coordPoint_natAbs_le {d r L : ℕ}
    {P : GAP d r} {radii : Fin r → ℕ} (hcentered : P.Centered radii)
    (hsteps : ∀ i j, (P.steps i j).natAbs ≤ L)
    (n : P.Coord) (j : Fin d) :
    (P.coordPoint n j).natAbs ≤ 3 * (∑ i, radii i) * L := by
  rw [hcentered.coordPoint_eq]
  calc
    (∑ i, ((((n i : ℕ) : ℤ) - (radii i : ℤ)) *
        P.steps i j)).natAbs ≤
        ∑ i, (((((n i : ℕ) : ℤ) - (radii i : ℤ)) *
          P.steps i j).natAbs) := Int.natAbs_sum_le _ _
    _ ≤ ∑ i, (3 * radii i) * L := by
      apply Finset.sum_le_sum
      intro i _
      rw [Int.natAbs_mul]
      apply Nat.mul_le_mul
      · calc
          ((((n i : ℕ) : ℤ) - (radii i : ℤ))).natAbs ≤
              (((n i : ℕ) : ℤ)).natAbs + ((radii i : ℤ)).natAbs :=
            Int.natAbs_sub_le _ _
          _ = (n i : ℕ) + radii i := by simp
          _ ≤ 3 * radii i := by
            have hn := (n i).isLt
            have hw := hcentered.width_eq i
            omega
      · exact hsteps i j
    _ = 3 * (∑ i, radii i) * L := by
      rw [Finset.mul_sum]
      rw [Finset.sum_mul]

/-- Carrier-level version of `centered_coordPoint_natAbs_le`. -/
theorem centered_carrier_subset_coordinateWindow {d r L : ℕ}
    {P : GAP d r} {radii : Fin r → ℕ} (hcentered : P.Centered radii)
    (hsteps : ∀ i j, (P.steps i j).natAbs ≤ L) :
    (P.carrier : Set (LatticePoint d)) ⊆
      coordinateWindow d (3 * (∑ i, radii i) * L) := by
  intro x hx
  obtain ⟨n, rfl⟩ := GAP.mem_carrier_iff.mp hx
  exact centered_coordPoint_natAbs_le hcentered hsteps n

/-- A translate of a centered dilate lies in the coordinate window obtained
by adding the translation radius and the coarse centered-carrier radius. -/
theorem translate_dilate_subset_coordinateWindow {d r k L T : ℕ}
    {P : GAP d r} {radii : Fin r → ℕ} (hcentered : P.Centered radii)
    (hsteps : ∀ i j, (P.steps i j).natAbs ≤ L)
    (t : LatticePoint d) (ht : ∀ j, (t j).natAbs ≤ T) :
    (translate t (P.dilate k).carrier : Set (LatticePoint d)) ⊆
      coordinateWindow d (T + 3 * (∑ i, k * radii i) * L) := by
  intro x hx
  obtain ⟨q, hq, rfl⟩ := mem_translate_iff.mp hx
  intro j
  calc
    (t j + q j).natAbs ≤ (t j).natAbs + (q j).natAbs :=
      Int.natAbs_add_le _ _
    _ ≤ T + 3 * (∑ i, k * radii i) * L := by
      exact Nat.add_le_add (ht j)
        (centered_carrier_subset_coordinateWindow
          (hcentered.dilate k) (by simpa using hsteps) hq j)

/-- Every active direction of a centered presentation occurs as a carrier
point. -/
theorem centered_step_mem_carrier {d r : ℕ} {P : GAP d r}
    {radii : Fin r → ℕ} (hcentered : P.Centered radii)
    (i : Fin r) (hi : 0 < radii i) :
    P.steps i ∈ P.carrier := by
  classical
  let n : P.Coord := fun j ↦
    if hji : j = i then
      ⟨radii j + 1, by
        subst j
        rw [hcentered.width_eq]
        omega⟩
    else hcentered.centerCoord j
  apply GAP.mem_carrier_iff.mpr
  refine ⟨n, ?_⟩
  rw [hcentered.coordPoint_eq]
  ext j
  rw [Finset.sum_eq_single i]
  · simp [n, GAP.Centered.centerCoord]
  · intro a _ hai
    simp [n, hai, GAP.Centered.centerCoord]
  · simp

/-- At positive dilation scale every active base direction remains a point
of the centered dilate. -/
theorem centered_step_mem_dilate_carrier {d r k : ℕ} {P : GAP d r}
    {radii : Fin r → ℕ} (hcentered : P.Centered radii)
    (i : Fin r) (hi : 0 < radii i) (hk : 0 < k) :
    P.steps i ∈ (P.dilate k).carrier := by
  have hmem := centered_step_mem_carrier (hcentered.dilate k) i (by
    positivity)
  simpa only [GAP.dilate_steps] using hmem

/-- A subset sum of an injective image has a source subset-sum preimage whose
sum maps to the prescribed target point. -/
theorem exists_subsetSum_preimage {d e : ℕ}
    (f : LatticePoint d →+ LatticePoint e)
    (R : Finset (LatticePoint d)) (hinjective : Set.InjOn f R)
    {z : LatticePoint e} (hz : z ∈ GAP.subsetSums (R.image f)) :
    ∃ y ∈ GAP.subsetSums R, f y = z := by
  classical
  obtain ⟨T, hT, hsum⟩ := GAP.mem_subsetSums_iff.mp hz
  let S : Finset (LatticePoint d) := R.filter fun x ↦ f x ∈ T
  have hmap : S.image f = T := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      exact (Finset.mem_filter.mp hx).2
    · intro hy
      obtain ⟨x, hxR, hxy⟩ := Finset.mem_image.mp (hT hy)
      exact Finset.mem_image.mpr
        ⟨x, Finset.mem_filter.mpr ⟨hxR, hxy.symm ▸ hy⟩, hxy⟩
  have hSR : S ⊆ R := by
    intro x hx
    exact (Finset.mem_filter.mp hx).1
  refine ⟨∑ x ∈ S, x, GAP.mem_subsetSums_iff.mpr ⟨S, hSR, rfl⟩, ?_⟩
  calc
    f (∑ x ∈ S, x) = ∑ x ∈ S, f x := by simp
    _ = ∑ y ∈ T, y := by
      rw [← hmap, Finset.sum_image]
      intro x hx y hy hxy
      exact hinjective (hSR hx) (hSR hy) hxy
    _ = z := hsum

/-- Pull a target subset sum back to a source sum of at most `s` elements. -/
theorem exists_boundedSubsetSum_preimage {d e s : ℕ}
    (f : LatticePoint d →+ LatticePoint e)
    (A R : Finset (LatticePoint d))
    (hinjective : Set.InjOn f R) (hRA : R ⊆ A) (hRcard : R.card ≤ s)
    {z : LatticePoint e} (hz : z ∈ GAP.subsetSums (R.image f)) :
    ∃ y ∈ boundedSubsetSums A s, f y = z := by
  obtain ⟨y, hy, hmap⟩ := exists_subsetSum_preimage f R hinjective hz
  exact ⟨y, subsetSums_subset_boundedSubsetSums hRA hRcard hy, hmap⟩

/-- Pull a target subset of an injective finite image back to the source
finite set. -/
def pullbackFinset {d e : ℕ} (f : LatticePoint d →+ LatticePoint e)
    (A : Finset (LatticePoint d)) (T : Finset (LatticePoint e)) :
    Finset (LatticePoint d) :=
  A.filter fun x ↦ f x ∈ T

@[simp]
theorem mem_pullbackFinset {d e : ℕ}
    (f : LatticePoint d →+ LatticePoint e)
    (A : Finset (LatticePoint d)) (T : Finset (LatticePoint e))
    (x : LatticePoint d) :
    x ∈ pullbackFinset f A T ↔ x ∈ A ∧ f x ∈ T := by
  simp [pullbackFinset]

theorem pullbackFinset_subset {d e : ℕ}
    (f : LatticePoint d →+ LatticePoint e)
    (A : Finset (LatticePoint d)) (T : Finset (LatticePoint e)) :
    pullbackFinset f A T ⊆ A := by
  intro x hx
  exact (mem_pullbackFinset f A T x |>.mp hx).1

theorem pullbackFinset_mono {d e : ℕ}
    (f : LatticePoint d →+ LatticePoint e)
    (A : Finset (LatticePoint d)) {T U : Finset (LatticePoint e)}
    (hTU : T ⊆ U) :
    pullbackFinset f A T ⊆ pullbackFinset f A U := by
  intro x hx
  have hx' := mem_pullbackFinset f A T x |>.mp hx
  exact mem_pullbackFinset f A U x |>.mpr ⟨hx'.1, hTU hx'.2⟩

/-- Pullback followed by the original map recovers every target subset of
the displayed finite image. -/
theorem image_pullbackFinset {d e : ℕ}
    (f : LatticePoint d →+ LatticePoint e)
    (A : Finset (LatticePoint d)) (T : Finset (LatticePoint e))
    (hT : T ⊆ A.image f) :
    (pullbackFinset f A T).image f = T := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact (mem_pullbackFinset f A T x |>.mp hx).2
  · intro hy
    obtain ⟨x, hxA, hxy⟩ := Finset.mem_image.mp (hT hy)
    exact Finset.mem_image.mpr
      ⟨x, mem_pullbackFinset f A T x |>.mpr ⟨hxA, hxy.symm ▸ hy⟩, hxy⟩

/-- An injective finite image and each of its pullback subsets have the same
cardinality as their source/target counterparts. -/
theorem card_pullbackFinset {d e : ℕ}
    (f : LatticePoint d →+ LatticePoint e)
    (A : Finset (LatticePoint d)) (T : Finset (LatticePoint e))
    (hinjective : Set.InjOn f A) (hT : T ⊆ A.image f) :
    (pullbackFinset f A T).card = T.card := by
  calc
    (pullbackFinset f A T).card =
        ((pullbackFinset f A T).image f).card :=
      (Finset.card_image_of_injOn
        (hinjective.mono (pullbackFinset_subset f A T))).symm
    _ = T.card := congrArg Finset.card (image_pullbackFinset f A T hT)

/-- Coverage supplies coherent bounded source preimages of the target
translation and every progression direction.  The direction lift is the
difference between preimages of the translated center and of the translated
step, hence has coordinate radius at most twice the subset-sum radius. -/
theorem exists_bounded_step_translate_lifts
    {d e s D k loss : ℕ} {A : Finset (LatticePoint d)}
    (f : LatticePoint d →+ LatticePoint e)
    (W : EnhancedCFPWitness (A.image f) s D k loss)
    (hinjectiveA : Set.InjOn f A) :
    ∃ (stepLift : Fin W.rank → LatticePoint d)
        (translateLift : LatticePoint d),
      (∀ i, f (stepLift i) = W.progression.steps i) ∧
      (∀ i j, (stepLift i j).natAbs ≤ 2 * s * coordinateRadius A) ∧
      f translateLift = W.translatePoint ∧
      (∀ j, (translateLift j).natAbs ≤ s * coordinateRadius A) := by
  classical
  let R := pullbackFinset f A W.reserved
  have hRsubset : R ⊆ A := pullbackFinset_subset f A W.reserved
  have hinjectiveR : Set.InjOn f R := hinjectiveA.mono hRsubset
  have hRimage : R.image f = W.reserved :=
    image_pullbackFinset f A W.reserved W.reserved_subset
  have hRcard : R.card ≤ s := by
    rw [card_pullbackFinset f A W.reserved hinjectiveA W.reserved_subset]
    exact W.reserved_small
  have hcenterTarget : W.translatePoint ∈
      translate W.translatePoint (W.progression.dilate k).carrier := by
    apply mem_translate_iff.mpr
    exact ⟨0, W.dilated_symmetric.zero_mem_carrier, by simp⟩
  have hcenterSum : W.translatePoint ∈ GAP.subsetSums (R.image f) := by
    rw [hRimage]
    exact W.covered hcenterTarget
  obtain ⟨centerLift, hcenterBounded, hcenterMap⟩ :=
    exists_boundedSubsetSum_preimage f A R hinjectiveR hRsubset hRcard hcenterSum
  have hcenterWindow : centerLift ∈
      coordinateWindow d (s * coordinateRadius A) :=
    boundedSubsetSums_subset_coordinateWindow A (Nat.le_refl _) hcenterBounded
  have hendpoint (i : Fin W.rank) :
      ∃ y ∈ boundedSubsetSums A s,
        f y = W.translatePoint + W.progression.steps i := by
    have hstepCarrier : W.progression.steps i ∈
        (W.progression.dilate k).carrier :=
      centered_step_mem_dilate_carrier W.symmetryCentered i
        (W.symmetryRadii_pos i) W.k_pos
    have hpoint : W.translatePoint + W.progression.steps i ∈
        translate W.translatePoint (W.progression.dilate k).carrier :=
      mem_translate_iff.mpr
        ⟨W.progression.steps i, hstepCarrier, rfl⟩
    have hsum : W.translatePoint + W.progression.steps i ∈
        GAP.subsetSums (R.image f) := by
      rw [hRimage]
      exact W.covered hpoint
    exact exists_boundedSubsetSum_preimage f A R hinjectiveR hRsubset hRcard hsum
  let endpointLift : Fin W.rank → LatticePoint d :=
    fun i ↦ Classical.choose (hendpoint i)
  have hendpointBounded (i : Fin W.rank) :
      endpointLift i ∈ boundedSubsetSums A s :=
    Classical.choose_spec (hendpoint i) |>.1
  have hendpointMap (i : Fin W.rank) :
      f (endpointLift i) = W.translatePoint + W.progression.steps i :=
    Classical.choose_spec (hendpoint i) |>.2
  let stepLift : Fin W.rank → LatticePoint d :=
    fun i ↦ endpointLift i - centerLift
  refine ⟨stepLift, centerLift, ?_, ?_, hcenterMap, hcenterWindow⟩
  · intro i
    change f (endpointLift i - centerLift) = W.progression.steps i
    rw [map_sub, hendpointMap, hcenterMap]
    abel
  · intro i j
    have hendpointWindow : endpointLift i ∈
        coordinateWindow d (s * coordinateRadius A) :=
      boundedSubsetSums_subset_coordinateWindow A (Nat.le_refl _)
        (hendpointBounded i)
    calc
      (stepLift i j).natAbs =
          (endpointLift i j - centerLift j).natAbs := rfl
      _ ≤ (endpointLift i j).natAbs + (centerLift j).natAbs :=
        Int.natAbs_sub_le _ _
      _ ≤ s * coordinateRadius A + s * coordinateRadius A :=
        Nat.add_le_add (hendpointWindow j) (hcenterWindow j)
      _ = 2 * s * coordinateRadius A := by ring

/-- Coverage bounds the target translate by the radius of the target input
set.  This is the first quantitative preimage estimate in the Appendix. -/
theorem translatePoint_natAbs_le_of_covered
    {e s D k loss : ℕ} {A : Finset (LatticePoint e)}
    (W : EnhancedCFPWitness A s D k loss) (j : Fin e) :
    (W.translatePoint j).natAbs ≤ s * coordinateRadius A := by
  have hcenter : W.translatePoint ∈
      translate W.translatePoint (W.progression.dilate k).carrier := by
    exact mem_translate_iff.mpr
      ⟨0, W.dilated_symmetric.zero_mem_carrier, by simp⟩
  have hsum : W.translatePoint ∈ boundedSubsetSums A s :=
    subsetSums_subset_boundedSubsetSums W.reserved_subset W.reserved_small
      (W.covered hcenter)
  exact boundedSubsetSums_subset_coordinateWindow A (Nat.le_refl _) hsum j

/-- Coverage bounds every target direction by twice the target subset-sum
radius, by subtracting the covered centre from a covered adjacent point. -/
theorem progression_step_natAbs_le_of_covered
    {e s D k loss : ℕ} {A : Finset (LatticePoint e)}
    (W : EnhancedCFPWitness A s D k loss) (i : Fin W.rank) (j : Fin e) :
    (W.progression.steps i j).natAbs ≤ 2 * s * coordinateRadius A := by
  have hstepCarrier : W.progression.steps i ∈
      (W.progression.dilate k).carrier :=
    centered_step_mem_dilate_carrier W.symmetryCentered i
      (W.symmetryRadii_pos i) W.k_pos
  have hendpoint : W.translatePoint + W.progression.steps i ∈
      boundedSubsetSums A s :=
    subsetSums_subset_boundedSubsetSums W.reserved_subset W.reserved_small
      (W.covered (mem_translate_iff.mpr
        ⟨W.progression.steps i, hstepCarrier, rfl⟩))
  have hendpointBound := boundedSubsetSums_subset_coordinateWindow A
    (Nat.le_refl (s * coordinateRadius A)) hendpoint j
  have hcenterBound := translatePoint_natAbs_le_of_covered W j
  calc
    (W.progression.steps i j).natAbs =
        ((W.translatePoint + W.progression.steps i) j -
          W.translatePoint j).natAbs := by simp
    _ ≤ ((W.translatePoint + W.progression.steps i) j).natAbs +
          (W.translatePoint j).natAbs := Int.natAbs_sub_le _ _
    _ ≤ s * coordinateRadius A + s * coordinateRadius A :=
      Nat.add_le_add hendpointBound hcenterBound
    _ = 2 * s * coordinateRadius A := by ring

/-- The covered centre is a subset sum of at most `s` points of the
centered target progression.  Summing their centered coordinates therefore
represents the translate with coefficient `i` bounded by
`s * symmetryRadii i`.  This is the exact bounded homogeneity input used in
the Appendix, and is independent of the numerical size of the encoded
target integers. -/
theorem exists_centered_bounded_translatePoint_coefficients
    {e s D k loss : ℕ} {A : Finset (LatticePoint e)}
    (W : EnhancedCFPWitness A s D k loss) :
    ∃ z : Fin W.rank → ℤ,
      W.translatePoint =
        (fun j ↦ ∑ i, z i * W.progression.steps i j) ∧
      ∀ i, (z i).natAbs ≤ s * W.symmetryRadii i := by
  classical
  have hcenter : W.translatePoint ∈
      translate W.translatePoint (W.progression.dilate k).carrier :=
    mem_translate_iff.mpr
      ⟨0, W.dilated_symmetric.zero_mem_carrier, by simp⟩
  obtain ⟨S, hSreserved, hsum⟩ :=
    GAP.mem_subsetSums_iff.mp (W.covered hcenter)
  have hScarrier (x : LatticePoint e) (hx : x ∈ S) :
      x ∈ W.progression.carrier := by
    apply W.core_zero_subset
    exact Finset.mem_insert_of_mem
      (W.reserved_subset_core (hSreserved hx))
  let coord (x : LatticePoint e) : W.progression.Coord :=
    if hx : x ∈ S then
      Classical.choose (GAP.mem_carrier_iff.mp (hScarrier x hx))
    else W.symmetryCentered.centerCoord
  have hcoord (x : LatticePoint e) (hx : x ∈ S) :
      W.progression.coordPoint (coord x) = x := by
    simp only [coord, dif_pos hx]
    exact Classical.choose_spec (GAP.mem_carrier_iff.mp (hScarrier x hx))
  let z : Fin W.rank → ℤ := fun i ↦
    Finset.sum S (fun x ↦ ((coord x i : ℕ) : ℤ) -
      (W.symmetryRadii i : ℤ))
  refine ⟨z, ?_, ?_⟩
  · rw [← hsum]
    ext j
    simp only [Finset.sum_apply]
    calc
      Finset.sum S (fun x ↦ x j) =
          Finset.sum S (fun x ↦ W.progression.coordPoint (coord x) j) := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [hcoord x hx]
      _ = Finset.sum S (fun x ↦ ∑ i,
          ((((coord x i : ℕ) : ℤ) -
            (W.symmetryRadii i : ℤ)) * W.progression.steps i j)) := by
        apply Finset.sum_congr rfl
        intro x hx
        exact congrFun (W.symmetryCentered.coordPoint_eq (coord x)) j
      _ = ∑ i, z i * W.progression.steps i j := by
        simp only [z]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        simpa only using
          (Finset.sum_mul S
            (fun x ↦ ((coord x i : ℕ) : ℤ) -
              (W.symmetryRadii i : ℤ))
            (W.progression.steps i j)).symm
  · intro i
    have hrelative (x : LatticePoint e) (hx : x ∈ S) :
        ((((coord x i : ℕ) : ℤ) -
          (W.symmetryRadii i : ℤ))).natAbs ≤ W.symmetryRadii i := by
      have hn : (coord x i : ℕ) < 2 * W.symmetryRadii i + 1 := by
        calc
          (coord x i : ℕ) < W.progression.widths i := (coord x i).isLt
          _ = 2 * W.symmetryRadii i + 1 := W.symmetryCentered.width_eq i
      by_cases hle : W.symmetryRadii i ≤ (coord x i : ℕ)
      · let a : ℤ := ((coord x i : ℕ) : ℤ) -
          (W.symmetryRadii i : ℤ)
        change a.natAbs ≤ W.symmetryRadii i
        have ha : 0 ≤ a := by dsimp [a]; omega
        have habs : ((a.natAbs : ℕ) : ℤ) = a :=
          Int.natAbs_of_nonneg ha
        have hbound : a ≤ (W.symmetryRadii i : ℤ) := by
          dsimp [a]
          omega
        have hcast : ((a.natAbs : ℕ) : ℤ) ≤
            (W.symmetryRadii i : ℤ) := habs ▸ hbound
        exact_mod_cast hcast
      · let a : ℤ := ((coord x i : ℕ) : ℤ) -
          (W.symmetryRadii i : ℤ)
        change a.natAbs ≤ W.symmetryRadii i
        have ha : 0 ≤ -a := by dsimp [a]; omega
        have habs : ((a.natAbs : ℕ) : ℤ) = -a := by
          calc
            ((a.natAbs : ℕ) : ℤ) = (((-a).natAbs : ℕ) : ℤ) := by
              rw [Int.natAbs_neg]
            _ = -a := Int.natAbs_of_nonneg ha
        have hbound : -a ≤ (W.symmetryRadii i : ℤ) := by
          dsimp [a]
          omega
        have hcast : ((a.natAbs : ℕ) : ℤ) ≤
            (W.symmetryRadii i : ℤ) := habs ▸ hbound
        exact_mod_cast hcast
    calc
      (z i).natAbs ≤ Finset.sum S (fun x ↦
          ((((coord x i : ℕ) : ℤ) -
            (W.symmetryRadii i : ℤ))).natAbs) := by
        simp only [z]
        simpa only using
          (Int.natAbs_sum_le S
            (fun x ↦ ((coord x i : ℕ) : ℤ) -
              (W.symmetryRadii i : ℤ)))
      _ ≤ Finset.sum S (fun _x ↦ W.symmetryRadii i) := by
        apply Finset.sum_le_sum
        intro x hx
        exact hrelative x hx
      _ = S.card * W.symmetryRadii i := by simp
      _ ≤ s * W.symmetryRadii i := by
        apply Nat.mul_le_mul_right
        exact (Finset.card_le_card hSreserved).trans W.reserved_small

/-- The total center radius is uniformly bounded by rank times the number
of reserve subsets.  Properness of the covered dilate bounds its volume by
`2^s`, while every center radius is at most one factor of that volume. -/
theorem sum_symmetryRadii_le_rank_mul_pow_s
    {e s D k loss : ℕ} {A : Finset (LatticePoint e)}
    (W : EnhancedCFPWitness A s D k loss) :
    (∑ i, W.symmetryRadii i) ≤ W.rank * 2 ^ s := by
  have hradius (i : Fin W.rank) : W.symmetryRadii i ≤ 2 ^ s := by
    have hfactor :
        (W.progression.dilate k).widths i ≤
          (W.progression.dilate k).volume := by
      rw [GAP.volume]
      apply Finset.single_le_prod'
      · intro j _
        exact (W.progression.dilate k).width_pos j
      · exact Finset.mem_univ i
    calc
      W.symmetryRadii i ≤
          (W.progression.dilate k).widths i := by
        rw [W.symmetryCentered.dilate_width_eq]
        have hk : 1 ≤ k := W.k_pos
        nlinarith
      _ ≤ (W.progression.dilate k).volume := hfactor
      _ ≤ 2 ^ s := W.dilated_volume_le_pow_s
  calc
    (∑ i, W.symmetryRadii i) ≤
        (Finset.univ : Finset (Fin W.rank)).card • (2 ^ s) :=
      Finset.sum_le_card_nsmul Finset.univ W.symmetryRadii (2 ^ s)
        (fun i _ ↦ hradius i)
    _ = W.rank * 2 ^ s := by simp [nsmul_eq_mul]

/-- Appendix polynomial volume bound.  Injectivity on the source input lets
every target reserve subset sum be pulled back to a source sum of at most
`s` points; all such sums lie in the finite box of radius
`s * coordinateRadius A`. -/
theorem dilated_volume_le_coordinateBound
    {d e s D k loss : ℕ} {A : Finset (LatticePoint d)}
    (f : LatticePoint d →+ LatticePoint e)
    (W : EnhancedCFPWitness (A.image f) s D k loss)
    (hinjectiveA : Set.InjOn f A) :
    (W.progression.dilate k).volume ≤
      (2 * (s * coordinateRadius A) + 1) ^ d := by
  let R := pullbackFinset f A W.reserved
  have hRsubset : R ⊆ A := pullbackFinset_subset f A W.reserved
  have hinjectiveR : Set.InjOn f R := hinjectiveA.mono hRsubset
  have hRimage : R.image f = W.reserved :=
    image_pullbackFinset f A W.reserved W.reserved_subset
  have hRcard : R.card ≤ s := by
    rw [card_pullbackFinset f A W.reserved hinjectiveA W.reserved_subset]
    exact W.reserved_small
  have htargetSums : GAP.subsetSums W.reserved ⊆
      (boundedSubsetSums A s).image f := by
    intro z hz
    have hz' : z ∈ GAP.subsetSums (R.image f) := by
      rwa [hRimage]
    obtain ⟨y, hy, hyMap⟩ :=
      exists_boundedSubsetSum_preimage f A R hinjectiveR hRsubset hRcard hz'
    exact Finset.mem_image.mpr ⟨y, hy, hyMap⟩
  have hboundedBox : boundedSubsetSums A s ⊆
      coordinateFinset d (s * coordinateRadius A) := by
    intro x hx
    apply mem_coordinateFinset_of_mem_coordinateWindow
    exact boundedSubsetSums_subset_coordinateWindow A (Nat.le_refl _) hx
  calc
    (W.progression.dilate k).volume ≤
        (GAP.subsetSums W.reserved).card :=
      W.dilated_volume_le_card_subsetSums
    _ ≤ ((boundedSubsetSums A s).image f).card :=
      Finset.card_le_card htargetSums
    _ ≤ (boundedSubsetSums A s).card := Finset.card_image_le
    _ ≤ (coordinateFinset d (s * coordinateRadius A)).card :=
      Finset.card_le_card hboundedBox
    _ = (2 * (s * coordinateRadius A) + 1) ^ d :=
      card_coordinateFinset d (s * coordinateRadius A)

/-- Polynomial center-radius bound used to fix the mixed-radix base before
the target witness is known. -/
theorem sum_symmetryRadii_le_rank_mul_coordinateBound
    {d e s D k loss : ℕ} {A : Finset (LatticePoint d)}
    (f : LatticePoint d →+ LatticePoint e)
    (W : EnhancedCFPWitness (A.image f) s D k loss)
    (hinjectiveA : Set.InjOn f A) :
    (∑ i, W.symmetryRadii i) ≤
      W.rank * (2 * (s * coordinateRadius A) + 1) ^ d := by
  have hvolume := dilated_volume_le_coordinateBound f W hinjectiveA
  have hradius (i : Fin W.rank) : W.symmetryRadii i ≤
      (2 * (s * coordinateRadius A) + 1) ^ d := by
    have hfactor :
        (W.progression.dilate k).widths i ≤
          (W.progression.dilate k).volume := by
      rw [GAP.volume]
      apply Finset.single_le_prod'
      · intro j _
        exact (W.progression.dilate k).width_pos j
      · exact Finset.mem_univ i
    calc
      W.symmetryRadii i ≤
          (W.progression.dilate k).widths i := by
        rw [W.symmetryCentered.dilate_width_eq]
        have hk : 1 ≤ k := W.k_pos
        nlinarith
      _ ≤ (W.progression.dilate k).volume := hfactor
      _ ≤ (2 * (s * coordinateRadius A) + 1) ^ d := hvolume
  calc
    (∑ i, W.symmetryRadii i) ≤
        (Finset.univ : Finset (Fin W.rank)).card •
          ((2 * (s * coordinateRadius A) + 1) ^ d) :=
      Finset.sum_le_card_nsmul Finset.univ W.symmetryRadii _
        (fun i _ ↦ hradius i)
    _ = W.rank * (2 * (s * coordinateRadius A) + 1) ^ d := by simp

/-! ## Bounded coefficients for a one-dimensional homogeneous translate -/

/-- Reduce every coefficient except one modulo a chosen nonzero direction,
absorbing the quotients into that direction. -/
def reducedSpanCoefficients {r : ℕ} (q z : Fin r → ℤ) (pivot : Fin r) :
    Fin r → ℤ := fun i ↦
  if i = pivot then
    z pivot + ∑ a ∈ Finset.univ.erase pivot, (z a / q pivot) * q a
  else z i % q pivot

/-- Coefficient reduction preserves the represented integer. -/
theorem sum_reducedSpanCoefficients {r : ℕ} (q z : Fin r → ℤ)
    (pivot : Fin r) :
    (∑ i, reducedSpanCoefficients q z pivot i * q i) =
      ∑ i, z i * q i := by
  classical
  rw [← Finset.sum_erase_add Finset.univ
    (fun i ↦ reducedSpanCoefficients q z pivot i * q i)
    (Finset.mem_univ pivot)]
  rw [← Finset.sum_erase_add Finset.univ
    (fun i ↦ z i * q i) (Finset.mem_univ pivot)]
  have hne (i : Fin r) (hi : i ∈ Finset.univ.erase pivot) : i ≠ pivot :=
    (Finset.mem_erase.mp hi).1
  have hreduced :
      (∑ i ∈ Finset.univ.erase pivot,
        reducedSpanCoefficients q z pivot i * q i) =
      ∑ i ∈ Finset.univ.erase pivot, (z i % q pivot) * q i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [reducedSpanCoefficients, if_neg (hne i hi)]
  rw [hreduced]
  rw [reducedSpanCoefficients, if_pos rfl]
  have hdiv (i : Fin r) : z i / q pivot * q pivot + z i % q pivot = z i :=
    Int.ediv_mul_add_emod _ _
  have hdecomp :
      (∑ i ∈ Finset.univ.erase pivot, z i * q i) =
      ∑ i ∈ Finset.univ.erase pivot,
        (z i / q pivot * q pivot + z i % q pivot) * q i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [hdiv]
  rw [hdecomp]
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]
  rw [Finset.sum_mul]
  ring_nf

/-- The reduced coefficients have a polynomial bound in the rank and in a
common bound for the represented integer and all directions. -/
theorem natAbs_reducedSpanCoefficients_le {r N : ℕ}
    (q z : Fin r → ℤ) (t : ℤ) (pivot : Fin r)
    (hpivot : q pivot ≠ 0)
    (hq : ∀ i, (q i).natAbs ≤ N) (ht : t.natAbs ≤ N)
    (hrep : (∑ i, z i * q i) = t) (i : Fin r) :
    (reducedSpanCoefficients q z pivot i).natAbs ≤ N + r * N * N := by
  classical
  let c := reducedSpanCoefficients q z pivot
  have hcRep : (∑ a, c a * q a) = t := by
    rw [sum_reducedSpanCoefficients]
    exact hrep
  have hmod (a : Fin r) : (z a % q pivot).natAbs < (q pivot).natAbs := by
    have hnonneg : 0 ≤ z a % q pivot := Int.emod_nonneg _ hpivot
    have hlt : z a % q pivot < ((q pivot).natAbs : ℤ) :=
      Int.emod_lt _ hpivot
    have hcast : ((z a % q pivot).natAbs : ℤ) <
        ((q pivot).natAbs : ℤ) := by
      rw [Int.natAbs_of_nonneg hnonneg]
      exact hlt
    exact_mod_cast hcast
  have hcOff (a : Fin r) (ha : a ≠ pivot) : (c a).natAbs ≤ N := by
    change (reducedSpanCoefficients q z pivot a).natAbs ≤ N
    rw [reducedSpanCoefficients, if_neg ha]
    exact (hmod a).le.trans (hq pivot)
  have hsumAbs :
      (∑ a ∈ Finset.univ.erase pivot, c a * q a).natAbs ≤ r * N * N := by
    calc
      (∑ a ∈ Finset.univ.erase pivot, c a * q a).natAbs ≤
          ∑ a ∈ Finset.univ.erase pivot, (c a * q a).natAbs :=
        Int.natAbs_sum_le _ _
      _ ≤ ∑ _a ∈ Finset.univ.erase pivot, N * N := by
        apply Finset.sum_le_sum
        intro a ha
        rw [Int.natAbs_mul]
        exact Nat.mul_le_mul (hcOff a (Finset.mem_erase.mp ha).1) (hq a)
      _ = (Finset.univ.erase pivot).card * (N * N) := by simp
      _ ≤ r * (N * N) := by
        exact Nat.mul_le_mul_right _ (by simp)
      _ = r * N * N := by ring
  by_cases hi : i = pivot
  · subst i
    have herase := Finset.sum_erase_add Finset.univ
      (fun a ↦ c a * q a) (Finset.mem_univ pivot)
    have hpivotEq : c pivot * q pivot =
        t - ∑ a ∈ Finset.univ.erase pivot, c a * q a := by
      rw [← hcRep, ← herase]
      abel
    have hproduct : (c pivot * q pivot).natAbs ≤ N + r * N * N := by
      rw [hpivotEq]
      exact (Int.natAbs_sub_le _ _).trans (Nat.add_le_add ht hsumAbs)
    calc
      (c pivot).natAbs ≤ (c pivot).natAbs * (q pivot).natAbs :=
        Nat.le_mul_of_pos_right _ (Int.natAbs_pos.mpr hpivot)
      _ = (c pivot * q pivot).natAbs := (Int.natAbs_mul _ _).symm
      _ ≤ N + r * N * N := hproduct
  · exact (hcOff i hi).trans (Nat.le_add_right _ _)

/-- Every one-dimensional integer-span representation admits coefficients
with a rank-polynomial bound. -/
theorem exists_bounded_span_coefficients {r N : ℕ}
    (q : Fin r → ℤ) (t : ℤ)
    (hq : ∀ i, (q i).natAbs ≤ N) (ht : t.natAbs ≤ N)
    (hspan : ∃ z : Fin r → ℤ, (∑ i, z i * q i) = t) :
    ∃ z : Fin r → ℤ,
      (∑ i, z i * q i) = t ∧ ∀ i, (z i).natAbs ≤ N + r * N * N := by
  classical
  by_cases hnonzero : ∃ i, q i ≠ 0
  · obtain ⟨pivot, hpivot⟩ := hnonzero
    obtain ⟨z, hz⟩ := hspan
    refine ⟨reducedSpanCoefficients q z pivot,
      (sum_reducedSpanCoefficients q z pivot).trans hz, ?_⟩
    exact natAbs_reducedSpanCoefficients_le q z t pivot hpivot hq ht hz
  · push Not at hnonzero
    have htzero : t = 0 := by
      obtain ⟨z, hz⟩ := hspan
      rw [show (∑ i, z i * q i) = 0 by simp [hnonzero]] at hz
      exact hz.symm
    refine ⟨0, ?_, ?_⟩
    · simp [htzero]
    · intro i
      simp

/-- In one dimension, homogeneity of the covered translate and centering of
the progression express the translate itself in the integer span of the
progression directions. -/
theorem translatePoint_zero_mem_stepSpan
    {s D k loss : ℕ} {A : Finset (LatticePoint 1)}
    (W : EnhancedCFPWitness A s D k loss) :
    ∃ z : Fin W.rank → ℤ,
      (∑ i, z i * W.progression.steps i 0) = W.translatePoint 0 := by
  classical
  obtain ⟨z, hz⟩ := W.covered_translate_homogeneous
  let radii := W.symmetryRadii
  refine ⟨fun i ↦ z i + (k * radii i : ℕ), ?_⟩
  have hz0 := congrFun hz 0
  have hoffset0 := congrFun ((W.symmetryCentered.dilate k).offset_eq) 0
  simp only [GAP.dilate_steps] at hoffset0
  change W.translatePoint 0 + (W.progression.dilate k).offset 0 = _ at hz0
  rw [hoffset0] at hz0
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]
  push_cast at hz0 ⊢
  linear_combination -hz0

/-- The one-dimensional covered translate has a representation whose
coefficients are bounded solely in terms of the target input radius and the
rank.  No coefficient or translate bound is exposed to the caller. -/
theorem exists_bounded_translatePoint_coefficients
    {s D k loss : ℕ} {A : Finset (LatticePoint 1)}
    (W : EnhancedCFPWitness A s D k loss) :
    ∃ z : Fin W.rank → ℤ,
      (∑ i, z i * W.progression.steps i 0) = W.translatePoint 0 ∧
      ∀ i, (z i).natAbs ≤
        2 * s * coordinateRadius A +
          W.rank * (2 * s * coordinateRadius A) *
            (2 * s * coordinateRadius A) := by
  let N := 2 * s * coordinateRadius A
  apply exists_bounded_span_coefficients
  · intro i
    exact progression_step_natAbs_le_of_covered W i 0
  · exact (translatePoint_natAbs_le_of_covered W 0).trans (by
      nlinarith)
  · exact translatePoint_zero_mem_stepSpan W

/-- The common source coordinate window needed by the Appendix lift.  Its
ingredients are the source subset-sum radius, the lifted step radius, and
the centered-coordinate bounds for the base GAP and translated dilate. -/
noncomputable def hornerLiftWindowRadius
    {d b s D k loss : ℕ} {A : Finset (LatticePoint d)}
    (W : EnhancedCFPWitness
      (A.image (hornerLatticeHom d b)) s D k loss) : ℕ :=
  let L := 2 * s * coordinateRadius A
  let T := s * (∑ i, W.symmetryRadii i) * L
  max (s * coordinateRadius A)
    (max (3 * (∑ i, W.symmetryRadii i) * L)
      (T + 3 * (∑ i, k * W.symmetryRadii i) * L))

/-- A witness-independent upper bound for the Appendix no-carry window.
This is the radius used to choose the Horner base before the target theorem
produces its witness. -/
def uniformHornerLiftWindowRadius {d : ℕ}
    (D s : ℕ) (A : Finset (LatticePoint d)) : ℕ :=
  let L := 2 * s * coordinateRadius A
  let Rho := D * (2 * (s * coordinateRadius A) + 1) ^ d
  let T := s * Rho * L
  max (s * coordinateRadius A)
    (max (3 * Rho * L) (T + 3 * (s * Rho) * L))

/-- Canonical Appendix base, fixed before applying the one-dimensional
structure theorem. -/
def appendixHornerBase {d : ℕ}
    (D s : ℕ) (A : Finset (LatticePoint d)) : ℕ :=
  2 * uniformHornerLiftWindowRadius D s A + 1

theorem appendixHornerBase_width {d : ℕ}
    (D s : ℕ) (A : Finset (LatticePoint d)) :
    2 * uniformHornerLiftWindowRadius D s A < appendixHornerBase D s A := by
  exact Nat.lt_succ_self _

/-- The window extracted from any rank-`D` target witness is bounded by the
uniform radius chosen before that witness. -/
theorem hornerLiftWindowRadius_le_uniform
    {d b s D k loss : ℕ} {A : Finset (LatticePoint d)}
    (W : EnhancedCFPWitness
      (A.image (hornerLatticeHom d b)) s D k loss)
    (hinjectiveA : Set.InjOn (hornerLatticeHom d b) A) :
    hornerLiftWindowRadius W ≤ uniformHornerLiftWindowRadius D s A := by
  have hsum : (∑ i, W.symmetryRadii i) ≤
      D * (2 * (s * coordinateRadius A) + 1) ^ d := by
    exact (sum_symmetryRadii_le_rank_mul_coordinateBound
      (hornerLatticeHom d b) W hinjectiveA).trans
      (Nat.mul_le_mul_right _ W.rank_le)
  have hksum : (∑ i, k * W.symmetryRadii i) ≤
      s * (D * (2 * (s * coordinateRadius A) + 1) ^ d) := by
    calc
      (∑ i, k * W.symmetryRadii i) =
          k * ∑ i, W.symmetryRadii i := by
        exact (Finset.mul_sum Finset.univ W.symmetryRadii k).symm
      _ ≤ s * (D * (2 * (s * coordinateRadius A) + 1) ^ d) :=
        Nat.mul_le_mul W.scale_upper hsum
  dsimp [hornerLiftWindowRadius, uniformHornerLiftWindowRadius]
  apply max_le
  · exact Nat.le_max_left _ _
  · apply max_le
    · have hbase :
          3 * (∑ i, W.symmetryRadii i) *
              (2 * s * coordinateRadius A) ≤
            3 * (D * (2 * (s * coordinateRadius A) + 1) ^ d) *
              (2 * s * coordinateRadius A) := by
          exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 3 hsum)
      exact hbase.trans
        ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _))
    · have htranslate :
          s * (∑ i, W.symmetryRadii i) *
              (2 * s * coordinateRadius A) ≤
            s * (D * (2 * (s * coordinateRadius A) + 1) ^ d) *
              (2 * s * coordinateRadius A) := by
          exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left s hsum)
      have hdilate :
          3 * (∑ i, k * W.symmetryRadii i) *
              (2 * s * coordinateRadius A) ≤
            3 * (s * (D *
              (2 * (s * coordinateRadius A) + 1) ^ d)) *
              (2 * s * coordinateRadius A) := by
          exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 3 hksum)
      exact (Nat.add_le_add htranslate hdilate).trans
        ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))

/-- Coefficients certifying homogeneity of the target covered translate. -/
noncomputable def coveredSpanCoefficients {e s D k loss : ℕ}
    {A : Finset (LatticePoint e)}
    (W : EnhancedCFPWitness A s D k loss) : Fin W.rank → ℤ :=
  Classical.choose W.covered_translate_homogeneous

theorem coveredSpanCoefficients_spec {e s D k loss : ℕ}
    {A : Finset (LatticePoint e)}
    (W : EnhancedCFPWitness A s D k loss) :
    W.translatePoint + (W.progression.dilate k).offset =
      (fun j ↦ ∑ i, coveredSpanCoefficients W i * W.progression.steps i j) :=
  Classical.choose_spec W.covered_translate_homogeneous

/-- Lift the centered target progression along chosen preimages of all its
directions. -/
noncomputable def liftedProgression {d e s D k loss : ℕ}
    {A : Finset (LatticePoint e)}
    (W : EnhancedCFPWitness A s D k loss)
    (stepLift : Fin W.rank → LatticePoint d) : GAP d W.rank :=
  centeredLiftGAP W.progression W.symmetryRadii W.symmetryCentered stepLift

/-- Choose the source translation canonically from the target homogeneity
coefficients.  This makes the lifted covered translate homogeneous by
construction. -/
noncomputable def liftedTranslatePoint {d e s D k loss : ℕ}
    {A : Finset (LatticePoint e)}
    (W : EnhancedCFPWitness A s D k loss)
    (stepLift : Fin W.rank → LatticePoint d) : LatticePoint d :=
  (∑ i, coveredSpanCoefficients W i • stepLift i) -
    ((liftedProgression W stepLift).dilate k).offset

theorem mapGAP_liftedProgression {d e s D k loss : ℕ}
    {A : Finset (LatticePoint e)}
    (f : LatticePoint d →+ LatticePoint e)
    (W : EnhancedCFPWitness A s D k loss)
    (stepLift : Fin W.rank → LatticePoint d)
    (hsteps : ∀ i, f (stepLift i) = W.progression.steps i) :
    mapGAP f (liftedProgression W stepLift) = W.progression := by
  exact mapGAP_centeredLiftGAP f W.progression W.symmetryRadii
    W.symmetryCentered stepLift hsteps

theorem map_liftedTranslatePoint {d e s D k loss : ℕ}
    {A : Finset (LatticePoint e)}
    (f : LatticePoint d →+ LatticePoint e)
    (W : EnhancedCFPWitness A s D k loss)
    (stepLift : Fin W.rank → LatticePoint d)
    (hsteps : ∀ i, f (stepLift i) = W.progression.steps i) :
    f (liftedTranslatePoint W stepLift) = W.translatePoint := by
  have hgap :
      mapGAP f ((liftedProgression W stepLift).dilate k) =
        W.progression.dilate k := by
    rw [mapGAP_dilate, mapGAP_liftedProgression f W stepLift hsteps]
  have hoffset :
      f ((liftedProgression W stepLift).dilate k).offset =
        (W.progression.dilate k).offset := by
    simpa only [mapGAP] using congrArg GAP.offset hgap
  rw [liftedTranslatePoint, map_sub, map_sum]
  simp_rw [map_zsmul, hsteps]
  rw [hoffset]
  have hspan := coveredSpanCoefficients_spec W
  have hspan' :
      W.translatePoint + (W.progression.dilate k).offset =
        ∑ i, coveredSpanCoefficients W i • W.progression.steps i := by
    rw [hspan]
    ext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [← hspan']
  abel

theorem liftedProgression_centered {d e s D k loss : ℕ}
    {A : Finset (LatticePoint e)}
    (W : EnhancedCFPWitness A s D k loss)
    (stepLift : Fin W.rank → LatticePoint d) :
    (liftedProgression W stepLift).Centered W.symmetryRadii :=
  centeredLiftGAP_centered W.progression W.symmetryRadii
    W.symmetryCentered stepLift

theorem lifted_covered_translate_homogeneous {d e s D k loss : ℕ}
    {A : Finset (LatticePoint e)}
    (W : EnhancedCFPWitness A s D k loss)
    (stepLift : Fin W.rank → LatticePoint d) :
    ∃ z : Fin W.rank → ℤ,
      liftedTranslatePoint W stepLift +
          ((liftedProgression W stepLift).dilate k).offset =
        (fun j ↦ ∑ i, z i * (liftedProgression W stepLift).steps i j) := by
  refine ⟨coveredSpanCoefficients W, ?_⟩
  have hrhs :
      (fun j ↦ ∑ i, coveredSpanCoefficients W i *
        (liftedProgression W stepLift).steps i j) =
      ∑ i, coveredSpanCoefficients W i • stepLift i := by
    ext j
    simp only [liftedProgression, centeredLiftGAP, liftGAP,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hrhs, liftedTranslatePoint]
  exact sub_add_cancel _ _

/-- Exact Appendix version of the homogeneous translate lift.  The target
translate is first represented as the sum of the centered coordinates of
the reserved subset which covers it.  Hence the lifted translate is bounded
by `s * sum radii * L`, with no dependence on the magnitude of the encoded
target integers. -/
theorem exists_centered_bounded_homogeneous_translateLift
    {d b s D k loss L : ℕ} {A : Finset (LatticePoint d)}
    (W : EnhancedCFPWitness
      (A.image (hornerLatticeHom d b)) s D k loss)
    (stepLift : Fin W.rank → LatticePoint d)
    (hsteps : ∀ i,
      hornerLatticeHom d b (stepLift i) = W.progression.steps i)
    (hstepBound : ∀ i j, (stepLift i j).natAbs ≤ L) :
    ∃ translateLift : LatticePoint d,
      hornerLatticeHom d b translateLift = W.translatePoint ∧
      (∀ j, (translateLift j).natAbs ≤
        s * (∑ i, W.symmetryRadii i) * L) ∧
      ∃ z : Fin W.rank → ℤ,
        translateLift + ((liftedProgression W stepLift).dilate k).offset =
          (fun j ↦ ∑ i,
            z i * (liftedProgression W stepLift).steps i j) := by
  classical
  obtain ⟨z, hz, hzBound⟩ :=
    exists_centered_bounded_translatePoint_coefficients W
  let translateLift : LatticePoint d := ∑ i, z i • stepLift i
  refine ⟨translateLift, ?_, ?_, ?_⟩
  · rw [hz]
    rw [map_sum]
    simp_rw [map_zsmul, hsteps]
    ext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  · intro j
    calc
      (translateLift j).natAbs =
          (∑ i, z i * stepLift i j).natAbs := by
            simp only [translateLift, Finset.sum_apply, Pi.smul_apply,
              smul_eq_mul]
      _ ≤ ∑ i, (z i * stepLift i j).natAbs :=
        Int.natAbs_sum_le _ _
      _ ≤ ∑ i, (s * W.symmetryRadii i) * L := by
        apply Finset.sum_le_sum
        intro i _
        rw [Int.natAbs_mul]
        exact Nat.mul_le_mul (hzBound i) (hstepBound i j)
      _ = s * (∑ i, W.symmetryRadii i) * L := by
        calc
          (∑ i, (s * W.symmetryRadii i) * L) =
              ∑ i, s * (W.symmetryRadii i * L) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Nat.mul_assoc]
          _ = s * ∑ i, W.symmetryRadii i * L := by
            exact (Finset.mul_sum Finset.univ
              (fun i ↦ W.symmetryRadii i * L) s).symm
          _ = s * (∑ i, W.symmetryRadii i) * L := by
            calc
              s * (∑ i, W.symmetryRadii i * L) =
                  s * ((∑ i, W.symmetryRadii i) * L) := by
                exact congrArg (fun x ↦ s * x)
                  (Finset.sum_mul Finset.univ W.symmetryRadii L).symm
              _ = s * (∑ i, W.symmetryRadii i) * L := by
                rw [Nat.mul_assoc]
  · refine ⟨fun i ↦ z i - (k * W.symmetryRadii i : ℕ), ?_⟩
    rw [((liftedProgression_centered W stepLift).dilate k).offset_eq]
    ext j
    simp only [translateLift, liftedProgression, centeredLiftGAP, liftGAP,
      Pi.add_apply, Pi.neg_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, GAP.dilate_steps]
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib]
    push_cast
    ring

/-- Replace the first bounded preimage of the target translate by a bounded
homogeneous one.  In dimension one the target homogeneity relation admits
the reduced coefficients above; using those same coefficients on the
bounded lifted directions gives the required source translate. -/
theorem exists_bounded_homogeneous_translateLift
    {d b s D k loss L : ℕ} {A : Finset (LatticePoint d)}
    (W : EnhancedCFPWitness
      (A.image (hornerLatticeHom d b)) s D k loss)
    (stepLift : Fin W.rank → LatticePoint d)
    (hsteps : ∀ i,
      hornerLatticeHom d b (stepLift i) = W.progression.steps i)
    (hstepBound : ∀ i j, (stepLift i j).natAbs ≤ L) :
    ∃ translateLift : LatticePoint d,
      hornerLatticeHom d b translateLift = W.translatePoint ∧
      (∀ j, (translateLift j).natAbs ≤
        W.rank *
          (2 * s * coordinateRadius
              (A.image (hornerLatticeHom d b)) +
            W.rank *
              (2 * s * coordinateRadius
                (A.image (hornerLatticeHom d b))) *
              (2 * s * coordinateRadius
                (A.image (hornerLatticeHom d b)))) * L) ∧
      ∃ z : Fin W.rank → ℤ,
        translateLift + ((liftedProgression W stepLift).dilate k).offset =
          (fun j ↦ ∑ i,
            z i * (liftedProgression W stepLift).steps i j) := by
  classical
  obtain ⟨z, hz, hzBound⟩ :=
    exists_bounded_translatePoint_coefficients W
  let translateLift : LatticePoint d := ∑ i, z i • stepLift i
  refine ⟨translateLift, ?_, ?_, ?_⟩
  · ext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    rw [map_sum]
    simp_rw [map_zsmul, hsteps]
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hz
  · intro j
    calc
      (translateLift j).natAbs =
          (∑ i, z i * stepLift i j).natAbs := by
            simp only [translateLift, Finset.sum_apply, Pi.smul_apply,
              smul_eq_mul]
      _ ≤ ∑ i, (z i * stepLift i j).natAbs :=
        Int.natAbs_sum_le _ _
      _ ≤ ∑ _i : Fin W.rank,
          (2 * s * coordinateRadius
              (A.image (hornerLatticeHom d b)) +
            W.rank *
              (2 * s * coordinateRadius
                (A.image (hornerLatticeHom d b))) *
              (2 * s * coordinateRadius
                (A.image (hornerLatticeHom d b)))) * L := by
        apply Finset.sum_le_sum
        intro i _
        rw [Int.natAbs_mul]
        exact Nat.mul_le_mul (hzBound i) (hstepBound i j)
      _ = W.rank *
          (2 * s * coordinateRadius
              (A.image (hornerLatticeHom d b)) +
            W.rank *
              (2 * s * coordinateRadius
                (A.image (hornerLatticeHom d b))) *
              (2 * s * coordinateRadius
                (A.image (hornerLatticeHom d b)))) * L := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        simp only [Nat.mul_assoc]
        rfl
  · refine ⟨fun i ↦ z i - (k * W.symmetryRadii i : ℕ), ?_⟩
    rw [((liftedProgression_centered W stepLift).dilate k).offset_eq]
    ext j
    simp only [translateLift, liftedProgression, centeredLiftGAP, liftGAP,
      Pi.add_apply, Pi.neg_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, GAP.dilate_steps]
    change (∑ i, z i * stepLift i j) +
        -(∑ i, (k * W.symmetryRadii i : ℕ) * stepLift i j) = _
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib]
    push_cast
    ring

/-- General form of the no-carry coverage pullback.  It applies to any
source GAP whose mapped presentation is exactly the target GAP. -/
theorem covered_of_mapGAP {d e r k : ℕ}
    (f : LatticePoint d →+ LatticePoint e) (Q : GAP d r) (P : GAP e r)
    (hmap : mapGAP f Q = P)
    (translateLift : LatticePoint d) (translateTarget : LatticePoint e)
    (htranslate : f translateLift = translateTarget)
    (R : Finset (LatticePoint d)) (hinjectiveR : Set.InjOn f R)
    (window : Set (LatticePoint d))
    (hstructured :
      (translate translateLift (Q.dilate k).carrier :
        Set (LatticePoint d)) ⊆ window)
    (hsubsetSums : (GAP.subsetSums R : Set (LatticePoint d)) ⊆ window)
    (hinjectiveWindow : Set.InjOn f window)
    (hcovered :
      translate translateTarget (P.dilate k).carrier ⊆
        GAP.subsetSums (R.image f)) :
    translate translateLift (Q.dilate k).carrier ⊆ GAP.subsetSums R := by
  intro x hx
  obtain ⟨q, hq, rfl⟩ := mem_translate_iff.mp hx
  have hqTarget : f q ∈ (P.dilate k).carrier := by
    have hqMapped : f q ∈ (mapGAP f (Q.dilate k)).carrier := by
      rw [mapGAP_carrier]
      exact Finset.mem_image.mpr ⟨q, hq, rfl⟩
    rw [mapGAP_dilate, hmap] at hqMapped
    exact hqMapped
  have htarget : f (translateLift + q) ∈
      translate translateTarget (P.dilate k).carrier := by
    apply mem_translate_iff.mpr
    exact ⟨f q, hqTarget, by simp only [map_add, htranslate]⟩
  obtain ⟨y, hySums, hyMap⟩ :=
    exists_subsetSum_preimage f R hinjectiveR (hcovered htarget)
  have hsourceWindow : translateLift + q ∈ window :=
    hstructured (mem_translate_iff.mpr ⟨q, hq, rfl⟩)
  have hyWindow : y ∈ window := hsubsetSums hySums
  have hxy : translateLift + q = y :=
    hinjectiveWindow hsourceWindow hyWindow (by rw [hyMap])
  rwa [hxy]

/-- Assemble the full source CFP witness once the quantitative mixed-radix
estimates place the input set, the lifted progression, its covered translate,
and the relevant subset sums in one injective window.  All qualitative
transport (rank, loss, scale, symmetry, homogeneity, and properness) is
performed here. -/
noncomputable def liftEnhancedCFPWitness_of_injectiveWindow
    {d e s D k loss : ℕ} {A : Finset (LatticePoint d)}
    (f : LatticePoint d →+ LatticePoint e)
    (W : EnhancedCFPWitness (A.image f) s D k loss)
    (stepLift : Fin W.rank → LatticePoint d)
    (hsteps : ∀ i, f (stepLift i) = W.progression.steps i)
    (translateLift : LatticePoint d)
    (htranslate : f translateLift = W.translatePoint)
    (htranslateHomogeneous :
      ∃ z : Fin W.rank → ℤ,
        translateLift + ((liftedProgression W stepLift).dilate k).offset =
          (fun j ↦ ∑ i, z i * (liftedProgression W stepLift).steps i j))
    (window : Set (LatticePoint d))
    (hAWindow : (A : Set (LatticePoint d)) ⊆ window)
    (hprogressionWindow :
      ((liftedProgression W stepLift).carrier : Set (LatticePoint d)) ⊆
        window)
    (htranslatedWindow :
      (translate translateLift
          ((liftedProgression W stepLift).dilate k).carrier :
        Set (LatticePoint d)) ⊆ window)
    (hsubsetSumsWindow :
      (GAP.subsetSums (pullbackFinset f A W.reserved) :
        Set (LatticePoint d)) ⊆ window)
    (hinjectiveWindow : Set.InjOn f window) :
    EnhancedCFPWitness A s D k loss := by
  let core := pullbackFinset f A W.core
  let reserved := pullbackFinset f A W.reserved
  let Q := liftedProgression W stepLift
  let t := translateLift
  have hinjectiveA : Set.InjOn f A := hinjectiveWindow.mono hAWindow
  have hmap : mapGAP f Q = W.progression := by
    exact mapGAP_liftedProgression f W stepLift hsteps
  have hcoreImage : core.image f = W.core := by
    exact image_pullbackFinset f A W.core W.core_subset
  have hreservedImage : reserved.image f = W.reserved := by
    exact image_pullbackFinset f A W.reserved W.reserved_subset
  have hcoreCard : core.card = W.core.card := by
    exact card_pullbackFinset f A W.core hinjectiveA W.core_subset
  have hreservedCard : reserved.card = W.reserved.card := by
    exact card_pullbackFinset f A W.reserved hinjectiveA W.reserved_subset
  have hACard : (A.image f).card = A.card :=
    Finset.card_image_of_injOn hinjectiveA
  have hcoreZero : insert 0 core ⊆ Q.carrier := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hxcore
    · exact (liftedProgression_centered W stepLift).zero_mem_carrier
    · have hxdata := mem_pullbackFinset f A W.core x |>.mp hxcore
      have hfxTarget : f x ∈ W.progression.carrier :=
        W.core_zero_subset (Finset.mem_insert_of_mem hxdata.2)
      have htargetImage : W.progression.carrier = Q.carrier.image f := by
        rw [← hmap, mapGAP_carrier]
      rw [htargetImage] at hfxTarget
      obtain ⟨q, hq, hqx⟩ := Finset.mem_image.mp hfxTarget
      have hqWindow : q ∈ window := hprogressionWindow hq
      have hxWindow : x ∈ window := hAWindow hxdata.1
      have hqeq : q = x := hinjectiveWindow hqWindow hxWindow hqx
      simpa [hqeq] using hq
  have hcovered :
      translate t (Q.dilate k).carrier ⊆ GAP.subsetSums reserved := by
    apply covered_of_mapGAP f Q W.progression hmap t W.translatePoint
      htranslate reserved
      (hinjectiveA.mono (pullbackFinset_subset f A W.reserved)) window
      htranslatedWindow hsubsetSumsWindow hinjectiveWindow
    rw [hreservedImage]
    exact W.covered
  have hproper : Q.Proper := by
    apply proper_of_mapGAP_proper f Q
    rw [hmap]
    exact W.progression_proper
  have hdilateProper : (Q.dilate k).Proper := by
    apply proper_of_mapGAP_proper f
    rw [mapGAP_dilate, hmap]
    exact W.dilate_proper
  refine
    { core := core
      reserved := reserved
      rank := W.rank
      rank_le := W.rank_le
      progression := Q
      core_subset := pullbackFinset_subset f A W.core
      reserved_subset_core := pullbackFinset_mono f A W.reserved_subset_core
      core_large := ?_
      reserved_small := ?_
      core_zero_subset := hcoreZero
      homogeneous := (liftedProgression_centered W stepLift).homogeneous
      translatePoint := t
      covered := hcovered
      dilate_proper := hdilateProper
      k_pos := W.k_pos
      scaleNum := W.scaleNum
      scaleDen := W.scaleDen
      scaleNum_pos := W.scaleNum_pos
      scaleDen_pos := W.scaleDen_pos
      scale_lower := W.scale_lower
      scale_upper := W.scale_upper
      progression_proper := hproper
      progression_symmetric :=
        ⟨W.symmetryRadii, liftedProgression_centered W stepLift⟩
      progression_nondegenerate := ?_
      covered_translate_homogeneous := htranslateHomogeneous }
  · calc
      A.card = (A.image f).card := hACard.symm
      _ ≤ W.core.card + loss := W.core_large
      _ = core.card + loss := by rw [hcoreCard]
  · rw [hreservedCard]
    exact W.reserved_small
  · intro i
    exact W.progression_nondegenerate i

/-- Mixed-radix specialization of the full witness lift.  The input set and
all subset sums of the pulled-back reserve are placed in the coordinate
window automatically.  The two remaining geometric hypotheses are exactly
the source Appendix estimates: the lifted base progression and its covered
translate must stay in that same no-carry window. -/
noncomputable def liftEnhancedCFPWitness_horner
    {d b s D k loss M : ℕ} {A : Finset (LatticePoint d)}
    (W : EnhancedCFPWitness
      (A.image (hornerLatticeHom d b)) s D k loss)
    (stepLift : Fin W.rank → LatticePoint d)
    (hsteps : ∀ i,
      hornerLatticeHom d b (stepLift i) = W.progression.steps i)
    (translateLift : LatticePoint d)
    (htranslate : hornerLatticeHom d b translateLift = W.translatePoint)
    (htranslateHomogeneous :
      ∃ z : Fin W.rank → ℤ,
        translateLift + ((liftedProgression W stepLift).dilate k).offset =
          (fun j ↦ ∑ i, z i * (liftedProgression W stepLift).steps i j))
    (hM : s * coordinateRadius A ≤ M)
    (hbase :
      ((liftedProgression W stepLift).carrier : Set (LatticePoint d)) ⊆
        coordinateWindow d M)
    (hcovered :
      (translate translateLift
          ((liftedProgression W stepLift).dilate k).carrier :
        Set (LatticePoint d)) ⊆ coordinateWindow d M)
    (hwidth : 2 * M < b) :
    EnhancedCFPWitness A s D k loss := by
  have hinjectiveWindow :
      Set.InjOn (hornerLatticeHom d b) (coordinateWindow d M) :=
    hornerLatticeHom_injOn_coordinateWindow (by omega) hwidth
  have hradius : coordinateRadius A ≤ M := by
    calc
      coordinateRadius A = 1 * coordinateRadius A := by simp
      _ ≤ s * coordinateRadius A :=
        Nat.mul_le_mul_right _ (Nat.succ_le_iff.mpr W.s_pos)
      _ ≤ M := hM
  have hAWindow :
      (A : Set (LatticePoint d)) ⊆ coordinateWindow d M :=
    subset_coordinateWindow A hradius
  have hinjectiveA : Set.InjOn (hornerLatticeHom d b) A :=
    hinjectiveWindow.mono hAWindow
  have hreservedCard :
      (pullbackFinset (hornerLatticeHom d b) A W.reserved).card ≤ s := by
    rw [card_pullbackFinset (hornerLatticeHom d b) A W.reserved
      hinjectiveA W.reserved_subset]
    exact W.reserved_small
  have hsubsetSumsWindow :
      (GAP.subsetSums
          (pullbackFinset (hornerLatticeHom d b) A W.reserved) :
        Set (LatticePoint d)) ⊆ coordinateWindow d M := by
    intro x hx
    apply boundedSubsetSums_subset_coordinateWindow A hM
    exact subsetSums_subset_boundedSubsetSums
      (pullbackFinset_subset (hornerLatticeHom d b) A W.reserved)
      hreservedCard hx
  exact liftEnhancedCFPWitness_of_injectiveWindow
    (hornerLatticeHom d b) W stepLift hsteps translateLift htranslate
    htranslateHomogeneous (coordinateWindow d M) hAWindow hbase hcovered
    hsubsetSumsWindow hinjectiveWindow

/-- Complete quantitative mixed-radix lift.  Target coverage constructs
bounded preimages of all directions; target homogeneity is reduced to
bounded one-dimensional coefficients and constructs a homogeneous source
translate; the single displayed base inequality then places every object in
one no-carry window. -/
noncomputable def liftEnhancedCFPWitness_horner_of_largeBase
    {d b s D k loss : ℕ} {A : Finset (LatticePoint d)}
    (W : EnhancedCFPWitness
      (A.image (hornerLatticeHom d b)) s D k loss)
    (hwidth : 2 * hornerLiftWindowRadius W < b) :
    EnhancedCFPWitness A s D k loss := by
  let L := 2 * s * coordinateRadius A
  let T := s * (∑ i, W.symmetryRadii i) * L
  let M := hornerLiftWindowRadius W
  have hsourceM : s * coordinateRadius A ≤ M := by
    simp [M, hornerLiftWindowRadius]
  have hradiusM : coordinateRadius A ≤ M := by
    calc
      coordinateRadius A = 1 * coordinateRadius A := by simp
      _ ≤ s * coordinateRadius A :=
        Nat.mul_le_mul_right _ (Nat.succ_le_iff.mpr W.s_pos)
      _ ≤ M := hsourceM
  have hinjectiveWindow :
      Set.InjOn (hornerLatticeHom d b) (coordinateWindow d M) :=
    hornerLatticeHom_injOn_coordinateWindow (by omega) (by
      simpa only [M] using hwidth)
  have hinjectiveA : Set.InjOn (hornerLatticeHom d b) A :=
    hinjectiveWindow.mono (subset_coordinateWindow A hradiusM)
  have hexistsLifts := exists_bounded_step_translate_lifts
    (hornerLatticeHom d b) W hinjectiveA
  let stepLift := Classical.choose hexistsLifts
  have hexistsFirstTranslate := Classical.choose_spec hexistsLifts
  let firstTranslateLift := Classical.choose hexistsFirstTranslate
  have hlifts := Classical.choose_spec hexistsFirstTranslate
  have hsteps : ∀ i,
      hornerLatticeHom d b (stepLift i) = W.progression.steps i := hlifts.1
  have hstepBound : ∀ i j,
      (stepLift i j).natAbs ≤ 2 * s * coordinateRadius A := hlifts.2.1
  have hstepBoundL : ∀ i j, (stepLift i j).natAbs ≤ L := by
    simpa only [L] using hstepBound
  have hexistsHomogeneousTranslate :=
    exists_centered_bounded_homogeneous_translateLift
      W stepLift hsteps hstepBoundL
  let translateLift := Classical.choose hexistsHomogeneousTranslate
  have htranslateData := Classical.choose_spec hexistsHomogeneousTranslate
  have htranslate :
      hornerLatticeHom d b translateLift = W.translatePoint :=
    htranslateData.1
  have htranslateBound := htranslateData.2.1
  have htranslateHomogeneous := htranslateData.2.2
  have htranslateBoundT : ∀ j, (translateLift j).natAbs ≤ T := by
    simpa only [T] using htranslateBound
  have hbaseSmall :
      ((liftedProgression W stepLift).carrier : Set (LatticePoint d)) ⊆
        coordinateWindow d (3 * (∑ i, W.symmetryRadii i) * L) :=
    centered_carrier_subset_coordinateWindow
      (liftedProgression_centered W stepLift) hstepBoundL
  have hbaseRadius : 3 * (∑ i, W.symmetryRadii i) * L ≤ M := by
    simp [M, hornerLiftWindowRadius, L, T]
  have hbase :
      ((liftedProgression W stepLift).carrier : Set (LatticePoint d)) ⊆
        coordinateWindow d M :=
    hbaseSmall.trans (coordinateWindow_mono hbaseRadius)
  have hcoveredSmall :
      (translate translateLift
          ((liftedProgression W stepLift).dilate k).carrier :
        Set (LatticePoint d)) ⊆
      coordinateWindow d
        (T + 3 * (∑ i, k * W.symmetryRadii i) * L) :=
    translate_dilate_subset_coordinateWindow
      (liftedProgression_centered W stepLift) hstepBoundL translateLift
        htranslateBoundT
  have hcoveredRadius :
      T + 3 * (∑ i, k * W.symmetryRadii i) * L ≤ M := by
    simp [M, hornerLiftWindowRadius, L, T]
  have hcovered :
      (translate translateLift
          ((liftedProgression W stepLift).dilate k).carrier :
        Set (LatticePoint d)) ⊆ coordinateWindow d M :=
    hcoveredSmall.trans (coordinateWindow_mono hcoveredRadius)
  exact liftEnhancedCFPWitness_horner W stepLift hsteps translateLift
    htranslate htranslateHomogeneous hsourceM hbase hcovered (by
      simpa only [M] using hwidth)

/-- Witness-independent-base form of the complete lift. -/
noncomputable def liftEnhancedCFPWitness_horner_of_uniformBase
    {d b s D k loss : ℕ} {A : Finset (LatticePoint d)}
    (W : EnhancedCFPWitness
      (A.image (hornerLatticeHom d b)) s D k loss)
    (hwidth : 2 * uniformHornerLiftWindowRadius D s A < b) :
    EnhancedCFPWitness A s D k loss := by
  let M := uniformHornerLiftWindowRadius D s A
  have hsourceM : s * coordinateRadius A ≤ M := by
    simp [M, uniformHornerLiftWindowRadius]
  have hradiusM : coordinateRadius A ≤ M := by
    calc
      coordinateRadius A = 1 * coordinateRadius A := by simp
      _ ≤ s * coordinateRadius A :=
        Nat.mul_le_mul_right _ (Nat.succ_le_iff.mpr W.s_pos)
      _ ≤ M := hsourceM
  have hinjectiveWindow :
      Set.InjOn (hornerLatticeHom d b) (coordinateWindow d M) :=
    hornerLatticeHom_injOn_coordinateWindow (by omega) (by
      simpa only [M] using hwidth)
  have hinjectiveA : Set.InjOn (hornerLatticeHom d b) A :=
    hinjectiveWindow.mono (subset_coordinateWindow A hradiusM)
  exact liftEnhancedCFPWitness_horner_of_largeBase W
    ((Nat.mul_le_mul_left 2
      (hornerLiftWindowRadius_le_uniform W hinjectiveA)).trans_lt hwidth)

/-- Canonical no-carry transport: the base is an explicit function of the
source set and the already-uniform theorem parameters, so no arithmetic
hypothesis remains at the consumer boundary. -/
noncomputable def liftEnhancedCFPWitness_appendixHornerBase
    {d s D k loss : ℕ} {A : Finset (LatticePoint d)}
    (W : EnhancedCFPWitness
      (A.image (hornerLatticeHom d (appendixHornerBase D s A)))
        s D k loss) :
    EnhancedCFPWitness A s D k loss :=
  liftEnhancedCFPWitness_horner_of_uniformBase W
    (appendixHornerBase_width D s A)

/-- Fixed-scale packaging of the canonical Appendix transport. -/
noncomputable def liftFixedScaleWitness_appendixHornerBase
    {d s D k loss scaleNum scaleDen : ℕ}
    {A : Finset (LatticePoint d)}
    (W : FixedScaleWitness
      (A.image (hornerLatticeHom d (appendixHornerBase D s A)))
        s D k loss scaleNum scaleDen) :
    FixedScaleWitness A s D k loss scaleNum scaleDen := by
  refine ⟨liftEnhancedCFPWitness_appendixHornerBase W.enhanced, ?_⟩
  change W.enhanced.scaleNum = scaleNum ∧
    W.enhanced.scaleDen = scaleDen
  exact W.2

/-- Pull target coverage back through a lifted GAP.  The only injectivity
needed is on one common window containing both the lifted translated dilate
and all source subset sums.  This is the source-shaped no-carry transport
used after the quantitative window estimates in the Appendix argument. -/
theorem liftGAP_covered_of_target_covered {d e r k : ℕ}
    (f : LatticePoint d →+ LatticePoint e) (P : GAP e r)
    (offsetLift translateLift : LatticePoint d)
    (stepLift : Fin r → LatticePoint d)
    (hoffset : f offsetLift = P.offset)
    (hsteps : ∀ i, f (stepLift i) = P.steps i)
    (translateTarget : LatticePoint e)
    (htranslate : f translateLift = translateTarget)
    (R : Finset (LatticePoint d)) (hinjectiveR : Set.InjOn f R)
    (window : Set (LatticePoint d))
    (hstructured :
      (translate translateLift
        ((liftGAP P offsetLift stepLift).dilate k).carrier :
          Set (LatticePoint d)) ⊆ window)
    (hsubsetSums : (GAP.subsetSums R : Set (LatticePoint d)) ⊆ window)
    (hinjectiveWindow : Set.InjOn f window)
    (hcovered :
      translate translateTarget (P.dilate k).carrier ⊆
        GAP.subsetSums (R.image f)) :
    translate translateLift
        ((liftGAP P offsetLift stepLift).dilate k).carrier ⊆
      GAP.subsetSums R := by
  intro x hx
  obtain ⟨q, hq, rfl⟩ := mem_translate_iff.mp hx
  have hqTarget : f q ∈ (P.dilate k).carrier := by
    have hqMapped : f q ∈
        (mapGAP f ((liftGAP P offsetLift stepLift).dilate k)).carrier := by
      rw [mapGAP_carrier]
      exact Finset.mem_image.mpr ⟨q, hq, rfl⟩
    rw [mapGAP_dilate,
      mapGAP_liftGAP f P offsetLift stepLift hoffset hsteps] at hqMapped
    exact hqMapped
  have htarget : f (translateLift + q) ∈
      translate translateTarget (P.dilate k).carrier := by
    apply mem_translate_iff.mpr
    exact ⟨f q, hqTarget, by simp only [map_add, htranslate]⟩
  obtain ⟨y, hySums, hyMap⟩ :=
    exists_subsetSum_preimage f R hinjectiveR (hcovered htarget)
  have hsourceWindow : translateLift + q ∈ window :=
    hstructured (mem_translate_iff.mpr ⟨q, hq, rfl⟩)
  have hyWindow : y ∈ window := hsubsetSums hySums
  have hxy : translateLift + q = y :=
    hinjectiveWindow hsourceWindow hyWindow (by
      rw [hyMap])
  rwa [hxy]

/-- Delete the first direction of a positive-rank GAP. -/
def dropFirst {d r : ℕ} (P : GAP d (r + 1)) : GAP d r where
  offset := P.offset
  steps := fun i => P.steps i.succ
  widths := fun i => P.widths i.succ
  width_pos := fun i => P.width_pos i.succ

/-- Restrict a coordinate tuple to all directions after the first. -/
def tailCoord {d r : ℕ} (P : GAP d (r + 1)) (n : P.Coord) :
    (dropFirst P).Coord := fun i : Fin r => n i.succ

/-- Extend a coordinate tuple by putting zero in the deleted direction. -/
def zeroHeadCoord {d r : ℕ} (P : GAP d (r + 1)) (n : (dropFirst P).Coord) :
    P.Coord := Fin.cases ⟨0, P.width_pos 0⟩ (fun i => n i)

@[simp] theorem zeroHeadCoord_zero {d r : ℕ} (P : GAP d (r + 1))
    (n : (dropFirst P).Coord) : (zeroHeadCoord P n 0 : ℕ) = 0 := rfl

@[simp] theorem zeroHeadCoord_succ {d r : ℕ} (P : GAP d (r + 1))
    (n : (dropFirst P).Coord) (i : Fin r) :
    zeroHeadCoord P n i.succ = n i := rfl

/-- Deleting a zero first direction does not change any displayed point. -/
theorem dropFirst_coordPoint_tail_of_step_zero {d r : ℕ}
    (P : GAP d (r + 1)) (hzero : P.steps 0 = 0) (n : P.Coord) :
    (dropFirst P).coordPoint (tailCoord P n) = P.coordPoint n := by
  ext j
  rw [GAP.coordPoint, GAP.coordPoint, Fin.sum_univ_succ]
  simp [dropFirst, tailCoord, hzero]

/-- Conversely, every displayed point after deletion is displayed by the
original presentation with coefficient zero in the deleted direction. -/
theorem coordPoint_zeroHead_eq_dropFirst {d r : ℕ}
    (P : GAP d (r + 1)) (hzero : P.steps 0 = 0)
    (n : (dropFirst P).Coord) :
    P.coordPoint (zeroHeadCoord P n) = (dropFirst P).coordPoint n := by
  ext j
  rw [GAP.coordPoint, GAP.coordPoint, Fin.sum_univ_succ]
  simp [dropFirst, zeroHeadCoord_succ, hzero]

/-- Elementary kernel elimination: a zero first direction can be removed
without changing the carrier. -/
theorem carrier_dropFirst_of_step_zero {d r : ℕ}
    (P : GAP d (r + 1)) (hzero : P.steps 0 = 0) :
    (dropFirst P).carrier = P.carrier := by
  ext x
  simp only [GAP.mem_carrier_iff]
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨zeroHeadCoord P n, coordPoint_zeroHead_eq_dropFirst P hzero n⟩
  · rintro ⟨n, rfl⟩
    exact ⟨tailCoord P n, dropFirst_coordPoint_tail_of_step_zero P hzero n⟩

/-- Projecting a GAP and removing a direction in the projection kernel
preserves its carrier. -/
theorem carrier_dropFirst_mapGAP_of_mem_ker {d e r : ℕ}
    (f : LatticePoint d →+ LatticePoint e) (P : GAP d (r + 1))
    (hzero : f (P.steps 0) = 0) :
    (dropFirst (mapGAP f P)).carrier = (mapGAP f P).carrier := by
  exact carrier_dropFirst_of_step_zero (mapGAP f P) hzero

/-- Carrier equality also preserves every translated coverage statement. -/
theorem translate_dropFirst_mapGAP_of_mem_ker {d e r : ℕ}
    (f : LatticePoint d →+ LatticePoint e) (P : GAP d (r + 1))
    (hzero : f (P.steps 0) = 0) (t : LatticePoint e) :
    translate t (dropFirst (mapGAP f P)).carrier =
      translate t (mapGAP f P).carrier := by
  rw [carrier_dropFirst_mapGAP_of_mem_ker f P hzero]

/-- Exact injectivity condition on the coefficient box which survives a
one-step kernel elimination. -/
def ProperAwayFirst {d r : ℕ} (P : GAP d (r + 1)) : Prop :=
  Function.Injective fun n : (dropFirst P).Coord =>
    P.coordPoint (zeroHeadCoord P n)

/-- The reduced presentation is proper exactly when the surviving
coefficient box is injective. -/
theorem dropFirst_proper_iff_properAwayFirst {d r : ℕ}
    (P : GAP d (r + 1)) (hzero : P.steps 0 = 0) :
    (dropFirst P).Proper ↔ ProperAwayFirst P := by
  constructor
  · intro h n m hnm
    apply h
    rw [← coordPoint_zeroHead_eq_dropFirst P hzero n,
      ← coordPoint_zeroHead_eq_dropFirst P hzero m]
    exact hnm
  · intro h n m hnm
    apply h
    change P.coordPoint (zeroHeadCoord P n) = P.coordPoint (zeroHeadCoord P m)
    rw [coordPoint_zeroHead_eq_dropFirst P hzero n,
      coordPoint_zeroHead_eq_dropFirst P hzero m]
    exact hnm

/-- A forward projected presentation, useful once a source GAP has already
been constructed.  This proposition is intentionally not claimed for an
arbitrary homomorphism: projection can introduce collisions.  The
source-facing pullback used by the higher-dimensional CFP argument instead
starts from `liftGAP` and proves that its chosen presentation data map to the
target GAP. -/
def HasProperProjectedPresentation {d e r : ℕ}
    (f : LatticePoint d →+ LatticePoint e) (P : GAP d r) (k : ℕ) : Prop :=
  ∃ r' : ℕ, ∃ Q : GAP e r',
    r' ≤ r ∧ Q.Proper ∧ (Q.dilate k).Proper ∧
      Q.carrier = (mapGAP f P).carrier ∧
      (Q.dilate k).carrier = (mapGAP f (P.dilate k)).carrier

/-- Injectivity of the ambient homomorphism on the displayed carrier
preserves properness. -/
theorem mapGAP_proper_of_injOn_carrier {d e r : ℕ}
    (f : LatticePoint d →+ LatticePoint e) (P : GAP d r)
    (hproper : P.Proper) (hinjective : Set.InjOn f P.carrier) :
    (mapGAP f P).Proper := by
  intro a b hab
  apply hproper
  apply hinjective (P.coordPoint_mem_carrier a) (P.coordPoint_mem_carrier b)
  simpa only [mapGAP_coordPoint] using hab

/-- Injectivity on one translate of a carrier is equivalent to the
injectivity needed on the untranslated carrier. -/
theorem injOn_carrier_of_injOn_translate {d e r : ℕ}
    (f : LatticePoint d →+ LatticePoint e) (P : GAP d r)
    (t : LatticePoint d)
    (hinjective : Set.InjOn f (translate t P.carrier : Set (LatticePoint d))) :
    Set.InjOn f (P.carrier : Set (LatticePoint d)) := by
  intro x hx y hy hxy
  have htx : t + x ∈ translate t P.carrier :=
    mem_translate_iff.mpr ⟨x, hx, rfl⟩
  have hty : t + y ∈ translate t P.carrier :=
    mem_translate_iff.mpr ⟨y, hy, rfl⟩
  have htranslated : t + x = t + y := hinjective htx hty (by
    simpa only [map_add, hxy])
  exact add_left_cancel htranslated

/-- The requested projected presentation is simply the mapped GAP whenever
the homomorphism is injective on the proper dilated carrier. -/
theorem hasProperProjectedPresentation_of_injOn_dilate {d e r k : ℕ}
    (f : LatticePoint d →+ LatticePoint e) (P : GAP d r)
    (hk : 0 < k) (hproper : (P.dilate k).Proper)
    (hinjective : Set.InjOn f (P.dilate k).carrier) :
    HasProperProjectedPresentation f P k := by
  let Q := mapGAP f P
  have hproperDilate : (Q.dilate k).Proper := by
    rw [← mapGAP_dilate]
    exact mapGAP_proper_of_injOn_carrier f (P.dilate k)
      hproper hinjective
  have hproperBase : Q.Proper :=
    GAP.SProper.proper
      (show Q.SProper k from Q.sProper_of_dilate_proper k hproperDilate) hk
  refine ⟨r, Q, Nat.le_refl r, hproperBase, hproperDilate, rfl, ?_⟩
  exact congrArg GAP.carrier (mapGAP_dilate f P k).symm

/-- Coverage by a set on which the homomorphism is injective supplies the
projected presentation without any separate kernel-elimination assumption. -/
theorem hasProperProjectedPresentation_of_covered {d e r k : ℕ}
    (f : LatticePoint d →+ LatticePoint e) (P : GAP d r)
    (t : LatticePoint d) (S : Set (LatticePoint d))
    (hk : 0 < k) (hproper : (P.dilate k).Proper)
    (hcovered : (translate t (P.dilate k).carrier : Set (LatticePoint d)) ⊆ S)
    (hinjective : Set.InjOn f S) :
    HasProperProjectedPresentation f P k := by
  apply hasProperProjectedPresentation_of_injOn_dilate f P hk hproper
  apply injOn_carrier_of_injOn_translate f (P.dilate k) t
  exact hinjective.mono hcovered

/-- The canonical no-carry map gives the proper projected presentation for
every positive-scale CFP witness.  Its covered translate lies in subset sums
of a reserve of size at most `s`, precisely the domain on which no-carry is
injective. -/
theorem CFPWitness.hasProperProjectedPresentation_noCarry
    {d s D k loss : ℕ} {A : Finset (LatticePoint d)}
    (W : CFPWitness A s D k loss) (hk : 0 < k) :
    HasProperProjectedPresentation
      (noCarryLatticeHom A s) W.progression k := by
  apply hasProperProjectedPresentation_of_covered
    (noCarryLatticeHom A s) W.progression W.translatePoint
      (boundedSubsetSums A s : Set (LatticePoint d))
      hk W.dilate_proper
  · exact W.covered.trans
      (subsetSums_subset_boundedSubsetSums W.reserved_subset W.reserved_small)
  · exact noCarryLatticeHom_injOn_boundedSubsetSums A

/-- Enhanced witnesses supply the required positive projection scale
internally. -/
theorem EnhancedCFPWitness.hasProperProjectedPresentation_noCarry
    {d s D k loss : ℕ} {A : Finset (LatticePoint d)}
    (W : EnhancedCFPWitness A s D k loss) :
    HasProperProjectedPresentation
      (noCarryLatticeHom A s) W.progression k :=
  CFPWitness.hasProperProjectedPresentation_noCarry W.basic W.k_pos

end Erdos186.CFP.NoCarryEmbedding
