/-
Copyright (c) 2026 The Flypitch Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Complete ordered fields inside Mathlib's `ZFSet` are (order-)isomorphic to `ℝ`, and the direction
"DeepMind's proposition ⇒ `Erdos501_f` holds in the standard structure" of the bridge.
-/
import Mathlib.Algebra.Order.CompleteField
import ErdosProblems.Erdos501.Flypitch4.Erdos501.StdSemantics

set_option relaxedAutoImplicit true

/-!
# Complete ordered fields in `ZFSet`, and `erdos501_deepmind → StdSem.erdos501`

Let `(R, plus, times, ltR, zero, one)` be a complete ordered field in the sense of
`StdSem.completeOrderedField` (a bundle `COF`).  Its carrier `Carrier F = {x : ZFSet // x ∈ R}`
carries the operations read off from the sets `plus`, `times`, `ltR`; we verify Mathlib's axioms
`Field`, `LinearOrder`, `IsStrictOrderedRing`, `ConditionallyCompleteLinearOrder` from the
internal axioms, so that Mathlib's uniqueness theorem for conditionally complete linear ordered
fields (`LinearOrderedField.inducedOrderRingIso`) gives an ordered ring isomorphism
`ℝ ≃+*o Carrier F` (`realIso F`).

Along this isomorphism, a family `A : R → 𝒫(R)` satisfying the internal hypotheses of the Erdős
property becomes a family `ℝ → Set ℝ` of bounded sets of Lebesgue outer measure `< 1`
(`isBounded_pull`, `volume_pull_lt_one`), and an infinite independent `X ⊆ ℝ` pushes forward to an
internal one (`erdos501_std_of_deepmind`).
-/

open Fol Set MeasureTheory
open scoped ENNReal

namespace Flypitch.Erdos501

namespace ZFSetCOF

open StdSem

/-- A complete ordered field inside `ZFSet`, in the sense of the sentence
`CompleteOrderedFieldF` read in the standard structure. -/
structure COF where
  R : ZFSet.{0}
  plus : ZFSet.{0}
  times : ZFSet.{0}
  ltR : ZFSet.{0}
  zero : ZFSet.{0}
  one : ZFSet.{0}
  h : completeOrderedField R plus times ltR zero one

namespace COF

variable (F : COF)

theorem isOp2_plus : isOp2 F.R F.plus := F.h.1
theorem isOp2_times : isOp2 F.R F.times := F.h.2.1
theorem zero_mem : F.zero ∈ F.R := F.h.2.2.1
theorem one_mem : F.one ∈ F.R := F.h.2.2.2.1
theorem assoc_plus : assoc F.R F.plus := F.h.2.2.2.2.1
theorem comm_plus : comm F.R F.plus := F.h.2.2.2.2.2.1
theorem ident_plus : ident F.R F.plus F.zero := F.h.2.2.2.2.2.2.1
theorem addInv' : addInv F.R F.plus F.zero := F.h.2.2.2.2.2.2.2.1
theorem assoc_times : assoc F.R F.times := F.h.2.2.2.2.2.2.2.2.1
theorem comm_times : comm F.R F.times := F.h.2.2.2.2.2.2.2.2.2.1
theorem ident_times : ident F.R F.times F.one := F.h.2.2.2.2.2.2.2.2.2.2.1
theorem mulInv' : mulInv F.R F.times F.zero F.one := F.h.2.2.2.2.2.2.2.2.2.2.2.1
theorem zero_ne_one' : ¬ F.zero = F.one := F.h.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem distrib' : distrib F.R F.plus F.times := F.h.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem irrefl' : irrefl F.R F.ltR := F.h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem trans' : trans F.R F.ltR := F.h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem total' : total F.R F.ltR := F.h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem addCompat' : addCompat F.R F.plus F.ltR := F.h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem mulPos' : mulPos F.R F.times F.ltR F.zero := F.h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem complete' : complete F.R F.ltR := F.h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-! ### The carrier and its operations -/

/-- The carrier of the internal field, as a Lean type. -/
def Carrier : Type 1 := {x : ZFSet.{0} // x ∈ F.R}

variable {F}

theorem Carrier.ext {x y : Carrier F} (h : x.1 = y.1) : x = y := Subtype.ext h

/-- The element of `Carrier F` with value `z ∈ R`. -/
def Carrier.mk (z : ZFSet.{0}) (hz : z ∈ F.R) : Carrier F := ⟨z, hz⟩

noncomputable instance : Add (Carrier F) :=
  ⟨fun x y => ⟨opval F.plus x.1 y.1, opval_mem F.isOp2_plus x.2 y.2⟩⟩

noncomputable instance : Mul (Carrier F) :=
  ⟨fun x y => ⟨opval F.times x.1 y.1, opval_mem F.isOp2_times x.2 y.2⟩⟩

instance : LT (Carrier F) := ⟨fun x y => lt F.ltR x.1 y.1⟩

instance : LE (Carrier F) := ⟨fun x y => x < y ∨ x = y⟩

instance : Zero (Carrier F) := ⟨⟨F.zero, F.zero_mem⟩⟩

instance : One (Carrier F) := ⟨⟨F.one, F.one_mem⟩⟩

/-- The additive inverse (chosen from the axiom `addInv`). -/
noncomputable def neg' (x : Carrier F) : Carrier F :=
  ⟨Classical.choose (F.addInv' x.1 x.2), (Classical.choose_spec (F.addInv' x.1 x.2)).1⟩

noncomputable instance : Neg (Carrier F) := ⟨neg'⟩

theorem val_neg (x : Carrier F) : (-x).1 = Classical.choose (F.addInv' x.1 x.2) := rfl

open scoped Classical in
/-- The multiplicative inverse (chosen from the axiom `mulInv`; `0⁻¹ = 0`). -/
noncomputable def inv' (x : Carrier F) : Carrier F :=
  if h : x.1 = F.zero then 0
  else ⟨Classical.choose (F.mulInv' x.1 x.2 h), (Classical.choose_spec (F.mulInv' x.1 x.2 h)).1⟩

noncomputable instance : Inv (Carrier F) := ⟨inv'⟩

theorem val_add (x y : Carrier F) : (x + y).1 = opval F.plus x.1 y.1 := rfl
theorem val_mul (x y : Carrier F) : (x * y).1 = opval F.times x.1 y.1 := rfl
theorem val_zero : (0 : Carrier F).1 = F.zero := rfl
theorem val_one : (1 : Carrier F).1 = F.one := rfl
theorem lt_def (x y : Carrier F) : x < y ↔ lt F.ltR x.1 y.1 := Iff.rfl
theorem le_def (x y : Carrier F) : x ≤ y ↔ x < y ∨ x = y := Iff.rfl

theorem app2_plus_add (x y : Carrier F) : app2 F.plus x.1 y.1 (x + y).1 :=
  app2_opval F.isOp2_plus x.2 y.2

theorem app2_times_mul (x y : Carrier F) : app2 F.times x.1 y.1 (x * y).1 :=
  app2_opval F.isOp2_times x.2 y.2

theorem eq_add_of_app2 (x y : Carrier F) {z : ZFSet.{0}} (h : app2 F.plus x.1 y.1 z) :
    z = (x + y).1 :=
  eq_opval_of_app2 F.isOp2_plus x.2 y.2 h

theorem eq_mul_of_app2 (x y : Carrier F) {z : ZFSet.{0}} (h : app2 F.times x.1 y.1 z) :
    z = (x * y).1 :=
  eq_opval_of_app2 F.isOp2_times x.2 y.2 h

theorem add_neg_cancel' (x : Carrier F) : x + -x = 0 := by
  apply Carrier.ext
  rw [val_zero]
  have h : app2 F.plus x.1 (-x).1 F.zero := (Classical.choose_spec (F.addInv' x.1 x.2)).2
  exact (eq_add_of_app2 x (-x) h).symm

theorem val_inv_of_ne (x : Carrier F) (h : x.1 ≠ F.zero) :
    (x⁻¹).1 = Classical.choose (F.mulInv' x.1 x.2 h) := by
  -- (`rw [inv', dif_neg h]` fails in Lean ≥ 4.34: the goal mixes `Carrier F` and `↥F.R`
  -- at reducible transparency; unfold by `show` instead)
  have e : inv' x = ⟨Classical.choose (F.mulInv' x.1 x.2 h),
      (Classical.choose_spec (F.mulInv' x.1 x.2 h)).1⟩ := dif_neg h
  show (inv' x).1 = _
  rw [e]

theorem mul_inv_cancel' (x : Carrier F) (hx : x ≠ 0) : x * x⁻¹ = 1 := by
  have h : x.1 ≠ F.zero := fun h => hx (Carrier.ext h)
  apply Carrier.ext
  rw [val_one]
  have h2 : app2 F.times x.1 (x⁻¹).1 F.one := by
    rw [val_inv_of_ne x h]
    exact (Classical.choose_spec (F.mulInv' x.1 x.2 h)).2
  exact (eq_mul_of_app2 x x⁻¹ h2).symm

theorem inv_zero' : (0 : Carrier F)⁻¹ = 0 := by
  show inv' 0 = 0
  rw [inv']
  exact dif_pos rfl

/-! ### The additive group -/

theorem add_assoc' (x y z : Carrier F) : x + y + z = x + (y + z) :=
  Carrier.ext (F.assoc_plus x.1 x.2 y.1 y.2 z.1 z.2 _ _ _ _
    (app2_plus_add x y) (app2_plus_add (x + y) z) (app2_plus_add y z) (app2_plus_add x (y + z)))

theorem add_comm' (x y : Carrier F) : x + y = y + x :=
  Carrier.ext (eq_add_of_app2 y x (F.comm_plus x.1 x.2 y.1 y.2 _ (app2_plus_add x y)))

theorem add_zero' (x : Carrier F) : x + 0 = x :=
  Carrier.ext (eq_add_of_app2 x 0 (F.ident_plus x.1 x.2)).symm

theorem zero_add' (x : Carrier F) : 0 + x = x := by
  rw [add_comm', add_zero']

noncomputable instance instAddCommGroupCarrier : AddCommGroup (Carrier F) where
  add := (· + ·)
  add_assoc := add_assoc'
  zero := 0
  zero_add := zero_add'
  add_zero := add_zero'
  nsmul := nsmulRec
  neg := (- ·)
  zsmul := zsmulRec
  neg_add_cancel x := by rw [add_comm']; exact add_neg_cancel' x
  add_comm := add_comm'

/-! ### The commutative ring -/

theorem mul_assoc' (x y z : Carrier F) : x * y * z = x * (y * z) :=
  Carrier.ext (F.assoc_times x.1 x.2 y.1 y.2 z.1 z.2 _ _ _ _
    (app2_times_mul x y) (app2_times_mul (x * y) z) (app2_times_mul y z)
    (app2_times_mul x (y * z)))

theorem mul_comm' (x y : Carrier F) : x * y = y * x :=
  Carrier.ext (eq_mul_of_app2 y x (F.comm_times x.1 x.2 y.1 y.2 _ (app2_times_mul x y)))

theorem mul_one' (x : Carrier F) : x * 1 = x :=
  Carrier.ext (eq_mul_of_app2 x 1 (F.ident_times x.1 x.2)).symm

theorem left_distrib' (x y z : Carrier F) : x * (y + z) = x * y + x * z :=
  Carrier.ext (F.distrib' x.1 x.2 y.1 y.2 z.1 z.2 _ _ _ _ _
    (app2_plus_add y z) (app2_times_mul x (y + z)) (app2_times_mul x y) (app2_times_mul x z)
    (app2_plus_add (x * y) (x * z)))

theorem mul_zero' (x : Carrier F) : x * 0 = 0 := by
  have h := left_distrib' x 0 0
  rw [add_zero] at h
  exact left_eq_add.1 h

noncomputable instance instCommRingCarrier : CommRing (Carrier F) :=
  { (inferInstance : AddCommGroup (Carrier F)) with
    mul := (· * ·)
    left_distrib := left_distrib'
    right_distrib := fun x y z => by
      rw [mul_comm' (x + y) z, left_distrib', mul_comm' z x, mul_comm' z y]
    zero_mul := fun x => by rw [mul_comm']; exact mul_zero' x
    mul_zero := mul_zero'
    mul_assoc := mul_assoc'
    one := 1
    one_mul := fun x => by rw [mul_comm']; exact mul_one' x
    mul_one := mul_one'
    npow := npowRec
    mul_comm := mul_comm' }

theorem zero_ne_one'' : (0 : Carrier F) ≠ 1 := fun h => F.zero_ne_one' (congrArg Subtype.val h)

/-! ### The field -/

noncomputable instance instFieldCarrier : Field (Carrier F) :=
  { (inferInstance : CommRing (Carrier F)) with
    inv := (·⁻¹)
    exists_pair_ne := ⟨0, 1, zero_ne_one''⟩
    mul_inv_cancel := mul_inv_cancel'
    inv_zero := inv_zero'
    nnqsmul := _
    nnqsmul_def := fun _ _ => rfl
    qsmul := _
    qsmul_def := fun _ _ => rfl }

/-! ### The linear order -/

theorem lt_irrefl' (x : Carrier F) : ¬ x < x := F.irrefl' x.1 x.2

theorem lt_trans' {x y z : Carrier F} (hxy : x < y) (hyz : y < z) : x < z :=
  F.trans' x.1 x.2 y.1 y.2 z.1 z.2 hxy hyz

theorem lt_asymm' {x y : Carrier F} (hxy : x < y) : ¬ y < x :=
  fun hyx => lt_irrefl' x (lt_trans' hxy hyx)

theorem lt_total' (x y : Carrier F) : x < y ∨ x = y ∨ y < x := by
  rcases F.total' x.1 x.2 y.1 y.2 with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl (Carrier.ext h))
  · exact Or.inr (Or.inr h)

noncomputable instance instLinearOrderCarrier : LinearOrder (Carrier F) where
  le := (· ≤ ·)
  lt := (· < ·)
  le_refl x := Or.inr rfl
  le_trans x y z hxy hyz := by
    rcases hxy with hxy | rfl
    · rcases hyz with hyz | rfl
      · exact Or.inl (lt_trans' hxy hyz)
      · exact Or.inl hxy
    · exact hyz
  le_antisymm x y hxy hyx := by
    rcases hxy with hxy | rfl
    · rcases hyx with hyx | rfl
      · exact absurd hyx (lt_asymm' hxy)
      · rfl
    · rfl
  le_total x y := by
    rcases lt_total' x y with h | rfl | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr rfl)
    · exact Or.inr (Or.inl h)
  lt_iff_le_not_ge x y := by
    constructor
    · intro h
      refine ⟨Or.inl h, ?_⟩
      rintro (h' | rfl)
      · exact lt_asymm' h h'
      · exact lt_irrefl' _ h
    · rintro ⟨h | rfl, h'⟩
      · exact h
      · exact absurd (Or.inr rfl) h'
  toDecidableLE := Classical.decRel _

/-! ### The ordered ring -/

theorem add_lt_add_right' {x y : Carrier F} (h : x < y) (z : Carrier F) : x + z < y + z :=
  F.addCompat' x.1 x.2 y.1 y.2 z.1 z.2 _ _ h (app2_plus_add x z) (app2_plus_add y z)

theorem mul_pos' {x y : Carrier F} (hx : 0 < x) (hy : 0 < y) : 0 < x * y :=
  F.mulPos' x.1 x.2 y.1 y.2 _ hx hy (app2_times_mul x y)

instance : IsOrderedAddMonoid (Carrier F) where
  add_le_add_left a b hab c := by
    rcases hab with hab | rfl
    · exact Or.inl (add_lt_add_right' hab c)
    · exact le_rfl

theorem zero_lt_one' : (0 : Carrier F) < 1 := by
  rcases lt_total' (0 : Carrier F) 1 with h | h | h
  · exact h
  · exact absurd h zero_ne_one''
  · -- `1 < 0`: then `0 = 1 + (-1) < 0 + (-1) = -1`, so `0 < (-1) * (-1) = 1`, contradiction.
    exfalso
    have h1 : (0 : Carrier F) < -1 := by
      have := add_lt_add_right' h (-1)
      rwa [add_neg_cancel, zero_add] at this
    have h2 := mul_pos' h1 h1
    rw [neg_one_mul, neg_neg] at h2
    exact lt_asymm' h h2

instance : ZeroLEOneClass (Carrier F) := ⟨zero_lt_one'.le⟩

instance instIsStrictOrderedRingCarrier : IsStrictOrderedRing (Carrier F) :=
  IsStrictOrderedRing.of_mul_pos fun _ _ ha hb => mul_pos' ha hb

/-! ### Conditional completeness -/

theorem exists_isLUB (s : Set (Carrier F)) (hb : BddAbove s) (hn : s.Nonempty) :
    ∃ u : Carrier F, IsLUB s u := by
  -- the internal set of the values of `s`
  let S : ZFSet.{0} := ZFSet.sep (fun z => ∃ x : Carrier F, x ∈ s ∧ x.1 = z) F.R
  have hS : ∀ z : ZFSet.{0}, z ∈ S ↔ ∃ x : Carrier F, x ∈ s ∧ x.1 = z := by
    intro z
    simp only [S, ZFSet.mem_sep]
    constructor
    · rintro ⟨-, h⟩
      exact h
    · rintro ⟨x, hx, h⟩
      exact ⟨h ▸ x.2, x, hx, h⟩
  have hSP : S ∈ ZFSet.powerset F.R := by
    rw [ZFSet.mem_powerset]
    intro z hz
    obtain ⟨x, -, rfl⟩ := (hS z).1 hz
    exact x.2
  have hSne : ¬ S = ∅ := by
    intro h
    obtain ⟨x, hx⟩ := hn
    have : x.1 ∈ S := (hS x.1).2 ⟨x, hx, rfl⟩
    rw [h] at this
    exact ZFSet.notMem_empty _ this
  have hSbdd : ∃ b : ZFSet.{0}, b ∈ F.R ∧ ∀ z : ZFSet.{0}, z ∈ S → le F.ltR z b := by
    obtain ⟨b, hb⟩ := hb
    refine ⟨b.1, b.2, fun z hz => ?_⟩
    obtain ⟨x, hx, rfl⟩ := (hS z).1 hz
    rcases hb hx with h | h
    · exact Or.inl h
    · exact Or.inr (congrArg Subtype.val h)
  obtain ⟨u, hu, hu1, hu2⟩ := F.complete' S hSP hSne hSbdd
  refine ⟨⟨u, hu⟩, ?_, ?_⟩
  · intro x hx
    rcases hu1 x.1 ((hS x.1).2 ⟨x, hx, rfl⟩) with h | h
    · exact Or.inl h
    · exact Or.inr (Subtype.ext h)
  · intro v hv
    have : ∀ z : ZFSet.{0}, z ∈ S → le F.ltR z v.1 := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := (hS z).1 hz
      rcases hv hx with h | h
      · exact Or.inl h
      · exact Or.inr (congrArg Subtype.val h)
    rcases hu2 v.1 v.2 this with h | h
    · exact Or.inl h
    · exact Or.inr (Subtype.ext h)

open scoped Classical

noncomputable instance : SupSet (Carrier F) :=
  ⟨fun s => if h : BddAbove s ∧ s.Nonempty then Classical.choose (exists_isLUB s h.1 h.2) else 0⟩

theorem isLUB_sSup' (s : Set (Carrier F)) (hb : BddAbove s) (hn : s.Nonempty) :
    IsLUB s (sSup s) := by
  have : sSup s = Classical.choose (exists_isLUB s hb hn) := by
    show (if h : BddAbove s ∧ s.Nonempty then Classical.choose (exists_isLUB s h.1 h.2) else 0) = _
    rw [dif_pos ⟨hb, hn⟩]
  rw [this]
  exact Classical.choose_spec (exists_isLUB s hb hn)

theorem sSup_of_not (s : Set (Carrier F)) (h : ¬ (BddAbove s ∧ s.Nonempty)) : sSup s = 0 := by
  show (if h : BddAbove s ∧ s.Nonempty then Classical.choose (exists_isLUB s h.1 h.2) else 0) = _
  rw [dif_neg h]

theorem not_bddAbove_univ : ¬ BddAbove (Set.univ : Set (Carrier F)) := by
  rintro ⟨b, hb⟩
  have := hb (Set.mem_univ (b + 1))
  exact absurd (lt_add_one b) (not_lt.2 this)

noncomputable instance instConditionallyCompleteLinearOrderCarrier :
    ConditionallyCompleteLinearOrder (Carrier F) :=
  { conditionallyCompleteLatticeOfLatticeOfsSup (Carrier F) isLUB_sSup',
    (inferInstance : LinearOrder (Carrier F)) with
    csSup_of_not_bddAbove := fun s hs => by
      rw [sSup_of_not s (fun h => hs h.1), sSup_of_not ∅ (fun h => h.2.ne_empty rfl)]
    csInf_of_not_bddBelow := fun s hs => by
      show sSup (lowerBounds s) = sSup (lowerBounds ∅)
      have h1 : lowerBounds s = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        intro b hb
        exact hs ⟨b, hb⟩
      rw [h1, lowerBounds_empty, sSup_of_not ∅ (fun h => h.2.ne_empty rfl),
        sSup_of_not Set.univ (fun h => not_bddAbove_univ h.1)] }

/-! ### The isomorphism with `ℝ` -/

/-- **Every complete ordered field inside `ZFSet` is order-isomorphic to `ℝ`**: the ordered ring
isomorphism `ℝ ≃+*o Carrier F` given by Mathlib's uniqueness theorem for conditionally complete
linear ordered fields. -/
noncomputable def realIso : ℝ ≃+*o Carrier F :=
  ConditionallyCompleteLinearOrderedField.inducedOrderRingIso ℝ (Carrier F)


/-! ### Reading elements of `Carrier F` as reals -/

/-- The real number corresponding to `x : Carrier F`. -/
noncomputable def toR (x : Carrier F) : ℝ := (realIso (F := F)).symm x

/-- The element of `Carrier F` corresponding to a real number. -/
noncomputable def ofR (r : ℝ) : Carrier F := realIso (F := F) r

theorem toR_ofR (r : ℝ) : toR (ofR (F := F) r) = r := (realIso (F := F)).symm_apply_apply r
theorem ofR_toR (x : Carrier F) : ofR (toR x) = x := (realIso (F := F)).apply_symm_apply x

theorem toR_lt_toR {x y : Carrier F} : toR x < toR y ↔ x < y :=
  map_lt_map_iff (realIso (F := F)).symm

theorem toR_le_toR {x y : Carrier F} : toR x ≤ toR y ↔ x ≤ y :=
  map_le_map_iff (realIso (F := F)).symm

theorem toR_add (x y : Carrier F) : toR (x + y) = toR x + toR y :=
  map_add (realIso (F := F)).symm x y

theorem toR_zero : toR (0 : Carrier F) = 0 := map_zero (realIso (F := F)).symm
theorem toR_one : toR (1 : Carrier F) = 1 := map_one (realIso (F := F)).symm

theorem ofR_injective : Function.Injective (ofR (F := F)) :=
  fun r r' h => by rw [← toR_ofR (F := F) r, h, toR_ofR]

/-! ### Transport of the Erdős property -/

section Transport

variable (A : ZFSet.{0})

/-- The pull-back to `ℝ` of a family `A : R → 𝒫(R)` given as a set of pairs. -/
def pull (r : ℝ) : Set ℝ := {y : ℝ | (ofR (F := F) y).1 ∈ fval A (ofR (F := F) r).1}

variable {A}

theorem isBounded_pull {r : ℝ} (hb : bounded F.R F.ltR (fval A (ofR (F := F) r).1)) :
    Bornology.IsBounded (pull (F := F) A r) := by
  obtain ⟨m₁, hm₁, m₂, hm₂, hy⟩ := hb
  refine (Metric.isBounded_Icc (toR (Carrier.mk (F := F) m₁ hm₁))
    (toR (Carrier.mk (F := F) m₂ hm₂))).subset fun y hy' => ?_
  obtain ⟨h1, h2⟩ := hy _ hy'
  have h1' : Carrier.mk (F := F) m₁ hm₁ < ofR y := h1
  have h2' : ofR (F := F) y < Carrier.mk (F := F) m₂ hm₂ := h2
  rw [← toR_lt_toR, toR_ofR] at h1' h2'
  exact ⟨h1'.le, h2'.le⟩

theorem volume_pull_lt_one {r : ℝ}
    (hm : outerMeasureLtOne F.R F.plus F.ltR F.zero F.one (fval A (ofR (F := F) r).1)) :
    volume (pull (F := F) A r) < 1 := by
  obtain ⟨a, b, s, ha, hb, hs, hnd, hcov, hs0, hps, rr, hrr, hr1, hbd⟩ := hm
  -- the three sequences, read as reals
  let av : ℕ → Carrier F := fun n => Carrier.mk (fval a (natZ n)) (fval_mem ha (natZ_mem_omega n))
  let bv : ℕ → Carrier F := fun n => Carrier.mk (fval b (natZ n)) (fval_mem hb (natZ_mem_omega n))
  let sv : ℕ → Carrier F := fun n => Carrier.mk (fval s (natZ n)) (fval_mem hs (natZ_mem_omega n))
  let a' : ℕ → ℝ := fun n => toR (av n)
  let b' : ℕ → ℝ := fun n => toR (bv n)
  let s' : ℕ → ℝ := fun n => toR (sv n)
  let rv : Carrier F := Carrier.mk rr hrr
  -- nondegenerate
  have hnd' : ∀ n, a' n < b' n := fun n => by
    have h : lt F.ltR (av n).1 (bv n).1 :=
      hnd (natZ n) (natZ_mem_omega n) _ _ (app_fval ha (natZ_mem_omega n))
        (app_fval hb (natZ_mem_omega n))
    exact toR_lt_toR.2 h
  -- covering
  have hcov' : pull (F := F) A r ⊆ ⋃ n, Ioo (a' n) (b' n) := by
    intro y hy
    obtain ⟨n, hn, u, v, hu, hv, h1, h2⟩ := hcov _ hy
    obtain ⟨k, rfl⟩ := mem_omega_iff.1 hn
    have hu' := eq_fval_of_app ha (natZ_mem_omega k) hu
    have hv' := eq_fval_of_app hb (natZ_mem_omega k) hv
    subst hu' hv'
    have h1' : av k < ofR y := h1
    have h2' : ofR (F := F) y < bv k := h2
    rw [← toR_lt_toR, toR_ofR] at h1' h2'
    exact mem_iUnion.2 ⟨k, h1', h2'⟩
  -- the partial sums
  have hs0' : sv 0 = 0 := by
    apply Carrier.ext
    exact (eq_fval_of_app hs (natZ_mem_omega 0) hs0).symm
  have hstep : ∀ k, sv (k + 1) + av k = sv k + bv k := by
    intro k
    apply Carrier.ext
    exact hps (natZ k) (natZ_mem_omega k) (natZ (k + 1)) (succ_natZ k) _ _ _ _ _ _
      (app_fval ha (natZ_mem_omega k)) (app_fval hb (natZ_mem_omega k))
      (app_fval hs (natZ_mem_omega k)) (app_fval hs (natZ_mem_omega (k + 1)))
      (app2_plus_add (sv (k + 1)) (av k)) (app2_plus_add (sv k) (bv k))
  have hsum : ∀ n, ∑ i ∈ Finset.range n, (b' i - a' i) = s' n := by
    intro n
    induction n with
    | zero => simp [s', hs0', toR_zero]
    | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      have := congrArg toR (hstep k)
      rw [toR_add, toR_add] at this
      simp only [s', a', b']
      linarith
  -- the bound
  have hbd' : ∀ n, s' n ≤ toR rv := fun n => by
    have h : le F.ltR (sv n).1 rv.1 :=
      hbd (natZ n) (natZ_mem_omega n) _ (app_fval hs (natZ_mem_omega n))
    have h' : sv n ≤ rv := by
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (Carrier.ext h)
    exact toR_le_toR.2 h'
  have hr1' : toR rv < 1 := by
    have h : rv < 1 := hr1
    rw [← toR_lt_toR, toR_one] at h
    exact h
  -- the estimate
  calc volume (pull (F := F) A r)
      ≤ volume (⋃ n, Ioo (a' n) (b' n)) := measure_mono hcov'
    _ ≤ ∑' n, volume (Ioo (a' n) (b' n)) := measure_iUnion_le _
    _ = ∑' n, ENNReal.ofReal (b' n - a' n) := by simp only [Real.volume_Ioo]
    _ ≤ ENNReal.ofReal (toR rv) := by
        refine ENNReal.tsum_le_of_sum_range_le fun n => ?_
        rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => sub_nonneg.2 (hnd' i).le]
        exact ENNReal.ofReal_le_ofReal ((hsum n).le.trans (hbd' n))
    _ < 1 := ENNReal.ofReal_lt_one.2 hr1'

/-- The push-forward of a set of reals to a subset of `R`. -/
def push (X' : Set ℝ) : ZFSet.{0} :=
  ZFSet.sep (fun z => ∃ y ∈ X', (ofR (F := F) y).1 = z) F.R

theorem mem_push {X' : Set ℝ} {z : ZFSet.{0}} :
    z ∈ push (F := F) X' ↔ ∃ y ∈ X', (ofR (F := F) y).1 = z := by
  rw [push, ZFSet.mem_sep]
  constructor
  · rintro ⟨-, h⟩
    exact h
  · rintro ⟨y, hy, h⟩
    exact ⟨h ▸ (ofR (F := F) y).2, y, hy, h⟩

theorem push_mem_powerset (X' : Set ℝ) : push (F := F) X' ∈ ZFSet.powerset F.R := by
  rw [ZFSet.mem_powerset]
  intro z hz
  obtain ⟨y, -, rfl⟩ := mem_push.1 hz
  exact (ofR (F := F) y).2

theorem infinite_push {X' : Set ℝ} (h : X'.Infinite) : infinite (push (F := F) X') := by
  let g : ℕ → ℝ := fun n => (Set.Infinite.natEmbedding X' h n).1
  have hg : ∀ n, g n ∈ X' := fun n => (Set.Infinite.natEmbedding X' h n).2
  have hginj : Function.Injective g :=
    Subtype.val_injective.comp (Set.Infinite.natEmbedding X' h).injective
  let f : ZFSet.{0} := ZFSet.range (fun n : ℕ => ZFSet.pair (natZ n) (ofR (F := F) (g n)).1)
  have happ : ∀ (n : ℕ) (u : ZFSet.{0}), app f (natZ n) u ↔ u = (ofR (F := F) (g n)).1 := by
    intro n u
    simp only [f, app, ZFSet.mem_range]
    constructor
    · rintro ⟨k, hk⟩
      rw [ZFSet.pair_inj] at hk
      obtain ⟨hk1, rfl⟩ := hk
      rw [natZ_injective hk1]
    · rintro rfl
      exact ⟨n, rfl⟩
  refine ⟨f, ?_, ?_⟩
  · intro n hn
    obtain ⟨k, rfl⟩ := mem_omega_iff.1 hn
    exact ⟨(ofR (F := F) (g k)).1, mem_push.2 ⟨g k, hg k, rfl⟩, (happ k _).2 rfl,
      fun y' hy' => (happ k y').1 hy'⟩
  · intro n hn m hm u hu hu'
    obtain ⟨k, rfl⟩ := mem_omega_iff.1 hn
    obtain ⟨l, rfl⟩ := mem_omega_iff.1 hm
    rw [happ] at hu hu'
    have h1 : ofR (F := F) (g k) = ofR (g l) := Carrier.ext (hu.symm.trans hu')
    rw [hginj (ofR_injective h1)]

theorem independent_push {A : ZFSet.{0}} (hA1 : isFun F.R (ZFSet.powerset F.R) A) {X' : Set ℝ}
    (hpw : X'.Pairwise fun x y => x ∉ pull (F := F) A y) : independent A (push (F := F) X') := by
  intro x hx y hy hxy Ay hAy hxAy
  obtain ⟨x', hx', rfl⟩ := mem_push.1 hx
  obtain ⟨y', hy', rfl⟩ := mem_push.1 hy
  have hne : x' ≠ y' := fun h => hxy (by rw [h])
  have h1 := hpw hx' hy' hne
  have h2 := eq_fval_of_app hA1 (ofR (F := F) y').2 hAy
  subst h2
  exact h1 hxAy

end Transport

/-- **DeepMind's proposition implies the Erdős property for every complete ordered field inside
`ZFSet`.** -/
theorem erdosProperty_of_deepmind (hE : erdos501_deepmind) (F : COF) :
    erdosProperty F.R F.plus F.ltR F.zero F.one := by
  intro A hA1 hA2
  have hbdd : ∀ r, Bornology.IsBounded (pull (F := F) A r) := fun r =>
    isBounded_pull (hA2 _ (ofR (F := F) r).2 _ (app_fval hA1 (ofR (F := F) r).2)).1
  have hvol : ∀ r, volume.toOuterMeasure (pull (F := F) A r) < 1 := fun r =>
    volume_pull_lt_one (hA2 _ (ofR (F := F) r).2 _ (app_fval hA1 (ofR (F := F) r).2)).2
  obtain ⟨X', hX'inf, hX'pw⟩ := hE (pull (F := F) A) hbdd hvol
  exact ⟨push (F := F) X', push_mem_powerset X', infinite_push hX'inf, independent_push hA1 hX'pw⟩

end COF

/-- **DeepMind's proposition implies `Erdos501_f` in the standard structure.** -/
theorem erdos501_std_of_deepmind (hE : erdos501_deepmind) : StdSem.erdos501 :=
  fun R plus times ltR zero one h =>
    COF.erdosProperty_of_deepmind hE ⟨R, plus, times, ltR, zero, one, h⟩

end ZFSetCOF

end Flypitch.Erdos501
