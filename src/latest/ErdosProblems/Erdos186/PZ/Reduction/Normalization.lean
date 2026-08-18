/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Reduction.InitialBox
import ErdosProblems.Erdos186.PZ.Reduction.BoundedContext

/-!
# Normalizing the initial integer box

The size estimates in the Pham--Zakharov reduction require a comparison box
which contains zero.  An arbitrary translated integer box does not have this
property.  We translate by its lower endpoint.  This preserves cardinality
and nonaveraging, sends the box to the zero-based box with the same number of
lattice points, and puts the normalized input in a rank-`d` proper GAP which
contains zero.
-/

namespace Erdos186.PZ.Reduction

noncomputable section

variable {d : ℕ}

/-- Translate a point so that the lower corner of `B` becomes zero. -/
def normalizePoint (B : CFP.IntegerBox d) (x : LatticePoint d) :
    LatticePoint d :=
  x - B.lower

/-- The inverse translation. -/
def denormalizePoint (B : CFP.IntegerBox d) (x : LatticePoint d) :
    LatticePoint d :=
  x + B.lower

@[simp] theorem denormalize_normalizePoint (B : CFP.IntegerBox d)
    (x : LatticePoint d) :
    denormalizePoint B (normalizePoint B x) = x := by
  funext i
  simp [normalizePoint, denormalizePoint]

@[simp] theorem normalize_denormalizePoint (B : CFP.IntegerBox d)
    (x : LatticePoint d) :
    normalizePoint B (denormalizePoint B x) = x := by
  funext i
  simp [normalizePoint, denormalizePoint]

theorem normalizePoint_injective (B : CFP.IntegerBox d) :
    Function.Injective (normalizePoint B) := by
  intro x y hxy
  have := congrArg (denormalizePoint B) hxy
  simpa using this

/-- The zero-based translate of `B`. -/
def normalizedBox (B : CFP.IntegerBox d) : CFP.IntegerBox d where
  lower := 0
  upper := B.upper - B.lower

/-- Membership is transported exactly by the normalization translation. -/
@[simp] theorem normalizePoint_mem_normalized_iff
    (B : CFP.IntegerBox d) (x : LatticePoint d) :
    normalizePoint B x ∈ (normalizedBox B).carrier ↔ x ∈ B.carrier := by
  rw [CFP.IntegerBox.mem_carrier_iff, CFP.IntegerBox.mem_carrier_iff]
  constructor <;> intro h i
  · have hi := h i
    dsimp [normalizePoint, normalizedBox] at hi ⊢
    constructor <;> linarith
  · have hi := h i
    dsimp [normalizePoint, normalizedBox] at hi ⊢
    constructor <;> linarith

/-- Translation does not change the number of lattice points of the box. -/
@[simp] theorem card_normalized (B : CFP.IntegerBox d) :
    (normalizedBox B).carrier.card = B.carrier.card := by
  rw [CFP.IntegerBox.card_carrier, CFP.IntegerBox.card_carrier]
  apply Finset.prod_congr rfl
  intro i _hi
  congr 1
  dsimp [normalizedBox]
  ring

/-- A nonempty original box gives a nonempty normalized box containing zero. -/
theorem normalized_nonempty (B : CFP.IntegerBox d)
    (hB : B.carrier.Nonempty) : (normalizedBox B).carrier.Nonempty := by
  obtain ⟨x, hx⟩ := hB
  exact ⟨normalizePoint B x, (normalizePoint_mem_normalized_iff B x).2 hx⟩

theorem zero_mem_normalized (B : CFP.IntegerBox d)
    (hB : B.carrier.Nonempty) : 0 ∈ (normalizedBox B).carrier := by
  rw [CFP.IntegerBox.mem_carrier_iff]
  intro i
  have hi := CFP.IntegerBox.lower_le_upper B hB i
  dsimp [normalizedBox]
  constructor <;> simp_all

/-- The symmetric enlargement of the zero-based box. -/
def symmetricNormalizedBox (B : CFP.IntegerBox d) : CFP.IntegerBox d where
  lower := -(B.upper - B.lower)
  upper := B.upper - B.lower

/-- The zero-based box lies in its symmetric enlargement. -/
theorem normalized_subset_symmetricNormalizedBox
    (B : CFP.IntegerBox d) (hB : B.carrier.Nonempty) :
    (normalizedBox B).carrier ⊆ (symmetricNormalizedBox B).carrier := by
  intro x hx
  rw [CFP.IntegerBox.mem_carrier_iff] at hx ⊢
  intro i
  have hwidth : 0 ≤ B.upper i - B.lower i := by
    exact sub_nonneg.mpr (CFP.IntegerBox.lower_le_upper B hB i)
  have hi := hx i
  dsimp [normalizedBox, symmetricNormalizedBox] at hi ⊢
  constructor
  · linarith
  · exact hi.2

/-- Symmetrization costs at most a factor `2^d` in box cardinality. -/
theorem card_symmetricNormalizedBox_le
    (B : CFP.IntegerBox d) (hB : B.carrier.Nonempty) :
    (symmetricNormalizedBox B).carrier.card ≤ 2 ^ d * B.carrier.card := by
  rw [CFP.IntegerBox.card_carrier, CFP.IntegerBox.card_carrier]
  calc
    ∏ i, ((symmetricNormalizedBox B).upper i + 1 -
          (symmetricNormalizedBox B).lower i).toNat
        ≤ ∏ i, 2 * (B.upper i + 1 - B.lower i).toNat := by
      apply Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _)
      intro i _hi
      have hw : 0 ≤ B.upper i - B.lower i :=
        sub_nonneg.mpr (CFP.IntegerBox.lower_le_upper B hB i)
      have hs : 0 ≤ (symmetricNormalizedBox B).upper i + 1 -
          (symmetricNormalizedBox B).lower i := by
        dsimp [symmetricNormalizedBox]
        linarith
      have ho : 0 ≤ B.upper i + 1 - B.lower i := by linarith
      dsimp [symmetricNormalizedBox]
      omega
    _ = 2 ^ d * ∏ i, (B.upper i + 1 - B.lower i).toNat := by
      rw [Finset.prod_mul_distrib]
      simp

/-- Normalize every point of a finite set by the lower corner of `B`. -/
def normalizeSet (B : CFP.IntegerBox d) (A : Finset (LatticePoint d)) :
    Finset (LatticePoint d) :=
  A.image (normalizePoint B)

@[simp] theorem card_normalizeSet (B : CFP.IntegerBox d)
    (A : Finset (LatticePoint d)) :
    (normalizeSet B A).card = A.card := by
  exact Finset.card_image_of_injective A (normalizePoint_injective B)

theorem normalizeSet_nonempty (B : CFP.IntegerBox d)
    {A : Finset (LatticePoint d)} (hA : A.Nonempty) :
    (normalizeSet B A).Nonempty := by
  obtain ⟨a, ha⟩ := hA
  exact ⟨normalizePoint B a, Finset.mem_image.mpr ⟨a, ha, rfl⟩⟩

theorem normalizeSet_subset_normalized (B : CFP.IntegerBox d)
    {A : Finset (LatticePoint d)} (hA : A ⊆ B.carrier) :
    normalizeSet B A ⊆ (normalizedBox B).carrier := by
  intro x hx
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  exact (normalizePoint_mem_normalized_iff B a).2 (hA ha)

/-- The normalized input also lies in the symmetric enlargement used by the
rank-at-most-ambient-dimensional comparison estimate. -/
theorem normalizeSet_subset_symmetricNormalizedBox
    (B : CFP.IntegerBox d) {A : Finset (LatticePoint d)}
    (hA : A.Nonempty) (hAB : A ⊆ B.carrier) :
    normalizeSet B A ⊆ (symmetricNormalizedBox B).carrier :=
  (normalizeSet_subset_normalized B hAB).trans
    (normalized_subset_symmetricNormalizedBox B (hA.mono hAB))

/-- Normalization is literally translation by `-B.lower`. -/
theorem normalizeSet_eq_translate (B : CFP.IntegerBox d)
    (A : Finset (LatticePoint d)) :
    normalizeSet B A = PZ.translate (-B.lower) A := by
  ext x
  simp only [normalizeSet, PZ.translate, Finset.mem_image]
  constructor <;> rintro ⟨a, ha, rfl⟩
  · exact ⟨a, ha, by funext i; simp [normalizePoint]; ring⟩
  · exact ⟨a, ha, by funext i; simp [normalizePoint]; ring⟩

/-- Nonaveraging is preserved by normalization. -/
theorem isBoxNonaveraging_normalizeSet (B : CFP.IntegerBox d)
    {A : Finset (LatticePoint d)} (hA : IsBoxNonaveraging A) :
    IsBoxNonaveraging (normalizeSet B A) := by
  rw [normalizeSet_eq_translate]
  exact PZ.isBoxNonaveraging_translate (-B.lower) hA

/-- Normalizing an eligible input preserves every analytic hypothesis and
the chosen scale. -/
def EligibleInput.normalize {β η : ℝ}
    {C : HigherDimensionalContext β η}
    {A : Finset (LatticePoint d)}
    (I : EligibleInput C A) : EligibleInput C (normalizeSet I.box A) where
  box := normalizedBox I.box
  scale := I.scale
  nonempty := normalizeSet_nonempty I.box I.nonempty
  subset_box := normalizeSet_subset_normalized I.box I.subset_box
  box_card_le := by simpa using I.box_card_le
  scale_lower := by simpa using I.scale_lower
  scale_upper := by simpa using I.scale_upper

/-- Normalize using a box propositionally identified with the box stored in
the eligible input.  This transport is useful in theorem statements whose
original box is a separate parameter. -/
def EligibleInput.normalizeTo {β η : ℝ}
    {C : HigherDimensionalContext β η}
    {A : Finset (LatticePoint d)} (I : EligibleInput C A)
    {B : CFP.IntegerBox d} (hB : I.box = B) :
    EligibleInput C (normalizeSet B A) := by
  subst B
  exact I.normalize

@[simp] theorem EligibleInput.normalize_scale {β η : ℝ}
    {C : HigherDimensionalContext β η}
    {A : Finset (LatticePoint d)} (I : EligibleInput C A) :
    I.normalize.scale = I.scale := rfl

@[simp] theorem EligibleInput.normalize_box {β η : ℝ}
    {C : HigherDimensionalContext β η}
    {A : Finset (LatticePoint d)} (I : EligibleInput C A) :
    I.normalize.box = normalizedBox I.box := rfl

end

end Erdos186.PZ.Reduction
