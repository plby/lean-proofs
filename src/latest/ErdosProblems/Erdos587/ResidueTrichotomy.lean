import ErdosProblems.Erdos587.NVDevelopment

open Filter MeasureTheory
open scoped Pointwise

namespace Erdos587

/-! ## The residue-selection part of the Nguyen--Vu trichotomy

The structural argument leaves the unused elements in only boundedly many
residue classes modulo the common step of the final progression.  The lemmas
below discard residue classes that occur too few times.  On the remaining
classes, Nguyen--Vu Lemma 4.3 either chooses realizable multiplicities whose
weighted sum is a prescribed quadratic residue, or a prime divisor of the
modulus divides every remaining element. -/

/-- The representative in `{1, ..., q}` of the residue class of `a` modulo
`q`; multiples of `q` are represented by `q`, rather than by zero. -/
def positiveResidue (q a : ℕ) : ℕ :=
  if q ∣ a then q else a % q

lemma positiveResidue_modEq (q a : ℕ) :
    a ≡ positiveResidue q a [MOD q] := by
  unfold positiveResidue Nat.ModEq
  by_cases h : q ∣ a
  · simp [h, Nat.mod_eq_zero_of_dvd h]
  · simp [h]

lemma positiveResidue_pos {q a : ℕ} (hq : 0 < q) :
    0 < positiveResidue q a := by
  unfold positiveResidue
  by_cases h : q ∣ a
  · simpa [h] using hq
  · simp only [h, ↓reduceIte]
    exact Nat.pos_of_ne_zero (by
      intro hz
      exact h (Nat.dvd_iff_mod_eq_zero.mpr hz))

lemma positiveResidue_le {q a : ℕ} (hq : 0 < q) :
    positiveResidue q a ≤ q := by
  unfold positiveResidue
  by_cases h : q ∣ a
  · simp [h]
  · simp only [h, ↓reduceIte]
    exact (Nat.mod_lt a hq).le

def residueFiber (q : ℕ) (A : Finset ℕ) (g : ℕ) : Finset ℕ :=
  A.filter fun a ↦ positiveResidue q a = g

def usedPositiveResidues (q : ℕ) (A : Finset ℕ) : Finset ℕ :=
  A.image (positiveResidue q)

@[simp] lemma mem_residueFiber {q g a : ℕ} {A : Finset ℕ} :
    a ∈ residueFiber q A g ↔ a ∈ A ∧ positiveResidue q a = g := by
  simp [residueFiber]

@[simp] lemma mem_usedPositiveResidues {q g : ℕ} {A : Finset ℕ} :
    g ∈ usedPositiveResidues q A ↔
      ∃ a ∈ A, positiveResidue q a = g := by
  simp [usedPositiveResidues]

/-- Realize a list of multiplicities by choosing that many distinct elements
from the corresponding residue fibers.  The no-duplicate condition on the
coefficient list makes the chosen fibers disjoint. -/
lemma exists_subset_sum_modEq_nvListDot_of_residue_fibers_with_card
    {q : ℕ} (A : Finset ℕ) (coeff values : List ℕ)
    (hnodup : coeff.Nodup)
    (hbounded : List.Forall₂
      (fun g x ↦ x ≤ (residueFiber q A g).card) coeff values) :
    ∃ S : Finset ℕ, S ⊆ A ∧
      (∀ a ∈ S, positiveResidue q a ∈ coeff) ∧
      S.card = values.sum ∧
      (((∑ a ∈ S, a : ℕ) : ℤ) ≡ nvListDot coeff values
        [ZMOD (q : ℤ)]) := by
  induction coeff generalizing values with
  | nil =>
      have hvalues : values = [] := by
        cases values with
        | nil => rfl
        | cons x xs => cases hbounded
      subst values
      exact ⟨∅, by simp, by simp, by simp, by simp⟩
  | cons g coeff ih =>
      cases values with
      | nil => cases hbounded
      | cons x values =>
          rw [List.nodup_cons] at hnodup
          cases hbounded with
          | cons hx htail =>
              obtain ⟨X, hXfiber, hXcard⟩ :=
                Finset.exists_subset_card_eq hx
              obtain ⟨S, hSA, hSres, hScard, hSmod⟩ :=
                ih values hnodup.2 htail
              have hXA : X ⊆ A := by
                intro a ha
                exact (mem_residueFiber.mp (hXfiber ha)).1
              have hXres : ∀ a ∈ X, positiveResidue q a = g := by
                intro a ha
                exact (mem_residueFiber.mp (hXfiber ha)).2
              have hdisj : Disjoint X S := by
                rw [Finset.disjoint_left]
                intro a haX haS
                have haTail := hSres a haS
                rw [hXres a haX] at haTail
                exact hnodup.1 haTail
              have hXmod : (((∑ a ∈ X, a : ℕ) : ℤ) ≡
                  (g : ℤ) * (x : ℤ) [ZMOD (q : ℤ)]) := by
                have hpoint : ∀ a ∈ X, (a : ℤ) ≡ (g : ℤ)
                    [ZMOD (q : ℤ)] := by
                  intro a ha
                  have hnat := positiveResidue_modEq q a
                  rw [hXres a ha] at hnat
                  exact_mod_cast hnat
                have hsum := Int.ModEq.sum hpoint
                have hcast : (((∑ a ∈ X, a : ℕ) : ℤ)) =
                    ∑ a ∈ X, (a : ℤ) := by push_cast; rfl
                have hconst : (∑ _a ∈ X, (g : ℤ)) =
                    (g : ℤ) * (x : ℤ) := by
                  simp [hXcard, mul_comm]
                rw [hcast]
                calc
                  (∑ a ∈ X, (a : ℤ)) ≡
                      ∑ _a ∈ X, (g : ℤ) [ZMOD (q : ℤ)] := hsum
                  _ = (g : ℤ) * (x : ℤ) := hconst
              refine ⟨X ∪ S, Finset.union_subset hXA hSA, ?_, ?_, ?_⟩
              · intro a ha
                rw [Finset.mem_union] at ha
                rcases ha with ha | ha
                · simp [hXres a ha]
                · exact List.mem_cons_of_mem g (hSres a ha)
              · rw [Finset.card_union_of_disjoint hdisj, hXcard, hScard,
                  List.sum_cons]
              · have hadd := hXmod.add hSmod
                have hcast : (((∑ a ∈ X ∪ S, a : ℕ) : ℤ)) =
                    ((∑ a ∈ X, a : ℕ) : ℤ) +
                      ((∑ a ∈ S, a : ℕ) : ℤ) := by
                  rw [Finset.sum_union hdisj]
                  push_cast
                  rfl
                rw [hcast]
                simpa only [nvListDot_cons] using hadd

/-- The cardinality-free form used by the terminal residue trichotomy. -/
lemma exists_subset_sum_modEq_nvListDot_of_residue_fibers
    {q : ℕ} (A : Finset ℕ) (coeff values : List ℕ)
    (hnodup : coeff.Nodup)
    (hbounded : List.Forall₂
      (fun g x ↦ x ≤ (residueFiber q A g).card) coeff values) :
    ∃ S : Finset ℕ, S ⊆ A ∧
      (∀ a ∈ S, positiveResidue q a ∈ coeff) ∧
      (((∑ a ∈ S, a : ℕ) : ℤ) ≡ nvListDot coeff values
        [ZMOD (q : ℤ)]) := by
  obtain ⟨S, hSA, hSres, _hScard, hSmod⟩ :=
    exists_subset_sum_modEq_nvListDot_of_residue_fibers_with_card
      A coeff values hnodup hbounded
  exact ⟨S, hSA, hSres, hSmod⟩

/-- Residue classes whose fibers can realize every multiplicity up to `B`. -/
def largePositiveResidues (q B : ℕ) (A : Finset ℕ) : Finset ℕ :=
  (usedPositiveResidues q A).filter fun g ↦
    B ≤ (residueFiber q A g).card

/-- The elements of `A` lying in a large residue fiber. -/
def largeResiduePart (q B : ℕ) (A : Finset ℕ) : Finset ℕ :=
  A.filter fun a ↦ positiveResidue q a ∈ largePositiveResidues q B A

lemma largeResiduePart_subset (q B : ℕ) (A : Finset ℕ) :
    largeResiduePart q B A ⊆ A := by
  exact Finset.filter_subset _ _

lemma mem_largeResiduePart {q B a : ℕ} {A : Finset ℕ} :
    a ∈ largeResiduePart q B A ↔
      a ∈ A ∧ positiveResidue q a ∈ largePositiveResidues q B A := by
  simp [largeResiduePart]

lemma mem_largePositiveResidues {q B g : ℕ} {A : Finset ℕ} :
    g ∈ largePositiveResidues q B A ↔
      g ∈ usedPositiveResidues q A ∧ B ≤ (residueFiber q A g).card := by
  simp [largePositiveResidues]

/-! ### From a bounded GAP cover to boundedly many residues -/

/-- Positive representative of an integer residue class modulo a positive
natural modulus. -/
def positiveIntResidue (q : ℕ) (z : ℤ) : ℕ :=
  if z % (q : ℤ) = 0 then q else (z % (q : ℤ)).toNat

lemma positiveIntResidue_modEq {q : ℕ} (hq : 0 < q) (z : ℤ) :
    (positiveIntResidue q z : ℤ) ≡ z [ZMOD (q : ℤ)] := by
  change (positiveIntResidue q z : ℤ) % (q : ℤ) = z % (q : ℤ)
  unfold positiveIntResidue
  by_cases hz : z % (q : ℤ) = 0
  · simp [hz, hq.ne']
  · simp only [hz, ↓reduceIte]
    have hnonneg : 0 ≤ z % (q : ℤ) :=
      Int.emod_nonneg _ (by exact_mod_cast hq.ne')
    rw [Int.toNat_of_nonneg hnonneg, Int.emod_emod]

/-- The ordinary integer residue classes represented by a finite set.  This
auxiliary set is used when only one step of a rank-two progression divides
the modulus: the other coordinate then controls the number of possible
residues. -/
def intResidues (q : ℕ) (A : Finset ℤ) : Finset ℤ :=
  A.image fun z ↦ z % (q : ℤ)

@[simp] lemma mem_intResidues {q : ℕ} {A : Finset ℤ} {r : ℤ} :
    r ∈ intResidues q A ↔ ∃ z ∈ A, z % (q : ℤ) = r := by
  simp [intResidues]

/-- Taking a difference can at most square the number of residue classes. -/
lemma intResidues_sub_card_le (q : ℕ) (A B : Finset ℤ) :
    (intResidues q (A - B)).card ≤
      (intResidues q A).card * (intResidues q B).card := by
  let C := Finset.image₂ (fun x y : ℤ ↦ (x - y) % (q : ℤ))
    (intResidues q A) (intResidues q B)
  have hsub : intResidues q (A - B) ⊆ C := by
    intro r hr
    obtain ⟨z, hz, hzr⟩ := mem_intResidues.mp hr
    obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_sub.mp hz
    apply Finset.mem_image₂.mpr
    refine ⟨a % (q : ℤ), ?_, b % (q : ℤ), ?_, ?_⟩
    · exact mem_intResidues.mpr ⟨a, ha, rfl⟩
    · exact mem_intResidues.mpr ⟨b, hb, rfl⟩
    · rw [← hzr]
      exact ((Int.mod_modEq a (q : ℤ)).sub
        (Int.mod_modEq b (q : ℤ))).eq
  calc
    (intResidues q (A - B)).card ≤ C.card := Finset.card_le_card hsub
    _ ≤ (intResidues q A).card * (intResidues q B).card :=
      Finset.card_image₂_le _ _ _

/-- After `n` iterated differences, the number of residues grows by at most
the `2^n`-th power. -/
lemma intResidues_iteratedDifference_card_le (q n : ℕ) (A : Finset ℤ) :
    (intResidues q (iteratedDifference n A)).card ≤
      (intResidues q A).card ^ (2 ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [iteratedDifference_succ]
      calc
        (intResidues q
            (iteratedDifference n A - iteratedDifference n A)).card ≤
            (intResidues q (iteratedDifference n A)).card *
              (intResidues q (iteratedDifference n A)).card :=
          intResidues_sub_card_le q _ _
        _ ≤ (intResidues q A).card ^ (2 ^ n) *
              (intResidues q A).card ^ (2 ^ n) :=
          Nat.mul_le_mul ih ih
        _ = (intResidues q A).card ^ (2 ^ (n + 1)) := by
          rw [pow_succ, pow_mul]
          rw [pow_two]

lemma positiveResidue_eq_positiveIntResidue_of_modEq
    {q a : ℕ} {z : ℤ} (hq : 0 < q)
    (h : (a : ℤ) ≡ z [ZMOD (q : ℤ)]) :
    positiveResidue q a = positiveIntResidue q z := by
  have h' := h
  change (a : ℤ) % (q : ℤ) = z % (q : ℤ) at h'
  have hrem : ((a % q : ℕ) : ℤ) = z % (q : ℤ) := by
    simpa only [Int.natCast_emod] using h'
  by_cases ha : q ∣ a
  · have ha0 : a % q = 0 := Nat.mod_eq_zero_of_dvd ha
    have hz0 : z % (q : ℤ) = 0 := by simpa [ha0] using hrem.symm
    simp [positiveResidue, positiveIntResidue, ha, hz0]
  · have ha0 : a % q ≠ 0 := by
      intro hz
      exact ha (Nat.dvd_iff_mod_eq_zero.mpr hz)
    have hz0 : z % (q : ℤ) ≠ 0 := by
      intro hz
      apply ha0
      exact_mod_cast hrem.trans hz
    simp only [positiveResidue, positiveIntResidue, ha, hz0, ↓reduceIte]
    have hznonneg : 0 ≤ z % (q : ℤ) :=
      Int.emod_nonneg _ (by exact_mod_cast hq.ne')
    rw [← Int.toNat_of_nonneg hznonneg] at hrem
    exact_mod_cast hrem

/-- A translate cover has at most the product of the two residue counts.
Unlike `usedPositiveResidues_card_le_of_iteratedDifference_cover`, this
lemma does not assume that the second summand is divisible by the modulus. -/
lemma usedPositiveResidues_card_le_of_add_cover
    {q : ℕ} {A : Finset ℕ} {Z D : Finset ℤ} (hq : 0 < q)
    (hcover : natToIntFinset A ⊆ Z + D) :
    (usedPositiveResidues q A).card ≤
      Z.card * (intResidues q D).card := by
  let Zres := intResidues q Z
  let Dres := intResidues q D
  let C := Finset.image₂
    (fun z d : ℤ ↦ positiveIntResidue q (z + d)) Zres Dres
  have hsub : usedPositiveResidues q A ⊆ C := by
    intro g hg
    obtain ⟨a, haA, rfl⟩ := mem_usedPositiveResidues.mp hg
    have haInt : (a : ℤ) ∈ natToIntFinset A :=
      natCast_mem_natToIntFinset.mpr haA
    obtain ⟨z, hz, d, hd, hzd⟩ := Finset.mem_add.mp (hcover haInt)
    apply Finset.mem_image₂.mpr
    refine ⟨z % (q : ℤ), ?_, d % (q : ℤ), ?_, ?_⟩
    · exact mem_intResidues.mpr ⟨z, hz, rfl⟩
    · exact mem_intResidues.mpr ⟨d, hd, rfl⟩
    · have hmod : (a : ℤ) ≡ z % (q : ℤ) + d % (q : ℤ)
          [ZMOD (q : ℤ)] := by
        rw [← hzd]
        exact (Int.mod_modEq z (q : ℤ)).symm.add
          (Int.mod_modEq d (q : ℤ)).symm
      exact (positiveResidue_eq_positiveIntResidue_of_modEq hq hmod).symm
  calc
    (usedPositiveResidues q A).card ≤ C.card := Finset.card_le_card hsub
    _ ≤ Zres.card * Dres.card := Finset.card_image₂_le _ _ _
    _ ≤ Z.card * (intResidues q D).card := by
      dsimp only [Zres, Dres]
      exact Nat.mul_le_mul_right _ Finset.card_image_le

namespace GeneralizedAP

/-- In a rank-two GAP, reduction modulo the second positive step forgets the
second coordinate.  Hence the first side alone bounds the number of residue
classes represented by the carrier. -/
lemma intResidues_carrier_card_le_first_side
    (R : GeneralizedAP) (hrank : R.rank = 2) {q : ℕ}
    (hqstep : (q : ℤ) = R.positiveForm.step
      ⟨1, by simp [GeneralizedAP.rank_positiveForm, hrank]⟩) :
    (intResidues q R.carrier).card ≤
      R.length ⟨0, by omega⟩ + 1 := by
  let S := R.positiveForm
  let i₀ : Fin S.rank := ⟨0, by dsimp [S]; omega⟩
  let i₁ : Fin S.rank := ⟨1, by dsimp [S]; omega⟩
  let X := (Finset.range (S.length i₀ + 1)).image
    (fun x : ℕ ↦ (S.base + (x : ℤ) * S.step i₀) % (q : ℤ))
  have hi01 : i₀ ≠ i₁ := by
    intro h
    have := congrArg Fin.val h
    simp [i₀, i₁] at this
  have hall (j : Fin S.rank) : j = i₀ ∨ j = i₁ := by
    have hjlt : j.val < 2 := by simpa [S, hrank] using j.isLt
    by_cases hj0 : j.val = 0
    · exact Or.inl (Fin.ext (by simpa [i₀] using hj0))
    · have hj1 : j.val = 1 := by omega
      exact Or.inr (Fin.ext (by simpa [i₁] using hj1))
  have huniv : (Finset.univ : Finset (Fin S.rank)) = {i₀, i₁} := by
    ext j
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
      true_iff]
    exact hall j
  have hsub : intResidues q R.carrier ⊆ X := by
    intro r hr
    obtain ⟨z, hzR, hzr⟩ := mem_intResidues.mp hr
    have hzS : z ∈ S.carrier := by
      dsimp only [S]
      rw [R.carrier_positiveForm]
      exact hzR
    obtain ⟨v, rfl⟩ := S.mem_carrier_iff.mp hzS
    apply Finset.mem_image.mpr
    refine ⟨(v i₀ : ℕ), Finset.mem_range.mpr (v i₀).isLt, ?_⟩
    rw [← hzr]
    have heval : S.eval v =
        S.base + ((v i₀ : ℕ) : ℤ) * S.step i₀ +
          ((v i₁ : ℕ) : ℤ) * S.step i₁ := by
      simp only [GeneralizedAP.eval]
      rw [huniv]
      simp [hi01]
      ring
    have hqstep' : (q : ℤ) = S.step i₁ := by
      simpa [S, i₁] using hqstep
    have hzero : ((v i₁ : ℕ) : ℤ) * S.step i₁ ≡ 0
        [ZMOD (q : ℤ)] := by
      rw [← hqstep']
      exact Int.modEq_zero_iff_dvd.mpr ⟨((v i₁ : ℕ) : ℤ), by ring⟩
    have hmod := (Int.ModEq.refl
      (S.base + ((v i₀ : ℕ) : ℤ) * S.step i₀)).add hzero
    rw [heval]
    simpa using hmod.eq.symm
  calc
    (intResidues q R.carrier).card ≤ X.card := Finset.card_le_card hsub
    _ ≤ (Finset.range (S.length i₀ + 1)).card := Finset.card_image_le
    _ = R.length ⟨0, by omega⟩ + 1 := by simp [S, i₀]

/-- Symmetric form: reduction modulo the first positive step forgets the
first coordinate, so the second side bounds the residue count. -/
lemma intResidues_carrier_card_le_second_side
    (R : GeneralizedAP) (hrank : R.rank = 2) {q : ℕ}
    (hqstep : (q : ℤ) = R.positiveForm.step
      ⟨0, by simp [GeneralizedAP.rank_positiveForm, hrank]⟩) :
    (intResidues q R.carrier).card ≤
      R.length ⟨1, by omega⟩ + 1 := by
  let S := R.positiveForm
  let i₀ : Fin S.rank := ⟨0, by dsimp [S]; omega⟩
  let i₁ : Fin S.rank := ⟨1, by dsimp [S]; omega⟩
  let X := (Finset.range (S.length i₁ + 1)).image
    (fun y : ℕ ↦ (S.base + (y : ℤ) * S.step i₁) % (q : ℤ))
  have hi01 : i₀ ≠ i₁ := by
    intro h
    have := congrArg Fin.val h
    simp [i₀, i₁] at this
  have hall (j : Fin S.rank) : j = i₀ ∨ j = i₁ := by
    have hjlt : j.val < 2 := by simpa [S, hrank] using j.isLt
    by_cases hj0 : j.val = 0
    · exact Or.inl (Fin.ext (by simpa [i₀] using hj0))
    · have hj1 : j.val = 1 := by omega
      exact Or.inr (Fin.ext (by simpa [i₁] using hj1))
  have huniv : (Finset.univ : Finset (Fin S.rank)) = {i₀, i₁} := by
    ext j
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
      true_iff]
    exact hall j
  have hsub : intResidues q R.carrier ⊆ X := by
    intro r hr
    obtain ⟨z, hzR, hzr⟩ := mem_intResidues.mp hr
    have hzS : z ∈ S.carrier := by
      dsimp only [S]
      rw [R.carrier_positiveForm]
      exact hzR
    obtain ⟨v, rfl⟩ := S.mem_carrier_iff.mp hzS
    apply Finset.mem_image.mpr
    refine ⟨(v i₁ : ℕ), Finset.mem_range.mpr (v i₁).isLt, ?_⟩
    rw [← hzr]
    have heval : S.eval v =
        S.base + ((v i₀ : ℕ) : ℤ) * S.step i₀ +
          ((v i₁ : ℕ) : ℤ) * S.step i₁ := by
      simp only [GeneralizedAP.eval]
      rw [huniv]
      simp [hi01]
      ring
    have hqstep' : (q : ℤ) = S.step i₀ := by
      simpa [S, i₀] using hqstep
    have hzero : ((v i₀ : ℕ) : ℤ) * S.step i₀ ≡ 0
        [ZMOD (q : ℤ)] := by
      rw [← hqstep']
      exact Int.modEq_zero_iff_dvd.mpr ⟨((v i₀ : ℕ) : ℤ), by ring⟩
    have hmod := hzero.add (Int.ModEq.refl
      (S.base + ((v i₁ : ℕ) : ℤ) * S.step i₁))
    rw [heval]
    have hmod' :
        S.base + ((v i₀ : ℕ) : ℤ) * S.step i₀ +
            ((v i₁ : ℕ) : ℤ) * S.step i₁ ≡
          S.base + ((v i₁ : ℕ) : ℤ) * S.step i₁ [ZMOD (q : ℤ)] := by
      convert hmod using 1 <;> ring
    exact hmod'.eq.symm
  calc
    (intResidues q R.carrier).card ≤ X.card := Finset.card_le_card hsub
    _ ≤ (Finset.range (S.length i₁ + 1)).card := Finset.card_image_le
    _ = R.length ⟨1, by omega⟩ + 1 := by simp [S, i₁]

/-- Modulo the second positive step, a carrier point is represented by its
first coordinate alone.  We retain the actual coordinate here (rather than
only its residue) in order to keep iterated differences inside a linearly
growing interval. -/
lemma carrier_modEq_first_coordinate_rank_two
    (R : GeneralizedAP) (hrank : R.rank = 2) {q : ℕ}
    (hqstep : (q : ℤ) = R.positiveForm.step
      ⟨1, by simp [GeneralizedAP.rank_positiveForm, hrank]⟩) :
    ∀ {z : ℤ}, z ∈ R.carrier →
      ∃ x : ℕ, x ≤ R.length ⟨0, by omega⟩ ∧
        z ≡ R.positiveForm.base +
          (x : ℤ) * R.positiveForm.step
            ⟨0, by simp [GeneralizedAP.rank_positiveForm, hrank]⟩
          [ZMOD (q : ℤ)] := by
  intro z hz
  let S := R.positiveForm
  let i₀ : Fin S.rank := ⟨0, by dsimp [S]; omega⟩
  let i₁ : Fin S.rank := ⟨1, by dsimp [S]; omega⟩
  have hi₀₁ : i₀ ≠ i₁ := by
    intro h
    have := congrArg Fin.val h
    simp [i₀, i₁] at this
  have huniv : (Finset.univ : Finset (Fin S.rank)) = {i₀, i₁} := by
    ext i
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
      true_iff]
    have hi : i.val = 0 ∨ i.val = 1 := by
      have hilt : i.val < 2 := by simpa [S, hrank] using i.isLt
      omega
    rcases hi with hi | hi
    · exact Or.inl (Fin.ext (by simpa [i₀] using hi))
    · exact Or.inr (Fin.ext (by simpa [i₁] using hi))
  have hzS : z ∈ S.carrier := by
    dsimp only [S]
    rw [R.carrier_positiveForm]
    exact hz
  obtain ⟨v, rfl⟩ := S.mem_carrier_iff.mp hzS
  refine ⟨(v i₀ : ℕ), Nat.le_of_lt_succ (v i₀).isLt, ?_⟩
  have heval : S.eval v =
      S.base + ((v i₀ : ℕ) : ℤ) * S.step i₀ +
        ((v i₁ : ℕ) : ℤ) * S.step i₁ := by
    simp only [GeneralizedAP.eval]
    rw [huniv]
    simp [hi₀₁]
    ring
  have hqstep' : (q : ℤ) = S.step i₁ := by
    simpa [S, i₁] using hqstep
  have hzero : ((v i₁ : ℕ) : ℤ) * S.step i₁ ≡ 0
      [ZMOD (q : ℤ)] := by
    rw [← hqstep']
    exact Int.modEq_zero_iff_dvd.mpr ⟨((v i₁ : ℕ) : ℤ), by ring⟩
  rw [heval]
  simpa [S, i₀] using
    (Int.ModEq.refl
      (S.base + ((v i₀ : ℕ) : ℤ) * S.step i₀)).add hzero

/-- After `n+1` differences, the surviving first coordinate has absolute
value at most `2^n` times the original first side. -/
lemma iteratedDifference_rank_two_exists_first_coordinate
    (R : GeneralizedAP) (hrank : R.rank = 2) {q : ℕ}
    (hqstep : (q : ℤ) = R.positiveForm.step
      ⟨1, by simp [GeneralizedAP.rank_positiveForm, hrank]⟩) :
    ∀ n {z : ℤ}, z ∈ iteratedDifference (n + 1) R.carrier →
      ∃ k : ℤ,
        |k| ≤ (2 ^ n * R.length ⟨0, by omega⟩ : ℕ) ∧
        z ≡ k * R.positiveForm.step
          ⟨0, by simp [GeneralizedAP.rank_positiveForm, hrank]⟩
          [ZMOD (q : ℤ)] := by
  intro n
  induction n with
  | zero =>
      intro z hz
      obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_sub.mp hz
      obtain ⟨x, hx, hax⟩ :=
        R.carrier_modEq_first_coordinate_rank_two hrank hqstep ha
      obtain ⟨y, hy, hby⟩ :=
        R.carrier_modEq_first_coordinate_rank_two hrank hqstep hb
      refine ⟨(x : ℤ) - y, ?_, ?_⟩
      · rw [abs_le]
        constructor <;> norm_num at * <;> omega
      · have := hax.sub hby
        convert this using 1 <;> ring
  | succ n ih =>
      intro z hz
      obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_sub.mp hz
      obtain ⟨x, hx, hax⟩ := ih ha
      obtain ⟨y, hy, hby⟩ := ih hb
      refine ⟨x - y, ?_, ?_⟩
      · calc
          |x - y| ≤ |x| + |y| := abs_sub x y
          _ ≤ (2 ^ n * R.length ⟨0, by omega⟩ : ℕ) +
                (2 ^ n * R.length ⟨0, by omega⟩ : ℕ) :=
            add_le_add hx hy
          _ = (2 ^ (n + 1) * R.length ⟨0, by omega⟩ : ℕ) := by
            norm_num
            rw [pow_succ]
            ring
      · convert hax.sub hby using 1 <;> ring

/-- The preceding coordinate interval gives a linear, rather than
exponential-in-the-side-length, residue bound for iterated differences. -/
lemma intResidues_iteratedDifference_rank_two_second_step_card_le
    (R : GeneralizedAP) (hrank : R.rank = 2) {q n : ℕ}
    (hqstep : (q : ℤ) = R.positiveForm.step
      ⟨1, by simp [GeneralizedAP.rank_positiveForm, hrank]⟩) :
    (intResidues q (iteratedDifference (n + 1) R.carrier)).card ≤
      2 * (2 ^ n * R.length ⟨0, by omega⟩) + 1 := by
  let B := 2 ^ n * R.length ⟨0, by omega⟩
  let X := (Finset.Icc (-(B : ℤ)) (B : ℤ)).image fun k ↦
    (k * R.positiveForm.step
      ⟨0, by simp [GeneralizedAP.rank_positiveForm, hrank]⟩) % (q : ℤ)
  have hsub : intResidues q (iteratedDifference (n + 1) R.carrier) ⊆ X := by
    intro r hr
    obtain ⟨z, hz, hzr⟩ := mem_intResidues.mp hr
    obtain ⟨k, hk, hzk⟩ :=
      R.iteratedDifference_rank_two_exists_first_coordinate hrank hqstep n hz
    apply Finset.mem_image.mpr
    refine ⟨k, Finset.mem_Icc.mpr (abs_le.mp (by simpa only [B] using hk)), ?_⟩
    rw [← hzr]
    exact hzk.eq.symm
  calc
    (intResidues q (iteratedDifference (n + 1) R.carrier)).card ≤ X.card :=
      Finset.card_le_card hsub
    _ ≤ (Finset.Icc (-(B : ℤ)) (B : ℤ)).card := Finset.card_image_le
    _ = 2 * B + 1 := by
      rw [Int.card_Icc]
      norm_num
      omega
    _ = 2 * (2 ^ n * R.length ⟨0, by omega⟩) + 1 := rfl

/-- Symmetric coordinate representative modulo the first positive step. -/
lemma carrier_modEq_second_coordinate_rank_two
    (R : GeneralizedAP) (hrank : R.rank = 2) {q : ℕ}
    (hqstep : (q : ℤ) = R.positiveForm.step
      ⟨0, by simp [GeneralizedAP.rank_positiveForm, hrank]⟩) :
    ∀ {z : ℤ}, z ∈ R.carrier →
      ∃ y : ℕ, y ≤ R.length ⟨1, by omega⟩ ∧
        z ≡ R.positiveForm.base +
          (y : ℤ) * R.positiveForm.step
            ⟨1, by simp [GeneralizedAP.rank_positiveForm, hrank]⟩
          [ZMOD (q : ℤ)] := by
  intro z hz
  let S := R.positiveForm
  let i₀ : Fin S.rank := ⟨0, by dsimp [S]; omega⟩
  let i₁ : Fin S.rank := ⟨1, by dsimp [S]; omega⟩
  have hi₀₁ : i₀ ≠ i₁ := by
    intro h
    have := congrArg Fin.val h
    simp [i₀, i₁] at this
  have huniv : (Finset.univ : Finset (Fin S.rank)) = {i₀, i₁} := by
    ext i
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
      true_iff]
    have hilt : i.val < 2 := by simpa [S, hrank] using i.isLt
    have hi : i.val = 0 ∨ i.val = 1 := by omega
    rcases hi with hi | hi
    · exact Or.inl (Fin.ext (by simpa [i₀] using hi))
    · exact Or.inr (Fin.ext (by simpa [i₁] using hi))
  have hzS : z ∈ S.carrier := by
    dsimp only [S]
    rw [R.carrier_positiveForm]
    exact hz
  obtain ⟨v, rfl⟩ := S.mem_carrier_iff.mp hzS
  refine ⟨(v i₁ : ℕ), Nat.le_of_lt_succ (v i₁).isLt, ?_⟩
  have heval : S.eval v =
      S.base + ((v i₀ : ℕ) : ℤ) * S.step i₀ +
        ((v i₁ : ℕ) : ℤ) * S.step i₁ := by
    simp only [GeneralizedAP.eval]
    rw [huniv]
    simp [hi₀₁]
    ring
  have hqstep' : (q : ℤ) = S.step i₀ := by
    simpa [S, i₀] using hqstep
  have hzero : ((v i₀ : ℕ) : ℤ) * S.step i₀ ≡ 0
      [ZMOD (q : ℤ)] := by
    rw [← hqstep']
    exact Int.modEq_zero_iff_dvd.mpr ⟨((v i₀ : ℕ) : ℤ), by ring⟩
  rw [heval]
  have hmod := hzero.add (Int.ModEq.refl
    (S.base + ((v i₁ : ℕ) : ℤ) * S.step i₁))
  convert hmod using 1 <;> simp [S, i₁] <;> ring

lemma iteratedDifference_rank_two_exists_second_coordinate
    (R : GeneralizedAP) (hrank : R.rank = 2) {q : ℕ}
    (hqstep : (q : ℤ) = R.positiveForm.step
      ⟨0, by simp [GeneralizedAP.rank_positiveForm, hrank]⟩) :
    ∀ n {z : ℤ}, z ∈ iteratedDifference (n + 1) R.carrier →
      ∃ k : ℤ,
        |k| ≤ (2 ^ n * R.length ⟨1, by omega⟩ : ℕ) ∧
        z ≡ k * R.positiveForm.step
          ⟨1, by simp [GeneralizedAP.rank_positiveForm, hrank]⟩
          [ZMOD (q : ℤ)] := by
  intro n
  induction n with
  | zero =>
      intro z hz
      obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_sub.mp hz
      obtain ⟨x, hx, hax⟩ :=
        R.carrier_modEq_second_coordinate_rank_two hrank hqstep ha
      obtain ⟨y, hy, hby⟩ :=
        R.carrier_modEq_second_coordinate_rank_two hrank hqstep hb
      refine ⟨(x : ℤ) - y, ?_, ?_⟩
      · rw [abs_le]
        constructor <;> norm_num at * <;> omega
      · have := hax.sub hby
        convert this using 1 <;> ring
  | succ n ih =>
      intro z hz
      obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_sub.mp hz
      obtain ⟨x, hx, hax⟩ := ih ha
      obtain ⟨y, hy, hby⟩ := ih hb
      refine ⟨x - y, ?_, ?_⟩
      · calc
          |x - y| ≤ |x| + |y| := abs_sub x y
          _ ≤ (2 ^ n * R.length ⟨1, by omega⟩ : ℕ) +
                (2 ^ n * R.length ⟨1, by omega⟩ : ℕ) :=
            add_le_add hx hy
          _ = (2 ^ (n + 1) * R.length ⟨1, by omega⟩ : ℕ) := by
            norm_num
            rw [pow_succ]
            ring
      · convert hax.sub hby using 1 <;> ring

lemma intResidues_iteratedDifference_rank_two_first_step_card_le
    (R : GeneralizedAP) (hrank : R.rank = 2) {q n : ℕ}
    (hqstep : (q : ℤ) = R.positiveForm.step
      ⟨0, by simp [GeneralizedAP.rank_positiveForm, hrank]⟩) :
    (intResidues q (iteratedDifference (n + 1) R.carrier)).card ≤
      2 * (2 ^ n * R.length ⟨1, by omega⟩) + 1 := by
  let B := 2 ^ n * R.length ⟨1, by omega⟩
  let X := (Finset.Icc (-(B : ℤ)) (B : ℤ)).image fun k ↦
    (k * R.positiveForm.step
      ⟨1, by simp [GeneralizedAP.rank_positiveForm, hrank]⟩) % (q : ℤ)
  have hsub : intResidues q (iteratedDifference (n + 1) R.carrier) ⊆ X := by
    intro r hr
    obtain ⟨z, hz, hzr⟩ := mem_intResidues.mp hr
    obtain ⟨k, hk, hzk⟩ :=
      R.iteratedDifference_rank_two_exists_second_coordinate hrank hqstep n hz
    apply Finset.mem_image.mpr
    refine ⟨k, Finset.mem_Icc.mpr (abs_le.mp (by simpa only [B] using hk)), ?_⟩
    rw [← hzr]
    exact hzk.eq.symm
  calc
    (intResidues q (iteratedDifference (n + 1) R.carrier)).card ≤ X.card :=
      Finset.card_le_card hsub
    _ ≤ (Finset.Icc (-(B : ℤ)) (B : ℤ)).card := Finset.card_image_le
    _ = 2 * B + 1 := by
      rw [Int.card_Icc]
      norm_num
      omega
    _ = 2 * (2 ^ n * R.length ⟨1, by omega⟩) + 1 := rfl

/-- If a modulus divides every GAP step, every carrier element is congruent
to the GAP base modulo that modulus. -/
lemma carrier_modEq_base_of_dvd_steps (R : GeneralizedAP) {q : ℕ}
    (hstep : ∀ i : Fin R.rank, (q : ℤ) ∣ R.step i) :
    ∀ {x : ℤ}, x ∈ R.carrier → x ≡ R.base [ZMOD (q : ℤ)] := by
  intro x hx
  obtain ⟨v, rfl⟩ := R.mem_carrier_iff.mp hx
  have hterm : ∀ i ∈ (Finset.univ : Finset (Fin R.rank)),
      ((v i : ℕ) : ℤ) * R.step i ≡ 0 [ZMOD (q : ℤ)] := by
    intro i _hi
    exact (Int.ModEq.refl (((v i : ℕ) : ℤ))).mul
      (Int.modEq_zero_iff_dvd.mpr (hstep i))
  have hsum := Int.ModEq.sum hterm
  have hadd := (Int.ModEq.refl R.base).add hsum
  simpa [GeneralizedAP.eval] using hadd

/-- The first difference of a GAP, and hence every subsequent iterated
difference, is divisible by every common divisor of the GAP steps. -/
lemma dvd_iteratedDifference_succ_of_dvd_steps
    (R : GeneralizedAP) {q : ℕ}
    (hstep : ∀ i : Fin R.rank, (q : ℤ) ∣ R.step i) :
    ∀ n x, x ∈ iteratedDifference (n + 1) R.carrier → (q : ℤ) ∣ x := by
  intro n
  induction n with
  | zero =>
      intro x hx
      obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_sub.mp hx
      have hab : a ≡ b [ZMOD (q : ℤ)] :=
        (R.carrier_modEq_base_of_dvd_steps hstep ha).trans
          (R.carrier_modEq_base_of_dvd_steps hstep hb).symm
      have hdiv : (q : ℤ) ∣ b - a := hab.dvd
      simpa only [neg_sub] using (dvd_neg.mpr hdiv)
  | succ n ih =>
      intro x hx
      obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_sub.mp hx
      exact dvd_sub (ih a ha) (ih b hb)

end GeneralizedAP

/-- A bounded translate cover by an iterated difference of a GAP bounds the
number of residue classes modulo every common divisor of the GAP steps. -/
lemma usedPositiveResidues_card_le_of_iteratedDifference_cover
    {q n : ℕ} {A : Finset ℕ} {Z : Finset ℤ} (R : GeneralizedAP)
    (hq : 0 < q)
    (hstep : ∀ i : Fin R.rank, (q : ℤ) ∣ R.step i)
    (hcover : natToIntFinset A ⊆
      Z + iteratedDifference (n + 1) R.carrier) :
    (usedPositiveResidues q A).card ≤ Z.card := by
  let Zres := Z.image (positiveIntResidue q)
  have hsub : usedPositiveResidues q A ⊆ Zres := by
    intro g hg
    obtain ⟨a, haA, rfl⟩ := mem_usedPositiveResidues.mp hg
    have haInt : (a : ℤ) ∈ natToIntFinset A :=
      natCast_mem_natToIntFinset.mpr haA
    obtain ⟨z, hz, y, hy, hzy⟩ := Finset.mem_add.mp (hcover haInt)
    have hdy : (q : ℤ) ∣ y :=
      R.dvd_iteratedDifference_succ_of_dvd_steps hstep n y hy
    have hmod : (a : ℤ) ≡ z [ZMOD (q : ℤ)] := by
      rw [Int.modEq_iff_dvd]
      have : (q : ℤ) ∣ -y := dvd_neg.mpr hdy
      convert this using 1 <;> omega
    apply Finset.mem_image.mpr
    exact ⟨z, hz,
      (positiveResidue_eq_positiveIntResidue_of_modEq hq hmod).symm⟩
  calc
    (usedPositiveResidues q A).card ≤ Zres.card := Finset.card_le_card hsub
    _ ≤ Z.card := Finset.card_image_le

/-- Rank-one specialization: the positive step extracted from `positiveForm`
divides every original step, so the bounded translate cover gives the needed
residue-class bound. -/
lemma usedPositiveResidues_card_le_rank_one
    {q n : ℕ} {A : Finset ℕ} {Z : Finset ℤ} (R : GeneralizedAP)
    (hrank : R.rank = 1) (hq : 0 < q)
    (hqstep : (q : ℤ) = R.positiveForm.step
      ⟨0, by simp [GeneralizedAP.rank_positiveForm, hrank]⟩)
    (hcover : natToIntFinset A ⊆
      Z + iteratedDifference (n + 1) R.carrier) :
    (usedPositiveResidues q A).card ≤ Z.card := by
  apply usedPositiveResidues_card_le_of_iteratedDifference_cover R hq
  · intro i
    have hi : i = ⟨0, by simpa [hrank] using i.isLt⟩ := by
      apply Fin.ext
      omega
    subst i
    have hqabs : (q : ℤ) = |R.step ⟨0, by omega⟩| := by
      simpa [GeneralizedAP.positiveForm] using hqstep
    rw [hqabs]
    exact abs_dvd_self _
  · exact hcover

/-- Rank-two specialization with modulus the gcd of the two positive steps. -/
lemma usedPositiveResidues_card_le_rank_two
    {q₁ q₂ n : ℕ} {A : Finset ℕ} {Z : Finset ℤ}
    (R : GeneralizedAP) (hrank : R.rank = 2)
    (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hq₁step : (q₁ : ℤ) = R.positiveForm.step
      ⟨0, by simp [GeneralizedAP.rank_positiveForm, hrank]⟩)
    (hq₂step : (q₂ : ℤ) = R.positiveForm.step
      ⟨1, by simp [GeneralizedAP.rank_positiveForm, hrank]⟩)
    (hcover : natToIntFinset A ⊆
      Z + iteratedDifference (n + 1) R.carrier) :
    (usedPositiveResidues (q₁.gcd q₂) A).card ≤ Z.card := by
  have hg : 0 < q₁.gcd q₂ := Nat.gcd_pos_of_pos_left _ hq₁
  apply usedPositiveResidues_card_le_of_iteratedDifference_cover R hg
  · intro i
    have hi : i.val = 0 ∨ i.val = 1 := by
      have := i.isLt
      omega
    rcases hi with hi | hi
    · have hieq : i = ⟨0, by omega⟩ := Fin.ext hi
      have hqabs : (q₁ : ℤ) = |R.step ⟨0, by omega⟩| := by
        simpa [GeneralizedAP.positiveForm] using hq₁step
      have hgd : ((q₁.gcd q₂ : ℕ) : ℤ) ∣ (q₁ : ℤ) := by
        exact_mod_cast Nat.gcd_dvd_left q₁ q₂
      rw [hqabs] at hgd
      rw [hieq]
      exact hgd.trans (abs_dvd_self _)
    · have hieq : i = ⟨1, by omega⟩ := Fin.ext hi
      have hqabs : (q₂ : ℤ) = |R.step ⟨1, by omega⟩| := by
        simpa [GeneralizedAP.positiveForm] using hq₂step
      have hgd : ((q₁.gcd q₂ : ℕ) : ℤ) ∣ (q₂ : ℤ) := by
        exact_mod_cast Nat.gcd_dvd_right q₁ q₂
      rw [hqabs] at hgd
      rw [hieq]
      exact hgd.trans (abs_dvd_self _)
  · exact hcover

/-- Rank-two cover bound modulo the second step.  Each difference iteration
squares the residue count, and the undifferenced carrier has at most one
residue for each first coordinate. -/
lemma usedPositiveResidues_card_le_rank_two_second_step
    {q₂ n : ℕ} {A : Finset ℕ} {Z : Finset ℤ}
    (R : GeneralizedAP) (hrank : R.rank = 2) (hq₂ : 0 < q₂)
    (hq₂step : (q₂ : ℤ) = R.positiveForm.step
      ⟨1, by simp [GeneralizedAP.rank_positiveForm, hrank]⟩)
    (hcover : natToIntFinset A ⊆
      Z + iteratedDifference (n + 1) R.carrier) :
    (usedPositiveResidues q₂ A).card ≤
      Z.card * (R.length ⟨0, by omega⟩ + 1) ^ (2 ^ (n + 1)) := by
  calc
    (usedPositiveResidues q₂ A).card ≤
        Z.card *
          (intResidues q₂
            (iteratedDifference (n + 1) R.carrier)).card :=
      usedPositiveResidues_card_le_of_add_cover hq₂ hcover
    _ ≤ Z.card * (intResidues q₂ R.carrier).card ^ (2 ^ (n + 1)) :=
      Nat.mul_le_mul_left _
        (intResidues_iteratedDifference_card_le q₂ (n + 1) R.carrier)
    _ ≤ Z.card * (R.length ⟨0, by omega⟩ + 1) ^ (2 ^ (n + 1)) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
        (R.intResidues_carrier_card_le_first_side hrank hq₂step) _)

/-- Symmetric rank-two cover bound modulo the first step. -/
lemma usedPositiveResidues_card_le_rank_two_first_step
    {q₁ n : ℕ} {A : Finset ℕ} {Z : Finset ℤ}
    (R : GeneralizedAP) (hrank : R.rank = 2) (hq₁ : 0 < q₁)
    (hq₁step : (q₁ : ℤ) = R.positiveForm.step
      ⟨0, by simp [GeneralizedAP.rank_positiveForm, hrank]⟩)
    (hcover : natToIntFinset A ⊆
      Z + iteratedDifference (n + 1) R.carrier) :
    (usedPositiveResidues q₁ A).card ≤
      Z.card * (R.length ⟨1, by omega⟩ + 1) ^ (2 ^ (n + 1)) := by
  calc
    (usedPositiveResidues q₁ A).card ≤
        Z.card *
          (intResidues q₁
            (iteratedDifference (n + 1) R.carrier)).card :=
      usedPositiveResidues_card_le_of_add_cover hq₁ hcover
    _ ≤ Z.card * (intResidues q₁ R.carrier).card ^ (2 ^ (n + 1)) :=
      Nat.mul_le_mul_left _
        (intResidues_iteratedDifference_card_le q₁ (n + 1) R.carrier)
    _ ≤ Z.card * (R.length ⟨1, by omega⟩ + 1) ^ (2 ^ (n + 1)) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
        (R.intResidues_carrier_card_le_second_side hrank hq₁step) _)

/-- Sharp linear cover bound modulo the second coordinate step.  The factor
`2^n` depends only on the bounded rank-reduction depth; crucially, the short
side length occurs only to the first power. -/
lemma usedPositiveResidues_card_le_rank_two_second_step_linear
    {q₂ n : ℕ} {A : Finset ℕ} {Z : Finset ℤ}
    (R : GeneralizedAP) (hrank : R.rank = 2) (hq₂ : 0 < q₂)
    (hq₂step : (q₂ : ℤ) = R.positiveForm.step
      ⟨1, by simp [GeneralizedAP.rank_positiveForm, hrank]⟩)
    (hcover : natToIntFinset A ⊆
      Z + iteratedDifference (n + 1) R.carrier) :
    (usedPositiveResidues q₂ A).card ≤
      Z.card * (2 * (2 ^ n * R.length ⟨0, by omega⟩) + 1) := by
  calc
    (usedPositiveResidues q₂ A).card ≤
        Z.card *
          (intResidues q₂
            (iteratedDifference (n + 1) R.carrier)).card :=
      usedPositiveResidues_card_le_of_add_cover hq₂ hcover
    _ ≤ Z.card * (2 * (2 ^ n * R.length ⟨0, by omega⟩) + 1) :=
      Nat.mul_le_mul_left _
        (R.intResidues_iteratedDifference_rank_two_second_step_card_le
          hrank hq₂step)

/-- Symmetric sharp linear cover bound modulo the first coordinate step. -/
lemma usedPositiveResidues_card_le_rank_two_first_step_linear
    {q₁ n : ℕ} {A : Finset ℕ} {Z : Finset ℤ}
    (R : GeneralizedAP) (hrank : R.rank = 2) (hq₁ : 0 < q₁)
    (hq₁step : (q₁ : ℤ) = R.positiveForm.step
      ⟨0, by simp [GeneralizedAP.rank_positiveForm, hrank]⟩)
    (hcover : natToIntFinset A ⊆
      Z + iteratedDifference (n + 1) R.carrier) :
    (usedPositiveResidues q₁ A).card ≤
      Z.card * (2 * (2 ^ n * R.length ⟨1, by omega⟩) + 1) := by
  calc
    (usedPositiveResidues q₁ A).card ≤
        Z.card *
          (intResidues q₁
            (iteratedDifference (n + 1) R.carrier)).card :=
      usedPositiveResidues_card_le_of_add_cover hq₁ hcover
    _ ≤ Z.card * (2 * (2 ^ n * R.length ⟨1, by omega⟩) + 1) :=
      Nat.mul_le_mul_left _
        (R.intResidues_iteratedDifference_rank_two_first_step_card_le
          hrank hq₁step)

/-- Removing all residue fibers of size below `B` costs at most `B` times
the number of used residue classes. -/
lemma card_le_card_largeResiduePart_add
    (q B : ℕ) (A : Finset ℕ) :
    A.card ≤ (largeResiduePart q B A).card +
      (usedPositiveResidues q A).card * B := by
  let small := usedPositiveResidues q A \ largePositiveResidues q B A
  have hcover : A \ largeResiduePart q B A ⊆
      small.biUnion (residueFiber q A) := by
    intro a ha
    have haA : a ∈ A := (Finset.mem_sdiff.mp ha).1
    have haNot := (Finset.mem_sdiff.mp ha).2
    have hresUsed : positiveResidue q a ∈ usedPositiveResidues q A := by
      exact mem_usedPositiveResidues.mpr ⟨a, haA, rfl⟩
    have hresNot : positiveResidue q a ∉ largePositiveResidues q B A := by
      intro hlarge
      exact haNot (mem_largeResiduePart.mpr ⟨haA, hlarge⟩)
    apply Finset.mem_biUnion.mpr
    exact ⟨positiveResidue q a,
      Finset.mem_sdiff.mpr ⟨hresUsed, hresNot⟩,
      mem_residueFiber.mpr ⟨haA, rfl⟩⟩
  have hfiber (g : ℕ) (hg : g ∈ small) :
      (residueFiber q A g).card ≤ B := by
    have hgNot : g ∉ largePositiveResidues q B A :=
      (Finset.mem_sdiff.mp hg).2
    have hgUsed : g ∈ usedPositiveResidues q A :=
      (Finset.mem_sdiff.mp hg).1
    have : ¬ B ≤ (residueFiber q A g).card := by
      intro hB
      exact hgNot (mem_largePositiveResidues.mpr ⟨hgUsed, hB⟩)
    omega
  have hsmallCard : (A \ largeResiduePart q B A).card ≤
      (usedPositiveResidues q A).card * B := by
    calc
      (A \ largeResiduePart q B A).card ≤
          (small.biUnion (residueFiber q A)).card :=
        Finset.card_le_card hcover
      _ ≤ ∑ g ∈ small, (residueFiber q A g).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _g ∈ small, B := by
        apply Finset.sum_le_sum
        intro g hg
        exact hfiber g hg
      _ = small.card * B := by simp
      _ ≤ (usedPositiveResidues q A).card * B := by
        apply Nat.mul_le_mul_right
        exact Finset.card_le_card (Finset.sdiff_subset)
  rw [← Finset.card_sdiff_add_card_eq_card
    (largeResiduePart_subset q B A)]
  omega

lemma largeResidues_forall₂_fiber_bound
    {q B : ℕ} {A : Finset ℕ} {values : List ℕ}
    (hlen : values.length = (largePositiveResidues q B A).toList.length)
    (hvalues : ∀ x ∈ values, x ≤ B) :
    List.Forall₂
      (fun g x ↦ x ≤ (residueFiber q A g).card)
      (largePositiveResidues q B A).toList values := by
  apply List.forall₂_iff_get.mpr
  refine ⟨hlen.symm, ?_⟩
  intro i hi hj
  have hg : (largePositiveResidues q B A).toList[i] ∈
      largePositiveResidues q B A := by
    exact Finset.mem_toList.mp (List.getElem_mem hi)
  exact (hvalues values[i] (List.getElem_mem hj)).trans
    (mem_largePositiveResidues.mp hg).2

/-- The finite Nguyen--Vu residue trichotomy.  The constant `Q` is the
uniform constant from the repaired one-variable quadratic congruence lemma.
If at most `C` positive residue classes occur modulo `q`, then either a
subset adjusts `r` to `p` times a square, or after discarding at most
`C * B` elements all remaining elements share a prime divisor of `q`, where
`B = log₂(q) * Q * (sqrt(pq)+1)`. -/
theorem exists_quadratic_adjustment_or_large_common_divisor_with_card :
    ∃ Q : ℕ, ∀ {p q r C : ℕ} (A : Finset ℕ),
      0 < p → 0 < q →
      (usedPositiveResidues q A).card ≤ C →
      ( (∃ T ⊆ A,
          T.card ≤ C *
            (Nat.log 2 q * (Q * (Nat.sqrt (p * q) + 1))) ∧
          ∃ z : ℤ,
          ((r + ∑ a ∈ T, a : ℕ) : ℤ) ≡
            (p : ℤ) * z ^ 2 [ZMOD (q : ℤ)]) ∨
        ∃ d : ℕ, ∃ D : Finset ℕ,
          D ⊆ A ∧ 1 < d ∧ d ∣ q ∧
          A.card ≤ D.card +
            C * (Nat.log 2 q * (Q * (Nat.sqrt (p * q) + 1))) ∧
          ∀ a ∈ D, d ∣ a ) := by
  obtain ⟨Q, hQ⟩ := exists_bounded_quadratic_congruence_primitive
  refine ⟨Q, ?_⟩
  intro p q r C A hp hq hresCard
  let B := Nat.log 2 q * (Q * (Nat.sqrt (p * q) + 1))
  let R := largePositiveResidues q B A
  let D := largeResiduePart q B A
  let coeff := R.toList
  have hcoeffNodup : coeff.Nodup := by
    exact R.nodup_toList
  have hcoeffPos : ∀ g ∈ coeff, 0 < g := by
    intro g hg
    have hgR : g ∈ R := by simpa [coeff] using hg
    obtain ⟨a, haA, hga⟩ :=
      mem_usedPositiveResidues.mp
        (mem_largePositiveResidues.mp (by simpa [R] using hgR)).1
    rw [← hga]
    exact positiveResidue_pos hq
  by_cases hprim : NVPrimitiveCoefficients coeff q
  · left
    obtain ⟨values, hlen, hvalues, z, hz⟩ :=
      hQ coeff (r : ℤ) hp hq hcoeffNodup hcoeffPos hprim
    have hfb : List.Forall₂
        (fun g x ↦ x ≤ (residueFiber q A g).card) coeff values := by
      apply largeResidues_forall₂_fiber_bound
      · simpa [coeff, R] using hlen
      · simpa [B] using hvalues
    obtain ⟨T, hTA, _hTres, hTcard, hTmod⟩ :=
      exists_subset_sum_modEq_nvListDot_of_residue_fibers_with_card
        A coeff values hcoeffNodup hfb
    have hRcard : R.card ≤ C := by
      calc
        R.card ≤ (usedPositiveResidues q A).card := by
          apply Finset.card_le_card
          exact Finset.filter_subset _ _
        _ ≤ C := hresCard
    have hvalueSum : values.sum ≤ C * B := by
      calc
        values.sum ≤ values.length * B := by
          simpa using List.sum_le_card_nsmul values B hvalues
        _ = R.card * B := by rw [hlen]; simp [coeff]
        _ ≤ C * B := Nat.mul_le_mul_right B hRcard
    refine ⟨T, hTA, ?_, z, ?_⟩
    · simpa [B, hTcard] using hvalueSum
    have hadd := (Int.ModEq.refl (r : ℤ)).add hTmod
    have hrt : (r : ℤ) + ((∑ a ∈ T, a : ℕ) : ℤ) ≡
        (r : ℤ) + nvListDot coeff values [ZMOD (q : ℤ)] := hadd
    calc
      ((r + ∑ a ∈ T, a : ℕ) : ℤ) ≡
          (r : ℤ) + nvListDot coeff values [ZMOD (q : ℤ)] := by
        simpa only [Nat.cast_add] using hrt
      _ ≡ nvListDot coeff values + (r : ℤ) [ZMOD (q : ℤ)] := by
        simp [add_comm]
      _ ≡ (p : ℤ) * z ^ 2 [ZMOD (q : ℤ)] := hz
  · right
    rw [NVPrimitiveCoefficients] at hprim
    push Not at hprim
    obtain ⟨d, hdq, hdall⟩ := hprim
    have hdprime : d.Prime := Nat.prime_of_mem_primeFactors hdq
    have hdvdq : d ∣ q := Nat.dvd_of_mem_primeFactors hdq
    refine ⟨d, D, largeResiduePart_subset q B A,
      hdprime.one_lt, hdvdq, ?_, ?_⟩
    · calc
        A.card ≤ D.card + (usedPositiveResidues q A).card * B := by
          simpa [D] using card_le_card_largeResiduePart_add q B A
        _ ≤ D.card + C * B := Nat.add_le_add_left
          (Nat.mul_le_mul_right B hresCard) D.card
        _ = D.card +
            C * (Nat.log 2 q * (Q * (Nat.sqrt (p * q) + 1))) := by rfl
    · intro a haD
      have ha := mem_largeResiduePart.mp (by simpa [D] using haD)
      have hgCoeff : positiveResidue q a ∈ coeff := by
        simpa [coeff, R] using ha.2
      have hdg : d ∣ positiveResidue q a := hdall _ hgCoeff
      have hmod : a ≡ positiveResidue q a [MOD d] :=
        (positiveResidue_modEq q a).of_dvd hdvdq
      apply Nat.dvd_iff_mod_eq_zero.mpr
      rw [hmod]
      exact Nat.mod_eq_zero_of_dvd hdg

/-- The cardinality-free public form of the finite Nguyen--Vu residue
trichotomy. -/
theorem exists_quadratic_adjustment_or_large_common_divisor :
    ∃ Q : ℕ, ∀ {p q r C : ℕ} (A : Finset ℕ),
      0 < p → 0 < q →
      (usedPositiveResidues q A).card ≤ C →
      ( (∃ T ⊆ A, ∃ z : ℤ,
          ((r + ∑ a ∈ T, a : ℕ) : ℤ) ≡
            (p : ℤ) * z ^ 2 [ZMOD (q : ℤ)]) ∨
        ∃ d : ℕ, ∃ D : Finset ℕ,
          D ⊆ A ∧ 1 < d ∧ d ∣ q ∧
          A.card ≤ D.card +
            C * (Nat.log 2 q * (Q * (Nat.sqrt (p * q) + 1))) ∧
          ∀ a ∈ D, d ∣ a ) := by
  obtain ⟨Q, hQ⟩ :=
    exists_quadratic_adjustment_or_large_common_divisor_with_card
  refine ⟨Q, ?_⟩
  intro p q r C A hp hq hres
  rcases hQ A hp hq hres with
    ⟨T, hTA, _hTcard, z, hz⟩ | hdiv
  · exact Or.inl ⟨T, hTA, z, hz⟩
  · exact Or.inr hdiv

end Erdos587
