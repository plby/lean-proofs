/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos360.StructuredPhaseCoordinates
import ErdosProblems.Erdos360.NormalizedFiberSelector

/-!
# Canonical coordinates for a generated cyclic subgroup

The arbitrary cyclic equivalence used by a normalized fibre need not retain
the arithmetic meaning of an integer pivot.  Here the chosen generator is
the literal `closureModulus`; its inverse coordinate of a pivot `p` is
therefore exactly `p / closureModulus`.  This is the coordinate system used
by the structured sieve phases.
-/

namespace Erdos360

attribute [local instance] Classical.propDecidable

noncomputable def closureGenerator
    {t : ℕ} [NeZero t] (ht : 0 < t) (R : Finset (ZMod t)) :
    AddSubgroup.closure ((R : Finset (ZMod t)) : Set (ZMod t)) :=
  ⟨(closureModulus ht R : ZMod t), by
    simpa using (closureModulus_spec ht R).2.2.2 1⟩

lemma closureGenerator_generates
    {t : ℕ} [NeZero t] (ht : 0 < t) (R : Finset (ZMod t)) :
    ∀ x : AddSubgroup.closure ((R : Finset (ZMod t)) : Set (ZMod t)),
      x ∈ AddSubgroup.zmultiples (closureGenerator ht R) := by
  intro x
  rw [AddSubgroup.mem_zmultiples_iff]
  have hx : x.1 ∈ AddSubgroup.zmultiples (closureModulus ht R : ZMod t) := by
    rw [← closure_eq_zmultiples_modulus ht R]
    exact x.2
  rw [AddSubgroup.mem_zmultiples_iff] at hx
  obtain ⟨i, hi⟩ := hx
  refine ⟨i, Subtype.ext ?_⟩
  simpa [closureGenerator] using hi

/-- The cyclic equivalence which sends `1` to the literal closure modulus. -/
noncomputable def closureZModEquiv
    {t : ℕ} [NeZero t] (ht : 0 < t) (R : Finset (ZMod t)) :
    ZMod (Nat.card (AddSubgroup.closure
      ((R : Finset (ZMod t)) : Set (ZMod t)))) ≃+
      AddSubgroup.closure ((R : Finset (ZMod t)) : Set (ZMod t)) :=
  zmodAddEquivOfGenerator (closureGenerator_generates ht R) rfl

lemma natCard_closure_eq_div_modulus
    {t : ℕ} [NeZero t] (ht : 0 < t) (R : Finset (ZMod t)) :
    Nat.card (AddSubgroup.closure ((R : Finset (ZMod t)) : Set (ZMod t))) =
      t / closureModulus ht R := by
  rw [Nat.card_eq_fintype_card]
  rw [show Fintype.card (AddSubgroup.closure
      ((R : Finset (ZMod t)) : Set (ZMod t))) =
      (AddSubgroup.closure ((R : Finset (ZMod t)) : Set (ZMod t)) :
        Set (ZMod t)).ncard by
    exact Set.fintypeCard_eq_ncard _]
  exact ncard_closure_eq_div_modulus ht R

/-- A lifted ordinary pivot has its literal divided value as canonical
closure coordinate. -/
lemma closureZModEquiv_symm_lift
    {t : ℕ} [NeZero t] (ht : 0 < t) {P : Finset ℕ}
    (hPt : ∀ p ∈ P, p < t) {p : ℕ} (hp : p ∈ P) :
    let R := ordinaryResidues t P
    let H := AddSubgroup.closure ((R : Finset (ZMod t)) : Set (ZMod t))
    (closureZModEquiv ht R).symm
      (⟨(p : ZMod t), AddSubgroup.subset_closure
        (Finset.mem_image.mpr ⟨p, hp, rfl⟩)⟩ : H) =
      ((p / closureModulus ht R : ℕ) : ZMod (Nat.card H)) := by
  dsimp only
  let R := ordinaryResidues t P
  let g := closureGenerator ht R
  have hqp : closureModulus ht R ∣ p :=
    closureModulus_dvd_of_mem_ordinary ht hPt hp
  have hEq :
      (⟨(p : ZMod t), AddSubgroup.subset_closure
        (Finset.mem_image.mpr ⟨p, hp, rfl⟩)⟩ :
        AddSubgroup.closure ((R : Finset (ZMod t)) : Set (ZMod t))) =
      (p / closureModulus ht R : ℕ) • g := by
    apply Subtype.ext
    dsimp [g, closureGenerator]
    rw [nsmul_eq_mul, ← Nat.cast_mul]
    rw [Nat.div_mul_cancel hqp]
  rw [hEq, map_nsmul]
  change (p / closureModulus ht R : ℕ) •
      (zmodAddEquivOfGenerator
        (closureGenerator_generates ht R) rfl).symm g = _
  rw [zmodAddEquivOfGenerator_symm_apply_generator]
  simp [R]

/-- The closure modulus divides an arbitrary integer representative of a
member of `ordinaryResidues`.  No size condition is needed because the
closure modulus also divides the ambient modulus. -/
lemma closureModulus_dvd_of_mem_ordinary_any
    {t : ℕ} [NeZero t] (ht : 0 < t) {P : Finset ℕ}
    {p : ℕ} (hp : p ∈ P) :
    closureModulus ht (ordinaryResidues t P) ∣ p := by
  let R := ordinaryResidues t P
  let q := closureModulus ht R
  have hpR : (p : ZMod t) ∈ R :=
    Finset.mem_image.mpr ⟨p, hp, rfl⟩
  have hqval : q ∣ (p : ZMod t).val :=
    (closureModulus_spec ht R).2.2.1 _
      (AddSubgroup.subset_closure hpR)
  have hqt : q ∣ t := closureModulus_dvd ht R
  simpa [q, R, ZMod.val_natCast, Nat.dvd_mod_iff hqt] using hqval

/-- Canonical closure coordinates are literal quotients even when the
chosen integer representatives lie outside `[0,t)`. -/
lemma closureZModEquiv_symm_lift_any
    {t : ℕ} [NeZero t] (ht : 0 < t) {P : Finset ℕ}
    {p : ℕ} (hp : p ∈ P) :
    let R := ordinaryResidues t P
    let H := AddSubgroup.closure ((R : Finset (ZMod t)) : Set (ZMod t))
    (closureZModEquiv ht R).symm
      (⟨(p : ZMod t), AddSubgroup.subset_closure
        (Finset.mem_image.mpr ⟨p, hp, rfl⟩)⟩ : H) =
      ((p / closureModulus ht R : ℕ) : ZMod (Nat.card H)) := by
  dsimp only
  let R := ordinaryResidues t P
  let g := closureGenerator ht R
  have hqp : closureModulus ht R ∣ p :=
    closureModulus_dvd_of_mem_ordinary_any ht hp
  have hEq :
      (⟨(p : ZMod t), AddSubgroup.subset_closure
        (Finset.mem_image.mpr ⟨p, hp, rfl⟩)⟩ :
        AddSubgroup.closure ((R : Finset (ZMod t)) : Set (ZMod t))) =
      (p / closureModulus ht R : ℕ) • g := by
    apply Subtype.ext
    dsimp [g, closureGenerator]
    rw [nsmul_eq_mul, ← Nat.cast_mul]
    rw [Nat.div_mul_cancel hqp]
  rw [hEq, map_nsmul]
  change (p / closureModulus ht R : ℕ) •
      (zmodAddEquivOfGenerator
        (closureGenerator_generates ht R) rfl).symm g = _
  rw [zmodAddEquivOfGenerator_symm_apply_generator]
  simp [R]

/-- Setwise version of the preceding unrestricted coordinate formula. -/
theorem equivCoordinates_closure_lift_ordinary_any
    {t : ℕ} [NeZero t] (ht : 0 < t) (P : Finset ℕ) :
    let R := ordinaryResidues t P
    let H := AddSubgroup.closure ((R : Finset (ZMod t)) : Set (ZMod t))
    equivCoordinates (closureZModEquiv ht R) (liftFinsetToClosure R) =
      P.image (fun p ↦
        ((p / closureModulus ht R : ℕ) : ZMod (Nat.card H))) := by
  dsimp only
  let R := ordinaryResidues t P
  let H := AddSubgroup.closure ((R : Finset (ZMod t)) : Set (ZMod t))
  ext z
  constructor
  · intro hz
    have hzX := mem_equivCoordinates_iff.mp hz
    have hzR : (closureZModEquiv ht R z).1 ∈ R :=
      mem_liftFinsetToClosure.mp hzX
    obtain ⟨p, hp, hep⟩ := Finset.mem_image.mp hzR
    apply Finset.mem_image.mpr
    refine ⟨p, hp, ?_⟩
    have heq : closureZModEquiv ht R z =
        (⟨(p : ZMod t), AddSubgroup.subset_closure
          (Finset.mem_image.mpr ⟨p, hp, rfl⟩)⟩ : H) := by
      apply Subtype.ext
      simpa [R] using hep.symm
    rw [← closureZModEquiv_symm_lift_any ht hp]
    simpa [H, R] using (congrArg (closureZModEquiv ht R).symm heq).symm
  · intro hz
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
    apply mem_equivCoordinates_iff.mpr
    have heq := closureZModEquiv_symm_lift_any ht hp
    have heq' : closureZModEquiv ht R
        ((p / closureModulus ht R : ℕ) : ZMod (Nat.card H)) =
        (⟨(p : ZMod t), AddSubgroup.subset_closure
          (Finset.mem_image.mpr ⟨p, hp, rfl⟩)⟩ : H) := by
      have := congrArg (closureZModEquiv ht R) heq
      simpa [H, R] using this.symm
    rw [heq']
    exact mem_liftFinsetToClosure.mpr
      (Finset.mem_image.mpr ⟨p, hp, rfl⟩)

/-- If the original representatives lie in `[lo,lo+t)`, choosing
`ceil(lo/q)` as the interval base recovers their literal quotients by the
closure modulus `q`. -/
theorem interval_equivCoordinates_closure_lift_ordinary
    {t lo : ℕ} [NeZero t] (ht : 0 < t) (P : Finset ℕ)
    (hloT : lo ≤ t) (hlo : ∀ p ∈ P, lo ≤ p)
    (hhi : ∀ p ∈ P, p < lo + t) :
    let R := ordinaryResidues t P
    let H := AddSubgroup.closure ((R : Finset (ZMod t)) : Set (ZMod t))
    let q := closureModulus ht R
    intervalZmodValues (lo ⌈/⌉ q)
        (equivCoordinates (closureZModEquiv ht R) (liftFinsetToClosure R)) =
      P.image fun p ↦ p / q := by
  dsimp only
  let R := ordinaryResidues t P
  let H := AddSubgroup.closure ((R : Finset (ZMod t)) : Set (ZMod t))
  let q := closureModulus ht R
  have hq : 0 < q := closureModulus_pos ht R
  have hqt : q ∣ t := closureModulus_dvd ht R
  have hcard : Nat.card H = t / q := by
    simpa [H, q] using natCard_closure_eq_div_modulus ht R
  rw [equivCoordinates_closure_lift_ordinary_any ht P]
  simpa only [Finset.image_image, Function.comp_def] using
    (intervalZmodValues_image_natCast
      (m := Nat.card H) (base := lo ⌈/⌉ q) (P.image fun p ↦ p / q)
      (by
        intro x hx
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
        apply (ceilDiv_le_iff_le_mul hq).2
        rw [Nat.mul_div_cancel' (closureModulus_dvd_of_mem_ordinary_any ht hp)]
        exact hlo p hp)
      (by
        intro x hx
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
        rw [hcard]
        rw [← Nat.mul_lt_mul_left hq]
        have hbase : lo ≤ q * (lo ⌈/⌉ q) :=
          le_smul_ceilDiv hq
        rw [Nat.mul_add,
          Nat.mul_div_cancel' (closureModulus_dvd_of_mem_ordinary_any ht hp),
          Nat.mul_div_cancel' hqt]
        exact (hhi p hp).trans_le (Nat.add_le_add_right hbase t)))

lemma ceilDiv_closureModulus_le_card
    {t lo : ℕ} [NeZero t] (ht : 0 < t) (R : Finset (ZMod t))
    (hlo : lo ≤ t) :
    lo ⌈/⌉ closureModulus ht R ≤
      Nat.card (AddSubgroup.closure ((R : Finset (ZMod t)) : Set (ZMod t))) := by
  rw [natCard_closure_eq_div_modulus ht R]
  apply (ceilDiv_le_iff_le_mul (closureModulus_pos ht R)).2
  rw [Nat.mul_div_cancel' (closureModulus_dvd ht R)]
  exact hlo

/-- Coprimality of an arbitrary short interval of integer representatives
passes to the matching interval representatives of the canonical closure
coordinates. -/
theorem interval_equivCoordinates_closure_coprime_any
    {t lo M : ℕ} [NeZero t] (ht : 0 < t) (P : Finset ℕ)
    (hloT : lo ≤ t) (hlo : ∀ p ∈ P, lo ≤ p)
    (hhi : ∀ p ∈ P, p < lo + t)
    (hcop : ∀ p ∈ P, Nat.Coprime M p) :
    let R := ordinaryResidues t P
    let H := AddSubgroup.closure ((R : Finset (ZMod t)) : Set (ZMod t))
    let q := closureModulus ht R
    ∀ x ∈ intervalZmodValues (lo ⌈/⌉ q)
      (equivCoordinates (closureZModEquiv ht R) (liftFinsetToClosure R)),
      Nat.Coprime M x := by
  dsimp only
  let R := ordinaryResidues t P
  let q := closureModulus ht R
  rw [interval_equivCoordinates_closure_lift_ordinary ht P hloT hlo hhi]
  intro x hx
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
  exact Nat.Coprime.of_dvd_right
    (div_dvd_self_of_pos_of_dvd (closureModulus_pos ht R)
      (closureModulus_dvd_of_mem_ordinary_any ht hp)) (hcop p hp)

/-- The canonical coordinates of a lifted integer residue set are precisely
the literal divided residues. -/
theorem equivCoordinates_closure_lift_ordinary
    {t : ℕ} [NeZero t] (ht : 0 < t) {P : Finset ℕ}
    (hPt : ∀ p ∈ P, p < t) :
    let R := ordinaryResidues t P
    let H := AddSubgroup.closure ((R : Finset (ZMod t)) : Set (ZMod t))
    equivCoordinates (closureZModEquiv ht R) (liftFinsetToClosure R) =
      P.image (fun p ↦
        ((p / closureModulus ht R : ℕ) : ZMod (Nat.card H))) := by
  dsimp only
  let R := ordinaryResidues t P
  let H := AddSubgroup.closure ((R : Finset (ZMod t)) : Set (ZMod t))
  ext z
  constructor
  · intro hz
    have hzX := mem_equivCoordinates_iff.mp hz
    have hzR : (closureZModEquiv ht R z).1 ∈ R :=
      mem_liftFinsetToClosure.mp hzX
    obtain ⟨p, hp, hep⟩ := Finset.mem_image.mp hzR
    apply Finset.mem_image.mpr
    refine ⟨p, hp, ?_⟩
    have heq : closureZModEquiv ht R z =
        (⟨(p : ZMod t), AddSubgroup.subset_closure
          (Finset.mem_image.mpr ⟨p, hp, rfl⟩)⟩ : H) := by
      apply Subtype.ext
      simpa [R] using hep.symm
    rw [← closureZModEquiv_symm_lift ht hPt hp]
    simpa [H, R] using (congrArg (closureZModEquiv ht R).symm heq).symm
  · intro hz
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
    apply mem_equivCoordinates_iff.mpr
    have heq := closureZModEquiv_symm_lift ht hPt hp
    have heq' : closureZModEquiv ht R
        ((p / closureModulus ht R : ℕ) : ZMod (Nat.card H)) =
        (⟨(p : ZMod t), AddSubgroup.subset_closure
          (Finset.mem_image.mpr ⟨p, hp, rfl⟩)⟩ : H) := by
      have := congrArg (closureZModEquiv ht R) heq
      simpa [H, R] using this.symm
    rw [heq']
    exact mem_liftFinsetToClosure.mpr
      (Finset.mem_image.mpr ⟨p, hp, rfl⟩)

/-- Base-zero interval representatives of canonical closure coordinates
inherit every coprimality property of the original integer pivots. -/
theorem interval_equivCoordinates_closure_coprime
    {t M : ℕ} [NeZero t] (ht : 0 < t) {P : Finset ℕ}
    (hPt : ∀ p ∈ P, p < t)
    (hcop : ∀ p ∈ P, Nat.Coprime M p) :
    let R := ordinaryResidues t P
    let H := AddSubgroup.closure ((R : Finset (ZMod t)) : Set (ZMod t))
    ∀ x ∈ intervalZmodValues 0
      (equivCoordinates (closureZModEquiv ht R) (liftFinsetToClosure R)),
      Nat.Coprime M x := by
  dsimp only
  let R := ordinaryResidues t P
  let H := AddSubgroup.closure ((R : Finset (ZMod t)) : Set (ZMod t))
  let q := closureModulus ht R
  have hcard : Nat.card H = t / q := by
    simpa [H, q] using natCard_closure_eq_div_modulus ht R
  have hcoords := equivCoordinates_closure_lift_ordinary ht hPt
  dsimp only at hcoords
  have hquot : ∀ p ∈ P, p / q < Nat.card H := by
    intro p hp
    rw [hcard]
    exact div_closureModulus_lt_closureQuotient ht hPt hp
  have hinter : intervalZmodValues 0
      (P.image (fun p ↦ ((p / q : ℕ) : ZMod (Nat.card H)))) =
      P.image (fun p ↦ p / q) := by
    simpa only [Finset.image_image, Function.comp_def] using
      (intervalZmodValues_image_natCast
        (m := Nat.card H) (base := 0) (P.image fun p ↦ p / q)
        (fun _ _ ↦ Nat.zero_le _)
        (by
          intro x hx
          obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
          simpa using hquot p hp))
  rw [hcoords, hinter]
  intro x hx
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
  exact coprime_div_of_coprime_of_dvd
    (closureModulus_pos ht R)
    (closureModulus_dvd_of_mem_ordinary ht hPt hp) (hcop p hp)

end Erdos360

#print axioms Erdos360.interval_equivCoordinates_closure_coprime
