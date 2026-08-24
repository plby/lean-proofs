import ErdosProblems.Erdos587.CyclicGapLift

/-! Elementary GAP presentations, independent of the analytic square-location inputs. -/

open scoped BigOperators Pointwise

namespace Erdos587

/-! ## Generalized arithmetic progressions -/

/-- An affine generalized arithmetic progression in `ℤ`, presented by a
finite box of coefficients. -/
structure GeneralizedAP where
  rank : ℕ
  base : ℤ
  step : Fin rank → ℤ
  length : Fin rank → ℕ

namespace GeneralizedAP

/-- Corresponding coordinate steps of `R` are integer multiples of those of
`Q`; the value-based formulation avoids carrying casts between equal ranks. -/
def StepsCoordinatewiseMultiples (R Q : GeneralizedAP) : Prop :=
  ∀ i : Fin R.rank, ∀ j : Fin Q.rank, i.val = j.val →
    ∃ a : ℤ, R.step i = a * Q.step j

/-- Corresponding side lengths of `R` are bounded by `t` times those of
`Q`.  This is the quantitative compatibility used in Nguyen--Vu's
standardization of the progressions produced from stopped pieces. -/
def SideLengthsBoundedBy (R Q : GeneralizedAP) (t : ℕ) : Prop :=
  ∀ i : Fin R.rank, ∀ j : Fin Q.rank, i.val = j.val →
    R.length i ≤ t * Q.length j

/-- On a nondegenerate output coordinate, the full excursion of the
corresponding generator is bounded by the coordinate range of the source
sumset.  Recording the product with the output side length is essential:
after common-side truncation it gives Nguyen--Vu's multiplier bound depending
only on the density parameters, rather than on the ambient side length. -/
def NondegenerateStepMultipliersBoundedBy
    (R Q : GeneralizedAP) (t : ℕ) : Prop :=
  ∀ i : Fin R.rank, ∀ j : Fin Q.rank, i.val = j.val →
    0 < R.length i →
      ∃ a : ℤ, R.step i = a * Q.step j ∧
        |(R.length i : ℤ) * a| ≤ ((t * Q.length j : ℕ) : ℤ)

/-- Bounded coordinatewise multiplier relation with no nondegeneracy
qualification.  Standardized GAPs satisfy this because collapsed
coordinates have been assigned the zero generator. -/
def StepMultipliersBoundedBy (R Q : GeneralizedAP) (t : ℕ) : Prop :=
  ∀ i : Fin R.rank, ∀ j : Fin Q.rank, i.val = j.val →
    ∃ a : ℤ, R.step i = a * Q.step j ∧
      |a| ≤ ((t * Q.length j : ℕ) : ℤ)

/-- Coordinatewise multiplier bound by one global constant.  This is the
quantitative form actually used in Nguyen--Vu Section 5.2: after common-side
truncation only finitely many patterns depending on the density parameters
remain, independently of the ambient GAP side lengths. -/
def StepMultipliersBoundedByConstant
    (R Q : GeneralizedAP) (B : ℕ) : Prop :=
  ∀ i : Fin R.rank, ∀ j : Fin Q.rank, i.val = j.val →
    ∃ a : ℤ, R.step i = a * Q.step j ∧ |a| ≤ (B : ℤ)

/-- The common integer-GAP presentation constructed by the cyclic-model
lifting module, viewed as the GAP type used by the Nguyen--Vu properization
machinery below. -/
def ofInteger (P : IntegerGeneralizedAP) : GeneralizedAP where
  rank := P.rank
  base := P.base
  step := P.step
  length := P.length

/-- Coefficient vectors in the defining box. -/
abbrev Param (Q : GeneralizedAP) := (i : Fin Q.rank) → Fin (Q.length i + 1)

/-- Evaluation of a coefficient vector. -/
def eval (Q : GeneralizedAP) (x : Q.Param) : ℤ :=
  Q.base + ∑ i : Fin Q.rank, (x i : ℤ) * Q.step i

/-- The finite carrier of a GAP. -/
def carrier (Q : GeneralizedAP) : Finset ℤ :=
  (Finset.univ : Finset Q.Param).image Q.eval

/-- A GAP is proper when its coefficient map is injective. -/
def Proper (Q : GeneralizedAP) : Prop := Function.Injective Q.eval

@[simp] lemma rank_ofInteger (P : IntegerGeneralizedAP) :
    (ofInteger P).rank = P.rank := rfl

@[simp] lemma eval_ofInteger (P : IntegerGeneralizedAP) (x : P.Param) :
    (ofInteger P).eval x = P.eval x := rfl

@[simp] lemma carrier_ofInteger (P : IntegerGeneralizedAP) :
    (ofInteger P).carrier = P.carrier := rfl

@[simp] lemma proper_ofInteger (P : IntegerGeneralizedAP) :
    (ofInteger P).Proper ↔ P.Proper := Iff.rfl

lemma mem_carrier_iff (Q : GeneralizedAP) {z : ℤ} :
    z ∈ Q.carrier ↔ ∃ x : Q.Param, Q.eval x = z := by
  simp [carrier]

/-- A proper GAP has the cardinality of its coefficient box. -/
lemma card_carrier_of_proper (Q : GeneralizedAP) (hQ : Q.Proper) :
    Q.carrier.card = ∏ i : Fin Q.rank, (Q.length i + 1) := by
  rw [carrier, Finset.card_image_of_injective (Finset.univ : Finset Q.Param) hQ,
    Finset.card_univ]
  simp [Param]

/-- The indices of the noncollapsed coordinates of a GAP. -/
abbrev PositiveSide (P : GeneralizedAP) :=
  {i : Fin P.rank // 0 < P.length i}

/-- Delete all zero-length coordinates of a GAP.  This operation changes
only the presentation: its carrier is exactly the original carrier. -/
noncomputable def trimZeroSides (P : GeneralizedAP) : GeneralizedAP where
  rank := Fintype.card (PositiveSide P)
  base := P.base
  step j := P.step ((Fintype.equivFin (PositiveSide P)).symm j).1
  length j := P.length ((Fintype.equivFin (PositiveSide P)).symm j).1

lemma trimZeroSides_length_pos (P : GeneralizedAP)
    (j : Fin (P.trimZeroSides.rank)) : 0 < P.trimZeroSides.length j := by
  exact ((Fintype.equivFin (PositiveSide P)).symm j).2

/-- Extend a parameter of the trimmed GAP by zero on every collapsed
coordinate. -/
noncomputable def liftTrimParam (P : GeneralizedAP)
    (x : P.trimZeroSides.Param) : P.Param := fun i =>
  if hi : 0 < P.length i then
    ⟨x (Fintype.equivFin (PositiveSide P) ⟨i, hi⟩), by
      have hx := (x (Fintype.equivFin (PositiveSide P) ⟨i, hi⟩)).isLt
      simpa [trimZeroSides] using hx⟩
  else 0

/-- Restrict an original parameter to the noncollapsed coordinates. -/
noncomputable def projectTrimParam (P : GeneralizedAP)
    (x : P.Param) : P.trimZeroSides.Param := fun j =>
  ⟨x ((Fintype.equivFin (PositiveSide P)).symm j).1, by
    have hx := (x ((Fintype.equivFin (PositiveSide P)).symm j).1).isLt
    simpa [trimZeroSides] using hx⟩

lemma liftTrimParam_apply_pos (P : GeneralizedAP)
    (x : P.trimZeroSides.Param) (i : Fin P.rank) (hi : 0 < P.length i) :
    (P.liftTrimParam x i : ℕ) =
      (x (Fintype.equivFin (PositiveSide P) ⟨i, hi⟩) : ℕ) := by
  simp [liftTrimParam, hi]

lemma liftTrimParam_apply_zero (P : GeneralizedAP)
    (x : P.trimZeroSides.Param) (i : Fin P.rank) (hi : P.length i = 0) :
    (P.liftTrimParam x i : ℕ) = 0 := by
  simp [liftTrimParam, hi]

lemma eval_liftTrimParam (P : GeneralizedAP)
    (x : P.trimZeroSides.Param) :
    P.eval (P.liftTrimParam x) = P.trimZeroSides.eval x := by
  change P.base + (∑ i : Fin P.rank,
      ((P.liftTrimParam x i : ℕ) : ℤ) * P.step i) =
    P.base + (∑ j : Fin (Fintype.card (PositiveSide P)),
      ((x j : ℕ) : ℤ) *
        P.step ((Fintype.equivFin (PositiveSide P)).symm j).1)
  apply congrArg (P.base + ·)
  let f : Fin P.rank → ℤ := fun i =>
    ((P.liftTrimParam x i : ℕ) : ℤ) * P.step i
  have hfilter : (∑ i : Fin P.rank, f i) =
      ∑ i ∈ (Finset.univ.filter fun i : Fin P.rank => 0 < P.length i),
        f i := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _hi
    by_cases hi : 0 < P.length i
    · simp [hi]
    · have hzero : P.length i = 0 := by omega
      simp [hi, f, liftTrimParam_apply_zero P x i hzero]
  rw [show (∑ i : Fin P.rank,
      ((P.liftTrimParam x i : ℕ) : ℤ) * P.step i) =
      ∑ i : Fin P.rank, f i by rfl, hfilter]
  rw [Finset.sum_subtype (p := fun i : Fin P.rank => 0 < P.length i)
    (Finset.univ.filter fun i : Fin P.rank => 0 < P.length i)
    (by simp) f]
  rw [← Equiv.sum_comp (Fintype.equivFin (PositiveSide P)).symm]
  apply Finset.sum_congr rfl
  intro j _hj
  dsimp only [f]
  rw [liftTrimParam_apply_pos P x
    ((Fintype.equivFin (PositiveSide P)).symm j).1
    ((Fintype.equivFin (PositiveSide P)).symm j).2]
  have hsub : (⟨((Fintype.equivFin (PositiveSide P)).symm j).1,
      ((Fintype.equivFin (PositiveSide P)).symm j).2⟩ : PositiveSide P) =
      (Fintype.equivFin (PositiveSide P)).symm j := Subtype.ext rfl
  rw [hsub, Equiv.apply_symm_apply]

lemma eval_projectTrimParam (P : GeneralizedAP) (x : P.Param) :
    P.trimZeroSides.eval (P.projectTrimParam x) = P.eval x := by
  rw [← P.eval_liftTrimParam (P.projectTrimParam x)]
  apply congrArg P.eval
  funext i
  apply Fin.ext
  by_cases hi : 0 < P.length i
  · rw [liftTrimParam_apply_pos P (P.projectTrimParam x) i hi]
    have heq := (Fintype.equivFin (PositiveSide P)).symm_apply_apply ⟨i, hi⟩
    have hval : ((Fintype.equivFin (PositiveSide P)).symm
        (Fintype.equivFin (PositiveSide P) ⟨i, hi⟩)).1 = i :=
      congrArg Subtype.val heq
    simp only [projectTrimParam]
    rw [hval]
  · have hzero : P.length i = 0 := by omega
    rw [liftTrimParam_apply_zero P (P.projectTrimParam x) i hzero]
    have hxi := (x i).isLt
    simp [hzero] at hxi
    omega

lemma carrier_trimZeroSides (P : GeneralizedAP) :
    P.trimZeroSides.carrier = P.carrier := by
  ext z
  rw [mem_carrier_iff, mem_carrier_iff]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨P.liftTrimParam x, P.eval_liftTrimParam x⟩
  · rintro ⟨x, rfl⟩
    exact ⟨P.projectTrimParam x, P.eval_projectTrimParam x⟩

lemma liftTrimParam_injective (P : GeneralizedAP) :
    Function.Injective P.liftTrimParam := by
  intro x y hxy
  funext j
  apply Fin.ext
  let i := (Fintype.equivFin (PositiveSide P)).symm j
  have h := congrFun hxy i.1
  have hv := congrArg Fin.val h
  simp only [liftTrimParam, i.2, dite_true] at hv
  have he : Fintype.equivFin (PositiveSide P)
      ⟨i.1, i.2⟩ = j := by
    have hsub : (⟨i.1, i.2⟩ : PositiveSide P) = i := Subtype.ext rfl
    rw [hsub]
    exact Equiv.apply_symm_apply _ _
  rw [he] at hv
  exact hv

lemma proper_trimZeroSides (P : GeneralizedAP) (hP : P.Proper) :
    P.trimZeroSides.Proper := by
  intro x y hxy
  apply P.liftTrimParam_injective
  apply hP
  simpa only [P.eval_liftTrimParam] using hxy

lemma rank_trimZeroSides_le (P : GeneralizedAP) :
    P.trimZeroSides.rank ≤ P.rank := by
  change Fintype.card (PositiveSide P) ≤ P.rank
  simpa using Fintype.card_subtype_le (fun i : Fin P.rank => 0 < P.length i)

/-- Trimming is rank-preserving when every displayed coordinate is
nondegenerate. -/
lemma rank_trimZeroSides_eq_of_pos (P : GeneralizedAP)
    (hpos : ∀ i, 0 < P.length i) : P.trimZeroSides.rank = P.rank := by
  change Fintype.card (PositiveSide P) = P.rank
  calc
    Fintype.card (PositiveSide P) = Fintype.card (Fin P.rank) := by
      apply Fintype.card_congr
      exact Equiv.ofBijective Subtype.val
        ⟨Subtype.val_injective, fun i ↦ ⟨⟨i, hpos i⟩, rfl⟩⟩
    _ = P.rank := Fintype.card_fin P.rank

/-- Restrict a GAP to prescribed smaller side lengths.  On a collapsed
coordinate the generator is normalized to zero, since its coefficient is
forced to vanish. -/
def cropToLengths (R : GeneralizedAP) (L : Fin R.rank → ℕ) : GeneralizedAP where
  rank := R.rank
  base := R.base
  step i := if L i = 0 then 0 else R.step i
  length := L

/-- Embed a parameter of a cropped GAP into the original coefficient box. -/
def liftCropParam (R : GeneralizedAP) (L : Fin R.rank → ℕ)
    (hL : ∀ i, L i ≤ R.length i)
    (x : (R.cropToLengths L).Param) : R.Param :=
  fun i => ⟨x i, lt_of_lt_of_le (x i).isLt
    (Nat.succ_le_succ (hL i))⟩

lemma eval_liftCropParam (R : GeneralizedAP) (L : Fin R.rank → ℕ)
    (hL : ∀ i, L i ≤ R.length i)
    (x : (R.cropToLengths L).Param) :
    R.eval (R.liftCropParam L hL x) = (R.cropToLengths L).eval x := by
  simp only [eval, cropToLengths, liftCropParam]
  congr 1
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hz : L i = 0
  · have hx : (x i : ℕ) = 0 := by
      have hxlt : (x i : ℕ) < L i + 1 := (x i).isLt
      omega
    simp [hz, hx]
  · simp [hz]

lemma proper_cropToLengths (R : GeneralizedAP) (L : Fin R.rank → ℕ)
    (hR : R.Proper) (hL : ∀ i, L i ≤ R.length i) :
    (R.cropToLengths L).Proper := by
  intro x y hxy
  have hlift : R.liftCropParam L hL x = R.liftCropParam L hL y := by
    apply hR
    rw [R.eval_liftCropParam L hL x, R.eval_liftCropParam L hL y]
    exact hxy
  funext i
  apply Fin.ext
  exact congrArg (fun z => (z i).val) hlift

lemma carrier_cropToLengths_subset (R : GeneralizedAP)
    (L : Fin R.rank → ℕ) (hL : ∀ i, L i ≤ R.length i) :
    (R.cropToLengths L).carrier ⊆ R.carrier := by
  intro z hz
  obtain ⟨x, rfl⟩ := (R.cropToLengths L).mem_carrier_iff.mp hz
  apply R.mem_carrier_iff.mpr
  refine ⟨R.liftCropParam L hL x, ?_⟩
  exact R.eval_liftCropParam L hL x

/-- The geometric volume used in the Szemerédi--Vu and Nguyen--Vu papers. -/
def volume (Q : GeneralizedAP) : ℕ :=
  ∏ i : Fin Q.rank, Q.length i

/-- The homogeneous linear part of the GAP evaluation map. -/
def linearEval (Q : GeneralizedAP) (v : Fin Q.rank → ℤ) : ℤ :=
  ∑ i : Fin Q.rank, v i * Q.step i

lemma eval_eq_iff_linearEval_sub_eq_zero (Q : GeneralizedAP)
    (x y : Q.Param) :
    Q.eval x = Q.eval y ↔
      Q.linearEval (fun i => (x i : ℤ) - (y i : ℤ)) = 0 := by
  simp only [eval, linearEval]
  constructor
  · intro h
    have h' : (∑ i, (x i : ℤ) * Q.step i) =
        ∑ i, (y i : ℤ) * Q.step i := add_left_cancel h
    rw [show (∑ i, ((x i : ℤ) - (y i : ℤ)) * Q.step i) =
        (∑ i, (x i : ℤ) * Q.step i) -
          ∑ i, (y i : ℤ) * Q.step i by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring]
    exact sub_eq_zero.mpr h'
  · intro h
    rw [show (∑ i, ((x i : ℤ) - (y i : ℤ)) * Q.step i) =
        (∑ i, (x i : ℤ) * Q.step i) -
          ∑ i, (y i : ℤ) * Q.step i by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring] at h
    exact congrArg (Q.base + ·) (sub_eq_zero.mp h)

/-- Even without properness, the carrier has no more elements than its
coefficient box. -/
lemma card_carrier_le_box (Q : GeneralizedAP) :
    Q.carrier.card ≤ ∏ i : Fin Q.rank, (Q.length i + 1) := by
  rw [carrier]
  calc
    ((Finset.univ : Finset Q.Param).image Q.eval).card ≤
        (Finset.univ : Finset Q.Param).card := Finset.card_image_le
    _ = ∏ i : Fin Q.rank, (Q.length i + 1) := by
      simp [Param]

/-- A coefficient vector which is killed by the homogeneous evaluation map. -/
def Vanishes (Q : GeneralizedAP) (v : Fin Q.rank → ℤ) : Prop :=
  Q.linearEval v = 0

/-- Paper notation `nQ`: multiply the affine base and every side length by
`n`, while retaining the difference set. -/
def dilate (n : ℕ) (Q : GeneralizedAP) : GeneralizedAP where
  rank := Q.rank
  base := n * Q.base
  step := Q.step
  length i := n * Q.length i

@[simp] lemma rank_dilate (n : ℕ) (Q : GeneralizedAP) :
    (Q.dilate n).rank = Q.rank := rfl

@[simp] lemma dilate_dilate (m n : ℕ) (Q : GeneralizedAP) :
    (Q.dilate m).dilate n = Q.dilate (n * m) := by
  cases Q with
  | mk rank base step length =>
      simp [dilate, Nat.cast_mul, mul_assoc]

@[simp] lemma dilate_one (Q : GeneralizedAP) : Q.dilate 1 = Q := by
  cases Q
  simp [dilate]

@[simp] lemma volume_dilate (n : ℕ) (Q : GeneralizedAP) :
    (Q.dilate n).volume = n ^ Q.rank * Q.volume := by
  change (∏ i : Fin Q.rank, n * Q.length i) =
    n ^ Q.rank * ∏ i : Fin Q.rank, Q.length i
  rw [Finset.prod_mul_distrib]
  simp

/-- The coefficient-box cardinality of a GAP presentation. -/
def boxCard (Q : GeneralizedAP) : ℕ :=
  ∏ i : Fin Q.rank, (Q.length i + 1)

/-! ### Positive presentation

Nguyen--Vu normalize every progression of positive integers by reflecting the
coordinates with negative steps.  The following finite construction records
that normalization without changing either the carrier or properness. -/

def positiveForm (Q : GeneralizedAP) : GeneralizedAP where
  rank := Q.rank
  base := Q.base + ∑ i, if Q.step i < 0 then (Q.length i : ℤ) * Q.step i else 0
  step := fun i => |Q.step i|
  length := Q.length

@[simp] lemma rank_positiveForm (Q : GeneralizedAP) :
    Q.positiveForm.rank = Q.rank := rfl

@[simp] lemma length_positiveForm (Q : GeneralizedAP) (i : Fin Q.rank) :
    Q.positiveForm.length i = Q.length i := rfl

@[simp] lemma step_positiveForm_nonneg (Q : GeneralizedAP)
    (i : Fin Q.rank) : 0 ≤ Q.positiveForm.step i := by
  exact abs_nonneg _

def reflectParam (Q : GeneralizedAP) (x : Q.Param) :
    Q.positiveForm.Param := fun i =>
  if _hi : Q.step i < 0 then
    ⟨Q.length i - (x i : ℕ), Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  else
    ⟨x i, (x i).isLt⟩

def unreflectParam (Q : GeneralizedAP) (x : Q.positiveForm.Param) :
    Q.Param := fun i =>
  if _hi : Q.step i < 0 then
    ⟨Q.length i - (x i : ℕ), Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  else
    ⟨x i, by simpa only [length_positiveForm] using (x i).isLt⟩

@[simp] lemma reflectParam_apply_of_neg (Q : GeneralizedAP)
    (x : Q.Param) (i : Fin Q.rank) (hi : Q.step i < 0) :
    (Q.reflectParam x i : ℕ) = Q.length i - (x i : ℕ) := by
  simp [reflectParam, hi]

@[simp] lemma reflectParam_apply_of_nonneg (Q : GeneralizedAP)
    (x : Q.Param) (i : Fin Q.rank) (hi : 0 ≤ Q.step i) :
    (Q.reflectParam x i : ℕ) = (x i : ℕ) := by
  simp [reflectParam, not_lt.mpr hi]

lemma reflectParam_leftInverse (Q : GeneralizedAP) :
    Function.LeftInverse Q.unreflectParam Q.reflectParam := by
  intro x
  funext i
  apply Fin.ext
  by_cases hi : Q.step i < 0
  · simp [reflectParam, unreflectParam, hi,
      Nat.sub_sub_self (Nat.le_of_lt_succ (x i).isLt)]
  · simp [reflectParam, unreflectParam, hi]

lemma unreflectParam_leftInverse (Q : GeneralizedAP) :
    Function.LeftInverse Q.reflectParam Q.unreflectParam := by
  intro x
  funext i
  apply Fin.ext
  by_cases hi : Q.step i < 0
  · simp only [reflectParam, unreflectParam, hi, dite_true]
    have hxi := (x i).isLt
    change (x i : ℕ) < Q.length i + 1 at hxi
    exact Nat.sub_sub_self (Nat.le_of_lt_succ hxi)
  · simp [reflectParam, unreflectParam, hi]

lemma reflectParam_bijective (Q : GeneralizedAP) :
    Function.Bijective Q.reflectParam :=
  ⟨Q.reflectParam_leftInverse.injective,
    Q.unreflectParam_leftInverse.surjective⟩

lemma unreflectParam_bijective (Q : GeneralizedAP) :
    Function.Bijective Q.unreflectParam :=
  ⟨Q.unreflectParam_leftInverse.injective,
    Q.reflectParam_leftInverse.surjective⟩

lemma eval_positiveForm_reflectParam (Q : GeneralizedAP)
    (x : Q.Param) : Q.positiveForm.eval (Q.reflectParam x) = Q.eval x := by
  simp only [eval, positiveForm]
  change (Q.base + ∑ i : Fin Q.rank,
      if Q.step i < 0 then (Q.length i : ℤ) * Q.step i else 0) +
      ∑ i : Fin Q.rank, ((Q.reflectParam x i : ℕ) : ℤ) * |Q.step i| =
    Q.base + ∑ i : Fin Q.rank, ((x i : ℕ) : ℤ) * Q.step i
  rw [add_assoc]
  apply congrArg (Q.base + ·)
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hi : Q.step i < 0
  · rw [if_pos hi, abs_of_neg hi]
    simp only [reflectParam_apply_of_neg Q x i hi]
    have hxi : (x i : ℕ) ≤ Q.length i := Nat.le_of_lt_succ (x i).isLt
    have hcast : (((Q.length i - (x i : ℕ) : ℕ) : ℤ)) =
        (Q.length i : ℤ) - (x i : ℤ) := by omega
    rw [hcast]
    ring
  · have hi' : 0 ≤ Q.step i := not_lt.mp hi
    rw [if_neg hi, abs_of_nonneg hi']
    simp only [reflectParam_apply_of_nonneg Q x i hi']
    ring

lemma eval_positiveForm_eq_eval_unreflectParam (Q : GeneralizedAP)
    (x : Q.positiveForm.Param) :
    Q.positiveForm.eval x = Q.eval (Q.unreflectParam x) := by
  rw [← Q.eval_positiveForm_reflectParam (Q.unreflectParam x)]
  rw [Q.unreflectParam_leftInverse x]

lemma carrier_positiveForm (Q : GeneralizedAP) :
    Q.positiveForm.carrier = Q.carrier := by
  ext z
  rw [mem_carrier_iff, mem_carrier_iff]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨Q.unreflectParam y,
      (Q.eval_positiveForm_eq_eval_unreflectParam y).symm⟩
  · rintro ⟨x, rfl⟩
    exact ⟨Q.reflectParam x, Q.eval_positiveForm_reflectParam x⟩

lemma proper_positiveForm_iff (Q : GeneralizedAP) :
    Q.positiveForm.Proper ↔ Q.Proper := by
  constructor
  · intro h x y hxy
    apply Q.reflectParam_bijective.1
    apply h
    simpa only [Q.eval_positiveForm_reflectParam] using hxy
  · intro h x y hxy
    apply Q.unreflectParam_bijective.1
    apply h
    simpa only [Q.eval_positiveForm_eq_eval_unreflectParam] using hxy

lemma step_ne_zero_of_proper_length_pos (Q : GeneralizedAP)
    (hproper : Q.Proper) {i : Fin Q.rank} (hlen : 0 < Q.length i) :
    Q.step i ≠ 0 := by
  intro hstep
  let x : Q.Param := fun _ => 0
  let y : Q.Param := fun j =>
    if hji : j = i then
      ⟨1, by subst j; omega⟩
    else 0
  have heval : Q.eval x = Q.eval y := by
    simp only [eval, x, y]
    congr 1
    apply Finset.sum_congr rfl
    intro j _hj
    by_cases hji : j = i
    · subst j
      simp [hstep]
    · simp [hji]
  have hxy := hproper heval
  have hi := congrFun hxy i
  have hval := congrArg Fin.val hi
  have hxval : (x i).val = 0 := rfl
  have hyval : (y i).val = 1 := by simp [y]
  omega

lemma step_positiveForm_pos_of_proper (Q : GeneralizedAP)
    (hproper : Q.Proper) (hpos : ∀ i, 0 < Q.length i)
    (i : Fin Q.rank) : 0 < Q.positiveForm.step i := by
  change 0 < |Q.step i|
  exact abs_pos.mpr (Q.step_ne_zero_of_proper_length_pos hproper (hpos i))


end GeneralizedAP

end Erdos587
