/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.InverseRationalPolynomial

/-!
# Translating a proper pole set in a prime field

The nondegeneracy check in BNPZ Section 10 repeatedly subtracts two
translates of a rational function.  A nonempty proper pole set cannot be
invariant under translation by a nonzero element of a prime field.  Hence
one of the two translates has a pole not shared by the other.
-/

namespace Erdos387

namespace InverseRational

/-- A nonempty proper subset of the additive group of a prime field is not
stable under a nonzero translation.  The conclusion is oriented exactly as
needed for the pole-survival induction. -/
theorem exists_mem_sub_not_mem_of_nonempty_ne_univ
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (P : Finset (ZMod p)) (hP : P.Nonempty)
    (hproper : P ≠ Finset.univ) {d : ZMod p} (hd : d ≠ 0) :
    ∃ r, r ∈ P ∧ r - d ∉ P := by
  by_contra hnone
  have hclosed : ∀ r, r ∈ P → r - d ∈ P := by
    intro r hr
    by_contra hout
    exact hnone ⟨r, hr, hout⟩
  obtain ⟨r, hr⟩ := hP
  have hiter : ∀ n : ℕ, r - (n : ZMod p) * d ∈ P := by
    intro n
    induction n with
    | zero => simpa using hr
    | succ n ih =>
        have hnext := hclosed (r - (n : ZMod p) * d) ih
        convert hnext using 1 <;> push_cast <;> ring
  apply hproper
  apply Finset.eq_univ_of_forall
  intro x
  let z : ZMod p := (r - x) * d⁻¹
  have hz := hiter z.val
  rw [ZMod.natCast_zmod_val] at hz
  have hzx : r - z * d = x := by
    dsimp [z]
    rw [mul_assoc, inv_mul_cancel₀ hd, mul_one]
    ring
  rwa [hzx] at hz

/-- Support of the nonzero partial-fraction coefficients. -/
noncomputable def poleSupport
    {p : ℕ} [NeZero p] (coeff : ZMod p → ZMod p) :
    Finset (ZMod p) := by
  classical
  exact Finset.univ.filter fun r => coeff r ≠ 0

@[simp] theorem mem_poleSupport
    {p : ℕ} [NeZero p] (coeff : ZMod p → ZMod p) (r : ZMod p) :
    r ∈ poleSupport coeff ↔ coeff r ≠ 0 := by
  simp [poleSupport]

/-- Coefficients after translating the argument by `t`. -/
def translatedCoefficient
    {p : ℕ} [NeZero p] (coeff : ZMod p → ZMod p) (t r : ZMod p) :
    ZMod p := coeff (r + t)

/-- Coefficients after subtracting two translates of the same simple-pole
partial fraction. -/
def differenceCoefficient
    {p : ℕ} [NeZero p] (coeff : ZMod p → ZMod p)
    (t₁ t₂ r : ZMod p) : ZMod p :=
  translatedCoefficient coeff t₁ r - translatedCoefficient coeff t₂ r

/-- Translating the argument translates the coefficient support in the
opposite direction. -/
theorem poleSupport_translatedCoefficient
    {p : ℕ} [NeZero p] (coeff : ZMod p → ZMod p) (t : ZMod p) :
    poleSupport (translatedCoefficient coeff t) =
      (poleSupport coeff).image (fun r => r - t) := by
  classical
  ext r
  rw [mem_poleSupport, Finset.mem_image]
  constructor
  · intro hr
    refine ⟨r + t, ?_, by ring⟩
    simpa [translatedCoefficient] using hr
  · rintro ⟨s, hs, rfl⟩
    simpa [translatedCoefficient] using hs

/-- A coefficient in the difference can be nonzero only where at least one
of the two translated coefficient families is nonzero. -/
theorem poleSupport_differenceCoefficient_subset
    {p : ℕ} [NeZero p] (coeff : ZMod p → ZMod p) (t₁ t₂ : ZMod p) :
    poleSupport (differenceCoefficient coeff t₁ t₂) ⊆
      poleSupport (translatedCoefficient coeff t₁) ∪
        poleSupport (translatedCoefficient coeff t₂) := by
  classical
  intro r hr
  rw [mem_poleSupport] at hr
  by_cases h₁ : coeff (r + t₁) = 0
  · rw [Finset.mem_union]
    right
    rw [mem_poleSupport]
    intro h₂
    apply hr
    have ht₁ : translatedCoefficient coeff t₁ r = 0 := by
      simpa [translatedCoefficient] using h₁
    rw [differenceCoefficient, ht₁, h₂, sub_self]
  · rw [Finset.mem_union]
    left
    simpa [translatedCoefficient] using h₁

/-- Subtracting two translates at most doubles the number of poles. -/
theorem card_poleSupport_differenceCoefficient_le
    {p : ℕ} [NeZero p] (coeff : ZMod p → ZMod p) (t₁ t₂ : ZMod p) :
    (poleSupport (differenceCoefficient coeff t₁ t₂)).card ≤
      2 * (poleSupport coeff).card := by
  classical
  have hinj (t : ZMod p) :
      Function.Injective (fun r : ZMod p => r - t) := by
    intro r s hrs
    calc
      r = (r - t) + t := (sub_add_cancel r t).symm
      _ = (s - t) + t := congrArg (fun x => x + t) hrs
      _ = s := sub_add_cancel s t
  have hcardTranslate (t : ZMod p) :
      (poleSupport (translatedCoefficient coeff t)).card =
        (poleSupport coeff).card := by
    rw [poleSupport_translatedCoefficient,
      Finset.card_image_of_injective _ (hinj t)]
  calc
    (poleSupport (differenceCoefficient coeff t₁ t₂)).card ≤
        (poleSupport (translatedCoefficient coeff t₁) ∪
          poleSupport (translatedCoefficient coeff t₂)).card :=
      Finset.card_le_card
        (poleSupport_differenceCoefficient_subset coeff t₁ t₂)
    _ ≤ (poleSupport (translatedCoefficient coeff t₁)).card +
          (poleSupport (translatedCoefficient coeff t₂)).card :=
      Finset.card_union_le _ _
    _ = 2 * (poleSupport coeff).card := by
      rw [hcardTranslate, hcardTranslate]
      omega

/-- If the old pole set is nonempty and has size below the field cardinality,
then subtracting translates by distinct shifts leaves at least one pole. -/
theorem poleSupport_differenceCoefficient_nonempty
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p)
    (hcoeff : (poleSupport coeff).Nonempty)
    (hcard : (poleSupport coeff).card < p)
    (t₁ t₂ : ZMod p) (hne : t₁ ≠ t₂) :
    (poleSupport (differenceCoefficient coeff t₁ t₂)).Nonempty := by
  classical
  have hproper : poleSupport coeff ≠ Finset.univ := by
    intro hfull
    rw [hfull] at hcard
    simpa using hcard
  have hd : t₁ - t₂ ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨r, hr, hrsub⟩ :=
    exists_mem_sub_not_mem_of_nonempty_ne_univ
      (poleSupport coeff) hcoeff hproper hd
  have hcr : coeff r ≠ 0 := (mem_poleSupport coeff r).mp hr
  have hcrsub : coeff (r - (t₁ - t₂)) = 0 := by
    simpa only [mem_poleSupport, not_ne_iff] using hrsub
  refine ⟨r - t₁, ?_⟩
  rw [mem_poleSupport]
  simp only [differenceCoefficient, translatedCoefficient]
  rw [show r - t₁ + t₁ = r by ring,
    show r - t₁ + t₂ = r - (t₁ - t₂) by ring, hcrsub, sub_zero]
  exact hcr

/-- Iterate the coefficient update associated with subtracting pairs of
translates.  This matches the rational functions `t_j` in BNPZ Section 10. -/
def iteratedDifferenceCoefficient
    {p : ℕ} [NeZero p] (coeff : ZMod p → ZMod p) :
    List (ZMod p × ZMod p) → ZMod p → ZMod p
  | [], r => coeff r
  | shifts :: rest, r =>
      differenceCoefficient
        (iteratedDifferenceCoefficient coeff rest) shifts.1 shifts.2 r

/-- After `j` translate-differences, the number of nonzero simple-pole
coefficients is at most `2^j` times the initial number. -/
theorem card_poleSupport_iteratedDifferenceCoefficient_le
    {p : ℕ} [NeZero p] (coeff : ZMod p → ZMod p)
    (shifts : List (ZMod p × ZMod p)) :
    (poleSupport (iteratedDifferenceCoefficient coeff shifts)).card ≤
      2 ^ shifts.length * (poleSupport coeff).card := by
  induction shifts with
  | nil => simp [iteratedDifferenceCoefficient]
  | cons t shifts ih =>
      calc
        (poleSupport
            (iteratedDifferenceCoefficient coeff (t :: shifts))).card ≤
            2 * (poleSupport
              (iteratedDifferenceCoefficient coeff shifts)).card := by
          exact card_poleSupport_differenceCoefficient_le
            (iteratedDifferenceCoefficient coeff shifts) t.1 t.2
        _ ≤ 2 * (2 ^ shifts.length * (poleSupport coeff).card) :=
          Nat.mul_le_mul_left 2 ih
        _ = 2 ^ (t :: shifts).length * (poleSupport coeff).card := by
          simp [pow_succ]
          ring

/-- Under the source's two hypotheses—every shift pair is distinct and the
final `2^j` pole envelope is smaller than `p`—the iterated rational phase
still has at least one pole. -/
theorem poleSupport_iteratedDifferenceCoefficient_nonempty
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p)
    (hcoeff : (poleSupport coeff).Nonempty)
    (shifts : List (ZMod p × ZMod p))
    (hdistinct : ∀ t ∈ shifts, t.1 ≠ t.2)
    (hcard : 2 ^ shifts.length * (poleSupport coeff).card < p) :
    (poleSupport (iteratedDifferenceCoefficient coeff shifts)).Nonempty := by
  induction shifts with
  | nil => simpa [iteratedDifferenceCoefficient] using hcoeff
  | cons t shifts ih =>
      have htailDistinct : ∀ u ∈ shifts, u.1 ≠ u.2 := by
        intro u hu
        exact hdistinct u (by simp [hu])
      have htailCard :
          2 ^ shifts.length * (poleSupport coeff).card < p := by
        apply lt_of_le_of_lt _ hcard
        simp only [List.length_cons, pow_succ]
        nlinarith [show 0 < 2 ^ shifts.length by positivity]
      have htailNonempty :
          (poleSupport
            (iteratedDifferenceCoefficient coeff shifts)).Nonempty :=
        ih htailDistinct htailCard
      have htailSupportCard :
          (poleSupport
            (iteratedDifferenceCoefficient coeff shifts)).card < p := by
        exact (card_poleSupport_iteratedDifferenceCoefficient_le
          coeff shifts).trans_lt htailCard
      exact poleSupport_differenceCoefficient_nonempty
        (iteratedDifferenceCoefficient coeff shifts) htailNonempty
        htailSupportCard t.1 t.2
        (hdistinct t (by simp))

/-- A single nonzero simple-pole coefficient. -/
def singlePoleCoefficient
    {p : ℕ} [NeZero p] (c pole r : ZMod p) : ZMod p :=
  if r = pole then c else 0

theorem poleSupport_singlePoleCoefficient
    {p : ℕ} [NeZero p] {c pole : ZMod p} (hc : c ≠ 0) :
    poleSupport (singlePoleCoefficient c pole) = {pole} := by
  classical
  ext r
  simp [singlePoleCoefficient, hc]

/-- The iterated difference of one nonzero reciprocal pole has a surviving
pole whenever `2^j < p` and all paired shifts are distinct. -/
theorem singlePole_iteratedDifference_nonempty
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {c pole : ZMod p} (hc : c ≠ 0)
    (shifts : List (ZMod p × ZMod p))
    (hdistinct : ∀ t ∈ shifts, t.1 ≠ t.2)
    (hpow : 2 ^ shifts.length < p) :
    (poleSupport
      (iteratedDifferenceCoefficient
        (singlePoleCoefficient c pole) shifts)).Nonempty := by
  have hsingle := poleSupport_singlePoleCoefficient (pole := pole) hc
  apply poleSupport_iteratedDifferenceCoefficient_nonempty
    (singlePoleCoefficient c pole)
  · rw [hsingle]
    simp
  · exact hdistinct
  · rw [hsingle]
    simpa using hpow

/-- Rational phase represented as a finite sum of simple reciprocal poles. -/
noncomputable def simplePolePhase
    {p : ℕ} [NeZero p] (coeff : ZMod p → ZMod p) (x : ZMod p) :
    ZMod p :=
  ∑ r : ZMod p, coeff r * (x - r)⁻¹

/-- Translating the coefficient support in the opposite direction translates
the argument of the represented rational phase. -/
theorem simplePolePhase_translatedCoefficient
    {p : ℕ} [NeZero p] (coeff : ZMod p → ZMod p)
    (t x : ZMod p) :
    simplePolePhase (translatedCoefficient coeff t) x =
      simplePolePhase coeff (x + t) := by
  classical
  unfold simplePolePhase
  refine Fintype.sum_equiv (Equiv.addRight t) _ _ ?_
  intro r
  change coeff (r + t) * (x - r)⁻¹ =
    coeff (r + t) * (x + t - (r + t))⁻¹
  congr 2
  ring

/-- Subtracting coefficient families represents the difference of the two
translated rational phases. -/
theorem simplePolePhase_differenceCoefficient
    {p : ℕ} [NeZero p] (coeff : ZMod p → ZMod p)
    (t₁ t₂ x : ZMod p) :
    simplePolePhase (differenceCoefficient coeff t₁ t₂) x =
      simplePolePhase coeff (x + t₁) -
        simplePolePhase coeff (x + t₂) := by
  classical
  change (∑ r : ZMod p,
      (translatedCoefficient coeff t₁ r -
        translatedCoefficient coeff t₂ r) * (x - r)⁻¹) = _
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  change simplePolePhase (translatedCoefficient coeff t₁) x -
      simplePolePhase (translatedCoefficient coeff t₂) x = _
  rw [
    simplePolePhase_translatedCoefficient,
    simplePolePhase_translatedCoefficient]

/-- The single coefficient at `-a` represents `c/(a+x)`. -/
theorem simplePolePhase_singlePoleCoefficient_neg
    {p : ℕ} [NeZero p] (c a x : ZMod p) :
    simplePolePhase (singlePoleCoefficient c (-a)) x =
      c * (a + x)⁻¹ := by
  classical
  simp [simplePolePhase, singlePoleCoefficient]
  congr 2
  ring

/-- Iterated subtraction of paired translates at the level of functions. -/
def iteratedTranslateDifference
    {p : ℕ} [NeZero p] (f : ZMod p → ZMod p) :
    List (ZMod p × ZMod p) → ZMod p → ZMod p
  | [], x => f x
  | shifts :: rest, x =>
      iteratedTranslateDifference f rest (x + shifts.1) -
        iteratedTranslateDifference f rest (x + shifts.2)

/-- The coefficient recursion and the pointwise translate-difference
recursion represent exactly the same rational phase. -/
theorem simplePolePhase_iteratedDifferenceCoefficient
    {p : ℕ} [NeZero p] (coeff : ZMod p → ZMod p)
    (shifts : List (ZMod p × ZMod p)) (x : ZMod p) :
    simplePolePhase (iteratedDifferenceCoefficient coeff shifts) x =
      iteratedTranslateDifference (simplePolePhase coeff) shifts x := by
  induction shifts generalizing x with
  | nil => rfl
  | cons t shifts ih =>
      change simplePolePhase
          (differenceCoefficient
            (iteratedDifferenceCoefficient coeff shifts) t.1 t.2) x =
        iteratedTranslateDifference (simplePolePhase coeff) shifts (x + t.1) -
          iteratedTranslateDifference (simplePolePhase coeff) shifts (x + t.2)
      rw [simplePolePhase_differenceCoefficient, ih, ih]

end InverseRational

end Erdos387
