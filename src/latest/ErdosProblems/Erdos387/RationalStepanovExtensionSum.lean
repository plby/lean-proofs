/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.RationalStepanovFiberCount
import Waring.Analytic.FiniteFiberCharacterBound
import Waring.Analytic.Basic

/-!
# Rational Stepanov extension-field character sum

The non-pole trace-fiber estimate is enlarged by the finite pole set and
combined with additive-character orthogonality.  Removing the pole terms
then gives a uniform square-root bound for the zero-extended rational phase.
-/

namespace Erdos387

open scoped BigOperators

namespace RationalStepanov

/-- In an extension field, the mapped pole set is the image of the base
pole support. -/
theorem isMappedPole_iff_mem_image
    {p : ℕ} [NeZero p]
    {E : Type*} [Field E] [DecidableEq E] [Algebra (ZMod p) E]
    (coeff : ZMod p → ZMod p) (x : E) :
    RationalWeil.IsMappedPole coeff x ↔
      x ∈ (InverseRational.poleSupport coeff).image
        (algebraMap (ZMod p) E) := by
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact Finset.mem_image.mpr ⟨r, hr, rfl⟩
  · intro hx
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨r, hr, rfl⟩

/-- The zero-extended rational trace sum in degree `2*(h+3)` has an
explicit square-root-sized bound. -/
theorem norm_extension_zeroExtendedTraceWeight_le
    {p : ℕ} [NeZero p] [Fact p.Prime] (hp : 1 < p)
    (coeff : ZMod p → ZMod p)
    (hne : (InverseRational.poleSupport coeff).Nonempty)
    (hs : (InverseRational.poleSupport coeff).card < p)
    (h : ℕ) :
    let E := FiniteField.Extension (ZMod p) p (2 * (h + 3))
    letI : Fintype E := Fintype.ofFinite E
    ‖∑ x : E, RationalWeil.zeroExtendedTraceWeight coeff x‖ ≤
      ((p * (p ^ (h + 3) + p ^ 2 *
          rationalPhaseAllowance p h
            (InverseRational.poleSupport coeff).card +
          (InverseRational.poleSupport coeff).card) +
        (InverseRational.poleSupport coeff).card : ℕ) : ℝ) := by
  classical
  let E := FiniteField.Extension (ZMod p) p (2 * (h + 3))
  let : CharP E p :=
    (Algebra.charP_iff (ZMod p) E p).mp (ZMod.charP p)
  let : Fintype E := Fintype.ofFinite E
  let phaseTrace : E → ZMod p := fun x =>
    Algebra.trace (ZMod p) E
      (RationalWeil.mappedSimplePolePhase coeff x)
  let poles : Finset E :=
    (InverseRational.poleSupport coeff).image (algebraMap (ZMod p) E)
  let average : ℕ := p ^ (2 * (h + 3) - 1)
  let error : ℕ := p ^ (h + 3) + p ^ 2 *
      rationalPhaseAllowance p h
        (InverseRational.poleSupport coeff).card +
      (InverseRational.poleSupport coeff).card
  have hpolesCard : poles.card =
      (InverseRational.poleSupport coeff).card := by
    exact Finset.card_image_of_injective _
      (algebraMap (ZMod p) E).injective
  have hfiber (c : ZMod p) :
      (Finset.univ.filter fun x : E => phaseTrace x = c).card ≤
        average + error := by
    let fullFiber : Finset E :=
      Finset.univ.filter fun x : E => phaseTrace x = c
    have hsubset : fullFiber ⊆ nonpoleTraceFiber coeff c ∪ poles := by
      intro x hx
      have hxc : phaseTrace x = c := (Finset.mem_filter.mp hx).2
      by_cases hxpole : RationalWeil.IsMappedPole coeff x
      · exact Finset.mem_union_right _ <|
          (isMappedPole_iff_mem_image coeff x).mp hxpole
      · apply Finset.mem_union_left
        simp only [nonpoleTraceFiber, Finset.mem_filter, Finset.mem_univ,
          true_and]
        exact ⟨hxpole, hxc⟩
    have hnonpole := card_nonpole_trace_fiber_le
      hp coeff hne hs h c
    change fullFiber.card ≤ average + error
    calc
      fullFiber.card ≤ (nonpoleTraceFiber coeff c ∪ poles).card :=
        Finset.card_le_card hsubset
      _ ≤ (nonpoleTraceFiber coeff c).card + poles.card :=
        Finset.card_union_le _ _
      _ ≤ rationalTraceFiberBound p h
          (InverseRational.poleSupport coeff).card + poles.card :=
        Nat.add_le_add_right hnonpole _
      _ = average + error := by
        rw [hpolesCard]
        unfold rationalTraceFiberBound average error
        omega
  have hcardE : Fintype.card E = p ^ (2 * (h + 3)) := by
    rw [Fintype.card_eq_nat_card]
    change Nat.card
      (FiniteField.Extension (ZMod p) p (2 * (h + 3))) = _
    rw [FiniteField.natCard_extension, Nat.card_zmod]
  have hcard : Fintype.card E = Fintype.card (ZMod p) * average := by
    rw [hcardE, ZMod.card]
    unfold average
    calc
      p ^ (2 * (h + 3)) = p ^ ((2 * (h + 3) - 1) + 1) := by
        congr 1 <;> omega
      _ = p ^ (2 * (h + 3) - 1) * p := by rw [pow_add, pow_one]
      _ = p * p ^ (2 * (h + 3) - 1) := Nat.mul_comm _ _
  have hcharNe : (ZMod.stdAddChar : AddChar (ZMod p) ℂ) ≠ 1 := by
    intro htrivial
    have hprimitive := ZMod.isPrimitive_stdAddChar p
    have hshift := hprimitive (a := 1) one_ne_zero
    rw [AddChar.mulShift_one, htrivial] at hshift
    exact hshift rfl
  have hmean : ∑ c : ZMod p, ZMod.stdAddChar c = 0 :=
    AddChar.sum_eq_zero_of_ne_one hcharNe
  have hweight (c : ZMod p) : ‖ZMod.stdAddChar c‖ ≤ 1 := by
    rw [Waring.Analytic.norm_stdAddChar]
  have hfull : ‖∑ x : E, ZMod.stdAddChar (phaseTrace x)‖ ≤
      (p * error : ℕ) := by
    have hcore := Waring.Analytic.norm_fintype_sum_comp_le_of_card_fiber_le
      phaseTrace (fun c : ZMod p => ZMod.stdAddChar c)
      average error hfiber hcard hmean hweight
    simpa only [ZMod.card] using hcore
  have hpoleIff (x : E) :
      RationalWeil.IsMappedPole coeff x ↔ x ∈ poles := by
    exact isMappedPole_iff_mem_image coeff x
  have hidentity :
      (∑ x : E, RationalWeil.zeroExtendedTraceWeight coeff x) =
        (∑ x : E, ZMod.stdAddChar (phaseTrace x)) -
          ∑ x ∈ poles, ZMod.stdAddChar (phaseTrace x) := by
    calc
      (∑ x : E, RationalWeil.zeroExtendedTraceWeight coeff x) =
          ∑ x : E, (ZMod.stdAddChar (phaseTrace x) -
            if x ∈ poles then ZMod.stdAddChar (phaseTrace x) else 0) := by
        apply Finset.sum_congr rfl
        intro x hx
        by_cases hxpole : RationalWeil.IsMappedPole coeff x
        · simp [RationalWeil.zeroExtendedTraceWeight, hxpole,
            (hpoleIff x).mp hxpole]
        · have hxnotmem : x ∉ poles := fun hxmem =>
            hxpole ((hpoleIff x).mpr hxmem)
          simp [RationalWeil.zeroExtendedTraceWeight, hxpole,
            hxnotmem, phaseTrace]
      _ = (∑ x : E, ZMod.stdAddChar (phaseTrace x)) -
          ∑ x : E,
            if x ∈ poles then ZMod.stdAddChar (phaseTrace x) else 0 := by
        rw [Finset.sum_sub_distrib]
      _ = (∑ x : E, ZMod.stdAddChar (phaseTrace x)) -
          ∑ x ∈ poles, ZMod.stdAddChar (phaseTrace x) := by
        congr 1
        simp
  have hpoleSum : ‖∑ x ∈ poles, ZMod.stdAddChar (phaseTrace x)‖ ≤
      ((InverseRational.poleSupport coeff).card : ℕ) := by
    calc
      ‖∑ x ∈ poles, ZMod.stdAddChar (phaseTrace x)‖ ≤
          ∑ x ∈ poles, ‖ZMod.stdAddChar (phaseTrace x)‖ :=
        norm_sum_le _ _
      _ = ∑ _x ∈ poles, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [Waring.Analytic.norm_stdAddChar]
      _ = poles.card := by simp
      _ = (InverseRational.poleSupport coeff).card := by rw [hpolesCard]
  dsimp only
  rw [hidentity]
  calc
    ‖(∑ x : E, ZMod.stdAddChar (phaseTrace x)) -
        ∑ x ∈ poles, ZMod.stdAddChar (phaseTrace x)‖ ≤
        ‖∑ x : E, ZMod.stdAddChar (phaseTrace x)‖ +
          ‖∑ x ∈ poles, ZMod.stdAddChar (phaseTrace x)‖ :=
      norm_sub_le _ _
    _ ≤ (p * error : ℕ) +
        (InverseRational.poleSupport coeff).card :=
      add_le_add hfull hpoleSum
    _ = ((p * (p ^ (h + 3) + p ^ 2 *
          rationalPhaseAllowance p h
            (InverseRational.poleSupport coeff).card +
          (InverseRational.poleSupport coeff).card) +
        (InverseRational.poleSupport coeff).card : ℕ) : ℝ) := by
      simp [error]

/-- The Stepanov estimate supplies the exact even-extension square-root
input required by the Artin-polynomial root-radius argument. -/
theorem hasEvenExtensionSquareRootBound
    {p : ℕ} [NeZero p] [Fact p.Prime] (hp : 1 < p)
    (coeff : ZMod p → ZMod p)
    (hne : (InverseRational.poleSupport coeff).Nonempty)
    (hs : (InverseRational.poleSupport coeff).card < p) :
    RationalWeil.HasEvenExtensionSquareRootBound coeff := by
  let s := (InverseRational.poleSupport coeff).card
  let Cnat := p * (1 + p ^ 2 * ((p - 1) * s) + s) + s
  refine ⟨(Cnat : ℝ), ?_⟩
  intro m hm
  let : NeZero (2 * m) := ⟨by omega⟩
  let E := FiniteField.Extension (ZMod p) p (2 * m)
  let : Fintype E := Fintype.ofFinite E
  let h := m - 3
  have hh : h + 3 = m := by omega
  have hstep := norm_extension_zeroExtendedTraceWeight_le
    hp coeff hne hs h
  dsimp only at hstep ⊢
  rw [hh] at hstep
  refine hstep.trans ?_
  have hp0 : 0 < p := by omega
  have hpowOne : 1 ≤ p ^ m := one_le_pow₀ (by omega : 1 ≤ p)
  have hgeomIdentity := pred_mul_frobeniusOrderSum_add_one
    (p := p) (m := m) hp0
  have hgeom : frobeniusOrderSum p m ≤ p ^ m := by
    have hpred : 1 ≤ p - 1 := by omega
    calc
      frobeniusOrderSum p m ≤
          (p - 1) * frobeniusOrderSum p m := by
        nlinarith
      _ ≤ (p - 1) * frobeniusOrderSum p m + 1 := Nat.le_add_right _ _
      _ = p ^ m := hgeomIdentity
  have hallow : rationalPhaseAllowance p h s ≤
      ((p - 1) * s) * p ^ m := by
    unfold rationalPhaseAllowance
    rw [hh]
    exact Nat.mul_le_mul_left ((p - 1) * s) hgeom
  have hsPow : s ≤ s * p ^ m := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left s hpowOne
  have hinside :
      p ^ m + p ^ 2 * rationalPhaseAllowance p h s + s ≤
        (1 + p ^ 2 * ((p - 1) * s) + s) * p ^ m := by
    calc
      p ^ m + p ^ 2 * rationalPhaseAllowance p h s + s ≤
          p ^ m + p ^ 2 * (((p - 1) * s) * p ^ m) + s * p ^ m :=
        Nat.add_le_add (Nat.add_le_add_left
          (Nat.mul_le_mul_left (p ^ 2) hallow) _) hsPow
      _ = (1 + p ^ 2 * ((p - 1) * s) + s) * p ^ m := by ring
  have hnat :
      p * (p ^ m + p ^ 2 * rationalPhaseAllowance p h s + s) + s ≤
        Cnat * p ^ m := by
    calc
      p * (p ^ m + p ^ 2 * rationalPhaseAllowance p h s + s) + s ≤
          p * ((1 + p ^ 2 * ((p - 1) * s) + s) * p ^ m) +
            s * p ^ m :=
        Nat.add_le_add (Nat.mul_le_mul_left p hinside) hsPow
      _ = Cnat * p ^ m := by unfold Cnat; ring
  norm_cast

/-- Unconditional base-field rational Weil bound for every nonempty
simple-pole phase whose support has cardinality below the characteristic. -/
theorem norm_zeroExtendedSimplePolePhase_sum_le
    {p : ℕ} [NeZero p] [Fact p.Prime] (hp : 1 < p)
    (coeff : ZMod p → ZMod p)
    (hne : (InverseRational.poleSupport coeff).Nonempty)
    (hs : (InverseRational.poleSupport coeff).card < p) :
    ‖∑ x : ZMod p,
        if x ∈ InverseRational.poleSupport coeff then 0
        else ZMod.stdAddChar (InverseRational.simplePolePhase coeff x)‖ ≤
      ((2 * (InverseRational.poleSupport coeff).card - 1 : ℕ) : ℝ) *
        Real.sqrt (p : ℝ) := by
  exact RationalWeil.norm_zeroExtendedSimplePolePhase_sum_le_of_evenExtensionBound
    coeff hne (hasEvenExtensionSquareRootBound hp coeff hne hs)

/-- The corresponding complete sum with the ordinary `ZMod` inverse values
restored at the poles.  Restoring those terms costs at most the support
cardinality. -/
theorem norm_simplePolePhase_sum_le
    {p : ℕ} [NeZero p] [Fact p.Prime] (hp : 1 < p)
    (coeff : ZMod p → ZMod p)
    (hne : (InverseRational.poleSupport coeff).Nonempty)
    (hs : (InverseRational.poleSupport coeff).card < p) :
    ‖∑ x : ZMod p,
        ZMod.stdAddChar (InverseRational.simplePolePhase coeff x)‖ ≤
      ((2 * (InverseRational.poleSupport coeff).card - 1 : ℕ) : ℝ) *
          Real.sqrt (p : ℝ) +
        (InverseRational.poleSupport coeff).card := by
  classical
  let support := InverseRational.poleSupport coeff
  have hzero := norm_zeroExtendedSimplePolePhase_sum_le
    hp coeff hne hs
  have hidentity :
      (∑ x : ZMod p,
          ZMod.stdAddChar (InverseRational.simplePolePhase coeff x)) =
        (∑ x : ZMod p,
          if x ∈ support then 0
          else ZMod.stdAddChar
            (InverseRational.simplePolePhase coeff x)) +
        ∑ x ∈ support,
          ZMod.stdAddChar (InverseRational.simplePolePhase coeff x) := by
    calc
      (∑ x : ZMod p,
          ZMod.stdAddChar (InverseRational.simplePolePhase coeff x)) =
          ∑ x : ZMod p,
            ((if x ∈ support then 0
              else ZMod.stdAddChar
                (InverseRational.simplePolePhase coeff x)) +
             if x ∈ support then
               ZMod.stdAddChar (InverseRational.simplePolePhase coeff x)
             else 0) := by
        apply Finset.sum_congr rfl
        intro x _hx
        by_cases hx : x ∈ support <;> simp [hx]
      _ = (∑ x : ZMod p,
            if x ∈ support then 0
            else ZMod.stdAddChar
              (InverseRational.simplePolePhase coeff x)) +
          ∑ x : ZMod p,
            if x ∈ support then
              ZMod.stdAddChar (InverseRational.simplePolePhase coeff x)
            else 0 := Finset.sum_add_distrib
      _ = (∑ x : ZMod p,
            if x ∈ support then 0
            else ZMod.stdAddChar
              (InverseRational.simplePolePhase coeff x)) +
          ∑ x ∈ support,
            ZMod.stdAddChar (InverseRational.simplePolePhase coeff x) := by
        congr 1
        simp
  have hpoles :
      ‖∑ x ∈ support,
          ZMod.stdAddChar (InverseRational.simplePolePhase coeff x)‖ ≤
        (support.card : ℝ) := by
    calc
      ‖∑ x ∈ support,
          ZMod.stdAddChar (InverseRational.simplePolePhase coeff x)‖ ≤
          ∑ x ∈ support,
            ‖ZMod.stdAddChar (InverseRational.simplePolePhase coeff x)‖ :=
        norm_sum_le _ _
      _ = ∑ _x ∈ support, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [AddChar.norm_apply]
      _ = support.card := by simp
  rw [hidentity]
  exact (norm_add_le _ _).trans (add_le_add hzero hpoles)

end RationalStepanov

end Erdos387
