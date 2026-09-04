import ErdosProblems.Erdos394.PairLatticeMomentBound
import ErdosProblems.Erdos394.RootBoxLocalCount

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Actual CRT tuple hit counts and their second moment
-/

open Nat Finset

namespace Erdos394

/-- Generic double-counting identity for a finite hit relation. -/
theorem sum_hitCount_sq_eq_pairCount [DecidableEq α] [DecidableEq β]
    (H : Finset α) (T : Finset β) (hit : α → β → Prop)
    [DecidableRel hit] :
    (∑ h ∈ H, ((T.filter (hit h)).card) ^ 2) =
      ∑ j ∈ T, ∑ l ∈ T,
        (H.filter (fun h ↦ hit h j ∧ hit h l)).card := by
  simp_rw [Finset.card_filter]
  simp only [pow_two]
  rw [show (∑ h ∈ H,
      (∑ j ∈ T, if hit h j then 1 else 0) *
        ∑ l ∈ T, if hit h l then 1 else 0) =
      ∑ h ∈ H, ∑ j ∈ T, ∑ l ∈ T,
        (if hit h j ∧ hit h l then 1 else 0) by
    apply Finset.sum_congr rfl
    intro h hh
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    by_cases hjhit : hit h j <;> by_cases hlhit : hit h l <;>
      simp [hjhit, hlhit]]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_comm]

abbrev RootBoxMultiplierTuple (P : Finset ℕ) :=
  ∀ p : ↥P, (ZMod p.val)ˣ

/-- Full independent local-unit tuple universe. -/
noncomputable def rootBoxMultiplierUniverse
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime) :
    Finset (RootBoxMultiplierTuple P) := by
  classical
  letI (p : ↥P) : NeZero p.val := ⟨(hprime p.val p.property).ne_zero⟩
  exact Fintype.piFinset (fun p : ↥P ↦
    (Finset.univ : Finset (ZMod p.val)ˣ))

/-- A multiplier tuple hits the block at time `j` at every prime. -/
def rootBoxGlobalHit (P : Finset ℕ) (K j : ℕ)
    (h : RootBoxMultiplierTuple P) : Prop :=
  ∀ p : ↥P, localBlockHit p.val K j (h p)

/-- Global tuples hitting at one time, represented as the independent product
of local hit sets. -/
noncomputable def rootBoxGlobalHitSet
    (P : Finset ℕ) (K j : ℕ) (hprime : ∀ p ∈ P, p.Prime) :
    Finset (RootBoxMultiplierTuple P) := by
  classical
  letI (p : ↥P) : NeZero p.val := ⟨(hprime p.val p.property).ne_zero⟩
  exact Fintype.piFinset (fun p : ↥P ↦ localBlockHitSet p.val K j)

/-- Membership in the product hit set is exactly the global hit predicate. -/
theorem mem_rootBoxGlobalHitSet_iff
    (P : Finset ℕ) (K j : ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (h : RootBoxMultiplierTuple P) :
    h ∈ rootBoxGlobalHitSet P K j hprime ↔ rootBoxGlobalHit P K j h := by
  classical
  let (p : ↥P) : NeZero p.val := ⟨(hprime p.val p.property).ne_zero⟩
  unfold rootBoxGlobalHitSet rootBoxGlobalHit
  rw [Fintype.mem_piFinset]
  constructor
  · intro hh p
    exact (Finset.mem_filter.mp (hh p)).2
  · intro hh p
    simpa [localBlockHitSet, hh p]

/-- Number of positive hit times through `Y` for one multiplier tuple. -/
noncomputable def rootBoxTupleHitNumber
    (P : Finset ℕ) (K Y : ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (h : RootBoxMultiplierTuple P) : ℕ :=
  ((Icc 1 Y).filter (fun j ↦ h ∈ rootBoxGlobalHitSet P K j hprime)).card

/-- Actual unnormalized second moment over all CRT multiplier tuples. -/
noncomputable def rootBoxTupleSecondMoment
    (P : Finset ℕ) (K Y : ℕ) (hprime : ∀ p ∈ P, p.Prime) : ℕ :=
  ∑ h ∈ rootBoxMultiplierUniverse P hprime,
    (rootBoxTupleHitNumber P K Y hprime h) ^ 2

/-- Pair-incidence representation of the tuple second moment. -/
noncomputable def rootBoxTuplePairIncidence
    (P : Finset ℕ) (K Y : ℕ) (hprime : ∀ p ∈ P, p.Prime) : ℕ :=
  ∑ j ∈ Icc 1 Y, ∑ l ∈ Icc 1 Y,
    ((rootBoxMultiplierUniverse P hprime).filter (fun h ↦
      h ∈ rootBoxGlobalHitSet P K j hprime ∧
      h ∈ rootBoxGlobalHitSet P K l hprime)).card

/-- The two definitions of the actual second moment agree exactly. -/
theorem rootBoxTupleSecondMoment_eq_pairIncidence
    (P : Finset ℕ) (K Y : ℕ) (hprime : ∀ p ∈ P, p.Prime) :
    rootBoxTupleSecondMoment P K Y hprime =
      rootBoxTuplePairIncidence P K Y hprime := by
  classical
  unfold rootBoxTupleSecondMoment rootBoxTuplePairIncidence
  exact sum_hitCount_sq_eq_pairCount
    (rootBoxMultiplierUniverse P hprime) (Icc 1 Y)
    (fun h j ↦ h ∈ rootBoxGlobalHitSet P K j hprime)

/-- The tuple universe has cardinality `Φ=∏(p-1)`. -/
theorem card_rootBoxMultiplierUniverse
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime) :
    (rootBoxMultiplierUniverse P hprime).card = primeUnitCount P := by
  classical
  let (p : ↥P) : NeZero p.val := ⟨(hprime p.val p.property).ne_zero⟩
  unfold rootBoxMultiplierUniverse
  rw [Fintype.card_piFinset]
  calc
    (∏ p : ↥P, (Finset.univ : Finset (ZMod p.val)ˣ).card) =
      ∏ p : ↥P, primeUnitFactor p.val := by
        apply Fintype.prod_congr
        intro p
        rw [Finset.card_univ, ZMod.card_units_eq_totient,
          Nat.totient_prime (hprime p.val p.property)]
        rfl
    _ = primeUnitCount P := prod_primeSubtype_units_eq P

/-- The underlying one-equation condition on a residue pair attached to two
root labels.  This deliberately allows the local origin unless both labels
are zero. -/
def localUnderlyingPairCondition (p j l : ℕ) (ab : ℕ × ℕ) : Prop :=
  if ab.1 = 0 ∧ ab.2 = 0 then
    (j : ZMod p) = 0 ∧ (l : ZMod p) = 0
  else if ab.1 = 0 then
    (j : ZMod p) = 0
  else if ab.2 = 0 then
    (l : ZMod p) = 0
  else
    (ab.1 : ZMod p) * (l : ZMod p) =
      (ab.2 : ZMod p) * (j : ZMod p)

/-- Natural indicator of the underlying local pair congruence. -/
noncomputable def localUnderlyingPairIndicator
    (p j l : ℕ) (ab : ℕ × ℕ) : ℕ := by
  classical
  exact if localUnderlyingPairCondition p j l ab then 1 else 0

/-- Unit multipliers realizing two fixed root labels at two fixed times. -/
noncomputable def fixedLabelPairMultiplierSet
    (p j l : ℕ) [NeZero p] (ab : ℕ × ℕ) : Finset (ZMod p)ˣ := by
  classical
  exact Finset.univ.filter fun h ↦
    (h : ZMod p) * (j : ZMod p) + (ab.1 : ZMod p) = 0 ∧
    (h : ZMod p) * (l : ZMod p) + (ab.2 : ZMod p) = 0

/-- Fixed-label equations imply the corresponding underlying pair-lattice
condition. -/
theorem fixedLabelPairMultiplierSet_implies_condition
    {p j l : ℕ} [NeZero p] {ab : ℕ × ℕ} {h : (ZMod p)ˣ}
    (hh : h ∈ fixedLabelPairMultiplierSet p j l ab) :
    localUnderlyingPairCondition p j l ab := by
  classical
  have heq := (Finset.mem_filter.mp hh).2
  have cancel_unit (x : ZMod p) (hx : (h : ZMod p) * x = 0) : x = 0 := by
    calc
      x = (↑(h⁻¹) : ZMod p) * ((h : ZMod p) * x) := by simp
      _ = 0 := by rw [hx, mul_zero]
  by_cases ha0 : ab.1 = 0
  · by_cases hb0 : ab.2 = 0
    · simp only [localUnderlyingPairCondition, ha0, hb0, and_self, if_true]
      constructor
      · apply cancel_unit
        simpa [ha0] using heq.1
      · apply cancel_unit
        simpa [hb0] using heq.2
    · simp only [localUnderlyingPairCondition, ha0, hb0, and_false,
        if_false, if_true]
      apply cancel_unit
      simpa [ha0] using heq.1
  · by_cases hb0 : ab.2 = 0
    · simp only [localUnderlyingPairCondition, ha0, hb0, false_and,
        if_false, if_true]
      apply cancel_unit
      simpa [hb0] using heq.2
    · simp only [localUnderlyingPairCondition, ha0, hb0, false_and,
        if_false]
      have hj : (h : ZMod p) * (j : ZMod p) = -(ab.1 : ZMod p) :=
        eq_neg_of_add_eq_zero_left heq.1
      have hl : (h : ZMod p) * (l : ZMod p) = -(ab.2 : ZMod p) :=
        eq_neg_of_add_eq_zero_left heq.2
      calc
        (ab.1 : ZMod p) * (l : ZMod p) =
            -((h : ZMod p) * (j : ZMod p)) * (l : ZMod p) := by rw [hj]; ring
        _ = -((h : ZMod p) * (l : ZMod p)) * (j : ZMod p) := by ring
        _ = (ab.2 : ZMod p) * (j : ZMod p) := by rw [hl]; ring

/-- At nonzero labels, at most one unit multiplier realizes both fixed-label
equations. -/
theorem card_fixedLabelPairMultiplierSet_le_one
    {p K j l : ℕ} [NeZero p] (hp : p.Prime) {ab : ℕ × ℕ}
    (hab : ab ∈ allLabelPairs K) (hKp : K < p) (hab0 : ab ≠ (0, 0)) :
    (fixedLabelPairMultiplierSet p j l ab).card ≤ 1 := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  rw [Finset.card_le_one]
  intro h₁ hh₁ h₂ hh₂
  have heq₁ := (Finset.mem_filter.mp hh₁).2
  have heq₂ := (Finset.mem_filter.mp hh₂).2
  have habBounds := Finset.mem_product.mp hab
  have haK := Finset.mem_range.mp habBounds.1
  have hbK := Finset.mem_range.mp habBounds.2
  apply Units.ext
  by_cases ha0 : ab.1 = 0
  · have hb0 : ab.2 ≠ 0 := by
      intro hb0
      exact hab0 (Prod.ext ha0 hb0)
    have hbpos : 0 < ab.2 := Nat.pos_of_ne_zero hb0
    have hbmod : (ab.2 : ZMod p) ≠ 0 :=
      natCast_zmod_ne_zero_of_pos_of_lt hbpos (hbK.trans hKp)
    have hl0 : (l : ZMod p) ≠ 0 := by
      intro hl0
      have : (ab.2 : ZMod p) = 0 := by simpa [hl0] using heq₁.2
      exact hbmod this
    apply mul_right_cancel₀ hl0
    have e₁ : (h₁ : ZMod p) * (l : ZMod p) = -(ab.2 : ZMod p) :=
      eq_neg_of_add_eq_zero_left heq₁.2
    have e₂ : (h₂ : ZMod p) * (l : ZMod p) = -(ab.2 : ZMod p) :=
      eq_neg_of_add_eq_zero_left heq₂.2
    exact e₁.trans e₂.symm
  · have hapos : 0 < ab.1 := Nat.pos_of_ne_zero ha0
    have hamod : (ab.1 : ZMod p) ≠ 0 :=
      natCast_zmod_ne_zero_of_pos_of_lt hapos (haK.trans hKp)
    have hj0 : (j : ZMod p) ≠ 0 := by
      intro hj0
      have : (ab.1 : ZMod p) = 0 := by simpa [hj0] using heq₁.1
      exact hamod this
    apply mul_right_cancel₀ hj0
    have e₁ : (h₁ : ZMod p) * (j : ZMod p) = -(ab.1 : ZMod p) :=
      eq_neg_of_add_eq_zero_left heq₁.1
    have e₂ : (h₂ : ZMod p) * (j : ZMod p) = -(ab.1 : ZMod p) :=
      eq_neg_of_add_eq_zero_left heq₂.1
    exact e₁.trans e₂.symm

/-- A fixed label pair contributes at most its multiplier weight, and only
when its underlying pair-lattice congruence is satisfied. -/
theorem card_fixedLabelPairMultiplierSet_le_weight_indicator
    {p K j l : ℕ} [NeZero p] (hp : p.Prime) {ab : ℕ × ℕ}
    (hab : ab ∈ allLabelPairs K) (hKp : K < p) :
    (fixedLabelPairMultiplierSet p j l ab).card ≤
      pairMultiplierLocalWeight p ab *
        localUnderlyingPairIndicator p j l ab := by
  classical
  by_cases hcond : localUnderlyingPairCondition p j l ab
  · simp only [localUnderlyingPairIndicator, hcond, if_true, mul_one]
    by_cases hab0 : ab = (0, 0)
    · unfold pairMultiplierLocalWeight
      rw [if_pos hab0]
      calc
        (fixedLabelPairMultiplierSet p j l ab).card ≤
            (Finset.univ : Finset (ZMod p)ˣ).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
        _ = p - 1 := by
          rw [Finset.card_univ, ZMod.card_units_eq_totient,
            Nat.totient_prime hp]
    · simpa [pairMultiplierLocalWeight, hab0] using
        card_fixedLabelPairMultiplierSet_le_one hp hab hKp hab0
  · simp only [localUnderlyingPairIndicator, hcond, if_false, mul_zero]
    have hzero : (fixedLabelPairMultiplierSet p j l ab).card = 0 := by
      by_contra hne
      have hnonempty : (fixedLabelPairMultiplierSet p j l ab).Nonempty :=
        Finset.card_pos.mp (Nat.pos_of_ne_zero hne)
      obtain ⟨h, hh⟩ := hnonempty
      exact hcond (fixedLabelPairMultiplierSet_implies_condition hh)
    omega

/-- Local unit multipliers hitting the block at both times. -/
noncomputable def localBlockDoubleHitSet
    (p K j l : ℕ) [NeZero p] : Finset (ZMod p)ˣ := by
  classical
  exact (localBlockHitSet p K j).filter (fun h ↦ localBlockHit p K l h)

/-- Membership in the local double-hit set. -/
theorem mem_localBlockDoubleHitSet_iff
    {p K j l : ℕ} [NeZero p] {h : (ZMod p)ˣ} :
    h ∈ localBlockDoubleHitSet p K j l ↔
      localBlockHit p K j h ∧ localBlockHit p K l h := by
  classical
  simp [localBlockDoubleHitSet, localBlockHitSet]

/-- Every double hit is covered by some fixed pair of root labels. -/
theorem localBlockDoubleHitSet_subset_labelUnion
    (p K j l : ℕ) [NeZero p] :
    localBlockDoubleHitSet p K j l ⊆
      (allLabelPairs K).biUnion
        (fixedLabelPairMultiplierSet p j l) := by
  classical
  intro h hh
  have hh' : h ∈ (localBlockHitSet p K j).filter
      (fun h ↦ localBlockHit p K l h) := by
    simpa [localBlockDoubleHitSet] using hh
  have hh' := Finset.mem_filter.mp hh'
  have hjhit := (Finset.mem_filter.mp hh'.1).2
  obtain ⟨A, hAK, hAj⟩ := hjhit
  obtain ⟨B, hBK, hBl⟩ := hh'.2
  apply Finset.mem_biUnion.mpr
  refine ⟨(A, B), ?_, ?_⟩
  · exact Finset.mem_product.mpr ⟨hAK, hBK⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hAj, hBl⟩

/-- The local double-hit count is bounded by the weighted sum of underlying
label-pair congruence indicators. -/
theorem card_localBlockDoubleHitSet_le_label_sum
    {p K j l : ℕ} [NeZero p] (hp : p.Prime) (hKp : K < p) :
    (localBlockDoubleHitSet p K j l).card ≤
      ∑ ab ∈ allLabelPairs K,
        pairMultiplierLocalWeight p ab *
          localUnderlyingPairIndicator p j l ab := by
  classical
  calc
    (localBlockDoubleHitSet p K j l).card ≤
        ((allLabelPairs K).biUnion
          (fixedLabelPairMultiplierSet p j l)).card :=
      Finset.card_le_card (localBlockDoubleHitSet_subset_labelUnion p K j l)
    _ ≤ ∑ ab ∈ allLabelPairs K,
        (fixedLabelPairMultiplierSet p j l ab).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ ab ∈ allLabelPairs K,
        pairMultiplierLocalWeight p ab *
          localUnderlyingPairIndicator p j l ab := by
      apply Finset.sum_le_sum
      intro ab hab
      exact card_fixedLabelPairMultiplierSet_le_weight_indicator hp hab hKp

/-- Membership of a positive integer pair in a pair-state lattice is exactly
the conjunction of its local underlying label congruences. -/
theorem natPair_mem_pairStateLattice_iff
    (P : Finset ℕ) (f : ∀ _p : ↥P, ℕ × ℕ) (j l : ℕ) :
    ![(j : ℤ), (l : ℤ)] ∈ pairStateLattice P f ↔
      ∀ p : ↥P, localUnderlyingPairCondition p.val j l (f p) := by
  classical
  let F := pairStateZeroPrimes P f
  let a := globalLabelFirst P f
  let b := globalLabelSecond P f
  let hFP : F ⊆ P := Finset.filter_subset _ _
  constructor
  · intro hx p
    have hker : globalForcedPairEquationLinear P F a b hFP
        ![(j : ℤ), (l : ℤ)] = 0 := by
      exact LinearMap.mem_ker.mp hx
    have hfirst := congrArg
      (fun y : ForcedPairEquationSpace P F ↦ y.1 p) hker
    dsimp [globalForcedPairEquationLinear, forcedPairEquationLinear,
      pairCRTLinear, zmodPiLinear] at hfirst
    simp only [Int.cast_natCast] at hfirst
    change (if p.val ∈ F then (j : ZMod p.val)
      else if a p.val = 0 then (j : ZMod p.val)
      else if b p.val = 0 then (l : ZMod p.val)
      else (a p.val : ZMod p.val) * (l : ZMod p.val) -
        (b p.val : ZMod p.val) * (j : ZMod p.val)) = 0 at hfirst
    by_cases hz : f p = (0, 0)
    · have hpF : p.val ∈ F := by
        dsimp [F]
        exact (mem_pairStateZeroPrimes_iff P f p.property).mpr hz
      let pf : {r // r ∈ F} := ⟨p.val, hpF⟩
      have hsecond := congrArg
        (fun y : ForcedPairEquationSpace P F ↦ y.2 pf) hker
      dsimp [globalForcedPairEquationLinear, forcedPairEquationLinear,
        pairCRTLinear, zmodPiLinear] at hsecond
      simp only [Int.cast_natCast] at hsecond
      change (l : ZMod p.val) = 0 at hsecond
      have ha0 : (f p).1 = 0 := congrArg Prod.fst hz
      have hb0 : (f p).2 = 0 := congrArg Prod.snd hz
      have hj0 : (j : ZMod p.val) = 0 := by
        simpa [hpF] using hfirst
      simpa [localUnderlyingPairCondition, ha0, hb0] using
        And.intro hj0 hsecond
    · have hpF : p.val ∉ F := by
        intro hp
        exact hz ((mem_pairStateZeroPrimes_iff P f p.property).mp hp)
      have ha : a p.val = (f p).1 := globalLabelFirst_at P f p.property
      have hb : b p.val = (f p).2 := globalLabelSecond_at P f p.property
      rw [if_neg hpF, ha, hb] at hfirst
      by_cases ha0 : (f p).1 = 0
      · have hb0 : (f p).2 ≠ 0 := by
          intro hb0
          exact hz (Prod.ext ha0 hb0)
        simpa [localUnderlyingPairCondition, ha0, hb0] using hfirst
      · by_cases hb0 : (f p).2 = 0
        · simpa [localUnderlyingPairCondition, ha0, hb0] using hfirst
        · simp only [ha0, hb0, if_false] at hfirst
          have hrel : (f p).1 * (l : ZMod p.val) =
              (f p).2 * (j : ZMod p.val) := sub_eq_zero.mp hfirst
          simpa [localUnderlyingPairCondition, ha0, hb0] using hrel
  · intro hall
    apply LinearMap.mem_ker.mpr
    change globalForcedPairEquationLinear P F a b hFP
      ![(j : ℤ), (l : ℤ)] = 0
    apply Prod.ext
    · funext p
      dsimp [globalForcedPairEquationLinear, forcedPairEquationLinear,
        pairCRTLinear, zmodPiLinear]
      simp only [Int.cast_natCast]
      change (if p.val ∈ F then (j : ZMod p.val)
        else if a p.val = 0 then (j : ZMod p.val)
        else if b p.val = 0 then (l : ZMod p.val)
        else (a p.val : ZMod p.val) * (l : ZMod p.val) -
          (b p.val : ZMod p.val) * (j : ZMod p.val)) = 0
      have hc := hall p
      by_cases hz : f p = (0, 0)
      · have hpF : p.val ∈ F := by
          dsimp [F]
          exact (mem_pairStateZeroPrimes_iff P f p.property).mpr hz
        have ha0 : (f p).1 = 0 := congrArg Prod.fst hz
        have hb0 : (f p).2 = 0 := congrArg Prod.snd hz
        have hc' : (j : ZMod p.val) = 0 ∧ (l : ZMod p.val) = 0 := by
          simpa [localUnderlyingPairCondition, ha0, hb0] using hc
        simp [hpF, hc'.1]
      · have hpF : p.val ∉ F := by
          intro hp
          exact hz ((mem_pairStateZeroPrimes_iff P f p.property).mp hp)
        have ha : a p.val = (f p).1 := globalLabelFirst_at P f p.property
        have hb : b p.val = (f p).2 := globalLabelSecond_at P f p.property
        rw [if_neg hpF, ha, hb]
        by_cases ha0 : (f p).1 = 0
        · have hb0 : (f p).2 ≠ 0 := by
            intro hb0
            exact hz (Prod.ext ha0 hb0)
          have hc' : (j : ZMod p.val) = 0 := by
            simpa [localUnderlyingPairCondition, ha0, hb0] using hc
          simp [ha0, hc']
        · by_cases hb0 : (f p).2 = 0
          · have hc' : (l : ZMod p.val) = 0 := by
              simpa [localUnderlyingPairCondition, ha0, hb0] using hc
            simp [ha0, hb0, hc']
          · have hc' : (f p).1 * (l : ZMod p.val) =
                (f p).2 * (j : ZMod p.val) := by
              simpa [localUnderlyingPairCondition, ha0, hb0] using hc
            simp [ha0, hb0, hc']
    · funext p
      dsimp [globalForcedPairEquationLinear, forcedPairEquationLinear,
        pairCRTLinear, zmodPiLinear]
      simp only [Int.cast_natCast]
      let pp : ↥P := forcedPrimeIncl hFP p
      have hpF : pp.val ∈ F := p.property
      have hz : f pp = (0, 0) :=
        (mem_pairStateZeroPrimes_iff P f pp.property).mp hpF
      have ha0 : (f pp).1 = 0 := congrArg Prod.fst hz
      have hb0 : (f pp).2 = 0 := congrArg Prod.snd hz
      have hc := hall pp
      have hc' : (j : ZMod pp.val) = 0 ∧ (l : ZMod pp.val) = 0 := by
        simpa [localUnderlyingPairCondition, ha0, hb0] using hc
      change (l : ZMod p.val) = 0
      exact hc'.2

/-- The product of local congruence indicators is the global pair-state
lattice-membership indicator. -/
theorem prod_localUnderlyingPairIndicator_eq_latticeIndicator
    (P : Finset ℕ) (f : ∀ _p : ↥P, ℕ × ℕ) (j l : ℕ) :
    (∏ p : ↥P,
      localUnderlyingPairIndicator p.val j l (f p)) =
      latticeMembershipIndicator (pairStateLattice P f)
        ![(j : ℤ), (l : ℤ)] := by
  classical
  by_cases hx : ![(j : ℤ), (l : ℤ)] ∈ pairStateLattice P f
  · have hall := (natPair_mem_pairStateLattice_iff P f j l).mp hx
    unfold latticeMembershipIndicator
    rw [if_pos hx]
    apply Finset.prod_eq_one
    intro p hp
    simp [localUnderlyingPairIndicator, hall p]
  · have hnotall : ¬ ∀ p : ↥P,
        localUnderlyingPairCondition p.val j l (f p) := by
      intro hall
      exact hx ((natPair_mem_pairStateLattice_iff P f j l).mpr hall)
    push Not at hnotall
    obtain ⟨p, hp⟩ := hnotall
    unfold latticeMembershipIndicator
    rw [if_neg hx]
    apply Finset.prod_eq_zero (Finset.mem_univ p)
    simp [localUnderlyingPairIndicator, hp]

/-- Product of the one-prime double-hit sets. -/
noncomputable def rootBoxGlobalDoubleHitSet
    (P : Finset ℕ) (K j l : ℕ) (hprime : ∀ p ∈ P, p.Prime) :
    Finset (RootBoxMultiplierTuple P) := by
  classical
  letI (p : ↥P) : NeZero p.val := ⟨(hprime p.val p.property).ne_zero⟩
  exact Fintype.piFinset (fun p : ↥P ↦
    @localBlockDoubleHitSet p.val K j l
      ⟨(hprime p.val p.property).ne_zero⟩)

/-- Membership in the global double-hit product is coordinatewise. -/
theorem mem_rootBoxGlobalDoubleHitSet_iff
    (P : Finset ℕ) (K j l : ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (h : RootBoxMultiplierTuple P) :
    h ∈ rootBoxGlobalDoubleHitSet P K j l hprime ↔
      ∀ p : ↥P, h p ∈ @localBlockDoubleHitSet p.val K j l
        ⟨(hprime p.val p.property).ne_zero⟩ := by
  classical
  unfold rootBoxGlobalDoubleHitSet
  rw [Fintype.mem_piFinset]

/-- Filtering the full tuple universe by two global hit events gives exactly
the independent product of the local double-hit sets. -/
theorem filter_rootBoxMultiplierUniverse_doubleHit_eq
    (P : Finset ℕ) (K j l : ℕ) (hprime : ∀ p ∈ P, p.Prime) :
    (rootBoxMultiplierUniverse P hprime).filter (fun h ↦
      h ∈ rootBoxGlobalHitSet P K j hprime ∧
      h ∈ rootBoxGlobalHitSet P K l hprime) =
      rootBoxGlobalDoubleHitSet P K j l hprime := by
  classical
  let (p : ↥P) : NeZero p.val := ⟨(hprime p.val p.property).ne_zero⟩
  ext h
  constructor
  · intro hh
    have hh' := (Finset.mem_filter.mp hh).2
    have hj := (mem_rootBoxGlobalHitSet_iff P K j hprime h).mp hh'.1
    have hl := (mem_rootBoxGlobalHitSet_iff P K l hprime h).mp hh'.2
    apply (mem_rootBoxGlobalDoubleHitSet_iff P K j l hprime h).mpr
    intro p
    exact mem_localBlockDoubleHitSet_iff.mpr ⟨hj p, hl p⟩
  · intro hh
    have hlocal : ∀ p : ↥P,
        h p ∈ @localBlockDoubleHitSet p.val K j l
          ⟨(hprime p.val p.property).ne_zero⟩ :=
      (mem_rootBoxGlobalDoubleHitSet_iff P K j l hprime h).mp hh
    apply Finset.mem_filter.mpr
    constructor
    · unfold rootBoxMultiplierUniverse
      apply Fintype.mem_piFinset.mpr
      intro p
      exact Finset.mem_univ _
    · constructor
      · apply (mem_rootBoxGlobalHitSet_iff P K j hprime h).mpr
        intro p
        exact (mem_localBlockDoubleHitSet_iff.mp (hlocal p)).1
      · apply (mem_rootBoxGlobalHitSet_iff P K l hprime h).mpr
        intro p
        exact (mem_localBlockDoubleHitSet_iff.mp (hlocal p)).2

/-- The global double-hit set cardinality factors into its local
cardinalities. -/
theorem card_rootBoxGlobalDoubleHitSet
    (P : Finset ℕ) (K j l : ℕ) (hprime : ∀ p ∈ P, p.Prime) :
    (rootBoxGlobalDoubleHitSet P K j l hprime).card =
      ∏ p : ↥P, (@localBlockDoubleHitSet p.val K j l
        ⟨(hprime p.val p.property).ne_zero⟩).card := by
  classical
  let (p : ↥P) : NeZero p.val := ⟨(hprime p.val p.property).ne_zero⟩
  unfold rootBoxGlobalDoubleHitSet
  exact Fintype.card_piFinset _

/-- For each pair of times, the number of multiplier tuples hitting at both
is bounded by the weighted count of the corresponding pair-state lattices. -/
theorem card_rootBox_doubleHit_le_pairStateIndicators
    (P : Finset ℕ) (K j l : ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (hKp : ∀ p ∈ P, K < p) :
    ((rootBoxMultiplierUniverse P hprime).filter (fun h ↦
      h ∈ rootBoxGlobalHitSet P K j hprime ∧
      h ∈ rootBoxGlobalHitSet P K l hprime)).card ≤
      ∑ f ∈ globalLabelPairs P K,
        pairMultiplierGlobalWeight P f *
          latticeMembershipIndicator (pairStateLattice P f)
            ![(j : ℤ), (l : ℤ)] := by
  classical
  let (p : ↥P) : NeZero p.val := ⟨(hprime p.val p.property).ne_zero⟩
  rw [filter_rootBoxMultiplierUniverse_doubleHit_eq,
    card_rootBoxGlobalDoubleHitSet]
  calc
    (∏ p : ↥P, (@localBlockDoubleHitSet p.val K j l
      ⟨(hprime p.val p.property).ne_zero⟩).card) ≤
        ∏ p : ↥P, ∑ ab ∈ allLabelPairs K,
          pairMultiplierLocalWeight p.val ab *
            localUnderlyingPairIndicator p.val j l ab := by
      apply Finset.prod_le_prod
      · intro p hp
        positivity
      · intro p hp
        exact card_localBlockDoubleHitSet_le_label_sum
          (hprime p.val p.property) (hKp p.val p.property)
    _ = ∑ f ∈ globalLabelPairs P K,
        ∏ p : ↥P,
          (pairMultiplierLocalWeight p.val (f p) *
            localUnderlyingPairIndicator p.val j l (f p)) := by
      unfold globalLabelPairs
      exact Finset.prod_univ_sum
        (fun _p : ↥P ↦ allLabelPairs K)
        (fun p ab ↦ pairMultiplierLocalWeight p.val ab *
          localUnderlyingPairIndicator p.val j l ab)
    _ = ∑ f ∈ globalLabelPairs P K,
        pairMultiplierGlobalWeight P f *
          latticeMembershipIndicator (pairStateLattice P f)
            ![(j : ℤ), (l : ℤ)] := by
      apply Finset.sum_congr rfl
      intro f hf
      rw [Finset.prod_mul_distrib,
        prod_localUnderlyingPairIndicator_eq_latticeIndicator]
      rfl

/-- Summing the pointwise double-hit bound gives a natural-valued upper bound
for the actual tuple second moment by all positive pair-state lattice points. -/
theorem rootBoxTupleSecondMoment_le_pairLatticeSumNat
    (P : Finset ℕ) (K Y : ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (hKp : ∀ p ∈ P, K < p) :
    rootBoxTupleSecondMoment P K Y hprime ≤
      ∑ f ∈ globalLabelPairs P K,
        pairMultiplierGlobalWeight P f *
          (latticePositiveSquare (pairStateLattice P f) Y).card := by
  classical
  rw [rootBoxTupleSecondMoment_eq_pairIncidence]
  unfold rootBoxTuplePairIncidence
  calc
    (∑ j ∈ Icc 1 Y, ∑ l ∈ Icc 1 Y,
      ((rootBoxMultiplierUniverse P hprime).filter (fun h ↦
        h ∈ rootBoxGlobalHitSet P K j hprime ∧
        h ∈ rootBoxGlobalHitSet P K l hprime)).card) ≤
      ∑ j ∈ Icc 1 Y, ∑ l ∈ Icc 1 Y,
        ∑ f ∈ globalLabelPairs P K,
          pairMultiplierGlobalWeight P f *
            latticeMembershipIndicator (pairStateLattice P f)
              ![(j : ℤ), (l : ℤ)] := by
        apply Finset.sum_le_sum
        intro j hj
        apply Finset.sum_le_sum
        intro l hl
        exact card_rootBox_doubleHit_le_pairStateIndicators
          P K j l hprime hKp
    _ = ∑ j ∈ Icc 1 Y, ∑ f ∈ globalLabelPairs P K,
        ∑ l ∈ Icc 1 Y,
          pairMultiplierGlobalWeight P f *
            latticeMembershipIndicator (pairStateLattice P f)
              ![(j : ℤ), (l : ℤ)] := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_comm]
    _ = ∑ f ∈ globalLabelPairs P K, ∑ j ∈ Icc 1 Y,
        ∑ l ∈ Icc 1 Y,
          pairMultiplierGlobalWeight P f *
            latticeMembershipIndicator (pairStateLattice P f)
              ![(j : ℤ), (l : ℤ)] := by
      rw [Finset.sum_comm]
    _ = ∑ f ∈ globalLabelPairs P K,
        pairMultiplierGlobalWeight P f *
          (latticePositiveSquare (pairStateLattice P f) Y).card := by
      apply Finset.sum_congr rfl
      intro f hf
      rw [latticePositiveSquare_card_eq_sum_indicator,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum]

/-- Real form of the actual-to-origin-ignored pair-lattice comparison. -/
theorem rootBoxTupleSecondMoment_le_pairLatticeWeightedSquareSum
    (P : Finset ℕ) (K Y : ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (hKp : ∀ p ∈ P, K < p) :
    (rootBoxTupleSecondMoment P K Y hprime : ℝ) ≤
      pairLatticeWeightedSquareSum P K Y := by
  have hnat := rootBoxTupleSecondMoment_le_pairLatticeSumNat
    P K Y hprime hKp
  unfold pairLatticeWeightedSquareSum
  exact_mod_cast hnat

/-- Complete explicit upper bound for the normalized actual CRT root-box
second moment. -/
theorem normalized_rootBoxTupleSecondMoment_le
    (P : Finset ℕ) (K Y Z : ℕ) (hK : 1 < K) (hZ : 1 ≤ Z)
    (hprime : ∀ p ∈ P, p.Prime)
    (hKp : ∀ p ∈ P, K < p) (hK2p : ∀ p ∈ P, K * K < p)
    (hlarge : ∀ p ∈ P, Z ^ (K * K) ≤ p)
    (hZp : ∀ p ∈ P, Z ≤ p) (hZ2p : ∀ p ∈ P, Z * Z ≤ p) :
    (rootBoxTupleSecondMoment P K Y hprime : ℝ) /
        (primeUnitCount P : ℝ) ≤
      (Y : ℝ) ^ 2 *
        ((((K * K) ^ P.card : ℕ) : ℝ) /
          (primeProduct P : ℝ) ^ 2 *
          ∏ p ∈ P,
            (1 + ((K * K - 1 : ℕ) : ℝ) /
              (((K * K : ℕ) : ℝ) * ((p - 1 : ℕ) : ℝ)))) +
      40 * (K * K - 1 : ℕ) *
        ((Y : ℝ) * ((K ^ P.card : ℕ) : ℝ) /
          (primeProduct P : ℝ) *
          ∏ p ∈ P,
            (1 + (2 * (K * K - 1 : ℕ) : ℝ) /
              ((K : ℝ) * ((p : ℝ) - 1)))) +
      80 * (K : ℝ) * (Y : ℝ) *
        ((1 / (primeProduct P : ℝ)) *
          ∏ _p ∈ P,
            (1 + 4 * ((K * K - 1 : ℕ) : ℝ) / (Z : ℝ))) +
      44 * ∏ _p ∈ P,
        (1 + 4 * ((K * K - 1 : ℕ) : ℝ) /
          ((Z * Z : ℕ) : ℝ)) := by
  have hphi : (0 : ℝ) < primeUnitCount P := by
    exact_mod_cast (show 0 < primeUnitCount P by
      unfold primeUnitCount
      exact Finset.prod_pos fun p hp ↦ by
        have hp2 := (hprime p hp).two_le
        omega)
  have hbridge := rootBoxTupleSecondMoment_le_pairLatticeWeightedSquareSum
    P K Y hprime hKp
  have hdiv : (rootBoxTupleSecondMoment P K Y hprime : ℝ) /
        (primeUnitCount P : ℝ) ≤
      pairLatticeWeightedSquareSum P K Y /
        (primeUnitCount P : ℝ) :=
    (div_le_div_iff_of_pos_right hphi).mpr hbridge
  exact hdiv.trans (normalized_pairLatticeWeightedSquareSum_le
    P K Y Z hK hZ hprime hKp hK2p hlarge hZp hZ2p)

end Erdos394
