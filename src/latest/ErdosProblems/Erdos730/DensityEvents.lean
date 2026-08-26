/- leanprover/lean4:v4.33.0  mathlib db584cd6 (master, the commit the v4.33.0 tag is cut from) -/
import ErdosProblems.Erdos730.ConsecutiveTransition
import ErdosProblems.Erdos730.FullDensityCore

/-!
# Erdős 730: finite bad-event accounting

This module turns the pointwise consecutive-support transition theorem into
the finite counting statement used by the density proof.  All parameter and
witness collections are honest `Finset`s.  In particular, the obstruction
count is a count of fully witnessed quadruples `(x,p,a,c)`, not merely a
count of parameters for which an unspecified witness exists.

No analytic estimate is asserted here.  The final theorem is only the exact
finite union bound `Bad(X) ≤ E_drop(X) + E_entry(X)`.
-/

namespace Erdos730
namespace DensityEvents

open ConsecutiveTransition FullDensityCore

noncomputable section

/-! ## Finite parameter sets -/

/-- The paper's parameter interval `1 ≤ x ≤ X`. -/
def parameterRange (X : ℕ) : Finset ℕ := Finset.Icc 1 X

/-- Good parameters in the paper family up to `X`. -/
def goodParametersUpTo (X : ℕ) : Finset ℕ :=
  by
    classical
    exact (parameterRange X).filter GoodParameter

/-- Bad parameters in the paper family up to `X`. -/
def badParametersUpTo (X : ℕ) : Finset ℕ :=
  by
    classical
    exact (parameterRange X).filter fun x => ¬GoodParameter x

@[simp] theorem mem_parameterRange {X x : ℕ} :
    x ∈ parameterRange X ↔ 1 ≤ x ∧ x ≤ X := by
  simp [parameterRange]

@[simp] theorem mem_goodParametersUpTo {X x : ℕ} :
    x ∈ goodParametersUpTo X ↔ x ∈ parameterRange X ∧ GoodParameter x := by
  simp [goodParametersUpTo]

@[simp] theorem mem_badParametersUpTo {X x : ℕ} :
    x ∈ badParametersUpTo X ↔ x ∈ parameterRange X ∧ ¬GoodParameter x := by
  simp [badParametersUpTo]

theorem good_bad_disjoint (X : ℕ) :
    Disjoint (goodParametersUpTo X) (badParametersUpTo X) := by
  rw [Finset.disjoint_left]
  intro x hxgood hxbad
  exact (mem_badParametersUpTo.mp hxbad).2
    (mem_goodParametersUpTo.mp hxgood).2

theorem good_union_bad (X : ℕ) :
    goodParametersUpTo X ∪ badParametersUpTo X = parameterRange X := by
  classical
  ext x
  constructor
  · intro hx
    rcases Finset.mem_union.mp hx with hxgood | hxbad
    · exact (mem_goodParametersUpTo.mp hxgood).1
    · exact (mem_badParametersUpTo.mp hxbad).1
  · intro hx
    by_cases hgood : GoodParameter x
    · exact Finset.mem_union_left _ (mem_goodParametersUpTo.mpr ⟨hx, hgood⟩)
    · exact Finset.mem_union_right _ (mem_badParametersUpTo.mpr ⟨hx, hgood⟩)

theorem parameterRange_card (X : ℕ) : (parameterRange X).card = X := by
  simp [parameterRange]

theorem good_card_add_bad_card (X : ℕ) :
    (goodParametersUpTo X).card + (badParametersUpTo X).card = X := by
  rw [← Finset.card_union_of_disjoint (good_bad_disjoint X), good_union_bad,
    parameterRange_card]

/-! ## Fully witnessed finite obstruction sets -/

/-- A nested product representation of the quadruple `(x,p,a,c)`. -/
abbrev ObstructionWitness := ℕ × (ℕ × (ℕ × ℕ))

def witnessParameter (w : ObstructionWitness) : ℕ := w.1
def witnessPrime (w : ObstructionWitness) : ℕ := w.2.1
def witnessExponent (w : ObstructionWitness) : ℕ := w.2.2.1
def witnessCofactor (w : ObstructionWitness) : ℕ := w.2.2.2

/-- A uniform exclusive upper bound for every coordinate other than `x`.
For `x ≤ X`, both possible transition factors are strictly below this
number. -/
def witnessBound (X : ℕ) : ℕ := 2 * n X + 2

/-- The finite box in which all obstruction witnesses for `x ≤ X` live. -/
def witnessBox (X : ℕ) : Finset ObstructionWitness :=
  (parameterRange X).product
    ((Finset.range (witnessBound X)).product
      ((Finset.range (witnessBound X)).product
        (Finset.range (witnessBound X))))

/-- Fully witnessed drop obstructions `(x,p,a,c)` up to `X`. -/
def dropWitnessesUpTo (X : ℕ) : Finset ObstructionWitness :=
  by
    classical
    exact (witnessBox X).filter fun w =>
      DropObstruction (n (witnessParameter w))
        (witnessPrime w) (witnessExponent w) (witnessCofactor w)

/-- Fully witnessed entry obstructions `(x,p,a,c)` up to `X`. -/
def entryWitnessesUpTo (X : ℕ) : Finset ObstructionWitness :=
  by
    classical
    exact (witnessBox X).filter fun w =>
      EntryObstruction (n (witnessParameter w))
        (witnessPrime w) (witnessExponent w) (witnessCofactor w)

/-- Parameters hit by at least one witnessed drop obstruction. -/
def dropParametersUpTo (X : ℕ) : Finset ℕ :=
  (dropWitnessesUpTo X).image witnessParameter

/-- Parameters hit by at least one witnessed entry obstruction. -/
def entryParametersUpTo (X : ℕ) : Finset ℕ :=
  (entryWitnessesUpTo X).image witnessParameter

@[simp] theorem mem_witnessBox {X : ℕ} {w : ObstructionWitness} :
    w ∈ witnessBox X ↔
      w.1 ∈ parameterRange X ∧
      w.2.1 < witnessBound X ∧
      w.2.2.1 < witnessBound X ∧
      w.2.2.2 < witnessBound X := by
  simp [witnessBox]

@[simp] theorem mem_dropWitnessesUpTo {X : ℕ} {w : ObstructionWitness} :
    w ∈ dropWitnessesUpTo X ↔
      w ∈ witnessBox X ∧
      DropObstruction (n (witnessParameter w))
        (witnessPrime w) (witnessExponent w) (witnessCofactor w) := by
  simp [dropWitnessesUpTo]

@[simp] theorem mem_entryWitnessesUpTo {X : ℕ} {w : ObstructionWitness} :
    w ∈ entryWitnessesUpTo X ↔
      w ∈ witnessBox X ∧
      EntryObstruction (n (witnessParameter w))
        (witnessPrime w) (witnessExponent w) (witnessCofactor w) := by
  simp [entryWitnessesUpTo]

/-- Every field of an exact prime-power cofactor witness is bounded by the
factor being decomposed. -/
theorem exactPrimePowerCofactor_coordinate_bounds
    {p a c N : ℕ} (hp : p.Prime)
    (h : ExactPrimePowerCofactor p a c N) :
    p ≤ N ∧ a ≤ N ∧ c ≤ N := by
  rcases h with ⟨ha, hN, hpc⟩
  have hc : 0 < c := by
    apply Nat.pos_of_ne_zero
    intro hc0
    subst c
    exact hpc (dvd_zero p)
  have hpow : 0 < p ^ a := pow_pos hp.pos a
  constructor
  · calc
      p ≤ p ^ a := Nat.le_pow ha
      _ ≤ p ^ a * c := Nat.le_mul_of_pos_right _ hc
      _ = N := hN.symm
  constructor
  · calc
      a ≤ p ^ a := (Nat.lt_pow_self hp.one_lt).le
      _ ≤ p ^ a * c := Nat.le_mul_of_pos_right _ hc
      _ = N := hN.symm
  · calc
      c ≤ p ^ a * c := Nat.le_mul_of_pos_left _ hpow
      _ = N := hN.symm

theorem n_mono {x X : ℕ} (hx : x ≤ X) : n x ≤ n X :=
  n_strictMono.monotone hx

theorem drop_factor_lt_witnessBound {x X : ℕ} (hx : x ≤ X) :
    n x + 1 < witnessBound X := by
  have hmono := n_mono hx
  simp only [witnessBound]
  omega

theorem entry_factor_lt_witnessBound {x X : ℕ} (hx : x ≤ X) :
    2 * n x + 1 < witnessBound X := by
  have hmono := n_mono hx
  simp only [witnessBound]
  omega

/-- A pointwise drop obstruction supplied by Proposition 1 belongs to the
finite witnessed drop set. -/
theorem dropWitness_mem
    {X x p a c : ℕ} (hx : x ∈ parameterRange X)
    (hobs : DropObstruction (n x) p a c) :
    (x, (p, (a, c))) ∈ dropWitnessesUpTo X := by
  rcases hobs with ⟨hp, hp2, hexact, hlow⟩
  have hb := drop_factor_lt_witnessBound (mem_parameterRange.mp hx).2
  rcases exactPrimePowerCofactor_coordinate_bounds hp hexact with
    ⟨hpN, haN, hcN⟩
  rw [mem_dropWitnessesUpTo]
  refine ⟨?_, hp, hp2, hexact, hlow⟩
  rw [mem_witnessBox]
  exact ⟨hx, hpN.trans_lt hb, haN.trans_lt hb, hcN.trans_lt hb⟩

/-- A pointwise entry obstruction supplied by Proposition 1 belongs to the
finite witnessed entry set. -/
theorem entryWitness_mem
    {X x p a c : ℕ} (hx : x ∈ parameterRange X)
    (hobs : EntryObstruction (n x) p a c) :
    (x, (p, (a, c))) ∈ entryWitnessesUpTo X := by
  rcases hobs with ⟨hp, hp2, hexact, hlow⟩
  have hb := entry_factor_lt_witnessBound (mem_parameterRange.mp hx).2
  rcases exactPrimePowerCofactor_coordinate_bounds hp hexact with
    ⟨hpN, haN, hcN⟩
  rw [mem_entryWitnessesUpTo]
  refine ⟨?_, hp, hp2, hexact, hlow⟩
  rw [mem_witnessBox]
  exact ⟨hx, hpN.trans_lt hb, haN.trans_lt hb, hcN.trans_lt hb⟩

theorem prime_dvd_factor_of_exactPrimePowerCofactor
    {p a c N : ℕ} (h : ExactPrimePowerCofactor p a c N) : p ∣ N := by
  rcases h with ⟨ha, hN, _hpc⟩
  rw [hN]
  exact dvd_mul_of_dvd_left (dvd_pow_self p ha.ne') c

/-- The same quadruple cannot be both a drop and an entry witness: its prime
would divide the coprime factors `n+1` and `2n+1`. -/
theorem drop_entry_witnesses_disjoint (X : ℕ) :
    Disjoint (dropWitnessesUpTo X) (entryWitnessesUpTo X) := by
  rw [Finset.disjoint_left]
  intro w hdrop hentry
  rcases w with ⟨x, ⟨p, ⟨a, c⟩⟩⟩
  rcases (mem_dropWitnessesUpTo.mp hdrop).2 with
    ⟨hp, _hp2, hexactDrop, _hlowDrop⟩
  rcases (mem_entryWitnessesUpTo.mp hentry).2 with
    ⟨_hp, _hp2, hexactEntry, _hlowEntry⟩
  have hpDrop : p ∣ n x + 1 :=
    prime_dvd_factor_of_exactPrimePowerCofactor hexactDrop
  have hpEntry : p ∣ 2 * n x + 1 :=
    prime_dvd_factor_of_exactPrimePowerCofactor hexactEntry
  exact (not_dvd_two_mul_add_one_of_dvd_succ hp hpDrop) hpEntry

/-! ## Pointwise coverage and the finite union bound -/

/-- Every bad paper-family parameter up to `X` is hit by a witnessed drop
or entry event. -/
theorem bad_mem_dropParameters_or_entryParameters
    {X x : ℕ} (hx : x ∈ badParametersUpTo X) :
    x ∈ dropParametersUpTo X ∨ x ∈ entryParametersUpTo X := by
  rcases mem_badParametersUpTo.mp hx with ⟨hxrange, hnotgood⟩
  have hxone : 1 ≤ x := (mem_parameterRange.mp hxrange).1
  have hbad :
      (n x).centralBinom.primeFactors ≠
        (n x + 1).centralBinom.primeFactors := by
    intro heq
    exact hnotgood ⟨hxone, heq⟩
  have hnpos : 0 < n x := by
    rw [n_expansion]
    omega
  rcases exists_obstruction_of_primeFactors_ne hnpos hbad with
    ⟨p, a, c, hdrop⟩ | ⟨p, a, c, hentry⟩
  · left
    rw [dropParametersUpTo, Finset.mem_image]
    exact ⟨(x, (p, (a, c))), dropWitness_mem hxrange hdrop, rfl⟩
  · right
    rw [entryParametersUpTo, Finset.mem_image]
    exact ⟨(x, (p, (a, c))), entryWitness_mem hxrange hentry, rfl⟩

theorem bad_subset_drop_union_entry (X : ℕ) :
    badParametersUpTo X ⊆ dropParametersUpTo X ∪ entryParametersUpTo X := by
  intro x hx
  exact Finset.mem_union.mpr (bad_mem_dropParameters_or_entryParameters hx)

/-- Parameter-level finite union bound. -/
theorem bad_card_le_dropParameters_add_entryParameters (X : ℕ) :
    (badParametersUpTo X).card ≤
      (dropParametersUpTo X).card + (entryParametersUpTo X).card := by
  exact (Finset.card_le_card (bad_subset_drop_union_entry X)).trans
    (Finset.card_union_le _ _)

theorem dropParameters_card_le_dropWitnesses_card (X : ℕ) :
    (dropParametersUpTo X).card ≤ (dropWitnessesUpTo X).card := by
  exact Finset.card_image_le

theorem entryParameters_card_le_entryWitnesses_card (X : ℕ) :
    (entryParametersUpTo X).card ≤ (entryWitnessesUpTo X).card := by
  exact Finset.card_image_le

/-- **Exact finite form of equation (22).**  The number of bad parameters
is at most the number of witnessed drop quadruples plus the number of
witnessed entry quadruples. -/
theorem bad_card_le_witnessed_obstruction_count (X : ℕ) :
    (badParametersUpTo X).card ≤
      (dropWitnessesUpTo X).card + (entryWitnessesUpTo X).card := by
  exact (bad_card_le_dropParameters_add_entryParameters X).trans
    (Nat.add_le_add (dropParameters_card_le_dropWitnesses_card X)
      (entryParameters_card_le_entryWitnesses_card X))

/-! ## Exact four-range partition

The analytic proof later chooses the two cutoffs to be `sqrt X` and
`sqrt X * (log X)^2`.  Here they remain arbitrary natural numbers.  This
section proves only the finite, disjoint classification and makes no claim
about the size of any part.
-/

/-- All witnessed transition obstructions, with duplicates between the two
event types removed. -/
def obstructionWitnessesUpTo (X : ℕ) : Finset ObstructionWitness :=
  dropWitnessesUpTo X ∪ entryWitnessesUpTo X

theorem obstructionWitnesses_card_eq_drop_add_entry (X : ℕ) :
    (obstructionWitnessesUpTo X).card =
      (dropWitnessesUpTo X).card + (entryWitnessesUpTo X).card := by
  rw [obstructionWitnessesUpTo,
    Finset.card_union_of_disjoint (drop_entry_witnesses_disjoint X)]

/-- Equation (22) with `E(X)` represented by the single finite obstruction
witness set. -/
theorem bad_card_le_obstructionWitnesses_card (X : ℕ) :
    (badParametersUpTo X).card ≤ (obstructionWitnessesUpTo X).card := by
  rw [obstructionWitnesses_card_eq_drop_add_entry]
  exact bad_card_le_witnessed_obstruction_count X

/-- The `a ≥ 2` range. -/
def higherPowerWitnessesUpTo (X : ℕ) : Finset ObstructionWitness :=
  (obstructionWitnessesUpTo X).filter fun w => 2 ≤ witnessExponent w

/-- The `a=1, p≤smallCut` range. -/
def smallPrimeWitnessesUpTo (X smallCut : ℕ) : Finset ObstructionWitness :=
  (obstructionWitnessesUpTo X).filter fun w =>
    witnessExponent w = 1 ∧ witnessPrime w ≤ smallCut

/-- The `a=1, smallCut<p≤topCut` transition range. -/
def transitionPrimeWitnessesUpTo
    (X smallCut topCut : ℕ) : Finset ObstructionWitness :=
  (obstructionWitnessesUpTo X).filter fun w =>
    witnessExponent w = 1 ∧
      smallCut < witnessPrime w ∧ witnessPrime w ≤ topCut

/-- The `a=1, topCut<p` top range. -/
def topPrimeWitnessesUpTo (X topCut : ℕ) : Finset ObstructionWitness :=
  (obstructionWitnessesUpTo X).filter fun w =>
    witnessExponent w = 1 ∧ topCut < witnessPrime w

@[simp] theorem mem_obstructionWitnessesUpTo
    {X : ℕ} {w : ObstructionWitness} :
    w ∈ obstructionWitnessesUpTo X ↔
      w ∈ dropWitnessesUpTo X ∨ w ∈ entryWitnessesUpTo X := by
  simp [obstructionWitnessesUpTo]

@[simp] theorem mem_higherPowerWitnessesUpTo
    {X : ℕ} {w : ObstructionWitness} :
    w ∈ higherPowerWitnessesUpTo X ↔
      w ∈ obstructionWitnessesUpTo X ∧ 2 ≤ witnessExponent w := by
  simp [higherPowerWitnessesUpTo]

@[simp] theorem mem_smallPrimeWitnessesUpTo
    {X smallCut : ℕ} {w : ObstructionWitness} :
    w ∈ smallPrimeWitnessesUpTo X smallCut ↔
      w ∈ obstructionWitnessesUpTo X ∧
        witnessExponent w = 1 ∧ witnessPrime w ≤ smallCut := by
  simp [smallPrimeWitnessesUpTo]

@[simp] theorem mem_transitionPrimeWitnessesUpTo
    {X smallCut topCut : ℕ} {w : ObstructionWitness} :
    w ∈ transitionPrimeWitnessesUpTo X smallCut topCut ↔
      w ∈ obstructionWitnessesUpTo X ∧
        witnessExponent w = 1 ∧
          smallCut < witnessPrime w ∧ witnessPrime w ≤ topCut := by
  simp [transitionPrimeWitnessesUpTo]

@[simp] theorem mem_topPrimeWitnessesUpTo
    {X topCut : ℕ} {w : ObstructionWitness} :
    w ∈ topPrimeWitnessesUpTo X topCut ↔
      w ∈ obstructionWitnessesUpTo X ∧
        witnessExponent w = 1 ∧ topCut < witnessPrime w := by
  simp [topPrimeWitnessesUpTo]

theorem obstructionWitness_exponent_pos
    {X : ℕ} {w : ObstructionWitness}
    (hw : w ∈ obstructionWitnessesUpTo X) :
    0 < witnessExponent w := by
  rcases mem_obstructionWitnessesUpTo.mp hw with hdrop | hentry
  · rcases (mem_dropWitnessesUpTo.mp hdrop).2 with
      ⟨_hp, _hp2, hexact, _hlow⟩
    exact hexact.1
  · rcases (mem_entryWitnessesUpTo.mp hentry).2 with
      ⟨_hp, _hp2, hexact, _hlow⟩
    exact hexact.1

/-- The four ranges are exhaustive.  The endpoint conventions are exact:
`p=smallCut` lies in the small range and `p=topCut` in the transition
range. -/
theorem obstructionWitnesses_fourRange
    (X smallCut topCut : ℕ) :
    obstructionWitnessesUpTo X =
      higherPowerWitnessesUpTo X ∪
        (smallPrimeWitnessesUpTo X smallCut ∪
          (transitionPrimeWitnessesUpTo X smallCut topCut ∪
            topPrimeWitnessesUpTo X topCut)) := by
  ext w
  constructor
  · intro hw
    have ha := obstructionWitness_exponent_pos hw
    by_cases hhigh : 2 ≤ witnessExponent w
    · exact Finset.mem_union_left _
        (mem_higherPowerWitnessesUpTo.mpr ⟨hw, hhigh⟩)
    have haone : witnessExponent w = 1 := by omega
    by_cases hsmall : witnessPrime w ≤ smallCut
    · exact Finset.mem_union_right _ <| Finset.mem_union_left _ <|
        mem_smallPrimeWitnessesUpTo.mpr ⟨hw, haone, hsmall⟩
    by_cases htransition : witnessPrime w ≤ topCut
    · exact Finset.mem_union_right _ <| Finset.mem_union_right _ <|
        Finset.mem_union_left _ <|
          mem_transitionPrimeWitnessesUpTo.mpr
            ⟨hw, haone, Nat.lt_of_not_ge hsmall, htransition⟩
    · exact Finset.mem_union_right _ <| Finset.mem_union_right _ <|
        Finset.mem_union_right _ <|
          mem_topPrimeWitnessesUpTo.mpr
            ⟨hw, haone, Nat.lt_of_not_ge htransition⟩
  · intro hw
    rcases Finset.mem_union.mp hw with hhigh | hrest
    · exact (mem_higherPowerWitnessesUpTo.mp hhigh).1
    rcases Finset.mem_union.mp hrest with hsmall | hrest
    · exact (mem_smallPrimeWitnessesUpTo.mp hsmall).1
    rcases Finset.mem_union.mp hrest with htransition | htop
    · exact (mem_transitionPrimeWitnessesUpTo.mp htransition).1
    · exact (mem_topPrimeWitnessesUpTo.mp htop).1

theorem higherPower_disjoint_otherRanges
    (X smallCut topCut : ℕ) :
    Disjoint (higherPowerWitnessesUpTo X)
      (smallPrimeWitnessesUpTo X smallCut ∪
        (transitionPrimeWitnessesUpTo X smallCut topCut ∪
          topPrimeWitnessesUpTo X topCut)) := by
  rw [Finset.disjoint_left]
  intro w hhigh hrest
  have ha2 := (mem_higherPowerWitnessesUpTo.mp hhigh).2
  rcases Finset.mem_union.mp hrest with hsmall | hrest
  · have ha1 := (mem_smallPrimeWitnessesUpTo.mp hsmall).2.1
    omega
  rcases Finset.mem_union.mp hrest with htransition | htop
  · have ha1 := (mem_transitionPrimeWitnessesUpTo.mp htransition).2.1
    omega
  · have ha1 := (mem_topPrimeWitnessesUpTo.mp htop).2.1
    omega

theorem smallPrime_disjoint_largerRanges
    (X smallCut topCut : ℕ) (hcuts : smallCut ≤ topCut) :
    Disjoint (smallPrimeWitnessesUpTo X smallCut)
      (transitionPrimeWitnessesUpTo X smallCut topCut ∪
        topPrimeWitnessesUpTo X topCut) := by
  rw [Finset.disjoint_left]
  intro w hsmall hrest
  have hpSmall := (mem_smallPrimeWitnessesUpTo.mp hsmall).2.2
  rcases Finset.mem_union.mp hrest with htransition | htop
  · have hpLarge := (mem_transitionPrimeWitnessesUpTo.mp htransition).2.2.1
    omega
  · have hpTop := (mem_topPrimeWitnessesUpTo.mp htop).2.2
    omega

theorem transitionPrime_disjoint_topRange
    (X smallCut topCut : ℕ) :
    Disjoint (transitionPrimeWitnessesUpTo X smallCut topCut)
      (topPrimeWitnessesUpTo X topCut) := by
  rw [Finset.disjoint_left]
  intro w htransition htop
  have hpLe := (mem_transitionPrimeWitnessesUpTo.mp htransition).2.2.2
  have hpGt := (mem_topPrimeWitnessesUpTo.mp htop).2.2
  omega

/-- Cardinal form of the exact, disjoint four-range partition. -/
theorem obstructionWitnesses_card_fourRange
    (X smallCut topCut : ℕ) (hcuts : smallCut ≤ topCut) :
    (obstructionWitnessesUpTo X).card =
      (higherPowerWitnessesUpTo X).card +
        ((smallPrimeWitnessesUpTo X smallCut).card +
          ((transitionPrimeWitnessesUpTo X smallCut topCut).card +
            (topPrimeWitnessesUpTo X topCut).card)) := by
  rw [obstructionWitnesses_fourRange X smallCut topCut,
    Finset.card_union_of_disjoint
      (higherPower_disjoint_otherRanges X smallCut topCut),
    Finset.card_union_of_disjoint
      (smallPrime_disjoint_largerRanges X smallCut topCut hcuts),
    Finset.card_union_of_disjoint
      (transitionPrime_disjoint_topRange X smallCut topCut)]

/-- Exact cardinal form of equations (22)--(24): the two witnessed event
counts split into the four disjoint ranges. -/
theorem witnessed_obstruction_count_card_fourRange
    (X smallCut topCut : ℕ) (hcuts : smallCut ≤ topCut) :
    (dropWitnessesUpTo X).card + (entryWitnessesUpTo X).card =
      (higherPowerWitnessesUpTo X).card +
        ((smallPrimeWitnessesUpTo X smallCut).card +
          ((transitionPrimeWitnessesUpTo X smallCut topCut).card +
            (topPrimeWitnessesUpTo X topCut).card)) := by
  rw [← obstructionWitnesses_card_eq_drop_add_entry]
  exact obstructionWitnesses_card_fourRange X smallCut topCut hcuts

#print axioms exactPrimePowerCofactor_coordinate_bounds
#print axioms dropWitness_mem
#print axioms entryWitness_mem
#print axioms bad_mem_dropParameters_or_entryParameters
#print axioms bad_card_le_witnessed_obstruction_count
#print axioms drop_entry_witnesses_disjoint
#print axioms bad_card_le_obstructionWitnesses_card
#print axioms obstructionWitnesses_fourRange
#print axioms obstructionWitnesses_card_fourRange
#print axioms witnessed_obstruction_count_card_fourRange

end

end DensityEvents
end Erdos730
