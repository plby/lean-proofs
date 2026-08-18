import ErdosProblems.Erdos140.BohrStopping
import ErdosProblems.Erdos140.BohrEstimates
import ErdosProblems.Erdos140.BourgainRegular
import ErdosProblems.Erdos140.Counting
import ErdosProblems.Erdos140.Sifting
import ErdosProblems.Erdos140.LocalizedAlmostPeriodicity
import ErdosProblems.Erdos140.LocalizedUnbalancing
import APAP.Prereqs.Convolution.Norm

/-!
# The concrete regular-Bohr density step

This file contains the set-theoretic part of the Kelley--Meka/Bloom--Sisask
count-or-increment step.  There are two normalization points which are easy
to lose in an informal argument.

* Intersecting two Bohr data means taking the old width on an old-only
  frequency, the new width on a new-only frequency, and the minimum on a
  shared frequency.
* If `x - c` is in the old restricted set, the new *centred* restricted set
  contains `-c`, not `c`.  With this convention its new location is
  `oldShift - x`, and membership in the original set is preserved exactly.

The final narrowing theorem below takes actual regular child carriers and
returns either the simultaneous dense-translate alternative used by the
analytic count argument, or an actual `BohrStopping.RegularRestriction` with
the advertised density increment.  No numerical state is manufactured.
-/

open Finset
open scoped BigOperators NNReal translate

namespace Erdos140.DensityStep

noncomputable section

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-! ## Intersections and frequency extensions -/

namespace Refinement

/-- The intersection of two finite Bohr data.  Frequencies occurring in both
data receive the smaller width. -/
def meet (B C : BohrData G) : BohrData G where
  freq := B.freq ∪ C.freq
  width gamma :=
    if gamma ∈ B.freq then
      if gamma ∈ C.freq then min (B.width gamma) (C.width gamma)
      else B.width gamma
    else C.width gamma

@[simp] theorem freq_meet (B C : BohrData G) :
    (meet B C).freq = B.freq ∪ C.freq := rfl

theorem rank_meet_le (B C : BohrData G) :
    (meet B C).rank ≤ B.rank + C.rank := by
  simpa [BohrData.rank, meet] using Finset.card_union_le B.freq C.freq

@[simp] theorem mem_meet_carrier (B C : BohrData G) (x : G) :
    x ∈ (meet B C).carrier ↔ x ∈ B.carrier ∧ x ∈ C.carrier := by
  classical
  simp only [BohrData.mem_carrier, meet, mem_union]
  constructor
  · intro hx
    constructor
    · intro gamma hgamma
      have h := hx gamma (Or.inl hgamma)
      by_cases hC : gamma ∈ C.freq
      · have h' : ‖gamma x‖ ≤ (min (B.width gamma) (C.width gamma) : NNReal) := by
          simpa [meet, hgamma, hC] using h
        calc
          ‖gamma x‖ ≤ (min (B.width gamma) (C.width gamma) : NNReal) := h'
          _ ≤ (B.width gamma : NNReal) := by exact_mod_cast min_le_left _ _
      · simpa [hgamma, hC] using h
    · intro gamma hgamma
      have h := hx gamma (Or.inr hgamma)
      by_cases hB : gamma ∈ B.freq
      · have h' : ‖gamma x‖ ≤ (min (B.width gamma) (C.width gamma) : NNReal) := by
          simpa [meet, hB, hgamma] using h
        calc
          ‖gamma x‖ ≤ (min (B.width gamma) (C.width gamma) : NNReal) := h'
          _ ≤ (C.width gamma : NNReal) := by exact_mod_cast min_le_right _ _
      · simpa [hB] using h
  · rintro ⟨hB, hC⟩ gamma (hgammaB | hgammaC)
    · by_cases hgammaC' : gamma ∈ C.freq
      · simpa [hgammaB, hgammaC'] using
          (le_min (hB gamma hgammaB) (hC gamma hgammaC'))
      · simpa [hgammaB, hgammaC'] using hB gamma hgammaB
    · by_cases hgammaB : gamma ∈ B.freq
      · simpa [hgammaB, hgammaC] using
          (le_min (hB gamma hgammaB) (hC gamma hgammaC))
      · simpa [hgammaB] using hC gamma hgammaC

/-- Bohr data with a prescribed common width on a finite frequency set. -/
def onFrequencies (Delta : Finset (AddCharacter G)) (width : NNReal) : BohrData G where
  freq := Delta
  width := fun _ => width

@[simp] theorem rank_onFrequencies (Delta : Finset (AddCharacter G)) (width : NNReal) :
    (onFrequencies Delta width).rank = Delta.card := rfl

@[simp] theorem mem_onFrequencies_carrier
    (Delta : Finset (AddCharacter G)) (width : NNReal) (x : G) :
    x ∈ (onFrequencies Delta width).carrier ↔
      ∀ gamma ∈ Delta, ‖gamma x‖ ≤ (width : Real) := by
  simp [onFrequencies, BohrData.mem_carrier]

/-- Add a finite family of common-width frequencies to an existing datum. -/
def extend (B : BohrData G) (Delta : Finset (AddCharacter G)) (width : NNReal) :
    BohrData G :=
  meet B (onFrequencies Delta width)

theorem rank_extend_le (B : BohrData G) (Delta : Finset (AddCharacter G))
    (width : NNReal) :
    (extend B Delta width).rank ≤ B.rank + Delta.card := by
  simpa [extend] using rank_meet_le B (onFrequencies Delta width)

@[simp] theorem mem_extend_carrier (B : BohrData G)
    (Delta : Finset (AddCharacter G)) (width : NNReal) (x : G) :
    x ∈ (extend B Delta width).carrier ↔
      x ∈ B.carrier ∧ ∀ gamma ∈ Delta, ‖gamma x‖ ≤ (width : Real) := by
  rw [extend, mem_meet_carrier, mem_onFrequencies_carrier]

end Refinement

/-! ## Located regular restrictions -/

open BohrStopping

/-- A regular restriction together with an exact translation back into the
fixed original set.  This is the provenance needed to lift a local mixed
progression count to the original progression count. -/
structure LocatedRestriction (original : Finset G) where
  restriction : RegularRestriction G
  shift : G
  subset_original :
    ∀ x ∈ restriction.set, x - shift ∈ original

namespace LocatedRestriction

def ambient {original : Finset G} (s : LocatedRestriction original) : Finset G :=
  s.restriction.ambient

def density {original : Finset G} (s : LocatedRestriction original) : Real :=
  s.restriction.density

def rank {original : Finset G} (s : LocatedRestriction original) : Nat :=
  s.restriction.rank

def card {original : Finset G} (s : LocatedRestriction original) : Nat :=
  s.restriction.card

lemma density_pos {original : Finset G} (s : LocatedRestriction original) :
    0 < s.density := s.restriction.density_pos

lemma density_le_one {original : Finset G} (s : LocatedRestriction original) :
    s.density ≤ 1 := s.restriction.density_le_one

/-- The local endpoint set lifts to the original set after translating by
the recorded location. -/
theorem mixedThreeAPCount_le_original {original : Finset G}
    (s : LocatedRestriction original) {C : Finset G}
    (hC : ∀ x ∈ C, x - s.shift ∈ original) :
    mixedThreeAPCount s.restriction.set C ≤ threeAPCount original := by
  exact mixedThreeAPCount_le_threeAPCount_of_sub_translate s.shift
    s.subset_original hC

end LocatedRestriction

/-- A chain of controlled increments which retains a translation into the
same original set at every node. -/
inductive LocatedControlledChain {original : Finset G}
    (q : Real) (rankCost : Nat) (sizeCost : Real) :
    Nat → LocatedRestriction original → LocatedRestriction original → Prop
  | nil (s : LocatedRestriction original) :
      LocatedControlledChain q rankCost sizeCost 0 s s
  | cons {n : Nat} {s t u : LocatedRestriction original}
      (hst : IsControlledIncrement q rankCost sizeCost
        s.restriction t.restriction)
      (htu : LocatedControlledChain q rankCost sizeCost n t u) :
      LocatedControlledChain q rankCost sizeCost (n + 1) s u

namespace LocatedControlledChain

theorem forget {original : Finset G} {q : Real} {rankCost : Nat}
    {sizeCost : Real} {n : Nat} {s t : LocatedRestriction original}
    (h : LocatedControlledChain q rankCost sizeCost n s t) :
    ControlledChain q rankCost sizeCost n s.restriction t.restriction := by
  induction h with
  | nil s => exact ControlledChain.nil s.restriction
  | cons hst _ ih => exact ControlledChain.cons hst ih

theorem density_bound {original : Finset G} {q : Real} {rankCost : Nat}
    {sizeCost : Real} (hq : 0 ≤ q) {n : Nat}
    {s t : LocatedRestriction original}
    (h : LocatedControlledChain q rankCost sizeCost n s t) :
    q ^ n * s.density ≤ t.density :=
  h.forget.density_bound hq

theorem rank_bound {original : Finset G} {q : Real} {rankCost : Nat}
    {sizeCost : Real} {n : Nat} {s t : LocatedRestriction original}
    (h : LocatedControlledChain q rankCost sizeCost n s t) :
    t.rank ≤ s.rank + n * rankCost :=
  h.forget.rank_bound

theorem card_bound {original : Finset G} {q : Real} {rankCost : Nat}
    {sizeCost : Real} {n : Nat} {s t : LocatedRestriction original}
    (h : LocatedControlledChain q rankCost sizeCost n s t) :
    Real.exp (-(n : Real) * sizeCost) * (s.card : Real) ≤ (t.card : Real) :=
  h.forget.card_bound

end LocatedControlledChain

/-- The provenance-preserving version of `BohrStopping.ProducesIncrement`. -/
def ProducesLocatedIncrement {original : Finset G}
    (Bad : LocatedRestriction original → Prop)
    (q : Real) (rankCost : Nat) (sizeCost : Real) : Prop :=
  ∀ s, Bad s → ∃ t : LocatedRestriction original,
    IsControlledIncrement q rankCost sizeCost s.restriction t.restriction

/-- Finite stopping recursion which retains the translation into the original
set.  This is the form required by the final mixed-progression lifting. -/
theorem exists_terminal_located_chain
    {original : Finset G} {Terminal : LocatedRestriction original → Prop}
    {q : Real} {rankCost : Nat} {sizeCost : Real}
    (hq : 0 ≤ q)
    (hstep : ∀ s : LocatedRestriction original,
      Terminal s ∨ ∃ t : LocatedRestriction original,
        IsControlledIncrement q rankCost sizeCost
        s.restriction t.restriction)
    (fuel : Nat) (s : LocatedRestriction original)
    (hgrowth : 1 < q ^ fuel * s.density) :
    ∃ n ≤ fuel, ∃ t : LocatedRestriction original,
      LocatedControlledChain q rankCost sizeCost n s t ∧ Terminal t := by
  induction fuel generalizing s with
  | zero =>
      have hs := s.density_le_one
      simp only [pow_zero, one_mul] at hgrowth
      exact (not_lt_of_ge hs hgrowth).elim
  | succ fuel ih =>
      rcases hstep s with hterminal | ⟨t, hst⟩
      · exact ⟨0, by omega, s, LocatedControlledChain.nil s, hterminal⟩
      · have hqpow : 0 ≤ q ^ fuel := pow_nonneg hq fuel
        have hgrowth' : 1 < q ^ fuel * t.density := by
          calc
            1 < q ^ (fuel + 1) * s.density := by simpa using hgrowth
            _ = q ^ fuel * (q * s.density) := by rw [pow_succ]; ring
            _ ≤ q ^ fuel * t.density :=
              mul_le_mul_of_nonneg_left hst.1 hqpow
        obtain ⟨n, hn, u, hchain, hu⟩ := ih t hgrowth'
        exact ⟨n + 1, by omega, u, LocatedControlledChain.cons hst hchain, hu⟩

/-- A bad predicate which always yields a located increment must fail along
a finite chain as soon as the corresponding density growth would exceed
one.  The conclusion includes all accumulated quantitative bounds. -/
theorem exists_stopping_located_chain
    {original : Finset G} {Bad : LocatedRestriction original → Prop}
    {q : Real} {rankCost : Nat} {sizeCost : Real}
    (hq : 0 ≤ q)
    (hbad : ProducesLocatedIncrement Bad q rankCost sizeCost)
    (fuel : Nat) (s : LocatedRestriction original)
    (hgrowth : 1 < q ^ fuel * s.density) :
    ∃ n ≤ fuel, ∃ t : LocatedRestriction original,
      LocatedControlledChain q rankCost sizeCost n s t ∧
      ¬ Bad t ∧
      q ^ n * s.density ≤ t.density ∧
      t.rank ≤ s.rank + n * rankCost ∧
      Real.exp (-(n : Real) * sizeCost) * (s.card : Real) ≤ (t.card : Real) := by
  classical
  have hstep : ∀ u : LocatedRestriction original,
      (¬ Bad u) ∨ ∃ v : LocatedRestriction original,
        IsControlledIncrement q rankCost sizeCost
        u.restriction v.restriction := by
    intro u
    by_cases hu : Bad u
    · exact Or.inr (hbad u hu)
    · exact Or.inl hu
  obtain ⟨n, hn, t, hchain, hterminal⟩ :=
    exists_terminal_located_chain hq hstep fuel s hgrowth
  exact ⟨n, hn, t, hchain, hterminal, hchain.density_bound hq,
    hchain.rank_bound, hchain.card_bound⟩

/-! ## The centred translated fiber -/

/-- Negated fibre of the translate `x - C` inside `A`.  Negation recentres
the fibre inside the symmetric Bohr carrier containing `C`. -/
def narrowingSet (A C : Finset G) (x : G) : Finset G :=
  (C.filter fun c => x - c ∈ A).image fun c => -c

@[simp] theorem mem_narrowingSet {A C : Finset G} {x z : G} :
    z ∈ narrowingSet A C x ↔ -z ∈ C ∧ x + z ∈ A := by
  classical
  simp only [narrowingSet, mem_image, mem_filter]
  constructor
  · rintro ⟨c, ⟨hc, hxc⟩, rfl⟩
    exact ⟨by simpa, by simpa [sub_eq_add_neg] using hxc⟩
  · rintro ⟨hzC, hxzA⟩
    refine ⟨-z, ?_, by simp⟩
    exact ⟨hzC, by simpa [sub_eq_add_neg] using hxzA⟩

theorem card_narrowingSet (A C : Finset G) (x : G) :
    (narrowingSet A C x).card = (C.filter fun c => x - c ∈ A).card := by
  classical
  unfold narrowingSet
  rw [Finset.card_image_of_injective]
  intro a b h
  exact neg_injective h

theorem narrowingSet_subset_carrier
    {B : BohrData G} {rho : NNReal} {A C : Finset G} {x : G}
    (hC : C ⊆ (B.dilate rho).carrier) :
    narrowingSet A C x ⊆ (B.dilate rho).carrier := by
  intro z hz
  have hz' := (mem_narrowingSet.mp hz).1
  exact BohrData.neg_mem_carrier.mp (hC hz')

/-- Exact normalization of a local density as the cardinality of the centred
translated fibre. -/
theorem localDensity_eq_card_narrowingSet_div
    {A C : Finset G} (hC : C.Nonempty) (x : G) :
    localDensity A C x = (narrowingSet A C x).card / (C.card : Real) := by
  classical
  rw [localDensity, normalizedConvolution]
  let e : G ≃ G := Equiv.subLeft x
  rw [Fintype.sum_equiv e
    (fun y : G => finsetIndicator A y * normalizedIndicator C (x - y))
    (fun c : G => finsetIndicator A (x - c) * normalizedIndicator C c)
    (fun c => by simp [e])]
  rw [card_narrowingSet]
  simp only [finsetIndicator, normalizedIndicator, div_eq_mul_inv]
  have hpoint (c : G) :
      (if x - c ∈ A then (1 : Real) else 0) *
          (if c ∈ C then (C.card : Real)⁻¹ else 0) =
        if c ∈ C ∧ x - c ∈ A then (C.card : Real)⁻¹ else 0 := by
    by_cases hc : c ∈ C <;> by_cases ha : x - c ∈ A <;> simp [hc, ha]
  simp_rw [hpoint]
  rw [← Finset.sum_filter]
  have hfilter :
      (Finset.univ.filter fun c : G => c ∈ C ∧ x - c ∈ A) =
        C.filter fun c => x - c ∈ A := by
    ext c
    simp
  rw [hfilter]
  simp

/-! ## Sifting and localized-almost-periodicity normalization -/

open Function MeasureTheory Real
open scoped ENNReal Indicator Pointwise mu

/-- APAP's probability indicator is the same counting-probability indicator
used by the local almost-periodicity file. -/
theorem probabilityIndicator_eq_mu (A : Finset G) :
    LocalizedAlmostPeriodicity.probabilityIndicator A = μ_[Real] A := by
  funext x
  simp [LocalizedAlmostPeriodicity.probabilityIndicator, mu_apply]

/-- APAP's discrete difference convolution and the explicit one-variable
counting sum in `LocalizedAlmostPeriodicity` agree exactly. -/
theorem differenceConvolution_probability_eq_dddconv (A₁ A₂ : Finset G) :
    LocalizedAlmostPeriodicity.differenceConvolution
        (LocalizedAlmostPeriodicity.probabilityIndicator A₁)
        (LocalizedAlmostPeriodicity.probabilityIndicator A₂) =
      μ_[Real] A₁ ○ᵈ μ A₂ := by
  funext x
  rw [probabilityIndicator_eq_mu, probabilityIndicator_eq_mu,
    LocalizedAlmostPeriodicity.differenceConvolution, dddconv_eq_sum_sub']
  simp

/-- The complex threefold convolution used by Croot--Sisask is the complex
embedding of the real counting inner product used by the localized triple
sum.  This is the sign-sensitive normalization bridge: the first set is
negated, while the sampling set is the unnormalised middle indicator. -/
theorem threefold_eq_ofReal_finiteInner
    (A₁ A₂ S : Finset G) (t : G) :
    ((μ_[ℂ] (-A₁) ∗ᵈ (𝟭_[S] : G → ℂ)) ∗ᵈ μ A₂) t =
      Complex.ofReal
        (LocalizedAlmostPeriodicity.countingInner
          (fun x ↦ LocalizedAlmostPeriodicity.differenceConvolution
            (LocalizedAlmostPeriodicity.probabilityIndicator A₁)
            (LocalizedAlmostPeriodicity.probabilityIndicator A₂) (x - t))
          (LocalizedAlmostPeriodicity.setIndicator S)) := by
  classical
  let a : G → Real := μ_[Real] A₁
  let b : G → Real := μ_[Real] A₂
  let oneS : G → Real := 𝟭_[S]
  have hcount :
      LocalizedAlmostPeriodicity.countingInner
          (fun x ↦ LocalizedAlmostPeriodicity.differenceConvolution
            (LocalizedAlmostPeriodicity.probabilityIndicator A₁)
            (LocalizedAlmostPeriodicity.probabilityIndicator A₂) (x - t))
          (LocalizedAlmostPeriodicity.setIndicator S) =
        ⟪τ t (a ○ᵈ b), oneS⟫_[Real] := by
    rw [differenceConvolution_probability_eq_dddconv]
    unfold LocalizedAlmostPeriodicity.countingInner
      LocalizedAlmostPeriodicity.setIndicator
    simp only [RCLike.wInner_one_eq_sum, RCLike.inner_apply',
      RCLike.conj_to_real, translate_apply, a, b, oneS, Set.indicator_apply,
      mem_coe]
  have hreal :
      ((μ_[Real] (-A₁) ∗ᵈ oneS) ∗ᵈ b) t =
        LocalizedAlmostPeriodicity.countingInner
          (fun x ↦ LocalizedAlmostPeriodicity.differenceConvolution
            (LocalizedAlmostPeriodicity.probabilityIndicator A₁)
            (LocalizedAlmostPeriodicity.probabilityIndicator A₂) (x - t))
          (LocalizedAlmostPeriodicity.setIndicator S) := by
    calc
      ((μ_[Real] (-A₁) ∗ᵈ oneS) ∗ᵈ b) t =
          ((oneS ∗ᵈ b) ∗ᵈ μ_[Real] (-A₁)) t := by
            apply congrFun
            calc
              (μ_[Real] (-A₁) ∗ᵈ oneS) ∗ᵈ b =
                  oneS ∗ᵈ (μ_[Real] (-A₁) ∗ᵈ b) := by
                    rw [ddconv_comm (μ_[Real] (-A₁)) oneS,
                      ddconv_assoc]
              _ = oneS ∗ᵈ (b ∗ᵈ μ_[Real] (-A₁)) := by
                    rw [ddconv_comm (μ_[Real] (-A₁)) b]
              _ = (oneS ∗ᵈ b) ∗ᵈ μ_[Real] (-A₁) := by
                    rw [ddconv_assoc]
      _ = ((oneS ∗ᵈ b) ○ᵈ a) t := by
        rw [← conjneg_mu (K := Real) A₁, ddconv_conjneg]
      _ = ⟪τ t a, oneS ∗ᵈ b⟫_[Real] := by
        rw [dddconv_eq_wInner_one]
        exact RCLike.conj_wInner_symm (𝕜 := Real)
          (1 : G → Real) (oneS ∗ᵈ b) (τ t a)
      _ = ⟪τ t a ○ᵈ b, oneS⟫_[Real] := by
        exact (dddconv_wInner_one_eq_wInner_one_ddconv
          (τ t a) b oneS).symm
      _ = ⟪τ t (a ○ᵈ b), oneS⟫_[Real] := by rw [translate_dddconv]
      _ = _ := hcount.symm
  have honeS : ((↑) ∘ oneS : G → Complex) = (𝟭_[S] : G → Complex) := by
    ext x
    by_cases hx : x ∈ S <;> simp [oneS, Set.indicator_apply, hx]
  rw [← hreal]
  change ((μ_[Complex] (-A₁) ∗ᵈ (𝟭_[S] : G → Complex)) ∗ᵈ μ A₂) t =
    (Complex.ofReal ∘ ((μ_[Real] (-A₁) ∗ᵈ oneS) ∗ᵈ b)) t
  rw [Complex.ofReal_comp_ddconv, Complex.ofReal_comp_ddconv]
  simp only [Complex.ofReal_comp_mu, b]
  rw [honeS]

/-- Pairing a probability difference convolution with a set indicator is
the literal mass of that convolution on the set. -/
theorem countingInner_difference_setIndicator_eq_sum
    (A₁ A₂ S : Finset G) :
    LocalizedAlmostPeriodicity.countingInner
        (LocalizedAlmostPeriodicity.differenceConvolution
          (LocalizedAlmostPeriodicity.probabilityIndicator A₁)
          (LocalizedAlmostPeriodicity.probabilityIndicator A₂))
        (LocalizedAlmostPeriodicity.setIndicator S) =
      ∑ x ∈ S, (μ_[Real] A₁ ○ᵈ μ A₂) x := by
  classical
  rw [differenceConvolution_probability_eq_dddconv]
  unfold LocalizedAlmostPeriodicity.countingInner
    LocalizedAlmostPeriodicity.setIndicator
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  have hfilter : Finset.univ.filter (fun x : G => x ∈ S) = S := by ext; simp
  rw [hfilter]

/-- The exact convexity consequence of the localized almost-periodicity
bridge: a popular-difference mass `1-delta` remains at least
`1-delta-epsilon` after smoothing by the actual Bohr probability measure. -/
theorem smoothed_popular_mass_lower_bound
    {D : BohrData G} {A₁ A₂ S : Finset G} {epsilon delta : Real}
    (hA₁ : A₁.Nonempty) (hA₂ : A₂.Nonempty)
    (hmass : 1 - delta ≤ ∑ x ∈ S, (μ_[Real] A₁ ○ᵈ μ A₂) x)
    (htriple : ∀ t ∈ D.carrier,
      |LocalizedAlmostPeriodicity.tripleIndicatorSum A₁ A₂ S t -
          LocalizedAlmostPeriodicity.tripleIndicatorSum A₁ A₂ S 0| ≤
        epsilon * (A₁.card : Real) * A₂.card) :
    1 - delta - epsilon ≤
      LocalizedAlmostPeriodicity.countingInner
        (LocalizedAlmostPeriodicity.sumConvolution
          (LocalizedAlmostPeriodicity.probabilityIndicator D.carrier)
          (LocalizedAlmostPeriodicity.differenceConvolution
            (LocalizedAlmostPeriodicity.probabilityIndicator A₁)
            (LocalizedAlmostPeriodicity.probabilityIndicator A₂)))
        (LocalizedAlmostPeriodicity.setIndicator S) := by
  have herr :=
    LocalizedAlmostPeriodicity.localized_inner_error_of_triple_almost_periods
      hA₁ hA₂ htriple
  have hbase :
      1 - delta ≤
        LocalizedAlmostPeriodicity.countingInner
          (LocalizedAlmostPeriodicity.differenceConvolution
            (LocalizedAlmostPeriodicity.probabilityIndicator A₁)
            (LocalizedAlmostPeriodicity.probabilityIndicator A₂))
          (LocalizedAlmostPeriodicity.setIndicator S) := by
    rwa [countingInner_difference_setIndicator_eq_sum]
  have hlower := (abs_le.mp herr).1
  linarith

section SiftingOutput

variable [MeasurableSpace G] [DiscreteMeasurableSpace G]

/-- The exact common density lower bound delivered by the sifting lemma.
Keeping this expression named prevents the two copies in the output
certificate from silently acquiring different normalizations. -/
def siftingDensityLower (A B₁ B₂ : Finset G) (p : Nat) : Real :=
  (4 : Real)⁻¹ *
      ‖𝟭_[A, ℝ] ○ᵈ 𝟭_[A]‖_[p, μ B₁ ○ᵈ μ B₂] ^ (2 * p) /
    (A.card : Real) ^ (2 * p)

/-- The explicit shift count used by the elementary sifting identity is
exactly the unnormalised indicator autocorrelation. -/
theorem commonShiftCount_eq_indicatorCorrelation
    (A : Finset G) (x : G) :
    (Sifting.commonShiftCount A x : Real) =
      (𝟭_[A, Real] ○ᵈ 𝟭_[A]) x := by
  classical
  rw [Sifting.commonShiftCount, dddconv_eq_sum_sub']
  have hcount :
      ((#(Finset.univ.filter fun t : G ↦ x - t ∈ A ∧ -t ∈ A) : Nat) : Real) =
        ∑ t : G, if x - t ∈ A ∧ -t ∈ A then (1 : Real) else 0 := by
    simpa using congrArg (fun n : Nat ↦ (n : Real))
      (Finset.card_filter (fun t : G ↦ x - t ∈ A ∧ -t ∈ A) Finset.univ)
  rw [hcount]
  refine Fintype.sum_equiv (Equiv.subLeft x) _ _ (fun y ↦ ?_)
  simp only [Equiv.subLeft_apply, Set.indicator_apply]
  have hneg : x - y - x = -y := by abel
  rw [hneg]
  split_ifs <;> simp_all

/-- The common-tuple sifted sets have the exact product-cardinality moment
which drives the high-product selection in dependent random choice.  This
version is public and, unlike the existential DRC wrapper, retains the tuple
which witnesses both output sets. -/
theorem sum_card_siftedSet_mul_card_siftedSet
    (A B₁ B₂ : Finset G) (p : Nat) (hp : p ≠ 0)
    (hB₁ : B₁.Nonempty) (hB₂ : B₂.Nonempty) :
    (∑ u : Fin p → G,
        ((Sifting.siftedSet A B₁ u).card : Real) *
          (Sifting.siftedSet A B₂ u).card) =
      (B₁.card : Real) * B₂.card *
        ‖𝟭_[A, Real] ○ᵈ 𝟭_[A]‖_[p, μ B₁ ○ᵈ μ B₂] ^ p := by
  classical
  let corr : G → Real := 𝟭_[A, Real] ○ᵈ 𝟭_[A]
  have hcorr : ∀ x, 0 ≤ corr x := fun x ↦
    dddconv_apply_nonneg Set.indicator_one_nonneg Set.indicator_one_nonneg x
  have hraw := Sifting.sum_pairSum_sifted A B₁ B₂ p (fun _ ↦ (1 : Real))
  have hleft :
      (∑ u : Fin p → G,
          Sifting.pairSum (Sifting.siftedSet A B₁ u)
            (Sifting.siftedSet A B₂ u) (fun _ ↦ (1 : Real))) =
        ∑ u : Fin p → G,
          ((Sifting.siftedSet A B₁ u).card : Real) *
            (Sifting.siftedSet A B₂ u).card := by
    apply Finset.sum_congr rfl
    intro u _
    simp [Sifting.pairSum]
  have hright :
      (∑ b₁ ∈ B₁, ∑ b₂ ∈ B₂,
          (Sifting.commonShiftCount A (b₁ - b₂) : Real) ^ p) =
        ∑ x : G, (𝟭_[B₁, Real] ○ᵈ 𝟭_[B₂]) x * corr x ^ p := by
    rw [sum_dddconv_mul]
    simp [Set.indicator_apply, corr, commonShiftCount_eq_indicatorCorrelation]
  have hweight :
      (𝟭_[B₁, Real] ○ᵈ 𝟭_[B₂]) =
        fun x ↦ (B₁.card : Real) * B₂.card *
          (μ_[Real] B₁ ○ᵈ μ B₂) x := by
    ext x
    simp only [dddconv_eq_sum_sub', Set.indicator_apply, mu_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hy : y ∈ B₁ <;> by_cases hyx : y - x ∈ B₂
    · simp only [mem_coe, if_pos hy, if_pos hyx, starRingEnd_apply,
        star_trivial, mul_one]
      have hB₁c : (B₁.card : Real) ≠ 0 := by
        exact_mod_cast hB₁.card_ne_zero
      have hB₂c : (B₂.card : Real) ≠ 0 := by
        exact_mod_cast hB₂.card_ne_zero
      field_simp
    · simp [hy, hyx]
    · simp [hy]
    · simp [hy]
  have hnorm := wLpNorm_pow_eq_sum_norm hp
    (μ_[NNReal] B₁ ○ᵈ μ B₂) corr
  rw [hleft] at hraw
  simp only [mul_one] at hraw
  calc
    (∑ u : Fin p → G,
        ((Sifting.siftedSet A B₁ u).card : Real) *
          (Sifting.siftedSet A B₂ u).card) =
        ∑ b₁ ∈ B₁, ∑ b₂ ∈ B₂,
          (Sifting.commonShiftCount A (b₁ - b₂) : Real) ^ p := by
      simpa using hraw
    _ =
        ∑ x : G, (𝟭_[B₁, Real] ○ᵈ 𝟭_[B₂]) x * corr x ^ p := by
      exact hright
    _ = (B₁.card : Real) * B₂.card *
          ∑ x : G, (μ_[Real] B₁ ○ᵈ μ B₂) x * corr x ^ p := by
      rw [hweight]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = (B₁.card : Real) * B₂.card *
        ‖𝟭_[A, Real] ○ᵈ 𝟭_[A]‖_[p, μ B₁ ○ᵈ μ B₂] ^ p := by
      congr 1
      rw [hnorm]
      apply Finset.sum_congr rfl
      intro x _
      simp only [NNReal.smul_def, smul_eq_mul, Real.norm_eq_abs,
        abs_of_nonneg (hcorr x), NNReal.coe_dddconv,
        NNReal.coe_comp_mu, corr]

/-- First moment of one common-tuple sifted set. -/
theorem sum_card_siftedSet (A B : Finset G) (p : Nat) :
    (∑ u : Fin p → G, ((Sifting.siftedSet A B u).card : Real)) =
      (A.card : Real) ^ p * B.card := by
  classical
  have hnat :
      ∑ u : Fin p → G, (Sifting.siftedSet A B u).card =
        A.card ^ p * B.card := by
    simp only [card_eq_sum_indicator_one, Sifting.siftedSet,
      Set.indicator_apply, mem_coe, mem_filter, mem_univ, true_and,
      boole_mul, mul_sum, sum_mul, @sum_comm G, Fintype.piFinset_univ,
      sum_pow']
    congr with b
    refine Fintype.sum_equiv (Equiv.subLeft fun _ : Fin p ↦ b) _ _ (fun u ↦ ?_)
    simp only [Equiv.subLeft_apply]
    by_cases hb : b ∈ B
    · simp only [hb, true_and, if_pos, mul_one]
      rw [Fintype.prod_boole]
      simp only [Pi.sub_apply]
      by_cases h : ∀ i : Fin p, b - u i ∈ A <;> simp [h]
    · simp [hb]
  exact_mod_cast hnat

/-- A common shift tuple simultaneously gives both sifting density bounds.
The proof is the high-product tail selection from dependent random choice,
kept separate so that the common-tuple support information remains usable. -/
theorem exists_common_sifted_density
    (A B₁ B₂ : Finset G) (p : Nat) (hpTwo : 2 ≤ p)
    (hB : (B₁ ∩ B₂).Nonempty) (hA : A.Nonempty) :
    ∃ u : Fin p → G,
      (Sifting.siftedSet A B₁ u).Nonempty ∧
      (Sifting.siftedSet A B₂ u).Nonempty ∧
      siftingDensityLower A B₁ B₂ p ≤
        ((Sifting.siftedSet A B₁ u).card : Real) / B₁.card ∧
      siftingDensityLower A B₁ B₂ p ≤
        ((Sifting.siftedSet A B₂ u).card : Real) / B₂.card := by
  classical
  have hp : p ≠ 0 := by omega
  have hB₁ : B₁.Nonempty := hB.mono inter_subset_left
  have hB₂ : B₂.Nonempty := hB.mono inter_subset_right
  have hAne : A.Nonempty := hA
  let A₁ : (Fin p → G) → Finset G := fun u ↦ Sifting.siftedSet A B₁ u
  let A₂ : (Fin p → G) → Finset G := fun u ↦ Sifting.siftedSet A B₂ u
  let N : Real := ‖𝟭_[A, Real] ○ᵈ 𝟭_[A]‖_[p, μ B₁ ○ᵈ μ B₂]
  let g : (Fin p → G) → Real := fun u ↦ (A₁ u).card * (A₂ u).card
  have hg : ∀ u, 0 ≤ g u := fun u ↦ by dsimp [g]; positivity
  have hgB : ∑ u, g u = (B₁.card : Real) * B₂.card * N ^ p := by
    simpa [g, A₁, A₂, N] using
      sum_card_siftedSet_mul_card_siftedSet A B₁ B₂ p hp hB₁ hB₂
  obtain ⟨b, hb⟩ := hB
  obtain ⟨a, ha⟩ := hA
  let u₀ : Fin p → G := fun _ ↦ b - a
  have hA₁u₀ : b ∈ A₁ u₀ := by
    simp only [A₁, Sifting.mem_siftedSet, u₀]
    refine ⟨(inter_subset_left hb), ?_⟩
    intro i
    have : b - (b - a) = a := by abel
    rwa [this]
  have hA₂u₀ : b ∈ A₂ u₀ := by
    simp only [A₂, Sifting.mem_siftedSet, u₀]
    refine ⟨(inter_subset_right hb), ?_⟩
    intro i
    have : b - (b - a) = a := by abel
    rwa [this]
  have hsumPos : 0 < ∑ u, g u := by
    exact Finset.sum_pos' (fun u _ ↦ hg u) ⟨u₀, Finset.mem_univ _, by
      dsimp only [g]
      exact mul_pos (by exact_mod_cast (Finset.card_pos.mpr ⟨b, hA₁u₀⟩))
        (by exact_mod_cast (Finset.card_pos.mpr ⟨b, hA₂u₀⟩))⟩
  have hNp : 0 < N ^ p := by
    have hcards : 0 < (B₁.card : Real) * B₂.card := by positivity
    rw [hgB] at hsumPos
    rcases mul_pos_iff.mp hsumPos with hpos | hneg
    · exact hpos.2
    · exact (not_lt_of_ge hcards.le hneg.1).elim
  let M : Real :=
    2⁻¹ * N ^ p * (Real.sqrt B₁.card * Real.sqrt B₂.card) /
      (A.card : Real) ^ p
  have hM : 0 < M := by
    dsimp [M]
    have hAc : (0 : Real) < A.card := by exact_mod_cast hAne.card_pos
    have hB₁c : (0 : Real) < B₁.card := by exact_mod_cast hB₁.card_pos
    have hB₂c : (0 : Real) < B₂.card := by exact_mod_cast hB₂.card_pos
    exact div_pos (mul_pos (mul_pos (by norm_num) hNp)
      (mul_pos (Real.sqrt_pos.2 hB₁c) (Real.sqrt_pos.2 hB₂c)))
      (pow_pos hAc p)
  have hsumOne : ∑ u, ((A₁ u).card : Real) = (A.card : Real) ^ p * B₁.card := by
    simpa [A₁] using sum_card_siftedSet A B₁ p
  have hsumTwo : ∑ u, ((A₂ u).card : Real) = (A.card : Real) ^ p * B₂.card := by
    simpa [A₂] using sum_card_siftedSet A B₂ p
  have hhigh : ∃ u, M ^ 2 ≤ g u := by
    by_cases h : ∀ u, g u ≠ 0 → M ^ 2 ≤ g u
    · have hne : ∃ u, g u ≠ 0 := by
        by_contra hn
        push_neg at hn
        have : ∑ u, g u = 0 := by simp [hn]
        linarith
      obtain ⟨u, hu⟩ := hne
      exact ⟨u, h u hu⟩
    · push_neg at h
      obtain ⟨u₁, hu₁ne, hu₁low⟩ := h
      have hlow : (2 : Real) * ∑ u with g u < M ^ 2, g u < ∑ u, g u := by
        rw [← lt_div_iff₀' (by norm_num : (0 : Real) < 2), div_eq_inv_mul]
        calc
          ∑ u with g u < M ^ 2, g u =
              ∑ u with g u < M ^ 2 ∧ g u ≠ 0,
                Real.sqrt (g u) * Real.sqrt (g u) := by
            simp_rw [Real.mul_self_sqrt (hg _), ← Finset.filter_filter,
              Finset.sum_filter_ne_zero]
          _ < ∑ u with g u < M ^ 2 ∧ g u ≠ 0,
                M * Real.sqrt (g u) := by
            apply Finset.sum_lt_sum_of_nonempty
            · exact ⟨u₁, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu₁low, hu₁ne⟩⟩
            · intro u hu
              have hgu := (Finset.mem_filter.mp hu).2.1
              have hgne := (Finset.mem_filter.mp hu).2.2
              exact mul_lt_mul_of_pos_right ((Real.sqrt_lt' hM).2 hgu)
                (Real.sqrt_pos.2 ((hg u).lt_of_ne' hgne))
          _ ≤ ∑ u, M * Real.sqrt (g u) :=
            Finset.sum_le_univ_sum_of_nonneg fun u ↦ by positivity
          _ = M * (∑ u, Real.sqrt ((A₁ u).card) *
                Real.sqrt ((A₂ u).card)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro u _
            dsimp only [g]
            rw [Real.sqrt_mul (by positivity : (0 : Real) ≤ (A₁ u).card)]
          _ ≤ M * (Real.sqrt (∑ u, ((A₁ u).card : Real)) *
                Real.sqrt (∑ u, ((A₂ u).card : Real))) := by
            gcongr
            exact Real.sum_sqrt_mul_sqrt_le _ (fun _ ↦ by positivity)
              (fun _ ↦ by positivity)
          _ = (2 : Real)⁻¹ * ∑ u, g u := by
            dsimp only [M]
            rw [hsumOne, hsumTwo, Real.sqrt_mul' _ (by positivity),
              Real.sqrt_mul' _ (by positivity),
              mul_mul_mul_comm (Real.sqrt _), Real.mul_self_sqrt,
              ← mul_assoc, div_mul_cancel₀, ← Real.sqrt_mul,
              mul_assoc, Real.mul_self_sqrt, hgB, mul_right_comm, mul_assoc]
            all_goals positivity
      by_contra hnone
      push_neg at hnone
      have hpartition : ∑ u, g u = ∑ u with g u < M ^ 2, g u := by
        congr 1
        symm
        exact Finset.filter_eq_self.mpr (fun u _ ↦ hnone u)
      rw [hpartition] at hlow
      linarith
  obtain ⟨u, hu⟩ := hhigh
  have hprod : siftingDensityLower A B₁ B₂ p ≤
      (((A₁ u).card : Real) / B₁.card) *
        (((A₂ u).card : Real) / B₂.card) := by
    dsimp [siftingDensityLower, M, N, g] at hu ⊢
    have hAc : (A.card : Real) ≠ 0 := by exact_mod_cast hAne.card_ne_zero
    have hB₁c : (B₁.card : Real) ≠ 0 := by exact_mod_cast hB₁.card_ne_zero
    have hB₂c : (B₂.card : Real) ≠ 0 := by exact_mod_cast hB₂.card_ne_zero
    rw [div_mul_div_comm, le_div_iff₀ (by positivity)]
    simpa [mul_pow, div_pow, pow_mul', show (2 : Real) ^ 2 = 4 by norm_num,
      Real.sq_sqrt (show 0 ≤ (B₁.card : Real) by positivity),
      Real.sq_sqrt (show 0 ≤ (B₂.card : Real) by positivity),
      hAc, hB₁c, hB₂c, mul_div_right_comm] using hu
  have hguPos : 0 < g u := (sq_pos_of_pos hM).trans_le hu
  have hcardsPos : 0 < ((A₁ u).card : Real) * (A₂ u).card := by
    simpa only [g] using hguPos
  have hpairs : 0 < ((A₁ u).card : Real) ∧ 0 < ((A₂ u).card : Real) := by
    rcases mul_pos_iff.mp hcardsPos with hpos | hneg
    · exact hpos
    · exact (not_lt_of_ge (Nat.cast_nonneg _) hneg.1).elim
  have hA₁pos : 0 < ((A₁ u).card : Real) := hpairs.1
  have hA₂pos : 0 < ((A₂ u).card : Real) := hpairs.2
  refine ⟨u, Finset.card_pos.mp (by exact_mod_cast hA₁pos),
    Finset.card_pos.mp (by exact_mod_cast hA₂pos), ?_, ?_⟩
  · have hcard₂ : ((A₂ u).card : Real) ≤ B₂.card := by
      exact_mod_cast Finset.card_le_card (Sifting.siftedSet_subset A B₂ u)
    exact hprod.trans (mul_le_of_le_one_right (by positivity)
      ((div_le_one (by positivity : (0 : Real) < B₂.card)).2 hcard₂))
  · have hcard₁ : ((A₁ u).card : Real) ≤ B₁.card := by
      exact_mod_cast Finset.card_le_card (Sifting.siftedSet_subset A B₁ u)
    exact hprod.trans (mul_le_of_le_one_left (by positivity)
      ((div_le_one (by positivity : (0 : Real) < B₁.card)).2 hcard₁))

/-- Concrete sifting output, including the two quantitative density bounds
which are needed when localized almost-periodicity is converted into a
Bohr-child size estimate. -/
structure SiftedPopularData (A B₁ B₂ : Finset G)
    (p : Nat) (epsilon delta : Real) where
  A₁ : Finset G
  A₂ : Finset G
  subset_one : A₁ ⊆ B₁
  subset_two : A₂ ⊆ B₂
  popular_mass : 1 - delta ≤
    LocalizedAlmostPeriodicity.countingInner
      (LocalizedAlmostPeriodicity.differenceConvolution
        (LocalizedAlmostPeriodicity.probabilityIndicator A₁)
        (LocalizedAlmostPeriodicity.probabilityIndicator A₂))
      (LocalizedAlmostPeriodicity.setIndicator (s p epsilon B₁ B₂ A))
  density_one : siftingDensityLower A B₁ B₂ p ≤
    (A₁.card : Real) / B₁.card
  density_two : siftingDensityLower A B₁ B₂ p ≤
    (A₂.card : Real) / B₂.card

namespace SiftedPopularData

/-- The global APAP popular set intersected with the actual base-pair
difference support.  This is the set used in local almost-periodicity:
its cardinality is controlled by the two local base sets rather than by the
ambient group. -/
def supportedPopularSet
    (A B₁ B₂ : Finset G) (p : Nat) (epsilon : Real) : Finset G :=
  _root_.s p epsilon B₁ B₂ A ∩ (B₁ - B₂)

theorem supportedPopularSet_subset_sub
    (A B₁ B₂ : Finset G) (p : Nat) (epsilon : Real) :
    supportedPopularSet A B₁ B₂ p epsilon ⊆ B₁ - B₂ :=
  Finset.inter_subset_right

theorem card_supportedPopularSet_le_card_sub
    (A B₁ B₂ : Finset G) (p : Nat) (epsilon : Real) :
    (supportedPopularSet A B₁ B₂ p epsilon).card ≤ (B₁ - B₂).card :=
  Finset.card_le_card (supportedPopularSet_subset_sub A B₁ B₂ p epsilon)

/-- Positive retained mass forces both sifted sets to be genuine nonempty
sets.  This small fact is essential before they may be used as probability
indicators by localized almost-periodicity. -/
theorem output_nonempty
    {A B₁ B₂ : Finset G} {p : Nat} {epsilon delta : Real}
    (data : SiftedPopularData A B₁ B₂ p epsilon delta)
    (hdelta : delta < 1) : data.A₁.Nonempty ∧ data.A₂.Nonempty := by
  have hmass : 1 - delta ≤
      ∑ x ∈ s p epsilon B₁ B₂ A, (μ_[Real] data.A₁ ○ᵈ μ data.A₂) x := by
    simpa only [countingInner_difference_setIndicator_eq_sum] using
      data.popular_mass
  constructor
  · by_contra hnonempty
    have hempty : data.A₁ = ∅ := not_nonempty_iff_eq_empty.mp hnonempty
    rw [hempty] at hmass
    simp [mu_apply] at hmass
    linarith
  · by_contra hnonempty
    have hempty : data.A₂ = ∅ := not_nonempty_iff_eq_empty.mp hnonempty
    rw [hempty] at hmass
    simp [mu_apply] at hmass
    linarith

/-- Intersecting the popular set with B₁-B₂ does not change the retained
mass, because every difference carrying μ_A₁ ○ μ_A₂ already lies there. -/
theorem supported_popular_mass
    {A B₁ B₂ : Finset G} {p : Nat} {epsilon delta : Real}
    (data : SiftedPopularData A B₁ B₂ p epsilon delta) :
    1 - delta ≤
      LocalizedAlmostPeriodicity.countingInner
        (LocalizedAlmostPeriodicity.differenceConvolution
          (LocalizedAlmostPeriodicity.probabilityIndicator data.A₁)
          (LocalizedAlmostPeriodicity.probabilityIndicator data.A₂))
        (LocalizedAlmostPeriodicity.setIndicator
          (supportedPopularSet A B₁ B₂ p epsilon)) := by
  have hglobal : 1 - delta ≤
      ∑ x ∈ _root_.s p epsilon B₁ B₂ A,
        (μ_[Real] data.A₁ ○ᵈ μ data.A₂) x := by
    simpa only [countingInner_difference_setIndicator_eq_sum] using
      data.popular_mass
  have hsum :
      ∑ x ∈ supportedPopularSet A B₁ B₂ p epsilon,
          (μ_[Real] data.A₁ ○ᵈ μ data.A₂) x =
        ∑ x ∈ _root_.s p epsilon B₁ B₂ A,
          (μ_[Real] data.A₁ ○ᵈ μ data.A₂) x := by
    apply Finset.sum_subset Finset.inter_subset_left
    intro x hxGlobal hxNot
    rw [← not_ne_iff]
    intro hxNe
    apply hxNot
    have hxSupport :
        x ∈ Function.support (μ_[Real] data.A₁ ○ᵈ μ data.A₂) := hxNe
    have hxDiff : x ∈ data.A₁ - data.A₂ := by
      simpa only [support_dddconv mu_nonneg mu_nonneg, support_mu,
        ← coe_sub, mem_coe] using hxSupport
    obtain ⟨a₁, ha₁, a₂, ha₂, hxa⟩ := Finset.mem_sub.mp hxDiff
    exact Finset.mem_inter.mpr ⟨hxGlobal,
      Finset.mem_sub.mpr ⟨a₁, data.subset_one ha₁, a₂,
        data.subset_two ha₂, hxa⟩⟩
  rw [countingInner_difference_setIndicator_eq_sum, hsum]
  exact hglobal

/-- A normalized difference convolution is pointwise bounded by the
reciprocal of the left set size.  We use the right probability measure as
the summation variable, so the translate still has total mass one. -/
theorem dddconv_mu_le_inv_card_left
    (A₁ A₂ : Finset G) (hA₂ : A₂.Nonempty) (x : G) :
    (μ_[Real] A₁ ○ᵈ μ A₂) x ≤ (A₁.card : Real)⁻¹ := by
  rw [dddconv_eq_sum_sub']
  simp only [starRingEnd_apply, star_trivial]
  calc
    ∑ y : G, μ_[Real] A₁ y * μ A₂ (y - x) ≤
        ∑ y : G, (A₁.card : Real)⁻¹ * μ_[Real] A₂ (y - x) := by
      apply Finset.sum_le_sum
      intro y _
      apply mul_le_mul_of_nonneg_right
      · rw [mu_apply]
        split_ifs <;> simp
      · rw [mu_apply]
        positivity
    _ = (A₁.card : Real)⁻¹ * ∑ y : G, μ_[Real] A₂ (y - x) := by
      rw [Finset.mul_sum]
    _ = (A₁.card : Real)⁻¹ * ∑ y : G, μ_[Real] A₂ y := by
      congr 1
      simpa only [translate_apply] using (sum_translate x (μ_[Real] A₂))
    _ = (A₁.card : Real)⁻¹ := by
      rw [sum_mu Real hA₂, mul_one]

/-- The retained supported mass forces the supported popular set to have
at least (1 - delta) * |A₁| elements.  This is the quantitative lower
bound that keeps the Croot--Sisask sampling ratio local and uniform. -/
theorem one_sub_delta_mul_card_le_card_supportedPopularSet
    {A B₁ B₂ : Finset G} {p : Nat} {epsilon delta : Real}
    (data : SiftedPopularData A B₁ B₂ p epsilon delta)
    (hdelta : delta < 1) :
    (1 - delta) * (data.A₁.card : Real) ≤
      (supportedPopularSet A B₁ B₂ p epsilon).card := by
  have houtputs := data.output_nonempty hdelta
  have hmass :
      1 - delta ≤
        ∑ x ∈ supportedPopularSet A B₁ B₂ p epsilon,
          (μ_[Real] data.A₁ ○ᵈ μ data.A₂) x := by
    simpa only [countingInner_difference_setIndicator_eq_sum] using
      data.supported_popular_mass
  have hupper :
      ∑ x ∈ supportedPopularSet A B₁ B₂ p epsilon,
          (μ_[Real] data.A₁ ○ᵈ μ data.A₂) x ≤
        (supportedPopularSet A B₁ B₂ p epsilon).card *
          (data.A₁.card : Real)⁻¹ := by
    calc
      ∑ x ∈ supportedPopularSet A B₁ B₂ p epsilon,
          (μ_[Real] data.A₁ ○ᵈ μ data.A₂) x ≤
          ∑ x ∈ supportedPopularSet A B₁ B₂ p epsilon,
            (data.A₁.card : Real)⁻¹ := by
        apply Finset.sum_le_sum
        intro x _
        exact dddconv_mu_le_inv_card_left data.A₁ data.A₂ houtputs.2 x
      _ = (supportedPopularSet A B₁ B₂ p epsilon).card *
          (data.A₁.card : Real)⁻¹ := by
        simp
  have hratio :
      1 - delta ≤
        (supportedPopularSet A B₁ B₂ p epsilon).card /
          (data.A₁.card : Real) := by
    calc
      1 - delta ≤
          ∑ x ∈ supportedPopularSet A B₁ B₂ p epsilon,
            (μ_[Real] data.A₁ ○ᵈ μ data.A₂) x := hmass
      _ ≤ (supportedPopularSet A B₁ B₂ p epsilon).card *
          (data.A₁.card : Real)⁻¹ := hupper
      _ = (supportedPopularSet A B₁ B₂ p epsilon).card /
          (data.A₁.card : Real) := by rw [div_eq_mul_inv]
  exact (le_div_iff₀ (by exact_mod_cast houtputs.1.card_pos)).mp hratio

/-- When the discarded mass is at most one half, at least half of the left
sifted set survives in the support-restricted popular set. -/
theorem card_div_two_le_card_supportedPopularSet
    {A B₁ B₂ : Finset G} {p : Nat} {epsilon delta : Real}
    (data : SiftedPopularData A B₁ B₂ p epsilon delta)
    (hdelta : delta ≤ 1 / 2) :
    (data.A₁.card : Real) / 2 ≤
      (supportedPopularSet A B₁ B₂ p epsilon).card := by
  have hdelta' : delta < 1 := lt_of_le_of_lt hdelta (by norm_num)
  have hmain :=
    data.one_sub_delta_mul_card_le_card_supportedPopularSet hdelta'
  calc
    (data.A₁.card : Real) / 2 =
        (1 / 2 : Real) * data.A₁.card := by ring
    _ ≤ (1 - delta) * data.A₁.card := by
      gcongr
      linarith
    _ ≤ (supportedPopularSet A B₁ B₂ p epsilon).card := hmain

/-- Positive supported popular mass makes the support-restricted popular set
nonempty. -/
theorem supportedPopularSet_nonempty
    {A B₁ B₂ : Finset G} {p : Nat} {epsilon delta : Real}
    (data : SiftedPopularData A B₁ B₂ p epsilon delta)
    (hdelta : delta < 1) :
    (supportedPopularSet A B₁ B₂ p epsilon).Nonempty := by
  by_contra hnone
  have hempty : supportedPopularSet A B₁ B₂ p epsilon = ∅ :=
    not_nonempty_iff_eq_empty.mp hnone
  have hmass := data.supported_popular_mass
  rw [hempty] at hmass
  simp [LocalizedAlmostPeriodicity.countingInner,
    LocalizedAlmostPeriodicity.setIndicator] at hmass
  linarith

end SiftedPopularData

/-- Direct, lossless invocation of sifting.  Unlike the lighter wrapper
below, this certificate retains the two `1/4` density estimates. -/
theorem exists_sifted_popular_data
    {A : Finset G} {p : Nat} {epsilon delta : Real}
    (B₁ B₂ : Finset G) (hepsilon : 0 < epsilon) (hepsilonOne : epsilon ≤ 1)
    (hdelta : 0 < delta) (hp : Even p) (hpTwo : 2 ≤ p)
    (hpEpsilon : epsilon⁻¹ * Real.log (2 / delta) ≤ p)
    (hB : (B₁ ∩ B₂).Nonempty) (hA : A.Nonempty)
    (hbad : ∃ x, x ∈ B₁ - B₂ ∧ x ∈ A - A ∧
      x ∉ s p epsilon B₁ B₂ A) :
    Nonempty (SiftedPopularData A B₁ B₂ p epsilon delta) := by
  obtain ⟨A₁, hA₁, A₂, hA₂, hmass, hden₁, hden₂⟩ :=
    Sifting.popularDifferences B₁ B₂ hepsilon hepsilonOne hdelta hp hpTwo
      hpEpsilon hB hA hbad
  refine ⟨{
    A₁ := A₁
    A₂ := A₂
    subset_one := hA₁
    subset_two := hA₂
    popular_mass := ?_
    density_one := ?_
    density_two := ?_ }⟩
  · rwa [countingInner_difference_setIndicator_eq_sum]
  · simpa only [siftingDensityLower] using hden₁
  · simpa only [siftingDensityLower] using hden₂

/-- In the complementary sifting branch, choose the two sifted sets from a
single high-product tuple.  Their whole difference support lies in `A-A`,
so the absence of an exceptional supported difference makes their popular
mass exactly one. -/
theorem exists_sifted_popular_data_of_no_bad
    {A : Finset G} {p : Nat} {epsilon delta : Real}
    (B₁ B₂ : Finset G) (hdelta : 0 < delta) (hpTwo : 2 ≤ p)
    (hB : (B₁ ∩ B₂).Nonempty) (hA : A.Nonempty)
    (hsupport : ∀ x, x ∈ B₁ - B₂ → x ∈ A - A →
      x ∈ s p epsilon B₁ B₂ A) :
    Nonempty (SiftedPopularData A B₁ B₂ p epsilon delta) := by
  classical
  obtain ⟨u, hA₁, hA₂, hden₁, hden₂⟩ :=
    exists_common_sifted_density A B₁ B₂ p hpTwo hB hA
  let A₁ := Sifting.siftedSet A B₁ u
  let A₂ := Sifting.siftedSet A B₂ u
  have hsub₁ : A₁ ⊆ B₁ := Sifting.siftedSet_subset A B₁ u
  have hsub₂ : A₂ ⊆ B₂ := Sifting.siftedSet_subset A B₂ u
  have hp : 0 < p := by omega
  let i : Fin p := ⟨0, hp⟩
  have hdiff : A₁ - A₂ ⊆ s p epsilon B₁ B₂ A := by
    intro x hx
    obtain ⟨a₁, ha₁, a₂, ha₂, hxa⟩ := Finset.mem_sub.mp hx
    apply hsupport x
    · exact Finset.mem_sub.mpr ⟨a₁, hsub₁ ha₁, a₂, hsub₂ ha₂, hxa⟩
    · have ha₁A := (Sifting.mem_siftedSet.mp ha₁).2 i
      have ha₂A := (Sifting.mem_siftedSet.mp ha₂).2 i
      refine Finset.mem_sub.mpr ⟨a₁ - u i, ha₁A, a₂ - u i, ha₂A, ?_⟩
      rw [← hxa]
      abel
  have hsum :
      ∑ x ∈ s p epsilon B₁ B₂ A, (μ_[Real] A₁ ○ᵈ μ A₂) x = 1 := by
    calc
      ∑ x ∈ s p epsilon B₁ B₂ A, (μ_[Real] A₁ ○ᵈ μ A₂) x =
          ∑ x : G, (μ_[Real] A₁ ○ᵈ μ A₂) x := by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro x _ hxnot
        rw [← not_ne_iff]
        intro hxne
        apply hxnot
        apply hdiff
        have hxmem : x ∈ Function.support (μ_[Real] A₁ ○ᵈ μ A₂) := hxne
        simpa only [support_dddconv mu_nonneg mu_nonneg, support_mu,
          ← coe_sub, mem_coe] using hxmem
      _ = 1 := by
        rw [sum_dddconv]
        simp only [starRingEnd_apply, star_trivial]
        rw [sum_mu _ (by simpa [A₁] using hA₁),
          sum_mu _ (by simpa [A₂] using hA₂), one_mul]
  refine ⟨{
    A₁ := A₁
    A₂ := A₂
    subset_one := hsub₁
    subset_two := hsub₂
    popular_mass := ?_
    density_one := by simpa [A₁] using hden₁
    density_two := by simpa [A₂] using hden₂ }⟩
  rw [countingInner_difference_setIndicator_eq_sum, hsum]
  linarith

/-- Unconditional localized sifting: the exceptional-difference branch is
the public DRC theorem, while its complement is the common-tuple
construction above. -/
theorem exists_sifted_popular_data_unconditional
    {A : Finset G} {p : Nat} {epsilon delta : Real}
    (B₁ B₂ : Finset G) (hepsilon : 0 < epsilon) (hepsilonOne : epsilon ≤ 1)
    (hdelta : 0 < delta) (hp : Even p) (hpTwo : 2 ≤ p)
    (hpEpsilon : epsilon⁻¹ * Real.log (2 / delta) ≤ p)
    (hB : (B₁ ∩ B₂).Nonempty) (hA : A.Nonempty) :
    Nonempty (SiftedPopularData A B₁ B₂ p epsilon delta) := by
  classical
  by_cases hbad : ∃ x, x ∈ B₁ - B₂ ∧ x ∈ A - A ∧
      x ∉ s p epsilon B₁ B₂ A
  · exact exists_sifted_popular_data B₁ B₂ hepsilon hepsilonOne
      hdelta hp hpTwo hpEpsilon hB hA hbad
  · apply exists_sifted_popular_data_of_no_bad B₁ B₂ hdelta hpTwo hB hA
    intro x hxB hxA
    by_contra hxS
    exact hbad ⟨x, hxB, hxA, hxS⟩

/-- The assumption in the sifting lemma is discharged by an exact
dichotomy.  If no exceptional supported difference exists, every difference
which can carry the comparison weight is already popular; otherwise the
full quantitative sifting certificate is produced. -/
theorem popular_support_or_sifted_data
    {A : Finset G} {p : Nat} {epsilon delta : Real}
    (B₁ B₂ : Finset G) (hepsilon : 0 < epsilon) (hepsilonOne : epsilon ≤ 1)
    (hdelta : 0 < delta) (hp : Even p) (hpTwo : 2 ≤ p)
    (hpEpsilon : epsilon⁻¹ * Real.log (2 / delta) ≤ p)
    (hB : (B₁ ∩ B₂).Nonempty) (hA : A.Nonempty) :
    (∀ x, x ∈ B₁ - B₂ → x ∈ A - A →
      x ∈ s p epsilon B₁ B₂ A) ∨
      Nonempty (SiftedPopularData A B₁ B₂ p epsilon delta) := by
  classical
  by_cases hbad : ∃ x, x ∈ B₁ - B₂ ∧ x ∈ A - A ∧
      x ∉ s p epsilon B₁ B₂ A
  · exact Or.inr (exists_sifted_popular_data B₁ B₂ hepsilon
      hepsilonOne hdelta hp hpTwo hpEpsilon hB hA hbad)
  · left
    intro x hxB hxA
    by_contra hxS
    exact hbad ⟨x, hxB, hxA, hxS⟩

/-- Direct invocation of the proved sifting theorem, converted to the
counting-sum normalization consumed by localized almost-periodicity. -/
theorem exists_sifted_popular_mass
    {A : Finset G} {p : Nat} {epsilon delta : Real}
    (B₁ B₂ : Finset G) (hepsilon : 0 < epsilon) (hepsilonOne : epsilon ≤ 1)
    (hdelta : 0 < delta) (hp : Even p) (hpTwo : 2 ≤ p)
    (hpEpsilon : epsilon⁻¹ * Real.log (2 / delta) ≤ p)
    (hB : (B₁ ∩ B₂).Nonempty) (hA : A.Nonempty)
    (hbad : ∃ x, x ∈ B₁ - B₂ ∧ x ∈ A - A ∧
      x ∉ s p epsilon B₁ B₂ A) :
    ∃ A₁, A₁ ⊆ B₁ ∧ ∃ A₂, A₂ ⊆ B₂ ∧
      1 - delta ≤
        LocalizedAlmostPeriodicity.countingInner
          (LocalizedAlmostPeriodicity.differenceConvolution
            (LocalizedAlmostPeriodicity.probabilityIndicator A₁)
            (LocalizedAlmostPeriodicity.probabilityIndicator A₂))
          (LocalizedAlmostPeriodicity.setIndicator (s p epsilon B₁ B₂ A)) := by
  obtain ⟨A₁, hA₁, A₂, hA₂, hmass, _hden₁, _hden₂⟩ :=
    Sifting.popularDifferences B₁ B₂ hepsilon hepsilonOne hdelta hp hpTwo
      hpEpsilon hB hA hbad
  refine ⟨A₁, hA₁, A₂, hA₂, ?_⟩
  rwa [countingInner_difference_setIndicator_eq_sum]

/-- The exact interface between sifting and the relative Fourier
almost-periodicity construction.  It records an actual rank-regular Bohr
datum, its subordination and relative-cardinality estimates, and the
pointwise triple-sum error which localized smoothing consumes.  None of the
fields asserts a density increment or a progression-count conclusion. -/
structure LocalizedSiftingPackage
    {A B₁ B₂ : Finset G} {p : Nat} {epsilon delta : Real}
    (data : SiftedPopularData A B₁ B₂ p epsilon delta)
    (parent : BohrData G) (parentWidth : NNReal)
    (source : Finset G) (rankCost cardMultiplier : Nat)
    (approximationError : Real) where
  child : BohrData G
  child_regular : child.IsRankRegular
  rank_bound : child.rank ≤ parent.rank + rankCost
  subordinate : child.carrier ⊆ (parent.dilate parentWidth).carrier
  relative_card : source.card ≤ cardMultiplier * child.carrier.card
  triple_error : ∀ t ∈ child.carrier,
    |LocalizedAlmostPeriodicity.tripleIndicatorSum
        data.A₁ data.A₂ (s p epsilon B₁ B₂ A) t -
      LocalizedAlmostPeriodicity.tripleIndicatorSum
        data.A₁ data.A₂ (s p epsilon B₁ B₂ A) 0| ≤
      approximationError * (data.A₁.card : Real) * data.A₂.card

/-- Enlarge the three numerical budgets of a localized sifting package.
This is the adapter used after the existential Croot--Sisask/Chang output is
dominated by the uniform rank, volume, and error budgets of a stopping step. -/
def LocalizedSiftingPackage.mono
    {A B₁ B₂ : Finset G} {p : Nat} {epsilon delta : Real}
    {data : SiftedPopularData A B₁ B₂ p epsilon delta}
    {parent : BohrData G} {parentWidth : NNReal} {source : Finset G}
    {rankCost cardMultiplier rankCost' cardMultiplier' : Nat}
    {approximationError approximationError' : Real}
    (P : LocalizedSiftingPackage data parent parentWidth source
      rankCost cardMultiplier approximationError)
    (hrank : rankCost ≤ rankCost')
    (hcard : cardMultiplier ≤ cardMultiplier')
    (herror : approximationError ≤ approximationError') :
    LocalizedSiftingPackage data parent parentWidth source
      rankCost' cardMultiplier' approximationError' where
  child := P.child
  child_regular := P.child_regular
  rank_bound := P.rank_bound.trans (Nat.add_le_add_left hrank _)
  subordinate := P.subordinate
  relative_card := P.relative_card.trans
    (Nat.mul_le_mul_right P.child.carrier.card hcard)
  triple_error := by
    intro t ht
    calc
      |LocalizedAlmostPeriodicity.tripleIndicatorSum
          data.A₁ data.A₂ (_root_.s p epsilon B₁ B₂ A) t -
        LocalizedAlmostPeriodicity.tripleIndicatorSum
          data.A₁ data.A₂ (_root_.s p epsilon B₁ B₂ A) 0|
          ≤ approximationError * (data.A₁.card : Real) * data.A₂.card :=
        P.triple_error t ht
      _ ≤ approximationError' * (data.A₁.card : Real) * data.A₂.card := by
        gcongr

/-- Support-restricted analogue of LocalizedSiftingPackage.  Its triple
error is stated on the actual pair-difference support, so local AP and Chang
see only a set whose size is controlled by B₁-B₂. -/
structure SupportedLocalizedSiftingPackage
    {A B₁ B₂ : Finset G} {p : Nat} {epsilon delta : Real}
    (data : SiftedPopularData A B₁ B₂ p epsilon delta)
    (parent : BohrData G) (parentWidth : NNReal)
    (source : Finset G) (rankCost cardMultiplier : Nat)
    (approximationError : Real) where
  child : BohrData G
  child_regular : child.IsRankRegular
  rank_bound : child.rank ≤ parent.rank + rankCost
  subordinate : child.carrier ⊆ (parent.dilate parentWidth).carrier
  relative_card : source.card ≤ cardMultiplier * child.carrier.card
  triple_error : ∀ t ∈ child.carrier,
    |LocalizedAlmostPeriodicity.tripleIndicatorSum
        data.A₁ data.A₂
          (SiftedPopularData.supportedPopularSet A B₁ B₂ p epsilon) t -
      LocalizedAlmostPeriodicity.tripleIndicatorSum
        data.A₁ data.A₂
          (SiftedPopularData.supportedPopularSet A B₁ B₂ p epsilon) 0| ≤
      approximationError * (data.A₁.card : Real) * data.A₂.card

/-- Enlarge the numerical budgets of a support-restricted localized package. -/
def SupportedLocalizedSiftingPackage.mono
    {A B₁ B₂ : Finset G} {p : Nat} {epsilon delta : Real}
    {data : SiftedPopularData A B₁ B₂ p epsilon delta}
    {parent : BohrData G} {parentWidth : NNReal} {source : Finset G}
    {rankCost cardMultiplier rankCost' cardMultiplier' : Nat}
    {approximationError approximationError' : Real}
    (P : SupportedLocalizedSiftingPackage data parent parentWidth source
      rankCost cardMultiplier approximationError)
    (hrank : rankCost ≤ rankCost')
    (hcard : cardMultiplier ≤ cardMultiplier')
    (herror : approximationError ≤ approximationError') :
    SupportedLocalizedSiftingPackage data parent parentWidth source
      rankCost' cardMultiplier' approximationError' where
  child := P.child
  child_regular := P.child_regular
  rank_bound := P.rank_bound.trans (Nat.add_le_add_left hrank _)
  subordinate := P.subordinate
  relative_card := P.relative_card.trans
    (Nat.mul_le_mul_right P.child.carrier.card hcard)
  triple_error := by
    intro t ht
    calc
      |LocalizedAlmostPeriodicity.tripleIndicatorSum
          data.A₁ data.A₂
            (SiftedPopularData.supportedPopularSet A B₁ B₂ p epsilon) t -
        LocalizedAlmostPeriodicity.tripleIndicatorSum
          data.A₁ data.A₂
            (SiftedPopularData.supportedPopularSet A B₁ B₂ p epsilon) 0|
          ≤ approximationError * (data.A₁.card : Real) * data.A₂.card :=
        P.triple_error t ht
      _ ≤ approximationError' * (data.A₁.card : Real) * data.A₂.card := by
        gcongr

/-- The lossless sifting certificate and a concrete localized
almost-periodicity package imply the normalized smoothed popular-mass
bound.  This is the analytic input to the final adjoint/averaging step. -/
theorem localized_smoothed_popular_mass_lower_bound
    {A B₁ B₂ : Finset G} {p : Nat} {epsilon delta : Real}
    (data : SiftedPopularData A B₁ B₂ p epsilon delta)
    (hdelta : delta < 1)
    {parent : BohrData G} {parentWidth : NNReal}
    {source : Finset G} {rankCost cardMultiplier : Nat}
    {approximationError : Real}
    (P : LocalizedSiftingPackage data parent parentWidth source
      rankCost cardMultiplier approximationError) :
    1 - delta - approximationError ≤
      LocalizedAlmostPeriodicity.countingInner
        (LocalizedAlmostPeriodicity.sumConvolution
          (LocalizedAlmostPeriodicity.probabilityIndicator P.child.carrier)
          (LocalizedAlmostPeriodicity.differenceConvolution
            (LocalizedAlmostPeriodicity.probabilityIndicator data.A₁)
            (LocalizedAlmostPeriodicity.probabilityIndicator data.A₂)))
        (LocalizedAlmostPeriodicity.setIndicator
          (s p epsilon B₁ B₂ A)) := by
  have hnonempty := data.output_nonempty hdelta
  have hmass : 1 - delta ≤
      ∑ x ∈ s p epsilon B₁ B₂ A,
        (μ_[Real] data.A₁ ○ᵈ μ data.A₂) x := by
    simpa only [countingInner_difference_setIndicator_eq_sum] using
      data.popular_mass
  exact smoothed_popular_mass_lower_bound hnonempty.1 hnonempty.2
    hmass P.triple_error

/-- APAP's smoothed probability convolution is exactly the discrete
counting convolution used by the sifting and adjoint identities. -/
theorem sumConvolution_probability_difference_eq
    (D A₁ A₂ : Finset G) :
    LocalizedAlmostPeriodicity.sumConvolution
        (LocalizedAlmostPeriodicity.probabilityIndicator D)
        (LocalizedAlmostPeriodicity.differenceConvolution
          (LocalizedAlmostPeriodicity.probabilityIndicator A₁)
          (LocalizedAlmostPeriodicity.probabilityIndicator A₂)) =
      μ_[Real] D ∗ᵈ (μ A₁ ○ᵈ μ A₂) := by
  funext x
  rw [probabilityIndicator_eq_mu,
    differenceConvolution_probability_eq_dddconv,
    LocalizedAlmostPeriodicity.sumConvolution, ddconv_eq_sum_sub']

/-- Exact set-mass form of the localized smoothed inner product. -/
theorem countingInner_smoothed_setIndicator_eq_sum
    (D A₁ A₂ S : Finset G) :
    LocalizedAlmostPeriodicity.countingInner
        (LocalizedAlmostPeriodicity.sumConvolution
          (LocalizedAlmostPeriodicity.probabilityIndicator D)
          (LocalizedAlmostPeriodicity.differenceConvolution
            (LocalizedAlmostPeriodicity.probabilityIndicator A₁)
            (LocalizedAlmostPeriodicity.probabilityIndicator A₂)))
        (LocalizedAlmostPeriodicity.setIndicator S) =
      ∑ x ∈ S, (μ_[Real] D ∗ᵈ (μ A₁ ○ᵈ μ A₂)) x := by
  classical
  rw [sumConvolution_probability_difference_eq]
  unfold LocalizedAlmostPeriodicity.countingInner
    LocalizedAlmostPeriodicity.setIndicator
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  have hfilter : Finset.univ.filter (fun x : G ↦ x ∈ S) = S := by ext; simp
  rw [hfilter]

/-- A lower bound for smoothed mass on a superlevel set gives the
corresponding lower bound for the full correlation inner product.  This is
the positivity half of the adjoint step and keeps every counting
normalization explicit. -/
theorem smoothed_superlevel_inner_lower_bound
    {D A₁ A₂ S : Finset G} {corr : G → Real}
    {mass threshold : Real}
    (hthreshold : 0 ≤ threshold)
    (hcorr : ∀ x, 0 ≤ corr x)
    (hpopular : ∀ x ∈ S, threshold ≤ corr x)
    (hmass : mass ≤
      LocalizedAlmostPeriodicity.countingInner
        (LocalizedAlmostPeriodicity.sumConvolution
          (LocalizedAlmostPeriodicity.probabilityIndicator D)
          (LocalizedAlmostPeriodicity.differenceConvolution
            (LocalizedAlmostPeriodicity.probabilityIndicator A₁)
            (LocalizedAlmostPeriodicity.probabilityIndicator A₂)))
        (LocalizedAlmostPeriodicity.setIndicator S)) :
    threshold * mass ≤
      ∑ x : G, (μ_[Real] D ∗ᵈ (μ A₁ ○ᵈ μ A₂)) x * corr x := by
  classical
  rw [countingInner_smoothed_setIndicator_eq_sum] at hmass
  have hf_nonneg : ∀ x : G,
      0 ≤ (μ_[Real] D ∗ᵈ (μ A₁ ○ᵈ μ A₂)) x := by
    intro x
    exact ddconv_apply_nonneg mu_nonneg
      (fun y ↦ dddconv_apply_nonneg mu_nonneg mu_nonneg y) x
  calc
    threshold * mass ≤
        threshold * ∑ x ∈ S,
          (μ_[Real] D ∗ᵈ (μ A₁ ○ᵈ μ A₂)) x :=
      mul_le_mul_of_nonneg_left hmass hthreshold
    _ = ∑ x ∈ S,
        threshold * (μ_[Real] D ∗ᵈ (μ A₁ ○ᵈ μ A₂)) x := by
      rw [Finset.mul_sum]
    _ ≤ ∑ x ∈ S,
        (μ_[Real] D ∗ᵈ (μ A₁ ○ᵈ μ A₂)) x * corr x := by
      apply Finset.sum_le_sum
      intro x hx
      rw [mul_comm threshold]
      exact mul_le_mul_of_nonneg_left (hpopular x hx) (hf_nonneg x)
    _ ≤ ∑ x : G,
        (μ_[Real] D ∗ᵈ (μ A₁ ○ᵈ μ A₂)) x * corr x := by
      exact Finset.sum_le_univ_sum_of_nonneg fun x ↦
        mul_nonneg (hf_nonneg x) (hcorr x)

/-- A finite probability-weighted average cannot exceed every value of the
averaged function.  The witness is chosen at a genuine maximum of the
finite ambient group. -/
theorem exists_value_ge_probability_average
    {w f : G → Real} (hw : ∀ x, 0 ≤ w x)
    (hwsum : ∑ x : G, w x = 1) {lower : Real}
    (hlower : lower ≤ ∑ x : G, w x * f x) :
    ∃ x : G, lower ≤ f x := by
  classical
  obtain ⟨x, _hx, hxmax⟩ :=
    Finset.exists_max_image Finset.univ f (Finset.univ_nonempty :
      (Finset.univ : Finset G).Nonempty)
  refine ⟨x, hlower.trans ?_⟩
  calc
    ∑ y : G, w y * f y ≤ ∑ y : G, w y * f x := by
      apply Finset.sum_le_sum
      intro y _
      exact mul_le_mul_of_nonneg_left (hxmax y (by simp)) (hw y)
    _ = f x := by rw [← Finset.sum_mul, hwsum, one_mul]

/-- Support-sensitive form of finite probability selection.  This keeps the
selected point inside the finite support, which is essential when the point
is subsequently represented as a difference of two Bohr-carrier elements. -/
theorem exists_value_ge_probability_average_on
    {w f : G → Real} {T : Finset G} (hT : T.Nonempty)
    (hw : ∀ x, 0 ≤ w x) (hwsupport : ∀ x, x ∉ T → w x = 0)
    (hwsum : ∑ x : G, w x = 1) {lower : Real}
    (hlower : lower ≤ ∑ x : G, w x * f x) :
    ∃ x ∈ T, lower ≤ f x := by
  classical
  obtain ⟨x, hxT, hxmax⟩ := Finset.exists_max_image T f hT
  refine ⟨x, hxT, hlower.trans ?_⟩
  calc
    ∑ y : G, w y * f y ≤ ∑ y : G, w y * f x := by
      apply Finset.sum_le_sum
      intro y _
      by_cases hy : y ∈ T
      · exact mul_le_mul_of_nonneg_left (hxmax y hy) (hw y)
      · rw [hwsupport y hy, zero_mul, zero_mul]
    _ = f x := by rw [← Finset.sum_mul, hwsum, one_mul]

/-- The localized-unbalancing weight admits the cross-difference
factorization used to select the translate in the sifting argument. -/
theorem coe_smoothingWeight_eq_crossDifference
    (D E : Finset G) :
    ((↑) ∘ LocalizedUnbalancing.smoothingWeight D E : G → Real) =
      (μ_[Real] D ○ᵈ μ E) ∗ᵈ (μ E ○ᵈ μ D) := by
  unfold LocalizedUnbalancing.smoothingWeight
    LocalizedUnbalancing.smoothingBase
  simp only [NNReal.coe_comp_dddconv, NNReal.coe_comp_ddconv,
    NNReal.coe_comp_mu]
  symm
  rw [dddconv_ddconv_dddconv_comm, ddconv_comm (μ_[Real] E) (μ D)]

/-- Expanding the cross-difference factorization writes the high moment as
an average of moments against translated finite difference measures. -/
theorem smoothingWeight_absMoment_eq_crossAverage
    (D E : Finset G) (f : G → Real) (p : Nat) :
    weightedAbsMoment
        ((↑) ∘ LocalizedUnbalancing.smoothingWeight D E) f p =
      ∑ z : G, (μ_[Real] D ○ᵈ μ E) z *
        weightedAbsMoment
          (fun x ↦ (μ_[Real] E ○ᵈ μ D) (x - z)) f p := by
  rw [coe_smoothingWeight_eq_crossDifference]
  unfold weightedAbsMoment
  simp_rw [ddconv_eq_sum_sub', Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- A high moment under the fourfold smoothing weight selects a translate
`z + E` which genuinely meets `D`, while retaining the full moment lower
bound against `μ_(z+E) ○ μ_D`. -/
theorem exists_translated_difference_moment_ge
    {D E : Finset G} (hD : D.Nonempty) (hE : E.Nonempty)
    (f : G → Real) (p : Nat) {lower : Real}
    (hlower : lower ≤ weightedAbsMoment
      ((↑) ∘ LocalizedUnbalancing.smoothingWeight D E) f p) :
    ∃ z ∈ D - E,
      ((z +ᵥ E) ∩ D).Nonempty ∧
      lower ≤ weightedAbsMoment (μ_[Real] (z +ᵥ E) ○ᵈ μ D) f p := by
  let w : G → Real := μ_[Real] D ○ᵈ μ E
  let F : G → Real := fun z ↦
    weightedAbsMoment (fun x ↦ (μ_[Real] E ○ᵈ μ D) (x - z)) f p
  have hDE : (D - E).Nonempty := by
    obtain ⟨d, hd⟩ := hD
    obtain ⟨e, he⟩ := hE
    refine ⟨d - e, ?_⟩
    exact Finset.mem_sub.mpr ⟨d, hd, e, he, rfl⟩
  have hw : ∀ z, 0 ≤ w z := by
    intro z
    exact dddconv_apply_nonneg mu_nonneg mu_nonneg z
  have hwsupport : ∀ z, z ∉ D - E → w z = 0 := by
    intro z hz
    rw [← not_ne_iff]
    intro hwz
    apply hz
    have hzsupport : z ∈ Function.support w := hwz
    simpa only [w, support_dddconv mu_nonneg mu_nonneg,
      support_mu, ← coe_sub, mem_coe] using hzsupport
  have hwsum : ∑ z : G, w z = 1 := by
    dsimp only [w]
    rw [sum_dddconv]
    simp only [starRingEnd_apply, star_trivial]
    rw [sum_mu _ hD, sum_mu _ hE, one_mul]
  have haverage : lower ≤ ∑ z : G, w z * F z := by
    rw [← smoothingWeight_absMoment_eq_crossAverage]
    exact hlower
  obtain ⟨z, hz, hzlarge⟩ :=
    exists_value_ge_probability_average_on hDE hw hwsupport hwsum haverage
  obtain ⟨d, hd, e, he, hde⟩ := Finset.mem_sub.mp hz
  refine ⟨z, hz, ?_, ?_⟩
  · refine ⟨d, Finset.mem_inter.mpr ⟨?_, hd⟩⟩
    rw [Finset.mem_vadd_finset]
    refine ⟨e, he, ?_⟩
    rw [← hde]
    simp only [vadd_eq_add, neg_smul, one_smul]
    exact sub_add_cancel d e
  · dsimp only [F] at hzlarge
    have hweight :
        (fun x ↦ (μ_[Real] E ○ᵈ μ D) (x - z)) =
          μ_[Real] (z +ᵥ E) ○ᵈ μ D := by
      rw [← translate_mu, translate_dddconv]
      rfl
    rw [hweight] at hzlarge
    exact hzlarge

/-- Norm-form translate selection used directly before sifting. -/
theorem exists_translated_difference_lpNorm_ge
    {D E A : Finset G} (hD : D.Nonempty) (hE : E.Nonempty)
    (hA : A.Nonempty) {p : Nat} (hp : 0 < p) {lower : Real}
    (hlowerNonneg : 0 ≤ lower)
    (hlower : lower ≤
      BalancedRestriction.weightedLpNorm
        ((↑) ∘ LocalizedUnbalancing.smoothingWeight D E)
        (μ_[Real] A ○ᵈ μ A) p) :
    ∃ z ∈ D - E,
      ((z +ᵥ E) ∩ D).Nonempty ∧
      lower ≤ ‖μ_[Real] A ○ᵈ μ A‖_[p, μ (z +ᵥ E) ○ᵈ μ D] := by
  let nu := LocalizedUnbalancing.smoothingWeight D E
  have hnu : BalancedRestriction.ProbabilityWeight
      ((↑) ∘ nu : G → Real) := by
    refine ⟨?_, ?_⟩
    · intro x
      exact_mod_cast (LocalizedUnbalancing.smoothingWeight_nonneg D E x)
    · simpa using congrArg (fun r : NNReal ↦ (r : Real))
        (LocalizedUnbalancing.smoothingWeight_sum hD hE)
  have hmoment : lower ^ p ≤
      weightedAbsMoment ((↑) ∘ nu : G → Real)
        (μ_[Real] A ○ᵈ μ A) p := by
    calc
      lower ^ p ≤
          BalancedRestriction.weightedLpNorm
              ((↑) ∘ nu : G → Real) (μ_[Real] A ○ᵈ μ A) p ^ p :=
        pow_le_pow_left₀ hlowerNonneg hlower p
      _ = weightedAbsMoment ((↑) ∘ nu : G → Real)
          (μ_[Real] A ○ᵈ μ A) p :=
        BalancedRestriction.weightedLpNorm_pow hnu hp
  obtain ⟨z, hz, hinter, hselected⟩ :=
    exists_translated_difference_moment_ge hD hE
      (μ_[Real] A ○ᵈ μ A) p (by simpa [nu] using hmoment)
  let wsel : G → NNReal := μ_[NNReal] (z +ᵥ E) ○ᵈ μ D
  have hB₁ : (z +ᵥ E).Nonempty := by
    obtain ⟨e, he⟩ := hE
    refine ⟨z + e, ?_⟩
    rw [Finset.mem_vadd_finset]
    exact ⟨e, he, rfl⟩
  have hwsel : BalancedRestriction.ProbabilityWeight
      ((↑) ∘ wsel : G → Real) := by
    refine ⟨?_, ?_⟩
    · intro x
      exact_mod_cast (dddconv_apply_nonneg mu_nonneg mu_nonneg x : 0 ≤ wsel x)
    · dsimp only [wsel]
      simp only [NNReal.coe_comp_dddconv, NNReal.coe_comp_mu]
      rw [sum_dddconv]
      simp only [starRingEnd_apply, star_trivial]
      rw [sum_mu _ hB₁, sum_mu _ hD, one_mul]
  have hselected' : lower ^ p ≤
      weightedAbsMoment ((↑) ∘ wsel : G → Real)
        (μ_[Real] A ○ᵈ μ A) p := by
    simpa only [wsel, NNReal.coe_comp_dddconv, NNReal.coe_comp_mu] using hselected
  have hlocalPow : lower ^ p ≤
      BalancedRestriction.weightedLpNorm
          ((↑) ∘ wsel : G → Real) (μ_[Real] A ○ᵈ μ A) p ^ p := by
    rw [BalancedRestriction.weightedLpNorm_pow hwsel hp]
    exact hselected'
  have hlocalNonneg : 0 ≤
      BalancedRestriction.weightedLpNorm
        ((↑) ∘ wsel : G → Real) (μ_[Real] A ○ᵈ μ A) p :=
    BalancedRestriction.weightedLpNorm_nonneg hwsel _ _
  have hlocal : lower ≤
      BalancedRestriction.weightedLpNorm
        ((↑) ∘ wsel : G → Real) (μ_[Real] A ○ᵈ μ A) p := by
    by_contra hnot
    have hlt := lt_of_not_ge hnot
    have hpwlt := pow_lt_pow_left₀ hlt hlocalNonneg hp.ne'
    exact (not_lt_of_ge hlocalPow) hpwlt
  refine ⟨z, hz, hinter, ?_⟩
  rw [LocalizedUnbalancing.weightedLpNorm_eq_wLpNorm wsel
    (μ_[Real] A ○ᵈ μ A) hp] at hlocal
  exact hlocal

/-- The APAP probability convolution is the local translate density divided
by `|A|`.  This is the final normalization conversion before
`narrowLocated`. -/
theorem card_mul_mu_ddconv_eq_localDensity
    {A D : Finset G} (hA : A.Nonempty) (x : G) :
    (A.card : Real) * (μ_[Real] D ∗ᵈ μ A) x = localDensity A D x := by
  classical
  rw [ddconv_eq_sum_sub', localDensity, normalizedConvolution, Finset.mul_sum]
  let e : G ≃ G := Equiv.subLeft x
  rw [Fintype.sum_equiv e
    (fun z : G ↦ (A.card : Real) * (μ_[Real] D z * μ A (x - z)))
    (fun y : G ↦ (A.card : Real) * (μ_[Real] D (x - y) * μ A y))]
  · apply Finset.sum_congr rfl
    intro y _
    simp only [mu_apply, finsetIndicator, normalizedIndicator]
    have hAcard : (A.card : Real) ≠ 0 := by exact_mod_cast hA.card_ne_zero
    by_cases hyA : y ∈ A
    · by_cases hxyD : x - y ∈ D
      · simp only [if_pos hyA, if_pos hxyD, mul_one]
        calc
          (A.card : Real) * ((D.card : Real)⁻¹ * (A.card : Real)⁻¹) =
              (D.card : Real)⁻¹ * ((A.card : Real) * (A.card : Real)⁻¹) := by ring
          _ = (D.card : Real)⁻¹ := by rw [mul_inv_cancel₀ hAcard, mul_one]
          _ = 1 * (D.card : Real)⁻¹ := by rw [one_mul]
      · simp [hyA, hxyD]
    · simp [hyA]
  · intro y
    simp [e]

/-- The exact adjoint identity at the heart of the localized density step.
It moves the smoothed difference convolution from the popular-difference
side onto the original set, leaving a nonnegative probability weight. -/
theorem smoothed_correlation_adjoint
    (d a₁ a₂ a : G → Real) :
    ⟪d ∗ᵈ (a₁ ○ᵈ a₂), a ○ᵈ a⟫_[Real] =
      ⟪d ∗ᵈ a, (a₂ ○ᵈ a₁) ∗ᵈ a⟫_[Real] := by
  rw [ddconv_wInner_one, ddconv_wInner_one]
  congr 1
  change (a ○ᵈ a) ○ᵈ (a₁ ○ᵈ a₂) = ((a₂ ○ᵈ a₁) ∗ᵈ a) ○ᵈ a
  simp_rw [← ddconv_conjneg, conjneg_ddconv, conjneg_conjneg]
  calc
    (a ∗ᵈ conjneg a) ∗ᵈ (conjneg a₁ ∗ᵈ a₂) =
        (a ∗ᵈ conjneg a₁) ∗ᵈ (conjneg a ∗ᵈ a₂) :=
      ddconv_ddconv_ddconv_comm _ _ _ _
    _ = (conjneg a₁ ∗ᵈ a) ∗ᵈ (a₂ ∗ᵈ conjneg a) := by
      rw [ddconv_comm a, ddconv_comm (conjneg a) a₂]
    _ = (conjneg a₁ ∗ᵈ a₂) ∗ᵈ (a ∗ᵈ conjneg a) :=
      ddconv_ddconv_ddconv_comm _ _ _ _
    _ = ((a₂ ∗ᵈ conjneg a₁) ∗ᵈ a) ∗ᵈ conjneg a := by
      rw [ddconv_comm (conjneg a₁) a₂]
      exact (ddconv_assoc _ _ _).symm

/-- After the adjoint identity, the remaining factor is a probability
weight.  Consequently the smoothed correlation is bounded by the genuine
pointwise supremum of the child average of the original set. -/
theorem smoothed_correlation_le_linfty
    {D A₁ A₂ A : Finset G}
    (hD : D.Nonempty) (hA₁ : A₁.Nonempty)
    (hA₂ : A₂.Nonempty) (hA : A.Nonempty) :
    ∑ x : G, (μ_[Real] D ∗ᵈ (μ A₁ ○ᵈ μ A₂)) x * (μ A ○ᵈ μ A) x ≤
      ‖μ_[Real] D ∗ᵈ μ A‖_[∞] := by
  have hadjoint := smoothed_correlation_adjoint
    (μ_[Real] D) (μ A₁) (μ A₂) (μ A)
  rw [RCLike.wInner_one_eq_sum, RCLike.wInner_one_eq_sum] at hadjoint
  simp only [RCLike.inner_apply', RCLike.conj_to_real] at hadjoint
  rw [hadjoint]
  let f : G → Real := μ_[Real] D ∗ᵈ μ A
  let w : G → Real := (μ_[Real] A₂ ○ᵈ μ A₁) ∗ᵈ μ A
  have hw : ∀ x, 0 ≤ w x := by
    intro x
    exact ddconv_apply_nonneg
      (fun y ↦ dddconv_apply_nonneg mu_nonneg mu_nonneg y) mu_nonneg x
  calc
    ∑ x : G, f x * w x ≤ ∑ x : G, ‖f‖_[∞] * w x := by
      apply Finset.sum_le_sum
      intro x _
      apply mul_le_mul_of_nonneg_right _ (hw x)
      exact (le_abs_self (f x)).trans (norm_le_dLinftyNorm (f := f))
    _ = ‖f‖_[∞] * ∑ x : G, w x := by rw [Finset.mul_sum]
    _ = ‖f‖_[∞] := by
      dsimp only [w]
      rw [sum_ddconv, sum_dddconv]
      simp only [starRingEnd_apply, star_trivial]
      rw [sum_mu _ hA₂, sum_mu _ hA₁, one_mul,
        sum_mu _ hA, mul_one, mul_one]
    _ = ‖μ_[Real] D ∗ᵈ μ A‖_[∞] := rfl

/-- The complete adjoint-selection step.  A smoothed popular-difference
mass supplies a genuine translate on which the original set has the
corresponding local density.  The conclusion is about an actual group
element and an actual finite carrier, not an `L∞` surrogate. -/
theorem exists_localDensity_ge_of_smoothed_superlevel
    {D A₁ A₂ A S : Finset G}
    (hD : D.Nonempty) (hA₁ : A₁.Nonempty)
    (hA₂ : A₂.Nonempty) (hA : A.Nonempty)
    {threshold mass lower : Real} (hthreshold : 0 ≤ threshold)
    (hcorr : ∀ x, 0 ≤ (μ_[Real] A ○ᵈ μ A) x)
    (hpopular : ∀ x ∈ S, threshold ≤ (μ_[Real] A ○ᵈ μ A) x)
    (hmass : mass ≤
      LocalizedAlmostPeriodicity.countingInner
        (LocalizedAlmostPeriodicity.sumConvolution
          (LocalizedAlmostPeriodicity.probabilityIndicator D)
          (LocalizedAlmostPeriodicity.differenceConvolution
            (LocalizedAlmostPeriodicity.probabilityIndicator A₁)
            (LocalizedAlmostPeriodicity.probabilityIndicator A₂)))
        (LocalizedAlmostPeriodicity.setIndicator S))
    (hlower : lower ≤ threshold * mass) :
    ∃ x : G, (A.card : Real) * lower ≤ localDensity A D x := by
  have hsmoothed := smoothed_superlevel_inner_lower_bound hthreshold hcorr
    hpopular hmass
  have hadjoint := smoothed_correlation_adjoint
    (μ_[Real] D) (μ A₁) (μ A₂) (μ A)
  rw [RCLike.wInner_one_eq_sum, RCLike.wInner_one_eq_sum] at hadjoint
  simp only [RCLike.inner_apply', RCLike.conj_to_real] at hadjoint
  let w : G → Real := (μ_[Real] A₂ ○ᵈ μ A₁) ∗ᵈ μ A
  let f : G → Real := μ_[Real] D ∗ᵈ μ A
  have hw : ∀ x, 0 ≤ w x := by
    intro x
    exact ddconv_apply_nonneg
      (fun y ↦ dddconv_apply_nonneg mu_nonneg mu_nonneg y) mu_nonneg x
  have hwsum : ∑ x : G, w x = 1 := by
    dsimp only [w]
    rw [sum_ddconv, sum_dddconv]
    simp only [starRingEnd_apply, star_trivial]
    rw [sum_mu _ hA₂, sum_mu _ hA₁, one_mul,
      sum_mu _ hA, mul_one]
  have havg : lower ≤ ∑ x : G, w x * f x := by
    calc
      lower ≤ threshold * mass := hlower
      _ ≤ ∑ x : G,
          (μ_[Real] D ∗ᵈ (μ A₁ ○ᵈ μ A₂)) x * (μ A ○ᵈ μ A) x :=
        hsmoothed
      _ = ∑ x : G, w x * f x := by
        rw [hadjoint]
        apply Finset.sum_congr rfl
        intro x _
        rw [mul_comm]
  obtain ⟨x, hx⟩ := exists_value_ge_probability_average hw hwsum havg
  refine ⟨x, ?_⟩
  rw [← card_mul_mu_ddconv_eq_localDensity hA]
  exact mul_le_mul_of_nonneg_left hx (Nat.cast_nonneg _)

end SiftingOutput

theorem narrowingSet_nonempty_of_localDensity_pos
    {A C : Finset G} (hC : C.Nonempty) {x : G}
    (hx : 0 < localDensity A C x) :
    (narrowingSet A C x).Nonempty := by
  by_contra h
  have hcardNot : ¬ 0 < (narrowingSet A C x).card := by
    intro hcard
    exact h (Finset.card_pos.mp hcard)
  have hcard : (narrowingSet A C x).card = 0 := Nat.eq_zero_of_not_pos hcardNot
  rw [localDensity_eq_card_narrowingSet_div hC, hcard] at hx
  norm_num at hx

/-! ## Making a genuine next restriction -/

/-- A regular child shell which can be used as the next ambient carrier. -/
structure RegularChild where
  bohr : BohrData G
  outer : NNReal
  inner : NNReal
  regular : 0 < inner ∧ inner ≤ outer ∧
    (bohr.dilate (outer + inner)).carrier.card ≤
      2 * (bohr.dilate (outer - inner)).carrier.card

namespace RegularChild

def carrier (c : RegularChild (G := G)) : Finset G :=
  (c.bohr.dilate c.outer).carrier

lemma carrier_nonempty (c : RegularChild (G := G)) : c.carrier.Nonempty :=
  (c.bohr.dilate c.outer).carrier_nonempty

def asRestriction (c : RegularChild (G := G))
    (A : Finset G) (hA : A.Nonempty) (hAcarrier : A ⊆ c.carrier) :
    RegularRestriction G where
  bohr := c.bohr
  outer := c.outer
  inner := c.inner
  regular := c.regular
  set := A
  nonempty := hA
  subset_carrier := hAcarrier

/-- Every finite Bohr datum has a genuine coarsely regular child at a scale
between one half and one.  Its carrier still contains the half-dilate, so the
regularization loses at most the rank-only factor from Bourgain's volume
bound. -/
theorem exists_of_bohr (B : BohrData G) :
    ∃ c : RegularChild (G := G),
      c.bohr = B ∧
      (1 / 2 : NNReal) ≤ c.outer ∧ c.outer ≤ 1 ∧
      (B.dilate (1 / 2)).carrier.card ≤ c.carrier.card := by
  let n : Nat := 2 * B.rank + 1
  have hn : 0 < n := by simp [n]
  have hvolume := BohrData.card_unit_le_four_pow_rank_mul_card_half B
  have hpow : 4 ^ B.rank = 2 ^ (2 * B.rank) := by
    calc
      4 ^ B.rank = (2 ^ 2) ^ B.rank := by norm_num
      _ = 2 ^ (2 * B.rank) := by rw [pow_mul]
  have hhalfPos : 0 < (B.dilate (1 / 2)).carrier.card :=
    (B.dilate (1 / 2)).carrier_nonempty.card_pos
  have hstrict :
      (B.dilate 1).carrier.card <
        2 ^ n * (B.dilate (1 / 2)).carrier.card := by
    calc
      (B.dilate 1).carrier.card ≤
          4 ^ B.rank * (B.dilate (1 / 2)).carrier.card := hvolume
      _ = 2 ^ (2 * B.rank) * (B.dilate (1 / 2)).carrier.card := by rw [hpow]
      _ < 2 ^ n * (B.dilate (1 / 2)).carrier.card := by
        dsimp [n]
        rw [pow_succ]
        have hp : 0 < 2 ^ (2 * B.rank) := pow_pos (by omega) _
        nlinarith
  obtain ⟨rho, eta, hrhoLower, hrhoUpper, _heta, hregular⟩ :=
    B.exists_coarselyRegularAt_of_card_growth n hn hstrict
  let c : RegularChild (G := G) :=
    { bohr := B
      outer := rho
      inner := eta
      regular := hregular }
  refine ⟨c, rfl, hrhoLower, hrhoUpper, ?_⟩
  exact Finset.card_le_card (BohrData.carrier_dilate_mono hrhoLower)

/-- A rank-regular datum is already a valid regular child at its unit
carrier.  The explicit `1/(400 max(rank,1))` inner width turns the two
rank-regular cardinality estimates into the required factor-two shell
bound. -/
theorem exists_of_rankRegular (B : BohrData G) (hreg : B.IsRankRegular) :
    ∃ c : RegularChild (G := G),
      c.bohr = B ∧ c.outer = 1 ∧ c.carrier = B.carrier := by
  let d : Nat := max B.rank 1
  let kappa : NNReal := 1 / (400 * (d : NNReal))
  have hd : 0 < d := by simp [d]
  have hkappaPos : 0 < kappa := by
    dsimp [kappa]
    positivity
  have hkappaReg : kappa ≤ 1 / (100 * (d : NNReal)) := by
    dsimp [kappa]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact mul_le_mul_of_nonneg_right (by norm_num : (100 : NNReal) ≤ 400)
      (by positivity)
  have hkappaOne : kappa ≤ 1 := by
    apply hkappaReg.trans
    rw [div_le_one]
    · exact_mod_cast (show 1 ≤ 100 * d by omega)
    · positivity
  have hcards := hreg kappa (by simpa [d] using hkappaReg)
  have hquarter : (100 : Real) * d * (kappa : Real) ≤ 1 / 4 := by
    have hkappaReal : (kappa : Real) ≤ 1 / (400 * (d : Real)) := by
      exact_mod_cast (show kappa ≤ 1 / (400 * (d : NNReal)) by rfl)
    have hdReal : (0 : Real) < d := by exact_mod_cast hd
    calc
      (100 : Real) * d * (kappa : Real) ≤
          100 * d * (1 / (400 * (d : Real))) := by gcongr
      _ = 1 / 4 := by field_simp; ring
  have hcardReal :
      ((B.dilate (1 + kappa)).carrier.card : Real) ≤
        2 * ((B.dilate (1 - kappa)).carrier.card : Real) := by
    nlinarith [hcards.1, hcards.2, hquarter,
      show (0 : Real) < B.carrier.card by
        exact_mod_cast B.carrier_nonempty.card_pos]
  have hcard :
      (B.dilate (1 + kappa)).carrier.card ≤
        2 * (B.dilate (1 - kappa)).carrier.card := by
    exact_mod_cast hcardReal
  let c : RegularChild (G := G) :=
    { bohr := B
      outer := 1
      inner := kappa
      regular := ⟨hkappaPos, hkappaOne, hcard⟩ }
  refine ⟨c, rfl, rfl, ?_⟩
  simp only [carrier, c, BohrData.dilate_one]

end RegularChild

/-- Recenter a dense translate on a regular child carrier, preserving its
exact translation back into the original set. -/
def narrowLocated {original : Finset G} (s : LocatedRestriction original)
    (child : RegularChild (G := G)) (x : G)
    (hpos : 0 < localDensity s.restriction.set child.carrier x) :
    LocatedRestriction original where
  restriction := child.asRestriction
    (narrowingSet s.restriction.set child.carrier x)
    (narrowingSet_nonempty_of_localDensity_pos child.carrier_nonempty hpos)
    (narrowingSet_subset_carrier (B := child.bohr) (rho := child.outer)
      (A := s.restriction.set) (C := child.carrier) (x := x) fun _ h => h)
  shift := s.shift - x
  subset_original := by
    intro z hz
    have hzA := (mem_narrowingSet.mp hz).2
    have hsource := s.subset_original (x + z) hzA
    have heq : z - (s.shift - x) = (x + z) - s.shift := by abel
    rwa [heq]

@[simp] theorem density_narrowLocated {original : Finset G}
    (s : LocatedRestriction original) (child : RegularChild (G := G)) (x : G)
    (hpos : 0 < localDensity s.restriction.set child.carrier x) :
    (narrowLocated s child x hpos).density =
      localDensity s.restriction.set child.carrier x := by
  change ((narrowingSet s.restriction.set child.carrier x).card : Real) /
      child.carrier.card = localDensity s.restriction.set child.carrier x
  exact (localDensity_eq_card_narrowingSet_div child.carrier_nonempty x).symm

theorem narrowLocated_isControlledIncrement
    {original : Finset G} (s : LocatedRestriction original)
    (child : RegularChild (G := G)) (x : G)
    {q sizeCost : Real} {rankCost : Nat}
    (hpos : 0 < localDensity s.restriction.set child.carrier x)
    (hdensity : q * s.density ≤
      localDensity s.restriction.set child.carrier x)
    (hrank : child.bohr.rank ≤ s.rank + rankCost)
    (hcard : Real.exp (-sizeCost) * (s.card : Real) ≤ child.carrier.card) :
    IsControlledIncrement q rankCost sizeCost s.restriction
      (narrowLocated s child x hpos).restriction := by
  refine ⟨?_, hrank, ?_⟩
  · change q * s.density ≤
      ((narrowingSet s.restriction.set child.carrier x).card : Real) /
        child.carrier.card
    rw [← localDensity_eq_card_narrowingSet_div child.carrier_nonempty]
    exact hdensity
  · change Real.exp (-sizeCost) * (s.restriction.card : Real) ≤
      child.carrier.card
    exact hcard

/-- Convert a local-density witness on a rank-regular Bohr datum into the
actual provenance-preserving next state used by the located stopping chain.
The child carrier is exactly `D.carrier`; no second regularization or hidden
cardinality loss is introduced. -/
theorem controlledIncrement_of_rankRegular_localDensity
    {original : Finset G} (s : LocatedRestriction original)
    (D : BohrData G) (hDreg : D.IsRankRegular)
    {q sizeCost : Real} {rankCost : Nat} (hq : 0 < q)
    (hrank : D.rank ≤ s.rank + rankCost)
    (hcard : Real.exp (-sizeCost) * (s.card : Real) ≤ D.carrier.card)
    (hdense : ∃ x : G, q * s.density ≤
      localDensity s.restriction.set D.carrier x) :
    ∃ t : LocatedRestriction original,
      IsControlledIncrement q rankCost sizeCost
        s.restriction t.restriction := by
  obtain ⟨child, hchildBohr, hchildOuter, hchildCarrier⟩ :=
    RegularChild.exists_of_rankRegular D hDreg
  obtain ⟨x, hx⟩ := hdense
  have hx' : q * s.density ≤
      localDensity s.restriction.set child.carrier x := by
    rwa [hchildCarrier]
  have hpos : 0 < localDensity s.restriction.set child.carrier x :=
    (mul_pos hq s.density_pos).trans_le hx'
  let t := narrowLocated s child x hpos
  refine ⟨t, narrowLocated_isControlledIncrement s child x hpos hx' ?_ ?_⟩
  · simpa [hchildBohr] using hrank
  · simpa [hchildCarrier] using hcard

section AnalyticLocatedIncrement

variable [MeasurableSpace G] [DiscreteMeasurableSpace G]

/-- Stable assembly point for the analytic density step.  Localized
almost-periodicity supplies the smoothed-mass premise on an actual
rank-regular datum `D`; the adjoint identity selects a translate; and the
result is immediately narrowed to an actual located restriction.

Every quantitative conclusion is proved here from the displayed rank,
cardinality, popularity, and smoothing estimates. -/
theorem locatedIncrement_of_smoothed_superlevel
    {original : Finset G} (s : LocatedRestriction original)
    (D : BohrData G) (hDreg : D.IsRankRegular)
    {A₁ A₂ S : Finset G} (hA₁ : A₁.Nonempty) (hA₂ : A₂.Nonempty)
    {threshold mass lower q sizeCost : Real} {rankCost : Nat}
    (hthreshold : 0 ≤ threshold)
    (hpopular : ∀ x ∈ S, threshold ≤
      (μ_[Real] s.restriction.set ○ᵈ μ s.restriction.set) x)
    (hmass : mass ≤
      LocalizedAlmostPeriodicity.countingInner
        (LocalizedAlmostPeriodicity.sumConvolution
          (LocalizedAlmostPeriodicity.probabilityIndicator D.carrier)
          (LocalizedAlmostPeriodicity.differenceConvolution
            (LocalizedAlmostPeriodicity.probabilityIndicator A₁)
            (LocalizedAlmostPeriodicity.probabilityIndicator A₂)))
        (LocalizedAlmostPeriodicity.setIndicator S))
    (hlower : lower ≤ threshold * mass)
    (hq : 0 < q)
    (hgain : q * s.density ≤ (s.restriction.set.card : Real) * lower)
    (hrank : D.rank ≤ s.rank + rankCost)
    (hcard : Real.exp (-sizeCost) * (s.card : Real) ≤ D.carrier.card) :
    ∃ t : LocatedRestriction original,
      IsControlledIncrement q rankCost sizeCost
        s.restriction t.restriction := by
  have hcorr : ∀ x, 0 ≤
      (μ_[Real] s.restriction.set ○ᵈ μ s.restriction.set) x := by
    intro x
    exact dddconv_apply_nonneg mu_nonneg mu_nonneg x
  obtain ⟨x, hx⟩ := exists_localDensity_ge_of_smoothed_superlevel
    D.carrier_nonempty hA₁ hA₂ s.restriction.nonempty hthreshold
      hcorr hpopular hmass hlower
  apply controlledIncrement_of_rankRegular_localDensity s D hDreg hq
    hrank hcard
  exact ⟨x, hgain.trans hx⟩

/-- **High smoothing norm gives a genuine located increment.**

This is the stable seam used by the balanced-restriction assembly.  Starting
from a large weighted autocorrelation norm, it first selects an actual
translated pair, invokes the unconditional (two-branch) sifting theorem on
that pair, and then consumes the localized almost-periodicity package
attached to the sifted output.  The latter package is exactly what
LocalizedAlmostPeriodicity.exists_unconditional_localized_linfty_almostPeriods
constructs after the quantitative rank and cardinality losses have been
budgeted by the caller.

The gain is deliberately the honest 1 + epsilon / 32: the factors
1 - sigma from popularity and 1 - delta - approximationError from
smoothing are still present in hgain, so no loss is silently discarded. -/
theorem highSmoothingNorm_locatedIncrement
    {original : Finset G} (s : LocatedRestriction original)
    {D E : Finset G}
    (hD : D.Nonempty) (hE : E.Nonempty)
    {epsilon sigma delta approximationError lowerNorm sizeCost : Real}
    {rankCost r : Nat}
    (hepsilon : 0 < epsilon)
    (hsigma : 0 < sigma) (hsigmaOne : sigma ≤ 1)
    (hdelta : 0 < delta) (hdeltaOne : delta < 1)
    (hr : 0 < r) (hrEven : Even r) (hrTwo : 2 ≤ r)
    (hrTail : sigma⁻¹ * Real.log (2 / delta) ≤ r)
    (hlowerNorm : 0 ≤ lowerNorm)
    (hhigh : lowerNorm ≤
      BalancedRestriction.weightedLpNorm
        ((↑) ∘ LocalizedUnbalancing.smoothingWeight D E)
        (μ_[Real] s.restriction.set ○ᵈ μ s.restriction.set) r)
    (hgain :
      (1 + epsilon / 32) * s.density ≤
        (s.restriction.set.card : Real) *
          (((1 - sigma) * lowerNorm) *
            (1 - delta - approximationError)))
    (hlocalized :
      ∀ (z : G), z ∈ D - E → ((z +ᵥ E) ∩ D).Nonempty →
        ∀ data : SiftedPopularData s.restriction.set (z +ᵥ E) D
            r sigma delta,
          ∃ (parent : BohrData G) (parentWidth : NNReal)
            (source : Finset G) (cardMultiplier : Nat),
            ∃ P : LocalizedSiftingPackage data parent parentWidth source
              rankCost cardMultiplier approximationError,
              P.child.rank ≤ s.rank + rankCost ∧
              Real.exp (-sizeCost) * (s.card : Real) ≤ P.child.carrier.card) :
    ∃ t : LocatedRestriction original,
      IsControlledIncrement (1 + epsilon / 32) rankCost sizeCost
        s.restriction t.restriction := by
  obtain ⟨z, hz, hinter, hlocalNorm⟩ :=
    exists_translated_difference_lpNorm_ge hD hE s.restriction.nonempty
      hr hlowerNorm hhigh
  let B₁ : Finset G := z +ᵥ E
  let B₂ : Finset G := D
  have hB : (B₁ ∩ B₂).Nonempty := by simpa [B₁, B₂] using hinter
  obtain ⟨data⟩ :=
    exists_sifted_popular_data_unconditional
      (A := s.restriction.set) (p := r) (epsilon := sigma) (delta := delta)
      B₁ B₂ hsigma hsigmaOne hdelta hrEven hrTwo hrTail hB
      s.restriction.nonempty
  obtain ⟨parent, parentWidth, source, cardMultiplier, P, hPrank, hPcard⟩ :=
    hlocalized z hz (by simpa [B₁, B₂] using hinter) (by simpa [B₁, B₂] using data)
  have houtputs := data.output_nonempty hdeltaOne
  have hmass :
      1 - delta - approximationError ≤
        LocalizedAlmostPeriodicity.countingInner
          (LocalizedAlmostPeriodicity.sumConvolution
            (LocalizedAlmostPeriodicity.probabilityIndicator P.child.carrier)
            (LocalizedAlmostPeriodicity.differenceConvolution
              (LocalizedAlmostPeriodicity.probabilityIndicator data.A₁)
              (LocalizedAlmostPeriodicity.probabilityIndicator data.A₂)))
          (LocalizedAlmostPeriodicity.setIndicator
            (_root_.s r sigma B₁ B₂ s.restriction.set)) := by
    exact smoothed_popular_mass_lower_bound houtputs.1 houtputs.2
      (by
        simpa only [countingInner_difference_setIndicator_eq_sum] using
          data.popular_mass)
      P.triple_error
  have hthreshold : 0 ≤ (1 - sigma) * lowerNorm :=
    mul_nonneg (sub_nonneg.mpr hsigmaOne) hlowerNorm
  have hpopular : ∀ x ∈ _root_.s r sigma B₁ B₂ s.restriction.set,
      (1 - sigma) * lowerNorm ≤
        (μ_[Real] s.restriction.set ○ᵈ μ s.restriction.set) x := by
    intro x hx
    have hxPopular :
        (1 - sigma) *
            ‖μ_[Real] s.restriction.set ○ᵈ μ s.restriction.set‖_[
              r, μ B₁ ○ᵈ μ B₂] <
          (μ_[Real] s.restriction.set ○ᵈ μ s.restriction.set) x :=
      (mem_s'.mp hx)
    exact (mul_le_mul_of_nonneg_left hlocalNorm
      (sub_nonneg.mpr hsigmaOne)).trans hxPopular.le
  apply locatedIncrement_of_smoothed_superlevel s P.child P.child_regular
    houtputs.1 houtputs.2 hthreshold hpopular hmass
      (show ((1 - sigma) * lowerNorm) * (1 - delta - approximationError) ≤
          ((1 - sigma) * lowerNorm) * (1 - delta - approximationError) from le_rfl)
      (by nlinarith [hepsilon]) hgain hPrank hPcard

/-- Support-restricted high-norm bridge.  It is identical to the global
bridge except that the localized AP package is built on the popular set
intersected with B₁-B₂; the retained DRC mass is unchanged by the support
restriction. -/
theorem highSmoothingNorm_locatedIncrement_supported
    {original : Finset G} (s : LocatedRestriction original)
    {D E : Finset G}
    (hD : D.Nonempty) (hE : E.Nonempty)
    {epsilon sigma delta approximationError lowerNorm sizeCost : Real}
    {rankCost r : Nat}
    (hepsilon : 0 < epsilon)
    (hsigma : 0 < sigma) (hsigmaOne : sigma ≤ 1)
    (hdelta : 0 < delta) (hdeltaOne : delta < 1)
    (hr : 0 < r) (hrEven : Even r) (hrTwo : 2 ≤ r)
    (hrTail : sigma⁻¹ * Real.log (2 / delta) ≤ r)
    (hlowerNorm : 0 ≤ lowerNorm)
    (hhigh : lowerNorm ≤
      BalancedRestriction.weightedLpNorm
        ((↑) ∘ LocalizedUnbalancing.smoothingWeight D E)
        (μ_[Real] s.restriction.set ○ᵈ μ s.restriction.set) r)
    (hgain :
      (1 + epsilon / 32) * s.density ≤
        (s.restriction.set.card : Real) *
          (((1 - sigma) * lowerNorm) *
            (1 - delta - approximationError)))
    (hlocalized :
      ∀ (z : G), z ∈ D - E → ((z +ᵥ E) ∩ D).Nonempty →
        ∀ data : SiftedPopularData s.restriction.set (z +ᵥ E) D
            r sigma delta,
          ∃ (parent : BohrData G) (parentWidth : NNReal)
            (source : Finset G) (cardMultiplier : Nat),
            ∃ P : SupportedLocalizedSiftingPackage data parent parentWidth source
              rankCost cardMultiplier approximationError,
              P.child.rank ≤ s.rank + rankCost ∧
              Real.exp (-sizeCost) * (s.card : Real) ≤ P.child.carrier.card) :
    ∃ t : LocatedRestriction original,
      IsControlledIncrement (1 + epsilon / 32) rankCost sizeCost
        s.restriction t.restriction := by
  obtain ⟨z, hz, hinter, hlocalNorm⟩ :=
    exists_translated_difference_lpNorm_ge hD hE s.restriction.nonempty
      hr hlowerNorm hhigh
  let B₁ : Finset G := z +ᵥ E
  let B₂ : Finset G := D
  have hB : (B₁ ∩ B₂).Nonempty := by simpa [B₁, B₂] using hinter
  obtain ⟨data⟩ :=
    exists_sifted_popular_data_unconditional
      (A := s.restriction.set) (p := r) (epsilon := sigma) (delta := delta)
      B₁ B₂ hsigma hsigmaOne hdelta hrEven hrTwo hrTail hB
      s.restriction.nonempty
  obtain ⟨parent, parentWidth, source, cardMultiplier, P, hPrank, hPcard⟩ :=
    hlocalized z hz (by simpa [B₁, B₂] using hinter) (by simpa [B₁, B₂] using data)
  have houtputs := data.output_nonempty hdeltaOne
  let S : Finset G :=
    SiftedPopularData.supportedPopularSet s.restriction.set B₁ B₂ r sigma
  have hsupportMass : 1 - delta ≤
      ∑ x ∈ S, (μ_[Real] data.A₁ ○ᵈ μ data.A₂) x := by
    have h := data.supported_popular_mass
    rw [countingInner_difference_setIndicator_eq_sum] at h
    simpa only [S] using h
  have hmass :
      1 - delta - approximationError ≤
        LocalizedAlmostPeriodicity.countingInner
          (LocalizedAlmostPeriodicity.sumConvolution
            (LocalizedAlmostPeriodicity.probabilityIndicator P.child.carrier)
            (LocalizedAlmostPeriodicity.differenceConvolution
              (LocalizedAlmostPeriodicity.probabilityIndicator data.A₁)
              (LocalizedAlmostPeriodicity.probabilityIndicator data.A₂)))
          (LocalizedAlmostPeriodicity.setIndicator S) := by
    exact smoothed_popular_mass_lower_bound houtputs.1 houtputs.2
      hsupportMass
      (by simpa [S] using P.triple_error)
  have hthreshold : 0 ≤ (1 - sigma) * lowerNorm :=
    mul_nonneg (sub_nonneg.mpr hsigmaOne) hlowerNorm
  have hpopular : ∀ x ∈ S,
      (1 - sigma) * lowerNorm ≤
        (μ_[Real] s.restriction.set ○ᵈ μ s.restriction.set) x := by
    intro x hx
    have hxGlobal : x ∈ _root_.s r sigma B₁ B₂ s.restriction.set := by
      exact (Finset.mem_inter.mp (by
        simpa only [S, SiftedPopularData.supportedPopularSet] using hx)).1
    have hxPopular :
        (1 - sigma) *
            ‖μ_[Real] s.restriction.set ○ᵈ μ s.restriction.set‖_[
              r, μ B₁ ○ᵈ μ B₂] <
          (μ_[Real] s.restriction.set ○ᵈ μ s.restriction.set) x :=
      (mem_s'.mp hxGlobal)
    exact (mul_le_mul_of_nonneg_left hlocalNorm
      (sub_nonneg.mpr hsigmaOne)).trans hxPopular.le
  apply locatedIncrement_of_smoothed_superlevel s P.child P.child_regular
    houtputs.1 houtputs.2 hthreshold hpopular hmass
      (show ((1 - sigma) * lowerNorm) * (1 - delta - approximationError) ≤
          ((1 - sigma) * lowerNorm) * (1 - delta - approximationError) from le_rfl)
      (by nlinarith [hepsilon]) hgain hPrank hPcard

/-- Convert the complex unnormalized threefold almost-period estimate
returned by the final localized Croot--Sisask/Chang theorem into the real
triple-indicator estimate consumed by LocalizedSiftingPackage.  The
translation is evaluated at zero with -t; symmetry of a Bohr carrier is
the only sign input. -/
theorem triple_error_of_threefold_dLinfty
    {D : BohrData G} {A₁ A₂ S : Finset G} {error : Real}
    (hA₁ : A₁.Nonempty) (hA₂ : A₂.Nonempty)
    (hperiod : ∀ t ∈ D.carrier,
      ‖τ t ((μ_[Complex] (-A₁) ∗ᵈ (𝟭_[S] : G → Complex)) ∗ᵈ μ A₂) -
          ((μ_[Complex] (-A₁) ∗ᵈ (𝟭_[S] : G → Complex)) ∗ᵈ μ A₂)‖_[∞] ≤
        error) :
    ∀ t ∈ D.carrier,
      |LocalizedAlmostPeriodicity.tripleIndicatorSum A₁ A₂ S t -
          LocalizedAlmostPeriodicity.tripleIndicatorSum A₁ A₂ S 0| ≤
        error * (A₁.card : Real) * A₂.card := by
  classical
  let F : G → Complex :=
    (μ_[Complex] (-A₁) ∗ᵈ (𝟭_[S] : G → Complex)) ∗ᵈ μ A₂
  have hF (u : G) :
      F u = Complex.ofReal
        (LocalizedAlmostPeriodicity.tripleIndicatorSum A₁ A₂ S u /
          (A₁.card * A₂.card : Real)) := by
    dsimp only [F]
    rw [threefold_eq_ofReal_finiteInner]
    congr 1
    exact LocalizedAlmostPeriodicity.finiteInner_translate_differenceConvolution_eq
      hA₁ hA₂ S u
  intro t ht
  have hneg : -t ∈ D.carrier := BohrData.neg_mem_carrier.mpr ht
  have hpoint :
      ‖(τ (-t) F - F) 0‖ ≤ error := by
    calc
      ‖(τ (-t) F - F) 0‖ ≤ ‖τ (-t) F - F‖_[∞] :=
        norm_le_dLinftyNorm
      _ ≤ error := by simpa only [F] using hperiod (-t) hneg
  have hquot :
      |(LocalizedAlmostPeriodicity.tripleIndicatorSum A₁ A₂ S t -
          LocalizedAlmostPeriodicity.tripleIndicatorSum A₁ A₂ S 0) /
          (A₁.card * A₂.card : Real)| ≤ error := by
    rw [Pi.sub_apply, translate_apply, sub_neg_eq_add, zero_add,
      hF t, hF 0, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      ← sub_div] at hpoint
    exact hpoint
  have hcard : (0 : Real) < (A₁.card : Real) * A₂.card :=
    mul_pos (by exact_mod_cast hA₁.card_pos) (by exact_mod_cast hA₂.card_pos)
  rw [abs_div, abs_of_pos hcard] at hquot
  have hscaled := (div_le_iff₀ hcard).mp hquot
  nlinarith

/-- Reflection/symmetry identity for the TeX orientation of the threefold
convolution: swapping the first and middle normalized sets and negating the
popular set changes the triple-sum parameter from t to -t. -/
theorem tripleIndicatorSum_reflect_swap
    (A₁ A₂ S : Finset G) (t : G) :
    LocalizedAlmostPeriodicity.tripleIndicatorSum A₂ (-S) A₁ t =
      LocalizedAlmostPeriodicity.tripleIndicatorSum A₁ A₂ S (-t) := by
  classical
  unfold LocalizedAlmostPeriodicity.tripleIndicatorSum
  nth_rewrite 2 [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a₂ _
  refine Fintype.sum_equiv (Equiv.subLeft (t + a₂)) _ _ (fun s ↦ ?_)
  change LocalizedAlmostPeriodicity.setIndicator A₂ a₂ *
      LocalizedAlmostPeriodicity.setIndicator (-S) s *
      LocalizedAlmostPeriodicity.setIndicator A₁ (t + a₂ - s) =
    LocalizedAlmostPeriodicity.setIndicator A₁ (t + a₂ - s) *
      LocalizedAlmostPeriodicity.setIndicator A₂ a₂ *
      LocalizedAlmostPeriodicity.setIndicator S (-t + (t + a₂ - s) - a₂)
  have harg : -t + (t + a₂ - s) - a₂ = -s := by abel
  rw [harg]
  have hA₂ : LocalizedAlmostPeriodicity.setIndicator A₂ a₂ *
      LocalizedAlmostPeriodicity.setIndicator (-S) s *
      LocalizedAlmostPeriodicity.setIndicator A₁ (t + a₂ - s) =
    LocalizedAlmostPeriodicity.setIndicator A₁ (t + a₂ - s) *
      LocalizedAlmostPeriodicity.setIndicator A₂ a₂ *
      LocalizedAlmostPeriodicity.setIndicator S (-s) := by
    by_cases hs : s ∈ -S
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_neg.mp hs
      by_cases ha : t + a₂ - -u ∈ A₁ <;>
        by_cases ha₂ : a₂ ∈ A₂ <;>
          simp [LocalizedAlmostPeriodicity.setIndicator, hu, ha, ha₂]
    · have hs' : -s ∉ S := by
        intro h
        apply hs
        simpa using h
      by_cases ha : t + a₂ - s ∈ A₁ <;>
        by_cases ha₂ : a₂ ∈ A₂ <;>
          simp [LocalizedAlmostPeriodicity.setIndicator, hs, hs', ha, ha₂]
  exact hA₂

/-- Triple-error bridge for the TeX/Bloom--Sisask orientation with first
factor μ(-A₂), middle factor 1(A₁), and last factor μ(-S).  Its value at u
is the normalized triple sum at -u, so evaluating a period at zero produces
the desired parameter t without a further sign loss.  The displayed factor
converts the |A₂||S| normalization back to the |A₁||A₂| convention of the
sifting package. -/
theorem triple_error_of_reflected_threefold_dLinfty
    {D : BohrData G} {A₁ A₂ S : Finset G} {error : Real}
    (hA₁ : A₁.Nonempty) (hA₂ : A₂.Nonempty) (hS : S.Nonempty)
    (hperiod : ∀ t ∈ D.carrier,
      ‖τ t ((μ_[Complex] (-A₂) ∗ᵈ (𝟭_[A₁] : G → Complex)) ∗ᵈ μ (-S)) -
          ((μ_[Complex] (-A₂) ∗ᵈ (𝟭_[A₁] : G → Complex)) ∗ᵈ μ (-S))‖_[∞] ≤
        error) :
    ∀ t ∈ D.carrier,
      |LocalizedAlmostPeriodicity.tripleIndicatorSum A₁ A₂ S t -
          LocalizedAlmostPeriodicity.tripleIndicatorSum A₁ A₂ S 0| ≤
        (error * (S.card : Real) / A₁.card) *
          (A₁.card : Real) * A₂.card := by
  classical
  have hnegS : (-S).Nonempty := by
    obtain ⟨s, hs⟩ := hS
    exact ⟨-s, by simpa using hs⟩
  let F : G → Complex :=
    (μ_[Complex] (-A₂) ∗ᵈ (𝟭_[A₁] : G → Complex)) ∗ᵈ μ (-S)
  have hF (u : G) :
      F u = Complex.ofReal
        (LocalizedAlmostPeriodicity.tripleIndicatorSum A₁ A₂ S (-u) /
          (A₂.card * S.card : Real)) := by
    dsimp only [F]
    rw [threefold_eq_ofReal_finiteInner]
    congr 1
    rw [LocalizedAlmostPeriodicity.finiteInner_translate_differenceConvolution_eq
      hA₂ hnegS A₁ u]
    rw [tripleIndicatorSum_reflect_swap]
    simp
  intro t ht
  have hpoint :
      ‖(τ t F - F) 0‖ ≤ error := by
    calc
      ‖(τ t F - F) 0‖ ≤ ‖τ t F - F‖_[∞] :=
        norm_le_dLinftyNorm
      _ ≤ error := by simpa only [F] using hperiod t ht
  have hquot :
      |(LocalizedAlmostPeriodicity.tripleIndicatorSum A₁ A₂ S t -
          LocalizedAlmostPeriodicity.tripleIndicatorSum A₁ A₂ S 0) /
          (A₂.card * S.card : Real)| ≤ error := by
    rw [Pi.sub_apply, translate_apply, zero_sub, hF (-t), hF 0,
      neg_neg, neg_zero, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, ← sub_div] at hpoint
    exact hpoint
  have hcard : (0 : Real) < (A₂.card : Real) * S.card :=
    mul_pos (by exact_mod_cast hA₂.card_pos) (by exact_mod_cast hS.card_pos)
  rw [abs_div, abs_of_pos hcard] at hquot
  have hscaled := (div_le_iff₀ hcard).mp hquot
  have hA₁card : (A₁.card : Real) ≠ 0 := by
    exact_mod_cast hA₁.card_ne_zero
  calc
    |LocalizedAlmostPeriodicity.tripleIndicatorSum A₁ A₂ S t -
        LocalizedAlmostPeriodicity.tripleIndicatorSum A₁ A₂ S 0|
        ≤ error * ((A₂.card : Real) * S.card) := hscaled
    _ = (error * (S.card : Real) / A₁.card) *
        (A₁.card : Real) * A₂.card := by
      field_simp [hA₁card]

/-- Reflection identity for the normalization-compatible ordering: after
swapping the two normalized sets, the negated popular set stays in the last
slot and the shift parameter changes sign. -/
theorem tripleIndicatorSum_commuted_reflect
    (A₁ A₂ S : Finset G) (t : G) :
    LocalizedAlmostPeriodicity.tripleIndicatorSum A₂ A₁ (-S) t =
      LocalizedAlmostPeriodicity.tripleIndicatorSum A₁ A₂ S (-t) := by
  classical
  unfold LocalizedAlmostPeriodicity.tripleIndicatorSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a₁ _
  apply Finset.sum_congr rfl
  intro a₂ _
  have hind (u : G) :
      LocalizedAlmostPeriodicity.setIndicator (-S) u =
        LocalizedAlmostPeriodicity.setIndicator S (-u) := by
    by_cases hu : u ∈ -S
    · have hneg : -u ∈ S := by simpa using hu
      simp [LocalizedAlmostPeriodicity.setIndicator, hu, hneg]
    · have hneg : -u ∉ S := by
        intro h
        apply hu
        simpa using h
      simp [LocalizedAlmostPeriodicity.setIndicator, hu, hneg]
  rw [hind]
  have harg : -(t + a₂ - a₁) = -t + a₁ - a₂ := by abel
  rw [harg]
  ring

/-- Triple-error bridge for the normalization-compatible commuted
orientation: first factor μ(-A₂), middle factor 1(-S), and last factor
μ(A₁).  This is exactly the reflected triple sum with its original
|A₁||A₂| normalization, so no extra |S|/|A₁| factor is introduced. -/
theorem triple_error_of_commuted_reflected_threefold_dLinfty
    {D : BohrData G} {A₁ A₂ S : Finset G} {error : Real}
    (hA₁ : A₁.Nonempty) (hA₂ : A₂.Nonempty)
    (hperiod : ∀ t ∈ D.carrier,
      ‖τ t ((μ_[Complex] (-A₂) ∗ᵈ
              (𝟭_[(-S : Finset G)] : G → Complex)) ∗ᵈ μ A₁) -
          ((μ_[Complex] (-A₂) ∗ᵈ
              (𝟭_[(-S : Finset G)] : G → Complex)) ∗ᵈ μ A₁)‖_[∞] ≤
        error) :
    ∀ t ∈ D.carrier,
      |LocalizedAlmostPeriodicity.tripleIndicatorSum A₁ A₂ S t -
          LocalizedAlmostPeriodicity.tripleIndicatorSum A₁ A₂ S 0| ≤
        error * (A₁.card : Real) * A₂.card := by
  classical
  have hbase := triple_error_of_threefold_dLinfty
    (D := D) (A₁ := A₂) (A₂ := A₁) (S := -S) (error := error)
    hA₂ hA₁ hperiod
  intro t ht
  have hneg : -t ∈ D.carrier := BohrData.neg_mem_carrier.mpr ht
  have h := hbase (-t) hneg
  rw [tripleIndicatorSum_commuted_reflect A₁ A₂ S (-t),
    tripleIndicatorSum_commuted_reflect A₁ A₂ S 0] at h
  simpa [mul_comm, mul_left_comm, mul_assoc] using h

/-- Positive retained popular mass makes the popular-difference set itself
nonempty.  This is the small input needed to use it as the middle set in the
final localized almost-periodicity theorem. -/
theorem popularSet_nonempty_of_siftedPopularData
    {A B₁ B₂ : Finset G} {p : Nat} {sigma delta : Real}
    (data : SiftedPopularData A B₁ B₂ p sigma delta)
    (hdelta : delta < 1) :
    (_root_.s p sigma B₁ B₂ A).Nonempty := by
  by_contra hnone
  have hempty : _root_.s p sigma B₁ B₂ A = ∅ :=
    not_nonempty_iff_eq_empty.mp hnone
  have hmass := data.popular_mass
  rw [hempty] at hmass
  simp [LocalizedAlmostPeriodicity.countingInner,
    LocalizedAlmostPeriodicity.setIndicator] at hmass
  linarith

/-- Concrete construction of the localized sifting package from the final
unconditional localized almost-periodicity theorem.  The rank cost,
relative-cardinality multiplier, and error are left as existential witnesses
because they depend on the selected Croot--Sisask set and Chang family; the
caller can subsequently dominate them by its global budget. -/
theorem exists_localizedSiftingPackage_of_unconditional_almostPeriods
    {A B₁ B₂ : Finset G} {p : Nat} {sigma delta : Real}
    (data : SiftedPopularData A B₁ B₂ p sigma delta)
    (hdelta : delta < 1)
    (S₀ : Finset G) (hS₀ : S₀.Nonempty)
    (approxDelta : Real) (happroxDelta : 0 < approxDelta)
    (m : Nat) (hm : m ≠ 0)
    (B₀ : BohrData G) (hB₀reg : B₀.IsRankRegular)
    (hlocal : S₀ - S₀ ⊆ B₀.carrier)
    (kappa : NNReal)
    (hkappa : kappa + kappa ≤
      1 / (100 * (max B₀.rank 1 : Nat) : NNReal)) :
    ∃ (parent : BohrData G) (parentWidth : NNReal)
      (source : Finset G) (rankCost cardMultiplier : Nat)
      (approximationError : Real),
      Nonempty (LocalizedSiftingPackage data parent parentWidth source
        rankCost cardMultiplier approximationError) := by
  classical
  have houtputs := data.output_nonempty hdelta
  have hnegA : (-data.A₁).Nonempty := by
    obtain ⟨a, ha⟩ := houtputs.1
    exact ⟨-a, by simpa using ha⟩
  have hpopular : (_root_.s p sigma B₁ B₂ A).Nonempty :=
    popularSet_nonempty_of_siftedPopularData data hdelta
  obtain ⟨T, X, z, rho, C₀, Delta, R, _hTS₀, _hzT, _hX,
      _hXne, _hXB₀, _hTcard, _hrhoHalf, _hrhoOne, hC₀,
      hC₀reg, _hDeltaCard, _hDeltaSpec, hRreg, hRrank, hRsub,
      hRcard, hperiod⟩ :=
    LocalizedAlmostPeriodicity.exists_unconditional_localized_linfty_almostPeriods
      (A := -data.A₁) (S₀ := S₀) hnegA hS₀ approxDelta happroxDelta
      m hm (_root_.s p sigma B₁ B₂ A) data.A₂ hpopular houtputs.2
      B₀ hB₀reg hlocal kappa hkappa
  let n : Nat :=
    LocalizedAlmostPeriodicity.spectralQuantization
      (RelativeChangSanders.localChangDimension B₀ X (1 / 2))
  let cardMultiplier : Nat :=
    n ^ Delta.card * 4 ^ (B₀.rank + Delta.card)
  let approximationError : Real :=
    2 * approxDelta +
      (4 * Real.pi * (Delta.card : Real) *
          ((((n : Nat) : NNReal)⁻¹ : Real)) +
        400 * ((max B₀.rank 1 : Nat) : Real) *
          (kappa + kappa : NNReal) +
        2 * (1 / 2 : Real) ^ m) *
      Real.sqrt (((_root_.s p sigma B₁ B₂ A).card : Real) / data.A₂.card)
  refine ⟨C₀, kappa + kappa, (C₀.dilate kappa).carrier,
    Delta.card, cardMultiplier, approximationError, ⟨?_⟩⟩
  refine
    { child := R
      child_regular := hRreg
      rank_bound := ?_
      subordinate := hRsub
      relative_card := ?_
      triple_error := ?_ }
  · simpa [hC₀] using hRrank
  · simpa [n, cardMultiplier, Nat.mul_assoc] using hRcard
  · apply triple_error_of_threefold_dLinfty houtputs.1 houtputs.2
    intro t ht
    simpa [n, approximationError, mul_assoc] using hperiod t ht

/-- Arbitrary-quantization version of the preceding constructor.  The extra
positive integer qQuant multiplies the spectral cell count, so callers can
make the Fourier phase part of approximationError as small as their stopping
budget requires. -/
theorem exists_localizedSiftingPackage_of_unconditional_almostPeriods_scaled
    {A B₁ B₂ : Finset G} {p : Nat} {sigma delta : Real}
    (data : SiftedPopularData A B₁ B₂ p sigma delta)
    (hdelta : delta < 1)
    (S₀ : Finset G) (hS₀ : S₀.Nonempty)
    (approxDelta : Real) (happroxDelta : 0 < approxDelta)
    (m : Nat) (hm : m ≠ 0)
    (B₀ : BohrData G) (hB₀reg : B₀.IsRankRegular)
    (hlocal : S₀ - S₀ ⊆ B₀.carrier)
    (kappa : NNReal)
    (hkappa : kappa + kappa ≤
      1 / (100 * (max B₀.rank 1 : Nat) : NNReal))
    (qQuant : Nat) (hqQuant : 0 < qQuant) :
    ∃ (parent : BohrData G) (parentWidth : NNReal)
      (source : Finset G) (rankCost cardMultiplier : Nat)
      (approximationError : Real),
      Nonempty (LocalizedSiftingPackage data parent parentWidth source
        rankCost cardMultiplier approximationError) := by
  classical
  have houtputs := data.output_nonempty hdelta
  have hnegA : (-data.A₁).Nonempty := by
    obtain ⟨a, ha⟩ := houtputs.1
    exact ⟨-a, by simpa using ha⟩
  have hpopular : (_root_.s p sigma B₁ B₂ A).Nonempty :=
    popularSet_nonempty_of_siftedPopularData data hdelta
  obtain ⟨T, X, z, rho, C₀, Delta, R, _hTS₀, _hzT, _hX,
      _hXne, _hXB₀, _hTcard, _hrhoHalf, _hrhoOne, hC₀,
      hC₀reg, _hDeltaCard, _hDeltaSpec, hRreg, hRrank, hRsub,
      hRcard, hperiod⟩ :=
    LocalizedAlmostPeriodicity.exists_unconditional_localized_linfty_almostPeriods_scaled
      (A := -data.A₁) (S₀ := S₀) hnegA hS₀ approxDelta happroxDelta
      m hm (_root_.s p sigma B₁ B₂ A) data.A₂ hpopular houtputs.2
      B₀ hB₀reg hlocal kappa hkappa qQuant hqQuant
  let n : Nat :=
    qQuant * LocalizedAlmostPeriodicity.spectralQuantization
      (RelativeChangSanders.localChangDimension B₀ X (1 / 2))
  let cardMultiplier : Nat :=
    n ^ Delta.card * 4 ^ (B₀.rank + Delta.card)
  let approximationError : Real :=
    2 * approxDelta +
      (4 * Real.pi * (Delta.card : Real) *
          ((((n : Nat) : NNReal)⁻¹ : Real)) +
        400 * ((max B₀.rank 1 : Nat) : Real) *
          (kappa + kappa : NNReal) +
        2 * (1 / 2 : Real) ^ m) *
      Real.sqrt (((_root_.s p sigma B₁ B₂ A).card : Real) / data.A₂.card)
  refine ⟨C₀, kappa + kappa, (C₀.dilate kappa).carrier,
    Delta.card, cardMultiplier, approximationError, ⟨?_⟩⟩
  refine
    { child := R
      child_regular := hRreg
      rank_bound := ?_
      subordinate := hRsub
      relative_card := ?_
      triple_error := ?_ }
  · simpa [hC₀] using hRrank
  · simpa [n, cardMultiplier, Nat.mul_assoc] using hRcard
  · apply triple_error_of_threefold_dLinfty houtputs.1 houtputs.2
    intro t ht
    simpa [n, approximationError, mul_assoc] using hperiod t ht

/-- Scaled constructor with a caller-chosen final error budget.  The hsmall
hypothesis is stated after replacing the spectral term by the clean bound
2/qQuant, so choosing qQuant large is enough to make the package error
smaller than a prescribed stopping allowance. -/
theorem exists_localizedSiftingPackage_of_unconditional_almostPeriods_scaled_le
    {A B₁ B₂ : Finset G} {p : Nat} {sigma delta : Real}
    (data : SiftedPopularData A B₁ B₂ p sigma delta)
    (hdelta : delta < 1)
    (S₀ : Finset G) (hS₀ : S₀.Nonempty)
    (approxDelta : Real) (happroxDelta : 0 < approxDelta)
    (m : Nat) (hm : m ≠ 0)
    (B₀ : BohrData G) (hB₀reg : B₀.IsRankRegular)
    (hlocal : S₀ - S₀ ⊆ B₀.carrier)
    (kappa : NNReal)
    (hkappa : kappa + kappa ≤
      1 / (100 * (max B₀.rank 1 : Nat) : NNReal))
    (qQuant : Nat) (hqQuant : 0 < qQuant)
    (approximationError : Real)
    (hsmall : ∀ (X : Finset G) (Delta : Finset (AddChar G Complex)),
      (Delta.card : Real) ≤
        RelativeChangSanders.localChangDimension B₀ X (1 / 2) →
      2 * approxDelta +
          (2 / (qQuant : Real) +
            400 * ((max B₀.rank 1 : Nat) : Real) *
              (kappa + kappa : NNReal) +
            2 * (1 / 2 : Real) ^ m) *
          Real.sqrt
            (((_root_.s p sigma B₁ B₂ A).card : Real) / data.A₂.card) ≤
        approximationError) :
    ∃ (parent : BohrData G) (parentWidth : NNReal)
      (source : Finset G) (rankCost cardMultiplier : Nat),
      Nonempty (LocalizedSiftingPackage data parent parentWidth source
        rankCost cardMultiplier approximationError) := by
  classical
  have houtputs := data.output_nonempty hdelta
  have hnegA : (-data.A₁).Nonempty := by
    obtain ⟨a, ha⟩ := houtputs.1
    exact ⟨-a, by simpa using ha⟩
  have hpopular : (_root_.s p sigma B₁ B₂ A).Nonempty :=
    popularSet_nonempty_of_siftedPopularData data hdelta
  obtain ⟨T, X, z, rho, C₀, Delta, R, _hTS₀, _hzT, _hX,
      _hXne, _hXB₀, _hTcard, _hrhoHalf, _hrhoOne, hC₀,
      hC₀reg, hDeltaCard, _hDeltaSpec, hRreg, hRrank, hRsub,
      hRcard, hperiod⟩ :=
    LocalizedAlmostPeriodicity.exists_unconditional_localized_linfty_almostPeriods_scaled
      (A := -data.A₁) (S₀ := S₀) hnegA hS₀ approxDelta happroxDelta
      m hm (_root_.s p sigma B₁ B₂ A) data.A₂ hpopular houtputs.2
      B₀ hB₀reg hlocal kappa hkappa qQuant hqQuant
  let n : Nat :=
    qQuant * LocalizedAlmostPeriodicity.spectralQuantization
      (RelativeChangSanders.localChangDimension B₀ X (1 / 2))
  let cardMultiplier : Nat :=
    n ^ Delta.card * 4 ^ (B₀.rank + Delta.card)
  let rawError : Real :=
    2 * approxDelta +
      (4 * Real.pi * (Delta.card : Real) *
          ((((n : Nat) : NNReal)⁻¹ : Real)) +
        400 * ((max B₀.rank 1 : Nat) : Real) *
          (kappa + kappa : NNReal) +
        2 * (1 / 2 : Real) ^ m) *
      Real.sqrt (((_root_.s p sigma B₁ B₂ A).card : Real) / data.A₂.card)
  have hphase :
      4 * Real.pi * (Delta.card : Real) *
          ((((n : Nat) : NNReal)⁻¹ : Real)) ≤ 2 / (qQuant : Real) := by
    simpa [n] using
      (LocalizedAlmostPeriodicity.scaled_spectral_phase_le
        (RelativeChangSanders.localChangDimension B₀ X (1 / 2))
        Delta.card qQuant hDeltaCard hqQuant)
  have hraw : rawError ≤ approximationError := by
    calc
      rawError ≤
          2 * approxDelta +
            (2 / (qQuant : Real) +
              400 * ((max B₀.rank 1 : Nat) : Real) *
                (kappa + kappa : NNReal) +
              2 * (1 / 2 : Real) ^ m) *
            Real.sqrt
              (((_root_.s p sigma B₁ B₂ A).card : Real) / data.A₂.card) := by
        dsimp only [rawError]
        gcongr
      _ ≤ approximationError := hsmall X Delta hDeltaCard
  refine ⟨C₀, kappa + kappa, (C₀.dilate kappa).carrier,
    Delta.card, cardMultiplier, ⟨?_⟩⟩
  refine
    { child := R
      child_regular := hRreg
      rank_bound := ?_
      subordinate := hRsub
      relative_card := ?_
      triple_error := ?_ }
  · simpa [hC₀] using hRrank
  · simpa [n, cardMultiplier, Nat.mul_assoc] using hRcard
  · have htriple := triple_error_of_threefold_dLinfty houtputs.1 houtputs.2
      (D := R) (error := rawError) (by
        intro t ht
        simpa [n, rawError, mul_assoc] using hperiod t ht)
    intro t ht
    calc
      |LocalizedAlmostPeriodicity.tripleIndicatorSum
          data.A₁ data.A₂ (_root_.s p sigma B₁ B₂ A) t -
        LocalizedAlmostPeriodicity.tripleIndicatorSum
          data.A₁ data.A₂ (_root_.s p sigma B₁ B₂ A) 0|
          ≤ rawError * (data.A₁.card : Real) * data.A₂.card :=
        htriple t ht
      _ ≤ approximationError * (data.A₁.card : Real) * data.A₂.card := by
        gcongr

/-- The Croot--Sisask exponent occurring in the localized AP output, named
so quantitative callers can state the retained-set lower bound without
repeating the nested ceiling expression. -/
noncomputable def localizedAPSampleQ (M L : Finset G) : Nat :=
  ⌈1 + Real.log (min 1 ((L.card : Real) / M.card))⁻¹⌉₊

/-- The corresponding Croot--Sisask sample size. -/
noncomputable def localizedAPSampleK
    (M L : Finset G) (approxDelta : Real) (m : Nat) : Nat :=
  crootSisaskSampleSize (localizedAPSampleQ M L)
    ((approxDelta / m) / Real.exp 1)

/-- Witness-retaining form of the scaled target-error constructor.
Besides the package itself it returns the actual Croot--Sisask set X and
Chang family Delta, together with the raw retained-set lower bound and the
relative Chang dimension bound.  These are precisely the witnesses needed
to dominate rankCost and cardMultiplier by a uniform stopping budget. -/
theorem exists_localizedSiftingPackage_of_unconditional_almostPeriods_scaled_le_with_witnesses
    {A B₁ B₂ : Finset G} {p : Nat} {sigma delta : Real}
    (data : SiftedPopularData A B₁ B₂ p sigma delta)
    (hdelta : delta < 1)
    (S₀ : Finset G) (hS₀ : S₀.Nonempty)
    (approxDelta : Real) (happroxDelta : 0 < approxDelta)
    (m : Nat) (hm : m ≠ 0)
    (B₀ : BohrData G) (hB₀reg : B₀.IsRankRegular)
    (hlocal : S₀ - S₀ ⊆ B₀.carrier)
    (kappa : NNReal)
    (hkappa : kappa + kappa ≤
      1 / (100 * (max B₀.rank 1 : Nat) : NNReal))
    (qQuant : Nat) (hqQuant : 0 < qQuant)
    (approximationError : Real)
    (hsmall : ∀ (X : Finset G) (Delta : Finset (AddChar G Complex)),
      (Delta.card : Real) ≤
        RelativeChangSanders.localChangDimension B₀ X (1 / 2) →
      2 * approxDelta +
          (2 / (qQuant : Real) +
            400 * ((max B₀.rank 1 : Nat) : Real) *
              (kappa + kappa : NNReal) +
            2 * (1 / 2 : Real) ^ m) *
          Real.sqrt
            (((_root_.s p sigma B₁ B₂ A).card : Real) / data.A₂.card) ≤
        approximationError) :
    ∃ (T X : Finset G) (C₀ : BohrData G)
      (Delta : Finset (AddChar G Complex)),
      ((((-data.A₁).card : Real) ^
            localizedAPSampleK (_root_.s p sigma B₁ B₂ A) data.A₂
              approxDelta m / 2 * S₀.card) /
          ((-data.A₁ + S₀).card : Real) ^
            localizedAPSampleK (_root_.s p sigma B₁ B₂ A) data.A₂
              approxDelta m ≤ T.card) ∧
      X.Nonempty ∧ X ⊆ B₀.carrier ∧
      (Delta.card : Real) ≤
        RelativeChangSanders.localChangDimension B₀ X (1 / 2) ∧
      Nonempty
        (LocalizedSiftingPackage data C₀ (kappa + kappa)
          (C₀.dilate kappa).carrier Delta.card
          ((qQuant * LocalizedAlmostPeriodicity.spectralQuantization
              (RelativeChangSanders.localChangDimension B₀ X (1 / 2))) ^
              Delta.card *
            4 ^ (B₀.rank + Delta.card))
          approximationError) := by
  classical
  have houtputs := data.output_nonempty hdelta
  have hnegA : (-data.A₁).Nonempty := by
    obtain ⟨a, ha⟩ := houtputs.1
    exact ⟨-a, by simpa using ha⟩
  have hpopular : (_root_.s p sigma B₁ B₂ A).Nonempty :=
    popularSet_nonempty_of_siftedPopularData data hdelta
  obtain ⟨T, X, z, rho, C₀, Delta, R, _hTS₀, _hzT, _hX,
      hXne, hXB₀, hTcard, _hrhoHalf, _hrhoOne, hC₀,
      hC₀reg, hDeltaCard, _hDeltaSpec, hRreg, hRrank, hRsub,
      hRcard, hperiod⟩ :=
    LocalizedAlmostPeriodicity.exists_unconditional_localized_linfty_almostPeriods_scaled
      (A := -data.A₁) (S₀ := S₀) hnegA hS₀ approxDelta happroxDelta
      m hm (_root_.s p sigma B₁ B₂ A) data.A₂ hpopular houtputs.2
      B₀ hB₀reg hlocal kappa hkappa qQuant hqQuant
  let n : Nat :=
    qQuant * LocalizedAlmostPeriodicity.spectralQuantization
      (RelativeChangSanders.localChangDimension B₀ X (1 / 2))
  let rawError : Real :=
    2 * approxDelta +
      (4 * Real.pi * (Delta.card : Real) *
          ((((n : Nat) : NNReal)⁻¹ : Real)) +
        400 * ((max B₀.rank 1 : Nat) : Real) *
          (kappa + kappa : NNReal) +
        2 * (1 / 2 : Real) ^ m) *
      Real.sqrt (((_root_.s p sigma B₁ B₂ A).card : Real) / data.A₂.card)
  have hphase :
      4 * Real.pi * (Delta.card : Real) *
          ((((n : Nat) : NNReal)⁻¹ : Real)) ≤ 2 / (qQuant : Real) := by
    simpa [n] using
      (LocalizedAlmostPeriodicity.scaled_spectral_phase_le
        (RelativeChangSanders.localChangDimension B₀ X (1 / 2))
        Delta.card qQuant hDeltaCard hqQuant)
  have hraw : rawError ≤ approximationError := by
    calc
      rawError ≤
          2 * approxDelta +
            (2 / (qQuant : Real) +
              400 * ((max B₀.rank 1 : Nat) : Real) *
                (kappa + kappa : NNReal) +
              2 * (1 / 2 : Real) ^ m) *
            Real.sqrt
              (((_root_.s p sigma B₁ B₂ A).card : Real) / data.A₂.card) := by
        dsimp only [rawError]
        gcongr
      _ ≤ approximationError := hsmall X Delta hDeltaCard
  refine ⟨T, X, C₀, Delta, ?_, hXne, hXB₀, hDeltaCard, ⟨?_⟩⟩
  · simpa [localizedAPSampleK, localizedAPSampleQ] using hTcard
  refine
    { child := R
      child_regular := hRreg
      rank_bound := ?_
      subordinate := hRsub
      relative_card := ?_
      triple_error := ?_ }
  · simpa [hC₀] using hRrank
  · simpa [n, Nat.mul_assoc] using hRcard
  · have htriple := triple_error_of_threefold_dLinfty houtputs.1 houtputs.2
      (D := R) (error := rawError) (by
        intro t ht
        simpa [n, rawError, mul_assoc] using hperiod t ht)
    intro t ht
    calc
      |LocalizedAlmostPeriodicity.tripleIndicatorSum
          data.A₁ data.A₂ (_root_.s p sigma B₁ B₂ A) t -
        LocalizedAlmostPeriodicity.tripleIndicatorSum
          data.A₁ data.A₂ (_root_.s p sigma B₁ B₂ A) 0|
          ≤ rawError * (data.A₁.card : Real) * data.A₂.card :=
        htriple t ht
      _ ≤ approximationError * (data.A₁.card : Real) * data.A₂.card := by
        gcongr

/-- TeX-aligned, T-relative package constructor.  It uses the
Bloom--Sisask orientation U=-A₂, M=A₁, L=-S and the relative-T localized AP
theorem.  Hence the Croot sample exponent depends on |S|/|A₁|, while the
Chang dimension is measured using the actual sampled set T inside B₀.
The package error includes the explicit normalization factor |S|/|A₁|. -/
theorem exists_localizedSiftingPackage_of_relativeT_scaled_le_with_witnesses
    {A B₁ B₂ : Finset G} {p : Nat} {sigma delta : Real}
    (data : SiftedPopularData A B₁ B₂ p sigma delta)
    (hdelta : delta < 1)
    (approxDelta : Real) (happroxDelta : 0 < approxDelta)
    (m : Nat) (hm : m ≠ 0)
    (B₀ : BohrData G) (hB₀reg : B₀.IsRankRegular)
    (kappa : NNReal)
    (hkappa : kappa + kappa ≤
      1 / (100 * (max B₀.rank 1 : Nat) : NNReal))
    (qQuant : Nat) (hqQuant : 0 < qQuant)
    (approximationError : Real)
    (hsmall : ∀ (T : Finset G) (Delta : Finset (AddChar G Complex)),
      (Delta.card : Real) ≤
        RelativeChangSanders.localChangDimension B₀ T (1 / 2) →
      (2 * approxDelta +
          (2 / (qQuant : Real) +
            400 * ((max B₀.rank 1 : Nat) : Real) *
              (kappa + kappa : NNReal) +
            2 * (1 / 2 : Real) ^ m) *
          Real.sqrt
            ((data.A₁.card : Real) /
              (_root_.s p sigma B₁ B₂ A).card)) *
          ((_root_.s p sigma B₁ B₂ A).card : Real) / data.A₁.card ≤
        approximationError) :
    ∃ (T X : Finset G) (C₀ : BohrData G)
      (Delta : Finset (AddChar G Complex)),
      ((((-data.A₂).card : Real) ^
            localizedAPSampleK data.A₁ (-(_root_.s p sigma B₁ B₂ A))
              approxDelta m / 2 * B₀.carrier.card) /
          ((-data.A₂ + B₀.carrier).card : Real) ^
            localizedAPSampleK data.A₁ (-(_root_.s p sigma B₁ B₂ A))
              approxDelta m ≤ T.card) ∧
      T ⊆ B₀.carrier ∧ X.Nonempty ∧
      (Delta.card : Real) ≤
        RelativeChangSanders.localChangDimension B₀ T (1 / 2) ∧
      Nonempty
        (LocalizedSiftingPackage data C₀ (kappa + kappa)
          (C₀.dilate kappa).carrier Delta.card
          ((qQuant * LocalizedAlmostPeriodicity.spectralQuantization
              (RelativeChangSanders.localChangDimension B₀ T (1 / 2))) ^
              Delta.card *
            4 ^ (B₀.rank + Delta.card))
          approximationError) := by
  classical
  let S : Finset G := _root_.s p sigma B₁ B₂ A
  have houtputs := data.output_nonempty hdelta
  have hnegA₂ : (-data.A₂).Nonempty := by
    obtain ⟨a, ha⟩ := houtputs.2
    exact ⟨-a, by simpa using ha⟩
  have hS : S.Nonempty := by
    simpa [S] using popularSet_nonempty_of_siftedPopularData data hdelta
  have hnegS : (-S).Nonempty := by
    obtain ⟨s, hs⟩ := hS
    exact ⟨-s, by simpa using hs⟩
  obtain ⟨T, X, z, rho, C₀, Delta, R, hTB₀, _hzT, _hX,
      hXne, hTcard, hrhoHalf, hrhoOne, hC₀, hC₀reg,
      hDeltaCard, _hDeltaSpec, hRreg, hRrank, hRsub, hRcard,
      hperiod⟩ :=
    LocalizedAlmostPeriodicity.exists_unconditional_localized_linfty_almostPeriods_relativeT_scaled
      (A := -data.A₂) hnegA₂ approxDelta happroxDelta m hm
      data.A₁ (-S) houtputs.1 hnegS B₀ hB₀reg kappa hkappa
      qQuant hqQuant
  let n : Nat :=
    qQuant * LocalizedAlmostPeriodicity.spectralQuantization
      (RelativeChangSanders.localChangDimension B₀ T (1 / 2))
  let rawError : Real :=
    2 * approxDelta +
      (4 * Real.pi * (Delta.card : Real) *
          ((((n : Nat) : NNReal)⁻¹ : Real)) +
        400 * ((max B₀.rank 1 : Nat) : Real) *
          (kappa + kappa : NNReal) +
        2 * (1 / 2 : Real) ^ m) *
      Real.sqrt ((data.A₁.card : Real) / S.card)
  have hphase :
      4 * Real.pi * (Delta.card : Real) *
          ((((n : Nat) : NNReal)⁻¹ : Real)) ≤ 2 / (qQuant : Real) := by
    simpa [n] using
      (LocalizedAlmostPeriodicity.scaled_spectral_phase_le
        (RelativeChangSanders.localChangDimension B₀ T (1 / 2))
        Delta.card qQuant hDeltaCard hqQuant)
  have hrawBase :
      rawError ≤
        2 * approxDelta +
          (2 / (qQuant : Real) +
            400 * ((max B₀.rank 1 : Nat) : Real) *
              (kappa + kappa : NNReal) +
            2 * (1 / 2 : Real) ^ m) *
          Real.sqrt ((data.A₁.card : Real) / S.card) := by
    dsimp only [rawError]
    gcongr
  have hraw :
      rawError * (S.card : Real) / data.A₁.card ≤ approximationError := by
    calc
      rawError * (S.card : Real) / data.A₁.card ≤
          (2 * approxDelta +
            (2 / (qQuant : Real) +
              400 * ((max B₀.rank 1 : Nat) : Real) *
                (kappa + kappa : NNReal) +
              2 * (1 / 2 : Real) ^ m) *
            Real.sqrt ((data.A₁.card : Real) / S.card)) *
              (S.card : Real) / data.A₁.card := by
        gcongr
      _ ≤ approximationError := by simpa [S] using hsmall T Delta hDeltaCard
  refine ⟨T, X, C₀, Delta, ?_, hTB₀, hXne, hDeltaCard, ⟨?_⟩⟩
  · simpa [S, localizedAPSampleK, localizedAPSampleQ] using hTcard
  refine
    { child := R
      child_regular := hRreg
      rank_bound := ?_
      subordinate := hRsub
      relative_card := ?_
      triple_error := ?_ }
  · simpa [hC₀] using hRrank
  · simpa [n, Nat.mul_assoc] using hRcard
  · have htriple := triple_error_of_reflected_threefold_dLinfty
      houtputs.1 houtputs.2 hS (D := R) (error := rawError) (by
        intro t ht
        simpa [S, n, rawError, mul_assoc] using hperiod t ht)
    intro t ht
    calc
      |LocalizedAlmostPeriodicity.tripleIndicatorSum
          data.A₁ data.A₂ (_root_.s p sigma B₁ B₂ A) t -
        LocalizedAlmostPeriodicity.tripleIndicatorSum
          data.A₁ data.A₂ (_root_.s p sigma B₁ B₂ A) 0|
          ≤ (rawError * (S.card : Real) / data.A₁.card) *
              (data.A₁.card : Real) * data.A₂.card := by
            simpa [S] using htriple t ht
      _ ≤ approximationError * (data.A₁.card : Real) * data.A₂.card := by
        gcongr

/-- Support-restricted TeX-aligned relative-T constructor.  This is the
quantitative version used by the final density step: S is the popular set
intersected with B₁-B₂, so all Croot, Fourier, and Chang cardinality terms
are local rather than ambient-sized. -/
theorem exists_supportedLocalizedSiftingPackage_of_relativeT_scaled_le_with_witnesses
    {A B₁ B₂ : Finset G} {p : Nat} {sigma delta : Real}
    (data : SiftedPopularData A B₁ B₂ p sigma delta)
    (hdelta : delta < 1)
    (approxDelta : Real) (happroxDelta : 0 < approxDelta)
    (m : Nat) (hm : m ≠ 0)
    (B₀ : BohrData G) (hB₀reg : B₀.IsRankRegular)
    (kappa : NNReal)
    (hkappa : kappa + kappa ≤
      1 / (100 * (max B₀.rank 1 : Nat) : NNReal))
    (qQuant : Nat) (hqQuant : 0 < qQuant)
    (approximationError : Real)
    (hsmall : ∀ (T : Finset G) (Delta : Finset (AddChar G Complex)),
      (Delta.card : Real) ≤
        RelativeChangSanders.localChangDimension B₀ T (1 / 2) →
      (2 * approxDelta +
          (2 / (qQuant : Real) +
            400 * ((max B₀.rank 1 : Nat) : Real) *
              (kappa + kappa : NNReal) +
            2 * (1 / 2 : Real) ^ m) *
          Real.sqrt
            ((data.A₁.card : Real) /
              (SiftedPopularData.supportedPopularSet A B₁ B₂ p sigma).card)) *
          ((SiftedPopularData.supportedPopularSet A B₁ B₂ p sigma).card : Real) /
            data.A₁.card ≤ approximationError) :
    ∃ (T X : Finset G) (rho : NNReal) (C₀ : BohrData G)
      (Delta : Finset (AddChar G Complex)),
      ((((-data.A₂).card : Real) ^
            localizedAPSampleK data.A₁
              (-(SiftedPopularData.supportedPopularSet A B₁ B₂ p sigma))
              approxDelta m / 2 * B₀.carrier.card) /
          ((-data.A₂ + B₀.carrier).card : Real) ^
            localizedAPSampleK data.A₁
              (-(SiftedPopularData.supportedPopularSet A B₁ B₂ p sigma))
              approxDelta m ≤ T.card) ∧
      T ⊆ B₀.carrier ∧ X.Nonempty ∧
      (Delta.card : Real) ≤
        RelativeChangSanders.localChangDimension B₀ T (1 / 2) ∧
      1 / 2 ≤ rho ∧ rho ≤ 1 ∧
      C₀ = B₀.dilate (rho *
        RelativeChangSanders.localChangBaseScale B₀ T (1 / 2)) ∧
      Nonempty
        (SupportedLocalizedSiftingPackage data C₀ (kappa + kappa)
          (C₀.dilate kappa).carrier Delta.card
          ((qQuant * LocalizedAlmostPeriodicity.spectralQuantization
              (RelativeChangSanders.localChangDimension B₀ T (1 / 2))) ^
              Delta.card *
            4 ^ (B₀.rank + Delta.card))
          approximationError) := by
  classical
  let S : Finset G :=
    SiftedPopularData.supportedPopularSet A B₁ B₂ p sigma
  have houtputs := data.output_nonempty hdelta
  have hnegA₂ : (-data.A₂).Nonempty := by
    obtain ⟨a, ha⟩ := houtputs.2
    exact ⟨-a, by simpa using ha⟩
  have hS : S.Nonempty := by
    simpa [S] using data.supportedPopularSet_nonempty hdelta
  have hnegS : (-S).Nonempty := by
    obtain ⟨s, hs⟩ := hS
    exact ⟨-s, by simpa using hs⟩
  obtain ⟨T, X, z, rho, C₀, Delta, R, hTB₀, _hzT, _hX,
      hXne, hTcard, hrhoHalf, hrhoOne, hC₀, hC₀reg,
      hDeltaCard, _hDeltaSpec, hRreg, hRrank, hRsub, hRcard,
      hperiod⟩ :=
    LocalizedAlmostPeriodicity.exists_unconditional_localized_linfty_almostPeriods_relativeT_scaled
      (A := -data.A₂) hnegA₂ approxDelta happroxDelta m hm
      data.A₁ (-S) houtputs.1 hnegS B₀ hB₀reg kappa hkappa
      qQuant hqQuant
  let n : Nat :=
    qQuant * LocalizedAlmostPeriodicity.spectralQuantization
      (RelativeChangSanders.localChangDimension B₀ T (1 / 2))
  let rawError : Real :=
    2 * approxDelta +
      (4 * Real.pi * (Delta.card : Real) *
          ((((n : Nat) : NNReal)⁻¹ : Real)) +
        400 * ((max B₀.rank 1 : Nat) : Real) *
          (kappa + kappa : NNReal) +
        2 * (1 / 2 : Real) ^ m) *
      Real.sqrt ((data.A₁.card : Real) / S.card)
  have hphase :
      4 * Real.pi * (Delta.card : Real) *
          ((((n : Nat) : NNReal)⁻¹ : Real)) ≤ 2 / (qQuant : Real) := by
    simpa [n] using
      (LocalizedAlmostPeriodicity.scaled_spectral_phase_le
        (RelativeChangSanders.localChangDimension B₀ T (1 / 2))
        Delta.card qQuant hDeltaCard hqQuant)
  have hrawBase :
      rawError ≤
        2 * approxDelta +
          (2 / (qQuant : Real) +
            400 * ((max B₀.rank 1 : Nat) : Real) *
              (kappa + kappa : NNReal) +
            2 * (1 / 2 : Real) ^ m) *
          Real.sqrt ((data.A₁.card : Real) / S.card) := by
    dsimp only [rawError]
    gcongr
  have hraw :
      rawError * (S.card : Real) / data.A₁.card ≤ approximationError := by
    calc
      rawError * (S.card : Real) / data.A₁.card ≤
          (2 * approxDelta +
            (2 / (qQuant : Real) +
              400 * ((max B₀.rank 1 : Nat) : Real) *
                (kappa + kappa : NNReal) +
              2 * (1 / 2 : Real) ^ m) *
            Real.sqrt ((data.A₁.card : Real) / S.card)) *
              (S.card : Real) / data.A₁.card := by
        gcongr
      _ ≤ approximationError := by simpa [S] using hsmall T Delta hDeltaCard
  refine ⟨T, X, rho, C₀, Delta, ?_, hTB₀, hXne, hDeltaCard,
    hrhoHalf, hrhoOne, hC₀, ⟨?_⟩⟩
  · simpa [S, localizedAPSampleK, localizedAPSampleQ] using hTcard
  refine
    { child := R
      child_regular := hRreg
      rank_bound := ?_
      subordinate := hRsub
      relative_card := ?_
      triple_error := ?_ }
  · simpa [hC₀] using hRrank
  · simpa [n, Nat.mul_assoc] using hRcard
  · have htriple := triple_error_of_reflected_threefold_dLinfty
      houtputs.1 houtputs.2 hS (D := R) (error := rawError) (by
        intro t ht
        simpa [S, n, rawError, mul_assoc] using hperiod t ht)
    intro t ht
    calc
      |LocalizedAlmostPeriodicity.tripleIndicatorSum
          data.A₁ data.A₂
            (SiftedPopularData.supportedPopularSet A B₁ B₂ p sigma) t -
        LocalizedAlmostPeriodicity.tripleIndicatorSum
          data.A₁ data.A₂
            (SiftedPopularData.supportedPopularSet A B₁ B₂ p sigma) 0|
          ≤ (rawError * (S.card : Real) / data.A₁.card) *
              (data.A₁.card : Real) * data.A₂.card := by
            simpa [S] using htriple t ht
      _ ≤ approximationError * (data.A₁.card : Real) * data.A₂.card := by
        gcongr

/-- Support-restricted relative-T constructor with the normalization-compatible
Bloom--Sisask ordering.  The Croot input is -A₂, the unnormalized middle set
is -S, and the final normalized set is A₁.  Consequently the sample exponent
depends on |A₁|/|S|, while the almost-period error transfers directly to the
triple sum without an additional |S|/|A₁| factor. -/
theorem exists_supportedLocalizedSiftingPackage_of_relativeT_scaled_le_with_witnesses_commuted
    {A B₁ B₂ : Finset G} {p : Nat} {sigma delta : Real}
    (data : SiftedPopularData A B₁ B₂ p sigma delta)
    (hdelta : delta < 1)
    (approxDelta : Real) (happroxDelta : 0 < approxDelta)
    (m : Nat) (hm : m ≠ 0)
    (B₀ : BohrData G) (hB₀reg : B₀.IsRankRegular)
    (kappa : NNReal)
    (hkappa : kappa + kappa ≤
      1 / (100 * (max B₀.rank 1 : Nat) : NNReal))
    (qQuant : Nat) (hqQuant : 0 < qQuant)
    (approximationError : Real)
    (hsmall : ∀ (T : Finset G) (Delta : Finset (AddChar G Complex)),
      (Delta.card : Real) ≤
        RelativeChangSanders.localChangDimension B₀ T (1 / 2) →
      2 * approxDelta +
          (2 / (qQuant : Real) +
            400 * ((max B₀.rank 1 : Nat) : Real) *
              (kappa + kappa : NNReal) +
            2 * (1 / 2 : Real) ^ m) *
          Real.sqrt
            (((SiftedPopularData.supportedPopularSet A B₁ B₂ p sigma).card : Real) /
              data.A₁.card) ≤ approximationError) :
    ∃ (T X : Finset G) (rho : NNReal) (C₀ : BohrData G)
      (Delta : Finset (AddChar G Complex)),
      ((((-data.A₂).card : Real) ^
            localizedAPSampleK
              (-(SiftedPopularData.supportedPopularSet A B₁ B₂ p sigma))
              data.A₁ approxDelta m / 2 * B₀.carrier.card) /
          ((-data.A₂ + B₀.carrier).card : Real) ^
            localizedAPSampleK
              (-(SiftedPopularData.supportedPopularSet A B₁ B₂ p sigma))
              data.A₁ approxDelta m ≤ T.card) ∧
      T ⊆ B₀.carrier ∧ X.Nonempty ∧
      (Delta.card : Real) ≤
        RelativeChangSanders.localChangDimension B₀ T (1 / 2) ∧
      1 / 2 ≤ rho ∧ rho ≤ 1 ∧
      C₀ = B₀.dilate (rho *
        RelativeChangSanders.localChangBaseScale B₀ T (1 / 2)) ∧
      Nonempty
        (SupportedLocalizedSiftingPackage data C₀ (kappa + kappa)
          (C₀.dilate kappa).carrier Delta.card
          ((qQuant * LocalizedAlmostPeriodicity.spectralQuantization
              (RelativeChangSanders.localChangDimension B₀ T (1 / 2))) ^
              Delta.card *
            4 ^ (B₀.rank + Delta.card))
          approximationError) := by
  classical
  let S : Finset G :=
    SiftedPopularData.supportedPopularSet A B₁ B₂ p sigma
  have houtputs := data.output_nonempty hdelta
  have hnegA₂ : (-data.A₂).Nonempty := by
    obtain ⟨a, ha⟩ := houtputs.2
    exact ⟨-a, by simpa using ha⟩
  have hS : S.Nonempty := by
    simpa [S] using data.supportedPopularSet_nonempty hdelta
  have hnegS : (-S).Nonempty := by
    obtain ⟨s, hs⟩ := hS
    exact ⟨-s, by simpa using hs⟩
  obtain ⟨T, X, z, rho, C₀, Delta, R, hTB₀, _hzT, _hX,
      hXne, hTcard, hrhoHalf, hrhoOne, hC₀, hC₀reg,
      hDeltaCard, _hDeltaSpec, hRreg, hRrank, hRsub, hRcard,
      hperiod⟩ :=
    LocalizedAlmostPeriodicity.exists_unconditional_localized_linfty_almostPeriods_relativeT_scaled
      (A := -data.A₂) hnegA₂ approxDelta happroxDelta m hm
      (-S) data.A₁ hnegS houtputs.1 B₀ hB₀reg kappa hkappa
      qQuant hqQuant
  let n : Nat :=
    qQuant * LocalizedAlmostPeriodicity.spectralQuantization
      (RelativeChangSanders.localChangDimension B₀ T (1 / 2))
  let rawError : Real :=
    2 * approxDelta +
      (4 * Real.pi * (Delta.card : Real) *
          ((((n : Nat) : NNReal)⁻¹ : Real)) +
        400 * ((max B₀.rank 1 : Nat) : Real) *
          (kappa + kappa : NNReal) +
        2 * (1 / 2 : Real) ^ m) *
      Real.sqrt ((S.card : Real) / data.A₁.card)
  have hphase :
      4 * Real.pi * (Delta.card : Real) *
          ((((n : Nat) : NNReal)⁻¹ : Real)) ≤ 2 / (qQuant : Real) := by
    simpa [n] using
      (LocalizedAlmostPeriodicity.scaled_spectral_phase_le
        (RelativeChangSanders.localChangDimension B₀ T (1 / 2))
        Delta.card qQuant hDeltaCard hqQuant)
  have hraw : rawError ≤ approximationError := by
    calc
      rawError ≤
          2 * approxDelta +
            (2 / (qQuant : Real) +
              400 * ((max B₀.rank 1 : Nat) : Real) *
                (kappa + kappa : NNReal) +
              2 * (1 / 2 : Real) ^ m) *
            Real.sqrt ((S.card : Real) / data.A₁.card) := by
        dsimp only [rawError]
        gcongr
      _ ≤ approximationError := by simpa [S] using hsmall T Delta hDeltaCard
  refine ⟨T, X, rho, C₀, Delta, ?_, hTB₀, hXne, hDeltaCard,
    hrhoHalf, hrhoOne, hC₀, ⟨?_⟩⟩
  · simpa [S, localizedAPSampleK, localizedAPSampleQ] using hTcard
  refine
    { child := R
      child_regular := hRreg
      rank_bound := ?_
      subordinate := hRsub
      relative_card := ?_
      triple_error := ?_ }
  · simpa [hC₀] using hRrank
  · simpa [n, Nat.mul_assoc] using hRcard
  · have htriple := triple_error_of_commuted_reflected_threefold_dLinfty
      houtputs.1 houtputs.2 (D := R) (error := rawError) (by
        intro t ht
        simpa [S, n, rawError, mul_assoc] using hperiod t ht)
    intro t ht
    calc
      |LocalizedAlmostPeriodicity.tripleIndicatorSum
          data.A₁ data.A₂
            (SiftedPopularData.supportedPopularSet A B₁ B₂ p sigma) t -
        LocalizedAlmostPeriodicity.tripleIndicatorSum
          data.A₁ data.A₂
            (SiftedPopularData.supportedPopularSet A B₁ B₂ p sigma) 0|
          ≤ rawError * (data.A₁.card : Real) * data.A₂.card := by
            simpa [S] using htriple t ht
      _ ≤ approximationError * (data.A₁.card : Real) * data.A₂.card := by
        gcongr

end AnalyticLocatedIncrement

/-! ## Bourgain narrowing as a concrete count-or-increment step -/

/-- The simultaneous dense-translate alternative left for the analytic
counting argument after Bourgain narrowing. -/
def HasDensePair {original : Finset G} (s : LocatedRestriction original)
    (childOne childTwo : RegularChild (G := G)) (epsilon : Real) : Prop :=
  ∃ x ∈ s.ambient,
    (1 - epsilon) * s.density ≤
      localDensity s.restriction.set childOne.carrier x ∧
    (1 - epsilon) * s.density ≤
      localDensity s.restriction.set childTwo.carrier x

/-- Turn the simultaneous dense-translate alternative into the exact two
finite sets consumed by the Holder endpoint.  Both fibres have the same
translation into the original set. -/
theorem exists_fibers_of_densePair
    {original : Finset G} {s : LocatedRestriction original}
    {childOne childTwo : RegularChild (G := G)} {epsilon : Real}
    (hepsilon : epsilon < 1)
    (hpair : HasDensePair s childOne childTwo epsilon) :
    ∃ x : G, ∃ A' A'' : Finset G,
      A'.Nonempty ∧ A''.Nonempty ∧
      A' ⊆ childOne.carrier ∧ A'' ⊆ childTwo.carrier ∧
      (1 - epsilon) * s.density * (childOne.carrier.card : Real) ≤
        (A'.card : Real) ∧
      (1 - epsilon) * s.density * (childTwo.carrier.card : Real) ≤
        (A''.card : Real) ∧
      (∀ z ∈ A', z - (s.shift - x) ∈ original) ∧
      (∀ z ∈ A'', z - (s.shift - x) ∈ original) := by
  obtain ⟨x, _hxAmbient, hxOne, hxTwo⟩ := hpair
  let A' := narrowingSet s.restriction.set childOne.carrier x
  let A'' := narrowingSet s.restriction.set childTwo.carrier x
  have hfactor : 0 < (1 - epsilon) * s.density :=
    mul_pos (sub_pos.mpr hepsilon) s.density_pos
  have hposOne : 0 < localDensity s.restriction.set childOne.carrier x :=
    hfactor.trans_le hxOne
  have hposTwo : 0 < localDensity s.restriction.set childTwo.carrier x :=
    hfactor.trans_le hxTwo
  have hA' : A'.Nonempty :=
    narrowingSet_nonempty_of_localDensity_pos childOne.carrier_nonempty hposOne
  have hA'' : A''.Nonempty :=
    narrowingSet_nonempty_of_localDensity_pos childTwo.carrier_nonempty hposTwo
  have hcardOnePos : (0 : Real) < childOne.carrier.card := by
    exact_mod_cast childOne.carrier_nonempty.card_pos
  have hcardTwoPos : (0 : Real) < childTwo.carrier.card := by
    exact_mod_cast childTwo.carrier_nonempty.card_pos
  have hdensityOne :
      (1 - epsilon) * s.density * (childOne.carrier.card : Real) ≤
        (A'.card : Real) := by
    rw [localDensity_eq_card_narrowingSet_div
      childOne.carrier_nonempty x] at hxOne
    exact (le_div_iff₀ hcardOnePos).mp (by simpa [A'] using hxOne)
  have hdensityTwo :
      (1 - epsilon) * s.density * (childTwo.carrier.card : Real) ≤
        (A''.card : Real) := by
    rw [localDensity_eq_card_narrowingSet_div
      childTwo.carrier_nonempty x] at hxTwo
    exact (le_div_iff₀ hcardTwoPos).mp (by simpa [A''] using hxTwo)
  refine ⟨x, A', A'', hA', hA'', ?_, ?_, hdensityOne, hdensityTwo, ?_, ?_⟩
  · exact narrowingSet_subset_carrier (B := childOne.bohr)
      (rho := childOne.outer) (fun _ h => h)
  · exact narrowingSet_subset_carrier (B := childTwo.bohr)
      (rho := childTwo.outer) (fun _ h => h)
  · intro z hz
    have hzSet := (mem_narrowingSet.mp hz).2
    have hsource := s.subset_original (x + z) hzSet
    have heq : z - (s.shift - x) = (x + z) - s.shift := by abel
    rwa [heq]
  · intro z hz
    have hzSet := (mem_narrowingSet.mp hz).2
    have hsource := s.subset_original (x + z) hzSet
    have heq : z - (s.shift - x) = (x + z) - s.shift := by abel
    rwa [heq]

/-- **Concrete narrowing alternative.**  If the parent carrier is on an
exact plateau and the two actual regular child carriers lie in its small
carrier, then either they have a common dense translate, or one of them is an
actual located regular restriction with a `(1+epsilon/2)` density increment.

The rank and size clauses are hypotheses about the already constructed child
Bohr data, rather than conclusions about a fictitious numerical state. -/
theorem densePair_or_controlledIncrement
    {original : Finset G} (s : LocatedRestriction original)
    {eta : NNReal}
    (hplateau : s.restriction.bohr.IsPlateauRegularAt s.restriction.outer eta)
    (childOne childTwo : RegularChild (G := G))
    (hsmallOne : childOne.carrier ⊆
      (s.restriction.bohr.dilate eta).carrier)
    (hsmallTwo : childTwo.carrier ⊆
      (s.restriction.bohr.dilate eta).carrier)
    {epsilon sizeCost : Real} {rankCost : Nat}
    (hepsilon : 0 < epsilon)
    (hrankOne : childOne.bohr.rank ≤ s.rank + rankCost)
    (hrankTwo : childTwo.bohr.rank ≤ s.rank + rankCost)
    (hcardOne : Real.exp (-sizeCost) * (s.card : Real) ≤ childOne.carrier.card)
    (hcardTwo : Real.exp (-sizeCost) * (s.card : Real) ≤ childTwo.carrier.card) :
    HasDensePair s childOne childTwo epsilon ∨
      ∃ t : LocatedRestriction original,
        IsControlledIncrement (1 + epsilon / 2) rankCost sizeCost
          s.restriction t.restriction := by
  have hnarrow := bohr_narrowing_alternative hplateau s.restriction.nonempty
    s.restriction.subset_carrier childOne.carrier_nonempty childTwo.carrier_nonempty
    hsmallOne hsmallTwo hepsilon
  rcases hnarrow with hpair | hincOne | hincTwo
  · exact Or.inl hpair
  · right
    obtain ⟨x, hx⟩ := hincOne
    have hdensityEq :
        relativeDensityOn s.restriction.set
            (s.restriction.bohr.dilate s.restriction.outer).carrier = s.density := rfl
    rw [hdensityEq] at hx
    have hpos : 0 < localDensity s.restriction.set childOne.carrier x :=
      by nlinarith [hx, s.density_pos, hepsilon]
    let t := narrowLocated s childOne x hpos
    exact ⟨t, narrowLocated_isControlledIncrement s childOne x hpos hx
      hrankOne hcardOne⟩
  · right
    obtain ⟨x, hx⟩ := hincTwo
    have hdensityEq :
        relativeDensityOn s.restriction.set
            (s.restriction.bohr.dilate s.restriction.outer).carrier = s.density := rfl
    rw [hdensityEq] at hx
    have hpos : 0 < localDensity s.restriction.set childTwo.carrier x :=
      by nlinarith [hx, s.density_pos, hepsilon]
    let t := narrowLocated s childTwo x hpos
    exact ⟨t, narrowLocated_isControlledIncrement s childTwo x hpos hx
      hrankTwo hcardTwo⟩

/-- Quantitative rank-regular version of the concrete narrowing alternative.
Here the current located restriction is represented at unit outer scale, so
its ambient carrier is literally the carrier of its rank-regular Bohr datum.
The explicit smallness inequality is the one consumed by
bohr_narrowing_alternative_of_rankRegular; no plateau witness is used. -/
theorem densePair_or_controlledIncrement_of_rankRegular
    {original : Finset G} (s : LocatedRestriction original)
    (houter : s.restriction.outer = 1)
    (hreg : s.restriction.bohr.IsRankRegular)
    {kappa : NNReal}
    (hkappa : kappa ≤
      1 / (100 * (max s.restriction.bohr.rank 1 : Nat) : NNReal))
    (childOne childTwo : RegularChild (G := G))
    (hsmallOne : childOne.carrier ⊆
      (s.restriction.bohr.dilate kappa).carrier)
    (hsmallTwo : childTwo.carrier ⊆
      (s.restriction.bohr.dilate kappa).carrier)
    {epsilon sizeCost : Real} {rankCost : Nat}
    (hepsilon : 0 < epsilon)
    (hsmall :
      400 * ((max s.restriction.bohr.rank 1 : Nat) : Real) *
          (kappa : Real) ≤ epsilon * s.density / 4)
    (hrankOne : childOne.bohr.rank ≤ s.rank + rankCost)
    (hrankTwo : childTwo.bohr.rank ≤ s.rank + rankCost)
    (hcardOne : Real.exp (-sizeCost) * (s.card : Real) ≤ childOne.carrier.card)
    (hcardTwo : Real.exp (-sizeCost) * (s.card : Real) ≤ childTwo.carrier.card) :
    HasDensePair s childOne childTwo epsilon ∨
      ∃ t : LocatedRestriction original,
        IsControlledIncrement (1 + epsilon / 2) rankCost sizeCost
          s.restriction t.restriction := by
  have hAcarrier :
      s.restriction.set ⊆ s.restriction.bohr.carrier := by
    simpa [BohrStopping.RegularRestriction.ambient, houter] using
      s.restriction.subset_carrier
  have hdensityEq :
      relativeDensityOn s.restriction.set s.restriction.bohr.carrier =
        s.density := by
    unfold LocatedRestriction.density BohrStopping.RegularRestriction.density
      relativeDensityOn BohrStopping.RegularRestriction.ambient
    simp [houter]
  have hsmall' :
      400 * ((max s.restriction.bohr.rank 1 : Nat) : Real) *
          (kappa : Real) ≤
        epsilon *
          relativeDensityOn s.restriction.set s.restriction.bohr.carrier / 4 := by
    simpa only [hdensityEq] using hsmall
  have hnarrow :=
    bohr_narrowing_alternative_of_rankRegular hreg hkappa
      s.restriction.nonempty hAcarrier childOne.carrier_nonempty
      childTwo.carrier_nonempty hsmallOne hsmallTwo hepsilon hsmall'
  rcases hnarrow with hpair | hincOne | hincTwo
  · left
    obtain ⟨x, hx, hxOne, hxTwo⟩ := hpair
    refine ⟨x, ?_, ?_, ?_⟩
    · simpa [LocatedRestriction.ambient,
        BohrStopping.RegularRestriction.ambient, houter] using hx
    · simpa only [hdensityEq] using hxOne
    · simpa only [hdensityEq] using hxTwo
  · right
    obtain ⟨x, hx⟩ := hincOne
    rw [hdensityEq] at hx
    have hpos : 0 < localDensity s.restriction.set childOne.carrier x := by
      nlinarith [hx, s.density_pos, hepsilon]
    let t := narrowLocated s childOne x hpos
    exact ⟨t, narrowLocated_isControlledIncrement s childOne x hpos hx
      hrankOne hcardOne⟩
  · right
    obtain ⟨x, hx⟩ := hincTwo
    rw [hdensityEq] at hx
    have hpos : 0 < localDensity s.restriction.set childTwo.carrier x := by
      nlinarith [hx, s.density_pos, hepsilon]
    let t := narrowLocated s childTwo x hpos
    exact ⟨t, narrowLocated_isControlledIncrement s childTwo x hpos hx
      hrankTwo hcardTwo⟩

/-- All concrete Bohr-geometric data required at one narrowing step.  This
is the interface supplied by the relative Chang--Sanders and localized
almost-periodicity construction: it contains actual Bohr data and actual
cardinality inequalities, not a numerical state or the desired increment. -/
structure NarrowingPackage {original : Finset G}
    (s : LocatedRestriction original) (epsilon sizeCost : Real)
    (rankCost : Nat) where
  eta : NNReal
  plateau : s.restriction.bohr.IsPlateauRegularAt s.restriction.outer eta
  childOne : RegularChild (G := G)
  childTwo : RegularChild (G := G)
  smallOne : childOne.carrier ⊆
    (s.restriction.bohr.dilate eta).carrier
  smallTwo : childTwo.carrier ⊆
    (s.restriction.bohr.dilate eta).carrier
  rankOne : childOne.bohr.rank ≤ s.rank + rankCost
  rankTwo : childTwo.bohr.rank ≤ s.rank + rankCost
  cardOne : Real.exp (-sizeCost) * (s.card : Real) ≤ childOne.carrier.card
  cardTwo : Real.exp (-sizeCost) * (s.card : Real) ≤ childTwo.carrier.card

/-- The terminal alternative associated to a concrete geometric package. -/
def HasCertifiedDensePair {original : Finset G}
    (s : LocatedRestriction original) (epsilon sizeCost : Real)
    (rankCost : Nat) : Prop :=
  ∃ P : NarrowingPackage s epsilon sizeCost rankCost,
    HasDensePair s P.childOne P.childTwo epsilon

/-- **Concrete one-step count-or-increment interface.**  Once the analytic
construction has produced its two actual regular children, the outcome is
unconditional: either those same children and their common dense translate
are retained for the counting endpoint, or an actual located restriction is
returned.  In particular, the first alternative is not merely a numerical
assertion; it contains the finite Bohr carriers later used to construct the
two Holder fibres. -/
theorem certifiedDensePair_or_controlledIncrement
    {original : Finset G} (s : LocatedRestriction original)
    {epsilon sizeCost : Real} {rankCost : Nat}
    (hepsilon : 0 < epsilon)
    (P : NarrowingPackage s epsilon sizeCost rankCost) :
    HasCertifiedDensePair s epsilon sizeCost rankCost ∨
      ∃ t : LocatedRestriction original,
        IsControlledIncrement (1 + epsilon / 2) rankCost sizeCost
          s.restriction t.restriction := by
  rcases densePair_or_controlledIncrement s P.plateau P.childOne P.childTwo
      P.smallOne P.smallTwo hepsilon P.rankOne P.rankTwo P.cardOne P.cardTwo with
    hdense | hincrement
  · exact Or.inl ⟨P, hdense⟩
  · exact Or.inr hincrement

/-- **Packaged one-step density increment.**  If the relative-spectrum
construction supplies concrete narrowing data at every located restriction,
then failure of the simultaneous dense-pair alternative produces an actual
provenance-preserving controlled increment.  This is the exact
`ProducesIncrement`-style input for the located stopping recursion. -/
theorem producesLocatedIncrement_of_narrowingPackages
    {original : Finset G} {epsilon sizeCost : Real} {rankCost : Nat}
    (hepsilon : 0 < epsilon)
    (hsupply : ∀ s : LocatedRestriction original,
      NarrowingPackage s epsilon sizeCost rankCost) :
    ProducesLocatedIncrement
      (fun s : LocatedRestriction original =>
        ¬ HasCertifiedDensePair s epsilon sizeCost rankCost)
      (1 + epsilon / 2) rankCost sizeCost := by
  intro s hbad
  let P := hsupply s
  rcases certifiedDensePair_or_controlledIncrement s hepsilon P with
    hdense | hincrement
  · exact (hbad hdense).elim
  · exact hincrement

#print axioms Refinement.mem_meet_carrier
#print axioms localDensity_eq_card_narrowingSet_div
#print axioms smoothed_popular_mass_lower_bound
#print axioms exists_sifted_popular_mass
#print axioms SiftedPopularData.supported_popular_mass
#print axioms SiftedPopularData.dddconv_mu_le_inv_card_left
#print axioms SiftedPopularData.one_sub_delta_mul_card_le_card_supportedPopularSet
#print axioms SiftedPopularData.card_div_two_le_card_supportedPopularSet
#print axioms LocalizedSiftingPackage.mono
#print axioms SupportedLocalizedSiftingPackage.mono
#print axioms narrowLocated_isControlledIncrement
#print axioms highSmoothingNorm_locatedIncrement
#print axioms highSmoothingNorm_locatedIncrement_supported
#print axioms triple_error_of_threefold_dLinfty
#print axioms tripleIndicatorSum_reflect_swap
#print axioms triple_error_of_reflected_threefold_dLinfty
#print axioms tripleIndicatorSum_commuted_reflect
#print axioms triple_error_of_commuted_reflected_threefold_dLinfty
#print axioms exists_localizedSiftingPackage_of_unconditional_almostPeriods
#print axioms exists_localizedSiftingPackage_of_unconditional_almostPeriods_scaled
#print axioms exists_localizedSiftingPackage_of_unconditional_almostPeriods_scaled_le
#print axioms exists_localizedSiftingPackage_of_unconditional_almostPeriods_scaled_le_with_witnesses
#print axioms exists_localizedSiftingPackage_of_relativeT_scaled_le_with_witnesses
#print axioms exists_supportedLocalizedSiftingPackage_of_relativeT_scaled_le_with_witnesses
#print axioms exists_supportedLocalizedSiftingPackage_of_relativeT_scaled_le_with_witnesses_commuted
#print axioms densePair_or_controlledIncrement
#print axioms densePair_or_controlledIncrement_of_rankRegular
#print axioms certifiedDensePair_or_controlledIncrement
#print axioms producesLocatedIncrement_of_narrowingPackages

end

end Erdos140.DensityStep
