/-
Copyright (c) 2026 The Erdos Problems Formalization Project.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Erdos Problems Formalization Project
-/
module

public import ErdosProblems.Erdos1165.NegativeBinomial
public import ErdosProblems.Erdos1165.UrnScreening

@[expose] public section

/-!
# The finite small-window calculation in HLOZ Proposition 4.9

This file isolates the finite calculation used after conditioning in
Hao--Li--Okada--Zheng, Proposition 4.9.  The random-walk argument supplies a
positive reference mass and uniform local estimates for the negative-binomial
mass on two adjacent windows.  Here we prove, with all such inputs explicit,
that

* the mass of a window is bounded by its cardinality times its pointwise bound;
* a window of at least `f` lattice points and pointwise mass at least `b` has
  mass at least `f * b`;
* consequently a small window of at most `g` lattice points has conditional
  proportion at most `C * g / f` inside the union of the two windows;
* for at most `J` conditionally independent candidates, the probability that
  at least one enters the small window is at most `C * g * J / f`.

No random-walk estimate is asserted here.  In particular, the hypotheses
called `hsmall` and `hlarge` below are precisely the local/moderate-deviation
inputs which the full proof must establish after conditioning on the external
walk.  The mass is the genuine HLOZ negative-binomial mass developed in
`NegativeBinomial.lean`, and the final finite probability estimate is the
binomial urn calculation from `UrnScreening.lean`.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal ProbabilityTheory unitInterval

namespace Erdos1165.SmallWindow

open NegativeBinomial UrnScreening

/-- Total HLOZ negative-binomial mass of a finite set of internal local-time
values. -/
noncomputable def windowMass (i : ℕ) (window : Finset ℕ) : ℝ :=
  ∑ j ∈ window, hlozMass i j

lemma windowMass_nonneg (i : ℕ) (window : Finset ℕ) :
    0 ≤ windowMass i window := by
  exact Finset.sum_nonneg fun j _ ↦ hlozMass_nonneg i j

/-- A pointwise upper bound sums to a cardinality upper bound. -/
lemma windowMass_le_card_mul {i : ℕ} {window : Finset ℕ} {u : ℝ}
    (hpoint : ∀ j ∈ window, hlozMass i j ≤ u) :
    windowMass i window ≤ window.card * u := by
  unfold windowMass
  calc
    ∑ j ∈ window, hlozMass i j ≤ ∑ _j ∈ window, u :=
      Finset.sum_le_sum fun j hj ↦ hpoint j hj
    _ = window.card * u := by simp

/-- A pointwise lower bound sums to a cardinality lower bound. -/
lemma card_mul_le_windowMass {i : ℕ} {window : Finset ℕ} {l : ℝ}
    (hpoint : ∀ j ∈ window, l ≤ hlozMass i j) :
    window.card * l ≤ windowMass i window := by
  unfold windowMass
  calc
    window.card * l = ∑ _j ∈ window, l := by simp
    _ ≤ ∑ j ∈ window, hlozMass i j :=
      Finset.sum_le_sum fun j hj ↦ hpoint j hj

/-- A nonempty finite window has strictly positive HLOZ mass whenever the
number `i` of successes is positive. -/
lemma windowMass_pos {i : ℕ} (hi : 0 < i) {window : Finset ℕ}
    (hwindow : window.Nonempty) :
    0 < windowMass i window := by
  obtain ⟨j, hj⟩ := hwindow
  have hterm : 0 < hlozMass i j := hlozMass_pos hi j
  have hrest : 0 ≤ ∑ x ∈ window.erase j, hlozMass i x :=
    Finset.sum_nonneg fun x _ ↦ hlozMass_nonneg i x
  rw [windowMass, ← Finset.sum_erase_add _ _ hj]
  linarith

/-- Mass is additive on disjoint windows.  This identifies the denominator in
the paper, which is the mass of the full window, with the sum of the small
window and its comparison buffer. -/
lemma windowMass_union {i : ℕ} {small large : Finset ℕ}
    (hdisjoint : Disjoint small large) :
    windowMass i (small ∪ large) = windowMass i small + windowMass i large := by
  simp only [windowMass]
  exact Finset.sum_union hdisjoint

/-- The deterministic mass comparison behind Proposition 4.9.

Every point of `small` has mass at most `C * b`, every point of `large` has
mass at least `b`, the small window has at most `g` lattice points, and the
large comparison window has at least `f` lattice points.  The conclusion is
the exact unnormalized bound needed for the urn calculation. -/
theorem windowMass_small_le_ratio_mul_large {i : ℕ}
    {small large : Finset ℕ} {b C g f : ℝ}
    (hb : 0 < b) (hC : 0 ≤ C) (hg : 0 ≤ g) (hf : 0 < f)
    (hsmallCard : (small.card : ℝ) ≤ g)
    (hlargeCard : f ≤ (large.card : ℝ))
    (hsmall : ∀ j ∈ small, hlozMass i j ≤ C * b)
    (hlarge : ∀ j ∈ large, b ≤ hlozMass i j) :
    windowMass i small ≤ (C * g / f) * windowMass i large := by
  have hsmallMass : windowMass i small ≤ (small.card : ℝ) * (C * b) :=
    windowMass_le_card_mul hsmall
  have hsmallScale : (small.card : ℝ) * (C * b) ≤ C * g * b := by
    calc
      (small.card : ℝ) * (C * b) ≤ g * (C * b) :=
        mul_le_mul_of_nonneg_right hsmallCard (mul_nonneg hC hb.le)
      _ = C * g * b := by ring
  have hlargeMass : (large.card : ℝ) * b ≤ windowMass i large :=
    card_mul_le_windowMass hlarge
  have hlargeScale : f * b ≤ windowMass i large := by
    exact (mul_le_mul_of_nonneg_right hlargeCard hb.le).trans hlargeMass
  calc
    windowMass i small ≤ C * g * b := hsmallMass.trans hsmallScale
    _ ≤ (C * g / f) * windowMass i large := by
      calc
        C * g * b = (C * g / f) * (f * b) := by
          field_simp
        _ ≤ (C * g / f) * windowMass i large :=
          mul_le_mul_of_nonneg_left hlargeScale
            (div_nonneg (mul_nonneg hC hg) hf.le)

/-- Conditional small-window proportion inside `small ∪ large`.  This is the
finite ratio conclusion of HLOZ Proposition 4.9, separated from every
random-walk input. -/
theorem windowMass_small_conditional_ratio {i : ℕ} (hi : 0 < i)
    {small large : Finset ℕ} {b C g f : ℝ}
    (hb : 0 < b) (hC : 0 ≤ C) (hg : 0 ≤ g) (hf : 0 < f)
    (hsmallCard : (small.card : ℝ) ≤ g)
    (hlargeCard : f ≤ (large.card : ℝ))
    (hsmall : ∀ j ∈ small, hlozMass i j ≤ C * b)
    (hlarge : ∀ j ∈ large, b ≤ hlozMass i j) :
    windowMass i small / (windowMass i small + windowMass i large) ≤ C * g / f := by
  have hlargeNonempty : large.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    subst large
    simp at hlargeCard
    linarith
  have hsmallNonneg := windowMass_nonneg i small
  have hlargePos := windowMass_pos hi hlargeNonempty
  have hmass := windowMass_small_le_ratio_mul_large hb hC hg hf hsmallCard
    hlargeCard hsmall hlarge
  rw [div_le_iff₀ (add_pos_of_nonneg_of_pos hsmallNonneg hlargePos)]
  nlinarith [mul_nonneg (div_nonneg (mul_nonneg hC hg) hf.le) hsmallNonneg]

/-- The ratio in the literal form used in HLOZ (4.58): the denominator is the
mass of the entire large window, presented as a disjoint union of the small
window and its comparison buffer. -/
theorem windowMass_small_div_union_le {i : ℕ} (hi : 0 < i)
    {small large : Finset ℕ} {b C g f : ℝ}
    (hdisjoint : Disjoint small large)
    (hb : 0 < b) (hC : 0 ≤ C) (hg : 0 ≤ g) (hf : 0 < f)
    (hsmallCard : (small.card : ℝ) ≤ g)
    (hlargeCard : f ≤ (large.card : ℝ))
    (hsmall : ∀ j ∈ small, hlozMass i j ≤ C * b)
    (hlarge : ∀ j ∈ large, b ≤ hlozMass i j) :
    windowMass i small / windowMass i (small ∪ large) ≤ C * g / f := by
  rw [windowMass_union hdisjoint]
  exact windowMass_small_conditional_ratio hi hb hC hg hf hsmallCard hlargeCard
    hsmall hlarge

/-- **Heterogeneous finite union form of Proposition 4.9's last step.**

Different candidate sites may have different external counts `successes x`,
different shifted integer windows, and different positive reference masses.
If all their exact negative-binomial conditional ratios satisfy the same
cardinality/local-mass hypotheses, then finite subadditivity costs only the
candidate budget `J`.  Independence is not needed for this last implication.
-/
theorem heterogeneous_smallWindow_union_le
    {Omega Candidate : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) (candidates : Finset Candidate)
    (near : Candidate → Set Omega) (successes : Candidate → ℕ)
    (small large : Candidate → Finset ℕ) (reference : Candidate → ℝ)
    {J : ℕ} {C g f : ℝ}
    (hcard : candidates.card ≤ J)
    (hC : 0 ≤ C) (hg : 0 ≤ g) (hf : 0 < f)
    (hsuccesses : ∀ x ∈ candidates, 0 < successes x)
    (href : ∀ x ∈ candidates, 0 < reference x)
    (hdisjoint : ∀ x ∈ candidates, Disjoint (small x) (large x))
    (hsmallCard : ∀ x ∈ candidates, ((small x).card : ℝ) ≤ g)
    (hlargeCard : ∀ x ∈ candidates, f ≤ ((large x).card : ℝ))
    (hsmall : ∀ x ∈ candidates, ∀ j ∈ small x,
      hlozMass (successes x) j ≤ C * reference x)
    (hlarge : ∀ x ∈ candidates, ∀ j ∈ large x,
      reference x ≤ hlozMass (successes x) j)
    (hnear : ∀ x ∈ candidates,
      mu.real (near x) ≤
        windowMass (successes x) (small x) /
          windowMass (successes x) (small x ∪ large x)) :
    mu.real {omega | ∃ x ∈ candidates, omega ∈ near x} ≤ C * g * J / f := by
  have hq : 0 ≤ C * g / f := div_nonneg (mul_nonneg hC hg) hf.le
  have hone (x : Candidate) (hx : x ∈ candidates) :
      mu.real (near x) ≤ C * g / f := by
    exact (hnear x hx).trans
      (windowMass_small_div_union_le (hsuccesses x hx) (hdisjoint x hx)
        (href x hx) hC hg hf (hsmallCard x hx) (hlargeCard x hx)
        (hsmall x hx) (hlarge x hx))
  rw [show {omega | ∃ x ∈ candidates, omega ∈ near x} =
      ⋃ x ∈ candidates, near x by ext omega; simp]
  calc
    mu.real (⋃ x ∈ candidates, near x) ≤
        ∑ x ∈ candidates, mu.real (near x) :=
      measureReal_biUnion_finset_le candidates near
    _ ≤ ∑ _x ∈ candidates, C * g / f :=
      Finset.sum_le_sum fun x hx ↦ hone x hx
    _ = (candidates.card : ℝ) * (C * g / f) := by simp
    _ ≤ (J : ℝ) * (C * g / f) := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hq
    _ = C * g * J / f := by ring

/-- The conditional small-window parameter as an element of `[0,1]`. -/
noncomputable def smallWindowParameter (i : ℕ) (small large : Finset ℕ)
    (hlarge : 0 < windowMass i large) : I :=
  pairParameter (windowMass i small) (windowMass i large)
    (windowMass_nonneg i small) hlarge.le
    (add_pos_of_nonneg_of_pos (windowMass_nonneg i small) hlarge)

@[simp] lemma coe_smallWindowParameter (i : ℕ) (small large : Finset ℕ)
    (hlarge : 0 < windowMass i large) :
    ((smallWindowParameter i small large hlarge : I) : ℝ) =
      windowMass i small / (windowMass i small + windowMass i large) := rfl

/-- The ratio hypotheses give the corresponding bound on the unit-interval
parameter used by the binomial conditional law. -/
theorem smallWindowParameter_le {i : ℕ} (hi : 0 < i)
    {small large : Finset ℕ} {b C g f : ℝ}
    (hb : 0 < b) (hC : 0 ≤ C) (hg : 0 ≤ g) (hf : 0 < f)
    (hsmallCard : (small.card : ℝ) ≤ g)
    (hlargeCard : f ≤ (large.card : ℝ))
    (hsmall : ∀ j ∈ small, hlozMass i j ≤ C * b)
    (hlarge : ∀ j ∈ large, b ≤ hlozMass i j) :
    let hlargePos : 0 < windowMass i large := by
      apply windowMass_pos hi
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      subst large
      simp at hlargeCard
      linarith
    ((smallWindowParameter i small large hlargePos : I) : ℝ) ≤ C * g / f := by
  dsimp only
  exact windowMass_small_conditional_ratio hi hb hC hg hf hsmallCard hlargeCard
    hsmall hlarge

/-- Exact finite union bound for the Proposition 4.9 conditional model.

After conditioning, suppose `n ≤ J` candidates independently select the
small window with the parameter obtained from the negative-binomial window
masses.  Then the probability that at least one is selected is bounded by
`C * g * J / f`.  The theorem does not claim that a random-walk conditioning
has this binomial law; that is an explicit upstream obligation. -/
theorem smallWindow_one_or_more_le {i n J : ℕ} (hi : 0 < i)
    {small large : Finset ℕ} {b C g f : ℝ}
    (hnJ : n ≤ J) (hb : 0 < b) (hC : 0 ≤ C) (hg : 0 ≤ g) (hf : 0 < f)
    (hsmallCard : (small.card : ℝ) ≤ g)
    (hlargeCard : f ≤ (large.card : ℝ))
    (hsmall : ∀ j ∈ small, hlozMass i j ≤ C * b)
    (hlarge : ∀ j ∈ large, b ≤ hlozMass i j) :
    let hlargePos : 0 < windowMass i large := by
      apply windowMass_pos hi
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      subst large
      simp at hlargeCard
      linarith
    Bin(n, smallWindowParameter i small large hlargePos).real (Set.Ici 1) ≤
      C * g * J / f := by
  dsimp only
  apply binomial_one_or_more_le
  · exact hnJ
  · exact hC
  · exact hg
  · exact hf
  · exact windowMass_small_conditional_ratio hi hb hC hg hf hsmallCard hlargeCard
      hsmall hlarge

/-- Singleton-count version of `smallWindow_one_or_more_le`: the chance of
exactly `j` selected candidates is bounded by `(C * g * J / f)^j`. -/
theorem smallWindow_exactly_le {i n J j : ℕ} (hi : 0 < i)
    {small large : Finset ℕ} {b C g f : ℝ}
    (hnJ : n ≤ J) (hb : 0 < b) (hC : 0 ≤ C) (hg : 0 ≤ g) (hf : 0 < f)
    (hsmallCard : (small.card : ℝ) ≤ g)
    (hlargeCard : f ≤ (large.card : ℝ))
    (hsmall : ∀ a ∈ small, hlozMass i a ≤ C * b)
    (hlarge : ∀ a ∈ large, b ≤ hlozMass i a) :
    let hlargePos : 0 < windowMass i large := by
      apply windowMass_pos hi
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      subst large
      simp at hlargeCard
      linarith
    Bin(n, smallWindowParameter i small large hlargePos).real {j} ≤
      (C * g * J / f) ^ j := by
  dsimp only
  apply two_window_urn_screening
  · exact hnJ
  · exact hC
  · exact hg
  · exact hf
  · exact windowMass_small_conditional_ratio hi hb hC hg hf hsmallCard hlargeCard
      hsmall hlarge

end Erdos1165.SmallWindow
