import Mathlib
import ErdosProblems.Erdos920.Averaging

/-!
# Finite probability tools for Erdős Problem 88

This file packages the elementary probability calculations used in the
reduction in Sections 2--3 of Kwan--Sah--Sauermann--Sawhney.  All expectations
are explicit finite sums over a powerset.  In particular, none of the results
below uses an ambient measure space or any asymptotic input.

The principal outputs are:

* the Bernoulli product probability on finite vertex sets;
* exact expectations of Boolean monomials and induced edge counts;
* the Boolean-polynomial and Fourier--Walsh expansions of an induced edge
  count with a linear perturbation;
* orthogonality, covariance cancellation, and exact variance identities;
* finite-sum Markov/Chebyshev and exponential (Chernoff) bounds; and
* the `|V|^3` variance bound for an induced edge count.
-/

open scoped BigOperators

namespace Erdos88
namespace Probability

open Classical

section FiniteProduct

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Bernoulli product weight of a subset of a finite type. -/
noncomputable def bernoulliWeight (p : ℝ) (W : Finset V) : ℝ :=
  Erdos202.ParkPham.bernoulliMass Finset.univ W p

/-- Expectation in the finite Bernoulli product model. -/
noncomputable def expectation (p : ℝ) (f : Finset V → ℝ) : ℝ :=
  ∑ W : Finset V, bernoulliWeight p W * f W

/-- Probability (as an explicit finite sum) of an event. -/
noncomputable def probability (p : ℝ) (A : Finset (Finset V)) : ℝ :=
  ∑ W ∈ A, bernoulliWeight p W

/-- Variance in the finite Bernoulli product model. -/
noncomputable def variance (p : ℝ) (f : Finset V → ℝ) : ℝ :=
  expectation p fun W => (f W - expectation p f) ^ 2

/-- Covariance in the finite Bernoulli product model. -/
noncomputable def covariance (p : ℝ) (f g : Finset V → ℝ) : ℝ :=
  expectation p fun W =>
    (f W - expectation p f) * (g W - expectation p g)

/-- The `0`--`1` coordinate attached to a vertex. -/
def bit (v : V) (W : Finset V) : ℝ := if v ∈ W then 1 else 0

/-- The `{-1,1}` coordinate attached to a vertex. -/
def sign (v : V) (W : Finset V) : ℝ := if v ∈ W then 1 else -1

/-- A Boolean monomial, written as the indicator that `T ⊆ W`. -/
def monomial (T W : Finset V) : ℝ := if T ⊆ W then 1 else 0

/-- A Walsh character on the discrete cube. -/
def walsh (T W : Finset V) : ℝ := ∏ v ∈ T, sign v W

@[simp] lemma monomial_empty (W : Finset V) : monomial ∅ W = 1 := by
  simp [monomial]

@[simp] lemma walsh_empty (W : Finset V) : walsh ∅ W = 1 := by
  simp [walsh]

lemma monomial_eq_prod_bit (T W : Finset V) :
    monomial T W = ∏ v ∈ T, bit v W := by
  classical
  by_cases h : T ⊆ W
  · rw [monomial, if_pos h]
    symm
    apply Finset.prod_eq_one
    intro v hv
    simp [bit, h hv]
  · obtain ⟨v, hvT, hvW⟩ := Finset.not_subset.mp h
    rw [monomial, if_neg h]
    exact (Finset.prod_eq_zero hvT (by simp [bit, hvW])).symm

lemma sum_univ_eq_sum_powerset (f : Finset V → ℝ) :
    (∑ W : Finset V, f W) = ∑ W ∈ (Finset.univ : Finset V).powerset, f W := by
  simp

lemma sum_bernoulliWeight (p : ℝ) :
    ∑ W : Finset V, bernoulliWeight p W = 1 := by
  rw [sum_univ_eq_sum_powerset]
  simpa [bernoulliWeight] using
    (Erdos202.ParkPham.sum_bernoulliMass_eq_one
      (X := (Finset.univ : Finset V)) (p := p) (by ring))

lemma bernoulliWeight_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (W : Finset V) : 0 ≤ bernoulliWeight p W := by
  exact Erdos202.ParkPham.bernoulliMass_nonneg hp0 hp1

@[simp] lemma expectation_const (p c : ℝ) :
    expectation (V := V) p (fun _ => c) = c := by
  simp [expectation, ← Finset.sum_mul, sum_bernoulliWeight]

lemma expectation_add (p : ℝ) (f g : Finset V → ℝ) :
    expectation p (fun W => f W + g W) = expectation p f + expectation p g := by
  simp [expectation, mul_add, Finset.sum_add_distrib]

lemma expectation_sub (p : ℝ) (f g : Finset V → ℝ) :
    expectation p (fun W => f W - g W) = expectation p f - expectation p g := by
  simp [expectation, mul_sub, Finset.sum_sub_distrib]

lemma expectation_smul (p c : ℝ) (f : Finset V → ℝ) :
    expectation p (fun W => c * f W) = c * expectation p f := by
  unfold expectation
  calc
    (∑ W : Finset V, bernoulliWeight p W * (c * f W)) =
        ∑ W : Finset V, c * (bernoulliWeight p W * f W) := by
      apply Finset.sum_congr rfl
      intro W hW
      ring
    _ = c * ∑ W : Finset V, bernoulliWeight p W * f W := by
      rw [Finset.mul_sum]

lemma expectation_sum {I : Type*} (p : ℝ) (s : Finset I)
    (f : I → Finset V → ℝ) :
    expectation p (fun W => ∑ i ∈ s, f i W) =
      ∑ i ∈ s, expectation p (f i) := by
  classical
  unfold expectation
  calc
    (∑ W : Finset V, bernoulliWeight p W * ∑ i ∈ s, f i W) =
        ∑ W : Finset V, ∑ i ∈ s, bernoulliWeight p W * f i W := by
          apply Finset.sum_congr rfl
          intro W hW
          rw [Finset.mul_sum]
    _ = ∑ i ∈ s, ∑ W : Finset V, bernoulliWeight p W * f i W := by
          rw [Finset.sum_comm]

lemma expectation_monomial {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (T : Finset V) : expectation p (monomial T) = p ^ T.card := by
  rw [expectation, sum_univ_eq_sum_powerset]
  simpa [bernoulliWeight, monomial] using
    (Erdos920.sum_bernoulliMass_indicator_superset
      (X := (Finset.univ : Finset V)) T (by simp) hp0 hp1)

@[simp] lemma expectation_bit {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (v : V) : expectation p (bit v) = p := by
  have hfun : bit v = monomial ({v} : Finset V) := by
    funext W
    simp [monomial, bit]
  rw [hfun, expectation_monomial hp0 hp1]
  simp

/-- The product-over-powerset factorization behind finite product measures. -/
lemma sum_prod_ite_mem (X : Finset V) (a b : V → ℝ) :
    (∑ W ∈ X.powerset, ∏ v ∈ X, if v ∈ W then a v else b v) =
      ∏ v ∈ X, (a v + b v) := by
  classical
  induction X using Finset.induction_on with
  | empty => simp
  | @insert x X hx ih =>
      rw [Finset.sum_powerset_insert hx]
      have hfirst :
          (∑ W ∈ X.powerset,
              ∏ v ∈ insert x X, if v ∈ W then a v else b v) =
            b x * ∑ W ∈ X.powerset,
              ∏ v ∈ X, if v ∈ W then a v else b v := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro W hW
        rw [Finset.prod_insert hx]
        have hxW : x ∉ W :=
          Finset.notMem_mono (Finset.mem_powerset.mp hW) hx
        simp [hxW]
      have hsecond :
          (∑ W ∈ X.powerset,
              ∏ v ∈ insert x X, if v ∈ insert x W then a v else b v) =
            a x * ∑ W ∈ X.powerset,
              ∏ v ∈ X, if v ∈ W then a v else b v := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro W hW
        rw [Finset.prod_insert hx]
        simp only [Finset.mem_insert, true_or, if_true]
        congr 1
        apply Finset.prod_congr rfl
        intro v hv
        have hvx : v ≠ x := fun h => hx (h ▸ hv)
        simp [hvx]
      rw [hfirst, hsecond, ih, Finset.prod_insert hx]
      ring

lemma prod_ite_const_of_subset {X W : Finset V} (hWX : W ⊆ X) (a b : ℝ) :
    (∏ v ∈ X, if v ∈ W then a else b) =
      a ^ W.card * b ^ (X.card - W.card) := by
  classical
  rw [Finset.prod_ite]
  have hfilter : X.filter (fun v => v ∈ W) = W := by
    ext v
    simp only [Finset.mem_filter]
    constructor
    · exact And.right
    · intro hv
      exact ⟨hWX hv, hv⟩
  have hfilterc : X.filter (fun v => ¬v ∈ W) = X \ W := by
    ext v
    simp
  rw [hfilter, hfilterc]
  simp only [Finset.prod_const]
  rw [Finset.card_sdiff_of_subset hWX]

/-- Exact moment-generating function of the sample size. -/
lemma expectation_exp_card (p t : ℝ) :
    expectation (V := V) p (fun W => Real.exp (t * W.card)) =
      (1 - p + p * Real.exp t) ^ Fintype.card V := by
  rw [expectation, sum_univ_eq_sum_powerset]
  simp only [bernoulliWeight, Erdos202.ParkPham.bernoulliMass]
  calc
    (∑ W ∈ (Finset.univ : Finset V).powerset,
        p ^ W.card * (1 - p) ^ (Finset.univ.card - W.card) *
          Real.exp (t * W.card)) =
        ∑ W ∈ (Finset.univ : Finset V).powerset,
          ∏ v ∈ (Finset.univ : Finset V),
            if v ∈ W then p * Real.exp t else 1 - p := by
      apply Finset.sum_congr rfl
      intro W hW
      have hWU : W ⊆ (Finset.univ : Finset V) := Finset.mem_powerset.mp hW
      rw [prod_ite_const_of_subset hWU]
      rw [show t * (W.card : ℝ) = (W.card : ℝ) * t by ring,
        Real.exp_nat_mul, mul_pow]
      ring
    _ = ∏ v ∈ (Finset.univ : Finset V),
          ((p * Real.exp t) + (1 - p)) :=
      sum_prod_ite_mem (X := (Finset.univ : Finset V))
        (a := fun _ => p * Real.exp t) (b := fun _ => 1 - p)
    _ = (1 - p + p * Real.exp t) ^ Fintype.card V := by
      simp [add_comm]

/-- Variance is the second moment minus the square of the first moment. -/
lemma variance_eq_expectation_sq_sub (p : ℝ) (f : Finset V → ℝ) :
    variance p f = expectation p (fun W => f W ^ 2) - (expectation p f) ^ 2 := by
  unfold variance
  have hfun : (fun W => (f W - expectation p f) ^ 2) =
      (fun W => f W ^ 2 - (2 * expectation p f) * f W +
        (expectation p f) ^ 2) := by
    funext W
    ring
  rw [hfun, expectation_add, expectation_sub,
    expectation_smul, expectation_const]
  ring

/-- Covariance is the mixed second moment minus the product of means. -/
lemma covariance_eq_expectation_mul_sub (p : ℝ) (f g : Finset V → ℝ) :
    covariance p f g =
      expectation p (fun W => f W * g W) - expectation p f * expectation p g := by
  unfold covariance
  have hfun :
      (fun W => (f W - expectation p f) * (g W - expectation p g)) =
        (fun W => f W * g W - (expectation p g) * f W -
          (expectation p f) * g W + expectation p f * expectation p g) := by
    funext W
    ring
  rw [hfun, expectation_add, expectation_sub, expectation_sub,
    expectation_smul, expectation_smul, expectation_const]
  ring

lemma monomial_mul (A B W : Finset V) :
    monomial A W * monomial B W = monomial (A ∪ B) W := by
  by_cases hA : A ⊆ W <;> by_cases hB : B ⊆ W <;>
    simp [monomial, hA, hB, Finset.union_subset_iff]

lemma expectation_monomial_mul {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (A B : Finset V) :
    expectation p (fun W => monomial A W * monomial B W) = p ^ (A ∪ B).card := by
  simp_rw [monomial_mul]
  exact expectation_monomial hp0 hp1 (A ∪ B)

lemma covariance_monomial {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (A B : Finset V) :
    covariance p (monomial A) (monomial B) =
      p ^ (A ∪ B).card - p ^ A.card * p ^ B.card := by
  rw [covariance_eq_expectation_mul_sub,
    expectation_monomial_mul hp0 hp1,
    expectation_monomial hp0 hp1, expectation_monomial hp0 hp1]

lemma covariance_monomial_eq_zero_of_disjoint {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {A B : Finset V} (hAB : Disjoint A B) :
    covariance p (monomial A) (monomial B) = 0 := by
  rw [covariance_monomial hp0 hp1, Finset.card_union_of_disjoint hAB, pow_add]
  ring

/-- Probability of a predicate in the explicit finite Bernoulli model. -/
noncomputable def eventProbability (p : ℝ) (P : Finset V → Prop)
    [DecidablePred P] : ℝ :=
  expectation p fun W => if P W then 1 else 0

lemma eventProbability_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (P : Finset V → Prop) [DecidablePred P] :
    0 ≤ eventProbability p P := by
  unfold eventProbability expectation
  apply Finset.sum_nonneg
  intro W hW
  exact mul_nonneg (bernoulliWeight_nonneg hp0 hp1 W) (by positivity)

/-- Monotonicity of the explicit finite Bernoulli event probability. -/
lemma eventProbability_mono {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {P Q : Finset V → Prop} [DecidablePred P] [DecidablePred Q]
    (hPQ : ∀ W, P W → Q W) :
    eventProbability p P ≤ eventProbability p Q := by
  unfold eventProbability expectation
  apply Finset.sum_le_sum
  intro W hW
  apply mul_le_mul_of_nonneg_left _ (bernoulliWeight_nonneg hp0 hp1 W)
  change (if P W then 1 else 0) ≤ (if Q W then 1 else 0)
  by_cases hP : P W
  · rw [if_pos hP, if_pos (hPQ W hP)]
  · simp only [hP, if_false]
    positivity

/-- Markov's inequality for an explicit finite probability mass function. -/
lemma markov_bound {p a : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ha : 0 < a)
    (Y : Finset V → ℝ) (hY : ∀ W, 0 ≤ Y W) :
    eventProbability p (fun W => a ≤ Y W) ≤ expectation p Y / a := by
  unfold eventProbability expectation
  apply (le_div_iff₀ ha).mpr
  rw [mul_comm]
  calc
    a * ∑ W : Finset V,
        bernoulliWeight p W * (if a ≤ Y W then 1 else 0) =
        ∑ W : Finset V,
          a * (bernoulliWeight p W * (if a ≤ Y W then 1 else 0)) := by
      rw [Finset.mul_sum]
    _ ≤ ∑ W : Finset V, bernoulliWeight p W * Y W := by
      apply Finset.sum_le_sum
      intro W hW
      have hw := bernoulliWeight_nonneg hp0 hp1 W
      by_cases h : a ≤ Y W
      · simp [h]
        simpa [mul_comm] using mul_le_mul_of_nonneg_left h hw
      · simp [h, mul_nonneg hw (hY W)]

/-- Chebyshev's inequality, in the squared-deviation form used in KSSS. -/
lemma chebyshev_sq_bound {p t : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ht : 0 < t)
    (f : Finset V → ℝ) :
    eventProbability p
        (fun W => t ^ 2 ≤ (f W - expectation p f) ^ 2) ≤
      variance p f / t ^ 2 := by
  exact markov_bound hp0 hp1 (sq_pos_of_pos ht)
    (fun W => (f W - expectation p f) ^ 2) (fun W => sq_nonneg _)

end FiniteProduct

section GraphPolynomial

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Number of edges of `G` whose two endpoints lie in `W`. -/
def inducedEdgeCount (W : Finset V) : ℕ :=
  (G.edgeFinset.filter fun e => e.toFinset ⊆ W).card

/-- The real Boolean polynomial counting induced edges. -/
def edgePolynomial (W : Finset V) : ℝ :=
  ∑ e ∈ G.edgeFinset, monomial e.toFinset W

lemma edgePolynomial_eq_inducedEdgeCount (W : Finset V) :
    edgePolynomial G W = inducedEdgeCount G W := by
  classical
  unfold edgePolynomial inducedEdgeCount
  rw [Finset.card_filter]
  simp [monomial]

lemma edgePolynomial_eq_sum_prod_bit (W : Finset V) :
    edgePolynomial G W =
      ∑ e ∈ G.edgeFinset, ∏ v ∈ e.toFinset, bit v W := by
  apply Finset.sum_congr rfl
  intro e he
  exact monomial_eq_prod_bit e.toFinset W

lemma expectation_edgePolynomial {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    expectation p (edgePolynomial G) = p ^ 2 * G.edgeFinset.card := by
  unfold edgePolynomial
  rw [expectation_sum]
  calc
    (∑ e ∈ G.edgeFinset, expectation p (monomial e.toFinset)) =
        ∑ _e ∈ G.edgeFinset, p ^ 2 := by
      apply Finset.sum_congr rfl
      intro e he
      rw [expectation_monomial hp0 hp1]
      rw [SimpleGraph.card_toFinset_mem_edgeFinset ⟨e, he⟩]
    _ = p ^ 2 * G.edgeFinset.card := by simp [mul_comm]

lemma edgePolynomial_sq (W : Finset V) :
    edgePolynomial G W ^ 2 =
      ∑ e ∈ G.edgeFinset, ∑ f ∈ G.edgeFinset,
        monomial e.toFinset W * monomial f.toFinset W := by
  unfold edgePolynomial
  rw [pow_two, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e he
  rw [Finset.mul_sum]

lemma expectation_edgePolynomial_sq {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    expectation p (fun W => edgePolynomial G W ^ 2) =
      ∑ e ∈ G.edgeFinset, ∑ f ∈ G.edgeFinset,
        p ^ (e.toFinset ∪ f.toFinset).card := by
  have hfun : (fun W => edgePolynomial G W ^ 2) =
      (fun W => ∑ e ∈ G.edgeFinset, ∑ f ∈ G.edgeFinset,
        monomial e.toFinset W * monomial f.toFinset W) := by
    funext W
    exact edgePolynomial_sq G W
  rw [hfun, expectation_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [expectation_sum]
  apply Finset.sum_congr rfl
  intro f hf
  exact expectation_monomial_mul hp0 hp1 e.toFinset f.toFinset

/-- Exact covariance-sum formula for the induced edge count. -/
lemma variance_edgePolynomial {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    variance p (edgePolynomial G) =
      ∑ e ∈ G.edgeFinset, ∑ f ∈ G.edgeFinset,
        (p ^ (e.toFinset ∪ f.toFinset).card - p ^ 4) := by
  rw [variance_eq_expectation_sq_sub,
    expectation_edgePolynomial_sq G hp0 hp1,
    expectation_edgePolynomial G hp0 hp1]
  have hconst :
      (p ^ 2 * (G.edgeFinset.card : ℝ)) ^ 2 =
        ∑ _e ∈ G.edgeFinset, ∑ _f ∈ G.edgeFinset, p ^ 4 := by
    simp
    push_cast
    ring
  rw [hconst]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e he
  rw [← Finset.sum_sub_distrib]

/-- Ordered pairs of graph edges which share at least one endpoint. -/
def intersectingEdgePairs : Finset (Sym2 V × Sym2 V) :=
  (G.edgeFinset ×ˢ G.edgeFinset).filter fun ef =>
    ¬ Disjoint ef.1.toFinset ef.2.toFinset

lemma intersectingEdgePairs_subset_incidence_union :
    intersectingEdgePairs G ⊆
      (Finset.univ : Finset V).biUnion (fun v =>
        G.incidenceFinset v ×ˢ G.incidenceFinset v) := by
  intro ef hef
  rcases Finset.mem_filter.mp hef with ⟨hefprod, hnotdisj⟩
  rcases Finset.mem_product.mp hefprod with ⟨he, hf⟩
  obtain ⟨v, hve, hvf⟩ := Finset.not_disjoint_iff.mp hnotdisj
  rw [Finset.mem_biUnion]
  refine ⟨v, Finset.mem_univ v, Finset.mem_product.mpr ⟨?_, ?_⟩⟩
  · rw [G.mem_incidenceFinset]
    exact (G.edge_mem_incidenceSet_iff
      (e := ⟨ef.1, SimpleGraph.mem_edgeFinset.mp he⟩)).2
        (Sym2.mem_toFinset.mp hve)
  · rw [G.mem_incidenceFinset]
    exact (G.edge_mem_incidenceSet_iff
      (e := ⟨ef.2, SimpleGraph.mem_edgeFinset.mp hf⟩)).2
        (Sym2.mem_toFinset.mp hvf)

/-- There are at most `|V|^3` ordered intersecting edge pairs. -/
lemma card_intersectingEdgePairs_le_cube :
    (intersectingEdgePairs G).card ≤ Fintype.card V ^ 3 := by
  calc
    (intersectingEdgePairs G).card ≤
        ((Finset.univ : Finset V).biUnion (fun v =>
          G.incidenceFinset v ×ˢ G.incidenceFinset v)).card :=
      Finset.card_le_card (intersectingEdgePairs_subset_incidence_union G)
    _ ≤ ∑ v : V, (G.incidenceFinset v ×ˢ G.incidenceFinset v).card :=
      Finset.card_biUnion_le
    _ = ∑ v : V, G.degree v * G.degree v := by
      apply Finset.sum_congr rfl
      intro v hv
      simp [Finset.card_product]
    _ ≤ ∑ _v : V, Fintype.card V * Fintype.card V := by
      apply Finset.sum_le_sum
      intro v hv
      exact Nat.mul_le_mul (Nat.le_of_lt (G.degree_lt_card_verts v))
        (Nat.le_of_lt (G.degree_lt_card_verts v))
    _ = Fintype.card V ^ 3 := by
      simp [pow_succ, mul_assoc]

lemma sum_intersecting_indicator :
    (∑ e ∈ G.edgeFinset, ∑ f ∈ G.edgeFinset,
      if ¬ Disjoint e.toFinset f.toFinset then (1 : ℝ) else 0) =
      (intersectingEdgePairs G).card := by
  simpa [intersectingEdgePairs, Finset.sum_product] using
    (Finset.sum_boole
      (R := ℝ)
      (fun ef : Sym2 V × Sym2 V =>
        ¬ Disjoint ef.1.toFinset ef.2.toFinset)
      (G.edgeFinset ×ˢ G.edgeFinset))

/-- The elementary estimate used in (4.9): the variance is at most `|V|^3`. -/
lemma variance_edgePolynomial_le_cube {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    variance p (edgePolynomial G) ≤ (Fintype.card V : ℝ) ^ 3 := by
  rw [variance_edgePolynomial G hp0 hp1]
  calc
    (∑ e ∈ G.edgeFinset, ∑ f ∈ G.edgeFinset,
        (p ^ (e.toFinset ∪ f.toFinset).card - p ^ 4)) ≤
        ∑ e ∈ G.edgeFinset, ∑ f ∈ G.edgeFinset,
          if ¬ Disjoint e.toFinset f.toFinset then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro e he
      apply Finset.sum_le_sum
      intro f hf
      by_cases hdisj : Disjoint e.toFinset f.toFinset
      · simp only [hdisj, not_true_eq_false, if_false]
        rw [Finset.card_union_of_disjoint hdisj,
          SimpleGraph.card_toFinset_mem_edgeFinset ⟨e, he⟩,
          SimpleGraph.card_toFinset_mem_edgeFinset ⟨f, hf⟩]
        norm_num
      · simp only [hdisj, not_false_eq_true, if_true]
        have hpPow : p ^ (e.toFinset ∪ f.toFinset).card ≤ 1 :=
          pow_le_one₀ hp0 hp1
        have hp4 : 0 ≤ p ^ 4 := pow_nonneg hp0 _
        linarith
    _ = (intersectingEdgePairs G).card := sum_intersecting_indicator G
    _ ≤ (Fintype.card V : ℝ) ^ 3 := by
      exact_mod_cast card_intersectingEdgePairs_le_cube G

/-- A linearly perturbed induced edge count, as in KSSS Theorem 2.1. -/
def perturbedEdgePolynomial (e₀ : ℝ) (c : V → ℝ) (W : Finset V) : ℝ :=
  e₀ + edgePolynomial G W + ∑ v, c v * bit v W

lemma expectation_perturbedEdgePolynomial {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (e₀ : ℝ) (c : V → ℝ) :
    expectation p (perturbedEdgePolynomial G e₀ c) =
      e₀ + p ^ 2 * G.edgeFinset.card + p * ∑ v, c v := by
  unfold perturbedEdgePolynomial
  rw [expectation_add, expectation_add, expectation_const,
    expectation_edgePolynomial G hp0 hp1]
  have hlin : expectation p (fun W => ∑ v, c v * bit v W) =
      p * ∑ v, c v := by
    rw [expectation_sum]
    simp_rw [expectation_smul, expectation_bit hp0 hp1]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v hv
    ring
  rw [hlin]

lemma bit_eq_half_one_add_sign (v : V) (W : Finset V) :
    bit v W = (1 + sign v W) / 2 := by
  by_cases h : v ∈ W <;> simp [bit, sign, h]

lemma edge_monomial_walsh (e : Sym2 V) (he : e ∈ G.edgeFinset) (W : Finset V) :
    monomial e.toFinset W =
      (1 + ∑ v ∈ e.toFinset, sign v W + walsh e.toFinset W) / 4 := by
  classical
  induction e using Sym2.inductionOn with
  | _ u v =>
      have hne : u ≠ v := by
        intro h
        subst v
        exact G.not_isDiag_of_mem_edgeFinset he rfl
      rw [Sym2.toFinset_mk_eq]
      simp only [walsh, monomial_eq_prod_bit, bit_eq_half_one_add_sign]
      simp [hne]
      ring

/-- The centered linear Walsh part of a perturbed edge count. -/
noncomputable def linearWalsh (c : V → ℝ) (W : Finset V) : ℝ :=
  ∑ v, (c v / 2 + (G.degree v : ℝ) / 4) * sign v W

/-- The quadratic Walsh part of an induced edge count. -/
noncomputable def quadraticWalsh (W : Finset V) : ℝ :=
  (1 / 4 : ℝ) * ∑ e ∈ G.edgeFinset, walsh e.toFinset W

/-- Fourier--Walsh decomposition (formula (4.11) in the writeup). -/
lemma perturbedEdgePolynomial_walsh (e₀ : ℝ) (c : V → ℝ) (W : Finset V) :
    perturbedEdgePolynomial G e₀ c W =
      (e₀ + (G.edgeFinset.card : ℝ) / 4 + (∑ v, c v) / 2) +
        linearWalsh G c W + quadraticWalsh G W := by
  classical
  -- Expand every Boolean coordinate and every edge monomial.
  rw [perturbedEdgePolynomial, edgePolynomial]
  simp_rw [bit_eq_half_one_add_sign]
  have hedge :
      (∑ e ∈ G.edgeFinset, monomial e.toFinset W) =
        ∑ e ∈ G.edgeFinset,
          (1 + ∑ v ∈ e.toFinset, sign v W + walsh e.toFinset W) / 4 := by
    apply Finset.sum_congr rfl
    intro e he
    exact edge_monomial_walsh G e he W
  rw [hedge]
  simp only [linearWalsh, quadraticWalsh]
  -- Regroup edge-linear terms by vertices using the degree sum identity.
  have hlinear :
      (∑ e ∈ G.edgeFinset, ∑ v ∈ e.toFinset, sign v W) =
        ∑ v, (G.degree v : ℝ) * sign v W := by
    calc
      (∑ e ∈ G.edgeFinset, ∑ v ∈ e.toFinset, sign v W) =
          ∑ e ∈ G.edgeFinset,
            ∑ v : V, if v ∈ e.toFinset then sign v W else 0 := by
        apply Finset.sum_congr rfl
        intro e he
        rw [← Finset.sum_filter]
        congr 1
        ext v
        simp
      _ = ∑ v : V, ∑ e ∈ G.edgeFinset,
            if v ∈ e.toFinset then sign v W else 0 := by
        rw [Finset.sum_comm]
      _ = ∑ v, (G.degree v : ℝ) * sign v W := by
        apply Finset.sum_congr rfl
        intro v hv
        rw [← Finset.sum_filter]
        simp only [Sym2.mem_toFinset]
        rw [← SimpleGraph.incidenceFinset_eq_filter]
        rw [Finset.sum_const, G.card_incidenceFinset_eq_degree]
        simp [nsmul_eq_mul]
  have hedgeExpand :
      (∑ e ∈ G.edgeFinset,
          (1 + ∑ v ∈ e.toFinset, sign v W + walsh e.toFinset W) / 4) =
        (G.edgeFinset.card : ℝ) / 4 +
          (∑ e ∈ G.edgeFinset, ∑ v ∈ e.toFinset, sign v W) / 4 +
          (∑ e ∈ G.edgeFinset, walsh e.toFinset W) / 4 := by
    simp only [div_eq_mul_inv, add_mul, Finset.sum_add_distrib,
      Finset.sum_const, nsmul_eq_mul]
    push_cast
    rw [Finset.sum_mul, Finset.sum_mul]
    ring
  have hcExpand :
      (∑ v, c v * ((1 + sign v W) / 2)) =
        (∑ v, c v) / 2 + ∑ v, (c v / 2) * sign v W := by
    calc
      (∑ v, c v * ((1 + sign v W) / 2)) =
          ∑ v, (c v / 2 + (c v / 2) * sign v W) := by
        apply Finset.sum_congr rfl
        intro v hv
        ring
      _ = (∑ v, c v / 2) + ∑ v, (c v / 2) * sign v W := by
        rw [Finset.sum_add_distrib]
      _ = (∑ v, c v) / 2 + ∑ v, (c v / 2) * sign v W := by
        rw [Finset.sum_div]
  have hlinExpand :
      (∑ v, (c v / 2 + (G.degree v : ℝ) / 4) * sign v W) =
        (∑ v, (c v / 2) * sign v W) +
          (∑ v, (G.degree v : ℝ) * sign v W) / 4 := by
    calc
      (∑ v, (c v / 2 + (G.degree v : ℝ) / 4) * sign v W) =
          ∑ v, ((c v / 2) * sign v W +
            ((G.degree v : ℝ) * sign v W) / 4) := by
        apply Finset.sum_congr rfl
        intro v hv
        ring
      _ = (∑ v, (c v / 2) * sign v W) +
          ∑ v, ((G.degree v : ℝ) * sign v W) / 4 := by
        rw [Finset.sum_add_distrib]
      _ = (∑ v, (c v / 2) * sign v W) +
          (∑ v, (G.degree v : ℝ) * sign v W) / 4 := by
        rw [Finset.sum_div]
  rw [hedgeExpand, hcExpand, hlinExpand, hlinear]
  ring

end GraphPolynomial

end Probability
end Erdos88
