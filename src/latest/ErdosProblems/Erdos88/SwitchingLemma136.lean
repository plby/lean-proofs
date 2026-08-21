import ErdosProblems.Erdos88.BooleanSlices
import ErdosProblems.Erdos88.SliceMixture
import ErdosProblems.Erdos88.BinomialLower

/-!
# The finite variance input to KSSS Lemma 13.6

This module records the exact Walsh expansion and variance identity for a
linearly perturbed induced-edge count under the uniform Boolean-cube law.
It is the first part of KSSS Lemma 13.6 and is kept separate from the
switching combinatorics to avoid a dependency cycle.
-/

open scoped BigOperators

namespace Erdos88.Switching

open Classical
open Erdos88.Probability
open Erdos88.BooleanSlices
open Erdos88.Concentration

section PerturbedVariance

variable {n : ℕ}

/-- Degree-one coordinates and actual graph edges index all nonconstant
Walsh characters in a perturbed induced-edge count. -/
abbrev PerturbedEdgeWalshIndex (G : SimpleGraph (Fin n)) :=
  Fin n ⊕ {e : Sym2 (Fin n) // e ∈ G.edgeFinset}

def perturbedEdgeWalshSupport (G : SimpleGraph (Fin n)) :
    PerturbedEdgeWalshIndex G → Finset (Fin n)
  | Sum.inl v => {v}
  | Sum.inr e => e.1.toFinset

noncomputable def perturbedEdgeWalshCoeff (G : SimpleGraph (Fin n))
    (c : Fin n → ℝ) : PerturbedEdgeWalshIndex G → ℝ
  | Sum.inl v => c v / 2 + (G.degree v : ℝ) / 4
  | Sum.inr _e => 1 / 4

lemma perturbedEdgeWalshSupport_injective (G : SimpleGraph (Fin n)) :
    Function.Injective (perturbedEdgeWalshSupport G) := by
  intro x y hxy
  cases x with
  | inl i =>
      cases y with
      | inl j =>
          simp only [perturbedEdgeWalshSupport, Finset.singleton_inj] at hxy
          subst j
          rfl
      | inr e =>
          have hcard := congrArg Finset.card hxy
          have hedge : ¬e.1.IsDiag :=
            G.not_isDiag_of_mem_edgeFinset e.2
          simp [perturbedEdgeWalshSupport,
            Sym2.card_toFinset_of_not_isDiag e.1 hedge] at hcard
  | inr e =>
      cases y with
      | inl j =>
          have hcard := congrArg Finset.card hxy
          have hedge : ¬e.1.IsDiag :=
            G.not_isDiag_of_mem_edgeFinset e.2
          simp [perturbedEdgeWalshSupport,
            Sym2.card_toFinset_of_not_isDiag e.1 hedge] at hcard
      | inr f =>
          refine congrArg Sum.inr (Subtype.ext ?_)
          apply Sym2.ext
          intro v
          change e.1.toFinset = f.1.toFinset at hxy
          simpa only [Sym2.mem_toFinset] using
            Finset.ext_iff.mp hxy v

/-- The centered perturbed edge count is precisely the sum of its
degree-one and graph-edge Walsh characters. -/
lemma perturbedEdgePolynomial_centered_eq_walshSum
    (G : SimpleGraph (Fin n)) (e₀ : ℝ) (c : Fin n → ℝ)
    (W : Finset (Fin n)) :
    perturbedEdgePolynomial G e₀ c W -
        expectation (1 / 2 : ℝ) (perturbedEdgePolynomial G e₀ c) =
      ∑ q : PerturbedEdgeWalshIndex G,
        perturbedEdgeWalshCoeff G c q *
          walsh (perturbedEdgeWalshSupport G q) W := by
  rw [expectation_perturbedEdgePolynomial G (by norm_num) (by norm_num),
    perturbedEdgePolynomial_walsh]
  rw [Fintype.sum_sum_type]
  simp only [perturbedEdgeWalshCoeff, perturbedEdgeWalshSupport]
  have hedge :
      (∑ e : {e : Sym2 (Fin n) // e ∈ G.edgeFinset},
          (1 / 4 : ℝ) * walsh e.1.toFinset W) =
        (1 / 4 : ℝ) * ∑ e ∈ G.edgeFinset, walsh e.toFinset W := by
    rw [Finset.mul_sum]
    symm
    apply Finset.sum_subtype
    intro e
    simp
  rw [hedge]
  simp only [linearWalsh, quadraticWalsh]
  simp only [walsh, Finset.prod_singleton]
  ring

/-- Exact variance formula in KSSS Lemma 13.6(1). -/
lemma variance_perturbedEdgePolynomial_half
    (G : SimpleGraph (Fin n)) (e₀ : ℝ) (c : Fin n → ℝ) :
    variance (1 / 2 : ℝ) (perturbedEdgePolynomial G e₀ c) =
      ∑ v, (c v / 2 + (G.degree v : ℝ) / 4) ^ 2 +
        (G.edgeFinset.card : ℝ) / 16 := by
  unfold variance
  rw [← uniformExpectation_finset_eq_probability_half
    (fun W => (perturbedEdgePolynomial G e₀ c W -
      expectation (1 / 2 : ℝ) (perturbedEdgePolynomial G e₀ c)) ^ 2)]
  simp_rw [perturbedEdgePolynomial_centered_eq_walshSum]
  rw [uniformExpectation_sq_walsh_sum _ _
    (perturbedEdgeWalshSupport_injective G)]
  rw [Fintype.sum_sum_type]
  simp only [perturbedEdgeWalshCoeff]
  have hedge :
      (∑ _e : {e : Sym2 (Fin n) // e ∈ G.edgeFinset},
          (1 / 4 : ℝ) ^ 2) = (G.edgeFinset.card : ℝ) / 16 := by
    simp
    ring
  rw [hedge]

/-- The quantitative variance estimate in KSSS Lemma 13.6(1). -/
lemma variance_perturbedEdgePolynomial_half_le
    (G : SimpleGraph (Fin n)) (e₀ : ℝ) (c : Fin n → ℝ) (R : ℝ)
    (hR : 1 ≤ R) (hc : ∀ v, |c v| ≤ R * n) :
    variance (1 / 2 : ℝ) (perturbedEdgePolynomial G e₀ c) ≤
      R ^ 2 * n ^ 3 := by
  rw [variance_perturbedEdgePolynomial_half]
  by_cases hn0 : n = 0
  · subst n
    have hedge := G.card_edgeFinset_le_card_choose_two
    have hedgeZero : G.edgeFinset.card = 0 := by simpa using hedge
    simp [hedgeZero]
  have hnNat : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast hnNat
  have hnnonneg : (0 : ℝ) ≤ n := zero_le_one.trans hn
  have hRnonneg : 0 ≤ R := zero_le_one.trans hR
  let b : Fin n → ℝ := fun v => c v / 2 + (G.degree v : ℝ) / 4
  have hb : ∀ v, |b v| ≤ (3 / 4 : ℝ) * R * n := by
    intro v
    have hdegNat : G.degree v ≤ n :=
      Nat.le_of_lt (by simpa using G.degree_lt_card_verts v)
    have hdeg : (G.degree v : ℝ) ≤ n := by exact_mod_cast hdegNat
    have hdegNonneg : (0 : ℝ) ≤ G.degree v := by positivity
    calc
      |b v| ≤ |c v / 2| + |(G.degree v : ℝ) / 4| := by
        exact abs_add_le _ _
      _ = |c v| / 2 + (G.degree v : ℝ) / 4 := by
        rw [abs_div, abs_div, abs_of_nonneg hdegNonneg]
        norm_num
      _ ≤ (R * n) / 2 + n / 4 := by
        exact add_le_add
          (div_le_div_of_nonneg_right (hc v) (by norm_num))
          (div_le_div_of_nonneg_right hdeg (by norm_num))
      _ ≤ (3 / 4 : ℝ) * R * n := by
        nlinarith [mul_nonneg hnnonneg (sub_nonneg.mpr hR)]
  have hBnonneg : 0 ≤ (3 / 4 : ℝ) * R * n := by positivity
  have hsum :
      (∑ v, (c v / 2 + (G.degree v : ℝ) / 4) ^ 2) ≤
        n * ((3 / 4 : ℝ) * R * n) ^ 2 := by
    simpa only [b, vectorSqNorm] using
      vectorSqNorm_le b ((3 / 4 : ℝ) * R * n) hBnonneg hb
  have hedgeNat : G.edgeFinset.card ≤ n ^ 2 := by
    calc
      G.edgeFinset.card ≤ (Fintype.card (Fin n)).choose 2 :=
        G.card_edgeFinset_le_card_choose_two
      _ = n.choose 2 := by simp
      _ ≤ n ^ 2 := Nat.choose_le_pow n 2
  have hedge : (G.edgeFinset.card : ℝ) ≤ n ^ 2 := by
    exact_mod_cast hedgeNat
  have hn23 : (n : ℝ) ^ 2 ≤ n ^ 3 := by
    nlinarith [mul_nonneg (sq_nonneg (n : ℝ)) (sub_nonneg.mpr hn)]
  have hR2 : (1 : ℝ) ≤ R ^ 2 := by
    nlinarith [sq_nonneg (R - 1)]
  have hcubeNonneg : (0 : ℝ) ≤ n ^ 3 := by positivity
  have hscale : (n : ℝ) ^ 2 ≤ R ^ 2 * n ^ 3 :=
    hn23.trans (by nlinarith [mul_nonneg (sub_nonneg.mpr hR2) hcubeNonneg])
  calc
    (∑ v, (c v / 2 + (G.degree v : ℝ) / 4) ^ 2) +
          (G.edgeFinset.card : ℝ) / 16 ≤
        n * ((3 / 4 : ℝ) * R * n) ^ 2 + n ^ 2 / 16 := by
      exact add_le_add hsum (div_le_div_of_nonneg_right hedge (by norm_num))
    _ = (9 / 16 : ℝ) * (R ^ 2 * n ^ 3) + n ^ 2 / 16 := by ring
    _ ≤ R ^ 2 * n ^ 3 := by
      nlinarith [mul_nonneg (sq_nonneg R) hcubeNonneg]

end PerturbedVariance

section PerturbedEditBounds

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Telescoping a one-coordinate bounded-difference estimate over a disjoint
finite set of inserted coordinates. -/
lemma abs_finsetFunction_union_sub_le_card_mul
    (f : Finset V → ℝ) (L : ℝ)
    (hstep : ∀ (S : Finset V) (v : V), v ∉ S →
      |f (insert v S) - f S| ≤ L)
    (A S : Finset V) (hAS : Disjoint A S) :
    |f (A ∪ S) - f S| ≤ A.card * L := by
  induction A using Finset.induction_on with
  | empty => simp
  | @insert v A hv ih =>
      have hvS : v ∉ S := by
        intro hvS
        exact (Finset.disjoint_left.mp hAS) (Finset.mem_insert_self v A) hvS
      have hAS' : Disjoint A S :=
        hAS.mono_left (Finset.subset_insert v A)
      have hvUnion : v ∉ A ∪ S := by simp [hv, hvS]
      rw [Finset.insert_union]
      calc
        |f (insert v (A ∪ S)) - f S| ≤
            |f (insert v (A ∪ S)) - f (A ∪ S)| +
              |f (A ∪ S) - f S| := by
                simpa only [sub_add_sub_cancel] using
                  abs_add_le (f (insert v (A ∪ S)) - f (A ∪ S))
                    (f (A ∪ S) - f S)
        _ ≤ L + A.card * L :=
          add_le_add (hstep (A ∪ S) v hvUnion) (ih hAS')
        _ = (insert v A).card * L := by simp [hv, add_mul, add_comm]

/-- A one-coordinate bounded-difference estimate implies a symmetric-
difference estimate between arbitrary finite sets. -/
lemma abs_finsetFunction_sub_le_symmDiff_card_mul
    (f : Finset V → ℝ) (L : ℝ)
    (hstep : ∀ (S : Finset V) (v : V), v ∉ S →
      |f (insert v S) - f S| ≤ L)
    (S T : Finset V) :
    |f S - f T| ≤ ((S \ T).card + (T \ S).card) * L := by
  let I := S ∩ T
  have hSI : (S \ T) ∪ I = S := by
    ext v
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter, I]
    tauto
  have hTI : (T \ S) ∪ I = T := by
    ext v
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter, I]
    tauto
  have hSdisj : Disjoint (S \ T) I := by
    apply Finset.disjoint_left.mpr
    intro v hvS hvI
    exact (Finset.mem_sdiff.mp hvS).2 (Finset.mem_inter.mp hvI).2
  have hTdisj : Disjoint (T \ S) I := by
    apply Finset.disjoint_left.mpr
    intro v hvT hvI
    exact (Finset.mem_sdiff.mp hvT).2 (Finset.mem_inter.mp hvI).1
  have hS := abs_finsetFunction_union_sub_le_card_mul
    f L hstep (S \ T) I hSdisj
  have hT := abs_finsetFunction_union_sub_le_card_mul
    f L hstep (T \ S) I hTdisj
  rw [hSI] at hS
  rw [hTI] at hT
  calc
    |f S - f T| ≤ |f S - f I| + |f T - f I| := by
      calc
        |f S - f T| = |(f S - f I) - (f T - f I)| := by ring_nf
        _ ≤ |f S - f I| + |f T - f I| := abs_sub _ _
    _ ≤ (S \ T).card * L + (T \ S).card * L :=
      add_le_add hS hT
    _ = ((S \ T).card + (T \ S).card) * L := by
      push_cast
      ring

variable {n : ℕ}

/-- Exact change in a perturbed induced-edge count after inserting one new
vertex. -/
lemma perturbedEdgePolynomial_insert_sub
    (G : SimpleGraph (Fin n)) (e₀ : ℝ) (c : Fin n → ℝ)
    (S : Finset (Fin n)) (v : Fin n) (hv : v ∉ S) :
    perturbedEdgePolynomial G e₀ c (insert v S) -
        perturbedEdgePolynomial G e₀ c S =
      (AKSGraph.degreeInto G v S : ℝ) + c v := by
  have hedge : edgePolynomial G (insert v S) - edgePolynomial G S =
      (AKSGraph.degreeInto G v S : ℝ) := by
    rw [edgePolynomial_eq_inducedEdgeCount,
      edgePolynomial_eq_inducedEdgeCount]
    change (AKSGraph.edgeCount G (insert v S) : ℝ) -
        (AKSGraph.edgeCount G S : ℝ) = _
    rw [AKSGraph.edgeCount_insert G v S hv]
    push_cast
    ring
  have hlinear :
      (∑ u, c u * bit u (insert v S)) - (∑ u, c u * bit u S) = c v := by
    rw [← Finset.sum_sub_distrib]
    rw [Finset.sum_eq_single v]
    · simp [bit, hv]
    · intro u _hu huv
      simp [bit, huv]
    · simp
  unfold perturbedEdgePolynomial
  calc
    e₀ + edgePolynomial G (insert v S) +
          ∑ u, c u * bit u (insert v S) -
        (e₀ + edgePolynomial G S + ∑ u, c u * bit u S) =
        (edgePolynomial G (insert v S) - edgePolynomial G S) +
          ((∑ u, c u * bit u (insert v S)) -
            ∑ u, c u * bit u S) := by ring
    _ = (AKSGraph.degreeInto G v S : ℝ) + c v := by
      rw [hedge, hlinear]

/-- Editing one vertex changes the perturbed edge statistic by at most
`(R+1)n`. -/
lemma abs_perturbedEdgePolynomial_insert_sub_le
    (G : SimpleGraph (Fin n)) (e₀ : ℝ) (c : Fin n → ℝ) (R : ℝ)
    (_hR : 0 ≤ R) (hc : ∀ v, |c v| ≤ R * n)
    (S : Finset (Fin n)) (v : Fin n) (hv : v ∉ S) :
    |perturbedEdgePolynomial G e₀ c (insert v S) -
        perturbedEdgePolynomial G e₀ c S| ≤ (R + 1) * n := by
  rw [perturbedEdgePolynomial_insert_sub G e₀ c S v hv]
  have hdegreeNat : AKSGraph.degreeInto G v S ≤ n :=
    (AKSGraph.degreeInto_le_card G v S).trans
      (by simpa using Finset.card_le_univ S)
  have hdegree : (AKSGraph.degreeInto G v S : ℝ) ≤ n := by
    exact_mod_cast hdegreeNat
  have hdegree0 : (0 : ℝ) ≤ AKSGraph.degreeInto G v S := by positivity
  calc
    |(AKSGraph.degreeInto G v S : ℝ) + c v| ≤
        (AKSGraph.degreeInto G v S : ℝ) + |c v| := by
      simpa only [abs_of_nonneg hdegree0] using
        abs_add_le (AKSGraph.degreeInto G v S : ℝ) (c v)
    _ ≤ (n : ℝ) + R * n := add_le_add hdegree (hc v)
    _ = (R + 1) * n := by ring

/-- Deterministic edit bound used in KSSS Lemma 13.6(2). -/
lemma abs_perturbedEdgePolynomial_sub_le_editDistance
    (G : SimpleGraph (Fin n)) (e₀ : ℝ) (c : Fin n → ℝ) (R : ℝ)
    (hR : 0 ≤ R) (hc : ∀ v, |c v| ≤ R * n)
    (S T : Finset (Fin n)) :
    |perturbedEdgePolynomial G e₀ c S -
        perturbedEdgePolynomial G e₀ c T| ≤
      (((S \ T).card + (T \ S).card : ℕ) : ℝ) * ((R + 1) * n) := by
  simpa only [Nat.cast_add, Nat.cast_mul] using
    abs_finsetFunction_sub_le_symmDiff_card_mul
      (perturbedEdgePolynomial G e₀ c) ((R + 1) * n)
      (abs_perturbedEdgePolynomial_insert_sub_le G e₀ c R hR hc) S T

end PerturbedEditBounds

section FiniteCouplingTransfer

open Erdos88.Concentration

variable {A B : Type*} [Fintype A] [Nonempty A]
  [Fintype B] [Nonempty B]

/-- The event probability of the left marginal of a finite uniform coupling
is its uniform probability. -/
lemma FiniteUniformCoupling.left_probability
    (C : FiniteUniformCoupling A B) (P : A → Prop) :
    C.probability (fun ω ↦ P (C.left ω)) = uniformProbability P := by
  classical
  have h := C.left_uniform_real (fun a ↦ if P a then (1 : ℝ) else 0)
  simpa [FiniteUniformCoupling.probability,
    Concentration.uniformProbability, BooleanSlices.uniformExpectation,
    Fintype.expect_eq_sum_div_card, Fintype.card_fin,
    Finset.sum_ite] using h

/-- The analogous exact event identity for the right marginal. -/
lemma FiniteUniformCoupling.right_probability
    (C : FiniteUniformCoupling A B) (P : B → Prop) :
    C.probability (fun ω ↦ P (C.right ω)) = uniformProbability P := by
  classical
  have h := C.right_uniform_real (fun b ↦ if P b then (1 : ℝ) else 0)
  simpa [FiniteUniformCoupling.probability,
    Concentration.uniformProbability, BooleanSlices.uniformExpectation,
    Fintype.expect_eq_sum_div_card, Fintype.card_fin,
    Finset.sum_ite] using h

/-- Union bound on the explicit finite sample space of a coupling. -/
lemma FiniteUniformCoupling.probability_or_le
    (C : FiniteUniformCoupling A B) (P Q : Fin C.size → Prop) :
    C.probability (fun ω ↦ P ω ∨ Q ω) ≤ C.probability P + C.probability Q := by
  classical
  rw [FiniteUniformCoupling.probability, FiniteUniformCoupling.probability,
    FiniteUniformCoupling.probability, ← add_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast (Finset.card_le_card (by
    intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
    rcases hω with hω | hω
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hω⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hω⟩))).trans
      (Finset.card_union_le _ _)

/-- An event and its complement have total uniform probability one. -/
lemma uniformProbability_add_compl (P : A → Prop) :
    uniformProbability P + uniformProbability (fun a ↦ ¬P a) = 1 := by
  classical
  rw [uniformProbability, uniformProbability, ← add_div]
  have hcard := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset A)) P
  field_simp
  norm_cast
  convert hcard.trans Finset.card_univ using 1
  congr 1 <;> apply congrArg Finset.card <;> apply Finset.ext <;> simp

/-- At density one half, the explicit Bernoulli event probability is the
uniform probability on all subsets. -/
lemma uniformProbability_eq_eventProbability_half {m : ℕ}
    (P : Finset (Fin m) → Prop) :
    uniformProbability P = eventProbability (1 / 2 : ℝ) P := by
  classical
  calc
    uniformProbability P =
        BooleanSlices.uniformExpectation
          (fun W : Finset (Fin m) ↦ if P W then 1 else 0) := by
      simp [uniformProbability, BooleanSlices.uniformExpectation,
        Fintype.expect_eq_sum_div_card]
    _ = expectation (1 / 2 : ℝ)
          (fun W : Finset (Fin m) ↦ if P W then 1 else 0) :=
      uniformExpectation_finset_eq_probability_half _
    _ = eventProbability (1 / 2 : ℝ) P := rfl

/-- A centered second-moment estimate under the uniform Boolean-cube law. -/
lemma uniformProbability_centered_tail_le {m : ℕ}
    (X : Finset (Fin m) → ℝ) (t : ℝ) (ht : 0 < t) :
    uniformProbability (fun W ↦
        t ≤ |X W - expectation (1 / 2 : ℝ) X|) ≤
      variance (1 / 2 : ℝ) X / t ^ 2 := by
  have hcheb := chebyshev_sq_bound (V := Fin m)
    (p := (1 / 2 : ℝ)) (by norm_num) (by norm_num) ht X
  have hiff : ∀ W : Finset (Fin m),
      (t ≤ |X W - expectation (1 / 2 : ℝ) X|) ↔
        t ^ 2 ≤ (X W - expectation (1 / 2 : ℝ) X) ^ 2 := by
    intro W
    simpa only [sq_abs] using
      (sq_le_sq₀ ht.le (abs_nonneg
        (X W - expectation (1 / 2 : ℝ) X))).symm
  rw [uniformProbability_eq_eventProbability_half]
  simpa only [hiff] using hcheb

/-- Push an event on the right marginal into an event on the left marginal,
up to one exceptional event on the coupling space. -/
lemma FiniteUniformCoupling.right_probability_le_left_add
    (C : FiniteUniformCoupling A B) (P : A → Prop) (Q : B → Prop)
    (E : Fin C.size → Prop) (q : ℝ)
    (himp : ∀ ω, Q (C.right ω) → P (C.left ω) ∨ E ω)
    (hE : C.probability E ≤ q) :
    uniformProbability Q ≤ uniformProbability P + q := by
  classical
  calc
    uniformProbability Q = C.probability (fun ω ↦ Q (C.right ω)) :=
      (Erdos88.Switching.FiniteUniformCoupling.right_probability
        (A := A) (B := B) C Q).symm
    _ ≤ C.probability (fun ω ↦ P (C.left ω) ∨ E ω) := by
      rw [FiniteUniformCoupling.probability,
        FiniteUniformCoupling.probability]
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast Finset.card_le_card (by
        intro ω hω
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
        exact himp ω hω)
    _ ≤ C.probability (fun ω ↦ P (C.left ω)) + C.probability E :=
      Erdos88.Switching.FiniteUniformCoupling.probability_or_le C _ E
    _ = uniformProbability P + C.probability E := by
      rw [Erdos88.Switching.FiniteUniformCoupling.left_probability
        (A := A) (B := B) C P]
    _ ≤ uniformProbability P + q := add_le_add le_rfl hE

/-- Transfer a centered window from the Boolean cube to any finite uniform
target through a high-probability bounded editing coupling. -/
lemma FiniteUniformCoupling.target_centered_window_lower {m : ℕ}
    (C : FiniteUniformCoupling (Finset (Fin m)) B)
    (X : Finset (Fin m) → ℝ) (Y : B → ℝ)
    (t r q : ℝ) (ht : 0 < t)
    (hclose : C.IsClose X Y r q) :
    1 - variance (1 / 2 : ℝ) X / t ^ 2 - q ≤
      uniformProbability (fun b ↦
        |Y b - expectation (1 / 2 : ℝ) X| < t + r) := by
  classical
  let sourceBad : Finset (Fin m) → Prop := fun W ↦
    t ≤ |X W - expectation (1 / 2 : ℝ) X|
  let couplingBad : Fin C.size → Prop := fun ω ↦
    r < |X (C.left ω) - Y (C.right ω)|
  let targetBad : B → Prop := fun b ↦
    t + r ≤ |Y b - expectation (1 / 2 : ℝ) X|
  have hbadSub : ∀ ω, targetBad (C.right ω) →
      sourceBad (C.left ω) ∨ couplingBad ω := by
    intro ω hω
    by_cases hsourceω : sourceBad (C.left ω)
    · exact Or.inl hsourceω
    right
    by_contra hcouplingω
    have hsourceLt :
        |X (C.left ω) - expectation (1 / 2 : ℝ) X| < t := by
      exact lt_of_not_ge hsourceω
    have hcouplingLe : |X (C.left ω) - Y (C.right ω)| ≤ r := by
      exact le_of_not_gt hcouplingω
    have htri : |Y (C.right ω) - expectation (1 / 2 : ℝ) X| ≤
        |Y (C.right ω) - X (C.left ω)| +
          |X (C.left ω) - expectation (1 / 2 : ℝ) X| := by
      calc
        |Y (C.right ω) - expectation (1 / 2 : ℝ) X| =
            |(Y (C.right ω) - X (C.left ω)) +
              (X (C.left ω) - expectation (1 / 2 : ℝ) X)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    have hsymm : |Y (C.right ω) - X (C.left ω)| =
        |X (C.left ω) - Y (C.right ω)| := abs_sub_comm _ _
    rw [hsymm] at htri
    have hsum :
        |X (C.left ω) - Y (C.right ω)| +
            |X (C.left ω) - expectation (1 / 2 : ℝ) X| < r + t :=
      add_lt_add_of_le_of_lt hcouplingLe hsourceLt
    exact (not_lt_of_ge hω) (lt_of_le_of_lt htri (by linarith))
  have hcoupling : C.probability couplingBad ≤ q := by
    exact C.bad_probability_le_of_isClose X Y r q hclose
  have htarget : uniformProbability targetBad ≤
      variance (1 / 2 : ℝ) X / t ^ 2 + q := by
    exact (Erdos88.Switching.FiniteUniformCoupling.right_probability_le_left_add
      C sourceBad targetBad couplingBad q hbadSub hcoupling).trans
        (add_le_add (by
          simpa only [sourceBad] using
            uniformProbability_centered_tail_le X t ht) le_rfl)
  have hpartition := uniformProbability_add_compl targetBad
  have hgoodEq : (fun b : B ↦ ¬targetBad b) =
      (fun b ↦ |Y b - expectation (1 / 2 : ℝ) X| < t + r) := by
    funext b
    apply propext
    simp only [targetBad, not_le]
  rw [hgoodEq] at hpartition
  linarith

/-- KSSS Lemma 13.6(2), reduced to its explicit editing-coupling input:
the variance term is discharged by part (1), so only the construction and
failure estimate for the conditioned block-slice coupling remain. -/
lemma perturbedEdge_target_centered_window_lower {m : ℕ}
    (G : SimpleGraph (Fin m)) (e₀ : ℝ) (c : Fin m → ℝ) (R : ℝ)
    (hR : 1 ≤ R) (hc : ∀ v, |c v| ≤ R * m)
    (C : FiniteUniformCoupling (Finset (Fin m)) B) (Y : B → ℝ)
    (t r q : ℝ) (ht : 0 < t)
    (hclose : C.IsClose (perturbedEdgePolynomial G e₀ c) Y r q) :
    1 - (R ^ 2 * m ^ 3) / t ^ 2 - q ≤
      uniformProbability (fun b ↦
        |Y b - expectation (1 / 2 : ℝ)
          (perturbedEdgePolynomial G e₀ c)| < t + r) := by
  have hvar := variance_perturbedEdgePolynomial_half_le G e₀ c R hR hc
  have htSq : 0 ≤ t ^ 2 := sq_nonneg t
  have hdiv :
      variance (1 / 2 : ℝ) (perturbedEdgePolynomial G e₀ c) / t ^ 2 ≤
        (R ^ 2 * m ^ 3) / t ^ 2 :=
    div_le_div_of_nonneg_right hvar htSq
  exact (by linarith :
      1 - (R ^ 2 * m ^ 3) / t ^ 2 - q ≤
        1 - variance (1 / 2 : ℝ)
          (perturbedEdgePolynomial G e₀ c) / t ^ 2 - q).trans
    (Erdos88.Switching.FiniteUniformCoupling.target_centered_window_lower C
      (perturbedEdgePolynomial G e₀ c) Y t r q ht hclose)

end FiniteCouplingTransfer

section WeightedCouplingTransfer

open Erdos88.Concentration

variable {A B : Type*} [Fintype A] [Nonempty A]
  [Fintype B] [Nonempty B]

/-- Reverse the two marginals of a finite weighted coupling. -/
noncomputable def FiniteWeightedCoupling.swap
    (C : FiniteWeightedCoupling A B) : FiniteWeightedCoupling B A where
  weight b a := C.weight a b
  weight_nonneg b a := C.weight_nonneg a b
  left_sum b := C.right_sum b
  right_sum a := C.left_sum a

/-- Swapping a weighted coupling transposes every event mass. -/
lemma FiniteWeightedCoupling.swap_mass
    (C : FiniteWeightedCoupling A B) (p : B → A → Prop) :
    (FiniteWeightedCoupling.swap C).mass p =
      C.mass (fun a b ↦ p b a) := by
  unfold FiniteWeightedCoupling.mass FiniteWeightedCoupling.swap
  rw [Finset.sum_comm]

/-- A closeness certificate is symmetric after swapping the coupling. -/
lemma FiniteWeightedCoupling.swap_isClose
    (C : FiniteWeightedCoupling A B)
    (X : A → ℝ) (Y : B → ℝ) (r q : ℝ)
    (h : C.IsClose X Y r q) :
    (FiniteWeightedCoupling.swap C).IsClose Y X r q := by
  unfold FiniteWeightedCoupling.IsClose at h ⊢
  rw [Erdos88.Switching.FiniteWeightedCoupling.swap_mass C]
  simpa only [abs_sub_comm] using h

/-- The left marginal event mass of a weighted coupling is the uniform
probability of that event. -/
lemma FiniteWeightedCoupling.left_mass
    (C : FiniteWeightedCoupling A B) (P : A → Prop) :
    C.mass (fun a _b ↦ P a) = uniformProbability P := by
  classical
  unfold FiniteWeightedCoupling.mass uniformProbability
  calc
    (∑ a, ∑ b, if P a then C.weight a b else 0) =
        ∑ a, if P a then 1 / (Fintype.card A : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro a _ha
      by_cases hPa : P a
      · simp only [hPa, if_true, C.left_sum]
      · simp only [hPa, if_false, Finset.sum_const_zero]
    _ = ((Finset.univ.filter P).card : ℝ) / Fintype.card A := by
      rw [Finset.sum_ite]
      simp [Finset.sum_const, nsmul_eq_mul]
      rw [Finset.card_filter]
      rw [div_eq_mul_inv]

/-- The analogous right marginal identity. -/
lemma FiniteWeightedCoupling.right_mass
    (C : FiniteWeightedCoupling A B) (P : B → Prop) :
    C.mass (fun _a b ↦ P b) = uniformProbability P := by
  classical
  unfold FiniteWeightedCoupling.mass uniformProbability
  rw [Finset.sum_comm]
  calc
    (∑ b, ∑ a, if P b then C.weight a b else 0) =
        ∑ b, if P b then 1 / (Fintype.card B : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro b _hb
      by_cases hPb : P b
      · simp only [hPb, if_true, C.right_sum]
      · simp only [hPb, if_false, Finset.sum_const_zero]
    _ = ((Finset.univ.filter P).card : ℝ) / Fintype.card B := by
      rw [Finset.sum_ite]
      simp [Finset.sum_const, nsmul_eq_mul]
      rw [Finset.card_filter]
      rw [div_eq_mul_inv]

/-- Complementary events have total weighted mass one. -/
lemma FiniteWeightedCoupling.mass_add_compl
    (C : FiniteWeightedCoupling A B) (P : A → B → Prop) :
    C.mass P + C.mass (fun a b ↦ ¬P a b) = 1 := by
  classical
  rw [← C.mass_univ]
  unfold FiniteWeightedCoupling.mass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _hb
  by_cases hP : P a b <;> simp [hP]

/-- Weighted mass is monotone under event inclusion. -/
lemma FiniteWeightedCoupling.mass_mono
    (C : FiniteWeightedCoupling A B) {P Q : A → B → Prop}
    (hPQ : ∀ a b, P a b → Q a b) : C.mass P ≤ C.mass Q := by
  classical
  unfold FiniteWeightedCoupling.mass
  apply Finset.sum_le_sum
  intro a _ha
  apply Finset.sum_le_sum
  intro b _hb
  by_cases hP : P a b
  · simp only [hP, if_true]
    simp only [hPQ a b hP, if_true]
    exact le_rfl
  · simp only [hP, if_false]
    by_cases hQ : Q a b <;> simp [hQ, C.weight_nonneg]

/-- Union bound for weighted coupling mass. -/
lemma FiniteWeightedCoupling.mass_or_le
    (C : FiniteWeightedCoupling A B) (P Q : A → B → Prop) :
    C.mass (fun a b ↦ P a b ∨ Q a b) ≤ C.mass P + C.mass Q := by
  classical
  unfold FiniteWeightedCoupling.mass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a _ha
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro b _hb
  by_cases hP : P a b <;> by_cases hQ : Q a b <;>
    simp [hP, hQ, C.weight_nonneg]

/-- Weighted analogue of the centered-window transfer theorem. -/
lemma FiniteWeightedCoupling.target_centered_window_lower {m : ℕ}
    (C : FiniteWeightedCoupling (Finset (Fin m)) B)
    (X : Finset (Fin m) → ℝ) (Y : B → ℝ)
    (t r q : ℝ) (ht : 0 < t)
    (hclose : C.IsClose X Y r q) :
    1 - variance (1 / 2 : ℝ) X / t ^ 2 - q ≤
      uniformProbability (fun b ↦
        |Y b - expectation (1 / 2 : ℝ) X| < t + r) := by
  classical
  let sourceBad : Finset (Fin m) → Prop := fun W ↦
    t ≤ |X W - expectation (1 / 2 : ℝ) X|
  let couplingBad : Finset (Fin m) → B → Prop := fun W b ↦
    r < |X W - Y b|
  let targetBad : B → Prop := fun b ↦
    t + r ≤ |Y b - expectation (1 / 2 : ℝ) X|
  have hbadSub : ∀ W b, targetBad b → sourceBad W ∨ couplingBad W b := by
    intro W b hb
    by_cases hW : sourceBad W
    · exact Or.inl hW
    right
    by_contra hcoupling
    have hsourceLt : |X W - expectation (1 / 2 : ℝ) X| < t :=
      lt_of_not_ge hW
    have hcouplingLe : |X W - Y b| ≤ r := le_of_not_gt hcoupling
    have htri : |Y b - expectation (1 / 2 : ℝ) X| ≤
        |Y b - X W| + |X W - expectation (1 / 2 : ℝ) X| := by
      calc
        |Y b - expectation (1 / 2 : ℝ) X| =
            |(Y b - X W) + (X W - expectation (1 / 2 : ℝ) X)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    rw [abs_sub_comm (Y b) (X W)] at htri
    exact (not_lt_of_ge hb) (lt_of_le_of_lt htri (by linarith))
  have hgoodBad := Erdos88.Switching.FiniteWeightedCoupling.mass_add_compl C
    (fun W b ↦ |X W - Y b| ≤ r)
  have hcoupling : C.mass couplingBad ≤ q := by
    unfold FiniteWeightedCoupling.IsClose at hclose
    have hcompl : C.mass couplingBad =
        C.mass (fun W b ↦ ¬ |X W - Y b| ≤ r) := by
      congr 1
      funext W b
      apply propext
      simp only [couplingBad, not_le]
    rw [hcompl]
    linarith
  have htarget : uniformProbability targetBad ≤
      variance (1 / 2 : ℝ) X / t ^ 2 + q := by
    calc
      uniformProbability targetBad = C.mass (fun _W b ↦ targetBad b) :=
        (Erdos88.Switching.FiniteWeightedCoupling.right_mass C targetBad).symm
      _ ≤ C.mass (fun W b ↦ sourceBad W ∨ couplingBad W b) :=
        Erdos88.Switching.FiniteWeightedCoupling.mass_mono C
          (fun W b hb ↦ hbadSub W b hb)
      _ ≤ C.mass (fun W _b ↦ sourceBad W) + C.mass couplingBad :=
        Erdos88.Switching.FiniteWeightedCoupling.mass_or_le C _ _
      _ = uniformProbability sourceBad + C.mass couplingBad := by
        rw [Erdos88.Switching.FiniteWeightedCoupling.left_mass C sourceBad]
      _ ≤ variance (1 / 2 : ℝ) X / t ^ 2 + q :=
        add_le_add (by
          simpa only [sourceBad] using
            uniformProbability_centered_tail_le X t ht) hcoupling
  have hpartition := uniformProbability_add_compl targetBad
  have hgoodEq : (fun b : B ↦ ¬targetBad b) =
      (fun b ↦ |Y b - expectation (1 / 2 : ℝ) X| < t + r) := by
    funext b
    apply propext
    simp only [targetBad, not_le]
  rw [hgoodEq] at hpartition
  linarith

end WeightedCouplingTransfer

section ProductSliceCubeCoupling

universe u v

variable {α : Type u} [Fintype α] [DecidableEq α]

/-- Prefixes of two lengths in the same decoded permutation are nested. -/
lemma signedSlicePositiveSupport_mono (I : Finset α) {p q : ℕ}
    (hpq : p ≤ q) (hp : p ≤ I.card) (hq : q ≤ I.card)
    (e : Fin I.card ≃ ↑I) (σ : Equiv.Perm (Fin I.card)) :
    signedSlicePositiveSupport I p 0 (by simpa using hp) e σ ⊆
      signedSlicePositiveSupport I q 0 (by simpa using hq) e σ := by
  intro x hx
  rw [signedSlicePositiveSupport, Finset.mem_map] at hx ⊢
  obtain ⟨i, _hi, rfl⟩ := hx
  refine ⟨Fin.castLE hpq i, Finset.mem_univ _, ?_⟩
  rfl

variable {κ : Type v} [Fintype κ] [DecidableEq κ]

/-- The restriction of the Boolean product decoder to one bucket is its
positive prefix support. -/
lemma productSlicePermutationDecode_bucket
    (P : BucketPartition α κ) (ell : κ → ℕ)
    (hell : ∀ k, ell k ≤ (P.fiber k).card)
    (e : ∀ k, Fin (P.fiber k).card ≃ ↑(P.fiber k))
    (σ : ProductSignedSliceSampler P) (k : κ) :
    ((productSliceEquiv P ell)
      (productSlicePermutationDecode P ell hell e σ) k).1 =
      signedSlicePositiveSupport (P.fiber k) (ell k) 0
        (by simpa using hell k) (e k) (σ k) := by
  simp [productSlicePermutationDecode, productSignedSliceZeroEquiv,
    signedSliceZeroEquiv, productSignedSliceDecode, signedSliceDecode] <;> rfl

/-- A partition decomposes the cardinality of every finite set into the
cardinalities of its bucket restrictions. -/
lemma card_eq_sum_card_inter_fiber
    (P : BucketPartition α κ) (S : Finset α) :
    S.card = ∑ k, (S ∩ P.fiber k).card := by
  have h := Finset.card_eq_sum_card_fiberwise
    (s := S) (t := (Finset.univ : Finset κ)) (f := P.bucket)
    (by intro x hx; simp)
  rw [h]
  apply Finset.sum_congr rfl
  intro k _hk
  congr 1
  ext x
  simp [BucketPartition.mem_fiber]

/-- Exact edit distance between two product slices decoded from the same
bucket permutations. -/
lemma productSlicePermutationDecode_symmDiff_card
    (P : BucketPartition α κ) (ell ell' : κ → ℕ)
    (hell : ∀ k, ell k ≤ (P.fiber k).card)
    (hell' : ∀ k, ell' k ≤ (P.fiber k).card)
    (e : ∀ k, Fin (P.fiber k).card ≃ ↑(P.fiber k))
    (σ : ProductSignedSliceSampler P) :
    let S := (productSlicePermutationDecode P ell hell e σ).1
    let T := (productSlicePermutationDecode P ell' hell' e σ).1
    (S \ T).card + (T \ S).card = ∑ k, Nat.dist (ell k) (ell' k) := by
  dsimp only
  let S := (productSlicePermutationDecode P ell hell e σ).1
  let T := (productSlicePermutationDecode P ell' hell' e σ).1
  have hS := card_eq_sum_card_inter_fiber P (S \ T)
  have hT := card_eq_sum_card_inter_fiber P (T \ S)
  rw [hS, hT, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _hk
  have hSbucket : S ∩ P.fiber k =
      signedSlicePositiveSupport (P.fiber k) (ell k) 0
        (by simpa using hell k) (e k) (σ k) := by
    exact productSlicePermutationDecode_bucket P ell hell e σ k
  have hTbucket : T ∩ P.fiber k =
      signedSlicePositiveSupport (P.fiber k) (ell' k) 0
        (by simpa using hell' k) (e k) (σ k) := by
    exact productSlicePermutationDecode_bucket P ell' hell' e σ k
  by_cases hle : ell k ≤ ell' k
  · have hsub : S ∩ P.fiber k ⊆ T ∩ P.fiber k := by
      rw [hSbucket, hTbucket]
      exact signedSlicePositiveSupport_mono (P.fiber k) hle
        (hell k) (hell' k) (e k) (σ k)
    have hleft : (S \ T) ∩ P.fiber k = ∅ := by
      ext x
      constructor
      · intro hx
        rw [Finset.mem_inter, Finset.mem_sdiff] at hx
        have hmem := hsub (Finset.mem_inter.mpr ⟨hx.1.1, hx.2⟩)
        have hcontra : False := hx.1.2 (Finset.mem_inter.mp hmem).1
        contradiction
      · intro hx
        simpa using hx
    have hright : (T \ S) ∩ P.fiber k =
        (T ∩ P.fiber k) \ (S ∩ P.fiber k) := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_sdiff]
      tauto
    rw [hleft, Finset.card_empty, zero_add, hright,
      Finset.card_sdiff_of_subset hsub]
    rw [show (T ∩ P.fiber k).card = ell' k by rw [hTbucket]; simp,
      show (S ∩ P.fiber k).card = ell k by rw [hSbucket]; simp]
    rw [Nat.dist_eq_sub_of_le hle]
  · have hle' : ell' k ≤ ell k := Nat.le_of_lt (Nat.lt_of_not_ge hle)
    have hsub : T ∩ P.fiber k ⊆ S ∩ P.fiber k := by
      rw [hSbucket, hTbucket]
      exact signedSlicePositiveSupport_mono (P.fiber k) hle'
        (hell' k) (hell k) (e k) (σ k)
    have hright : (T \ S) ∩ P.fiber k = ∅ := by
      ext x
      constructor
      · intro hx
        rw [Finset.mem_inter, Finset.mem_sdiff] at hx
        have hmem := hsub (Finset.mem_inter.mpr ⟨hx.1.1, hx.2⟩)
        have hcontra : False := hx.1.2 (Finset.mem_inter.mp hmem).1
        contradiction
      · intro hx
        simpa using hx
    have hleft : (S \ T) ∩ P.fiber k =
        (S ∩ P.fiber k) \ (T ∩ P.fiber k) := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_sdiff]
      tauto
    rw [hright, Finset.card_empty, add_zero, hleft,
      Finset.card_sdiff_of_subset hsub]
    rw [show (T ∩ P.fiber k).card = ell' k by rw [hTbucket]; simp,
      show (S ∩ P.fiber k).card = ell k by rw [hSbucket]; simp]
    rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hle']

/-- Couple a fixed product slice to the entire Boolean cube by first drawing
the cube's bucket-count vector with its exact binomial weight and then using
shared permutation prefixes inside every bucket. -/
noncomputable def productSliceCubeCoupling
    (P : BucketPartition α κ) (ell : κ → ℕ)
    (hell : ∀ k, ell k ≤ (P.fiber k).card)
    (e : ∀ k, Fin (P.fiber k).card ≃ ↑(P.fiber k)) :
    letI : Nonempty (ProductSlicePoint P ell) :=
      productSlicePoint_nonempty P ell hell
    FiniteWeightedCoupling (ProductSlicePoint P ell) (Finset α) := by
  letI : Nonempty (ProductSlicePoint P ell) :=
    productSlicePoint_nonempty P ell hell
  let D := fun j : BucketCountVector P ↦
    ProductSlicePoint P (fun k ↦ (j k).val)
  let C : (j : BucketCountVector P) →
      FiniteWeightedCoupling (ProductSlicePoint P ell) (D j) := fun j ↦
    (productSliceSharedPermutationCoupling P ell
      (fun k ↦ (j k).val) hell
      (fun k ↦ Nat.le_of_lt_succ (j k).isLt) e).toWeighted
  exact (FiniteWeightedCoupling.sigmaMixture C).mapRight
    (finsetEquivSigmaProductSlices P).symm

/-- A pointwise bound on shared permutation decodings gives a zero-failure
uniform-coupling certificate. -/
lemma productSliceSharedPermutationCoupling_isClose_of_forall
    (P : BucketPartition α κ) (ell ell' : κ → ℕ)
    (hell : ∀ k, ell k ≤ (P.fiber k).card)
    (hell' : ∀ k, ell' k ≤ (P.fiber k).card)
    (e : ∀ k, Fin (P.fiber k).card ≃ ↑(P.fiber k))
    (X : ProductSlicePoint P ell → ℝ)
    (Y : ProductSlicePoint P ell' → ℝ) (r : ℝ)
    (h : ∀ σ : ProductSignedSliceSampler P,
      |X (productSlicePermutationDecode P ell hell e σ) -
        Y (productSlicePermutationDecode P ell' hell' e σ)| ≤ r) :
    letI : Nonempty (ProductSlicePoint P ell) :=
      productSlicePoint_nonempty P ell hell
    letI : Nonempty (ProductSlicePoint P ell') :=
      productSlicePoint_nonempty P ell' hell'
    (productSliceSharedPermutationCoupling P ell ell' hell hell' e).IsClose
      X Y r 0 := by
  letI : Nonempty (ProductSlicePoint P ell) :=
    productSlicePoint_nonempty P ell hell
  letI : Nonempty (ProductSlicePoint P ell') :=
    productSlicePoint_nonempty P ell' hell'
  let C := productSliceSharedPermutationCoupling P ell ell' hell hell' e
  unfold FiniteUniformCoupling.IsClose FiniteUniformCoupling.probability
  have hall : (Finset.univ.filter fun ω : Fin C.size ↦
      |X (C.left ω) - Y (C.right ω)| ≤ r) = Finset.univ := by
    apply Finset.filter_eq_self.mpr
    intro ω _hω
    simpa only [C, productSliceSharedPermutationCoupling,
      FiniteUniformCoupling.ofMaps] using
      h ((Fintype.equivFin (ProductSignedSliceSampler P)).symm ω)
  rw [hall, Finset.card_univ, Fintype.card_fin]
  have hsize : (C.size : ℝ) ≠ 0 := by exact_mod_cast C.size_pos.ne'
  rw [div_self hsize]
  norm_num

/-- Lift a pointwise bound on every good bucket-count vector through the
exact binomial mixture.  The failure probability is exactly the mass of the
bad count vectors under the uniform Boolean cube. -/
lemma productSliceCubeCoupling_isClose
    (P : BucketPartition α κ) (ell : κ → ℕ)
    (hell : ∀ k, ell k ≤ (P.fiber k).card)
    (e : ∀ k, Fin (P.fiber k).card ≃ ↑(P.fiber k))
    (X : ProductSlicePoint P ell → ℝ) (Y : Finset α → ℝ)
    (good : BucketCountVector P → Prop) (r : ℝ)
    (hclose : ∀ j, good j → ∀ σ : ProductSignedSliceSampler P,
      |X (productSlicePermutationDecode P ell hell e σ) -
        Y (productSlicePermutationDecode P (fun k ↦ (j k).val)
          (fun k ↦ Nat.le_of_lt_succ (j k).isLt) e σ).1| ≤ r) :
    letI : Nonempty (ProductSlicePoint P ell) :=
      productSlicePoint_nonempty P ell hell
    (productSliceCubeCoupling P ell hell e).IsClose X Y r
      (countVectorMass P (fun j ↦ ¬ good j)) := by
  letI : Nonempty (ProductSlicePoint P ell) :=
    productSlicePoint_nonempty P ell hell
  let D := fun j : BucketCountVector P ↦
    ProductSlicePoint P (fun k ↦ (j k).val)
  let C : (j : BucketCountVector P) →
      FiniteWeightedCoupling (ProductSlicePoint P ell) (D j) := fun j ↦
    (productSliceSharedPermutationCoupling P ell
      (fun k ↦ (j k).val) hell
      (fun k ↦ Nat.le_of_lt_succ (j k).isLt) e).toWeighted
  let Ysigma : Sigma D → ℝ := fun s ↦ Y s.2.1
  have hCclose : ∀ j, good j →
      (C j).IsClose X (fun b ↦ Ysigma ⟨j, b⟩) r 0 := by
    intro j hj
    apply FiniteUniformCoupling.toWeighted_isClose
    apply productSliceSharedPermutationCoupling_isClose_of_forall
    intro σ
    exact hclose j hj σ
  have hmix := FiniteWeightedCoupling.sigmaMixture_isClose_of_good
    C good X Ysigma r 0 (by norm_num) hCclose
  have hbad : FiniteWeightedCoupling.indexMass (D := D)
      (fun j ↦ ¬ good j) = countVectorMass P (fun j ↦ ¬ good j) := by
    exact sliceSigma_indexMass_eq_countVectorMass P _
  rw [zero_add, hbad] at hmix
  let ef : Finset α ≃ Sigma D := finsetEquivSigmaProductSlices P
  change ((FiniteWeightedCoupling.sigmaMixture C).mapRight ef.symm).IsClose
    X Y r (countVectorMass P (fun j ↦ ¬ good j))
  apply FiniteWeightedCoupling.mapRight_isClose
  have heinv (s : Sigma D) : ef.symm s = s.2.1 := rfl
  simpa only [Ysigma, heinv] using hmix

/-- For a perturbed induced-edge statistic, the shared-prefix cube coupling
is close whenever the total bucket-count displacement is bounded. -/
lemma perturbedEdge_productSliceCubeCoupling_isClose {n m : ℕ}
    (P : BucketPartition (Fin n) (Fin m)) (ell : Fin m → ℕ)
    (hell : ∀ k, ell k ≤ (P.fiber k).card)
    (e : ∀ k, Fin (P.fiber k).card ≃ ↑(P.fiber k))
    (G : SimpleGraph (Fin n)) (e₀ : ℝ) (c : Fin n → ℝ)
    (R : ℝ) (hR : 0 ≤ R) (hc : ∀ v, |c v| ≤ R * n)
    (d : ℕ) :
    letI : Nonempty (ProductSlicePoint P ell) :=
      productSlicePoint_nonempty P ell hell
    (productSliceCubeCoupling P ell hell e).IsClose
      (fun S ↦ perturbedEdgePolynomial G e₀ c S.1)
      (perturbedEdgePolynomial G e₀ c)
      ((d : ℝ) * ((R + 1) * n))
      (countVectorMass P (fun j ↦
        ¬ ∑ k, Nat.dist (ell k) (j k).val ≤ d)) := by
  letI : Nonempty (ProductSlicePoint P ell) :=
    productSlicePoint_nonempty P ell hell
  apply productSliceCubeCoupling_isClose P ell hell e
    (fun S ↦ perturbedEdgePolynomial G e₀ c S.1)
    (perturbedEdgePolynomial G e₀ c)
    (fun j ↦ ∑ k, Nat.dist (ell k) (j k).val ≤ d)
    ((d : ℝ) * ((R + 1) * n))
  intro j hj σ
  let hell' : ∀ k, (j k).val ≤ (P.fiber k).card :=
    fun k ↦ Nat.le_of_lt_succ (j k).isLt
  let S := (productSlicePermutationDecode P ell hell e σ).1
  let T := (productSlicePermutationDecode P (fun k ↦ (j k).val) hell' e σ).1
  have hdist : (S \ T).card + (T \ S).card =
      ∑ k, Nat.dist (ell k) (j k).val := by
    exact productSlicePermutationDecode_symmDiff_card P ell
      (fun k ↦ (j k).val) hell hell' e σ
  have hraw := abs_perturbedEdgePolynomial_sub_le_editDistance
    G e₀ c R hR hc S T
  have hcast : ((∑ k, Nat.dist (ell k) (j k).val : ℕ) : ℝ) ≤ d := by
    exact_mod_cast hj
  have hL : 0 ≤ (R + 1) * (n : ℝ) := by positivity
  dsimp only [S, T] at hraw ⊢
  rw [hdist] at hraw
  exact hraw.trans (mul_le_mul_of_nonneg_right hcast hL)

/-- A natural-number distance becomes the absolute difference after casting
to the reals. -/
lemma natCast_dist_eq_abs_sub (a b : ℕ) :
    (Nat.dist a b : ℝ) = |(a : ℝ) - b| := by
  by_cases h : a ≤ b
  · rw [Nat.dist_eq_sub_of_le h, Nat.cast_sub h]
    rw [abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast h))]
    ring
  · have h' : b ≤ a := Nat.le_of_lt (Nat.lt_of_not_ge h)
    rw [Nat.dist_comm, Nat.dist_eq_sub_of_le h', Nat.cast_sub h']
    rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast h'))]

/-- Real-budget version of the preceding edit coupling, convenient when the
count window is expressed using square roots. -/
lemma perturbedEdge_productSliceCubeCoupling_isClose_real {n m : ℕ}
    (P : BucketPartition (Fin n) (Fin m)) (ell : Fin m → ℕ)
    (hell : ∀ k, ell k ≤ (P.fiber k).card)
    (e : ∀ k, Fin (P.fiber k).card ≃ ↑(P.fiber k))
    (G : SimpleGraph (Fin n)) (e₀ : ℝ) (c : Fin n → ℝ)
    (R : ℝ) (hR : 0 ≤ R) (hc : ∀ v, |c v| ≤ R * n)
    (d : ℝ) :
    letI : Nonempty (ProductSlicePoint P ell) :=
      productSlicePoint_nonempty P ell hell
    (productSliceCubeCoupling P ell hell e).IsClose
      (fun S ↦ perturbedEdgePolynomial G e₀ c S.1)
      (perturbedEdgePolynomial G e₀ c)
      (d * ((R + 1) * n))
      (countVectorMass P (fun j ↦
        ¬ ∑ k, (Nat.dist (ell k) (j k).val : ℝ) ≤ d)) := by
  letI : Nonempty (ProductSlicePoint P ell) :=
    productSlicePoint_nonempty P ell hell
  apply productSliceCubeCoupling_isClose P ell hell e
    (fun S ↦ perturbedEdgePolynomial G e₀ c S.1)
    (perturbedEdgePolynomial G e₀ c)
    (fun j ↦ ∑ k, (Nat.dist (ell k) (j k).val : ℝ) ≤ d)
    (d * ((R + 1) * n))
  intro j hj σ
  let hell' : ∀ k, (j k).val ≤ (P.fiber k).card :=
    fun k ↦ Nat.le_of_lt_succ (j k).isLt
  let S := (productSlicePermutationDecode P ell hell e σ).1
  let T := (productSlicePermutationDecode P (fun k ↦ (j k).val) hell' e σ).1
  have hdist : (S \ T).card + (T \ S).card =
      ∑ k, Nat.dist (ell k) (j k).val := by
    exact productSlicePermutationDecode_symmDiff_card P ell
      (fun k ↦ (j k).val) hell hell' e σ
  have hraw := abs_perturbedEdgePolynomial_sub_le_editDistance
    G e₀ c R hR hc S T
  have hL : 0 ≤ (R + 1) * (n : ℝ) := by positivity
  dsimp only [S, T] at hraw ⊢
  rw [hdist] at hraw
  push_cast at hraw
  exact hraw.trans (mul_le_mul_of_nonneg_right hj hL)

/-- If the prescribed counts are `A`-close to half and the cube counts are
`W`-close to half, their total shared-prefix edit distance is at most
`m(A+W)`.  Hence the complementary count-vector mass has the standard
binomial union bound. -/
noncomputable def binomialTailBound {α : Type*} [Fintype α] [DecidableEq α]
    (I : Finset α) (W : ℝ) : ℝ :=
  if I.card = 0 then 0 else 2 * Real.exp (-2 * W ^ 2 / I.card)

lemma binomialTailBound_nonneg {α : Type*} [Fintype α] [DecidableEq α]
    (I : Finset α) (W : ℝ) : 0 ≤ binomialTailBound I W := by
  unfold binomialTailBound
  split <;> positivity

/-- The two-sided binomial bound with the zero-coordinate case normalized
exactly to zero. -/
lemma uniformProbability_card_inter_two_sided_sharp {n : ℕ}
    (I : Finset (Fin n)) (W : ℝ) (hW : 0 ≤ W) :
    uniformProbability (fun S : Finset (Fin n) ↦
        W < |((S ∩ I).card : ℝ) - (I.card : ℝ) / 2|) ≤
      binomialTailBound I W := by
  by_cases hI : I.card = 0
  · have hIempty : I = ∅ := Finset.card_eq_zero.mp hI
    simp [binomialTailBound, hIempty, uniformProbability, not_lt_of_ge hW]
  · rw [binomialTailBound, if_neg hI]
    exact uniformProbability_card_inter_two_sided I W hW

/-- Union bound for all bucket counts, without charging empty buckets. -/
lemma uniformProbability_bucketCounts_not_near_sharp
    {n m : ℕ} (P : BucketPartition (Fin n) (Fin m))
    (W : ℝ) (hW : 0 ≤ W) :
    uniformProbability (fun S : Finset (Fin n) ↦
        ¬ ∀ k, |((S ∩ P.fiber k).card : ℝ) -
          ((P.fiber k).card : ℝ) / 2| ≤ W) ≤
      ∑ k : Fin m, binomialTailBound (P.fiber k) W := by
  calc
    uniformProbability (fun S : Finset (Fin n) ↦
        ¬ ∀ k, |((S ∩ P.fiber k).card : ℝ) -
          ((P.fiber k).card : ℝ) / 2| ≤ W) =
        uniformProbability (fun S ↦ ∃ k,
          W < |((S ∩ P.fiber k).card : ℝ) -
            ((P.fiber k).card : ℝ) / 2|) := by
      congr 1
      funext S
      simp only [not_forall, not_le]
    _ ≤ ∑ k : Fin m, uniformProbability
          (fun S : Finset (Fin n) ↦
            W < |((S ∩ P.fiber k).card : ℝ) -
              ((P.fiber k).card : ℝ) / 2|) :=
      uniformProbability_exists_le_sum _
    _ ≤ ∑ k : Fin m, binomialTailBound (P.fiber k) W := by
      apply Finset.sum_le_sum
      intro k _hk
      exact uniformProbability_card_inter_two_sided_sharp (P.fiber k) W hW

lemma countVectorMass_totalDist_gt_le {n m : ℕ}
    (P : BucketPartition (Fin n) (Fin m)) (ell : Fin m → ℕ)
    (A W : ℝ) (hW : 0 ≤ W)
    (hellCenter : ∀ k,
      |(ell k : ℝ) - ((P.fiber k).card : ℝ) / 2| ≤ A) :
    countVectorMass P (fun j ↦
        (m : ℝ) * (A + W) <
          ∑ k, (Nat.dist (ell k) (j k).val : ℝ)) ≤
      ∑ k : Fin m,
        2 * Real.exp (-2 * W ^ 2 / (P.fiber k).card) := by
  rw [countVectorMass_eq_uniformProbability]
  apply (Erdos88.Concentration.uniformProbability_mono (fun S hS ↦ ?_)).trans
    (uniformProbability_bucketCounts_not_near P W hW)
  intro hall
  have hbound :
      (∑ k, (Nat.dist (ell k) (bucketCounts P S k).val : ℝ)) ≤
        (m : ℝ) * (A + W) := by
    calc
      (∑ k, (Nat.dist (ell k) (bucketCounts P S k).val : ℝ)) ≤
          ∑ _k : Fin m, (A + W) := by
        apply Finset.sum_le_sum
        intro k _hk
        rw [natCast_dist_eq_abs_sub]
        have hsource :
            |((bucketCounts P S k).val : ℝ) -
              ((P.fiber k).card : ℝ) / 2| ≤ W := by
          exact hall k
        calc
          |(ell k : ℝ) - (bucketCounts P S k).val| ≤
              |(ell k : ℝ) - ((P.fiber k).card : ℝ) / 2| +
                |((bucketCounts P S k).val : ℝ) -
                  ((P.fiber k).card : ℝ) / 2| := by
            calc
              |(ell k : ℝ) - (bucketCounts P S k).val| =
                  |((ell k : ℝ) - ((P.fiber k).card : ℝ) / 2) -
                    (((bucketCounts P S k).val : ℝ) -
                      ((P.fiber k).card : ℝ) / 2)| := by ring_nf
              _ ≤ _ := abs_sub _ _
          _ ≤ A + W := add_le_add (hellCenter k) hsource
      _ = (m : ℝ) * (A + W) := by simp; ring
  exact (not_lt_of_ge hbound) hS

/-- Sharp empty-bucket version of `countVectorMass_totalDist_gt_le`. -/
lemma countVectorMass_totalDist_gt_le_sharp {n m : ℕ}
    (P : BucketPartition (Fin n) (Fin m)) (ell : Fin m → ℕ)
    (A W : ℝ) (hW : 0 ≤ W)
    (hellCenter : ∀ k,
      |(ell k : ℝ) - ((P.fiber k).card : ℝ) / 2| ≤ A) :
    countVectorMass P (fun j ↦
        (m : ℝ) * (A + W) <
          ∑ k, (Nat.dist (ell k) (j k).val : ℝ)) ≤
      ∑ k : Fin m, binomialTailBound (P.fiber k) W := by
  rw [countVectorMass_eq_uniformProbability]
  apply (uniformProbability_mono (fun S hS ↦ ?_)).trans
    (uniformProbability_bucketCounts_not_near_sharp P W hW)
  intro hall
  have hbound :
      (∑ k, (Nat.dist (ell k) (bucketCounts P S k).val : ℝ)) ≤
        (m : ℝ) * (A + W) := by
    calc
      (∑ k, (Nat.dist (ell k) (bucketCounts P S k).val : ℝ)) ≤
          ∑ _k : Fin m, (A + W) := by
        apply Finset.sum_le_sum
        intro k _hk
        rw [natCast_dist_eq_abs_sub]
        have hsource :
            |((bucketCounts P S k).val : ℝ) -
              ((P.fiber k).card : ℝ) / 2| ≤ W := by
          exact hall k
        calc
          |(ell k : ℝ) - (bucketCounts P S k).val| ≤
              |(ell k : ℝ) - ((P.fiber k).card : ℝ) / 2| +
                |((bucketCounts P S k).val : ℝ) -
                  ((P.fiber k).card : ℝ) / 2| := by
            calc
              |(ell k : ℝ) - (bucketCounts P S k).val| =
                  |((ell k : ℝ) - ((P.fiber k).card : ℝ) / 2) -
                    (((bucketCounts P S k).val : ℝ) -
                      ((P.fiber k).card : ℝ) / 2)| := by ring_nf
              _ ≤ _ := abs_sub _ _
          _ ≤ A + W := add_le_add (hellCenter k) hsource
      _ = (m : ℝ) * (A + W) := by simp; ring
  exact (not_lt_of_ge hbound) hS

/-- A product slice whose bucket sizes are close to half inherits a centered
window lower bound from the full Boolean cube.  The two error terms are the
Chebyshev loss for the quadratic polynomial and the binomial loss for the
random cube bucket counts. -/
lemma perturbedEdge_productSlice_centered_window_lower {n m : ℕ}
    (P : BucketPartition (Fin n) (Fin m)) (ell : Fin m → ℕ)
    (hell : ∀ k, ell k ≤ (P.fiber k).card)
    (e : ∀ k, Fin (P.fiber k).card ≃ ↑(P.fiber k))
    (G : SimpleGraph (Fin n)) (e₀ : ℝ) (c : Fin n → ℝ)
    (R : ℝ) (hR : 1 ≤ R) (hc : ∀ v, |c v| ≤ R * n)
    (A W t : ℝ) (hW : 0 ≤ W) (ht : 0 < t)
    (hellCenter : ∀ k,
      |(ell k : ℝ) - ((P.fiber k).card : ℝ) / 2| ≤ A) :
    letI : Nonempty (ProductSlicePoint P ell) :=
      productSlicePoint_nonempty P ell hell
    1 - (R ^ 2 * n ^ 3) / t ^ 2 -
        (∑ k : Fin m,
          2 * Real.exp (-2 * W ^ 2 / (P.fiber k).card)) ≤
      Erdos88.Concentration.uniformProbability
        (fun S : ProductSlicePoint P ell ↦
          |perturbedEdgePolynomial G e₀ c S.1 -
            expectation (1 / 2 : ℝ) (perturbedEdgePolynomial G e₀ c)| <
              t + ((m : ℝ) * (A + W)) * ((R + 1) * n)) := by
  letI : Nonempty (ProductSlicePoint P ell) :=
    productSlicePoint_nonempty P ell hell
  let C := productSliceCubeCoupling P ell hell e
  let q := countVectorMass P (fun j ↦
    ¬ ∑ k, (Nat.dist (ell k) (j k).val : ℝ) ≤ (m : ℝ) * (A + W))
  have hcloseTarget : C.IsClose
      (fun S ↦ perturbedEdgePolynomial G e₀ c S.1)
      (perturbedEdgePolynomial G e₀ c)
      (((m : ℝ) * (A + W)) * ((R + 1) * n)) q := by
    exact perturbedEdge_productSliceCubeCoupling_isClose_real
      P ell hell e G e₀ c R (by linarith) hc ((m : ℝ) * (A + W))
  have hcloseSource : (FiniteWeightedCoupling.swap C).IsClose
      (perturbedEdgePolynomial G e₀ c)
      (fun S ↦ perturbedEdgePolynomial G e₀ c S.1)
      (((m : ℝ) * (A + W)) * ((R + 1) * n)) q :=
    Erdos88.Switching.FiniteWeightedCoupling.swap_isClose C _ _ _ _ hcloseTarget
  have hwindow := Erdos88.Switching.FiniteWeightedCoupling.target_centered_window_lower
    (FiniteWeightedCoupling.swap C)
    (perturbedEdgePolynomial G e₀ c)
    (fun S ↦ perturbedEdgePolynomial G e₀ c S.1)
    t (((m : ℝ) * (A + W)) * ((R + 1) * n)) q ht hcloseSource
  have hvar := variance_perturbedEdgePolynomial_half_le G e₀ c R hR hc
  have hdiv : variance (1 / 2 : ℝ) (perturbedEdgePolynomial G e₀ c) / t ^ 2 ≤
      (R ^ 2 * n ^ 3) / t ^ 2 :=
    div_le_div_of_nonneg_right hvar (sq_nonneg t)
  have hq : q ≤ ∑ k : Fin m,
      2 * Real.exp (-2 * W ^ 2 / (P.fiber k).card) := by
    simpa only [q, not_le] using
      countVectorMass_totalDist_gt_le P ell A W hW hellCenter
  exact (by linarith :
      1 - (R ^ 2 * n ^ 3) / t ^ 2 -
          (∑ k : Fin m, 2 * Real.exp (-2 * W ^ 2 / (P.fiber k).card)) ≤
        1 - variance (1 / 2 : ℝ) (perturbedEdgePolynomial G e₀ c) / t ^ 2 - q).trans
    hwindow

/-- Extend a vector of prescribed bucket counts by a freely varying final
bucket count. -/
def extendLastCount {m : ℕ} (ell : Fin m → ℕ) (h : ℕ) :
    Fin (m + 1) → ℕ :=
  Fin.lastCases h ell

@[simp] lemma extendLastCount_last {m : ℕ} (ell : Fin m → ℕ) (h : ℕ) :
    extendLastCount ell h (Fin.last m) = h := by
  simp [extendLastCount]

@[simp] lemma extendLastCount_castSucc {m : ℕ} (ell : Fin m → ℕ)
    (h : ℕ) (k : Fin m) :
    extendLastCount ell h k.castSucc = ell k := by
  simp [extendLastCount]

/-- Subsets satisfying prescribed counts on every bucket except the final
bucket of a partition. -/
def PrescribedProductSlicePoint {n m : ℕ}
    (P : BucketPartition (Fin n) (Fin (m + 1))) (ell : Fin m → ℕ) :=
  {S : Finset (Fin n) //
    ∀ k : Fin m, (S ∩ P.fiber k.castSucc).card = ell k}

/-- Decompose a partially prescribed product slice according to the number
of selected points in the final bucket. -/
noncomputable def partialProductSliceEquiv {n m : ℕ}
    (P : BucketPartition (Fin n) (Fin (m + 1))) (ell : Fin m → ℕ) :
    (Sigma fun h : Fin ((P.fiber (Fin.last m)).card + 1) ↦
      ProductSlicePoint P (extendLastCount ell h.val)) ≃
      PrescribedProductSlicePoint P ell where
  toFun S := ⟨S.2.1, fun k ↦ by
    simpa only [extendLastCount, Fin.lastCases_castSucc] using
      (mem_productBooleanSlice P (extendLastCount ell S.1.val) S.2.1).mp
        S.2.2 k.castSucc⟩
  invFun S :=
    ⟨⟨(S.1 ∩ P.fiber (Fin.last m)).card,
        Nat.lt_succ_of_le (Finset.card_le_card Finset.inter_subset_right)⟩,
      ⟨S.1, (mem_productBooleanSlice P
        (extendLastCount ell (S.1 ∩ P.fiber (Fin.last m)).card) S.1).mpr (fun k ↦ by
          refine Fin.lastCases ?_ (fun j ↦ ?_) k
          · simp only [extendLastCount, Fin.lastCases_last]
          · simpa only [extendLastCount, Fin.lastCases_castSucc] using S.2 j)⟩⟩
  left_inv S := by
    have hh :
        (⟨(S.2.1 ∩ P.fiber (Fin.last m)).card,
          Nat.lt_succ_of_le (Finset.card_le_card Finset.inter_subset_right)⟩ :
            Fin ((P.fiber (Fin.last m)).card + 1)) = S.1 := by
      apply Fin.ext
      simpa only [extendLastCount, Fin.lastCases_last] using
        (mem_productBooleanSlice P (extendLastCount ell S.1.val) S.2.1).mp
          S.2.2 (Fin.last m)
    apply Sigma.ext hh
    apply (Subtype.heq_iff_coe_eq (fun x ↦ by
      change x ∈ productBooleanSlice P
          (extendLastCount ell (S.2.1 ∩ P.fiber (Fin.last m)).card) ↔
        x ∈ productBooleanSlice P (extendLastCount ell S.1.val)
      have hhval := congrArg Fin.val hh
      change (S.2.1 ∩ P.fiber (Fin.last m)).card = S.1.val at hhval
      rw [hhval])).2
    rfl
  right_inv S := by
    apply Subtype.ext
    rfl

noncomputable instance prescribedProductSlicePointFintype {n m : ℕ}
    (P : BucketPartition (Fin n) (Fin (m + 1))) (ell : Fin m → ℕ) :
    Fintype (PrescribedProductSlicePoint P ell) :=
  Fintype.ofEquiv _ (partialProductSliceEquiv P ell)

theorem prescribedProductSlicePoint_nonempty {n m : ℕ}
    (P : BucketPartition (Fin n) (Fin (m + 1))) (ell : Fin m → ℕ)
    (hell : ∀ k, ell k ≤ (P.fiber k.castSucc).card) :
    Nonempty (PrescribedProductSlicePoint P ell) := by
  let h0 : Fin ((P.fiber (Fin.last m)).card + 1) :=
    ⟨0, Nat.zero_lt_succ _⟩
  let ell0 := extendLastCount ell h0.val
  have hell0 : ∀ k, ell0 k ≤ (P.fiber k).card := by
    intro k
    refine Fin.lastCases ?_ (fun j ↦ ?_) k
    · simp only [ell0, h0, extendLastCount, Fin.lastCases_last]
      exact Nat.zero_le _
    · simpa only [ell0, extendLastCount, Fin.lastCases_castSucc] using hell j
  let T := Classical.choice (productSlicePoint_nonempty P ell0 hell0)
  exact ⟨⟨T.1, fun k ↦ by
    simpa only [ell0, extendLastCount, Fin.lastCases_castSucc] using
      (mem_productBooleanSlice P ell0 T.1).mp T.2 k.castSucc⟩⟩

/-- Cardinality of one fiber in the decomposition of a partially prescribed
product slice. -/
lemma partialProductSlice_fiber_card {n m : ℕ}
    (P : BucketPartition (Fin n) (Fin (m + 1))) (ell : Fin m → ℕ)
    (h : Fin ((P.fiber (Fin.last m)).card + 1)) :
    Fintype.card (ProductSlicePoint P (extendLastCount ell h.val)) =
      (∏ k : Fin m, (P.fiber k.castSucc).card.choose (ell k)) *
        (P.fiber (Fin.last m)).card.choose h.val := by
  rw [card_productSlicePoint, Fin.prod_univ_castSucc]
  simp only [extendLastCount_castSucc, extendLastCount_last]

/-- Exact cardinality of a partially prescribed product slice. -/
lemma card_partialProductSlice {n m : ℕ}
    (P : BucketPartition (Fin n) (Fin (m + 1))) (ell : Fin m → ℕ) :
    Fintype.card
        (Sigma fun h : Fin ((P.fiber (Fin.last m)).card + 1) ↦
          ProductSlicePoint P (extendLastCount ell h.val)) =
      (∏ k : Fin m, (P.fiber k.castSucc).card.choose (ell k)) *
        2 ^ (P.fiber (Fin.last m)).card := by
  rw [Fintype.card_sigma]
  simp_rw [partialProductSlice_fiber_card]
  rw [← Finset.mul_sum]
  rw [Fin.sum_univ_eq_sum_range
    (fun h ↦ (P.fiber (Fin.last m)).card.choose h)
    ((P.fiber (Fin.last m)).card + 1)]
  rw [Nat.sum_range_choose]

/-- The free final-bucket index has its exact binomial law. -/
lemma partialProductSlice_indexMass_eq {n m : ℕ}
    (P : BucketPartition (Fin n) (Fin (m + 1))) (ell : Fin m → ℕ)
    (hell : ∀ k, ell k ≤ (P.fiber k.castSucc).card)
    (E : Fin ((P.fiber (Fin.last m)).card + 1) → Prop) :
    FiniteWeightedCoupling.indexMass
        (D := fun h : Fin ((P.fiber (Fin.last m)).card + 1) ↦
          ProductSlicePoint P (extendLastCount ell h.val)) E =
      ∑ h : Fin ((P.fiber (Fin.last m)).card + 1),
        if E h then
          ((P.fiber (Fin.last m)).card.choose h.val : ℝ) /
            2 ^ (P.fiber (Fin.last m)).card
        else 0 := by
  let K : ℕ := ∏ k : Fin m,
    (P.fiber k.castSucc).card.choose (ell k)
  have hK : 0 < K := by
    dsimp only [K]
    exact Finset.prod_pos fun k _hk ↦ Nat.choose_pos (hell k)
  unfold FiniteWeightedCoupling.indexMass
  rw [card_partialProductSlice]
  apply Finset.sum_congr rfl
  intro h _hh
  rw [partialProductSlice_fiber_card]
  by_cases hE : E h
  · simp only [hE, if_true, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    dsimp only [K] at hK ⊢
    field_simp
  · simp only [hE, if_false]

/-- The explicit binomial index mass equals uniform subset probability. -/
lemma binomialIndexMass_eq_uniformProbability (M : ℕ)
    (E : Fin (M + 1) → Prop) :
    (∑ h : Fin (M + 1),
        if E h then (M.choose h.val : ℝ) / 2 ^ M else 0) =
      uniformProbability (fun S : Finset (Fin M) ↦
        E ⟨S.card, by simpa using Finset.card_le_univ S⟩) := by
  have hnumNat :
      (Finset.univ.filter (fun S : Finset (Fin M) ↦
        E ⟨S.card, by simpa using Finset.card_le_univ S⟩)).card =
      ∑ h : Fin (M + 1), if E h then M.choose h.val else 0 := by
    let g : Finset (Fin M) → Fin (M + 1) := fun S ↦
      ⟨S.card, by simpa using Finset.card_le_univ S⟩
    rw [Finset.card_eq_sum_card_fiberwise
      (s := Finset.univ.filter (fun S : Finset (Fin M) ↦ E (g S)))
      (t := Finset.univ) (f := g) (by simp)]
    apply Finset.sum_congr rfl
    intro h _hh
    by_cases hE : E h
    · rw [if_pos hE]
      rw [show (Finset.univ.filter (fun S : Finset (Fin M) ↦
          E (g S))).filter (fun S ↦ g S = h) =
          (Finset.univ : Finset (Fin M)).powersetCard h.val by
        ext S
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_powersetCard]
        constructor
        · intro hS
          exact ⟨Finset.subset_univ _, by
            have := congrArg Fin.val hS.2
            simpa only [g] using this⟩
        · intro hS
          refine ⟨?_, ?_⟩
          · simpa only [g, hS.2] using hE
          · apply Fin.ext
            simpa only [g] using hS.2]
      simp
    · rw [if_neg hE]
      have hempty : (Finset.univ.filter (fun S : Finset (Fin M) ↦
          E (g S))).filter (fun S ↦ g S = h) = ∅ := by
        ext S
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro hS
          exact (hE (hS.2 ▸ hS.1)).elim
        · intro hS
          simp at hS
      rw [hempty]
      simp
  unfold uniformProbability
  have hden : Fintype.card (Finset (Fin M)) = 2 ^ M := by simp
  rw [hnumNat, hden, Nat.cast_sum]
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro h _hh
  by_cases hE : E h <;> simp [hE]

/-- The exceptional mass from the free final bucket obeys the standard
two-sided binomial tail. -/
lemma partialProductSlice_indexMass_not_near_le {n m : ℕ}
    (P : BucketPartition (Fin n) (Fin (m + 1))) (ell : Fin m → ℕ)
    (hell : ∀ k, ell k ≤ (P.fiber k.castSucc).card)
    (W : ℝ) (hW : 0 ≤ W) :
    FiniteWeightedCoupling.indexMass
        (D := fun h : Fin ((P.fiber (Fin.last m)).card + 1) ↦
          ProductSlicePoint P (extendLastCount ell h.val))
        (fun h ↦ ¬ |(h.val : ℝ) -
          ((P.fiber (Fin.last m)).card : ℝ) / 2| ≤ W) ≤
      binomialTailBound (P.fiber (Fin.last m)) W := by
  rw [partialProductSlice_indexMass_eq P ell hell]
  rw [binomialIndexMass_eq_uniformProbability]
  have htail := uniformProbability_card_inter_two_sided_sharp
    (Finset.univ : Finset (Fin (P.fiber (Fin.last m)).card)) W hW
  simpa only [not_le, Finset.inter_univ, Finset.card_univ,
    Fintype.card_fin, binomialTailBound] using htail

/-- Centered-window lower bound on the sigma presentation of a partially
prescribed product slice. -/
lemma partialProductSlice_centered_window_lower {n m : ℕ}
    (P : BucketPartition (Fin n) (Fin (m + 1))) (ell : Fin m → ℕ)
    (hell : ∀ k, ell k ≤ (P.fiber k.castSucc).card)
    (e : ∀ k, Fin (P.fiber k).card ≃ ↑(P.fiber k))
    (G : SimpleGraph (Fin n)) (e₀ : ℝ) (c : Fin n → ℝ)
    (R : ℝ) (hR : 1 ≤ R) (hc : ∀ v, |c v| ≤ R * n)
    (A B W t : ℝ) (hB : 0 ≤ B) (hW : 0 ≤ W) (ht : 0 < t)
    (hellCenter : ∀ k,
      |(ell k : ℝ) - ((P.fiber k.castSucc).card : ℝ) / 2| ≤ A) :
    let D := fun h : Fin ((P.fiber (Fin.last m)).card + 1) ↦
      ProductSlicePoint P (extendLastCount ell h.val)
    1 - (R ^ 2 * n ^ 3) / t ^ 2 -
        (∑ k : Fin (m + 1),
          binomialTailBound (P.fiber k) W) -
        binomialTailBound (P.fiber (Fin.last m)) B ≤
      uniformProbability (fun S : Sigma D ↦
        |perturbedEdgePolynomial G e₀ c S.2.1 -
          expectation (1 / 2 : ℝ) (perturbedEdgePolynomial G e₀ c)| <
            t + (((m + 1 : ℕ) : ℝ) * (max A B + W)) *
              ((R + 1) * n)) := by
  let J := Fin ((P.fiber (Fin.last m)).card + 1)
  let ellExt : J → Fin (m + 1) → ℕ := fun h ↦
    extendLastCount ell h.val
  let D : J → Type := fun h ↦ ProductSlicePoint P (ellExt h)
  let hellExt : ∀ h k, ellExt h k ≤ (P.fiber k).card := fun h k ↦ by
    refine Fin.lastCases ?_ (fun j ↦ ?_) k
    · simpa only [ellExt, extendLastCount_last] using Nat.le_of_lt_succ h.isLt
    · simpa only [ellExt, extendLastCount_castSucc] using hell j
  letI : (h : J) → Nonempty (D h) := fun h ↦
    productSlicePoint_nonempty P (ellExt h) (hellExt h)
  let C : (h : J) → FiniteWeightedCoupling (Finset (Fin n)) (D h) := fun h ↦
    FiniteWeightedCoupling.swap
      (productSliceCubeCoupling P (ellExt h) (hellExt h) e)
  let good : J → Prop := fun h ↦
    |(h.val : ℝ) - ((P.fiber (Fin.last m)).card : ℝ) / 2| ≤ B
  let radius : ℝ := (((m + 1 : ℕ) : ℝ) * (max A B + W)) *
    ((R + 1) * n)
  let q : ℝ := ∑ k : Fin (m + 1),
    binomialTailBound (P.fiber k) W
  let X : Finset (Fin n) → ℝ := perturbedEdgePolynomial G e₀ c
  let Y : Sigma D → ℝ := fun S ↦ perturbedEdgePolynomial G e₀ c S.2.1
  have hq : 0 ≤ q :=
    Finset.sum_nonneg fun k _ ↦ binomialTailBound_nonneg (P.fiber k) W
  have hclose : ∀ h, good h →
      (C h).IsClose X (fun S ↦ Y ⟨h, S⟩) radius q := by
    intro h hh
    have hcenter : ∀ k,
        |(ellExt h k : ℝ) - ((P.fiber k).card : ℝ) / 2| ≤ max A B := by
      intro k
      refine Fin.lastCases ?_ (fun j ↦ ?_) k
      · simpa only [ellExt, extendLastCount_last] using
          hh.trans (le_max_right A B)
      · simpa only [ellExt, extendLastCount_castSucc] using
          (hellCenter j).trans (le_max_left A B)
    let qh := countVectorMass P (fun j ↦
      ¬ ∑ k, (Nat.dist (ellExt h k) (j k).val : ℝ) ≤
        ((m + 1 : ℕ) : ℝ) * (max A B + W))
    have htarget : (productSliceCubeCoupling P (ellExt h) (hellExt h) e).IsClose
        (fun S ↦ perturbedEdgePolynomial G e₀ c S.1)
        (perturbedEdgePolynomial G e₀ c) radius qh := by
      simpa only [radius, qh] using
        perturbedEdge_productSliceCubeCoupling_isClose_real
          P (ellExt h) (hellExt h) e G e₀ c R (by linarith) hc
            (((m + 1 : ℕ) : ℝ) * (max A B + W))
    have hsource : (C h).IsClose X (fun S ↦ Y ⟨h, S⟩) radius qh := by
      simpa only [C, X, Y] using
        Erdos88.Switching.FiniteWeightedCoupling.swap_isClose
          (productSliceCubeCoupling P (ellExt h) (hellExt h) e)
          _ _ _ _ htarget
    apply hsource.mono_failure
    simpa only [q, qh, not_le] using
      countVectorMass_totalDist_gt_le_sharp P (ellExt h) (max A B) W hW hcenter
  have hmix := FiniteWeightedCoupling.sigmaMixture_isClose_of_good
    C good X Y radius q hq hclose
  have hwindow := Erdos88.Switching.FiniteWeightedCoupling.target_centered_window_lower
    (FiniteWeightedCoupling.sigmaMixture C) X Y t radius
      (q + FiniteWeightedCoupling.indexMass (D := D) (fun h ↦ ¬good h))
      ht hmix
  have hvar := variance_perturbedEdgePolynomial_half_le G e₀ c R hR hc
  have hdiv : variance (1 / 2 : ℝ) X / t ^ 2 ≤
      (R ^ 2 * n ^ 3) / t ^ 2 := by
    exact div_le_div_of_nonneg_right (by simpa only [X] using hvar) (sq_nonneg t)
  have hbad : FiniteWeightedCoupling.indexMass (D := D) (fun h ↦ ¬good h) ≤
      binomialTailBound (P.fiber (Fin.last m)) B := by
    simpa only [D, J, ellExt, good] using
      partialProductSlice_indexMass_not_near_le P ell hell B hB
  exact (by linarith :
      1 - (R ^ 2 * n ^ 3) / t ^ 2 - q -
          binomialTailBound (P.fiber (Fin.last m)) B ≤
        1 - variance (1 / 2 : ℝ) X / t ^ 2 -
          (q + FiniteWeightedCoupling.indexMass (D := D) (fun h ↦ ¬good h))).trans
    (by simpa only [D, X, Y, radius, q] using hwindow)

/-- KSSS Lemma 13.6(2), at the exact finite-probability level, for a
partition whose first `m` buckets have prescribed counts and whose final
bucket is unrestricted. -/
lemma prescribedProductSlice_centered_window_lower {n m : ℕ}
    (P : BucketPartition (Fin n) (Fin (m + 1))) (ell : Fin m → ℕ)
    (hell : ∀ k, ell k ≤ (P.fiber k.castSucc).card)
    (e : ∀ k, Fin (P.fiber k).card ≃ ↑(P.fiber k))
    (G : SimpleGraph (Fin n)) (e₀ : ℝ) (c : Fin n → ℝ)
    (R : ℝ) (hR : 1 ≤ R) (hc : ∀ v, |c v| ≤ R * n)
    (A B W t : ℝ) (hB : 0 ≤ B) (hW : 0 ≤ W) (ht : 0 < t)
    (hellCenter : ∀ k,
      |(ell k : ℝ) - ((P.fiber k.castSucc).card : ℝ) / 2| ≤ A) :
    letI : Nonempty (PrescribedProductSlicePoint P ell) :=
      prescribedProductSlicePoint_nonempty P ell hell
    1 - (R ^ 2 * n ^ 3) / t ^ 2 -
        (∑ k : Fin (m + 1),
          binomialTailBound (P.fiber k) W) -
        binomialTailBound (P.fiber (Fin.last m)) B ≤
      uniformProbability (fun S : PrescribedProductSlicePoint P ell ↦
        |perturbedEdgePolynomial G e₀ c S.1 -
          expectation (1 / 2 : ℝ) (perturbedEdgePolynomial G e₀ c)| <
            t + (((m + 1 : ℕ) : ℝ) * (max A B + W)) *
              ((R + 1) * n)) := by
  letI : Nonempty (PrescribedProductSlicePoint P ell) :=
    prescribedProductSlicePoint_nonempty P ell hell
  let D := fun h : Fin ((P.fiber (Fin.last m)).card + 1) ↦
    ProductSlicePoint P (extendLastCount ell h.val)
  have hsigma : Nonempty (Sigma D) :=
    Nonempty.map (partialProductSliceEquiv P ell).symm inferInstance
  letI : Nonempty (Sigma D) := hsigma
  have h := partialProductSlice_centered_window_lower
    P ell hell e G e₀ c R hR hc A B W t hB hW ht hellCenter
  rw [← uniformProbability_comp_equiv (partialProductSliceEquiv P ell)
    (fun S : PrescribedProductSlicePoint P ell ↦
      |perturbedEdgePolynomial G e₀ c S.1 -
        expectation (1 / 2 : ℝ) (perturbedEdgePolynomial G e₀ c)| <
          t + (((m + 1 : ℕ) : ℝ) * (max A B + W)) * ((R + 1) * n))]
  change _ ≤ uniformProbability (fun S : Sigma D ↦
    |perturbedEdgePolynomial G e₀ c
          ((partialProductSliceEquiv P ell) S).1 -
      expectation (1 / 2 : ℝ) (perturbedEdgePolynomial G e₀ c)| <
        t + (((m + 1 : ℕ) : ℝ) * (max A B + W)) * ((R + 1) * n))
  have hfun :
      (fun S : Sigma D ↦
        |perturbedEdgePolynomial G e₀ c S.2.1 -
          expectation (1 / 2 : ℝ) (perturbedEdgePolynomial G e₀ c)| <
            t + (((m + 1 : ℕ) : ℝ) * (max A B + W)) * ((R + 1) * n)) =
      (fun S : Sigma D ↦
        |perturbedEdgePolynomial G e₀ c
            ((partialProductSliceEquiv P ell) S).1 -
          expectation (1 / 2 : ℝ) (perturbedEdgePolynomial G e₀ c)| <
            t + (((m + 1 : ℕ) : ℝ) * (max A B + W)) * ((R + 1) * n)) := by
    funext S
    rfl
  rw [← hfun]
  simpa only [D] using h

/-- The canonical partition whose first buckets are a pairwise-disjoint
prescribed family and whose final bucket is their complement. -/
noncomputable def prescribedFamilyPartition {n m : ℕ}
    (W : Fin m → Finset (Fin n)) : BucketPartition (Fin n) (Fin (m + 1)) where
  bucket v := if h : ∃ k, v ∈ W k then (Classical.choose h).castSucc else Fin.last m

lemma prescribedFamilyPartition_fiber_castSucc {n m : ℕ}
    (W : Fin m → Finset (Fin n))
    (hdisj : ∀ i j, i ≠ j → Disjoint (W i) (W j)) (k : Fin m) :
    (prescribedFamilyPartition W).fiber k.castSucc = W k := by
  ext v
  rw [BucketPartition.mem_fiber]
  constructor
  · intro hv
    change (if h : ∃ i, v ∈ W i then (Classical.choose h).castSucc
      else Fin.last m) = k.castSucc at hv
    split at hv
    next h =>
      have hi : Classical.choose h = k := Fin.castSucc_inj.mp hv
      simpa only [hi] using Classical.choose_spec h
    next h =>
      exact (Fin.castSucc_ne_last k hv.symm).elim
  · intro hv
    have h : ∃ i, v ∈ W i := ⟨k, hv⟩
    have hi : Classical.choose h = k := by
      by_contra hik
      exact (Finset.disjoint_left.mp
        (hdisj (Classical.choose h) k hik)
        (Classical.choose_spec h) hv)
    simp only [prescribedFamilyPartition, h, dite_true, hi]

lemma prescribedFamilyPartition_fiber_last {n m : ℕ}
    (W : Fin m → Finset (Fin n)) :
    (prescribedFamilyPartition W).fiber (Fin.last m) =
      (Finset.univ : Finset (Fin n)) \ Finset.univ.biUnion W := by
  ext v
  rw [BucketPartition.mem_fiber]
  simp only [prescribedFamilyPartition, Finset.mem_sdiff, Finset.mem_univ,
    true_and, Finset.mem_biUnion, not_exists]
  constructor
  · intro hv i
    by_contra hvi
    have h : ∃ k, v ∈ W k := ⟨i, hvi⟩
    simp only [h, dite_true] at hv
    exact Fin.castSucc_ne_last (Classical.choose h) hv
  · intro hv
    have h : ¬∃ k, v ∈ W k := by
      intro h
      exact hv h.choose (by simpa using h.choose_spec)
    simp only [h, dite_false]

lemma prescribedFamilyPartition_last_card {n m : ℕ}
    (W : Fin m → Finset (Fin n)) :
    ((prescribedFamilyPartition W).fiber (Fin.last m)).card =
      n - (Finset.univ.biUnion W).card := by
  rw [prescribedFamilyPartition_fiber_last]
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  simp

/-- Subsets with prescribed intersection sizes in a disjoint family. -/
def PrescribedFamilySlicePoint {n m : ℕ}
    (W : Fin m → Finset (Fin n)) (ell : Fin m → ℕ) :=
  {S : Finset (Fin n) // ∀ k, (S ∩ W k).card = ell k}

/-- The family-slice presentation is the partially prescribed product slice
for the canonical family/complement partition. -/
noncomputable def prescribedFamilySliceEquiv {n m : ℕ}
    (W : Fin m → Finset (Fin n))
    (hdisj : ∀ i j, i ≠ j → Disjoint (W i) (W j))
    (ell : Fin m → ℕ) :
    PrescribedProductSlicePoint (prescribedFamilyPartition W) ell ≃
      PrescribedFamilySlicePoint W ell where
  toFun S := ⟨S.1, fun k ↦ by
    rw [← prescribedFamilyPartition_fiber_castSucc W hdisj k]
    exact S.2 k⟩
  invFun S := ⟨S.1, fun k ↦ by
    rw [prescribedFamilyPartition_fiber_castSucc W hdisj k]
    exact S.2 k⟩
  left_inv S := by apply Subtype.ext; rfl
  right_inv S := by apply Subtype.ext; rfl

noncomputable instance prescribedFamilySlicePointFintype {n m : ℕ}
    (W : Fin m → Finset (Fin n)) (ell : Fin m → ℕ) :
    Fintype (PrescribedFamilySlicePoint W ell) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

theorem prescribedFamilySlicePoint_nonempty {n m : ℕ}
    (W : Fin m → Finset (Fin n))
    (hdisj : ∀ i j, i ≠ j → Disjoint (W i) (W j))
    (ell : Fin m → ℕ) (hell : ∀ k, ell k ≤ (W k).card) :
    Nonempty (PrescribedFamilySlicePoint W ell) := by
  apply Nonempty.map (prescribedFamilySliceEquiv W hdisj ell)
  apply prescribedProductSlicePoint_nonempty
  intro k
  simpa only [prescribedFamilyPartition_fiber_castSucc W hdisj k] using hell k

/-- Exact size of a prescribed family slice: independent choices inside the
disjoint blocks and an arbitrary choice on their complement. -/
lemma card_prescribedFamilySlicePoint {n m : ℕ}
    (W : Fin m → Finset (Fin n))
    (hdisj : ∀ i j, i ≠ j → Disjoint (W i) (W j))
    (ell : Fin m → ℕ) :
    Fintype.card (PrescribedFamilySlicePoint W ell) =
      (∏ k : Fin m, (W k).card.choose (ell k)) *
        2 ^ (n - (Finset.univ.biUnion W).card) := by
  rw [Fintype.card_congr (prescribedFamilySliceEquiv W hdisj ell).symm]
  rw [Fintype.card_congr (partialProductSliceEquiv
    (prescribedFamilyPartition W) ell).symm]
  rw [card_partialProductSlice]
  rw [prescribedFamilyPartition_last_card]
  congr 1
  apply Finset.prod_congr rfl
  intro k _hk
  rw [prescribedFamilyPartition_fiber_castSucc W hdisj k]

/-- KSSS Lemma 13.6(2) at the exact finite-probability level for a
pairwise-disjoint prescribed family. -/
lemma prescribedFamilySlice_centered_window_lower {n m : ℕ}
    (W : Fin m → Finset (Fin n))
    (hdisj : ∀ i j, i ≠ j → Disjoint (W i) (W j))
    (ell : Fin m → ℕ) (hell : ∀ k, ell k ≤ (W k).card)
    (G : SimpleGraph (Fin n)) (e₀ : ℝ) (c : Fin n → ℝ)
    (R : ℝ) (hR : 1 ≤ R) (hc : ∀ v, |c v| ≤ R * n)
    (A B D t : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D) (ht : 0 < t)
    (hellCenter : ∀ k,
      |(ell k : ℝ) - ((W k).card : ℝ) / 2| ≤ A) :
    let outside := (Finset.univ : Finset (Fin n)) \ Finset.univ.biUnion W
    letI : Nonempty (PrescribedFamilySlicePoint W ell) :=
      prescribedFamilySlicePoint_nonempty W hdisj ell hell
    1 - (R ^ 2 * n ^ 3) / t ^ 2 -
        ((∑ k : Fin m, binomialTailBound (W k) D) +
          binomialTailBound outside D) -
        binomialTailBound outside B ≤
      uniformProbability (fun S : PrescribedFamilySlicePoint W ell ↦
        |perturbedEdgePolynomial G e₀ c S.1 -
          expectation (1 / 2 : ℝ) (perturbedEdgePolynomial G e₀ c)| <
            t + (((m + 1 : ℕ) : ℝ) * (max A B + D)) *
              ((R + 1) * n)) := by
  let P := prescribedFamilyPartition W
  let outside := (Finset.univ : Finset (Fin n)) \ Finset.univ.biUnion W
  have hellP : ∀ k, ell k ≤ (P.fiber k.castSucc).card := by
    intro k
    simpa only [P, prescribedFamilyPartition_fiber_castSucc W hdisj k] using hell k
  let e : ∀ k, Fin (P.fiber k).card ≃ ↑(P.fiber k) := fun k ↦ by
    simpa only [Fintype.card_coe] using (Fintype.equivFin ↑(P.fiber k)).symm
  letI : Nonempty (PrescribedProductSlicePoint P ell) :=
    prescribedProductSlicePoint_nonempty P ell hellP
  letI : Nonempty (PrescribedFamilySlicePoint W ell) :=
    prescribedFamilySlicePoint_nonempty W hdisj ell hell
  have hcenterP : ∀ k,
      |(ell k : ℝ) - ((P.fiber k.castSucc).card : ℝ) / 2| ≤ A := by
    intro k
    simpa only [P, prescribedFamilyPartition_fiber_castSucc W hdisj k] using
      hellCenter k
  have hbase := prescribedProductSlice_centered_window_lower
    P ell hellP e G e₀ c R hR hc A B D t hB hD ht hcenterP
  have hsum :
      (∑ k : Fin (m + 1), binomialTailBound (P.fiber k) D) =
        (∑ k : Fin m, binomialTailBound (W k) D) +
          binomialTailBound outside D := by
    rw [Fin.sum_univ_castSucc]
    congr 1
    · apply Finset.sum_congr rfl
      intro k _hk
      rw [show P.fiber k.castSucc = W k by
        exact prescribedFamilyPartition_fiber_castSucc W hdisj k]
    · rw [show P.fiber (Fin.last m) = outside by
        exact prescribedFamilyPartition_fiber_last W]
  have hlast : P.fiber (Fin.last m) = outside := by
    exact prescribedFamilyPartition_fiber_last W
  rw [← uniformProbability_comp_equiv (prescribedFamilySliceEquiv W hdisj ell)
    (fun S : PrescribedFamilySlicePoint W ell ↦
      |perturbedEdgePolynomial G e₀ c S.1 -
        expectation (1 / 2 : ℝ) (perturbedEdgePolynomial G e₀ c)| <
          t + (((m + 1 : ℕ) : ℝ) * (max A B + D)) * ((R + 1) * n))]
  have hfun :
      (fun S : PrescribedProductSlicePoint P ell ↦
        |perturbedEdgePolynomial G e₀ c S.1 -
          expectation (1 / 2 : ℝ) (perturbedEdgePolynomial G e₀ c)| <
            t + (((m + 1 : ℕ) : ℝ) * (max A B + D)) * ((R + 1) * n)) =
      (fun S : PrescribedProductSlicePoint P ell ↦
        |perturbedEdgePolynomial G e₀ c
            ((prescribedFamilySliceEquiv W hdisj ell) S).1 -
          expectation (1 / 2 : ℝ) (perturbedEdgePolynomial G e₀ c)| <
            t + (((m + 1 : ℕ) : ℝ) * (max A B + D)) * ((R + 1) * n)) := by
    funext S
    rfl
  rw [← hfun]
  simpa only [P, outside, hsum, hlast] using hbase

/-- Clearing the uniform denominator turns a probability lower bound into
an exact finite-cardinality lower bound. -/
lemma card_filter_ge_of_uniformProbability_ge {Ω : Type*}
    [Fintype Ω] [Nonempty Ω] (P : Ω → Prop) (q : ℝ)
    (h : q ≤ uniformProbability P) :
    q * Fintype.card Ω ≤ ((Finset.univ.filter P).card : ℝ) := by
  rw [uniformProbability] at h
  rwa [le_div_iff₀ (by exact_mod_cast Fintype.card_pos)] at h

/-- Counting form of the prescribed-family finite probability estimate in
KSSS Lemma 13.6(2).  The factor multiplying the probability lower bound is
the exact number of subsets with the prescribed intersections. -/
lemma card_prescribedFamilySlice_centered_window_lower {n m : ℕ}
    (W : Fin m → Finset (Fin n))
    (hdisj : ∀ i j, i ≠ j → Disjoint (W i) (W j))
    (ell : Fin m → ℕ) (hell : ∀ k, ell k ≤ (W k).card)
    (G : SimpleGraph (Fin n)) (e₀ : ℝ) (c : Fin n → ℝ)
    (R : ℝ) (hR : 1 ≤ R) (hc : ∀ v, |c v| ≤ R * n)
    (A B D t : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D) (ht : 0 < t)
    (hellCenter : ∀ k,
      |(ell k : ℝ) - ((W k).card : ℝ) / 2| ≤ A) :
    let outside := (Finset.univ : Finset (Fin n)) \ Finset.univ.biUnion W
    let q := 1 - (R ^ 2 * n ^ 3) / t ^ 2 -
        ((∑ k : Fin m, binomialTailBound (W k) D) +
          binomialTailBound outside D) -
        binomialTailBound outside B
    letI : Nonempty (PrescribedFamilySlicePoint W ell) :=
      prescribedFamilySlicePoint_nonempty W hdisj ell hell
    q * (((∏ k : Fin m, (W k).card.choose (ell k)) *
        2 ^ (n - (Finset.univ.biUnion W).card) : ℕ) : ℝ) ≤
      (((Finset.univ : Finset (PrescribedFamilySlicePoint W ell)).filter
        fun S ↦
          |perturbedEdgePolynomial G e₀ c S.1 -
            expectation (1 / 2 : ℝ) (perturbedEdgePolynomial G e₀ c)| <
              t + (((m + 1 : ℕ) : ℝ) * (max A B + D)) *
                ((R + 1) * n)).card : ℝ) := by
  let outside := (Finset.univ : Finset (Fin n)) \ Finset.univ.biUnion W
  let q := 1 - (R ^ 2 * n ^ 3) / t ^ 2 -
      ((∑ k : Fin m, binomialTailBound (W k) D) +
        binomialTailBound outside D) -
      binomialTailBound outside B
  letI : Nonempty (PrescribedFamilySlicePoint W ell) :=
    prescribedFamilySlicePoint_nonempty W hdisj ell hell
  let P := fun S : PrescribedFamilySlicePoint W ell ↦
    |perturbedEdgePolynomial G e₀ c S.1 -
      expectation (1 / 2 : ℝ) (perturbedEdgePolynomial G e₀ c)| <
        t + (((m + 1 : ℕ) : ℝ) * (max A B + D)) * ((R + 1) * n)
  have hprob : q ≤ uniformProbability P := by
    simpa only [q, P, outside] using
      prescribedFamilySlice_centered_window_lower W hdisj ell hell
        G e₀ c R hR hc A B D t hB hD ht hellCenter
  have hcount := card_filter_ge_of_uniformProbability_ge P q hprob
  rw [card_prescribedFamilySlicePoint W hdisj ell] at hcount
  simpa only [q, P, outside] using hcount

/-- Replacing every prescribed binomial coefficient by its explicit
near-central lower bound preserves any nonnegative state-count estimate. -/
lemma card_prescribedFamilySlice_near_lower {n m D : ℕ}
    (W : Fin m → Finset (Fin n))
    (ell : Fin m → ℕ) (hell : ∀ k, ell k ≤ (W k).card)
    (hWpos : ∀ k, 1 ≤ (W k).card)
    (hD : ∀ k, 8 * D ≤ (W k).card / 2)
    (hellNear : ∀ k, Nat.dist (ell k) ((W k).card / 2) ≤ D)
    (q : ℝ) (hq : 0 ≤ q) (E : PrescribedFamilySlicePoint W ell → Prop)
    (hcount :
      q * (((∏ k : Fin m, (W k).card.choose (ell k)) *
          2 ^ (n - (Finset.univ.biUnion W).card) : ℕ) : ℝ) ≤
        (((Finset.univ : Finset (PrescribedFamilySlicePoint W ell)).filter E).card : ℝ)) :
    q * ((∏ k : Fin m,
          (((2 : ℝ) ^ (W k).card / (8 * Real.sqrt (W k).card)) *
            Real.exp (-8 * (D : ℝ) ^ 2 / ((W k).card / 2 : ℕ)))) *
        (2 : ℝ) ^ (n - (Finset.univ.biUnion W).card)) ≤
      (((Finset.univ : Finset (PrescribedFamilySlicePoint W ell)).filter E).card : ℝ) := by
  have hprod := prod_choose_near_middle_lower
    (fun k : Fin m ↦ (W k).card) ell D hWpos hD hell hellNear
  have hfree : (0 : ℝ) ≤ (2 : ℝ) ^
      (n - (Finset.univ.biUnion W).card) := by positivity
  have hscaled :
      (∏ k : Fin m,
          (((2 : ℝ) ^ (W k).card / (8 * Real.sqrt (W k).card)) *
            Real.exp (-8 * (D : ℝ) ^ 2 / ((W k).card / 2 : ℕ)))) *
          (2 : ℝ) ^ (n - (Finset.univ.biUnion W).card) ≤
        (∏ k : Fin m, (Nat.choose (W k).card (ell k) : ℝ)) *
          (2 : ℝ) ^ (n - (Finset.univ.biUnion W).card) :=
    mul_le_mul_of_nonneg_right hprod hfree
  calc
    q * ((∏ k : Fin m,
          (((2 : ℝ) ^ (W k).card / (8 * Real.sqrt (W k).card)) *
            Real.exp (-8 * (D : ℝ) ^ 2 / ((W k).card / 2 : ℕ)))) *
        (2 : ℝ) ^ (n - (Finset.univ.biUnion W).card)) ≤
        q * ((∏ k : Fin m, (Nat.choose (W k).card (ell k) : ℝ)) *
          (2 : ℝ) ^ (n - (Finset.univ.biUnion W).card)) :=
      mul_le_mul_of_nonneg_left hscaled hq
    _ = q * (((∏ k : Fin m, (W k).card.choose (ell k)) *
        2 ^ (n - (Finset.univ.biUnion W).card) : ℕ) : ℝ) := by
      push_cast
      rfl
    _ ≤ (((Finset.univ : Finset (PrescribedFamilySlicePoint W ell)).filter E).card : ℝ) :=
      hcount

/-- The powers of two from disjoint prescribed blocks and their free
complement combine to the full Boolean-cube factor. -/
lemma prescribed_family_lower_factor_eq {n m : ℕ}
    (W : Fin m → Finset (Fin n))
    (hdisj : ∀ i j, i ≠ j → Disjoint (W i) (W j)) (C : ℝ) :
    (∏ k : Fin m, (((2 : ℝ) ^ (W k).card / (8 * Real.sqrt n)) *
        Real.exp (-8 * C))) *
      (2 : ℝ) ^ (n - (Finset.univ.biUnion W).card) =
    (2 : ℝ) ^ n *
      (Real.exp (-8 * C) / (8 * Real.sqrt n)) ^ m := by
  have hWcard : (Finset.univ.biUnion W).card = ∑ k, (W k).card := by
    apply Finset.card_biUnion
    intro i _hi j _hj hij
    exact hdisj i j hij
  have hWle : (Finset.univ.biUnion W).card ≤ n := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_le_card (Finset.subset_univ (Finset.univ.biUnion W))
  simp_rw [show ∀ k : Fin m,
      ((2 : ℝ) ^ (W k).card / (8 * Real.sqrt n)) * Real.exp (-8 * C) =
        (2 : ℝ) ^ (W k).card *
          (Real.exp (-8 * C) / (8 * Real.sqrt n)) by
    intro k
    ring]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  calc
    (2 : ℝ) ^ (∑ i, (W i).card) *
          (Real.exp (-8 * C) / (8 * Real.sqrt n)) ^ m *
        (2 : ℝ) ^ (n - (Finset.univ.biUnion W).card) =
        ((2 : ℝ) ^ (∑ i, (W i).card) *
          (2 : ℝ) ^ (n - (Finset.univ.biUnion W).card)) *
            (Real.exp (-8 * C) / (8 * Real.sqrt n)) ^ m := by ring
    _ = (2 : ℝ) ^ n *
        (Real.exp (-8 * C) / (8 * Real.sqrt n)) ^ m := by
      rw [← pow_add, ← hWcard, Nat.add_sub_of_le hWle]

/-- Source-shaped state-count lower bound from KSSS Lemma 13.6(2): for
`m` disjoint near-balanced blocks, the prescribed event has the full
`2^n n^{-m/2}` scale, with an explicit Gaussian constant. -/
lemma card_prescribedFamilySlice_ambient_lower {n m D : ℕ}
    (W : Fin m → Finset (Fin n))
    (hdisj : ∀ i j, i ≠ j → Disjoint (W i) (W j))
    (ell : Fin m → ℕ) (hell : ∀ k, ell k ≤ (W k).card)
    (hWpos : ∀ k, 1 ≤ (W k).card)
    (hhalf : ∀ k, 1 ≤ (W k).card / 2)
    (hD : ∀ k, 8 * D ≤ (W k).card / 2)
    (hellNear : ∀ k, Nat.dist (ell k) ((W k).card / 2) ≤ D)
    (C q : ℝ) (hquad : ∀ k, (D : ℝ) ^ 2 ≤ C * ((W k).card / 2 : ℕ))
    (hq : 0 ≤ q) (E : PrescribedFamilySlicePoint W ell → Prop)
    (hcount :
      q * (((∏ k : Fin m, (W k).card.choose (ell k)) *
          2 ^ (n - (Finset.univ.biUnion W).card) : ℕ) : ℝ) ≤
        (((Finset.univ : Finset (PrescribedFamilySlicePoint W ell)).filter E).card : ℝ)) :
    q * ((2 : ℝ) ^ n *
        (Real.exp (-8 * C) / (8 * Real.sqrt n)) ^ m) ≤
      (((Finset.univ : Finset (PrescribedFamilySlicePoint W ell)).filter E).card : ℝ) := by
  have hWn : ∀ k, (W k).card ≤ n := by
    intro k
    simpa only [Finset.card_univ, Fintype.card_fin] using
      Finset.card_le_card (Finset.subset_univ (W k))
  have hprod := prod_choose_near_middle_lower_of_ambient n
    (fun k : Fin m ↦ (W k).card) ell D C hWpos hWn hhalf hD hell hellNear hquad
  have hfree : (0 : ℝ) ≤ (2 : ℝ) ^
      (n - (Finset.univ.biUnion W).card) := by positivity
  have hscaled :
      (∏ k : Fin m, (((2 : ℝ) ^ (W k).card / (8 * Real.sqrt n)) *
          Real.exp (-8 * C))) *
          (2 : ℝ) ^ (n - (Finset.univ.biUnion W).card) ≤
        (∏ k : Fin m, (Nat.choose (W k).card (ell k) : ℝ)) *
          (2 : ℝ) ^ (n - (Finset.univ.biUnion W).card) :=
    mul_le_mul_of_nonneg_right hprod hfree
  calc
    q * ((2 : ℝ) ^ n *
        (Real.exp (-8 * C) / (8 * Real.sqrt n)) ^ m) =
        q * ((∏ k : Fin m,
            (((2 : ℝ) ^ (W k).card / (8 * Real.sqrt n)) *
              Real.exp (-8 * C))) *
          (2 : ℝ) ^ (n - (Finset.univ.biUnion W).card)) := by
      rw [prescribed_family_lower_factor_eq W hdisj C]
    _ ≤ q * ((∏ k : Fin m, (Nat.choose (W k).card (ell k) : ℝ)) *
          (2 : ℝ) ^ (n - (Finset.univ.biUnion W).card)) :=
      mul_le_mul_of_nonneg_left hscaled hq
    _ = q * (((∏ k : Fin m, (W k).card.choose (ell k)) *
        2 ^ (n - (Finset.univ.biUnion W).card) : ℕ) : ℝ) := by
      push_cast
      rfl
    _ ≤ (((Finset.univ : Finset (PrescribedFamilySlicePoint W ell)).filter E).card : ℝ) :=
      hcount

end ProductSliceCubeCoupling

end Erdos88.Switching
