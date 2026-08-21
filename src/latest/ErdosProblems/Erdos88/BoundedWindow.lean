import ErdosProblems.Erdos88.SwitchingLemma136

/-!
# The graph-level bounded-window interface

This file records the exact source-facing statement of KSSS Theorem 3.1 in
a finite-type invariant form.  The radius is normalized to be a positive
natural number; this is the form used in the switching argument after the
standard finite enlargement/covering of the real radius in the paper.

No instance of the theorem is assumed here.  The elementary declarations
below only convert its probability conclusions into finite cardinality
bounds, making the remaining graph-specific analytic input explicit.
-/

open scoped BigOperators

namespace Erdos88

/-- A finite-type invariant version of `RamseyFree`. -/
def FiniteRamseyFree {V : Type*} [Fintype V]
    (C : ℝ) (G : SimpleGraph V) : Prop :=
  ∀ S : Finset V,
    (G.IsClique (S : Set V) ∨ G.IsIndepSet (S : Set V)) →
      (S.card : ℝ) < C * Real.logb 2 (Fintype.card V)

lemma finiteRamseyFree_fin_iff {n : ℕ} (C : ℝ)
    (G : SimpleGraph (Fin n)) :
    FiniteRamseyFree C G ↔ RamseyFree C G := by
  simp only [FiniteRamseyFree, RamseyFree, Fintype.card_fin]

/-- Ramsey-freeness passes to an induced finite subtype whenever the target
logarithmic threshold dominates the ambient one. -/
lemma finiteRamseyFree_induce_of_threshold {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) (A : Finset V) {C D : ℝ}
    (hG : FiniteRamseyFree C G)
    (hthreshold : C * Real.logb 2 (Fintype.card V) ≤
      D * Real.logb 2 A.card) :
    FiniteRamseyFree D (G.induce (A : Set V)) := by
  intro T hT
  let S : Finset V := T.image Subtype.val
  have hcard : S.card = T.card := by
    exact Finset.card_image_iff.mpr Subtype.val_injective.injOn
  have hhom : G.IsClique (S : Set V) ∨ G.IsIndepSet (S : Set V) := by
    rcases hT with hclique | hindep
    · left
      intro x hx y hy hxy
      simp only [S, Finset.coe_image, Set.mem_image] at hx hy
      obtain ⟨x', hx', rfl⟩ := hx
      obtain ⟨y', hy', rfl⟩ := hy
      exact hclique hx' hy' (fun h ↦ hxy (congrArg Subtype.val h))
    · right
      intro x hx y hy hxy hadj
      simp only [S, Finset.coe_image, Set.mem_image] at hx hy
      obtain ⟨x', hx', rfl⟩ := hx
      obtain ⟨y', hy', rfl⟩ := hy
      exact hindep hx' hy' (fun h ↦ hxy (congrArg Subtype.val h)) hadj
  have hlt := hG S hhom
  rw [← hcard]
  apply hlt.trans_le
  rw [card_subtype_coe_finset A]
  exact hthreshold

/-- A globally `C`-Ramsey graph remains `2 C`-Ramsey on any induced
reservoir of size at least the ambient square root. -/
lemma finiteRamseyFree_induce_of_sqrt {n : ℕ}
    (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) {C : ℝ}
    (hC : 0 < C) (hn : 1 ≤ n) (hG : RamseyFree C G)
    (hA : Real.sqrt n ≤ (A.card : ℝ)) :
    FiniteRamseyFree (2 * C) (G.induce (A : Set (Fin n))) := by
  apply finiteRamseyFree_induce_of_threshold G A
  · exact (finiteRamseyFree_fin_iff C G).2 hG
  · have hnpos : (0 : ℝ) < n := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
    have hsqrtPos : 0 < Real.sqrt n := Real.sqrt_pos.2 hnpos
    have hlogMono :
        Real.logb 2 (Real.sqrt n) ≤ Real.logb 2 (A.card : ℝ) :=
      Real.logb_le_logb_of_le (by norm_num) hsqrtPos hA
    have hlogSqrt :
        Real.logb 2 (Real.sqrt n) =
          (1 / 2 : ℝ) * Real.logb 2 n := by
      rw [Real.logb, Real.logb, Real.log_sqrt hnpos.le]
      ring
    rw [hlogSqrt] at hlogMono
    have hscaled := mul_le_mul_of_nonneg_left hlogMono hC.le
    simp only [Fintype.card_fin]
    calc
      C * Real.logb 2 n =
          2 * (C * ((1 / 2 : ℝ) * Real.logb 2 n)) := by ring
      _ ≤ 2 * (C * Real.logb 2 (A.card : ℝ)) := by gcongr
      _ = (2 * C) * Real.logb 2 (A.card : ℝ) := by ring

/-- Kwan--Sah--Sauermann--Sawhney, Theorem 3.1, with a common integral
window radius.  The upper constant may depend on `C,H`; the lower constant
may additionally depend on the bulk parameter `A`, while the radius depends
only on `C`. -/
def KSSSBoundedWindow : Prop :=
  ∀ C : ℝ, 0 < C →
    ∃ B : ℕ, 0 < B ∧
      (∀ H : ℝ, 0 < H →
        ∃ K : ℝ, 0 < K ∧ ∃ N : ℕ,
          ∀ (V : Type) [Fintype V] [DecidableEq V]
            (G : SimpleGraph V) [DecidableRel G.Adj],
            N ≤ Fintype.card V → FiniteRamseyFree C G →
            ∀ (e₀ : ℝ) (c : V → ℝ),
              (∀ v, 0 ≤ c v ∧ c v ≤ H * Fintype.card V) →
              ∀ x : ℤ,
                Probability.eventProbability (1 / 2 : ℝ) (fun U ↦
                    |Probability.perturbedEdgePolynomial G e₀ c U - x| ≤ B) ≤
                  K * (Fintype.card V : ℝ) ^ (-(3 / 2 : ℝ))) ∧
      (∀ H A : ℝ, 0 < H → 0 < A →
        ∃ kappa : ℝ, 0 < kappa ∧ ∃ N : ℕ,
          ∀ (V : Type) [Fintype V] [DecidableEq V]
            (G : SimpleGraph V) [DecidableRel G.Adj],
            N ≤ Fintype.card V → FiniteRamseyFree C G →
            ∀ (e₀ : ℝ) (c : V → ℝ),
              (∀ v, 0 ≤ c v ∧ c v ≤ H * Fintype.card V) →
              ∀ x : ℤ,
                |(x : ℝ) - Probability.expectation (1 / 2 : ℝ)
                    (Probability.perturbedEdgePolynomial G e₀ c)| ≤
                    A * (Fintype.card V : ℝ) ^ (3 / 2 : ℝ) →
                kappa * (Fintype.card V : ℝ) ^ (-(3 / 2 : ℝ)) ≤
                  Probability.eventProbability (1 / 2 : ℝ) (fun U ↦
                    |Probability.perturbedEdgePolynomial G e₀ c U - x| ≤ B))

namespace BoundedWindow

/-- Forget the membership proofs in a subset of the subtype cut out by `A`. -/
def subtypeSubsetImage {V : Type*} [DecidableEq V] (A : Finset V)
    (R : Finset (A : Set V)) : Finset V :=
  R.image Subtype.val

lemma subtypeSubsetImage_subset {V : Type*} [DecidableEq V]
    (A : Finset V) (R : Finset (A : Set V)) :
    subtypeSubsetImage A R ⊆ A := by
  intro x hx
  simp only [subtypeSubsetImage, Finset.mem_image] at hx
  obtain ⟨y, _hy, rfl⟩ := hx
  exact y.property

/-- Subsets of the subtype cut out by `A` and members of `A.powerset` have
the same filtered cardinality under the forgetful map. -/
lemma card_filter_subtypeSubsetImage {V : Type*} [Fintype V]
    [DecidableEq V] (A : Finset V) (P : Finset V → Prop)
    [DecidablePred P] :
    ((Finset.univ : Finset (Finset (A : Set V))).filter fun R ↦
        P (subtypeSubsetImage A R)).card =
      (A.powerset.filter P).card := by
  classical
  apply Finset.card_bij (fun R _hR ↦ subtypeSubsetImage A R)
  · intro R hR
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hR ⊢
    exact ⟨Finset.mem_powerset.mpr (subtypeSubsetImage_subset A R), hR⟩
  · intro R₁ _hR₁ R₂ _hR₂ hEq
    exact Finset.image_injective Subtype.val_injective hEq
  · intro S hS
    have hS' := Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
    let emb : (S : Set V) ↪ (A : Set V) :=
      ⟨fun x ↦ ⟨x.1, hS' x.2⟩,
        fun x y h ↦
          Subtype.ext (congrArg (fun z : (A : Set V) ↦ z.1) h)⟩
    let R : Finset (A : Set V) := S.attach.map emb
    have hEq : subtypeSubsetImage A R = S := by
      ext x
      simp [subtypeSubsetImage, R, emb]
      exact fun hx ↦ hS' hx
    refine ⟨R, ?_, hEq⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hEq]
    exact (Finset.mem_filter.mp hS).2

/-- Inducing on `A` and then on a subtype subset counts the same edges as
forgetting the subtype proofs first. -/
lemma inducedEdges_subtypeSubsetImage {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (R : Finset (A : Set V)) :
    inducedEdges (G.induce (A : Set V)) R =
      inducedEdges G (subtypeSubsetImage A R) := by
  let H := G.induce (A : Set V)
  let sA : Set A := R
  let sV : Set V := Subtype.val '' sA
  let ev : sA ≃ sV := Equiv.Set.image Subtype.val sA Subtype.val_injective
  let iso : H.induce sA ≃g G.induce sV :=
    { toEquiv := ev
      map_rel_iff' := by intro x y; rfl }
  have hU : (↑(subtypeSubsetImage A R) : Set V) = sV := by
    ext x
    simp [subtypeSubsetImage, sV, sA]
  let iso' : H.induce sA ≃g
      G.induce (↑(subtypeSubsetImage A R) : Set V) := by
    rw [hU]
    exact iso
  rw [inducedEdges_eq_card_edgeFinset_induce,
    inducedEdges_eq_card_edgeFinset_induce]
  exact iso'.card_edgeFinset_eq

lemma probability_inducedEdgeCount_eq_inducedEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    Probability.inducedEdgeCount G S = inducedEdges G S := by
  rw [Probability.inducedEdgeCount, inducedEdges_eq_card_filter]

/-- A perturbed edge polynomial on an induced subtype is exactly the
ambient polynomial evaluated after forgetting subtype proofs. -/
lemma perturbedEdgePolynomial_induce_subtypeSubsetImage
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (e₀ : ℝ) (c : V → ℝ)
    (R : Finset (A : Set V)) :
    Probability.perturbedEdgePolynomial (G.induce (A : Set V)) e₀
        (fun v ↦ c v.1) R =
      Probability.perturbedEdgePolynomial G e₀ c
        (subtypeSubsetImage A R) := by
  rw [Probability.perturbedEdgePolynomial,
    Probability.perturbedEdgePolynomial,
    Probability.edgePolynomial_eq_inducedEdgeCount,
    Probability.edgePolynomial_eq_inducedEdgeCount]
  rw [probability_inducedEdgeCount_eq_inducedEdges,
    probability_inducedEdgeCount_eq_inducedEdges,
    inducedEdges_subtypeSubsetImage]
  congr 1
  classical
  calc
    (∑ v : (A : Set V), c v.1 * Probability.bit v R) =
        ∑ v ∈ R, c v.1 := by
      simp only [Probability.bit]
      simp_rw [mul_ite, mul_one, mul_zero]
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter,
        Finset.univ_inter]
    _ = ∑ v ∈ subtypeSubsetImage A R, c v := by
      rw [subtypeSubsetImage]
      exact (Finset.sum_image Subtype.val_injective.injOn).symm
    _ = ∑ v : V, c v *
        Probability.bit v (subtypeSubsetImage A R) := by
      simp only [Probability.bit]
      simp_rw [mul_ite, mul_one, mul_zero]
      rw [← Finset.sum_filter, Finset.filter_mem_eq_inter,
        Finset.univ_inter]

/-- The unbiased Bernoulli probability of an event is its cardinality
divided by the size of the Boolean cube. -/
lemma eventProbability_half_eq_card_div {V : Type*} [Fintype V]
    (P : Finset V → Prop) [DecidablePred P] :
    Probability.eventProbability (1 / 2 : ℝ) P =
      (((Finset.univ : Finset (Finset V)).filter P).card : ℝ) /
        (2 : ℝ) ^ Fintype.card V := by
  classical
  unfold Probability.eventProbability Probability.expectation
  simp_rw [Switching.bernoulliWeight_half_switching]
  rw [← Finset.mul_sum]
  have hsum :
      (∑ W : Finset V, if P W then (1 : ℝ) else 0) =
        (((Finset.univ : Finset (Finset V)).filter P).card : ℝ) := by
    exact_mod_cast
      (Finset.sum_boole (R := ℕ) P (Finset.univ : Finset (Finset V)))
  rw [hsum, one_div, inv_pow, div_eq_mul_inv]
  ring

/-- Counting form of the lower half of the bounded-window theorem. -/
lemma card_window_ge_of_probability {V : Type*} [Fintype V]
    (P : Finset V → Prop) [DecidablePred P] (q : ℝ)
    (h : q ≤ Probability.eventProbability (1 / 2 : ℝ) P) :
    q * (2 : ℝ) ^ Fintype.card V ≤
      (((Finset.univ : Finset (Finset V)).filter P).card : ℝ) := by
  rw [eventProbability_half_eq_card_div] at h
  exact (le_div_iff₀ (by positivity)).mp h

/-- Counting form of the upper half of the bounded-window theorem. -/
lemma card_window_le_of_probability {V : Type*} [Fintype V]
    (P : Finset V → Prop) [DecidablePred P] (q : ℝ)
    (h : Probability.eventProbability (1 / 2 : ℝ) P ≤ q) :
    (((Finset.univ : Finset (Finset V)).filter P).card : ℝ) ≤
      q * (2 : ℝ) ^ Fintype.card V := by
  rw [eventProbability_half_eq_card_div] at h
  exact (div_le_iff₀ (by positivity)).mp h

/-- Apply a lower window-probability estimate on the induced subtype and
transport it to an exact count in the ambient powerset. -/
lemma card_induced_window_ge_of_probability
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (e₀ : ℝ) (c : V → ℝ) (x : ℤ) (B : ℕ) (q : ℝ)
    (h : q ≤ Probability.eventProbability (1 / 2 : ℝ)
      (fun R : Finset (A : Set V) ↦
        |Probability.perturbedEdgePolynomial (G.induce (A : Set V)) e₀
          (fun v ↦ c v.1) R - x| ≤ B)) :
    q * (2 : ℝ) ^ A.card ≤
      ((A.powerset.filter fun R ↦
        |Probability.perturbedEdgePolynomial G e₀ c R - x| ≤ B).card : ℝ) := by
  classical
  let P : Finset V → Prop := fun R ↦
    |Probability.perturbedEdgePolynomial G e₀ c R - x| ≤ B
  have hcount := card_window_ge_of_probability
    (fun R : Finset (A : Set V) ↦
      |Probability.perturbedEdgePolynomial (G.induce (A : Set V)) e₀
        (fun v ↦ c v.1) R - x| ≤ B) q h
  have hfilter :
      ((Finset.univ : Finset (Finset (A : Set V))).filter fun R ↦
        |Probability.perturbedEdgePolynomial (G.induce (A : Set V)) e₀
          (fun v ↦ c v.1) R - x| ≤ B).card =
        (A.powerset.filter P).card := by
    rw [show ((Finset.univ : Finset (Finset (A : Set V))).filter fun R ↦
        |Probability.perturbedEdgePolynomial (G.induce (A : Set V)) e₀
          (fun v ↦ c v.1) R - x| ≤ B) =
      ((Finset.univ : Finset (Finset (A : Set V))).filter fun R ↦
        P (subtypeSubsetImage A R)) by
      apply Finset.filter_congr
      intro R _hR
      rw [perturbedEdgePolynomial_induce_subtypeSubsetImage]]
    exact card_filter_subtypeSubsetImage A P
  simpa only [card_subtype_coe_finset A, hfilter, P] using hcount

/-- Upper-count companion of `card_induced_window_ge_of_probability`. -/
lemma card_induced_window_le_of_probability
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (A : Finset V) (e₀ : ℝ) (c : V → ℝ) (x : ℤ) (B : ℕ) (q : ℝ)
    (h : Probability.eventProbability (1 / 2 : ℝ)
      (fun R : Finset (A : Set V) ↦
        |Probability.perturbedEdgePolynomial (G.induce (A : Set V)) e₀
          (fun v ↦ c v.1) R - x| ≤ B) ≤ q) :
    ((A.powerset.filter fun R ↦
        |Probability.perturbedEdgePolynomial G e₀ c R - x| ≤ B).card : ℝ) ≤
      q * (2 : ℝ) ^ A.card := by
  classical
  let P : Finset V → Prop := fun R ↦
    |Probability.perturbedEdgePolynomial G e₀ c R - x| ≤ B
  have hcount := card_window_le_of_probability
    (fun R : Finset (A : Set V) ↦
      |Probability.perturbedEdgePolynomial (G.induce (A : Set V)) e₀
        (fun v ↦ c v.1) R - x| ≤ B) q h
  have hfilter :
      ((Finset.univ : Finset (Finset (A : Set V))).filter fun R ↦
        |Probability.perturbedEdgePolynomial (G.induce (A : Set V)) e₀
          (fun v ↦ c v.1) R - x| ≤ B).card =
        (A.powerset.filter P).card := by
    rw [show ((Finset.univ : Finset (Finset (A : Set V))).filter fun R ↦
        |Probability.perturbedEdgePolynomial (G.induce (A : Set V)) e₀
          (fun v ↦ c v.1) R - x| ≤ B) =
      ((Finset.univ : Finset (Finset (A : Set V))).filter fun R ↦
        P (subtypeSubsetImage A R)) by
      apply Finset.filter_congr
      intro R _hR
      rw [perturbedEdgePolynomial_induce_subtypeSubsetImage]]
    exact card_filter_subtypeSubsetImage A P
  simpa only [card_subtype_coe_finset A, hfilter, P] using hcount

end BoundedWindow
end Erdos88
