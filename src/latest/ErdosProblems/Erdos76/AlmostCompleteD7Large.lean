/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import ErdosProblems.Erdos76.AlmostCompleteD7Correction

/-!
# The large-universal-set branch of D7

This file combines the coherent universal-vertex deletion packings with the
explicit correction from `AlmostCompleteD7Correction`.
-/

open Finset
open scoped BigOperators

namespace Erdos76

noncomputable section

attribute [local instance] Classical.propDecidable

variable {A : Type} [Fintype A] [DecidableEq A]

lemma sum_ite_eq_zero_else {B : Type} [Fintype B] [DecidableEq B]
    (y : B) (c : ℝ) :
    (∑ z : B, if z = y then 0 else c) =
      ((Fintype.card B : ℝ) - 1) * c := by
  simp only [Finset.sum_ite, Finset.filter_eq', Finset.filter_ne',
    Finset.sum_const, nsmul_eq_mul]
  have hcard : 1 ≤ Fintype.card B := Fintype.card_pos_iff.mpr ⟨y⟩
  rw [if_pos (Finset.mem_univ y), Finset.card_singleton,
    Finset.card_erase_of_mem (Finset.mem_univ y), Finset.card_univ]
  simp only [Nat.cast_one, one_mul, zero_add]
  have hcast : ((Fintype.card B - 1 : ℕ) : ℝ) =
      (Fintype.card B : ℝ) - 1 := by
    rw [Nat.cast_sub hcard, Nat.cast_one]
  rw [hcast]

lemma sum_ite_eq_zero_else_two {B : Type} [Fintype B] [DecidableEq B]
    (x y : B) (hxy : x ≠ y) (c : ℝ) :
    (∑ z : B, if z = x ∨ z = y then 0 else c) =
      ((Fintype.card B : ℝ) - 2) * c := by
  rw [Finset.sum_ite]
  have hfalse : (Finset.univ : Finset B).filter
      (fun z ↦ ¬(z = x ∨ z = y)) =
      ((Finset.univ : Finset B).erase x).erase y := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase]
    tauto
  have hcardFalse : ((Finset.univ : Finset B).filter
      (fun z ↦ ¬(z = x ∨ z = y))).card = Fintype.card B - 2 := by
    rw [hfalse, Finset.card_erase_of_mem]
    · rw [Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ]
      omega
    · exact Finset.mem_erase.mpr ⟨hxy.symm, Finset.mem_univ y⟩
  rw [Finset.sum_const_zero, zero_add, Finset.sum_const,
    hcardFalse]
  simp only [nsmul_eq_mul]
  have hcard : 2 ≤ Fintype.card B := by
    have hxmem : x ∈ ({x, y} : Finset B) := by simp
    have hymem : y ∈ ({x, y} : Finset B) := by simp
    have hpairs : ({x, y} : Finset B).card = 2 := by simp [hxy]
    have hsub : ({x, y} : Finset B) ⊆ Finset.univ := Finset.subset_univ _
    have := Finset.card_le_card hsub
    simpa [hpairs] using this
  rw [Nat.cast_sub hcard, Nat.cast_ofNat]

/-- A nonuniversal ambient vertex survives deletion of a universal vertex. -/
def d7NonUniversalDeletedEmbedding (G : SimpleGraph A)
    (z : ↑(universalVertices G)) :
    ↑(nonUniversalVertices G) ↪ ↑(d7DeletedFinset (A := A) (z : A)) where
  toFun u := d7DeletedVertex (z : A) (u : A) (by
    intro h
    have hu := mem_nonUniversalVertices.mp u.property
    have hz := mem_universalVertices.mp z.property
    rw [h, hz] at hu
    omega)
  inj' := by
    intro u v h
    apply Subtype.ext
    exact congrArg (fun q : ↑(d7DeletedFinset (A := A) (z : A)) ↦
      (q : A)) h

@[simp] lemma d7NonUniversalDeletedEmbedding_val (G : SimpleGraph A)
    (z : ↑(universalVertices G)) (u : ↑(nonUniversalVertices G)) :
    ((d7NonUniversalDeletedEmbedding G z u :
      ↑(d7DeletedFinset (A := A) (z : A))) : A) = (u : A) := rfl

/-- The load of a zero-extended induced weighting vanishes on an edge with
one endpoint outside the inducing set. -/
lemma fractionalEdgeLoad_extendInducedWeight_eq_zero_of_endpoint
    (G : SimpleGraph A) (S : Finset A) (w : Finset S → ℝ)
    (a b : A) (ha : a ∉ S) :
    fractionalEdgeLoad G (extendInducedWeight S w) s(a, b) = 0 := by
  unfold fractionalEdgeLoad
  apply Finset.sum_eq_zero
  intro t ht
  simp only [Finset.mem_filter] at ht
  rw [extendInducedWeight, dif_neg]
  intro hsub
  exact ha (hsub (Finset.mk_mem_sym2_iff.mp ht.2).1)

lemma fractionalEdgeLoad_d7LiftedWeight_eq_zero_of_endpoint
    (G : SimpleGraph A) (z y : A)
    (w : Finset (↑(d7DeletedFinset (A := A) z)) → ℝ) :
    fractionalEdgeLoad G (d7LiftedWeight z w) s(z, y) = 0 := by
  exact fractionalEdgeLoad_extendInducedWeight_eq_zero_of_endpoint
    G (d7DeletedFinset z) w z y (by simp [d7DeletedFinset])

lemma fractionalEdgeLoad_d7LiftedWeight_of_ne
    (G : SimpleGraph A) (z x y : A)
    (w : Finset (↑(d7DeletedFinset (A := A) z)) → ℝ)
    (hx : x ≠ z) (hy : y ≠ z) :
    fractionalEdgeLoad G (d7LiftedWeight z w) s(x, y) =
      fractionalEdgeLoad (d7DeletedGraph G z) w
        s(d7DeletedVertex z x hx, d7DeletedVertex z y hy) := by
  let e : Sym2 (↑(d7DeletedFinset (A := A) z)) :=
    s(d7DeletedVertex z x hx, d7DeletedVertex z y hy)
  have hmap : (inducedEmbedding (d7DeletedFinset z)).sym2Map e = s(x, y) := rfl
  unfold d7LiftedWeight
  rw [← hmap, fractionalEdgeLoad_extendInducedWeight]
  rfl

lemma fractionalEdgeLoad_add_separated_add_remaining_eq_one
    {B : Type} [Fintype B] [DecidableEq B]
    (H : SimpleGraph B) (w : Finset B → ℝ)
    (e : Sym2 B) (he : e ∈ H.edgeFinset) :
    fractionalEdgeLoad H w e + d7SeparatedUnit H w e +
        d7RemainingResidual H w e = 1 := by
  unfold d7RemainingResidual d7ResidualEdgeWeight
  rw [if_pos he]
  ring

lemma d7NonUniversalDeletedEdge_mem (G : SimpleGraph A)
    (z : ↑(universalVertices G))
    (e : Sym2 (↑(nonUniversalVertices G)))
    (he : e ∈ (G.induce
      (↑(nonUniversalVertices G) : Set A)).edgeFinset) :
    (d7NonUniversalDeletedEmbedding G z).sym2Map e ∈
      (d7DeletedGraph G (z : A)).edgeFinset := by
  rw [SimpleGraph.mem_edgeFinset] at he
  induction e using Sym2.inductionOn with
  | hf u v =>
      rw [SimpleGraph.mem_edgeFinset]
      change (d7DeletedGraph G (z : A)).Adj
        (d7NonUniversalDeletedEmbedding G z u)
        (d7NonUniversalDeletedEmbedding G z v)
      change G.Adj (u : A) (v : A)
      change G.Adj (u : A) (v : A) at he
      exact he

lemma d7MixedDeletedEdge_mem (G : SimpleGraph A)
    (z y : ↑(universalVertices G)) (hyz : (y : A) ≠ (z : A))
    (u : ↑(nonUniversalVertices G)) :
    s(d7NonUniversalDeletedEmbedding G z u,
      d7DeletedVertex (z : A) (y : A) hyz) ∈
        (d7DeletedGraph G (z : A)).edgeFinset := by
  rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
  change G.Adj (u : A) (y : A)
  exact (adj_of_mem_universalVertices G y.property (by
    intro h
    exact nonUniversalVertex_not_mem_universalVertices G u.property
      (h ▸ y.property))).symm

lemma d7UniversalDeletedEdge_mem (G : SimpleGraph A)
    (z x y : ↑(universalVertices G))
    (hxz : (x : A) ≠ (z : A)) (hyz : (y : A) ≠ (z : A))
    (hxy : (x : A) ≠ (y : A)) :
    s(d7DeletedVertex (z : A) (x : A) hxz,
      d7DeletedVertex (z : A) (y : A) hyz) ∈
        (d7DeletedGraph G (z : A)).edgeFinset := by
  rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
  change G.Adj (x : A) (y : A)
  exact adj_of_mem_universalVertices G x.property hxy

/-- The three separated-unit orbit values described by `P` agree with every
member of the coherent deletion family. -/
structure D7SeparatedParameters.RealizesCoherentFamily
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G))
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (P : D7SeparatedParameters G) : Prop where
  beta_eq : ∀ (z : ↑(universalVertices G))
    (e : Sym2 (↑(nonUniversalVertices G)))
    (he : e ∈ (G.induce
      (↑(nonUniversalVertices G) : Set A)).edgeFinset),
    d7SeparatedUnit (d7DeletedGraph G (z : A))
      (d7CoherentUniversalDeletedWeight G z₀ w₀ z)
      ((d7NonUniversalDeletedEmbedding G z).sym2Map e) = P.beta e
  alpha_eq : ∀ (z y : ↑(universalVertices G))
    (hyz : (y : A) ≠ (z : A)) (u : ↑(nonUniversalVertices G)),
    d7SeparatedUnit (d7DeletedGraph G (z : A))
      (d7CoherentUniversalDeletedWeight G z₀ w₀ z)
      s(d7NonUniversalDeletedEmbedding G z u,
        d7DeletedVertex (z : A) (y : A) hyz) = P.alpha u
  gamma_eq : ∀ (z x y : ↑(universalVertices G))
    (hxz : (x : A) ≠ (z : A)) (hyz : (y : A) ≠ (z : A))
    (hxy : (x : A) ≠ (y : A)),
    d7SeparatedUnit (d7DeletedGraph G (z : A))
      (d7CoherentUniversalDeletedWeight G z₀ w₀ z)
      s(d7DeletedVertex (z : A) (x : A) hxz,
        d7DeletedVertex (z : A) (y : A) hyz) = P.gamma

lemma fractionalEdgeLoad_d7LiftedWeight_nonUniversal
    (G : SimpleGraph A) (z : ↑(universalVertices G))
    (w : Finset (↑(d7DeletedFinset (A := A) (z : A))) → ℝ)
    (e : Sym2 (↑(nonUniversalVertices G))) :
    fractionalEdgeLoad G (d7LiftedWeight (z : A) w)
        ((inducedEmbedding (nonUniversalVertices G)).sym2Map e) =
      fractionalEdgeLoad (d7DeletedGraph G (z : A)) w
        ((d7NonUniversalDeletedEmbedding G z).sym2Map e) := by
  induction e using Sym2.inductionOn with
  | hf u v =>
      apply fractionalEdgeLoad_d7LiftedWeight_of_ne
      · intro h
        have h' : (u : A) = (z : A) := h
        exact nonUniversalVertex_not_mem_universalVertices G u.property
          (h' ▸ z.property)
      · intro h
        have h' : (v : A) = (z : A) := h
        exact nonUniversalVertex_not_mem_universalVertices G v.property
          (h' ▸ z.property)

lemma d7LargeCorrection_numerator_nonUniversal
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G))
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (P : D7SeparatedParameters G)
    (hreal : P.RealizesCoherentFamily G z₀ w₀)
    (e : Sym2 (↑(nonUniversalVertices G)))
    (he : e ∈ (G.induce
      (↑(nonUniversalVertices G) : Set A)).edgeFinset) :
    (∑ z : ↑(universalVertices G),
        fractionalEdgeLoad G
          (d7LiftedWeight (z : A)
            (d7CoherentUniversalDeletedWeight G z₀ w₀ z))
          ((inducedEmbedding (nonUniversalVertices G)).sym2Map e)) +
        fractionalEdgeLoad G (d7LargeCorrection G P)
          ((inducedEmbedding (nonUniversalVertices G)).sym2Map e) =
      ((universalVertices G).card : ℝ) -
        ∑ z : ↑(universalVertices G),
          d7RemainingResidual (d7DeletedGraph G (z : A))
            (d7CoherentUniversalDeletedWeight G z₀ w₀ z)
            ((d7NonUniversalDeletedEmbedding G z).sym2Map e) := by
  rw [fractionalEdgeLoad_d7LargeCorrection_nonUniversal G P e he]
  have hterms : ∀ z : ↑(universalVertices G),
      fractionalEdgeLoad G
          (d7LiftedWeight (z : A)
            (d7CoherentUniversalDeletedWeight G z₀ w₀ z))
          ((inducedEmbedding (nonUniversalVertices G)).sym2Map e) =
        1 - P.beta e -
          d7RemainingResidual (d7DeletedGraph G (z : A))
            (d7CoherentUniversalDeletedWeight G z₀ w₀ z)
            ((d7NonUniversalDeletedEmbedding G z).sym2Map e) := by
    intro z
    rw [fractionalEdgeLoad_d7LiftedWeight_nonUniversal]
    have hone := fractionalEdgeLoad_add_separated_add_remaining_eq_one
      (d7DeletedGraph G (z : A))
      (d7CoherentUniversalDeletedWeight G z₀ w₀ z)
      ((d7NonUniversalDeletedEmbedding G z).sym2Map e)
      (d7NonUniversalDeletedEdge_mem G z e he)
    rw [hreal.beta_eq z e he] at hone
    linarith
  simp_rw [hterms]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
    Fintype.card_coe]
  ring

lemma fractionalEdgeLoad_d7LiftedWeight_mixed
    (G : SimpleGraph A) (z y : ↑(universalVertices G))
    (hyz : (y : A) ≠ (z : A))
    (w : Finset (↑(d7DeletedFinset (A := A) (z : A))) → ℝ)
    (u : ↑(nonUniversalVertices G)) :
    fractionalEdgeLoad G (d7LiftedWeight (z : A) w) s((u : A), (y : A)) =
      fractionalEdgeLoad (d7DeletedGraph G (z : A)) w
        s(d7NonUniversalDeletedEmbedding G z u,
          d7DeletedVertex (z : A) (y : A) hyz) := by
  apply fractionalEdgeLoad_d7LiftedWeight_of_ne
  · intro h
    exact nonUniversalVertex_not_mem_universalVertices G u.property
      (h ▸ z.property)

/-- The residual remainder on a mixed edge, interpreted as zero in the one
deletion where that edge is absent. -/
def d7MixedRemainingResidual (G : SimpleGraph A)
    (z₀ : ↑(universalVertices G))
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (u : ↑(nonUniversalVertices G)) (y z : ↑(universalVertices G)) : ℝ :=
  if h : z = y then 0 else
    d7RemainingResidual (d7DeletedGraph G (z : A))
      (d7CoherentUniversalDeletedWeight G z₀ w₀ z)
      s(d7NonUniversalDeletedEmbedding G z u,
        d7DeletedVertex (z : A) (y : A) (by
          intro hval
          exact h (Subtype.ext hval.symm)))

lemma d7LargeCorrection_numerator_mixed
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G))
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (P : D7SeparatedParameters G)
    (hreal : P.RealizesCoherentFamily G z₀ w₀)
    (hm : 4 ≤ (universalVertices G).card)
    (u : ↑(nonUniversalVertices G)) (y : ↑(universalVertices G)) :
    (∑ z : ↑(universalVertices G),
        fractionalEdgeLoad G
          (d7LiftedWeight (z : A)
            (d7CoherentUniversalDeletedWeight G z₀ w₀ z))
          s((u : A), (y : A))) +
        fractionalEdgeLoad G (d7LargeCorrection G P) s((u : A), (y : A)) =
      ((universalVertices G).card : ℝ) -
        ∑ z : ↑(universalVertices G),
          d7MixedRemainingResidual G z₀ w₀ u y z := by
  rw [fractionalEdgeLoad_d7LargeCorrection_mixed G P hm u y]
  change (∑ z : ↑(universalVertices G),
      fractionalEdgeLoad G
        (d7LiftedWeight (z : A)
          (d7CoherentUniversalDeletedWeight G z₀ w₀ z))
        s((u : A), (y : A))) +
      (1 + (((universalVertices G).card : ℝ) - 1) * P.alpha u) =
    ((universalVertices G).card : ℝ) -
      ∑ z, d7MixedRemainingResidual G z₀ w₀ u y z
  have hterms : ∀ z : ↑(universalVertices G),
      fractionalEdgeLoad G
          (d7LiftedWeight (z : A)
          (d7CoherentUniversalDeletedWeight G z₀ w₀ z))
          s((u : A), (y : A)) =
        if z = y then 0 else 1 - P.alpha u -
          d7MixedRemainingResidual G z₀ w₀ u y z := by
    intro z
    by_cases hzy : z = y
    · subst z
      rw [if_pos rfl]
      simpa only [Sym2.eq_swap] using
        (fractionalEdgeLoad_d7LiftedWeight_eq_zero_of_endpoint
          G (y : A) (u : A)
            (d7CoherentUniversalDeletedWeight G z₀ w₀ y))
    · rw [if_neg hzy]
      have hyz : (y : A) ≠ (z : A) := by
        intro h
        exact hzy (Subtype.ext h.symm)
      rw [fractionalEdgeLoad_d7LiftedWeight_mixed G z y hyz]
      have hone := fractionalEdgeLoad_add_separated_add_remaining_eq_one
        (d7DeletedGraph G (z : A))
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z)
        s(d7NonUniversalDeletedEmbedding G z u,
          d7DeletedVertex (z : A) (y : A) hyz)
        (d7MixedDeletedEdge_mem G z y hyz u)
      rw [hreal.alpha_eq z y hyz u] at hone
      simp only [d7MixedRemainingResidual, hzy, dite_false]
      linarith
  simp_rw [hterms]
  have hsplit : ∀ z : ↑(universalVertices G),
      (if z = y then 0 else 1 - P.alpha u -
        d7MixedRemainingResidual G z₀ w₀ u y z) =
        (if z = y then 0 else 1 - P.alpha u) -
          d7MixedRemainingResidual G z₀ w₀ u y z := by
    intro z
    by_cases h : z = y <;> simp [h, d7MixedRemainingResidual]
  simp_rw [hsplit]
  rw [Finset.sum_sub_distrib, sum_ite_eq_zero_else]
  simp only [Fintype.card_coe]
  ring

lemma fractionalEdgeLoad_d7LiftedWeight_universal
    (G : SimpleGraph A) (z x y : ↑(universalVertices G))
    (hxz : (x : A) ≠ (z : A)) (hyz : (y : A) ≠ (z : A))
    (w : Finset (↑(d7DeletedFinset (A := A) (z : A))) → ℝ) :
    fractionalEdgeLoad G (d7LiftedWeight (z : A) w) s((x : A), (y : A)) =
      fractionalEdgeLoad (d7DeletedGraph G (z : A)) w
        s(d7DeletedVertex (z : A) (x : A) hxz,
          d7DeletedVertex (z : A) (y : A) hyz) := by
  exact fractionalEdgeLoad_d7LiftedWeight_of_ne G (z : A) (x : A) (y : A)
    w hxz hyz

/-- The residual remainder on a universal edge, interpreted as zero in its
two endpoint deletions. -/
def d7UniversalRemainingResidual (G : SimpleGraph A)
    (z₀ : ↑(universalVertices G))
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (x y z : ↑(universalVertices G)) : ℝ :=
  if h : z = x ∨ z = y then 0 else
    d7RemainingResidual (d7DeletedGraph G (z : A))
      (d7CoherentUniversalDeletedWeight G z₀ w₀ z)
      s(d7DeletedVertex (z : A) (x : A) (by
          intro hval
          exact h (Or.inl (Subtype.ext hval.symm))),
        d7DeletedVertex (z : A) (y : A) (by
          intro hval
          exact h (Or.inr (Subtype.ext hval.symm))))

lemma d7LargeCorrection_numerator_universal
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G))
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (P : D7SeparatedParameters G)
    (hreal : P.RealizesCoherentFamily G z₀ w₀)
    (hm : 4 ≤ (universalVertices G).card)
    (x y : ↑(universalVertices G)) (hxy : x ≠ y) :
    (∑ z : ↑(universalVertices G),
        fractionalEdgeLoad G
          (d7LiftedWeight (z : A)
            (d7CoherentUniversalDeletedWeight G z₀ w₀ z))
          s((x : A), (y : A))) +
        fractionalEdgeLoad G (d7LargeCorrection G P) s((x : A), (y : A)) =
      ((universalVertices G).card : ℝ) -
        ∑ z : ↑(universalVertices G),
          d7UniversalRemainingResidual G z₀ w₀ x y z := by
  let e : Sym2 (↑(universalVertices G)) := s(x, y)
  have he : e ∈ (⊤ : SimpleGraph
      (↑(universalVertices G))).edgeFinset := by
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact hxy
  have hcorr := fractionalEdgeLoad_d7LargeCorrection_universal_simplified
    G P hm e he
  change fractionalEdgeLoad G (d7LargeCorrection G P) s((x : A), (y : A)) =
      2 + (((universalVertices G).card : ℝ) - 2) * P.gamma at hcorr
  rw [hcorr]
  have hterms : ∀ z : ↑(universalVertices G),
      fractionalEdgeLoad G
          (d7LiftedWeight (z : A)
            (d7CoherentUniversalDeletedWeight G z₀ w₀ z))
          s((x : A), (y : A)) =
        if z = x ∨ z = y then 0 else 1 - P.gamma -
          d7UniversalRemainingResidual G z₀ w₀ x y z := by
    intro z
    by_cases hz : z = x ∨ z = y
    · rw [if_pos hz]
      rcases hz with hzx | hzy
      · rw [hzx]
        exact fractionalEdgeLoad_d7LiftedWeight_eq_zero_of_endpoint
          G (x : A) (y : A)
            (d7CoherentUniversalDeletedWeight G z₀ w₀ x)
      · rw [hzy]
        simpa only [Sym2.eq_swap] using
          (fractionalEdgeLoad_d7LiftedWeight_eq_zero_of_endpoint
            G (y : A) (x : A)
              (d7CoherentUniversalDeletedWeight G z₀ w₀ y))
    · rw [if_neg hz]
      have hxz : (x : A) ≠ (z : A) := by
        intro h
        exact hz (Or.inl (Subtype.ext h.symm))
      have hyz : (y : A) ≠ (z : A) := by
        intro h
        exact hz (Or.inr (Subtype.ext h.symm))
      have hxyA : (x : A) ≠ (y : A) := fun h ↦ hxy (Subtype.ext h)
      rw [fractionalEdgeLoad_d7LiftedWeight_universal G z x y hxz hyz]
      have hone := fractionalEdgeLoad_add_separated_add_remaining_eq_one
        (d7DeletedGraph G (z : A))
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z)
        s(d7DeletedVertex (z : A) (x : A) hxz,
          d7DeletedVertex (z : A) (y : A) hyz)
        (d7UniversalDeletedEdge_mem G z x y hxz hyz hxyA)
      rw [hreal.gamma_eq z x y hxz hyz hxyA] at hone
      simp only [d7UniversalRemainingResidual, hz, dite_false]
      linarith
  simp_rw [hterms]
  have hsplit : ∀ z : ↑(universalVertices G),
      (if z = x ∨ z = y then 0 else 1 - P.gamma -
        d7UniversalRemainingResidual G z₀ w₀ x y z) =
        (if z = x ∨ z = y then 0 else 1 - P.gamma) -
          d7UniversalRemainingResidual G z₀ w₀ x y z := by
    intro z
    by_cases h : z = x ∨ z = y <;>
      simp [h, d7UniversalRemainingResidual]
  simp_rw [hsplit]
  rw [Finset.sum_sub_distrib,
    sum_ite_eq_zero_else_two x y hxy]
  simp only [Fintype.card_coe]
  ring

/-- The explicit large-`m` averaging numerator, divided by the number of
universal vertices. -/
def d7LargeAverageWeight (G : SimpleGraph A)
    (z₀ : ↑(universalVertices G))
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (P : D7SeparatedParameters G) : Finset A → ℝ :=
  fun t ↦ (((universalVertices G).card : ℝ)⁻¹) *
    ((∑ z : ↑(universalVertices G),
      d7LiftedWeight (z : A)
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z) t) +
      d7LargeCorrection G P t)

lemma fractionalEdgeLoad_d7LargeAverageWeight (G : SimpleGraph A)
    (z₀ : ↑(universalVertices G))
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (P : D7SeparatedParameters G) (e : Sym2 A) :
    fractionalEdgeLoad G (d7LargeAverageWeight G z₀ w₀ P) e =
      (((universalVertices G).card : ℝ)⁻¹) *
        ((∑ z : ↑(universalVertices G),
          fractionalEdgeLoad G
            (d7LiftedWeight (z : A)
              (d7CoherentUniversalDeletedWeight G z₀ w₀ z)) e) +
          fractionalEdgeLoad G (d7LargeCorrection G P) e) := by
  unfold d7LargeAverageWeight
  rw [fractionalEdgeLoad_smul, fractionalEdgeLoad_add,
    fractionalEdgeLoad_sum]

lemma d7LargeAverageWeight_edgeLoad_le_one_nonUniversal
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G))
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (P : D7SeparatedParameters G)
    (hreal : P.RealizesCoherentFamily G z₀ w₀)
    (hm : 4 ≤ (universalVertices G).card)
    (hwPacking : ∀ z : ↑(universalVertices G),
      IsFractionalPacking (d7DeletedGraph G (z : A))
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z))
    (hwOne : ∀ z : ↑(universalVertices G),
      1 ≤ fractionalUncoveredWeight (d7DeletedGraph G (z : A))
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z))
    (e : Sym2 (↑(nonUniversalVertices G)))
    (he : e ∈ (G.induce
      (↑(nonUniversalVertices G) : Set A)).edgeFinset) :
    fractionalEdgeLoad G (d7LargeAverageWeight G z₀ w₀ P)
        ((inducedEmbedding (nonUniversalVertices G)).sym2Map e) ≤ 1 := by
  rw [fractionalEdgeLoad_d7LargeAverageWeight,
    d7LargeCorrection_numerator_nonUniversal G z₀ w₀ P hreal e he]
  have hrem : 0 ≤ ∑ z : ↑(universalVertices G),
      d7RemainingResidual (d7DeletedGraph G (z : A))
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z)
        ((d7NonUniversalDeletedEmbedding G z).sym2Map e) := by
    exact Finset.sum_nonneg fun z _ ↦
      d7RemainingResidual_nonneg (hwPacking z) (hwOne z) _
  have hmR : 0 < ((universalVertices G).card : ℝ) := by
    exact_mod_cast (by omega : 0 < (universalVertices G).card)
  calc
    ((universalVertices G).card : ℝ)⁻¹ *
        (((universalVertices G).card : ℝ) - ∑ z : ↑(universalVertices G),
          d7RemainingResidual (d7DeletedGraph G (z : A))
            (d7CoherentUniversalDeletedWeight G z₀ w₀ z)
            ((d7NonUniversalDeletedEmbedding G z).sym2Map e)) ≤
        ((universalVertices G).card : ℝ)⁻¹ *
          ((universalVertices G).card : ℝ) :=
      mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.mpr hmR.le)
    _ = 1 := by field_simp

lemma d7LargeAverageWeight_edgeLoad_le_one_mixed
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G))
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (P : D7SeparatedParameters G)
    (hreal : P.RealizesCoherentFamily G z₀ w₀)
    (hm : 4 ≤ (universalVertices G).card)
    (hwPacking : ∀ z : ↑(universalVertices G),
      IsFractionalPacking (d7DeletedGraph G (z : A))
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z))
    (hwOne : ∀ z : ↑(universalVertices G),
      1 ≤ fractionalUncoveredWeight (d7DeletedGraph G (z : A))
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z))
    (u : ↑(nonUniversalVertices G)) (y : ↑(universalVertices G)) :
    fractionalEdgeLoad G (d7LargeAverageWeight G z₀ w₀ P)
        s((u : A), (y : A)) ≤ 1 := by
  rw [fractionalEdgeLoad_d7LargeAverageWeight,
    d7LargeCorrection_numerator_mixed G z₀ w₀ P hreal hm u y]
  have hrem : 0 ≤ ∑ z : ↑(universalVertices G),
      d7MixedRemainingResidual G z₀ w₀ u y z := by
    apply Finset.sum_nonneg
    intro z _
    unfold d7MixedRemainingResidual
    split
    · exact le_rfl
    · exact d7RemainingResidual_nonneg (hwPacking z) (hwOne z) _
  have hmR : 0 < ((universalVertices G).card : ℝ) := by
    exact_mod_cast (by omega : 0 < (universalVertices G).card)
  calc
    ((universalVertices G).card : ℝ)⁻¹ *
        (((universalVertices G).card : ℝ) - ∑ z,
          d7MixedRemainingResidual G z₀ w₀ u y z) ≤
        ((universalVertices G).card : ℝ)⁻¹ *
          ((universalVertices G).card : ℝ) :=
      mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.mpr hmR.le)
    _ = 1 := by field_simp

lemma d7LargeAverageWeight_edgeLoad_le_one_universal
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G))
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (P : D7SeparatedParameters G)
    (hreal : P.RealizesCoherentFamily G z₀ w₀)
    (hm : 4 ≤ (universalVertices G).card)
    (hwPacking : ∀ z : ↑(universalVertices G),
      IsFractionalPacking (d7DeletedGraph G (z : A))
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z))
    (hwOne : ∀ z : ↑(universalVertices G),
      1 ≤ fractionalUncoveredWeight (d7DeletedGraph G (z : A))
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z))
    (x y : ↑(universalVertices G)) (hxy : x ≠ y) :
    fractionalEdgeLoad G (d7LargeAverageWeight G z₀ w₀ P)
        s((x : A), (y : A)) ≤ 1 := by
  rw [fractionalEdgeLoad_d7LargeAverageWeight,
    d7LargeCorrection_numerator_universal G z₀ w₀ P hreal hm x y hxy]
  have hrem : 0 ≤ ∑ z : ↑(universalVertices G),
      d7UniversalRemainingResidual G z₀ w₀ x y z := by
    apply Finset.sum_nonneg
    intro z _
    unfold d7UniversalRemainingResidual
    split
    · exact le_rfl
    · exact d7RemainingResidual_nonneg (hwPacking z) (hwOne z) _
  have hmR : 0 < ((universalVertices G).card : ℝ) := by
    exact_mod_cast (by omega : 0 < (universalVertices G).card)
  calc
    ((universalVertices G).card : ℝ)⁻¹ *
        (((universalVertices G).card : ℝ) - ∑ z,
          d7UniversalRemainingResidual G z₀ w₀ x y z) ≤
        ((universalVertices G).card : ℝ)⁻¹ *
          ((universalVertices G).card : ℝ) :=
      mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.mpr hmR.le)
    _ = 1 := by field_simp

/-- Feasibility of the corrected large-`m` D7 average.  The three edge
classes in the universal/nonuniversal vertex partition are discharged by
the exact residual identities above. -/
lemma d7LargeAverageWeight_isFractionalPacking
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G))
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (P : D7SeparatedParameters G)
    (hreal : P.RealizesCoherentFamily G z₀ w₀)
    (hn : 14 ≤ Fintype.card A)
    (hm : 4 ≤ (universalVertices G).card)
    (hlarge : Fintype.card A - 7 ≤ (universalVertices G).card)
    (hwPacking : ∀ z : ↑(universalVertices G),
      IsFractionalPacking (d7DeletedGraph G (z : A))
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z))
    (hwOne : ∀ z : ↑(universalVertices G),
      1 ≤ fractionalUncoveredWeight (d7DeletedGraph G (z : A))
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z)) :
    IsFractionalPacking G (d7LargeAverageWeight G z₀ w₀ P) := by
  constructor
  · intro t ht
    unfold d7LargeAverageWeight
    apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    apply add_nonneg
    · apply Finset.sum_nonneg
      intro z _
      exact (IsFractionalPacking.extendInduced
        (G := G) (S := d7DeletedFinset (z : A)) (hwPacking z)).1 t ht
    · exact d7LargeCorrection_nonneg G P hn hm hlarge t ht
  · intro e he
    induction e using Sym2.inductionOn with
    | _ x y =>
      have hxy : x ≠ y := by
        have hnd := G.not_isDiag_of_mem_edgeFinset he
        simpa only [Sym2.mk_isDiag_iff] using hnd
      have nonUniversal_of_not_universal : ∀ {v : A},
          v ∉ universalVertices G → v ∈ nonUniversalVertices G := by
        intro v hv
        apply mem_nonUniversalVertices.mpr
        have hvne : Gᶜ.degree v ≠ 0 := by
          intro hz
          exact hv (mem_universalVertices.mpr hz)
        exact Nat.pos_of_ne_zero hvne
      by_cases hxZ : x ∈ universalVertices G
      · let zx : ↑(universalVertices G) := ⟨x, hxZ⟩
        by_cases hyZ : y ∈ universalVertices G
        · let zy : ↑(universalVertices G) := ⟨y, hyZ⟩
          have hzxy : zx ≠ zy := by
            intro h
            exact hxy (congrArg Subtype.val h)
          exact d7LargeAverageWeight_edgeLoad_le_one_universal
            G z₀ w₀ P hreal hm hwPacking hwOne zx zy hzxy
        · let uy : ↑(nonUniversalVertices G) :=
            ⟨y, nonUniversal_of_not_universal hyZ⟩
          rw [show s(x, y) = s(y, x) from Sym2.eq_swap]
          exact d7LargeAverageWeight_edgeLoad_le_one_mixed
            G z₀ w₀ P hreal hm hwPacking hwOne uy zx
      · let ux : ↑(nonUniversalVertices G) :=
          ⟨x, nonUniversal_of_not_universal hxZ⟩
        by_cases hyZ : y ∈ universalVertices G
        · let zy : ↑(universalVertices G) := ⟨y, hyZ⟩
          exact d7LargeAverageWeight_edgeLoad_le_one_mixed
            G z₀ w₀ P hreal hm hwPacking hwOne ux zy
        · let uy : ↑(nonUniversalVertices G) :=
            ⟨y, nonUniversal_of_not_universal hyZ⟩
          let q : Sym2 (↑(nonUniversalVertices G)) := s(ux, uy)
          have hq : q ∈ (G.induce
              (↑(nonUniversalVertices G) : Set A)).edgeFinset := by
            rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
            change G.Adj x y
            simpa only [SimpleGraph.mem_edgeFinset,
              SimpleGraph.mem_edgeSet] using he
          exact d7LargeAverageWeight_edgeLoad_le_one_nonUniversal
            G z₀ w₀ P hreal hm hwPacking hwOne q hq

lemma D7SeparatedParameters.beta_le_one_of_mem
    {G : SimpleGraph A} (P : D7SeparatedParameters G)
    (hm : 4 ≤ (universalVertices G).card)
    (e : Sym2 (↑(nonUniversalVertices G)))
    (he : e ∈ (G.induce
      (↑(nonUniversalVertices G) : Set A)).edgeFinset) :
    P.beta e ≤ 1 := by
  calc
    P.beta e ≤ ∑ f ∈ (G.induce
        (↑(nonUniversalVertices G) : Set A)).edgeFinset, P.beta f := by
      apply Finset.single_le_sum
      · intro f hf
        exact P.beta_nonneg f hf
      · exact he
    _ = P.betaMass := rfl
    _ ≤ 1 := P.betaMass_le_one (by omega)

lemma D7SeparatedParameters.largeMixedCoefficient_le_one
    {G : SimpleGraph A} (P : D7SeparatedParameters G)
    (hm : 4 ≤ (universalVertices G).card)
    (u : ↑(nonUniversalVertices G)) :
    P.largeMixedCoefficient u ≤ 1 := by
  let m : ℝ := ((universalVertices G).card : ℝ)
  have hm1 : 0 < m - 1 := by
    dsimp only [m]
    exact sub_pos.mpr (by exact_mod_cast (by omega :
      1 < (universalVertices G).card))
  have hfactor : 0 ≤ m - 1 := hm1.le
  have halphaSingle : P.alpha u ≤ ∑ v, P.alpha v := by
    apply Finset.single_le_sum
    · intro v _
      exact P.alpha_nonneg v
    · exact Finset.mem_univ u
  have halphaTerm : (m - 1) * P.alpha u ≤ P.alphaMass := by
    unfold D7SeparatedParameters.alphaMass
    exact mul_le_mul_of_nonneg_left halphaSingle hfactor
  have halphaMass : P.alphaMass ≤ 1 := P.alphaMass_le_one (by omega)
  have hbetaIncident : 0 ≤ P.betaIncident u := P.betaIncident_nonneg u
  unfold D7SeparatedParameters.largeMixedCoefficient
  change (1 + (m - 1) * P.alpha u - P.betaIncident u) / (m - 1) ≤ 1
  apply (div_le_one hm1).2
  have hm4 : (4 : ℝ) ≤ m := by
    dsimp only [m]
    exact_mod_cast hm
  linarith

lemma D7SeparatedParameters.largeUniversalCoefficient_le_one
    {G : SimpleGraph A} (P : D7SeparatedParameters G)
    (hn : 14 ≤ Fintype.card A)
    (hm : 4 ≤ (universalVertices G).card)
    (hlarge : Fintype.card A - 7 ≤ (universalVertices G).card) :
    P.largeUniversalCoefficient ≤ 1 := by
  let m : ℝ := ((universalVertices G).card : ℝ)
  let q : ℝ := (Fintype.card A : ℝ)
  let alpha : ℝ := P.alphaMass
  let beta : ℝ := P.betaMass
  have hm7Nat : 7 ≤ (universalVertices G).card := by omega
  have hm7 : (7 : ℝ) ≤ m := by
    dsimp only [m]
    exact_mod_cast hm7Nat
  have hm1 : 0 < m - 1 := by linarith
  have hm2 : 0 < m - 2 := by linarith
  have hmqNat : (universalVertices G).card ≤ Fintype.card A := by
    simpa only [Finset.card_univ] using
      Finset.card_le_card (Finset.subset_univ (universalVertices G))
  have hmq : m ≤ q := by
    dsimp only [m, q]
    exact_mod_cast hmqNat
  have halpha0 : 0 ≤ alpha := P.alphaMass_nonneg (by omega)
  have hbeta0 : 0 ≤ beta := P.betaMass_nonneg
  have hbeta1 : beta ≤ 1 := P.betaMass_le_one (by omega)
  have hgamma0 : 0 ≤ P.gamma := P.gamma_nonneg
  have hgammaTerm0 := P.gammaTerm_nonneg (by omega :
    2 ≤ (universalVertices G).card)
  have hnorm : ((m - 1) * (m - 2) / 2) * P.gamma + alpha + beta = 1 := by
    simpa only [m, alpha, beta, D7SeparatedParameters.alphaMass,
      D7SeparatedParameters.betaMass] using P.normalization
  have hgammaTerm1 : ((m - 1) * (m - 2) / 2) * P.gamma ≤ 1 := by
    linarith
  have hgammaSmall : (m - 2) * P.gamma ≤ 1 / 3 := by
    nlinarith
  have hbetaSmall : 2 * beta / (m - 1) ≤ 1 / 3 := by
    apply (div_le_iff₀ hm1).2
    nlinarith
  unfold D7SeparatedParameters.largeUniversalCoefficient
  change (2 + (m - 2) * P.gamma - (q - m) / (m - 1) -
      alpha / (m - 1) + 2 * beta / (m - 1)) / (m - 2) ≤ 1
  apply (div_le_one hm2).2
  have hnonnegQ : 0 ≤ (q - m) / (m - 1) :=
    div_nonneg (sub_nonneg.mpr hmq) hm1.le
  have hnonnegAlpha : 0 ≤ alpha / (m - 1) :=
    div_nonneg halpha0 hm1.le
  linarith

lemma fractionalSize_weightedAttachedEdgeWeight
    {G : SimpleGraph A} {S : Finset A} {u : A}
    {C : Finset (Sym2 S)} {r : Sym2 S → ℝ}
    (htri : ∀ e ∈ C, attachedEdgeTriangle S u e ∈ G.cliqueFinset 3) :
    fractionalSize G (weightedAttachedEdgeWeight S u C r) =
      ∑ e ∈ C, r e := by
  unfold fractionalSize weightedAttachedEdgeWeight singleTriangleWeight
  rw [Finset.sum_comm]
  calc
    (∑ e : ↑C, ∑ t ∈ G.cliqueFinset 3,
        if t = attachedEdgeTriangle S u e then r e else 0) =
        ∑ e : ↑C, r e := by
      apply Fintype.sum_congr
      intro e
      calc
        (∑ t ∈ G.cliqueFinset 3,
            if t = attachedEdgeTriangle S u e then r e else 0) =
            (if attachedEdgeTriangle S u e = attachedEdgeTriangle S u e
              then r e else 0) := by
          apply Finset.sum_eq_single (attachedEdgeTriangle S u e)
          · intro t _ hne
            rw [if_neg hne]
          · intro hnot
            exact (hnot (htri e e.property)).elim
        _ = r e := by simp
    _ = ∑ e ∈ C, r e := by
      exact (Finset.sum_subtype C (fun _ ↦ Iff.rfl) r).symm

lemma fractionalSize_d7UUZCorrection (G : SimpleGraph A)
    (P : D7SeparatedParameters G) :
    fractionalSize G (d7UUZCorrection G P) =
      ((universalVertices G).card : ℝ) * P.betaMass := by
  unfold fractionalSize d7UUZCorrection
  rw [Finset.sum_comm]
  calc
    (∑ z : ↑(universalVertices G),
        ∑ t ∈ G.cliqueFinset 3,
          weightedAttachedEdgeWeight (nonUniversalVertices G) (z : A)
            (G.induce (↑(nonUniversalVertices G) : Set A)).edgeFinset
            P.beta t) =
        ∑ _z : ↑(universalVertices G), P.betaMass := by
      apply Fintype.sum_congr
      intro z
      change fractionalSize G
        (weightedAttachedEdgeWeight (nonUniversalVertices G) (z : A)
          (G.induce (↑(nonUniversalVertices G) : Set A)).edgeFinset
          P.beta) = P.betaMass
      rw [fractionalSize_weightedAttachedEdgeWeight
        (fun e he ↦ d7UUZTriangle_mem_cliqueFinset G z ⟨e, he⟩)]
      rfl
    _ = ((universalVertices G).card : ℝ) * P.betaMass := by
      simp

lemma fractionalSize_d7UZZCorrection (G : SimpleGraph A)
    (P : D7SeparatedParameters G) :
    fractionalSize G (d7UZZCorrection G P) =
      (((universalVertices G).card.choose 2 : ℕ) : ℝ) *
        ∑ u : ↑(nonUniversalVertices G), P.largeMixedCoefficient u := by
  unfold fractionalSize d7UZZCorrection
  rw [Finset.sum_comm]
  calc
    (∑ u : ↑(nonUniversalVertices G),
        ∑ t ∈ G.cliqueFinset 3,
          weightedAttachedEdgeWeight (universalVertices G) (u : A)
            (⊤ : SimpleGraph (↑(universalVertices G))).edgeFinset
            (fun _ ↦ P.largeMixedCoefficient u) t) =
        ∑ u : ↑(nonUniversalVertices G),
          (((universalVertices G).card.choose 2 : ℕ) : ℝ) *
            P.largeMixedCoefficient u := by
      apply Fintype.sum_congr
      intro u
      change fractionalSize G
        (weightedAttachedEdgeWeight (universalVertices G) (u : A)
          (⊤ : SimpleGraph (↑(universalVertices G))).edgeFinset
          (fun _ ↦ P.largeMixedCoefficient u)) = _
      rw [fractionalSize_weightedAttachedEdgeWeight
        (fun e he ↦ d7UZZTriangle_mem_cliqueFinset G u ⟨e, he⟩),
        Finset.sum_const, SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
      simp only [Fintype.card_coe, nsmul_eq_mul]
    _ = (((universalVertices G).card.choose 2 : ℕ) : ℝ) *
          ∑ u : ↑(nonUniversalVertices G), P.largeMixedCoefficient u := by
      rw [Finset.mul_sum]

lemma fractionalSize_d7ZZZCorrection (G : SimpleGraph A)
    (P : D7SeparatedParameters G) :
    fractionalSize G (d7ZZZCorrection G P) =
      (((universalVertices G).card.choose 3 : ℕ) : ℝ) *
        P.largeUniversalCoefficient := by
  unfold fractionalSize d7ZZZCorrection singleTriangleWeight
  rw [Finset.sum_comm]
  calc
    (∑ q : ↑((universalVertices G).powersetCard 3),
        ∑ t ∈ G.cliqueFinset 3,
          if t = (q : Finset A) then P.largeUniversalCoefficient else 0) =
        ∑ _q : ↑((universalVertices G).powersetCard 3),
          P.largeUniversalCoefficient := by
      apply Fintype.sum_congr
      intro q
      calc
        (∑ t ∈ G.cliqueFinset 3,
            if t = (q : Finset A) then P.largeUniversalCoefficient else 0) =
            (if (q : Finset A) = (q : Finset A)
              then P.largeUniversalCoefficient else 0) := by
          apply Finset.sum_eq_single (q : Finset A)
          · intro t _ hne
            rw [if_neg hne]
          · intro hnot
            exact (hnot (d7ZZZTriangle_mem_cliqueFinset G q)).elim
        _ = P.largeUniversalCoefficient := by simp
    _ = (((universalVertices G).card.choose 3 : ℕ) : ℝ) *
          P.largeUniversalCoefficient := by
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
        Fintype.card_coe, Finset.card_powersetCard]

lemma fractionalSize_d7LargeCorrection (G : SimpleGraph A)
    (P : D7SeparatedParameters G) :
    fractionalSize G (d7LargeCorrection G P) =
      ((universalVertices G).card : ℝ) * P.betaMass +
      (((universalVertices G).card.choose 2 : ℕ) : ℝ) *
        ∑ u : ↑(nonUniversalVertices G), P.largeMixedCoefficient u +
      (((universalVertices G).card.choose 3 : ℕ) : ℝ) *
        P.largeUniversalCoefficient := by
  unfold fractionalSize d7LargeCorrection
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  exact congrArg₂ (· + ·)
    (congrArg₂ (· + ·)
      (fractionalSize_d7UUZCorrection G P)
      (fractionalSize_d7UZZCorrection G P))
    (fractionalSize_d7ZZZCorrection G P)

lemma cast_choose_three_d7 (n : ℕ) :
    ((n.choose 3 : ℕ) : ℝ) =
      (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) / 6 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Nat.choose_succ_succ]
      push_cast
      rw [Nat.cast_choose_two, ih]
      push_cast
      ring

/-- The total size of the explicit correction collapses to `m*q/3`.
This is the global form of the three edge-type cancellations in the paper. -/
lemma fractionalSize_d7LargeCorrection_eq (G : SimpleGraph A)
    (P : D7SeparatedParameters G)
    (hm : 4 ≤ (universalVertices G).card) :
    fractionalSize G (d7LargeCorrection G P) =
      ((universalVertices G).card : ℝ) * (Fintype.card A : ℝ) / 3 := by
  rw [fractionalSize_d7LargeCorrection,
    P.sum_largeMixedCoefficient, Nat.cast_choose_two,
    cast_choose_three_d7]
  let m : ℝ := ((universalVertices G).card : ℝ)
  let q : ℝ := (Fintype.card A : ℝ)
  let alpha : ℝ := P.alphaMass
  let beta : ℝ := P.betaMass
  have hm1 : m - 1 ≠ 0 := by
    dsimp only [m]
    have : (1 : ℝ) < ((universalVertices G).card : ℝ) := by
      exact_mod_cast (by omega : 1 < (universalVertices G).card)
    linarith
  have hm2 : m - 2 ≠ 0 := by
    dsimp only [m]
    have : (2 : ℝ) < ((universalVertices G).card : ℝ) := by
      exact_mod_cast (by omega : 2 < (universalVertices G).card)
    linarith
  have hnorm : ((m - 1) * (m - 2) / 2) * P.gamma + alpha + beta = 1 := by
    simpa only [m, alpha, beta, D7SeparatedParameters.alphaMass,
      D7SeparatedParameters.betaMass] using P.normalization
  unfold D7SeparatedParameters.largeUniversalCoefficient
  change m * beta +
      (m * (m - 1) / 2) * ((q - m + alpha - 2 * beta) / (m - 1)) +
      (m * (m - 1) * (m - 2) / 6) *
        ((2 + (m - 2) * P.gamma - (q - m) / (m - 1) -
          alpha / (m - 1) + 2 * beta / (m - 1)) / (m - 2)) =
        m * q / 3
  field_simp [hm1, hm2]
  have hscaled := congrArg (fun x : ℝ ↦ 12 * m * x) hnorm
  ring_nf at hscaled ⊢
  linarith

lemma fractionalSize_d7CoherentUniversalDeletedWeight
    (G : SimpleGraph A) (z₀ z : ↑(universalVertices G))
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ) :
    fractionalSize (d7DeletedGraph G (z : A))
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z) =
      fractionalSize (d7DeletedGraph G (z₀ : A)) w₀ := by
  have h := fractionalSize_relabel (d7DeletedGraph G (z₀ : A))
    (d7DeletedSwapEquiv (z₀ : A) (z : A)) w₀
  rwa [d7DeletedGraph_map_d7DeletedSwapEquiv G z₀.property z.property] at h

lemma fractionalSize_d7LargeAverageWeight (G : SimpleGraph A)
    (z₀ : ↑(universalVertices G))
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (P : D7SeparatedParameters G)
    (hm : 4 ≤ (universalVertices G).card) :
    fractionalSize G (d7LargeAverageWeight G z₀ w₀ P) =
      fractionalSize (d7DeletedGraph G (z₀ : A)) w₀ +
        (Fintype.card A : ℝ) / 3 := by
  have hmain :
      (∑ t ∈ G.cliqueFinset 3,
        ∑ z : ↑(universalVertices G),
          d7LiftedWeight (z : A)
            (d7CoherentUniversalDeletedWeight G z₀ w₀ z) t) =
        ∑ z : ↑(universalVertices G),
          fractionalSize (d7DeletedGraph G (z : A))
            (d7CoherentUniversalDeletedWeight G z₀ w₀ z) := by
    rw [Finset.sum_comm]
    apply Fintype.sum_congr
    intro z
    exact fractionalSize_extendInducedWeight G
      (d7DeletedFinset (z : A))
      (d7CoherentUniversalDeletedWeight G z₀ w₀ z)
  unfold fractionalSize d7LargeAverageWeight
  rw [← Finset.mul_sum, Finset.sum_add_distrib, hmain]
  change (((universalVertices G).card : ℝ)⁻¹) *
      ((∑ z : ↑(universalVertices G),
        fractionalSize (d7DeletedGraph G (z : A))
          (d7CoherentUniversalDeletedWeight G z₀ w₀ z)) +
        fractionalSize G (d7LargeCorrection G P)) =
      fractionalSize (d7DeletedGraph G (z₀ : A)) w₀ +
        (Fintype.card A : ℝ) / 3
  rw [fractionalSize_d7LargeCorrection_eq G P hm]
  simp_rw [fractionalSize_d7CoherentUniversalDeletedWeight G z₀]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
    Fintype.card_coe]
  have hmR : ((universalVertices G).card : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : (universalVertices G).card ≠ 0)
  field_simp [hmR]

lemma degree_eq_card_sub_one_of_mem_universalVertices
    (G : SimpleGraph A) {z : A} (hz : z ∈ universalVertices G) :
    G.degree z = Fintype.card A - 1 := by
  have hcomp := G.degree_compl (v := z)
  rw [mem_universalVertices.mp hz] at hcomp
  have hlt := G.degree_lt_card_verts z
  omega

/-- The corrected average leaves exactly the canonical deletion remainder:
its uncovered weight is the deletion's uncovered weight minus the separated
unit. -/
lemma fractionalUncoveredWeight_d7LargeAverageWeight
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G))
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (P : D7SeparatedParameters G)
    (hm : 4 ≤ (universalVertices G).card) :
    fractionalUncoveredWeight G (d7LargeAverageWeight G z₀ w₀ P) =
      fractionalUncoveredWeight (d7DeletedGraph G (z₀ : A)) w₀ - 1 := by
  have hedgeNat := card_edgeSet_induce_univ_erase_add_degree G (z₀ : A)
  have hdegree := degree_eq_card_sub_one_of_mem_universalVertices G z₀.property
  rw [hdegree] at hedgeNat
  have hedge' : (Nat.card G.edgeSet : ℝ) =
      (Nat.card (d7DeletedGraph G (z₀ : A)).edgeSet : ℝ) +
        ((Fintype.card A - 1 : ℕ) : ℝ) := by
    exact_mod_cast hedgeNat
  have hcardPos : 1 ≤ Fintype.card A := Fintype.card_pos_iff.mpr ⟨z₀⟩
  have hedge : (Nat.card G.edgeSet : ℝ) =
      (Nat.card (d7DeletedGraph G (z₀ : A)).edgeSet : ℝ) +
        (Fintype.card A : ℝ) - 1 := by
    rw [Nat.cast_sub hcardPos, Nat.cast_one] at hedge'
    linarith
  rw [fractionalUncoveredWeight_eq_card_sub_general,
    fractionalUncoveredWeight_eq_card_sub_general,
    fractionalSize_d7LargeAverageWeight G z₀ w₀ P hm]
  linarith

lemma fractionalUncoveredWeight_d7LargeAverageWeight_le
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G))
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (P : D7SeparatedParameters G)
    (hm : 4 ≤ (universalVertices G).card) {a : ℝ}
    (hwUpper : fractionalUncoveredWeight
      (d7DeletedGraph G (z₀ : A)) w₀ ≤ a + 1) :
    fractionalUncoveredWeight G (d7LargeAverageWeight G z₀ w₀ P) ≤ a := by
  rw [fractionalUncoveredWeight_d7LargeAverageWeight G z₀ w₀ P hm]
  linarith

/-- The already-verified feasibility and budget portions of the large-`m`
assembly, packaged so that the remaining pointwise half-bound is explicit. -/
lemma hasStrongFractionalPacking_d7LargeAverageWeight_of_halfBounded
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G))
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (P : D7SeparatedParameters G)
    (hreal : P.RealizesCoherentFamily G z₀ w₀)
    (hn : 14 ≤ Fintype.card A)
    (hm : 4 ≤ (universalVertices G).card)
    (hlarge : Fintype.card A - 7 ≤ (universalVertices G).card)
    (hwPacking : ∀ z : ↑(universalVertices G),
      IsFractionalPacking (d7DeletedGraph G (z : A))
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z))
    (hwOne : ∀ z : ↑(universalVertices G),
      1 ≤ fractionalUncoveredWeight (d7DeletedGraph G (z : A))
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z))
    {a : ℝ}
    (hwUpper : fractionalUncoveredWeight
      (d7DeletedGraph G (z₀ : A)) w₀ ≤ a + 1)
    (hhalf : IsHalfBounded G (d7LargeAverageWeight G z₀ w₀ P)) :
    HasStrongFractionalPacking G a := by
  exact ⟨d7LargeAverageWeight G z₀ w₀ P,
    d7LargeAverageWeight_isFractionalPacking G z₀ w₀ P hreal hn hm hlarge
      hwPacking hwOne,
    fractionalUncoveredWeight_d7LargeAverageWeight_le G z₀ w₀ P hm hwUpper,
    hhalf⟩

lemma weightedAttachedEdgeWeight_apply_d7
    {S : Finset A} {u : A} {C : Finset (Sym2 S)}
    {r : Sym2 S → ℝ} (hu : u ∉ S)
    (hnonDiag : ∀ e ∈ C, ¬e.IsDiag) {e : Sym2 S} (he : e ∈ C) :
    weightedAttachedEdgeWeight S u C r (attachedEdgeTriangle S u e) = r e := by
  unfold weightedAttachedEdgeWeight singleTriangleWeight
  let eC : ↑C := ⟨e, he⟩
  rw [Fintype.sum_eq_single eC]
  · dsimp only [eC]
    rw [if_pos rfl]
  · intro f hfe
    rw [if_neg]
    intro htri
    apply hfe
    apply Subtype.ext
    exact attachedEdgeTriangle_injective (S := S) (u := u) hu
      (e := f) (f := e) (hnonDiag f f.property) (hnonDiag e he) htri.symm

lemma d7UUZCorrection_apply
    (G : SimpleGraph A) (P : D7SeparatedParameters G)
    (u v : ↑(nonUniversalVertices G)) (huv : u ≠ v)
    (z : ↑(universalVertices G))
    (he : s(u, v) ∈ (G.induce
      (↑(nonUniversalVertices G) : Set A)).edgeFinset) :
    d7UUZCorrection G P {(z : A), (u : A), (v : A)} = P.beta s(u, v) := by
  let e : Sym2 (↑(nonUniversalVertices G)) := s(u, v)
  have heND : ¬e.IsDiag := by
    simpa only [e, Sym2.mk_isDiag_iff] using huv
  have htriangle : attachedEdgeTriangle (nonUniversalVertices G) (z : A) e =
      ({(z : A), (u : A), (v : A)} : Finset A) := by
    simp only [attachedEdgeTriangle, e, Sym2.toFinset_mk_eq,
      Finset.map_insert, Finset.map_singleton, inducedEmbedding_apply]
  unfold d7UUZCorrection
  rw [Fintype.sum_eq_single z]
  · rw [← htriangle]
    exact weightedAttachedEdgeWeight_apply_d7
      (universalVertex_not_mem_nonUniversalVertices G z.property)
      (fun f hf ↦
        (G.induce (↑(nonUniversalVertices G) : Set A)).not_isDiag_of_mem_edgeFinset hf)
      he
  · intro z' hz'
    unfold weightedAttachedEdgeWeight singleTriangleWeight
    apply Fintype.sum_eq_zero
    intro f
    rw [if_neg]
    intro hEq
    apply hz'
    apply Subtype.ext
    have hzmem : (z' : A) ∈ ({(z : A), (u : A), (v : A)} : Finset A) := by
      rw [hEq]
      simp [attachedEdgeTriangle]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hzmem
    rcases hzmem with h | h | h
    · exact h
    · exact (universalVertex_not_mem_nonUniversalVertices G z'.property
        (h ▸ u.property)).elim
    · exact (universalVertex_not_mem_nonUniversalVertices G z'.property
        (h ▸ v.property)).elim

lemma d7UZZCorrection_apply_UUZ_eq_zero
    (G : SimpleGraph A) (P : D7SeparatedParameters G)
    (u v : ↑(nonUniversalVertices G))
    (z : ↑(universalVertices G)) :
    d7UZZCorrection G P {(z : A), (u : A), (v : A)} = 0 := by
  unfold d7UZZCorrection weightedAttachedEdgeWeight singleTriangleWeight
  apply Fintype.sum_eq_zero
  intro u'
  apply Fintype.sum_eq_zero
  intro f
  rw [if_neg]
  intro hEq
  have hfND : ¬(f : Sym2 (↑(universalVertices G))).IsDiag :=
    (⊤ : SimpleGraph (↑(universalVertices G))).not_isDiag_of_mem_edgeFinset
      f.property
  have hmapSub : (f : Sym2 (↑(universalVertices G))).toFinset.map
      (inducedEmbedding (universalVertices G)) ⊆
        ({(z : A), (u : A), (v : A)} : Finset A) := by
    intro x hx
    rw [hEq]
    simp only [attachedEdgeTriangle, Finset.mem_insert]
    exact Or.inr hx
  have hmapSingleton : (f : Sym2 (↑(universalVertices G))).toFinset.map
      (inducedEmbedding (universalVertices G)) ⊆ ({(z : A)} : Finset A) := by
    intro x hx
    have hxTarget := hmapSub hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxTarget ⊢
    rcases hxTarget with hxz | hxu | hxv
    · exact hxz
    · obtain ⟨x', hx', rfl⟩ := Finset.mem_map.mp hx
      apply (universalVertex_not_mem_nonUniversalVertices G x'.property).elim
      change (x' : A) = (u : A) at hxu
      rw [hxu]
      exact u.property
    · obtain ⟨x', hx', rfl⟩ := Finset.mem_map.mp hx
      apply (universalVertex_not_mem_nonUniversalVertices G x'.property).elim
      change (x' : A) = (v : A) at hxv
      rw [hxv]
      exact v.property
  have hcardMap : ((f : Sym2 (↑(universalVertices G))).toFinset.map
      (inducedEmbedding (universalVertices G))).card = 2 := by
    rw [Finset.card_map, Sym2.card_toFinset_of_not_isDiag _ hfND]
  have hcardLe := Finset.card_le_card hmapSingleton
  rw [hcardMap, Finset.card_singleton] at hcardLe
  omega

lemma d7ZZZCorrection_apply_UUZ_eq_zero
    (G : SimpleGraph A) (P : D7SeparatedParameters G)
    (u v : ↑(nonUniversalVertices G))
    (z : ↑(universalVertices G)) :
    d7ZZZCorrection G P {(z : A), (u : A), (v : A)} = 0 := by
  unfold d7ZZZCorrection singleTriangleWeight
  apply Fintype.sum_eq_zero
  intro q
  rw [if_neg]
  intro hEq
  have huq : (u : A) ∈ (q : Finset A) := by
    rw [← hEq]
    simp
  have huZ := (Finset.mem_powersetCard.mp q.property).1 huq
  exact nonUniversalVertex_not_mem_universalVertices G u.property huZ

lemma d7LargeCorrection_apply_UUZ
    (G : SimpleGraph A) (P : D7SeparatedParameters G)
    (u v : ↑(nonUniversalVertices G)) (huv : u ≠ v)
    (z : ↑(universalVertices G))
    (he : s(u, v) ∈ (G.induce
      (↑(nonUniversalVertices G) : Set A)).edgeFinset) :
    d7LargeCorrection G P {(z : A), (u : A), (v : A)} = P.beta s(u, v) := by
  unfold d7LargeCorrection
  rw [d7UUZCorrection_apply G P u v huv z he,
    d7UZZCorrection_apply_UUZ_eq_zero G P u v z,
    d7ZZZCorrection_apply_UUZ_eq_zero G P u v z]
  ring

lemma IsHalfBounded.extendInducedGraph
    {G : SimpleGraph A} {S : Finset A} {w : Finset S → ℝ}
    (hw : IsHalfBounded (G.induce (↑S : Set A)) w) :
    IsHalfBounded G (extendInducedWeight S w) := by
  intro t ht
  by_cases hsub : t ⊆ S
  · let q : Finset S := restrictToInduced S t hsub
    have hmap : q.map (inducedEmbedding S) = t := by
      simpa only [q, restrictToInduced, inducedEmbedding] using
        (Finset.subtype_map_of_mem hsub)
    rw [extendInducedWeight, dif_pos hsub]
    apply hw q
    apply SimpleGraph.mem_cliqueFinset_iff.mpr
    rw [SimpleGraph.isNClique_induce_iff,
      ← inducedEmbedding_eq_setEmbedding S, hmap]
    exact SimpleGraph.mem_cliqueFinset_iff.mp ht
  · rw [extendInducedWeight_eq_zero hsub]
    norm_num

lemma d7LiftedWeight_eq_zero_of_mem
    (G : SimpleGraph A) (z : ↑(universalVertices G))
    (w : Finset (↑(d7DeletedFinset (A := A) (z : A))) → ℝ)
    {t : Finset A} (hz : (z : A) ∈ t) :
    d7LiftedWeight (z : A) w t = 0 := by
  apply extendInducedWeight_eq_zero
  intro hsub
  have hzdel := hsub hz
  simp [d7DeletedFinset] at hzdel

lemma d7LiftedWeight_le_half
    (G : SimpleGraph A) (z : ↑(universalVertices G))
    {w : Finset (↑(d7DeletedFinset (A := A) (z : A))) → ℝ}
    (hw : IsHalfBounded (d7DeletedGraph G (z : A)) w)
    {t : Finset A} (ht : t ∈ G.cliqueFinset 3) :
    d7LiftedWeight (z : A) w t ≤ 1 / 2 := by
  exact hw.extendInducedGraph t ht

lemma IsFractionalPacking.weight_le_fractionalEdgeLoad
    {G : SimpleGraph A} {w : Finset A → ℝ}
    (hw : IsFractionalPacking G w) {t : Finset A}
    (ht : t ∈ G.cliqueFinset 3) {e : Sym2 A} (het : e ∈ t.sym2) :
    w t ≤ fractionalEdgeLoad G w e := by
  unfold fractionalEdgeLoad
  apply Finset.single_le_sum
  · intro q hq
    exact hw.nonneg_on (Finset.mem_filter.mp hq).1
  · exact Finset.mem_filter.mpr ⟨ht, het⟩

lemma d7LiftedWeight_add_beta_le_one
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G))
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (P : D7SeparatedParameters G)
    (hreal : P.RealizesCoherentFamily G z₀ w₀)
    (hwPacking : ∀ z : ↑(universalVertices G),
      IsFractionalPacking (d7DeletedGraph G (z : A))
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z))
    (hwOne : ∀ z : ↑(universalVertices G),
      1 ≤ fractionalUncoveredWeight (d7DeletedGraph G (z : A))
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z))
    (u v : ↑(nonUniversalVertices G)) (huv : u ≠ v)
    (z y : ↑(universalVertices G))
    (he : s(u, v) ∈ (G.induce
      (↑(nonUniversalVertices G) : Set A)).edgeFinset)
    (ht : ({(z : A), (u : A), (v : A)} : Finset A) ∈
      G.cliqueFinset 3) :
    d7LiftedWeight (y : A)
        (d7CoherentUniversalDeletedWeight G z₀ w₀ y)
        {(z : A), (u : A), (v : A)} + P.beta s(u, v) ≤ 1 := by
  let e : Sym2 (↑(nonUniversalVertices G)) := s(u, v)
  let w := d7CoherentUniversalDeletedWeight G z₀ w₀ y
  have hwLift : IsFractionalPacking G (d7LiftedWeight (y : A) w) := by
    exact IsFractionalPacking.extendInduced (G := G)
      (S := d7DeletedFinset (y : A)) (hwPacking y)
  have het : (inducedEmbedding (nonUniversalVertices G)).sym2Map e ∈
      ({(z : A), (u : A), (v : A)} : Finset A).sym2 := by
    simp only [e, Sym2.map_mk, inducedEmbedding_apply,
      Finset.mk_mem_sym2_iff]
    simp
  have hweight := hwLift.weight_le_fractionalEdgeLoad ht het
  rw [fractionalEdgeLoad_d7LiftedWeight_nonUniversal G y w e] at hweight
  have heDel := d7NonUniversalDeletedEdge_mem G y e he
  have hsplit := fractionalEdgeLoad_add_separated_add_remaining_eq_one
    (d7DeletedGraph G (y : A)) w
    ((d7NonUniversalDeletedEmbedding G y).sym2Map e) heDel
  have hbeta := hreal.beta_eq y e he
  have hrem := d7RemainingResidual_nonneg (hwPacking y) (hwOne y)
    ((d7NonUniversalDeletedEmbedding G y).sym2Map e)
  change d7SeparatedUnit (d7DeletedGraph G (y : A)) w
      ((d7NonUniversalDeletedEmbedding G y).sym2Map e) = P.beta e at hbeta
  rw [hbeta] at hsplit
  change _ + P.beta e ≤ 1
  linarith

lemma sum_le_two_exception {B : Type} [Fintype B] [DecidableEq B]
    (f : B → ℝ) (x y : B) (hxy : x ≠ y)
    (ax ay c : ℝ) (hx : f x ≤ ax) (hy : f y ≤ ay)
    (hrest : ∀ z, z ≠ x → z ≠ y → f z ≤ c) :
    (∑ z : B, f z) ≤ ax + ay + ((Fintype.card B : ℝ) - 2) * c := by
  calc
    (∑ z : B, f z) ≤
        ∑ z : B, if z = x then ax else if z = y then ay else c := by
      apply Finset.sum_le_sum
      intro z _
      by_cases hzx : z = x
      · subst z
        rw [if_pos rfl]
        exact hx
      · rw [if_neg hzx]
        by_cases hzy : z = y
        · subst z
          rw [if_pos rfl]
          exact hy
        · rw [if_neg hzy]
          exact hrest z hzx hzy
    _ = ax + ay + ((Fintype.card B : ℝ) - 2) * c := by
      have hpoint : ∀ z : B,
          (if z = x then ax else if z = y then ay else c) =
            (if z = x ∨ z = y then 0 else c) +
              (if z = x then ax else 0) +
              (if z = y then ay else 0) := by
        intro z
        by_cases hzx : z = x
        · subst z
          simp [hxy]
        · by_cases hzy : z = y
          · subst z
            simp [hxy, hzx]
          · simp [hzx, hzy]
      simp_rw [hpoint, Finset.sum_add_distrib,
        sum_ite_eq_zero_else_two x y hxy]
      simp [add_assoc, add_left_comm, add_comm]

lemma d7LargeAverageWeight_UUZ_numerator_le
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G))
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (P : D7SeparatedParameters G)
    (hreal : P.RealizesCoherentFamily G z₀ w₀)
    (hm : 4 ≤ (universalVertices G).card)
    (hwPacking : ∀ z : ↑(universalVertices G),
      IsFractionalPacking (d7DeletedGraph G (z : A))
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z))
    (hwHalf : ∀ z : ↑(universalVertices G),
      IsHalfBounded (d7DeletedGraph G (z : A))
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z))
    (hwOne : ∀ z : ↑(universalVertices G),
      1 ≤ fractionalUncoveredWeight (d7DeletedGraph G (z : A))
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z))
    (u v : ↑(nonUniversalVertices G)) (huv : u ≠ v)
    (z : ↑(universalVertices G))
    (he : s(u, v) ∈ (G.induce
      (↑(nonUniversalVertices G) : Set A)).edgeFinset)
    (ht : ({(z : A), (u : A), (v : A)} : Finset A) ∈
      G.cliqueFinset 3) :
    (∑ y : ↑(universalVertices G),
      d7LiftedWeight (y : A)
        (d7CoherentUniversalDeletedWeight G z₀ w₀ y)
        {(z : A), (u : A), (v : A)}) +
      d7LargeCorrection G P {(z : A), (u : A), (v : A)} ≤
        ((universalVertices G).card : ℝ) / 2 := by
  have hcardZ : Fintype.card (↑(universalVertices G)) =
      (universalVertices G).card := Fintype.card_coe _
  obtain ⟨y, hyz⟩ := Fintype.exists_ne_of_one_lt_card
    (α := ↑(universalVertices G)) (by rw [hcardZ]; omega) z
  rw [d7LargeCorrection_apply_UUZ G P u v huv z he]
  let f : ↑(universalVertices G) → ℝ := fun x ↦
    d7LiftedWeight (x : A)
      (d7CoherentUniversalDeletedWeight G z₀ w₀ x)
      {(z : A), (u : A), (v : A)}
  have hfz : f z ≤ 0 := by
    rw [show f z = 0 by
      exact d7LiftedWeight_eq_zero_of_mem G z _ (by simp)]
  have hfy : f y ≤ 1 - P.beta s(u, v) := by
    have hpair := d7LiftedWeight_add_beta_le_one G z₀ w₀ P hreal
      hwPacking hwOne u v huv z y he ht
    dsimp only [f]
    linarith
  have hrest : ∀ x, x ≠ z → x ≠ y → f x ≤ 1 / 2 := by
    intro x _ _
    exact d7LiftedWeight_le_half G x (hwHalf x) ht
  have hsum := sum_le_two_exception f z y hyz.symm 0
    (1 - P.beta s(u, v)) (1 / 2) hfz hfy hrest
  dsimp only [f] at hsum
  rw [hcardZ] at hsum
  linarith

lemma d7UUZCorrection_apply_UZZ_eq_zero
    (G : SimpleGraph A) (P : D7SeparatedParameters G)
    (u : ↑(nonUniversalVertices G))
    (x y : ↑(universalVertices G)) :
    d7UUZCorrection G P {(u : A), (x : A), (y : A)} = 0 := by
  unfold d7UUZCorrection weightedAttachedEdgeWeight singleTriangleWeight
  apply Fintype.sum_eq_zero
  intro z
  apply Fintype.sum_eq_zero
  intro e
  rw [if_neg]
  intro hEq
  have heND : ¬(e : Sym2 (↑(nonUniversalVertices G))).IsDiag :=
    (G.induce (↑(nonUniversalVertices G) : Set A)).not_isDiag_of_mem_edgeFinset
      e.property
  have hmapSub : (e : Sym2 (↑(nonUniversalVertices G))).toFinset.map
      (inducedEmbedding (nonUniversalVertices G)) ⊆
        ({(u : A), (x : A), (y : A)} : Finset A) := by
    intro a ha
    rw [hEq]
    simp only [attachedEdgeTriangle, Finset.mem_insert]
    exact Or.inr ha
  have hmapSingleton : (e : Sym2 (↑(nonUniversalVertices G))).toFinset.map
      (inducedEmbedding (nonUniversalVertices G)) ⊆ ({(u : A)} : Finset A) := by
    intro a ha
    have haTarget := hmapSub ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at haTarget ⊢
    rcases haTarget with hau | hax | hay
    · exact hau
    · obtain ⟨a', ha', rfl⟩ := Finset.mem_map.mp ha
      apply (nonUniversalVertex_not_mem_universalVertices G a'.property).elim
      change (a' : A) = (x : A) at hax
      rw [hax]
      exact x.property
    · obtain ⟨a', ha', rfl⟩ := Finset.mem_map.mp ha
      apply (nonUniversalVertex_not_mem_universalVertices G a'.property).elim
      change (a' : A) = (y : A) at hay
      rw [hay]
      exact y.property
  have hcardMap : ((e : Sym2 (↑(nonUniversalVertices G))).toFinset.map
      (inducedEmbedding (nonUniversalVertices G))).card = 2 := by
    rw [Finset.card_map, Sym2.card_toFinset_of_not_isDiag _ heND]
  have hcardLe := Finset.card_le_card hmapSingleton
  rw [hcardMap, Finset.card_singleton] at hcardLe
  omega

lemma d7UZZCorrection_apply
    (G : SimpleGraph A) (P : D7SeparatedParameters G)
    (u : ↑(nonUniversalVertices G))
    (x y : ↑(universalVertices G)) (hxy : x ≠ y) :
    d7UZZCorrection G P {(u : A), (x : A), (y : A)} =
      P.largeMixedCoefficient u := by
  let e : Sym2 (↑(universalVertices G)) := s(x, y)
  have he : e ∈ (⊤ : SimpleGraph
      (↑(universalVertices G))).edgeFinset := by
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact hxy
  have htriangle : attachedEdgeTriangle (universalVertices G) (u : A) e =
      ({(u : A), (x : A), (y : A)} : Finset A) := by
    simp only [attachedEdgeTriangle, e, Sym2.toFinset_mk_eq,
      Finset.map_insert, Finset.map_singleton, inducedEmbedding_apply]
  unfold d7UZZCorrection
  rw [Fintype.sum_eq_single u]
  · rw [← htriangle]
    exact weightedAttachedEdgeWeight_apply_d7
      (nonUniversalVertex_not_mem_universalVertices G u.property)
      (fun f hf ↦
        (⊤ : SimpleGraph (↑(universalVertices G))).not_isDiag_of_mem_edgeFinset hf)
      he
  · intro u' hu'
    unfold weightedAttachedEdgeWeight singleTriangleWeight
    apply Fintype.sum_eq_zero
    intro f
    rw [if_neg]
    intro hEq
    apply hu'
    apply Subtype.ext
    have humem : (u' : A) ∈ ({(u : A), (x : A), (y : A)} : Finset A) := by
      rw [hEq]
      simp [attachedEdgeTriangle]
    simp only [Finset.mem_insert, Finset.mem_singleton] at humem
    rcases humem with h | h | h
    · exact h
    · exact (nonUniversalVertex_not_mem_universalVertices G u'.property
        (h ▸ x.property)).elim
    · exact (nonUniversalVertex_not_mem_universalVertices G u'.property
        (h ▸ y.property)).elim

lemma d7ZZZCorrection_apply_UZZ_eq_zero
    (G : SimpleGraph A) (P : D7SeparatedParameters G)
    (u : ↑(nonUniversalVertices G))
    (x y : ↑(universalVertices G)) :
    d7ZZZCorrection G P {(u : A), (x : A), (y : A)} = 0 := by
  unfold d7ZZZCorrection singleTriangleWeight
  apply Fintype.sum_eq_zero
  intro q
  rw [if_neg]
  intro hEq
  have huq : (u : A) ∈ (q : Finset A) := by
    rw [← hEq]
    simp
  have huZ := (Finset.mem_powersetCard.mp q.property).1 huq
  exact nonUniversalVertex_not_mem_universalVertices G u.property huZ

lemma d7LargeCorrection_apply_UZZ
    (G : SimpleGraph A) (P : D7SeparatedParameters G)
    (u : ↑(nonUniversalVertices G))
    (x y : ↑(universalVertices G)) (hxy : x ≠ y) :
    d7LargeCorrection G P {(u : A), (x : A), (y : A)} =
      P.largeMixedCoefficient u := by
  unfold d7LargeCorrection
  rw [d7UUZCorrection_apply_UZZ_eq_zero G P u x y,
    d7UZZCorrection_apply G P u x y hxy,
    d7ZZZCorrection_apply_UZZ_eq_zero G P u x y]
  ring

lemma d7LargeAverageWeight_UZZ_numerator_le
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G))
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (P : D7SeparatedParameters G)
    (hm : 4 ≤ (universalVertices G).card)
    (hwHalf : ∀ z : ↑(universalVertices G),
      IsHalfBounded (d7DeletedGraph G (z : A))
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z))
    (u : ↑(nonUniversalVertices G))
    (x y : ↑(universalVertices G)) (hxy : x ≠ y)
    (ht : ({(u : A), (x : A), (y : A)} : Finset A) ∈
      G.cliqueFinset 3) :
    (∑ z : ↑(universalVertices G),
      d7LiftedWeight (z : A)
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z)
        {(u : A), (x : A), (y : A)}) +
      d7LargeCorrection G P {(u : A), (x : A), (y : A)} ≤
        ((universalVertices G).card : ℝ) / 2 := by
  rw [d7LargeCorrection_apply_UZZ G P u x y hxy]
  let f : ↑(universalVertices G) → ℝ := fun z ↦
    d7LiftedWeight (z : A)
      (d7CoherentUniversalDeletedWeight G z₀ w₀ z)
      {(u : A), (x : A), (y : A)}
  have hfx : f x ≤ 0 := by
    rw [show f x = 0 by
      exact d7LiftedWeight_eq_zero_of_mem G x _ (by simp)]
  have hfy : f y ≤ 0 := by
    rw [show f y = 0 by
      exact d7LiftedWeight_eq_zero_of_mem G y _ (by simp)]
  have hrest : ∀ z, z ≠ x → z ≠ y → f z ≤ 1 / 2 := by
    intro z _ _
    exact d7LiftedWeight_le_half G z (hwHalf z) ht
  have hsum := sum_le_two_exception f x y hxy 0 0 (1 / 2)
    hfx hfy hrest
  have hcardZ : Fintype.card (↑(universalVertices G)) =
      (universalVertices G).card := Fintype.card_coe _
  dsimp only [f] at hsum
  rw [hcardZ] at hsum
  have hcorr := P.largeMixedCoefficient_le_one hm u
  linarith

lemma d7UUZCorrection_apply_ZZZ_eq_zero
    (G : SimpleGraph A) (P : D7SeparatedParameters G)
    (x y z : ↑(universalVertices G)) :
    d7UUZCorrection G P {(x : A), (y : A), (z : A)} = 0 := by
  unfold d7UUZCorrection weightedAttachedEdgeWeight singleTriangleWeight
  apply Fintype.sum_eq_zero
  intro z'
  apply Fintype.sum_eq_zero
  intro e
  rw [if_neg]
  intro hEq
  obtain ⟨u, hu⟩ := Finset.nonempty_iff_ne_empty.mpr
    (Sym2.toFinset_ne_empty (e : Sym2 (↑(nonUniversalVertices G))))
  have huMap : (u : A) ∈ ({(x : A), (y : A), (z : A)} : Finset A) := by
    rw [hEq]
    simp only [attachedEdgeTriangle, Finset.mem_insert]
    right
    exact Finset.mem_map.mpr ⟨u, hu, rfl⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at huMap
  rcases huMap with h | h | h
  · apply (nonUniversalVertex_not_mem_universalVertices G u.property).elim
    change (u : A) = (x : A) at h
    rw [h]
    exact x.property
  · apply (nonUniversalVertex_not_mem_universalVertices G u.property).elim
    change (u : A) = (y : A) at h
    rw [h]
    exact y.property
  · apply (nonUniversalVertex_not_mem_universalVertices G u.property).elim
    change (u : A) = (z : A) at h
    rw [h]
    exact z.property

lemma d7UZZCorrection_apply_ZZZ_eq_zero
    (G : SimpleGraph A) (P : D7SeparatedParameters G)
    (x y z : ↑(universalVertices G)) :
    d7UZZCorrection G P {(x : A), (y : A), (z : A)} = 0 := by
  unfold d7UZZCorrection weightedAttachedEdgeWeight singleTriangleWeight
  apply Fintype.sum_eq_zero
  intro u
  apply Fintype.sum_eq_zero
  intro e
  rw [if_neg]
  intro hEq
  have huTarget : (u : A) ∈
      ({(x : A), (y : A), (z : A)} : Finset A) := by
    rw [hEq]
    simp [attachedEdgeTriangle]
  simp only [Finset.mem_insert, Finset.mem_singleton] at huTarget
  rcases huTarget with h | h | h
  · exact (nonUniversalVertex_not_mem_universalVertices G u.property
      (h ▸ x.property)).elim
  · exact (nonUniversalVertex_not_mem_universalVertices G u.property
      (h ▸ y.property)).elim
  · exact (nonUniversalVertex_not_mem_universalVertices G u.property
      (h ▸ z.property)).elim

lemma d7ZZZCorrection_apply
    (G : SimpleGraph A) (P : D7SeparatedParameters G)
    (x y z : ↑(universalVertices G))
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    d7ZZZCorrection G P {(x : A), (y : A), (z : A)} =
      P.largeUniversalCoefficient := by
  have hxyA : (x : A) ≠ (y : A) := fun h ↦ hxy (Subtype.ext h)
  have hxzA : (x : A) ≠ (z : A) := fun h ↦ hxz (Subtype.ext h)
  have hyzA : (y : A) ≠ (z : A) := fun h ↦ hyz (Subtype.ext h)
  let q0 : Finset A := {(x : A), (y : A), (z : A)}
  have hqsub : q0 ⊆ universalVertices G := by
    intro a ha
    simp only [q0, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · exact x.property
    · exact y.property
    · exact z.property
  have hqcard : q0.card = 3 := by
    simp [q0, hxyA, hxzA, hyzA]
  let q : ↑((universalVertices G).powersetCard 3) :=
    ⟨q0, Finset.mem_powersetCard.mpr ⟨hqsub, hqcard⟩⟩
  unfold d7ZZZCorrection singleTriangleWeight
  rw [Fintype.sum_eq_single q]
  · dsimp only [q, q0]
    rw [if_pos rfl]
  · intro q' hne
    rw [if_neg]
    intro hEq
    apply hne
    apply Subtype.ext
    exact hEq.symm

lemma d7LargeCorrection_apply_ZZZ
    (G : SimpleGraph A) (P : D7SeparatedParameters G)
    (x y z : ↑(universalVertices G))
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    d7LargeCorrection G P {(x : A), (y : A), (z : A)} =
      P.largeUniversalCoefficient := by
  unfold d7LargeCorrection
  rw [d7UUZCorrection_apply_ZZZ_eq_zero G P x y z,
    d7UZZCorrection_apply_ZZZ_eq_zero G P x y z,
    d7ZZZCorrection_apply G P x y z hxy hxz hyz]
  ring

lemma sum_ite_eq_zero_else_three {B : Type} [Fintype B] [DecidableEq B]
    (x y z : B) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (c : ℝ) :
    (∑ w : B, if w = x ∨ w = y ∨ w = z then 0 else c) =
      ((Fintype.card B : ℝ) - 3) * c := by
  rw [Finset.sum_ite]
  have hfalse : (Finset.univ : Finset B).filter
      (fun w ↦ ¬(w = x ∨ w = y ∨ w = z)) =
      (Finset.univ : Finset B) \ {x, y, z} := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
  have htriple : ({x, y, z} : Finset B).card = 3 := by
    simp [hxy, hxz, hyz]
  have hcard : ((Finset.univ : Finset B).filter
      (fun w ↦ ¬(w = x ∨ w = y ∨ w = z))).card = Fintype.card B - 3 := by
    rw [hfalse, Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ, htriple]
  rw [Finset.sum_const_zero, zero_add, Finset.sum_const, hcard]
  simp only [nsmul_eq_mul]
  have hthree : 3 ≤ Fintype.card B := by
    have hsub : ({x, y, z} : Finset B) ⊆ Finset.univ := Finset.subset_univ _
    have := Finset.card_le_card hsub
    simpa only [htriple, Finset.card_univ] using this
  rw [Nat.cast_sub hthree, Nat.cast_ofNat]

lemma sum_le_three_zero {B : Type} [Fintype B] [DecidableEq B]
    (f : B → ℝ) (x y z : B)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hx : f x ≤ 0) (hy : f y ≤ 0) (hz : f z ≤ 0)
    (hrest : ∀ w, w ≠ x → w ≠ y → w ≠ z → f w ≤ 1 / 2) :
    (∑ w : B, f w) ≤ ((Fintype.card B : ℝ) - 3) * (1 / 2) := by
  calc
    (∑ w : B, f w) ≤
        ∑ w : B, if w = x ∨ w = y ∨ w = z then 0 else 1 / 2 := by
      apply Finset.sum_le_sum
      intro w _
      by_cases hwx : w = x
      · subst w
        rw [if_pos (Or.inl rfl)]
        exact hx
      · by_cases hwy : w = y
        · subst w
          rw [if_pos (Or.inr (Or.inl rfl))]
          exact hy
        · by_cases hwz : w = z
          · subst w
            rw [if_pos (Or.inr (Or.inr rfl))]
            exact hz
          · rw [if_neg]
            · exact hrest w hwx hwy hwz
            · tauto
    _ = ((Fintype.card B : ℝ) - 3) * (1 / 2) :=
      sum_ite_eq_zero_else_three x y z hxy hxz hyz (1 / 2)

lemma d7LargeAverageWeight_ZZZ_numerator_le
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G))
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (P : D7SeparatedParameters G)
    (hn : 14 ≤ Fintype.card A)
    (hm : 4 ≤ (universalVertices G).card)
    (hlarge : Fintype.card A - 7 ≤ (universalVertices G).card)
    (hwHalf : ∀ z : ↑(universalVertices G),
      IsHalfBounded (d7DeletedGraph G (z : A))
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z))
    (x y z : ↑(universalVertices G))
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (ht : ({(x : A), (y : A), (z : A)} : Finset A) ∈
      G.cliqueFinset 3) :
    (∑ w : ↑(universalVertices G),
      d7LiftedWeight (w : A)
        (d7CoherentUniversalDeletedWeight G z₀ w₀ w)
        {(x : A), (y : A), (z : A)}) +
      d7LargeCorrection G P {(x : A), (y : A), (z : A)} ≤
        ((universalVertices G).card : ℝ) / 2 := by
  rw [d7LargeCorrection_apply_ZZZ G P x y z hxy hxz hyz]
  let f : ↑(universalVertices G) → ℝ := fun w ↦
    d7LiftedWeight (w : A)
      (d7CoherentUniversalDeletedWeight G z₀ w₀ w)
      {(x : A), (y : A), (z : A)}
  have hfx : f x ≤ 0 := by
    rw [show f x = 0 by
      exact d7LiftedWeight_eq_zero_of_mem G x _ (by simp)]
  have hfy : f y ≤ 0 := by
    rw [show f y = 0 by
      exact d7LiftedWeight_eq_zero_of_mem G y _ (by simp)]
  have hfz : f z ≤ 0 := by
    rw [show f z = 0 by
      exact d7LiftedWeight_eq_zero_of_mem G z _ (by simp)]
  have hrest : ∀ w, w ≠ x → w ≠ y → w ≠ z → f w ≤ 1 / 2 := by
    intro w _ _ _
    exact d7LiftedWeight_le_half G w (hwHalf w) ht
  have hsum := sum_le_three_zero f x y z hxy hxz hyz hfx hfy hfz hrest
  have hcardZ : Fintype.card (↑(universalVertices G)) =
      (universalVertices G).card := Fintype.card_coe _
  dsimp only [f] at hsum
  rw [hcardZ] at hsum
  have hcorr := P.largeUniversalCoefficient_le_one hn hm hlarge
  linarith

lemma d7UUZCorrection_apply_UUU_eq_zero
    (G : SimpleGraph A) (P : D7SeparatedParameters G)
    (u v w : ↑(nonUniversalVertices G)) :
    d7UUZCorrection G P {(u : A), (v : A), (w : A)} = 0 := by
  unfold d7UUZCorrection weightedAttachedEdgeWeight singleTriangleWeight
  apply Fintype.sum_eq_zero
  intro z
  apply Fintype.sum_eq_zero
  intro e
  rw [if_neg]
  intro hEq
  have hzTarget : (z : A) ∈
      ({(u : A), (v : A), (w : A)} : Finset A) := by
    rw [hEq]
    simp [attachedEdgeTriangle]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hzTarget
  rcases hzTarget with h | h | h
  · exact (universalVertex_not_mem_nonUniversalVertices G z.property
      (h ▸ u.property)).elim
  · exact (universalVertex_not_mem_nonUniversalVertices G z.property
      (h ▸ v.property)).elim
  · exact (universalVertex_not_mem_nonUniversalVertices G z.property
      (h ▸ w.property)).elim

lemma d7UZZCorrection_apply_UUU_eq_zero
    (G : SimpleGraph A) (P : D7SeparatedParameters G)
    (u v w : ↑(nonUniversalVertices G)) :
    d7UZZCorrection G P {(u : A), (v : A), (w : A)} = 0 := by
  unfold d7UZZCorrection weightedAttachedEdgeWeight singleTriangleWeight
  apply Fintype.sum_eq_zero
  intro u'
  apply Fintype.sum_eq_zero
  intro e
  rw [if_neg]
  intro hEq
  obtain ⟨z, hz⟩ := Finset.nonempty_iff_ne_empty.mpr
    (Sym2.toFinset_ne_empty (e : Sym2 (↑(universalVertices G))))
  have hzMap : (z : A) ∈ ({(u : A), (v : A), (w : A)} : Finset A) := by
    rw [hEq]
    simp only [attachedEdgeTriangle, Finset.mem_insert]
    right
    exact Finset.mem_map.mpr ⟨z, hz, rfl⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hzMap
  rcases hzMap with h | h | h
  · exact (universalVertex_not_mem_nonUniversalVertices G z.property
      (h ▸ u.property)).elim
  · exact (universalVertex_not_mem_nonUniversalVertices G z.property
      (h ▸ v.property)).elim
  · exact (universalVertex_not_mem_nonUniversalVertices G z.property
      (h ▸ w.property)).elim

lemma d7ZZZCorrection_apply_UUU_eq_zero
    (G : SimpleGraph A) (P : D7SeparatedParameters G)
    (u v w : ↑(nonUniversalVertices G)) :
    d7ZZZCorrection G P {(u : A), (v : A), (w : A)} = 0 := by
  unfold d7ZZZCorrection singleTriangleWeight
  apply Fintype.sum_eq_zero
  intro q
  rw [if_neg]
  intro hEq
  have hqne : (q : Finset A) ≠ ∅ := by
    intro hzero
    have hcard := (Finset.mem_powersetCard.mp q.property).2
    rw [hzero, Finset.card_empty] at hcard
    omega
  obtain ⟨z, hzq⟩ := Finset.nonempty_iff_ne_empty.mpr hqne
  have hzTarget : z ∈ ({(u : A), (v : A), (w : A)} : Finset A) := by
    rw [hEq]
    exact hzq
  have hzZ := (Finset.mem_powersetCard.mp q.property).1 hzq
  simp only [Finset.mem_insert, Finset.mem_singleton] at hzTarget
  rcases hzTarget with h | h | h
  · exact (nonUniversalVertex_not_mem_universalVertices G u.property
      (h ▸ hzZ)).elim
  · exact (nonUniversalVertex_not_mem_universalVertices G v.property
      (h ▸ hzZ)).elim
  · exact (nonUniversalVertex_not_mem_universalVertices G w.property
      (h ▸ hzZ)).elim

lemma d7LargeCorrection_apply_UUU_eq_zero
    (G : SimpleGraph A) (P : D7SeparatedParameters G)
    (u v w : ↑(nonUniversalVertices G)) :
    d7LargeCorrection G P {(u : A), (v : A), (w : A)} = 0 := by
  unfold d7LargeCorrection
  rw [d7UUZCorrection_apply_UUU_eq_zero G P u v w,
    d7UZZCorrection_apply_UUU_eq_zero G P u v w,
    d7ZZZCorrection_apply_UUU_eq_zero G P u v w]
  ring

lemma d7LargeAverageWeight_UUU_numerator_le
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G))
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (P : D7SeparatedParameters G)
    (hwHalf : ∀ z : ↑(universalVertices G),
      IsHalfBounded (d7DeletedGraph G (z : A))
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z))
    (u v w : ↑(nonUniversalVertices G))
    (ht : ({(u : A), (v : A), (w : A)} : Finset A) ∈
      G.cliqueFinset 3) :
    (∑ z : ↑(universalVertices G),
      d7LiftedWeight (z : A)
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z)
        {(u : A), (v : A), (w : A)}) +
      d7LargeCorrection G P {(u : A), (v : A), (w : A)} ≤
        ((universalVertices G).card : ℝ) / 2 := by
  rw [d7LargeCorrection_apply_UUU_eq_zero G P u v w, add_zero]
  calc
    (∑ z : ↑(universalVertices G),
      d7LiftedWeight (z : A)
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z)
        {(u : A), (v : A), (w : A)}) ≤
        ∑ _z : ↑(universalVertices G), (1 / 2 : ℝ) := by
      apply Finset.sum_le_sum
      intro z _
      exact d7LiftedWeight_le_half G z (hwHalf z) ht
    _ = ((universalVertices G).card : ℝ) / 2 := by
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
        Fintype.card_coe]
      ring

private lemma d7LargeAverageWeight_numerator_le_of_mem_universal_left
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G))
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (P : D7SeparatedParameters G)
    (hreal : P.RealizesCoherentFamily G z₀ w₀)
    (hn : 14 ≤ Fintype.card A)
    (hm : 4 ≤ (universalVertices G).card)
    (hlarge : Fintype.card A - 7 ≤ (universalVertices G).card)
    (hwPacking : ∀ z : ↑(universalVertices G),
      IsFractionalPacking (d7DeletedGraph G (z : A))
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z))
    (hwHalf : ∀ z : ↑(universalVertices G),
      IsHalfBounded (d7DeletedGraph G (z : A))
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z))
    (hwOne : ∀ z : ↑(universalVertices G),
      1 ≤ fractionalUncoveredWeight (d7DeletedGraph G (z : A))
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z))
    {a b c : A} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ht : ({a, b, c} : Finset A) ∈ G.cliqueFinset 3)
    (haZ : a ∈ universalVertices G) :
    (∑ z : ↑(universalVertices G),
      d7LiftedWeight (z : A)
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z) {a, b, c}) +
        d7LargeCorrection G P {a, b, c} ≤
          ((universalVertices G).card : ℝ) / 2 := by
  have htri := SimpleGraph.mem_cliqueFinset_iff.mp ht
  have hadj := SimpleGraph.is3Clique_triple_iff.mp htri
  have nonUniversal_of_not_universal : ∀ {v : A},
      v ∉ universalVertices G → v ∈ nonUniversalVertices G := by
    intro v hv
    apply mem_nonUniversalVertices.mpr
    have hvne : Gᶜ.degree v ≠ 0 := by
      intro hz
      exact hv (mem_universalVertices.mpr hz)
    exact Nat.pos_of_ne_zero hvne
  let za : ↑(universalVertices G) := ⟨a, haZ⟩
  by_cases hbZ : b ∈ universalVertices G
  · let zb : ↑(universalVertices G) := ⟨b, hbZ⟩
    by_cases hcZ : c ∈ universalVertices G
    · let zc : ↑(universalVertices G) := ⟨c, hcZ⟩
      have hzab : za ≠ zb := fun h ↦ hab (congrArg Subtype.val h)
      have hzac : za ≠ zc := fun h ↦ hac (congrArg Subtype.val h)
      have hzbc : zb ≠ zc := fun h ↦ hbc (congrArg Subtype.val h)
      exact d7LargeAverageWeight_ZZZ_numerator_le G z₀ w₀ P hn hm hlarge
        hwHalf za zb zc hzab hzac hzbc ht
    · let uc : ↑(nonUniversalVertices G) :=
        ⟨c, nonUniversal_of_not_universal hcZ⟩
      have hzab : za ≠ zb := fun h ↦ hab (congrArg Subtype.val h)
      have hset : ({(uc : A), (za : A), (zb : A)} : Finset A) =
          ({a, b, c} : Finset A) := by
        ext x
        simp only [uc, za, zb, Finset.mem_insert, Finset.mem_singleton]
        tauto
      have htri' : ({(uc : A), (za : A), (zb : A)} : Finset A) ∈
          G.cliqueFinset 3 := by
        rw [hset]
        exact ht
      have hnum := d7LargeAverageWeight_UZZ_numerator_le G z₀ w₀ P hm
        hwHalf uc za zb hzab htri'
      rw [hset] at hnum
      exact hnum
  · let ub : ↑(nonUniversalVertices G) :=
      ⟨b, nonUniversal_of_not_universal hbZ⟩
    by_cases hcZ : c ∈ universalVertices G
    · let zc : ↑(universalVertices G) := ⟨c, hcZ⟩
      have hzac : za ≠ zc := fun h ↦ hac (congrArg Subtype.val h)
      have hset : ({(ub : A), (za : A), (zc : A)} : Finset A) =
          ({a, b, c} : Finset A) := by
        ext x
        simp only [ub, za, zc, Finset.mem_insert, Finset.mem_singleton]
        tauto
      have htri' : ({(ub : A), (za : A), (zc : A)} : Finset A) ∈
          G.cliqueFinset 3 := by
        rw [hset]
        exact ht
      have hnum := d7LargeAverageWeight_UZZ_numerator_le G z₀ w₀ P hm
        hwHalf ub za zc hzac htri'
      rw [hset] at hnum
      exact hnum
    · let uc : ↑(nonUniversalVertices G) :=
        ⟨c, nonUniversal_of_not_universal hcZ⟩
      have hubc : ub ≠ uc := fun h ↦ hbc (congrArg Subtype.val h)
      have he : s(ub, uc) ∈ (G.induce
          (↑(nonUniversalVertices G) : Set A)).edgeFinset := by
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
        change G.Adj b c
        exact hadj.2.2
      exact d7LargeAverageWeight_UUZ_numerator_le G z₀ w₀ P hreal hm
        hwPacking hwHalf hwOne ub uc hubc za he ht

private lemma d7LargeAverageWeight_numerator_le_of_not_mem_universal_left
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G))
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (P : D7SeparatedParameters G)
    (hreal : P.RealizesCoherentFamily G z₀ w₀)
    (hm : 4 ≤ (universalVertices G).card)
    (hwPacking : ∀ z : ↑(universalVertices G),
      IsFractionalPacking (d7DeletedGraph G (z : A))
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z))
    (hwHalf : ∀ z : ↑(universalVertices G),
      IsHalfBounded (d7DeletedGraph G (z : A))
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z))
    (hwOne : ∀ z : ↑(universalVertices G),
      1 ≤ fractionalUncoveredWeight (d7DeletedGraph G (z : A))
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z))
    {a b c : A} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ht : ({a, b, c} : Finset A) ∈ G.cliqueFinset 3)
    (haZ : a ∉ universalVertices G) :
    (∑ z : ↑(universalVertices G),
      d7LiftedWeight (z : A)
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z) {a, b, c}) +
        d7LargeCorrection G P {a, b, c} ≤
          ((universalVertices G).card : ℝ) / 2 := by
  have htri := SimpleGraph.mem_cliqueFinset_iff.mp ht
  have hadj := SimpleGraph.is3Clique_triple_iff.mp htri
  have nonUniversal_of_not_universal : ∀ {v : A},
      v ∉ universalVertices G → v ∈ nonUniversalVertices G := by
    intro v hv
    apply mem_nonUniversalVertices.mpr
    have hvne : Gᶜ.degree v ≠ 0 := by
      intro hz
      exact hv (mem_universalVertices.mpr hz)
    exact Nat.pos_of_ne_zero hvne
  let ua : ↑(nonUniversalVertices G) :=
    ⟨a, nonUniversal_of_not_universal haZ⟩
  by_cases hbZ : b ∈ universalVertices G
  · let zb : ↑(universalVertices G) := ⟨b, hbZ⟩
    by_cases hcZ : c ∈ universalVertices G
    · let zc : ↑(universalVertices G) := ⟨c, hcZ⟩
      have hzbc : zb ≠ zc := fun h ↦ hbc (congrArg Subtype.val h)
      exact d7LargeAverageWeight_UZZ_numerator_le G z₀ w₀ P hm hwHalf
        ua zb zc hzbc ht
    · let uc : ↑(nonUniversalVertices G) :=
        ⟨c, nonUniversal_of_not_universal hcZ⟩
      have huac : ua ≠ uc := fun h ↦ hac (congrArg Subtype.val h)
      have he : s(ua, uc) ∈ (G.induce
          (↑(nonUniversalVertices G) : Set A)).edgeFinset := by
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
        change G.Adj a c
        exact hadj.2.1
      have hset : ({(zb : A), (ua : A), (uc : A)} : Finset A) =
          ({a, b, c} : Finset A) := by
        ext x
        simp only [zb, ua, uc, Finset.mem_insert, Finset.mem_singleton]
        tauto
      have htri' : ({(zb : A), (ua : A), (uc : A)} : Finset A) ∈
          G.cliqueFinset 3 := by
        rw [hset]
        exact ht
      have hnum := d7LargeAverageWeight_UUZ_numerator_le G z₀ w₀ P hreal hm
        hwPacking hwHalf hwOne ua uc huac zb he htri'
      rw [hset] at hnum
      exact hnum
  · let ub : ↑(nonUniversalVertices G) :=
      ⟨b, nonUniversal_of_not_universal hbZ⟩
    by_cases hcZ : c ∈ universalVertices G
    · let zc : ↑(universalVertices G) := ⟨c, hcZ⟩
      have huab : ua ≠ ub := fun h ↦ hab (congrArg Subtype.val h)
      have he : s(ua, ub) ∈ (G.induce
          (↑(nonUniversalVertices G) : Set A)).edgeFinset := by
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
        change G.Adj a b
        exact hadj.1
      have hset : ({(zc : A), (ua : A), (ub : A)} : Finset A) =
          ({a, b, c} : Finset A) := by
        ext x
        simp only [zc, ua, ub, Finset.mem_insert, Finset.mem_singleton]
        tauto
      have htri' : ({(zc : A), (ua : A), (ub : A)} : Finset A) ∈
          G.cliqueFinset 3 := by
        rw [hset]
        exact ht
      have hnum := d7LargeAverageWeight_UUZ_numerator_le G z₀ w₀ P hreal hm
        hwPacking hwHalf hwOne ua ub huab zc he htri'
      rw [hset] at hnum
      exact hnum
    · let uc : ↑(nonUniversalVertices G) :=
        ⟨c, nonUniversal_of_not_universal hcZ⟩
      exact d7LargeAverageWeight_UUU_numerator_le G z₀ w₀ P hwHalf
        ua ub uc ht

/-- The symmetrized deletion inputs and the exact occurrence counts retain
the pointwise one-half bound in the corrected large-`m` average. -/
lemma d7LargeAverageWeight_halfBounded
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G))
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (P : D7SeparatedParameters G)
    (hreal : P.RealizesCoherentFamily G z₀ w₀)
    (hn : 14 ≤ Fintype.card A)
    (hm : 4 ≤ (universalVertices G).card)
    (hlarge : Fintype.card A - 7 ≤ (universalVertices G).card)
    (hwPacking : ∀ z : ↑(universalVertices G),
      IsFractionalPacking (d7DeletedGraph G (z : A))
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z))
    (hwHalf : ∀ z : ↑(universalVertices G),
      IsHalfBounded (d7DeletedGraph G (z : A))
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z))
    (hwOne : ∀ z : ↑(universalVertices G),
      1 ≤ fractionalUncoveredWeight (d7DeletedGraph G (z : A))
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z)) :
    IsHalfBounded G (d7LargeAverageWeight G z₀ w₀ P) := by
  intro t ht
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp
    (SimpleGraph.mem_cliqueFinset_iff.mp ht).card_eq
  have finish :
      (∑ z : ↑(universalVertices G),
        d7LiftedWeight (z : A)
          (d7CoherentUniversalDeletedWeight G z₀ w₀ z) {a, b, c}) +
          d7LargeCorrection G P {a, b, c} ≤
            ((universalVertices G).card : ℝ) / 2 →
        d7LargeAverageWeight G z₀ w₀ P {a, b, c} ≤ 1 / 2 := by
    intro hnum
    unfold d7LargeAverageWeight
    have hmR : 0 < ((universalVertices G).card : ℝ) := by
      exact_mod_cast (by omega : 0 < (universalVertices G).card)
    calc
      ((universalVertices G).card : ℝ)⁻¹ *
          ((∑ z : ↑(universalVertices G),
            d7LiftedWeight (z : A)
              (d7CoherentUniversalDeletedWeight G z₀ w₀ z) {a, b, c}) +
            d7LargeCorrection G P {a, b, c}) ≤
          ((universalVertices G).card : ℝ)⁻¹ *
            (((universalVertices G).card : ℝ) / 2) :=
        mul_le_mul_of_nonneg_left hnum (inv_nonneg.mpr hmR.le)
      _ = 1 / 2 := by field_simp
  by_cases haZ : a ∈ universalVertices G
  · apply finish
    exact d7LargeAverageWeight_numerator_le_of_mem_universal_left G z₀ w₀ P
      hreal hn hm hlarge hwPacking hwHalf hwOne hab hac hbc ht haZ
  · apply finish
    exact d7LargeAverageWeight_numerator_le_of_not_mem_universal_left G z₀ w₀ P
      hreal hm hwPacking hwHalf hwOne hab hac hbc ht haZ

/-- The corrected large-`m` average is a strong packing once its coherent
deletion family is supplied; the one-half bound is now discharged internally. -/
lemma hasStrongFractionalPacking_d7LargeAverageWeight
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G))
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (P : D7SeparatedParameters G)
    (hreal : P.RealizesCoherentFamily G z₀ w₀)
    (hn : 14 ≤ Fintype.card A)
    (hm : 4 ≤ (universalVertices G).card)
    (hlarge : Fintype.card A - 7 ≤ (universalVertices G).card)
    (hwPacking : ∀ z : ↑(universalVertices G),
      IsFractionalPacking (d7DeletedGraph G (z : A))
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z))
    (hwHalf : ∀ z : ↑(universalVertices G),
      IsHalfBounded (d7DeletedGraph G (z : A))
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z))
    (hwOne : ∀ z : ↑(universalVertices G),
      1 ≤ fractionalUncoveredWeight (d7DeletedGraph G (z : A))
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z))
    {a : ℝ}
    (hwUpper : fractionalUncoveredWeight
      (d7DeletedGraph G (z₀ : A)) w₀ ≤ a + 1) :
    HasStrongFractionalPacking G a := by
  apply hasStrongFractionalPacking_d7LargeAverageWeight_of_halfBounded G z₀
    w₀ P hreal hn hm hlarge hwPacking hwOne hwUpper
  exact d7LargeAverageWeight_halfBounded G z₀ w₀ P hreal hn hm hlarge
    hwPacking hwHalf hwOne

end

end Erdos76
