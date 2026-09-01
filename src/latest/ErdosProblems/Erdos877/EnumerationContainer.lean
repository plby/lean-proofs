/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos877.SchurHypergraph
import ErdosProblems.Erdos565.ContainerA
import ErdosProblems.Erdos565.ContainerConsistency
import ErdosProblems.Erdos565.SpecialContainerTheorem

/-!
# Containers for the distinct Schur hypergraph

This file instantiates the finite Campos--Samotij container algorithm from
`Erdos565` with the three-uniform hypergraph whose edges are the triples of
distinct elements of `[1,n]` satisfying `x + y = z`.  The repeated-summand
relations `x + x = 2x` are deliberately omitted here: every sum-free set is
still independent in this smaller hypergraph, and the elementary
supersaturation argument used later counts distinct-summand triples.
-/

open Finset

namespace Erdos877
namespace Enumeration

open Erdos565
open Erdos565.Hypergraph

section FiniteContainer

variable {n : ℕ} {p : ℝ}

/-- The rich finite output of the container algorithm for the Schur
hypergraph. -/
noncomputable def schurContainerOutput (I : Finset (Fin n))
    (hp : 0 < p) (hpmax : p ≤ 1 / 72)
    (hI : (schurHypergraph n).IsIndependent I) :
    ContainerA.FiniteContainerOutput (schurHypergraph n) I p 3 :=
  ContainerA.finiteContainer (schurHypergraph n) 3 p (by omega) hp (by
    norm_num at hpmax ⊢
    exact hpmax) (schurHypergraph_isUniform n) I hI

theorem schurContainer_fingerprint_subset (I : Finset (Fin n))
    (hp : 0 < p) (hpmax : p ≤ 1 / 72)
    (hI : (schurHypergraph n).IsIndependent I) :
    (schurContainerOutput I hp hpmax hI).fingerprint ⊆ I :=
  (schurContainerOutput I hp hpmax hI).fingerprint_subset

theorem schurContainer_input_subset (I : Finset (Fin n))
    (hp : 0 < p) (hpmax : p ≤ 1 / 72)
    (hI : (schurHypergraph n).IsIndependent I) :
    I ⊆ (schurContainerOutput I hp hpmax hI).container :=
  (schurContainerOutput I hp hpmax hI).input_subset

/-- The specialized fingerprint estimate `8 * 3^2 * p * n = 72pn`. -/
theorem schurContainer_fingerprint_card (I : Finset (Fin n))
    (hp : 0 < p) (hpmax : p ≤ 1 / 72)
    (hI : (schurHypergraph n).IsIndependent I) :
    ((schurContainerOutput I hp hpmax hI).fingerprint.card : ℝ) ≤
      72 * p * n := by
  have h := (schurContainerOutput I hp hpmax hI).fingerprint_card
  norm_num at h ⊢
  simpa only [mul_assoc] using h

/-- The residual cover returned by the algorithm has rank at most three.
This is an invariant of the finite update kernel; it is not a field of the
public output record, so we expose it here. -/
theorem schurContainer_cover_card_le_three (I : Finset (Fin n))
    (hp : 0 < p) (hpmax : p ≤ 1 / 72)
    (hI : (schurHypergraph n).IsIndependent I) :
    ∀ c ∈ (schurContainerOutput I hp hpmax hI).cover, c.card ≤ 3 := by
  intro c hc
  change c ∈ ContainerA.aboveOne
      (ContainerA.finalQuantState (schurHypergraph n) I p 3 (by omega) hp
        (by norm_num at hpmax ⊢; exact hpmax)
        (schurHypergraph_isUniform n) hI).1.family at hc
  exact (ContainerA.finalQuantState (schurHypergraph n) I p 3 (by omega) hp
    (by norm_num at hpmax ⊢; exact hpmax)
    (schurHypergraph_isUniform n) hI).2.family_bounded
      (ContainerA.mem_aboveOne.mp hc).1

end FiniteContainer

section CoverCounting

variable {V : Type*}

/-- A cover with codegree at most `D` covers at most `D` edges per cover
member.  This elementary union bound is the bridge between the weighted
container output and the Schur-edge count. -/
theorem card_le_cover_card_mul_of_degree_le
    {H C : Erdos565.Hypergraph V} {D : ℕ} [DecidableEq V]
    (hcover : ContainerA.Covers C H)
    (hdegree : ∀ c ∈ C, H.degree c ≤ D) :
    H.card ≤ C.card * D := by
  let fibers : Finset V → Erdos565.Hypergraph V :=
    fun c ↦ H.filter fun e ↦ c ⊆ e
  have hsub : H ⊆ C.biUnion fibers := by
    intro e he
    obtain ⟨c, hcC, hce⟩ := hcover he
    exact Finset.mem_biUnion.mpr
      ⟨c, hcC, Finset.mem_filter.mpr ⟨he, hce⟩⟩
  calc
    H.card ≤ (C.biUnion fibers).card := Finset.card_le_card hsub
    _ ≤ ∑ c ∈ C, (fibers c).card := Finset.card_biUnion_le
    _ ≤ ∑ _c ∈ C, D := by
      apply Finset.sum_le_sum
      intro c hc
      exact hdegree c hc
    _ = C.card * D := by simp

/-- If every cover member has size between two and three, its `p`-weight
controls its cardinality from below by `p^3 |C|`. -/
theorem cover_card_mul_cube_le_pWeight
    {C : Erdos565.Hypergraph V} {p : ℝ}
    (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hlo : ∀ c ∈ C, 2 ≤ c.card)
    (hhi : ∀ c ∈ C, c.card ≤ 3) :
    (C.card : ℝ) * p ^ 3 ≤ C.pWeight p := by
  classical
  rw [Erdos565.Hypergraph.pWeight, Erdos565.Hypergraph.weight]
  calc
    (C.card : ℝ) * p ^ 3 = ∑ _c ∈ C, p ^ 3 := by simp
    _ ≤ ∑ c ∈ C, p ^ c.card := by
      apply Finset.sum_le_sum
      intro c hc
      have hcard : c.card = 2 ∨ c.card = 3 := by
        have := hlo c hc
        have := hhi c hc
        omega
      rcases hcard with hcard | hcard
      · rw [hcard]
        nlinarith [mul_nonneg hp (mul_nonneg hp (sub_nonneg.mpr hp1))]
      · rw [hcard]

/-- Quantitative consequence of a rank-three weighted cover whose members
have codegree at most `D`.  The division-free form is convenient downstream.
-/
theorem sq_mul_card_le_of_weighted_cover
    {H C : Erdos565.Hypergraph V} {X : Finset V} {p : ℝ} {D : ℕ}
    [DecidableEq V]
    (hp : 0 < p) (hp1 : p ≤ 1)
    (hcover : ContainerA.Covers C H)
    (hlo : ∀ c ∈ C, 2 ≤ c.card)
    (hhi : ∀ c ∈ C, c.card ≤ 3)
    (hweight : C.pWeight p ≤ p * X.card)
    (hdegree : ∀ c ∈ C, H.degree c ≤ D) :
    p ^ 2 * (H.card : ℝ) ≤ D * (X.card : ℝ) := by
  have hCweight : (C.card : ℝ) * p ^ 3 ≤ p * X.card :=
    (cover_card_mul_cube_le_pWeight hp.le hp1 hlo hhi).trans hweight
  have hC : p ^ 2 * (C.card : ℝ) ≤ X.card := by
    apply le_of_mul_le_mul_left _ hp
    calc
      p * (p ^ 2 * (C.card : ℝ)) = (C.card : ℝ) * p ^ 3 := by ring
      _ ≤ p * X.card := hCweight
  have hHCnat : H.card ≤ C.card * D :=
    card_le_cover_card_mul_of_degree_le hcover hdegree
  have hHC : (H.card : ℝ) ≤ (C.card : ℝ) * D := by
    exact_mod_cast hHCnat
  calc
    p ^ 2 * (H.card : ℝ) ≤ p ^ 2 * ((C.card : ℝ) * D) :=
      mul_le_mul_of_nonneg_left hHC (sq_nonneg p)
    _ = D * (p ^ 2 * (C.card : ℝ)) := by ring
    _ ≤ D * (X.card : ℝ) :=
      mul_le_mul_of_nonneg_left hC (Nat.cast_nonneg D)

end CoverCounting

section SpecializedEdgeBound

variable {n : ℕ} {p : ℝ}

/-- The division-free Schur-edge estimate furnished by a finite container.
The local codegree hypothesis is discharged by the Schur-hypergraph
codegree lemma in the final public specialization. -/
theorem schurContainer_edge_bound_of_degree
    (I : Finset (Fin n)) (hp : 0 < p) (hp1 : p ≤ 1)
    (hpmax : p ≤ 1 / 72)
    (hI : (schurHypergraph n).IsIndependent I)
    (hdegree : ∀ c : Finset (Fin n), 2 ≤ c.card →
      (schurHypergraph n).degree c ≤ 6) :
    p ^ 2 * (((schurHypergraph n).restrict
      (schurContainerOutput I hp hpmax hI).container).card : ℝ) ≤
      6 * ((schurContainerOutput I hp hpmax hI).container.card : ℝ) := by
  let out := schurContainerOutput I hp hpmax hI
  apply sq_mul_card_le_of_weighted_cover hp hp1 out.covers out.edge_card
    (schurContainer_cover_card_le_three I hp hpmax hI) out.weight_le
  intro c hc
  exact (Erdos565.Hypergraph.degree_mono_left
      (Erdos565.Hypergraph.restrict_subset (schurHypergraph n) out.container) c).trans
    (hdegree c (out.edge_card c hc))

/-- Public finite-container estimate for the restricted Schur hypergraph. -/
theorem schurContainer_edge_bound
    (I : Finset (Fin n)) (hp : 0 < p) (hp1 : p ≤ 1)
    (hpmax : p ≤ 1 / 72)
    (hI : (schurHypergraph n).IsIndependent I) :
    p ^ 2 * (((schurHypergraph n).restrict
      (schurContainerOutput I hp hpmax hI).container).card : ℝ) ≤
      6 * ((schurContainerOutput I hp hpmax hI).container.card : ℝ) :=
  schurContainer_edge_bound_of_degree I hp hp1 hpmax hI
    (schurHypergraph_degree_le_six n)

end SpecializedEdgeBound

section Canonical

variable {n : ℕ} {p : ℝ}

/-- The deterministic container indexed only by its fingerprint. -/
noncomputable def schurCanonicalContainer (hp : 0 < p) (S : Finset (Fin n)) :
    Finset (Fin n) :=
  Erdos565.SpecialContainerTheorem.canonicalContainer
    (schurHypergraph n) 3 p (by omega) hp S

/-- Canonical representative attached to a putative fingerprint. -/
noncomputable def schurCanonicalRepresentative (hp : 0 < p)
    (S : Finset (Fin n)) : Finset (Fin n) :=
  (ContainerA.algorithmSelector (V := Fin n) p 3 (by omega) hp).representative
    (schurHypergraph n) S

theorem schurCanonicalRepresentative_independent (hp : 0 < p)
    (S : Finset (Fin n)) :
    (schurHypergraph n).IsIndependent (schurCanonicalRepresentative hp S) := by
  exact Erdos565.SpecialContainerTheorem.canonicalRepresentative_independent
    (schurHypergraph n) 3 p (by omega) hp (schurHypergraph_isUniform n) S

/-- Rich container output run on the canonical representative of `S`. -/
noncomputable def schurCanonicalOutput (hp : 0 < p) (hpmax : p ≤ 1 / 72)
    (S : Finset (Fin n)) :
    ContainerA.FiniteContainerOutput (schurHypergraph n)
      (schurCanonicalRepresentative hp S) p 3 :=
  schurContainerOutput (schurCanonicalRepresentative hp S) hp hpmax
    (schurCanonicalRepresentative_independent hp S)

theorem schurCanonicalOutput_container (hp : 0 < p) (hpmax : p ≤ 1 / 72)
    (S : Finset (Fin n)) :
    (schurCanonicalOutput hp hpmax S).container =
      schurCanonicalContainer hp S := by
  let I := schurCanonicalRepresentative hp S
  let hI : (schurHypergraph n).IsIndependent I :=
    schurCanonicalRepresentative_independent hp S
  change (schurContainerOutput I hp hpmax hI).container = _
  calc
    (schurContainerOutput I hp hpmax hI).container =
        (ContainerA.algorithmSelector (V := Fin n) p 3 (by omega) hp).container
          (schurHypergraph n) I := by
      exact ContainerA.Selector.finiteContainer_container_eq_selector_container
        (schurHypergraph n) I p 3 (by omega) hp
        (by norm_num at hpmax ⊢; exact hpmax)
        (schurHypergraph_isUniform n) hI
    _ = schurCanonicalContainer hp S := rfl

/-- Every canonical container obeys the same Schur-edge estimate. -/
theorem schurCanonicalContainer_edge_bound_of_degree
    (hp : 0 < p) (hp1 : p ≤ 1) (hpmax : p ≤ 1 / 72)
    (S : Finset (Fin n))
    (hdegree : ∀ c : Finset (Fin n), 2 ≤ c.card →
      (schurHypergraph n).degree c ≤ 6) :
    p ^ 2 * (((schurHypergraph n).restrict
      (schurCanonicalContainer hp S)).card : ℝ) ≤
      6 * ((schurCanonicalContainer hp S).card : ℝ) := by
  let I := schurCanonicalRepresentative hp S
  let hI : (schurHypergraph n).IsIndependent I :=
    schurCanonicalRepresentative_independent hp S
  have h := schurContainer_edge_bound_of_degree I hp hp1 hpmax hI hdegree
  have hout : (schurContainerOutput I hp hpmax hI).container =
      schurCanonicalContainer hp S := by
    change (schurCanonicalOutput hp hpmax S).container = _
    exact schurCanonicalOutput_container hp hpmax S
  rw [hout] at h
  exact h

/-- Every canonical Schur container has only `O(n)` distinct Schur triples;
the division-free bound is uniform in the fingerprint. -/
theorem schurCanonicalContainer_edge_bound
    (hp : 0 < p) (hp1 : p ≤ 1) (hpmax : p ≤ 1 / 72)
    (S : Finset (Fin n)) :
    p ^ 2 * (((schurHypergraph n).restrict
      (schurCanonicalContainer hp S)).card : ℝ) ≤
      6 * ((schurCanonicalContainer hp S).card : ℝ) :=
  schurCanonicalContainer_edge_bound_of_degree hp hp1 hpmax S
    (schurHypergraph_degree_le_six n)

/-- A sum-free subset of `[1,n]` is covered by a canonical Schur container
whose fingerprint is contained in the input and has size at most `72pn`. -/
theorem exists_schurCanonicalContainer {A : Finset ℕ}
    (hAU : A ⊆ interval n) (hA : SumFree A)
    (hp : 0 < p) (hpmax : p ≤ 1 / 72) :
    ∃ S : Finset (Fin n),
      S ⊆ verticesOf n A ∧
      (S.card : ℝ) ≤ 72 * p * n ∧
      A ⊆ naturalsOf (schurCanonicalContainer hp S) := by
  let I := verticesOf n A
  let hI : (schurHypergraph n).IsIndependent I :=
    sumFree_independent_verticesOf (n := n) hA
  let out := schurContainerOutput I hp hpmax hI
  refine ⟨out.fingerprint, out.fingerprint_subset, ?_, ?_⟩
  · exact schurContainer_fingerprint_card I hp hpmax hI
  · rw [← naturalsOf_verticesOf hAU]
    unfold naturalsOf
    apply Finset.image_mono
    have hout : schurCanonicalContainer hp out.fingerprint = out.container := by
      exact Erdos565.SpecialContainerTheorem.finiteContainer_canonicalContainer
        (schurHypergraph n) 3 p (by omega) hp
        (by norm_num at hpmax ⊢; exact hpmax)
        (schurHypergraph_isUniform n) I hI
    rw [hout]
    exact out.input_subset

end Canonical

end Enumeration
end Erdos877
