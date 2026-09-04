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
import ErdosProblems.Erdos76.AlmostCompleteStrongInduction

/-!
# The large-universal-set case D7

This file formalizes the symmetry and correction machinery in case D7 of
Gruslys--Letzter.  The graph-level residual estimate and the normalized
corrected-average endpoint live in `AlmostCompleteStrongInduction`; here we
construct the symmetric deletion packings and the two explicit corrections.
-/

open Finset
open scoped BigOperators

namespace Erdos76

noncomputable section

attribute [local instance] Classical.propDecidable

variable {A : Type} [Fintype A] [DecidableEq A]

/-! ## Averaging over a universal subset -/

/-- A permutation supported on vertices which are adjacent to every other
vertex is a graph automorphism.  The statement is phrased for an arbitrary
predicate so that it applies directly on a vertex-deleted subtype. -/
lemma map_eq_of_permutes_universalSubset (H : SimpleGraph A) (P : A → Prop)
    (e : Equiv.Perm A)
    (huniversal : ∀ x, P x → ∀ y, x ≠ y → H.Adj x y)
    (hpreserve : ∀ x, P (e x) ↔ P x)
    (hfix : ∀ x, ¬ P x → e x = x) :
    H.map e.toEmbedding = H := by
  rw [← SimpleGraph.comap_symm H e]
  ext x y
  simp only [SimpleGraph.comap_adj]
  change H.Adj (e.symm x) (e.symm y) ↔ H.Adj x y
  by_cases hxy : x = y
  · subst y
    simp
  by_cases hx : P x
  · have hx' : P (e.symm x) := by
      apply (hpreserve (e.symm x)).mp
      simpa
    have hleft : H.Adj (e.symm x) (e.symm y) :=
      huniversal (e.symm x) hx' (e.symm y)
        (fun h ↦ hxy (e.symm.injective h))
    have hright : H.Adj x y := huniversal x hx y hxy
    exact iff_of_true hleft hright
  by_cases hy : P y
  · have hy' : P (e.symm y) := by
      apply (hpreserve (e.symm y)).mp
      simpa
    have hleft : H.Adj (e.symm x) (e.symm y) :=
      (huniversal (e.symm y) hy' (e.symm x)
        (Ne.symm (fun h ↦ hxy (e.symm.injective h)))).symm
    have hright : H.Adj x y := (huniversal y hy x (Ne.symm hxy)).symm
    exact iff_of_true hleft hright
  · have hxsymm : e.symm x = x := by
      apply e.injective
      rw [e.apply_symm_apply, hfix x hx]
    have hysymm : e.symm y = y := by
      apply e.injective
      rw [e.apply_symm_apply, hfix y hy]
    rw [hxsymm, hysymm]

/-- The remaining originally universal vertices after deleting `z`. -/
def d7RemainingUniversalVertices (G : SimpleGraph A) (z : A) : Type :=
  {x : ↑(d7DeletedFinset (A := A) z) //
    (x : A) ∈ universalVertices G}

noncomputable instance d7RemainingUniversalVerticesFintype
    (G : SimpleGraph A) (z : A) :
    Fintype (d7RemainingUniversalVertices G z) :=
  by
    unfold d7RemainingUniversalVertices
    infer_instance

/-- The definitional presentation of the named remaining-universal type as
the corresponding subtype of the deletion graph. -/
def d7RemainingUniversalEquiv (G : SimpleGraph A) (z : A) :
    d7RemainingUniversalVertices G z ≃
      {x : ↑(d7DeletedFinset (A := A) z) //
        (x : A) ∈ universalVertices G} := by
  unfold d7RemainingUniversalVertices
  exact Equiv.refl _

/-- Extend a permutation of the remaining universal vertices by the identity
on every nonuniversal vertex of the deletion graph. -/
def d7ExtendUniversalPerm (G : SimpleGraph A) (z : A)
    (p : Equiv.Perm (d7RemainingUniversalVertices G z)) :
    Equiv.Perm (↑(d7DeletedFinset (A := A) z)) :=
  p.extendDomain (d7RemainingUniversalEquiv G z)

lemma d7ExtendUniversalPerm_preserves (G : SimpleGraph A) (z : A)
    (p : Equiv.Perm (d7RemainingUniversalVertices G z))
    (x : ↑(d7DeletedFinset (A := A) z)) :
    ((d7ExtendUniversalPerm G z p x :
        ↑(d7DeletedFinset (A := A) z)) : A) ∈
        universalVertices G ↔
      (x : A) ∈ universalVertices G := by
  let P : ↑(d7DeletedFinset (A := A) z) → Prop :=
    fun y ↦ (y : A) ∈ universalVertices G
  change P (d7ExtendUniversalPerm G z p x) ↔ P x
  by_cases hx : P x
  · constructor
    · intro _
      exact hx
    · intro _
      change P (d7ExtendUniversalPerm G z p x)
      unfold d7ExtendUniversalPerm
      rw [Equiv.Perm.extendDomain_apply_subtype p
        (d7RemainingUniversalEquiv G z) hx]
      exact (d7RemainingUniversalEquiv G z
        (p ((d7RemainingUniversalEquiv G z).symm ⟨x, hx⟩))).2
  · have hfix := Equiv.Perm.extendDomain_apply_not_subtype p
      (d7RemainingUniversalEquiv G z) hx
    rw [show d7ExtendUniversalPerm G z p x = x by
      simpa only [d7ExtendUniversalPerm] using hfix]

lemma d7ExtendUniversalPerm_fixes_nonuniversal (G : SimpleGraph A) (z : A)
    (p : Equiv.Perm (d7RemainingUniversalVertices G z))
    (x : ↑(d7DeletedFinset (A := A) z))
    (hx : (x : A) ∉ universalVertices G) :
    d7ExtendUniversalPerm G z p x = x := by
  simpa only [d7ExtendUniversalPerm] using
    Equiv.Perm.extendDomain_apply_not_subtype p
      (d7RemainingUniversalEquiv G z) hx

lemma d7DeletedGraph_map_extendUniversalPerm (G : SimpleGraph A) (z : A)
    (p : Equiv.Perm (d7RemainingUniversalVertices G z)) :
    (d7DeletedGraph (A := A) G z).map
        (d7ExtendUniversalPerm G z p).toEmbedding =
      d7DeletedGraph (A := A) G z := by
  apply map_eq_of_permutes_universalSubset
    (d7DeletedGraph (A := A) G z)
    (fun x : ↑(d7DeletedFinset (A := A) z) ↦
      (x : A) ∈ universalVertices G)
    (d7ExtendUniversalPerm G z p)
  · intro x hx y hxy
    change G.Adj (x : A) (y : A)
    have hxzero : Gᶜ.degree (x : A) = 0 := mem_universalVertices.mp hx
    by_contra hnot
    have hcomp : Gᶜ.Adj (x : A) (y : A) := by
      refine ⟨?_, hnot⟩
      intro h
      exact hxy (Subtype.ext h)
    have hpos := hcomp.degree_pos_left
    omega
  · exact d7ExtendUniversalPerm_preserves G z p
  · exact d7ExtendUniversalPerm_fixes_nonuniversal G z p

/-- Fractional size commutes with a finite average of triangle weights. -/
lemma fractionalSize_averageTriangleWeight {I : Type*} [Fintype I]
    (G : SimpleGraph A) (w : I → Finset A → ℝ) :
    fractionalSize G (averageTriangleWeight w) =
      (Fintype.card I : ℝ)⁻¹ * ∑ i, fractionalSize G (w i) := by
  unfold fractionalSize averageTriangleWeight
  rw [← Finset.mul_sum, Finset.sum_comm]

/-- Convexity of the fractional-packing constraints. -/
lemma isFractionalPacking_averageTriangleWeight {I : Type*}
    [Fintype I] [Nonempty I] (G : SimpleGraph A)
    (w : I → Finset A → ℝ)
    (hw : ∀ i, IsFractionalPacking G (w i)) :
    IsFractionalPacking G (averageTriangleWeight w) := by
  constructor
  · exact averageTriangleWeight_nonneg fun i t ht ↦ (hw i).nonneg_on ht
  · intro e he
    rw [fractionalEdgeLoad_average]
    exact average_le_of_forall_le fun i ↦ (hw i).edgeLoad_le_one he

/-- Average a deletion packing over every permutation of its remaining
universal vertices. -/
def d7SymmetrizedWeight (G : SimpleGraph A) (z : A)
    (w : Finset (↑(d7DeletedFinset (A := A) z)) → ℝ) :
    Finset (↑(d7DeletedFinset (A := A) z)) → ℝ :=
  averageTriangleWeight fun
    p : Equiv.Perm (d7RemainingUniversalVertices G z) ↦
      relabelWeight (d7ExtendUniversalPerm G z p) w

lemma d7SymmetrizedWeight_isFractionalPacking (G : SimpleGraph A) (z : A)
    {w : Finset (↑(d7DeletedFinset (A := A) z)) → ℝ}
    (hw : IsFractionalPacking (d7DeletedGraph (A := A) G z) w) :
    IsFractionalPacking (d7DeletedGraph (A := A) G z)
      (d7SymmetrizedWeight G z w) := by
  unfold d7SymmetrizedWeight
  apply isFractionalPacking_averageTriangleWeight
  intro p
  have hp := hw.relabel (d7ExtendUniversalPerm G z p)
  rw [d7DeletedGraph_map_extendUniversalPerm] at hp
  exact hp

lemma d7SymmetrizedWeight_halfBounded (G : SimpleGraph A) (z : A)
    {w : Finset (↑(d7DeletedFinset (A := A) z)) → ℝ}
    (hw : IsHalfBounded (d7DeletedGraph (A := A) G z) w) :
    IsHalfBounded (d7DeletedGraph (A := A) G z)
      (d7SymmetrizedWeight G z w) := by
  unfold d7SymmetrizedWeight
  apply averageTriangleWeight_le_half
  intro p
  have hp := hw.relabel (d7ExtendUniversalPerm G z p)
  rw [d7DeletedGraph_map_extendUniversalPerm] at hp
  exact hp

lemma fractionalSize_d7SymmetrizedWeight (G : SimpleGraph A) (z : A)
    (w : Finset (↑(d7DeletedFinset (A := A) z)) → ℝ) :
    fractionalSize (d7DeletedGraph (A := A) G z)
        (d7SymmetrizedWeight G z w) =
      fractionalSize (d7DeletedGraph (A := A) G z) w := by
  rw [d7SymmetrizedWeight, fractionalSize_averageTriangleWeight]
  have hterm : ∀ p : Equiv.Perm (d7RemainingUniversalVertices G z),
      fractionalSize (d7DeletedGraph G z)
          (relabelWeight (d7ExtendUniversalPerm G z p) w) =
        fractionalSize (d7DeletedGraph G z) w := by
    intro p
    have hp := fractionalSize_relabel (d7DeletedGraph G z)
      (d7ExtendUniversalPerm G z p) w
    rw [d7DeletedGraph_map_extendUniversalPerm] at hp
    exact hp
  simp_rw [hterm]
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  have hcard : (Fintype.card
      (Equiv.Perm (d7RemainingUniversalVertices G z)) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp

lemma fractionalUncoveredWeight_d7SymmetrizedWeight (G : SimpleGraph A)
    (z : A)
    (w : Finset (↑(d7DeletedFinset (A := A) z)) → ℝ) :
    fractionalUncoveredWeight (d7DeletedGraph (A := A) G z)
        (d7SymmetrizedWeight G z w) =
      fractionalUncoveredWeight (d7DeletedGraph (A := A) G z) w := by
  rw [fractionalUncoveredWeight_eq_card_sub_general,
    fractionalUncoveredWeight_eq_card_sub_general,
    fractionalSize_d7SymmetrizedWeight]

/-- Right composition by a fixed permutation is an equivalence of the
finite permutation type. -/
def permTransRight {X : Type*} (q : Equiv.Perm X) :
    Equiv.Perm X ≃ Equiv.Perm X where
  toFun p := p.trans q
  invFun p := p.trans q.symm
  left_inv p := by
    ext x
    simp
  right_inv p := by
    ext x
    simp

/-- The full symmetric group is transitive on ordered pairs of distinct
points.  The explicit two-swap witness avoids importing group-action
machinery for this elementary fact. -/
lemma exists_perm_map_pair {X : Type*} [DecidableEq X]
    {a b c d : X} (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ p : Equiv.Perm X, p a = c ∧ p b = d := by
  let p₁ : Equiv.Perm X := Equiv.swap a c
  let b₁ : X := p₁ b
  let p₂ : Equiv.Perm X := Equiv.swap b₁ d
  have hp₁a : p₁ a = c := by
    exact Equiv.swap_apply_left a c
  have hcb₁ : c ≠ b₁ := by
    intro h
    apply hab
    apply p₁.injective
    rw [hp₁a]
    exact h
  refine ⟨p₁.trans p₂, ?_, ?_⟩
  · rw [Equiv.trans_apply, hp₁a]
    exact Equiv.swap_apply_of_ne_of_ne hcb₁ hcd
  · rw [Equiv.trans_apply]
    exact Equiv.swap_apply_left b₁ d

lemma relabelWeight_trans {X : Type*} [DecidableEq X]
    (e f : Equiv.Perm X) (w : Finset X → ℝ) :
    relabelWeight f (relabelWeight e w) = relabelWeight (e.trans f) w := by
  funext t
  simp [relabelWeight, Finset.map_map]

lemma d7ExtendUniversalPerm_apply_universal (G : SimpleGraph A) (z : A)
    (p : Equiv.Perm (d7RemainingUniversalVertices G z))
    (x : ↑(d7DeletedFinset (A := A) z))
    (hx : (x : A) ∈ universalVertices G) :
    d7ExtendUniversalPerm G z p x =
      (d7RemainingUniversalEquiv G z
        (p ((d7RemainingUniversalEquiv G z).symm ⟨x, hx⟩))).1 := by
  unfold d7ExtendUniversalPerm
  exact Equiv.Perm.extendDomain_apply_subtype p
    (d7RemainingUniversalEquiv G z) hx

/-- Any ordered pair of distinct remaining universal vertices can be sent
to any other such pair by one of the permutations used in the D7 average. -/
lemma exists_d7ExtendUniversalPerm_map_pair (G : SimpleGraph A) (z : A)
    (x₁ x₂ y₁ y₂ : ↑(d7DeletedFinset (A := A) z))
    (hx₁ : (x₁ : A) ∈ universalVertices G)
    (hx₂ : (x₂ : A) ∈ universalVertices G)
    (hy₁ : (y₁ : A) ∈ universalVertices G)
    (hy₂ : (y₂ : A) ∈ universalVertices G)
    (hxx : x₁ ≠ x₂) (hyy : y₁ ≠ y₂) :
    ∃ p : Equiv.Perm (d7RemainingUniversalVertices G z),
      d7ExtendUniversalPerm G z p x₁ = y₁ ∧
        d7ExtendUniversalPerm G z p x₂ = y₂ := by
  let E := d7RemainingUniversalEquiv G z
  let a₁ : d7RemainingUniversalVertices G z := E.symm ⟨x₁, hx₁⟩
  let a₂ : d7RemainingUniversalVertices G z := E.symm ⟨x₂, hx₂⟩
  let b₁ : d7RemainingUniversalVertices G z := E.symm ⟨y₁, hy₁⟩
  let b₂ : d7RemainingUniversalVertices G z := E.symm ⟨y₂, hy₂⟩
  have ha : a₁ ≠ a₂ := by
    intro h
    apply hxx
    have h' := congrArg (fun q ↦ (E q).1) h
    simpa only [a₁, a₂, Equiv.apply_symm_apply] using h'
  have hb : b₁ ≠ b₂ := by
    intro h
    apply hyy
    have h' := congrArg (fun q ↦ (E q).1) h
    simpa only [b₁, b₂, Equiv.apply_symm_apply] using h'
  obtain ⟨p, hp₁, hp₂⟩ := exists_perm_map_pair ha hb
  refine ⟨p, ?_, ?_⟩
  · rw [d7ExtendUniversalPerm_apply_universal G z p x₁ hx₁, hp₁]
    simp only [b₁, E, Equiv.apply_symm_apply]
  · rw [d7ExtendUniversalPerm_apply_universal G z p x₂ hx₂, hp₂]
    simp only [b₂, E, Equiv.apply_symm_apply]

lemma exists_d7ExtendUniversalPerm_apply_eq (G : SimpleGraph A) (z : A)
    (x y : ↑(d7DeletedFinset (A := A) z))
    (hx : (x : A) ∈ universalVertices G)
    (hy : (y : A) ∈ universalVertices G) :
    ∃ p : Equiv.Perm (d7RemainingUniversalVertices G z),
      d7ExtendUniversalPerm G z p x = y := by
  let E := d7RemainingUniversalEquiv G z
  let a : d7RemainingUniversalVertices G z := E.symm ⟨x, hx⟩
  let b : d7RemainingUniversalVertices G z := E.symm ⟨y, hy⟩
  refine ⟨Equiv.swap a b, ?_⟩
  rw [d7ExtendUniversalPerm_apply_universal G z (Equiv.swap a b) x hx]
  change (E (Equiv.swap a b a)).1 = y
  rw [Equiv.swap_apply_left]
  simp only [b, Equiv.apply_symm_apply]

/-- The symmetrized deletion weighting is invariant under every permutation
of the remaining universal vertices. -/
lemma d7SymmetrizedWeight_map_extendUniversalPerm (G : SimpleGraph A) (z : A)
    (w : Finset (↑(d7DeletedFinset (A := A) z)) → ℝ)
    (q : Equiv.Perm (d7RemainingUniversalVertices G z))
    (t : Finset (↑(d7DeletedFinset (A := A) z))) :
    d7SymmetrizedWeight G z w
        (t.map (d7ExtendUniversalPerm G z q).toEmbedding) =
      d7SymmetrizedWeight G z w t := by
  let R := permTransRight q.symm
  let term : Equiv.Perm (d7RemainingUniversalVertices G z) → ℝ :=
    fun p ↦ relabelWeight (d7ExtendUniversalPerm G z p) w t
  have hext (p : Equiv.Perm (d7RemainingUniversalVertices G z)) :
      (d7ExtendUniversalPerm G z p).trans
          (d7ExtendUniversalPerm G z q).symm =
        d7ExtendUniversalPerm G z (p.trans q.symm) := by
    unfold d7ExtendUniversalPerm
    rw [Equiv.Perm.extendDomain_symm, Equiv.Perm.extendDomain_trans]
  have hterm (p : Equiv.Perm (d7RemainingUniversalVertices G z)) :
      relabelWeight (d7ExtendUniversalPerm G z p) w
          (t.map (d7ExtendUniversalPerm G z q).toEmbedding) =
        term (R p) := by
    calc
      relabelWeight (d7ExtendUniversalPerm G z p) w
          (t.map (d7ExtendUniversalPerm G z q).toEmbedding) =
        relabelWeight (d7ExtendUniversalPerm G z q).symm
          (relabelWeight (d7ExtendUniversalPerm G z p) w) t := by
            simp [relabelWeight, Finset.map_map]
      _ = relabelWeight ((d7ExtendUniversalPerm G z p).trans
            (d7ExtendUniversalPerm G z q).symm) w t := by
          rw [relabelWeight_trans]
      _ = term (R p) := by
          rw [hext]
          rfl
  unfold d7SymmetrizedWeight averageTriangleWeight
  congr 1
  calc
    ∑ p : Equiv.Perm (d7RemainingUniversalVertices G z),
        relabelWeight (d7ExtendUniversalPerm G z p) w
          (t.map (d7ExtendUniversalPerm G z q).toEmbedding) =
      ∑ p : Equiv.Perm (d7RemainingUniversalVertices G z), term (R p) := by
        apply Finset.sum_congr rfl
        intro p _
        exact hterm p
    _ = ∑ p : Equiv.Perm (d7RemainingUniversalVertices G z), term p :=
      Equiv.sum_comp R term

lemma d7ExtendUniversalPerm_symm (G : SimpleGraph A) (z : A)
    (p : Equiv.Perm (d7RemainingUniversalVertices G z)) :
    (d7ExtendUniversalPerm G z p).symm =
      d7ExtendUniversalPerm G z p.symm := by
  unfold d7ExtendUniversalPerm
  rw [Equiv.Perm.extendDomain_symm]

/-- Function-level form of the remaining-universal symmetry. -/
lemma relabelWeight_d7SymmetrizedWeight (G : SimpleGraph A) (z : A)
    (w : Finset (↑(d7DeletedFinset (A := A) z)) → ℝ)
    (p : Equiv.Perm (d7RemainingUniversalVertices G z)) :
    relabelWeight (d7ExtendUniversalPerm G z p)
        (d7SymmetrizedWeight G z w) =
      d7SymmetrizedWeight G z w := by
  funext t
  unfold relabelWeight
  rw [d7ExtendUniversalPerm_symm]
  exact d7SymmetrizedWeight_map_extendUniversalPerm G z w p.symm t

/-! ## Normalizing the separated uncovered unit -/

lemma fractionalSize_smulWeight (G : SimpleGraph A) (c : ℝ)
    (w : Finset A → ℝ) :
    fractionalSize G (fun t ↦ c * w t) = c * fractionalSize G w := by
  unfold fractionalSize
  rw [← Finset.mul_sum]

lemma fractionalUncoveredWeight_smulWeight (G : SimpleGraph A) (c : ℝ)
    (w : Finset A → ℝ) :
    fractionalUncoveredWeight G (fun t ↦ c * w t) =
      (1 - c) * (G.edgeFinset.card : ℝ) +
        c * fractionalUncoveredWeight G w := by
  rw [fractionalUncoveredWeight_eq_card_sub_general,
    fractionalUncoveredWeight_eq_card_sub_general,
    Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet,
    fractionalSize_smulWeight]
  ring

lemma IsFractionalPacking.smul_unitInterval {G : SimpleGraph A}
    {w : Finset A → ℝ} (hw : IsFractionalPacking G w)
    {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    IsFractionalPacking G (fun t ↦ c * w t) := by
  constructor
  · intro t ht
    exact mul_nonneg hc0 (hw.nonneg_on ht)
  · intro e he
    rw [fractionalEdgeLoad_smul]
    calc
      c * fractionalEdgeLoad G w e ≤ c * 1 :=
        mul_le_mul_of_nonneg_left (hw.edgeLoad_le_one he) hc0
      _ ≤ 1 := by simpa only [mul_one] using hc1

lemma IsHalfBounded.smul_unitInterval {G : SimpleGraph A}
    {w : Finset A → ℝ} (hw : IsHalfBounded G w)
    {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    IsHalfBounded G (fun t ↦ c * w t) := by
  intro t ht
  calc
    c * w t ≤ c * (1 / 2) := mul_le_mul_of_nonneg_left (hw t ht) hc0
    _ ≤ 1 * (1 / 2) := mul_le_mul_of_nonneg_right hc1 (by norm_num)
    _ = 1 / 2 := by ring

/-- Scale a packing down exactly enough to raise its uncovered weight to
one, leaving it unchanged when it already has uncovered weight at least one.
This makes the paper's separated unit rigorous even when induction produces
a packing strictly better than its stated upper bound. -/
def normalizeUncoveredOne (G : SimpleGraph A) (w : Finset A → ℝ) :
    Finset A → ℝ :=
  let r := fractionalUncoveredWeight G w
  let E := (G.edgeFinset.card : ℝ)
  if r < 1 then
    fun t ↦ ((E - 1) / (E - r)) * w t
  else w

private lemma normalizeUncoveredOne_factor_mem_Icc (G : SimpleGraph A)
    {w : Finset A → ℝ} (hw : IsFractionalPacking G w)
    (hE : 1 ≤ G.edgeFinset.card) :
    let r := fractionalUncoveredWeight G w
    let E := (G.edgeFinset.card : ℝ)
    if r < 1 then ((E - 1) / (E - r)) ∈ Set.Icc (0 : ℝ) 1
    else (1 : ℝ) ∈ Set.Icc 0 1 := by
  let r := fractionalUncoveredWeight G w
  let E := (G.edgeFinset.card : ℝ)
  have hr0 : 0 ≤ r := by
    exact fractionalUncoveredWeight_nonneg hw
  have hE1 : (1 : ℝ) ≤ E := by
    dsimp only [E]
    exact_mod_cast hE
  by_cases hr : r < 1
  · rw [if_pos hr]
    have hden : 0 < E - r := by linarith
    constructor
    · exact div_nonneg (sub_nonneg.mpr hE1) hden.le
    · apply (div_le_one hden).mpr
      linarith
  · rw [if_neg hr]
    exact ⟨by norm_num, by norm_num⟩

lemma normalizeUncoveredOne_isFractionalPacking (G : SimpleGraph A)
    {w : Finset A → ℝ} (hw : IsFractionalPacking G w)
    (hE : 1 ≤ G.edgeFinset.card) :
    IsFractionalPacking G (normalizeUncoveredOne G w) := by
  let r := fractionalUncoveredWeight G w
  let E := (G.edgeFinset.card : ℝ)
  have hfactor := normalizeUncoveredOne_factor_mem_Icc G hw hE
  dsimp only [r, E] at hfactor
  unfold normalizeUncoveredOne
  by_cases hr : fractionalUncoveredWeight G w < 1
  · rw [if_pos hr]
    have hf : (((G.edgeFinset.card : ℝ) - 1) /
        ((G.edgeFinset.card : ℝ) - fractionalUncoveredWeight G w)) ∈
          Set.Icc (0 : ℝ) 1 := by
      simpa [hr] using hfactor
    exact hw.smul_unitInterval hf.1 hf.2
  · rw [if_neg hr]
    exact hw

lemma normalizeUncoveredOne_halfBounded (G : SimpleGraph A)
    {w : Finset A → ℝ} (hpacking : IsFractionalPacking G w)
    (hw : IsHalfBounded G w) (hE : 1 ≤ G.edgeFinset.card) :
    IsHalfBounded G (normalizeUncoveredOne G w) := by
  let r := fractionalUncoveredWeight G w
  let E := (G.edgeFinset.card : ℝ)
  have hfactor := normalizeUncoveredOne_factor_mem_Icc G hpacking hE
  dsimp only [r, E] at hfactor
  unfold normalizeUncoveredOne
  by_cases hr : fractionalUncoveredWeight G w < 1
  · rw [if_pos hr]
    have hf : (((G.edgeFinset.card : ℝ) - 1) /
        ((G.edgeFinset.card : ℝ) - fractionalUncoveredWeight G w)) ∈
          Set.Icc (0 : ℝ) 1 := by
      simpa [hr] using hfactor
    exact hw.smul_unitInterval hf.1 hf.2
  · rw [if_neg hr]
    exact hw

lemma fractionalUncoveredWeight_normalizeUncoveredOne (G : SimpleGraph A)
    {w : Finset A → ℝ} (hw : IsFractionalPacking G w)
    (hE : 1 ≤ G.edgeFinset.card) :
    fractionalUncoveredWeight G (normalizeUncoveredOne G w) =
      max 1 (fractionalUncoveredWeight G w) := by
  let r := fractionalUncoveredWeight G w
  let E := (G.edgeFinset.card : ℝ)
  have hr0 : 0 ≤ r := fractionalUncoveredWeight_nonneg hw
  have hE1 : (1 : ℝ) ≤ E := by
    dsimp only [E]
    exact_mod_cast hE
  unfold normalizeUncoveredOne
  by_cases hr : r < 1
  · rw [if_pos hr, fractionalUncoveredWeight_smulWeight, max_eq_left hr.le]
    have hden : E - r ≠ 0 := by linarith
    change (1 - (E - 1) / (E - r)) * E +
      ((E - 1) / (E - r)) * r = 1
    field_simp [hden]
    ring
  · rw [if_neg hr, max_eq_right (le_of_not_gt hr)]

lemma fractionalUncoveredWeight_normalizeUncoveredOne_mem_Icc
    (G : SimpleGraph A) {w : Finset A → ℝ}
    (hw : IsFractionalPacking G w) (hE : 1 ≤ G.edgeFinset.card)
    {b : ℝ} (hb : fractionalUncoveredWeight G w ≤ b) (h1b : 1 ≤ b) :
    fractionalUncoveredWeight G (normalizeUncoveredOne G w) ∈
      Set.Icc (1 : ℝ) b := by
  rw [fractionalUncoveredWeight_normalizeUncoveredOne G hw hE]
  exact ⟨le_max_left _ _, max_le h1b hb⟩

lemma relabelWeight_normalizeUncoveredOne_of_invariant
    (G : SimpleGraph A) (e : Equiv.Perm A) (w : Finset A → ℝ)
    (hw : relabelWeight e w = w) :
    relabelWeight e (normalizeUncoveredOne G w) =
      normalizeUncoveredOne G w := by
  unfold normalizeUncoveredOne
  by_cases hr : fractionalUncoveredWeight G w < 1
  · rw [if_pos hr]
    funext t
    change ((G.edgeFinset.card : ℝ) - 1) /
          ((G.edgeFinset.card : ℝ) - fractionalUncoveredWeight G w) *
          w (t.map e.symm.toEmbedding) =
        ((G.edgeFinset.card : ℝ) - 1) /
          ((G.edgeFinset.card : ℝ) - fractionalUncoveredWeight G w) * w t
    have ht := congrFun hw t
    change w (t.map e.symm.toEmbedding) = w t at ht
    rw [ht]
  · rw [if_neg hr]
    exact hw

/-- Symmetrize a deletion packing and then normalize its uncovered weight
to be at least one.  This is the canonical deletion weighting used in D7. -/
def d7CanonicalDeletedWeight (G : SimpleGraph A) (z : A)
    (w : Finset (↑(d7DeletedFinset (A := A) z)) → ℝ) :
    Finset (↑(d7DeletedFinset (A := A) z)) → ℝ :=
  normalizeUncoveredOne (d7DeletedGraph G z) (d7SymmetrizedWeight G z w)

lemma relabelWeight_d7CanonicalDeletedWeight (G : SimpleGraph A) (z : A)
    (w : Finset (↑(d7DeletedFinset (A := A) z)) → ℝ)
    (p : Equiv.Perm (d7RemainingUniversalVertices G z)) :
    relabelWeight (d7ExtendUniversalPerm G z p)
        (d7CanonicalDeletedWeight G z w) =
      d7CanonicalDeletedWeight G z w := by
  apply relabelWeight_normalizeUncoveredOne_of_invariant
  exact relabelWeight_d7SymmetrizedWeight G z w p

lemma d7CanonicalDeletedWeight_isFractionalPacking (G : SimpleGraph A)
    (z : A) {w : Finset (↑(d7DeletedFinset (A := A) z)) → ℝ}
    (hw : IsFractionalPacking (d7DeletedGraph G z) w)
    (hE : 1 ≤ (d7DeletedGraph G z).edgeFinset.card) :
    IsFractionalPacking (d7DeletedGraph G z)
      (d7CanonicalDeletedWeight G z w) := by
  exact normalizeUncoveredOne_isFractionalPacking _
    (d7SymmetrizedWeight_isFractionalPacking G z hw) hE

lemma d7CanonicalDeletedWeight_halfBounded (G : SimpleGraph A) (z : A)
    {w : Finset (↑(d7DeletedFinset (A := A) z)) → ℝ}
    (hpacking : IsFractionalPacking (d7DeletedGraph G z) w)
    (hw : IsHalfBounded (d7DeletedGraph G z) w)
    (hE : 1 ≤ (d7DeletedGraph G z).edgeFinset.card) :
    IsHalfBounded (d7DeletedGraph G z)
      (d7CanonicalDeletedWeight G z w) := by
  exact normalizeUncoveredOne_halfBounded _
    (d7SymmetrizedWeight_isFractionalPacking G z hpacking)
    (d7SymmetrizedWeight_halfBounded G z hw) hE

lemma fractionalUncoveredWeight_d7CanonicalDeletedWeight_mem_Icc
    (G : SimpleGraph A) (z : A)
    {w : Finset (↑(d7DeletedFinset (A := A) z)) → ℝ}
    (hw : IsFractionalPacking (d7DeletedGraph G z) w)
    (hE : 1 ≤ (d7DeletedGraph G z).edgeFinset.card)
    {b : ℝ} (hb : fractionalUncoveredWeight (d7DeletedGraph G z) w ≤ b)
    (h1b : 1 ≤ b) :
    fractionalUncoveredWeight (d7DeletedGraph G z)
        (d7CanonicalDeletedWeight G z w) ∈ Set.Icc (1 : ℝ) b := by
  apply fractionalUncoveredWeight_normalizeUncoveredOne_mem_Icc
    (d7DeletedGraph G z)
    (d7SymmetrizedWeight_isFractionalPacking G z hw) hE
  · rwa [fractionalUncoveredWeight_d7SymmetrizedWeight]
  · exact h1b

/-! ## Separating one unit of uncovered edge weight -/

/-- Pointwise uncovered capacity, extended by zero to nonedges. -/
def d7ResidualEdgeWeight (G : SimpleGraph A) (w : Finset A → ℝ) :
    Sym2 A → ℝ :=
  fun e ↦ if e ∈ G.edgeFinset then 1 - fractionalEdgeLoad G w e else 0

/-- The canonical separated unit: normalize the uncovered edge vector by
its total weight. -/
def d7SeparatedUnit (G : SimpleGraph A) (w : Finset A → ℝ) :
    Sym2 A → ℝ :=
  fun e ↦ (fractionalUncoveredWeight G w)⁻¹ * d7ResidualEdgeWeight G w e

/-- The uncovered edge vector left after removing the canonical unit. -/
def d7RemainingResidual (G : SimpleGraph A) (w : Finset A → ℝ) :
    Sym2 A → ℝ :=
  fun e ↦ d7ResidualEdgeWeight G w e - d7SeparatedUnit G w e

lemma d7ResidualEdgeWeight_relabel {B : Type} [Fintype B]
    [DecidableEq B] (G : SimpleGraph A) (e : A ≃ B)
    (w : Finset A → ℝ) (p : Sym2 A) :
    d7ResidualEdgeWeight (G.map e.toEmbedding) (relabelWeight e w)
        (e.toEmbedding.sym2Map p) =
      d7ResidualEdgeWeight G w p := by
  classical
  let : DecidableRel G.Adj := Classical.decRel _
  let : DecidableRel (G.map e.toEmbedding).Adj := Classical.decRel _
  unfold d7ResidualEdgeWeight
  have hmem : e.toEmbedding.sym2Map p ∈
        (G.map e.toEmbedding).edgeFinset ↔ p ∈ G.edgeFinset := by
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeFinset,
      SimpleGraph.edgeSet_map]
    constructor
    · rintro ⟨q, hq, hqp⟩
      have : q = p := e.toEmbedding.sym2Map.injective hqp
      simpa only [this] using hq
    · intro hp
      exact ⟨p, hp, rfl⟩
  rw [if_congr hmem rfl rfl, fractionalEdgeLoad_relabel]

lemma d7SeparatedUnit_relabel {B : Type} [Fintype B] [DecidableEq B]
    (G : SimpleGraph A) (e : A ≃ B) (w : Finset A → ℝ) (p : Sym2 A) :
    d7SeparatedUnit (G.map e.toEmbedding) (relabelWeight e w)
        (e.toEmbedding.sym2Map p) =
      d7SeparatedUnit G w p := by
  unfold d7SeparatedUnit
  rw [fractionalUncoveredWeight_relabel_general,
    d7ResidualEdgeWeight_relabel]

lemma d7RemainingResidual_relabel {B : Type} [Fintype B]
    [DecidableEq B] (G : SimpleGraph A) (e : A ≃ B)
    (w : Finset A → ℝ) (p : Sym2 A) :
    d7RemainingResidual (G.map e.toEmbedding) (relabelWeight e w)
        (e.toEmbedding.sym2Map p) =
      d7RemainingResidual G w p := by
  unfold d7RemainingResidual
  rw [d7ResidualEdgeWeight_relabel, d7SeparatedUnit_relabel]

lemma d7SeparatedUnit_map_extendUniversalPerm_of_invariant
    (G : SimpleGraph A) (z : A)
    (w : Finset (↑(d7DeletedFinset (A := A) z)) → ℝ)
    (p : Equiv.Perm (d7RemainingUniversalVertices G z))
    (hw : relabelWeight (d7ExtendUniversalPerm G z p) w = w)
    (e : Sym2 (↑(d7DeletedFinset (A := A) z))) :
    d7SeparatedUnit (d7DeletedGraph G z) w
        ((d7ExtendUniversalPerm G z p).toEmbedding.sym2Map e) =
      d7SeparatedUnit (d7DeletedGraph G z) w e := by
  have h := d7SeparatedUnit_relabel (d7DeletedGraph G z)
    (d7ExtendUniversalPerm G z p) w e
  rw [d7DeletedGraph_map_extendUniversalPerm, hw] at h
  exact h

lemma d7SeparatedUnit_canonical_map_extendUniversalPerm
    (G : SimpleGraph A) (z : A)
    (w : Finset (↑(d7DeletedFinset (A := A) z)) → ℝ)
    (p : Equiv.Perm (d7RemainingUniversalVertices G z))
    (e : Sym2 (↑(d7DeletedFinset (A := A) z))) :
    d7SeparatedUnit (d7DeletedGraph G z) (d7CanonicalDeletedWeight G z w)
        ((d7ExtendUniversalPerm G z p).toEmbedding.sym2Map e) =
      d7SeparatedUnit (d7DeletedGraph G z) (d7CanonicalDeletedWeight G z w)
        e := by
  have h := d7SeparatedUnit_relabel (d7DeletedGraph G z)
    (d7ExtendUniversalPerm G z p) (d7CanonicalDeletedWeight G z w) e
  rw [d7DeletedGraph_map_extendUniversalPerm,
    relabelWeight_d7CanonicalDeletedWeight] at h
  exact h

lemma d7RemainingResidual_canonical_map_extendUniversalPerm
    (G : SimpleGraph A) (z : A)
    (w : Finset (↑(d7DeletedFinset (A := A) z)) → ℝ)
    (p : Equiv.Perm (d7RemainingUniversalVertices G z))
    (e : Sym2 (↑(d7DeletedFinset (A := A) z))) :
    d7RemainingResidual (d7DeletedGraph G z) (d7CanonicalDeletedWeight G z w)
        ((d7ExtendUniversalPerm G z p).toEmbedding.sym2Map e) =
      d7RemainingResidual (d7DeletedGraph G z) (d7CanonicalDeletedWeight G z w)
        e := by
  have h := d7RemainingResidual_relabel (d7DeletedGraph G z)
    (d7ExtendUniversalPerm G z p) (d7CanonicalDeletedWeight G z w) e
  rw [d7DeletedGraph_map_extendUniversalPerm,
    relabelWeight_d7CanonicalDeletedWeight] at h
  exact h

/-- The separated uncovered unit has one common value on all edges between
two distinct remaining universal vertices. -/
lemma d7SeparatedUnit_canonical_universal_pair_eq
    (G : SimpleGraph A) (z : A)
    (w : Finset (↑(d7DeletedFinset (A := A) z)) → ℝ)
    (x₁ x₂ y₁ y₂ : ↑(d7DeletedFinset (A := A) z))
    (hx₁ : (x₁ : A) ∈ universalVertices G)
    (hx₂ : (x₂ : A) ∈ universalVertices G)
    (hy₁ : (y₁ : A) ∈ universalVertices G)
    (hy₂ : (y₂ : A) ∈ universalVertices G)
    (hxx : x₁ ≠ x₂) (hyy : y₁ ≠ y₂) :
    d7SeparatedUnit (d7DeletedGraph G z) (d7CanonicalDeletedWeight G z w)
        s(x₁, x₂) =
      d7SeparatedUnit (d7DeletedGraph G z) (d7CanonicalDeletedWeight G z w)
        s(y₁, y₂) := by
  obtain ⟨p, hp₁, hp₂⟩ := exists_d7ExtendUniversalPerm_map_pair G z
    x₁ x₂ y₁ y₂ hx₁ hx₂ hy₁ hy₂ hxx hyy
  have hmap : (d7ExtendUniversalPerm G z p).toEmbedding.sym2Map s(x₁, x₂) =
      s(y₁, y₂) := by
    change Sym2.map (d7ExtendUniversalPerm G z p) s(x₁, x₂) = s(y₁, y₂)
    rw [Sym2.map_mk, hp₁, hp₂]
  have h := d7SeparatedUnit_canonical_map_extendUniversalPerm G z w p
    s(x₁, x₂)
  rw [hmap] at h
  exact h.symm

/-- For a fixed nonuniversal vertex, the separated-unit value of its edge
to a remaining universal vertex is independent of the universal endpoint. -/
lemma d7SeparatedUnit_canonical_mixed_eq
    (G : SimpleGraph A) (z : A)
    (w : Finset (↑(d7DeletedFinset (A := A) z)) → ℝ)
    (u x y : ↑(d7DeletedFinset (A := A) z))
    (hu : (u : A) ∉ universalVertices G)
    (hx : (x : A) ∈ universalVertices G)
    (hy : (y : A) ∈ universalVertices G) :
    d7SeparatedUnit (d7DeletedGraph G z) (d7CanonicalDeletedWeight G z w)
        s(u, x) =
      d7SeparatedUnit (d7DeletedGraph G z) (d7CanonicalDeletedWeight G z w)
        s(u, y) := by
  obtain ⟨p, hp⟩ := exists_d7ExtendUniversalPerm_apply_eq G z x y hx hy
  have hfix := d7ExtendUniversalPerm_fixes_nonuniversal G z p u hu
  have hmap : (d7ExtendUniversalPerm G z p).toEmbedding.sym2Map s(u, x) =
      s(u, y) := by
    change Sym2.map (d7ExtendUniversalPerm G z p) s(u, x) = s(u, y)
    rw [Sym2.map_mk, hfix, hp]
  have h := d7SeparatedUnit_canonical_map_extendUniversalPerm G z w p s(u, x)
  rw [hmap] at h
  exact h.symm

lemma d7SeparatedUnit_universal_pair_eq_of_invariant
    (G : SimpleGraph A) (z : A)
    (w : Finset (↑(d7DeletedFinset (A := A) z)) → ℝ)
    (hw : ∀ p : Equiv.Perm (d7RemainingUniversalVertices G z),
      relabelWeight (d7ExtendUniversalPerm G z p) w = w)
    (x₁ x₂ y₁ y₂ : ↑(d7DeletedFinset (A := A) z))
    (hx₁ : (x₁ : A) ∈ universalVertices G)
    (hx₂ : (x₂ : A) ∈ universalVertices G)
    (hy₁ : (y₁ : A) ∈ universalVertices G)
    (hy₂ : (y₂ : A) ∈ universalVertices G)
    (hxx : x₁ ≠ x₂) (hyy : y₁ ≠ y₂) :
    d7SeparatedUnit (d7DeletedGraph G z) w s(x₁, x₂) =
      d7SeparatedUnit (d7DeletedGraph G z) w s(y₁, y₂) := by
  obtain ⟨p, hp₁, hp₂⟩ := exists_d7ExtendUniversalPerm_map_pair G z
    x₁ x₂ y₁ y₂ hx₁ hx₂ hy₁ hy₂ hxx hyy
  have hmap : (d7ExtendUniversalPerm G z p).toEmbedding.sym2Map s(x₁, x₂) =
      s(y₁, y₂) := by
    change Sym2.map (d7ExtendUniversalPerm G z p) s(x₁, x₂) = s(y₁, y₂)
    rw [Sym2.map_mk, hp₁, hp₂]
  have h := d7SeparatedUnit_map_extendUniversalPerm_of_invariant
    G z w p (hw p) s(x₁, x₂)
  rw [hmap] at h
  exact h.symm

lemma d7SeparatedUnit_mixed_eq_of_invariant
    (G : SimpleGraph A) (z : A)
    (w : Finset (↑(d7DeletedFinset (A := A) z)) → ℝ)
    (hw : ∀ p : Equiv.Perm (d7RemainingUniversalVertices G z),
      relabelWeight (d7ExtendUniversalPerm G z p) w = w)
    (u x y : ↑(d7DeletedFinset (A := A) z))
    (hu : (u : A) ∉ universalVertices G)
    (hx : (x : A) ∈ universalVertices G)
    (hy : (y : A) ∈ universalVertices G) :
    d7SeparatedUnit (d7DeletedGraph G z) w s(u, x) =
      d7SeparatedUnit (d7DeletedGraph G z) w s(u, y) := by
  obtain ⟨p, hp⟩ := exists_d7ExtendUniversalPerm_apply_eq G z x y hx hy
  have hfix := d7ExtendUniversalPerm_fixes_nonuniversal G z p u hu
  have hmap : (d7ExtendUniversalPerm G z p).toEmbedding.sym2Map s(u, x) =
      s(u, y) := by
    change Sym2.map (d7ExtendUniversalPerm G z p) s(u, x) = s(u, y)
    rw [Sym2.map_mk, hfix, hp]
  have h := d7SeparatedUnit_map_extendUniversalPerm_of_invariant
    G z w p (hw p) s(u, x)
  rw [hmap] at h
  exact h.symm

/-! ## Transport between two universal-vertex deletions -/

/-- Swapping `z` and `y` identifies the vertex sets obtained by deleting
`z` and by deleting `y`. -/
def d7DeletedSwapEquiv (z y : A) :
    ↑(d7DeletedFinset (A := A) z) ≃ ↑(d7DeletedFinset (A := A) y) :=
  (Equiv.swap z y).subtypeEquiv fun x ↦ by
    simp only [d7DeletedFinset, Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · intro hx hswap
      have : x = z := by
        have h := congrArg (Equiv.swap z y) hswap
        simpa only [Equiv.swap_apply_self, Equiv.swap_apply_right] using h
      exact hx this
    · intro hx hxz
      apply hx
      subst x
      exact Equiv.swap_apply_left z y

@[simp] lemma d7DeletedSwapEquiv_apply_val (z y : A)
    (x : ↑(d7DeletedFinset (A := A) z)) :
    ((d7DeletedSwapEquiv z y x : ↑(d7DeletedFinset (A := A) y)) : A) =
      Equiv.swap z y (x : A) := rfl

@[simp] lemma d7DeletedSwapEquiv_symm_apply_val (z y : A)
    (x : ↑(d7DeletedFinset (A := A) y)) :
    (((d7DeletedSwapEquiv z y).symm x :
        ↑(d7DeletedFinset (A := A) z)) : A) =
      Equiv.swap z y (x : A) := by
  rfl

lemma map_swap_universalVertices_eq (G : SimpleGraph A) {z y : A}
    (hz : z ∈ universalVertices G) (hy : y ∈ universalVertices G) :
    G.map (Equiv.swap z y).toEmbedding = G := by
  apply map_eq_of_permutes_universalSubset G
    (fun x ↦ x ∈ universalVertices G) (Equiv.swap z y)
  · intro x hx v hxv
    have hxzero : Gᶜ.degree x = 0 := mem_universalVertices.mp hx
    by_contra hnot
    have hcomp : Gᶜ.Adj x v := ⟨hxv, hnot⟩
    have hpos := hcomp.degree_pos_left
    rw [hxzero] at hpos
    omega
  · intro x
    by_cases hxz : x = z
    · subst x
      rw [Equiv.swap_apply_left]
      exact iff_of_true hy hz
    by_cases hxy : x = y
    · subst x
      rw [Equiv.swap_apply_right]
      exact iff_of_true hz hy
    rw [Equiv.swap_apply_of_ne_of_ne hxz hxy]
  · intro x hx
    apply Equiv.swap_apply_of_ne_of_ne
    · intro h
      subst x
      exact hx hz
    · intro h
      subst x
      exact hx hy

lemma d7DeletedGraph_map_d7DeletedSwapEquiv (G : SimpleGraph A) {z y : A}
    (hz : z ∈ universalVertices G) (hy : y ∈ universalVertices G) :
    (d7DeletedGraph G z).map (d7DeletedSwapEquiv z y).toEmbedding =
      d7DeletedGraph G y := by
  rw [← SimpleGraph.comap_symm (d7DeletedGraph G z)
    (d7DeletedSwapEquiv z y)]
  ext x v
  change G.Adj (Equiv.swap z y (x : A)) (Equiv.swap z y (v : A)) ↔
    G.Adj (x : A) (v : A)
  have hmap := map_swap_universalVertices_eq G hz hy
  rw [← SimpleGraph.comap_symm G (Equiv.swap z y)] at hmap
  have hadj := congrFun (congrFun (SimpleGraph.ext_iff.mp hmap) (x : A)) (v : A)
  change G.Adj (Equiv.swap z y (x : A)) (Equiv.swap z y (v : A)) =
    G.Adj (x : A) (v : A) at hadj
  rw [hadj]

/-- Transport a weighting from the deletion of `z` to the deletion of `y`. -/
def d7TransportDeletedWeight (z y : A)
    (w : Finset (↑(d7DeletedFinset (A := A) z)) → ℝ) :
    Finset (↑(d7DeletedFinset (A := A) y)) → ℝ :=
  relabelWeight (d7DeletedSwapEquiv z y) w

lemma d7TransportDeletedWeight_isFractionalPacking (G : SimpleGraph A)
    {z y : A} (hz : z ∈ universalVertices G) (hy : y ∈ universalVertices G)
    {w : Finset (↑(d7DeletedFinset (A := A) z)) → ℝ}
    (hw : IsFractionalPacking (d7DeletedGraph G z) w) :
    IsFractionalPacking (d7DeletedGraph G y)
      (d7TransportDeletedWeight z y w) := by
  have h := hw.relabel (d7DeletedSwapEquiv z y)
  rwa [d7DeletedGraph_map_d7DeletedSwapEquiv G hz hy] at h

lemma d7TransportDeletedWeight_halfBounded (G : SimpleGraph A)
    {z y : A} (hz : z ∈ universalVertices G) (hy : y ∈ universalVertices G)
    {w : Finset (↑(d7DeletedFinset (A := A) z)) → ℝ}
    (hw : IsHalfBounded (d7DeletedGraph G z) w) :
    IsHalfBounded (d7DeletedGraph G y)
      (d7TransportDeletedWeight z y w) := by
  have h := hw.relabel (d7DeletedSwapEquiv z y)
  rwa [d7DeletedGraph_map_d7DeletedSwapEquiv G hz hy] at h

lemma fractionalUncoveredWeight_d7TransportDeletedWeight (G : SimpleGraph A)
    {z y : A} (hz : z ∈ universalVertices G) (hy : y ∈ universalVertices G)
    (w : Finset (↑(d7DeletedFinset (A := A) z)) → ℝ) :
    fractionalUncoveredWeight (d7DeletedGraph G y)
        (d7TransportDeletedWeight z y w) =
      fractionalUncoveredWeight (d7DeletedGraph G z) w := by
  have h := fractionalUncoveredWeight_relabel_general
    (d7DeletedGraph G z) (d7DeletedSwapEquiv z y) w
  rwa [d7DeletedGraph_map_d7DeletedSwapEquiv G hz hy] at h

lemma d7SeparatedUnit_d7TransportDeletedWeight (G : SimpleGraph A)
    {z y : A} (hz : z ∈ universalVertices G) (hy : y ∈ universalVertices G)
    (w : Finset (↑(d7DeletedFinset (A := A) z)) → ℝ)
    (e : Sym2 (↑(d7DeletedFinset (A := A) z))) :
    d7SeparatedUnit (d7DeletedGraph G y) (d7TransportDeletedWeight z y w)
        ((d7DeletedSwapEquiv z y).toEmbedding.sym2Map e) =
      d7SeparatedUnit (d7DeletedGraph G z) w e := by
  have h := d7SeparatedUnit_relabel (d7DeletedGraph G z)
    (d7DeletedSwapEquiv z y) w e
  rwa [d7DeletedGraph_map_d7DeletedSwapEquiv G hz hy] at h

/-- An ambient vertex different from `z`, regarded as a vertex of `G-z`. -/
def d7DeletedVertex (z x : A) (hx : x ≠ z) :
    ↑(d7DeletedFinset (A := A) z) :=
  ⟨x, by simp [d7DeletedFinset, hx]⟩

@[simp] lemma d7DeletedVertex_val (z x : A) (hx : x ≠ z) :
    (d7DeletedVertex z x hx : A) = x := rfl

/-- Starting from one canonical deletion weighting, transport it coherently
to every other deleted universal vertex. -/
def d7CoherentUniversalDeletedWeight (G : SimpleGraph A)
    (z₀ : ↑(universalVertices G))
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (z : ↑(universalVertices G)) :
    Finset (↑(d7DeletedFinset (A := A) (z : A))) → ℝ :=
  d7TransportDeletedWeight (z₀ : A) (z : A) w₀

lemma d7CoherentUniversalDeletedWeight_isFractionalPacking
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G))
    {w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ}
    (hw₀ : IsFractionalPacking (d7DeletedGraph G (z₀ : A)) w₀)
    (z : ↑(universalVertices G)) :
    IsFractionalPacking (d7DeletedGraph G (z : A))
      (d7CoherentUniversalDeletedWeight G z₀ w₀ z) := by
  exact d7TransportDeletedWeight_isFractionalPacking G z₀.property z.property hw₀

lemma d7CoherentUniversalDeletedWeight_halfBounded
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G))
    {w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ}
    (hw₀ : IsHalfBounded (d7DeletedGraph G (z₀ : A)) w₀)
    (z : ↑(universalVertices G)) :
    IsHalfBounded (d7DeletedGraph G (z : A))
      (d7CoherentUniversalDeletedWeight G z₀ w₀ z) := by
  exact d7TransportDeletedWeight_halfBounded G z₀.property z.property hw₀

lemma fractionalUncoveredWeight_d7CoherentUniversalDeletedWeight
    (G : SimpleGraph A) (z₀ : ↑(universalVertices G))
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (z : ↑(universalVertices G)) :
    fractionalUncoveredWeight (d7DeletedGraph G (z : A))
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z) =
      fractionalUncoveredWeight (d7DeletedGraph G (z₀ : A)) w₀ := by
  exact fractionalUncoveredWeight_d7TransportDeletedWeight G
    z₀.property z.property w₀

/-- Coherence on every ambient edge which survives both deletions. -/
lemma d7SeparatedUnit_coherent_eq (G : SimpleGraph A)
    (z₀ z : ↑(universalVertices G))
    (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ)
    (x y : A)
    (hx₀ : x ≠ (z₀ : A)) (hx : x ≠ (z : A))
    (hy₀ : y ≠ (z₀ : A)) (hy : y ≠ (z : A)) :
    d7SeparatedUnit (d7DeletedGraph G (z : A))
        (d7CoherentUniversalDeletedWeight G z₀ w₀ z)
        s(d7DeletedVertex (z : A) x hx, d7DeletedVertex (z : A) y hy) =
      d7SeparatedUnit (d7DeletedGraph G (z₀ : A)) w₀
        s(d7DeletedVertex (z₀ : A) x hx₀,
          d7DeletedVertex (z₀ : A) y hy₀) := by
  have hmap : (d7DeletedSwapEquiv (z₀ : A) (z : A)).toEmbedding.sym2Map
        s(d7DeletedVertex (z₀ : A) x hx₀,
          d7DeletedVertex (z₀ : A) y hy₀) =
      s(d7DeletedVertex (z : A) x hx, d7DeletedVertex (z : A) y hy) := by
    change Sym2.map (d7DeletedSwapEquiv (z₀ : A) (z : A))
        s(d7DeletedVertex (z₀ : A) x hx₀,
          d7DeletedVertex (z₀ : A) y hy₀) = _
    rw [Sym2.map_mk]
    congr 1
    · apply Subtype.ext
      simp only [d7DeletedSwapEquiv_apply_val, d7DeletedVertex_val]
      rw [Equiv.swap_apply_of_ne_of_ne hx₀ hx]
    · apply Subtype.ext
      simp only [d7DeletedSwapEquiv_apply_val, d7DeletedVertex_val]
      rw [Equiv.swap_apply_of_ne_of_ne hy₀ hy]
  have h := d7SeparatedUnit_d7TransportDeletedWeight G
    z₀.property z.property w₀
      s(d7DeletedVertex (z₀ : A) x hx₀,
        d7DeletedVertex (z₀ : A) y hy₀)
  rw [hmap] at h
  exact h

lemma d7ResidualEdgeWeight_nonneg {G : SimpleGraph A} {w : Finset A → ℝ}
    (hw : IsFractionalPacking G w) (e : Sym2 A) :
    0 ≤ d7ResidualEdgeWeight G w e := by
  unfold d7ResidualEdgeWeight
  split_ifs with he
  · exact sub_nonneg.mpr (hw.edgeLoad_le_one he)
  · exact le_rfl

lemma sum_d7ResidualEdgeWeight (G : SimpleGraph A) (w : Finset A → ℝ) :
    ∑ e ∈ G.edgeFinset, d7ResidualEdgeWeight G w e =
      fractionalUncoveredWeight G w := by
  unfold fractionalUncoveredWeight d7ResidualEdgeWeight
  apply Finset.sum_congr rfl
  intro e he
  rw [if_pos he]

lemma d7SeparatedUnit_nonneg {G : SimpleGraph A} {w : Finset A → ℝ}
    (hw : IsFractionalPacking G w) (e : Sym2 A) :
    0 ≤ d7SeparatedUnit G w e := by
  exact mul_nonneg (inv_nonneg.mpr (fractionalUncoveredWeight_nonneg hw))
    (d7ResidualEdgeWeight_nonneg hw e)

lemma d7SeparatedUnit_le_residual {G : SimpleGraph A}
    {w : Finset A → ℝ} (hw : IsFractionalPacking G w)
    (hone : 1 ≤ fractionalUncoveredWeight G w) (e : Sym2 A) :
    d7SeparatedUnit G w e ≤ d7ResidualEdgeWeight G w e := by
  unfold d7SeparatedUnit
  have hr0 : 0 ≤ d7ResidualEdgeWeight G w e :=
    d7ResidualEdgeWeight_nonneg hw e
  have hinv : (fractionalUncoveredWeight G w)⁻¹ ≤ 1 := by
    simpa using (inv_le_one₀ (by linarith : 0 < fractionalUncoveredWeight G w)).mpr hone
  calc
    (fractionalUncoveredWeight G w)⁻¹ * d7ResidualEdgeWeight G w e ≤
        1 * d7ResidualEdgeWeight G w e :=
      mul_le_mul_of_nonneg_right hinv hr0
    _ = d7ResidualEdgeWeight G w e := one_mul _

lemma d7RemainingResidual_nonneg {G : SimpleGraph A}
    {w : Finset A → ℝ} (hw : IsFractionalPacking G w)
    (hone : 1 ≤ fractionalUncoveredWeight G w) (e : Sym2 A) :
    0 ≤ d7RemainingResidual G w e := by
  exact sub_nonneg.mpr (d7SeparatedUnit_le_residual hw hone e)

lemma sum_d7SeparatedUnit {G : SimpleGraph A} {w : Finset A → ℝ}
    (hone : 1 ≤ fractionalUncoveredWeight G w) :
    ∑ e ∈ G.edgeFinset, d7SeparatedUnit G w e = 1 := by
  unfold d7SeparatedUnit
  rw [← Finset.mul_sum, sum_d7ResidualEdgeWeight]
  have hne : fractionalUncoveredWeight G w ≠ 0 := by linarith
  field_simp

lemma sum_d7RemainingResidual {G : SimpleGraph A} {w : Finset A → ℝ}
    (hone : 1 ≤ fractionalUncoveredWeight G w) :
    ∑ e ∈ G.edgeFinset, d7RemainingResidual G w e =
      fractionalUncoveredWeight G w - 1 := by
  unfold d7RemainingResidual
  rw [Finset.sum_sub_distrib, sum_d7ResidualEdgeWeight,
    sum_d7SeparatedUnit hone]

/-! ## Canonical one-unit split supplied by induction -/

/-- A strong packing on one deletion can be symmetrized and normalized so
that its uncovered vector has mass between one and the original defect;
the separated part then has total mass exactly one. -/
theorem exists_d7CanonicalDeletedWeight_of_strong (G : SimpleGraph A)
    (z : A) {b : ℝ} (hb : HasStrongFractionalPacking (d7DeletedGraph G z) b)
    (hE : 1 ≤ (d7DeletedGraph G z).edgeFinset.card) (h1b : 1 ≤ b) :
    ∃ w : Finset (↑(d7DeletedFinset (A := A) z)) → ℝ,
      IsFractionalPacking (d7DeletedGraph G z) w ∧
      IsHalfBounded (d7DeletedGraph G z) w ∧
      fractionalUncoveredWeight (d7DeletedGraph G z) w ∈ Set.Icc (1 : ℝ) b ∧
      (∀ p : Equiv.Perm (d7RemainingUniversalVertices G z),
        relabelWeight (d7ExtendUniversalPerm G z p) w = w) ∧
      ∑ e ∈ (d7DeletedGraph G z).edgeFinset,
        d7SeparatedUnit (d7DeletedGraph G z) w e = 1 := by
  obtain ⟨v, hvPacking, hvUncovered, hvHalf⟩ := hb
  let w := d7CanonicalDeletedWeight G z v
  have hwPacking : IsFractionalPacking (d7DeletedGraph G z) w :=
    d7CanonicalDeletedWeight_isFractionalPacking G z hvPacking hE
  have hwHalf : IsHalfBounded (d7DeletedGraph G z) w :=
    d7CanonicalDeletedWeight_halfBounded G z hvPacking hvHalf hE
  have hwUncovered : fractionalUncoveredWeight (d7DeletedGraph G z) w ∈
      Set.Icc (1 : ℝ) b :=
    fractionalUncoveredWeight_d7CanonicalDeletedWeight_mem_Icc
      G z hvPacking hE hvUncovered h1b
  refine ⟨w, hwPacking, hwHalf, hwUncovered, ?_, ?_⟩
  · intro p
    exact relabelWeight_d7CanonicalDeletedWeight G z v p
  · exact sum_d7SeparatedUnit hwUncovered.1

lemma d7DeletedGraph_edgeFinset_nonempty_of_four_universal
    (G : SimpleGraph A) {z : A} (hz : z ∈ universalVertices G)
    (hm : 4 ≤ (universalVertices G).card) :
    (d7DeletedGraph G z).edgeFinset.Nonempty := by
  let Z := universalVertices G
  have hcardErase : 3 ≤ (Z.erase z).card := by
    rw [card_erase_of_mem hz]
    omega
  have hnonempty : (Z.erase z).Nonempty := by
    exact card_pos.mp (by omega)
  obtain ⟨x, hx⟩ := hnonempty
  have hxZ : x ∈ Z := mem_of_mem_erase hx
  have hxz : x ≠ z := ne_of_mem_erase hx
  have hcardEraseX : 2 ≤ ((Z.erase z).erase x).card := by
    rw [card_erase_of_mem hx]
    omega
  have hnonemptyX : ((Z.erase z).erase x).Nonempty := by
    exact card_pos.mp (by omega)
  obtain ⟨y, hy⟩ := hnonemptyX
  have hyErase : y ∈ Z.erase z := mem_of_mem_erase hy
  have hyZ : y ∈ Z := mem_of_mem_erase hyErase
  have hyz : y ≠ z := ne_of_mem_erase hyErase
  have hyx : y ≠ x := ne_of_mem_erase hy
  let x' := d7DeletedVertex z x hxz
  let y' := d7DeletedVertex z y hyz
  refine ⟨s(x', y'), ?_⟩
  rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
  change G.Adj x y
  have hxzero : Gᶜ.degree x = 0 := mem_universalVertices.mp hxZ
  by_contra hnot
  have hcomp : Gᶜ.Adj x y := ⟨hyx.symm, hnot⟩
  have hpos := hcomp.degree_pos_left
  rw [hxzero] at hpos
  omega

lemma one_le_d7DeletedGraph_edgeFinset_card_of_four_universal
    (G : SimpleGraph A) {z : A} (hz : z ∈ universalVertices G)
    (hm : 4 ≤ (universalVertices G).card) :
    1 ≤ (d7DeletedGraph G z).edgeFinset.card :=
  Finset.one_le_card.mpr
    (d7DeletedGraph_edgeFinset_nonempty_of_four_universal G hz hm)

/-- In the D7 range, induction supplies one canonical base deletion
weighting; transporting it gives a coherent strong family on every
universal-vertex deletion. -/
theorem exists_d7CoherentUniversalDeletedWeights {n a : ℕ}
    (hcard : Fintype.card A = n) (hn : 14 ≤ n) (ha : a < 4)
    (G : SimpleGraph A) (hexact : missingEdgeCount G = n - 4 + a)
    (hm : 4 ≤ (universalVertices G).card)
    (sigma : A → ℕ) (hsigma : ∀ u, sigma u ≤ d7ResidualAllowance G a u)
    (hstrong : AlmostCompleteStrongAt (n - 1)) :
    ∃ (z₀ : ↑(universalVertices G))
      (w₀ : Finset (↑(d7DeletedFinset (A := A) (z₀ : A))) → ℝ),
      IsFractionalPacking (d7DeletedGraph G (z₀ : A)) w₀ ∧
      IsHalfBounded (d7DeletedGraph G (z₀ : A)) w₀ ∧
      fractionalUncoveredWeight (d7DeletedGraph G (z₀ : A)) w₀ ∈
        Set.Icc (1 : ℝ) (a + 1 : ℕ) ∧
      (∀ p : Equiv.Perm (d7RemainingUniversalVertices G (z₀ : A)),
        relabelWeight (d7ExtendUniversalPerm G (z₀ : A) p) w₀ = w₀) ∧
      (∑ e ∈ (d7DeletedGraph G (z₀ : A)).edgeFinset,
        d7SeparatedUnit (d7DeletedGraph G (z₀ : A)) w₀ e) = 1 ∧
      ∀ z : ↑(universalVertices G),
        IsFractionalPacking (d7DeletedGraph G (z : A))
          (d7CoherentUniversalDeletedWeight G z₀ w₀ z) ∧
        IsHalfBounded (d7DeletedGraph G (z : A))
          (d7CoherentUniversalDeletedWeight G z₀ w₀ z) ∧
        fractionalUncoveredWeight (d7DeletedGraph G (z : A))
          (d7CoherentUniversalDeletedWeight G z₀ w₀ z) ∈
            Set.Icc (1 : ℝ) (a + 1 : ℕ) := by
  have hZ : (universalVertices G).Nonempty := by
    exact card_pos.mp (by omega)
  let z₀ : ↑(universalVertices G) := ⟨hZ.choose, hZ.choose_spec⟩
  have hzNot : (z₀ : A) ∉ nonUniversalVertices G := by
    rw [mem_nonUniversalVertices]
    rw [mem_universalVertices.mp z₀.property]
    omega
  have hraw := d7DeletedGraph_hasStrongFractionalPacking hcard hn ha G hexact
    sigma hsigma hstrong (z₀ : A)
  have hraw' : HasStrongFractionalPacking (d7DeletedGraph G (z₀ : A))
      ((a + 1 : ℕ) : ℝ) := by
    simpa only [d7LocalDefect, if_neg hzNot] using hraw
  have hE : 1 ≤ (d7DeletedGraph G (z₀ : A)).edgeFinset.card :=
    one_le_d7DeletedGraph_edgeFinset_card_of_four_universal G z₀.property hm
  obtain ⟨w₀, hwPack, hwHalf, hwUncov, hwSymm, hwOne⟩ :=
    exists_d7CanonicalDeletedWeight_of_strong G (z₀ : A) hraw' hE
      (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le a))
  refine ⟨z₀, w₀, hwPack, hwHalf, hwUncov, hwSymm, hwOne, ?_⟩
  intro z
  refine ⟨d7CoherentUniversalDeletedWeight_isFractionalPacking G z₀
    hwPack z, d7CoherentUniversalDeletedWeight_halfBounded G z₀ hwHalf z, ?_⟩
  rw [fractionalUncoveredWeight_d7CoherentUniversalDeletedWeight]
  exact hwUncov

/-! ## Weighted attached-triangle families for the D7 correction -/

lemma adj_of_mem_universalVertices (G : SimpleGraph A) {z x : A}
    (hz : z ∈ universalVertices G) (hzx : z ≠ x) : G.Adj z x := by
  have hzzero : Gᶜ.degree z = 0 := mem_universalVertices.mp hz
  by_contra hnot
  have hcomp : Gᶜ.Adj z x := ⟨hzx, hnot⟩
  have hpos := hcomp.degree_pos_left
  rw [hzzero] at hpos
  omega

/-- Edge-dependent version of `attachedEdgeWeight`. -/
def weightedAttachedEdgeWeight (S : Finset A) (u : A)
    (C : Finset (Sym2 S)) (r : Sym2 S → ℝ) : Finset A → ℝ :=
  fun t ↦ ∑ e : ↑C, singleTriangleWeight (attachedEdgeTriangle S u e) (r e) t

lemma weightedAttachedEdgeWeight_nonneg {G : SimpleGraph A} {S : Finset A}
    {u : A} {C : Finset (Sym2 S)} {r : Sym2 S → ℝ}
    (hr : ∀ e ∈ C, 0 ≤ r e) :
    ∀ t ∈ G.cliqueFinset 3, 0 ≤ weightedAttachedEdgeWeight S u C r t := by
  intro t _
  unfold weightedAttachedEdgeWeight singleTriangleWeight
  exact Finset.sum_nonneg fun e _ ↦ by
    split_ifs
    · exact hr e e.property
    · exact le_rfl

lemma fractionalEdgeLoad_weightedAttachedEdgeWeight
    {G : SimpleGraph A} {S : Finset A} {u : A}
    {C : Finset (Sym2 S)} {r : Sym2 S → ℝ}
    (htri : ∀ e ∈ C, attachedEdgeTriangle S u e ∈ G.cliqueFinset 3)
    (p : Sym2 A) :
    fractionalEdgeLoad G (weightedAttachedEdgeWeight S u C r) p =
      ∑ e : ↑C, if p ∈ (attachedEdgeTriangle S u e).sym2 then r e else 0 := by
  unfold weightedAttachedEdgeWeight
  rw [fractionalEdgeLoad_sum]
  apply Finset.sum_congr rfl
  intro e _
  exact fractionalEdgeLoad_singleTriangle (htri e e.property) (r e) p

/-! ## Abstract D7 separated parameters -/

/-- The three orbit parameters extracted from a coherent separated unit.
The normalization field is equation (5.4) of the paper, written over
`Real` so no truncated natural subtraction enters the correction algebra. -/
structure D7SeparatedParameters (G : SimpleGraph A) where
  gamma : ℝ
  alpha : ↑(nonUniversalVertices G) → ℝ
  beta : Sym2 (↑(nonUniversalVertices G)) → ℝ
  gamma_nonneg : 0 ≤ gamma
  alpha_nonneg : ∀ u, 0 ≤ alpha u
  beta_nonneg : ∀ e ∈ (G.induce
    (↑(nonUniversalVertices G) : Set A)).edgeFinset, 0 ≤ beta e
  normalization :
    ((((universalVertices G).card : ℝ) - 1) *
        (((universalVertices G).card : ℝ) - 2) / 2) * gamma +
      (((universalVertices G).card : ℝ) - 1) * ∑ u, alpha u +
      ∑ e ∈ (G.induce
        (↑(nonUniversalVertices G) : Set A)).edgeFinset, beta e = 1

def D7SeparatedParameters.alphaMass {G : SimpleGraph A}
    (P : D7SeparatedParameters G) : ℝ :=
  (((universalVertices G).card : ℝ) - 1) * ∑ u, P.alpha u

def D7SeparatedParameters.betaMass {G : SimpleGraph A}
    (P : D7SeparatedParameters G) : ℝ :=
  ∑ e ∈ (G.induce
    (↑(nonUniversalVertices G) : Set A)).edgeFinset, P.beta e

def D7SeparatedParameters.betaIncident {G : SimpleGraph A}
    (P : D7SeparatedParameters G)
    (u : ↑(nonUniversalVertices G)) : ℝ :=
  ∑ e ∈ (G.induce
    (↑(nonUniversalVertices G) : Set A)).edgeFinset with
      (u : ↑(nonUniversalVertices G)) ∈ e.toFinset, P.beta e

lemma D7SeparatedParameters.alphaMass_nonneg {G : SimpleGraph A}
    (P : D7SeparatedParameters G)
    (hm : 1 ≤ (universalVertices G).card) :
    0 ≤ P.alphaMass := by
  unfold alphaMass
  apply mul_nonneg
  · exact sub_nonneg.mpr (by exact_mod_cast hm)
  · exact Finset.sum_nonneg fun u _ ↦ P.alpha_nonneg u

lemma D7SeparatedParameters.betaMass_nonneg {G : SimpleGraph A}
    (P : D7SeparatedParameters G) :
    0 ≤ P.betaMass := by
  unfold betaMass
  exact Finset.sum_nonneg fun e he ↦ P.beta_nonneg e he

lemma D7SeparatedParameters.gammaTerm_nonneg {G : SimpleGraph A}
    (P : D7SeparatedParameters G)
    (hm : 2 ≤ (universalVertices G).card) :
    0 ≤ ((((universalVertices G).card : ℝ) - 1) *
      (((universalVertices G).card : ℝ) - 2) / 2) * P.gamma := by
  have h₁ : 0 ≤ ((universalVertices G).card : ℝ) - 1 := by
    exact sub_nonneg.mpr (by exact_mod_cast (hm.trans' (by omega : 1 ≤ 2)))
  have h₂ : 0 ≤ ((universalVertices G).card : ℝ) - 2 := by
    exact sub_nonneg.mpr (by exact_mod_cast hm)
  exact mul_nonneg (div_nonneg (mul_nonneg h₁ h₂) (by norm_num))
    P.gamma_nonneg

lemma D7SeparatedParameters.alphaMass_le_one {G : SimpleGraph A}
    (P : D7SeparatedParameters G)
    (hm : 2 ≤ (universalVertices G).card) :
    P.alphaMass ≤ 1 := by
  have hgamma := P.gammaTerm_nonneg hm
  have hbeta := P.betaMass_nonneg
  change 0 ≤ (∑ e ∈ (G.induce
    (↑(nonUniversalVertices G) : Set A)).edgeFinset, P.beta e) at hbeta
  rw [← P.normalization]
  change (((universalVertices G).card : ℝ) - 1) * ∑ u, P.alpha u ≤ _
  linarith

lemma D7SeparatedParameters.betaMass_le_one {G : SimpleGraph A}
    (P : D7SeparatedParameters G)
    (hm : 2 ≤ (universalVertices G).card) :
    P.betaMass ≤ 1 := by
  have hgamma := P.gammaTerm_nonneg hm
  have halpha := P.alphaMass_nonneg (by omega)
  change 0 ≤ (((universalVertices G).card : ℝ) - 1) *
    ∑ u, P.alpha u at halpha
  rw [← P.normalization]
  change (∑ e ∈ (G.induce
    (↑(nonUniversalVertices G) : Set A)).edgeFinset, P.beta e) ≤ _
  linarith

lemma D7SeparatedParameters.betaIncident_nonneg
    {G : SimpleGraph A} (P : D7SeparatedParameters G)
    (u : ↑(nonUniversalVertices G)) :
    0 ≤ P.betaIncident u := by
  unfold betaIncident
  exact Finset.sum_nonneg fun e he ↦ P.beta_nonneg e (mem_filter.mp he).1

lemma D7SeparatedParameters.betaIncident_le_betaMass
    {G : SimpleGraph A} (P : D7SeparatedParameters G)
    (u : ↑(nonUniversalVertices G)) :
    P.betaIncident u ≤ P.betaMass := by
  unfold betaIncident betaMass
  exact Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
    (fun e he _ ↦ P.beta_nonneg e he)

/-- The coefficient placed on a triangle with one nonuniversal and two
universal vertices in the large-`m` D7 correction. -/
def D7SeparatedParameters.largeMixedCoefficient
    {G : SimpleGraph A} (P : D7SeparatedParameters G)
    (u : ↑(nonUniversalVertices G)) : ℝ :=
  (1 + (((universalVertices G).card : ℝ) - 1) * P.alpha u -
      P.betaIncident u) /
    (((universalVertices G).card : ℝ) - 1)

lemma D7SeparatedParameters.largeMixedCoefficient_nonneg
    {G : SimpleGraph A} (P : D7SeparatedParameters G)
    (hm : 4 ≤ (universalVertices G).card)
    (u : ↑(nonUniversalVertices G)) :
    0 ≤ P.largeMixedCoefficient u := by
  unfold largeMixedCoefficient
  have hden : 0 < ((universalVertices G).card : ℝ) - 1 := by
    have hc : (1 : ℝ) < ((universalVertices G).card : ℝ) := by
      exact_mod_cast (by omega : 1 < (universalVertices G).card)
    linarith
  apply div_nonneg
  · have hinc : P.betaIncident u ≤ 1 :=
      (P.betaIncident_le_betaMass u).trans (P.betaMass_le_one (by omega))
    have halpha := P.alpha_nonneg u
    nlinarith
  · exact hden.le

/-- The constant coefficient placed on a triangle of three universal
vertices in the large-`m` D7 correction. -/
def D7SeparatedParameters.largeUniversalCoefficient
    {G : SimpleGraph A} (P : D7SeparatedParameters G) : ℝ :=
  (2 + (((universalVertices G).card : ℝ) - 2) * P.gamma -
      ((Fintype.card A : ℝ) - (universalVertices G).card) /
        (((universalVertices G).card : ℝ) - 1) -
      P.alphaMass / (((universalVertices G).card : ℝ) - 1) +
      2 * P.betaMass / (((universalVertices G).card : ℝ) - 1)) /
    (((universalVertices G).card : ℝ) - 2)

lemma D7SeparatedParameters.largeUniversalCoefficient_nonneg
    {G : SimpleGraph A} (P : D7SeparatedParameters G)
    (hn : 14 ≤ Fintype.card A)
    (hm : 4 ≤ (universalVertices G).card)
    (hlarge : Fintype.card A - 7 ≤ (universalVertices G).card) :
    0 ≤ P.largeUniversalCoefficient := by
  let m : ℝ := ((universalVertices G).card : ℝ)
  let q : ℝ := (Fintype.card A : ℝ)
  let alpha : ℝ := P.alphaMass
  let beta : ℝ := P.betaMass
  have hm₁ : 0 < m - 1 := by
    dsimp only [m]
    have hcast : (1 : ℝ) < ((universalVertices G).card : ℝ) := by
      exact_mod_cast (by omega : 1 < (universalVertices G).card)
    linarith
  have hm₂ : 0 < m - 2 := by
    dsimp only [m]
    have hcast : (2 : ℝ) < ((universalVertices G).card : ℝ) := by
      exact_mod_cast (by omega : 2 < (universalVertices G).card)
    linarith
  have halpha₀ : 0 ≤ alpha := by
    exact P.alphaMass_nonneg (by omega)
  have halpha₁ : alpha ≤ 1 := by
    exact P.alphaMass_le_one (by omega)
  have hbeta₀ : 0 ≤ beta := P.betaMass_nonneg
  have hnorm : ((m - 1) * (m - 2) / 2) * P.gamma + alpha + beta = 1 := by
    simpa only [m, alpha, beta, D7SeparatedParameters.alphaMass,
      D7SeparatedParameters.betaMass] using P.normalization
  have hgapNat : Fintype.card A + 7 ≤ 3 * (universalVertices G).card := by
    omega
  have hgap : q + 7 ≤ 3 * m := by
    dsimp only [q, m]
    exact_mod_cast hgapNat
  have htarget : 0 ≤ 3 * m - q - 3 * alpha := by
    nlinarith
  let numerator : ℝ :=
    2 + (m - 2) * P.gamma - (q - m) / (m - 1) -
      alpha / (m - 1) + 2 * beta / (m - 1)
  have heq : (m - 1) * numerator = 3 * m - q - 3 * alpha := by
    dsimp only [numerator]
    field_simp [ne_of_gt hm₁]
    nlinarith [hnorm]
  have hnum : 0 ≤ numerator := by
    apply nonneg_of_mul_nonneg_right (a := m - 1)
    · rw [heq]
      exact htarget
    · exact hm₁
  unfold largeUniversalCoefficient
  change 0 ≤ numerator / (m - 2)
  exact div_nonneg hnum hm₂.le

end

end Erdos76
