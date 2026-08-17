/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

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

import ErdosProblems.Erdos636.External.Erdos88.ProductPermutationConcentration
import ErdosProblems.Erdos636.External.Erdos88.SignedSliceConcentration
import ErdosProblems.Erdos636.AugmentationIdentity
import ErdosProblems.Erdos636.OuterSwitching
import ErdosProblems.Erdos636.SliceMoments

/-!
# Uniform degree control on the outer switching path

This file is the finite concentration step in Claim 4.4 of
Kwan--Sudakov.  A single pair of permutations of the two structural
switching cells is chosen.  Simultaneously for every switching time and
every member of the structural matching, its degree into the current
switching set is close to the same deterministic hypergeometric mean.

The theorem is stated with the exact finite union-bound inequality.  Its
only graph-theoretic bounded-difference input is that changing one image of
one of the two permutations exchanges at most two vertices of the current
state.  Consequently the Lipschitz constant is `2 * K`, independent of the
number of vertices.
-/

open Classical SimpleGraph
open scoped BigOperators

namespace Erdos636
namespace StructuralOuterConcentration

open Erdos88
open Erdos88.BooleanSlices
open Erdos88.FiniteSliceConcentration
open OuterSwitching

universe u

noncomputable section

variable {V : Type u} [Fintype V] [DecidableEq V]

/-! ## Two shared permutation buckets -/

/-- The two permutation lengths, written as a dependent `Fin 2` tuple. -/
abbrev sideCard {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b : ℝ}
    (S : StructuralWitness G scale nW ell K alpha aDisc aDiv b) :
    Fin 2 → ℕ := fun _ ↦ nW

/-- A shared pair of uniform permutations of the two switching cells. -/
abbrev OrderingSampler {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b : ℝ}
    (S : StructuralWitness G scale nW ell K alpha aDisc aDiv b) :=
  PermutationProduct (sideCard S)

/-- Convert the two sampled permutations to the order convention of
`SwitchingOrderings.state`.  The minus ordering is reversed, so its suffix
at time `i` is the first `nW-i` images of the sampled permutation. -/
def sampledOrderings {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b : ℝ}
    (S : StructuralWitness G scale nW ell K alpha aDisc aDiv b)
    (sigma : OrderingSampler S) :
    SwitchingOrderings S.Wminus S.Wplus nW where
  minus i := ((Finset.equivFin S.Wminus).symm
    (Fin.cast S.card_Wminus.symm (sigma 0 (Fin.rev i)))).1
  plus i := ((Finset.equivFin S.Wplus).symm
    (Fin.cast S.card_Wplus.symm (sigma 1 i))).1
  minus_injective := by
    intro i j hij
    apply Fin.rev_injective
    apply (sigma 0).injective
    apply Fin.cast_injective
    apply (Finset.equivFin S.Wminus).symm.injective
    exact Subtype.ext hij
  plus_injective := by
    intro i j hij
    apply (sigma 1).injective
    apply Fin.cast_injective
    apply (Finset.equivFin S.Wplus).symm.injective
    exact Subtype.ext hij
  minus_mem i := ((Finset.equivFin S.Wminus).symm _).2
  plus_mem i := ((Finset.equivFin S.Wplus).symm _).2
  minus_surjective := by
    intro v hv
    let j : Fin nW := Fin.cast S.card_Wminus
      (Finset.equivFin S.Wminus ⟨v, hv⟩)
    let i : Fin nW := ((sigma 0).symm j).rev
    refine ⟨i, ?_⟩
    simp [i, j]
  plus_surjective := by
    intro v hv
    let j : Fin nW := Fin.cast S.card_Wplus
      (Finset.equivFin S.Wplus ⟨v, hv⟩)
    let i : Fin nW := (sigma 1).symm j
    refine ⟨i, ?_⟩
    simp [i, j]

/-- A literal prefix of a permutation enumerating a finset of a specified
cardinality. -/
def cellPrefix (W : Finset V) (n : ℕ) (hW : W.card = n)
    (sigma : Equiv.Perm (Fin n)) (r : ℕ) (hr : r ≤ n) : Finset V :=
  Finset.univ.image fun j : Fin r ↦
    ((Finset.equivFin W).symm
      (Fin.cast hW.symm (sigma (Fin.castLE hr j)))).1

/-- The minus part of the state, expressed as a literal permutation
prefix. -/
def sampledMinusPrefix {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b : ℝ}
    (S : StructuralWitness G scale nW ell K alpha aDisc aDiv b)
    (sigma : OrderingSampler S) (i : ℕ) (hi : i ≤ nW) : Finset V :=
  cellPrefix S.Wminus nW S.card_Wminus (sigma 0) (nW - i)
    (Nat.sub_le nW i)

/-- The plus part of the state, expressed as a literal permutation prefix. -/
def sampledPlusPrefix {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b : ℝ}
    (S : StructuralWitness G scale nW ell K alpha aDisc aDiv b)
    (sigma : OrderingSampler S) (i : ℕ) (hi : i ≤ nW) : Finset V :=
  cellPrefix S.Wplus nW S.card_Wplus (sigma 1) i hi

lemma sampledMinusPrefix_subset {G : SimpleGraph V}
    {scale nW ell K : ℕ} {alpha aDisc aDiv b : ℝ}
    (S : StructuralWitness G scale nW ell K alpha aDisc aDiv b)
    (sigma : OrderingSampler S) (i : ℕ) (hi : i ≤ nW) :
    sampledMinusPrefix S sigma i hi ⊆ S.Wminus :=
  by
    intro v hv
    rw [sampledMinusPrefix, cellPrefix] at hv
    obtain ⟨r, _hr, rfl⟩ := Finset.mem_image.mp hv
    exact ((Finset.equivFin S.Wminus).symm _).2

lemma sampledPlusPrefix_subset {G : SimpleGraph V}
    {scale nW ell K : ℕ} {alpha aDisc aDiv b : ℝ}
    (S : StructuralWitness G scale nW ell K alpha aDisc aDiv b)
    (sigma : OrderingSampler S) (i : ℕ) (hi : i ≤ nW) :
    sampledPlusPrefix S sigma i hi ⊆ S.Wplus :=
  by
    intro v hv
    rw [sampledPlusPrefix, cellPrefix] at hv
    obtain ⟨r, _hr, rfl⟩ := Finset.mem_image.mp hv
    exact ((Finset.equivFin S.Wplus).symm _).2

/-- The reversal in `sampledOrderings` makes its two state pieces exactly
the two literal prefixes above. -/
lemma sampledOrderings_state_eq_prefix_union {G : SimpleGraph V}
    {scale nW ell K : ℕ} {alpha aDisc aDiv b : ℝ}
    (S : StructuralWitness G scale nW ell K alpha aDisc aDiv b)
    (sigma : OrderingSampler S) (i : ℕ) (hi : i ≤ nW) :
    (sampledOrderings S sigma).state i =
      sampledMinusPrefix S sigma i hi ∪ sampledPlusPrefix S sigma i hi := by
  classical
  ext v
  simp only [SwitchingOrderings.state, sampledMinusPrefix, sampledPlusPrefix,
    sampledOrderings, cellPrefix,
    Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · rintro (⟨j, hij, rfl⟩ | ⟨j, hji, rfl⟩)
    · left
      let r : Fin (nW - i) := ⟨(Fin.rev j).val, by
        rw [Fin.val_rev]
        have hjlt : j.val < nW := j.isLt
        omega⟩
      refine ⟨r, ?_⟩
      apply congrArg Subtype.val
      apply congrArg (Finset.equivFin S.Wminus).symm
      apply congrArg (Fin.cast S.card_Wminus.symm)
      apply congrArg (sigma 0)
      apply Fin.ext
      rfl
    · right
      let r : Fin i := ⟨j.val, hji⟩
      refine ⟨r, ?_⟩
      apply congrArg Subtype.val
      apply congrArg (Finset.equivFin S.Wplus).symm
      apply congrArg (Fin.cast S.card_Wplus.symm)
      apply congrArg (sigma 1)
      apply Fin.ext
      rfl
  · rintro (⟨r, hrv⟩ | ⟨r, hrv⟩)
    · left
      let j : Fin nW := Fin.rev (Fin.castLE (Nat.sub_le nW i) r)
      refine ⟨j, ?_, ?_⟩
      · dsimp [j]
        have hrlt := r.isLt
        omega
      · rw [← hrv]
        simp [j]
    · right
      let j : Fin nW := Fin.castLE hi r
      refine ⟨j, ?_, ?_⟩
      · exact r.isLt
      · rw [← hrv]

/-! ## Degree perturbation under a two-vertex exchange -/

lemma degreeInto_le_add_card_mul_sdiff (G : SimpleGraph V)
    (U T x : Finset V) :
    degreeInto G U x ≤ degreeInto G T x + x.card * (U \ T).card := by
  rw [degreeInto, degreeInto]
  calc
    ∑ v ∈ x, (Erdos88.neighborsIn G v U).card ≤
        ∑ v ∈ x, ((Erdos88.neighborsIn G v T).card + (U \ T).card) := by
      apply Finset.sum_le_sum
      intro v _hv
      calc
        (Erdos88.neighborsIn G v U).card ≤
            ((Erdos88.neighborsIn G v T) ∪ (U \ T)).card := by
          apply Finset.card_le_card
          intro w hw
          have hwU := (Erdos88.mem_neighborsIn.mp hw).1
          have hadj := (Erdos88.mem_neighborsIn.mp hw).2
          by_cases hwT : w ∈ T
          · exact Finset.mem_union_left _
              (Erdos88.mem_neighborsIn.mpr ⟨hwT, hadj⟩)
          · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hwU, hwT⟩)
        _ ≤ (Erdos88.neighborsIn G v T).card + (U \ T).card :=
          Finset.card_union_le _ _
    _ = ∑ v ∈ x, (Erdos88.neighborsIn G v T).card +
          x.card * (U \ T).card := by
      simp only [Finset.sum_add_distrib]
      simp

/-- If each directional set difference has at most `c` vertices, changing
the target set changes the multiset degree by at most `c * |x|`. -/
lemma abs_degreeInto_sub_le_of_sdiff_card_le (G : SimpleGraph V)
    (U T x : Finset V) (c : ℕ)
    (hUT : (U \ T).card ≤ c) (hTU : (T \ U).card ≤ c) :
    |(degreeInto G U x : ℝ) - degreeInto G T x| ≤ c * x.card := by
  have hforward := degreeInto_le_add_card_mul_sdiff G U T x
  have hback := degreeInto_le_add_card_mul_sdiff G T U x
  have hmulForward : x.card * (U \ T).card ≤ x.card * c :=
    Nat.mul_le_mul_left _ hUT
  have hmulBack : x.card * (T \ U).card ≤ x.card * c :=
    Nat.mul_le_mul_left _ hTU
  have hforward' : (degreeInto G U x : ℝ) ≤
      degreeInto G T x + c * x.card := by
    have := hforward.trans
      (Nat.add_le_add_left hmulForward (degreeInto G T x))
    exact_mod_cast (by simpa [Nat.mul_comm] using this)
  have hback' : (degreeInto G T x : ℝ) ≤
      degreeInto G U x + c * x.card := by
    have := hback.trans
      (Nat.add_le_add_left hmulBack (degreeInto G U x))
    exact_mod_cast (by simpa [Nat.mul_comm] using this)
  rw [abs_le]
  constructor <;> linarith

lemma map_swap_sdiff_subset_pair (U : Finset V) (p q : V) :
    U.map (Equiv.swap p q).toEmbedding \ U ⊆ {p, q} := by
  intro v hv
  obtain ⟨hvMap, hvU⟩ := Finset.mem_sdiff.mp hv
  obtain ⟨w, hwU, hwv⟩ := Finset.mem_map.mp hvMap
  by_cases hwp : w = p
  · subst w
    simp at hwv ⊢
    exact Or.inr hwv.symm
  by_cases hwq : w = q
  · subst w
    simp [hwp] at hwv ⊢
    exact Or.inl hwv.symm
  have hfix : Equiv.swap p q w = w := Equiv.swap_apply_of_ne_of_ne hwp hwq
  apply (hvU ?_).elim
  rw [← hwv]
  change (Equiv.swap p q) w ∈ U
  rw [hfix]
  exact hwU

lemma sdiff_map_swap_subset_pair (U : Finset V) (p q : V) :
    U \ U.map (Equiv.swap p q).toEmbedding ⊆ {p, q} := by
  intro v hv
  obtain ⟨hvU, hvMap⟩ := Finset.mem_sdiff.mp hv
  by_cases hvp : v = p
  · simp [hvp]
  by_cases hvq : v = q
  · simp [hvq]
  have hfix : Equiv.swap p q v = v := Equiv.swap_apply_of_ne_of_ne hvp hvq
  apply (hvMap ?_).elim
  exact Finset.mem_map.mpr ⟨v, hvU, hfix⟩

lemma map_swap_sdiff_card_le_two (U : Finset V) (p q : V) :
    (U.map (Equiv.swap p q).toEmbedding \ U).card ≤ 2 := by
  calc
    _ ≤ ({p, q} : Finset V).card :=
      Finset.card_le_card (map_swap_sdiff_subset_pair U p q)
    _ ≤ ({q} : Finset V).card + 1 := Finset.card_insert_le p {q}
    _ = 2 := by simp

lemma sdiff_map_swap_card_le_two (U : Finset V) (p q : V) :
    (U \ U.map (Equiv.swap p q).toEmbedding).card ≤ 2 := by
  calc
    _ ≤ ({p, q} : Finset V).card :=
      Finset.card_le_card (sdiff_map_swap_subset_pair U p q)
    _ ≤ ({q} : Finset V).card + 1 := Finset.card_insert_le p {q}
    _ = 2 := by simp

/-- A transposition of two ambient vertices changes the degree of an
`x`-cell by at most `2|x|`. -/
lemma abs_degreeInto_map_swap_sub_le (G : SimpleGraph V)
    (U x : Finset V) (p q : V) :
    |(degreeInto G (U.map (Equiv.swap p q).toEmbedding) x : ℝ) -
        degreeInto G U x| ≤ 2 * x.card := by
  exact abs_degreeInto_sub_le_of_sdiff_card_le G
    (U.map (Equiv.swap p q).toEmbedding) U x 2
      (map_swap_sdiff_card_le_two U p q)
      (sdiff_map_swap_card_le_two U p q)

lemma map_swap_eq_self_of_not_mem (U : Finset V) (p q : V)
    (hp : p ∉ U) (hq : q ∉ U) :
    U.map (Equiv.swap p q).toEmbedding = U := by
  ext v
  constructor
  · intro hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hv
    by_cases hwp : w = p
    · exact (hp (hwp ▸ hw)).elim
    by_cases hwq : w = q
    · exact (hq (hwq ▸ hw)).elim
    simpa [Equiv.swap_apply_of_ne_of_ne hwp hwq] using hw
  · intro hv
    have hvp : v ≠ p := fun h ↦ hp (h ▸ hv)
    have hvq : v ≠ q := fun h ↦ hq (h ▸ hv)
    exact Finset.mem_map.mpr
      ⟨v, hv, Equiv.swap_apply_of_ne_of_ne hvp hvq⟩

def minusVertex {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b : ℝ}
    (S : StructuralWitness G scale nW ell K alpha aDisc aDiv b)
    (p : Fin nW) : V :=
  ((Finset.equivFin S.Wminus).symm
    (Fin.cast S.card_Wminus.symm p)).1

def plusVertex {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b : ℝ}
    (S : StructuralWitness G scale nW ell K alpha aDisc aDiv b)
    (p : Fin nW) : V :=
  ((Finset.equivFin S.Wplus).symm
    (Fin.cast S.card_Wplus.symm p)).1

lemma minusVertex_mem {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b : ℝ}
    (S : StructuralWitness G scale nW ell K alpha aDisc aDiv b)
    (p : Fin nW) : minusVertex S p ∈ S.Wminus :=
  ((Finset.equivFin S.Wminus).symm _).2

lemma plusVertex_mem {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b : ℝ}
    (S : StructuralWitness G scale nW ell K alpha aDisc aDiv b)
    (p : Fin nW) : plusVertex S p ∈ S.Wplus :=
  ((Finset.equivFin S.Wplus).symm _).2

lemma minusVertex_injective {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b : ℝ}
    (S : StructuralWitness G scale nW ell K alpha aDisc aDiv b) :
    Function.Injective (minusVertex S) := by
  intro p q hpq
  apply Fin.cast_injective
  apply (Finset.equivFin S.Wminus).symm.injective
  exact Subtype.ext hpq

lemma plusVertex_injective {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b : ℝ}
    (S : StructuralWitness G scale nW ell K alpha aDisc aDiv b) :
    Function.Injective (plusVertex S) := by
  intro p q hpq
  apply Fin.cast_injective
  apply (Finset.equivFin S.Wplus).symm.injective
  exact Subtype.ext hpq

/-- A sampler transposition maps every state by the corresponding ambient
vertex transposition. -/
lemma sampledOrderings_state_left_swap {G : SimpleGraph V}
    {scale nW ell K : ℕ} {alpha aDisc aDiv b : ℝ}
    (S : StructuralWitness G scale nW ell K alpha aDisc aDiv b)
    (sigma tau : OrderingSampler S) (k : Fin 2)
    (p q : Fin (sideCard S k))
    (hk : tau k = Equiv.swap p q * sigma k)
    (hsame : ∀ j, j ≠ k → tau j = sigma j)
    (i : ℕ) (hi : i ≤ nW) :
    ∃ a c : V,
      (sampledOrderings S tau).state i =
        ((sampledOrderings S sigma).state i).map
          (Equiv.swap a c).toEmbedding := by
  fin_cases k
  · change Fin nW at p q
    have hk0 : tau 0 = Equiv.swap p q * sigma 0 := by
      simpa using hk
    let a : V := minusVertex S p
    let c : V := minusVertex S q
    have hminus : sampledMinusPrefix S tau i hi =
        (sampledMinusPrefix S sigma i hi).map
          (Equiv.swap a c).toEmbedding := by
      ext v
      simp only [sampledMinusPrefix, cellPrefix, Finset.mem_image, Finset.mem_univ,
        true_and, Finset.mem_map, hk0, Equiv.Perm.mul_apply]
      constructor
      · rintro ⟨r, rfl⟩
        refine ⟨minusVertex S (sigma 0 (Fin.castLE (Nat.sub_le nW i) r)),
          ⟨r, by simp [minusVertex]⟩, ?_⟩
        simpa [a, c, minusVertex] using
          ((minusVertex_injective S).map_swap p q
            (sigma 0 (Fin.castLE (Nat.sub_le nW i) r))).symm
      · rintro ⟨w, ⟨r, rfl⟩, rfl⟩
        refine ⟨r, ?_⟩
        simpa [a, c, minusVertex] using
          (minusVertex_injective S).map_swap p q
            (sigma 0 (Fin.castLE (Nat.sub_le nW i) r))
    have hplusSigma : tau 1 = sigma 1 := hsame 1 (by decide)
    have haPlus : a ∉ sampledPlusPrefix S sigma i hi := by
      intro ha
      exact Finset.disjoint_left.mp S.disjoint_Wminus_Wplus
        (minusVertex_mem S p) (sampledPlusPrefix_subset S sigma i hi ha)
    have hcPlus : c ∉ sampledPlusPrefix S sigma i hi := by
      intro hc
      exact Finset.disjoint_left.mp S.disjoint_Wminus_Wplus
        (minusVertex_mem S q) (sampledPlusPrefix_subset S sigma i hi hc)
    refine ⟨a, c, ?_⟩
    rw [sampledOrderings_state_eq_prefix_union S tau i hi,
      sampledOrderings_state_eq_prefix_union S sigma i hi]
    rw [hminus]
    have hplus : sampledPlusPrefix S tau i hi =
        sampledPlusPrefix S sigma i hi := by
      simp [sampledPlusPrefix, hplusSigma]
    rw [hplus, Finset.map_union,
      map_swap_eq_self_of_not_mem _ _ _ haPlus hcPlus]
  · change Fin nW at p q
    have hk1 : tau 1 = Equiv.swap p q * sigma 1 := by
      simpa using hk
    let a : V := plusVertex S p
    let c : V := plusVertex S q
    have hplus : sampledPlusPrefix S tau i hi =
        (sampledPlusPrefix S sigma i hi).map
          (Equiv.swap a c).toEmbedding := by
      ext v
      simp only [sampledPlusPrefix, cellPrefix, Finset.mem_image, Finset.mem_univ,
        true_and, Finset.mem_map, hk1, Equiv.Perm.mul_apply]
      constructor
      · rintro ⟨r, rfl⟩
        refine ⟨plusVertex S (sigma 1 (Fin.castLE hi r)),
          ⟨r, by simp [plusVertex]⟩, ?_⟩
        simpa [a, c, plusVertex] using
          ((plusVertex_injective S).map_swap p q
            (sigma 1 (Fin.castLE hi r))).symm
      · rintro ⟨w, ⟨r, rfl⟩, rfl⟩
        refine ⟨r, ?_⟩
        simpa [a, c, plusVertex] using
          (plusVertex_injective S).map_swap p q (sigma 1 (Fin.castLE hi r))
    have hminusSigma : tau 0 = sigma 0 := hsame 0 (by decide)
    have haMinus : a ∉ sampledMinusPrefix S sigma i hi := by
      intro ha
      exact Finset.disjoint_left.mp S.disjoint_Wminus_Wplus
        (sampledMinusPrefix_subset S sigma i hi ha) (plusVertex_mem S p)
    have hcMinus : c ∉ sampledMinusPrefix S sigma i hi := by
      intro hc
      exact Finset.disjoint_left.mp S.disjoint_Wminus_Wplus
        (sampledMinusPrefix_subset S sigma i hi hc) (plusVertex_mem S q)
    refine ⟨a, c, ?_⟩
    rw [sampledOrderings_state_eq_prefix_union S tau i hi,
      sampledOrderings_state_eq_prefix_union S sigma i hi]
    rw [hplus]
    have hminus : sampledMinusPrefix S tau i hi =
        sampledMinusPrefix S sigma i hi := by
      simp [sampledMinusPrefix, hminusSigma]
    rw [hminus, Finset.map_union,
      map_swap_eq_self_of_not_mem _ _ _ haMinus hcMinus]

/-! ## Exact hypergeometric centers -/

/-- Exact mean of the multiset degree into a permutation prefix. -/
lemma uniformExpectation_degreeInto_prefix
    (G : SimpleGraph V) (W x : Finset V) (r d : ℕ)
    (hr : r ≤ W.card) (hW : W.Nonempty)
    (hd : degreeInto G W x = d) :
    Erdos88.Concentration.uniformExpectation
        (fun sigma : Equiv.Perm (Fin W.card) ↦
          (degreeInto G
            (signedSlicePositiveSupport W r 0 (by simpa using hr)
              (Finset.equivFin W).symm sigma) x : ℝ)) =
      (r : ℝ) / W.card * d := by
  let E := signedSliceZeroEquiv W r
  have hdecode := uniformExpectation_signedSliceDecode W r 0
    (by simpa using hr) (Finset.equivFin W).symm
      (fun T ↦ (degreeInto G T.1.1 x : ℝ))
  have hequiv :
      Erdos88.Concentration.uniformExpectation
          (fun T : SignedSlicePoint W r 0 ↦
            (degreeInto G T.1.1 x : ℝ)) =
        Erdos88.Concentration.uniformExpectation
          (fun T : BooleanSlicePoint W r ↦
            (degreeInto G T.1 x : ℝ)) := by
    unfold Erdos88.Concentration.uniformExpectation
    rw [Fintype.card_congr E]
    congr 1
    exact E.sum_comp (fun T : BooleanSlicePoint W r ↦
      (degreeInto G T.1 x : ℝ))
  have hslice := SliceMoments.expectation_sum_card_neighborsIn
    G x W r hr hW
  have hslice' :
      Erdos88.Concentration.uniformExpectation
          (fun T : BooleanSlicePoint W r ↦
            (degreeInto G T.1 x : ℝ)) =
        (r : ℝ) / W.card * degreeInto G W x := by
    rw [Fintype.expect_eq_sum_div_card] at hslice
    simpa only [Erdos88.Concentration.uniformExpectation, degreeInto,
      Nat.cast_sum] using hslice
  calc
    Erdos88.Concentration.uniformExpectation
        (fun sigma : Equiv.Perm (Fin W.card) ↦
          (degreeInto G
            (signedSlicePositiveSupport W r 0 (by simpa using hr)
              (Finset.equivFin W).symm sigma) x : ℝ)) =
        Erdos88.Concentration.uniformExpectation
          (fun T : SignedSlicePoint W r 0 ↦
            (degreeInto G T.1.1 x : ℝ)) := by
      simpa only [signedSliceDecode] using hdecode
    _ = Erdos88.Concentration.uniformExpectation
          (fun T : BooleanSlicePoint W r ↦
            (degreeInto G T.1 x : ℝ)) := hequiv
    _ = (r : ℝ) / W.card * degreeInto G W x := hslice'
    _ = (r : ℝ) / W.card * d := by rw [hd]

/-- Cardinality-transported version of the exact prefix mean. -/
lemma uniformExpectation_degreeInto_cellPrefix
    (G : SimpleGraph V) (W x : Finset V) (n r d : ℕ)
    (hWcard : W.card = n) (hr : r ≤ n) (hW : W.Nonempty)
    (hd : degreeInto G W x = d) :
    Erdos88.Concentration.uniformExpectation
        (fun sigma : Equiv.Perm (Fin n) ↦
          (degreeInto G (cellPrefix W n hWcard sigma r hr) x : ℝ)) =
      (r : ℝ) / n * d := by
  subst n
  have hmean := uniformExpectation_degreeInto_prefix G W x r d hr hW hd
  convert hmean using 1
  apply congrArg Erdos88.Concentration.uniformExpectation
  funext sigma
  congr 2
  ext v
  simp [cellPrefix, signedSlicePositiveSupport, decodedCoordinateEmbedding]

/-- The common deterministic center for all matching cells. -/
def expectedDegree {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b : ℝ}
    (S : StructuralWitness G scale nW ell K alpha aDisc aDiv b)
    (i : ℕ) : ℝ :=
  ((nW - i : ℕ) : ℝ) / nW * S.dMinus +
    (i : ℝ) / nW * S.dPlus

/-- Splitting a sampled state into its two disjoint prefixes also splits
its multiset degree. -/
lemma degreeInto_sampledOrderings_state {G : SimpleGraph V}
    {scale nW ell K : ℕ} {alpha aDisc aDiv b : ℝ}
    (S : StructuralWitness G scale nW ell K alpha aDisc aDiv b)
    (sigma : OrderingSampler S) (i : ℕ) (hi : i ≤ nW)
    (x : Finset V) :
    degreeInto G ((sampledOrderings S sigma).state i) x =
      degreeInto G (sampledMinusPrefix S sigma i hi) x +
        degreeInto G (sampledPlusPrefix S sigma i hi) x := by
  rw [sampledOrderings_state_eq_prefix_union S sigma i hi]
  apply degreeInto_union_of_disjoint
  exact S.disjoint_Wminus_Wplus.mono
    (sampledMinusPrefix_subset S sigma i hi)
    (sampledPlusPrefix_subset S sigma i hi)

def orderingSamplerEquivProd {G : SimpleGraph V}
    {scale nW ell K : ℕ} {alpha aDisc aDiv b : ℝ}
    (S : StructuralWitness G scale nW ell K alpha aDisc aDiv b) :
    OrderingSampler S ≃
      Equiv.Perm (Fin nW) × Equiv.Perm (Fin nW) where
  toFun sigma := (sigma 0, sigma 1)
  invFun p := Fin.cases p.1 (fun _ ↦ p.2)
  left_inv sigma := by
    funext k
    fin_cases k <;> rfl
  right_inv p := rfl

lemma uniformExpectation_sampler_zero {G : SimpleGraph V}
    {scale nW ell K : ℕ} {alpha aDisc aDiv b : ℝ}
    (S : StructuralWitness G scale nW ell K alpha aDisc aDiv b)
    (f : Equiv.Perm (Fin nW) → ℝ) :
    Erdos88.Concentration.uniformExpectation
        (fun sigma : OrderingSampler S ↦ f (sigma 0)) =
      Erdos88.Concentration.uniformExpectation f := by
  unfold Erdos88.Concentration.uniformExpectation
  rw [Fintype.card_congr (orderingSamplerEquivProd S)]
  have hnum : (∑ sigma : OrderingSampler S, f (sigma 0)) =
      ∑ p : Equiv.Perm (Fin nW) × Equiv.Perm (Fin nW), f p.1 := by
    change (∑ sigma : OrderingSampler S,
      f ((orderingSamplerEquivProd S sigma).1)) =
        ∑ p : Equiv.Perm (Fin nW) × Equiv.Perm (Fin nW), f p.1
    exact (orderingSamplerEquivProd S).sum_comp
      (fun p : Equiv.Perm (Fin nW) × Equiv.Perm (Fin nW) ↦ f p.1)
  rw [hnum, Fintype.sum_prod_type, Fintype.card_prod]
  have hcard : (Fintype.card (Equiv.Perm (Fin nW)) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (Equiv.Perm (Fin nW)) ≠ 0)
  simp only [Finset.sum_const, nsmul_eq_mul]
  field_simp [hcard]
  simp only [Finset.card_univ]
  push_cast
  rw [← Finset.mul_sum]
  ring

lemma uniformExpectation_sampler_one {G : SimpleGraph V}
    {scale nW ell K : ℕ} {alpha aDisc aDiv b : ℝ}
    (S : StructuralWitness G scale nW ell K alpha aDisc aDiv b)
    (f : Equiv.Perm (Fin nW) → ℝ) :
    Erdos88.Concentration.uniformExpectation
        (fun sigma : OrderingSampler S ↦ f (sigma 1)) =
      Erdos88.Concentration.uniformExpectation f := by
  unfold Erdos88.Concentration.uniformExpectation
  rw [Fintype.card_congr (orderingSamplerEquivProd S)]
  have hnum : (∑ sigma : OrderingSampler S, f (sigma 1)) =
      ∑ p : Equiv.Perm (Fin nW) × Equiv.Perm (Fin nW), f p.2 := by
    change (∑ sigma : OrderingSampler S,
      f ((orderingSamplerEquivProd S sigma).2)) =
        ∑ p : Equiv.Perm (Fin nW) × Equiv.Perm (Fin nW), f p.2
    exact (orderingSamplerEquivProd S).sum_comp
      (fun p : Equiv.Perm (Fin nW) × Equiv.Perm (Fin nW) ↦ f p.2)
  rw [hnum, Fintype.sum_prod_type, Fintype.card_prod]
  have hcard : (Fintype.card (Equiv.Perm (Fin nW)) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (Equiv.Perm (Fin nW)) ≠ 0)
  simp only [Finset.sum_const, nsmul_eq_mul]
  field_simp [hcard]
  simp only [Finset.card_univ]
  push_cast
  ring

/-- Every matching cell has the same exact mean along the sampled path. -/
lemma uniformExpectation_degreeInto_sampled_state {G : SimpleGraph V}
    {scale nW ell K : ℕ} {alpha aDisc aDiv b : ℝ}
    (S : StructuralWitness G scale nW ell K alpha aDisc aDiv b)
    (hnW : 0 < nW) (i : ℕ) (hi : i ≤ nW)
    (x : Finset V) (hx : x ∈ S.matching) :
    Erdos88.Concentration.uniformExpectation
        (fun sigma : OrderingSampler S ↦
          (degreeInto G ((sampledOrderings S sigma).state i) x : ℝ)) =
      expectedDegree S i := by
  have hminusNonempty : S.Wminus.Nonempty := by
    rw [← Finset.card_pos, S.card_Wminus]
    exact hnW
  have hplusNonempty : S.Wplus.Nonempty := by
    rw [← Finset.card_pos, S.card_Wplus]
    exact hnW
  have hminus := uniformExpectation_degreeInto_cellPrefix G S.Wminus x
    nW (nW - i) S.dMinus S.card_Wminus (Nat.sub_le nW i)
      hminusNonempty (S.degree_Wminus x hx)
  have hplus := uniformExpectation_degreeInto_cellPrefix G S.Wplus x
    nW i S.dPlus S.card_Wplus hi hplusNonempty
      (S.degree_Wplus x hx)
  rw [show (fun sigma : OrderingSampler S ↦
      (degreeInto G ((sampledOrderings S sigma).state i) x : ℝ)) =
      (fun sigma ↦
        (degreeInto G (sampledMinusPrefix S sigma i hi) x : ℝ) +
          (degreeInto G (sampledPlusPrefix S sigma i hi) x : ℝ)) by
    funext sigma
    exact_mod_cast degreeInto_sampledOrderings_state S sigma i hi x]
  rw [Erdos88.Concentration.uniformExpectation_add]
  simp only [sampledMinusPrefix, sampledPlusPrefix]
  rw [uniformExpectation_sampler_zero S
      (fun sigma ↦ (degreeInto G
        (cellPrefix S.Wminus nW S.card_Wminus sigma (nW - i)
          (Nat.sub_le nW i)) x : ℝ)),
    uniformExpectation_sampler_one S
      (fun sigma ↦ (degreeInto G
        (cellPrefix S.Wplus nW S.card_Wplus sigma i hi) x : ℝ))]
  rw [hminus, hplus]
  rfl

/-! ## Simultaneous concentration -/

/-- One fixed time and one matching cell satisfy the product-permutation
tail estimate with bounded-difference constant `2*K`. -/
lemma degreeInto_sampled_state_tail {G : SimpleGraph V}
    {scale nW ell K : ℕ} {alpha aDisc aDiv b : ℝ}
    (S : StructuralWitness G scale nW ell K alpha aDisc aDiv b)
    (hnW : 0 < nW) (hK : 0 < K)
    (i : ℕ) (hi : i ≤ nW) (x : Finset V) (hx : x ∈ S.matching)
    (t : ℝ) (ht : 0 ≤ t) :
    Erdos88.Concentration.uniformProbability
        (fun sigma : OrderingSampler S ↦
          t ≤ |(degreeInto G ((sampledOrderings S sigma).state i) x : ℝ) -
            expectedDegree S i|) ≤
      2 * Real.exp (-t ^ 2 /
        (2 * (2 * nW) * (2 * K : ℕ) ^ 2)) := by
  let F : OrderingSampler S → ℝ := fun sigma ↦
    (degreeInto G ((sampledOrderings S sigma).state i) x : ℝ)
  have hprefix : PermutationProductPrefixDependent
      (N := sideCard S) (L := sideCard S) (fun _ ↦ le_rfl) F := by
    intro sigma tau hst
    have hEq : sigma = tau := by
      funext k
      apply Equiv.ext
      intro j
      simpa using hst k j
    exact congrArg F hEq
  have hswitch : PermutationProductSwitchLipschitz F (2 * K) := by
    intro sigma tau k p q hk hsame
    obtain ⟨a, c, hstate⟩ :=
      sampledOrderings_state_left_swap S sigma tau k p q hk hsame i hi
    have hdegree := abs_degreeInto_map_swap_sub_le G
      ((sampledOrderings S sigma).state i) x a c
    have hxcard : x.card ≤ K := (S.matching_uniform x hx).le.trans S.k_le
    have hcast : (2 : ℝ) * x.card ≤ 2 * K := by exact_mod_cast Nat.mul_le_mul_left 2 hxcard
    dsimp [F]
    rw [hstate]
    simpa [abs_sub_comm] using hdegree.trans hcast
  have hsum : ∑ k, sideCard S k = 2 * nW := by
    rw [Fin.sum_univ_two]
    simp [sideCard, two_mul]
  have htail := permutationProduct_two_sided_probability
    (N := sideCard S) (L := sideCard S) (fun _ ↦ le_rfl)
      F (2 * K) t (by rw [hsum]; omega)
      (by positivity) ht hprefix hswitch
  have hmean := uniformExpectation_degreeInto_sampled_state S hnW i hi x hx
  dsimp [F] at htail
  rw [hmean, hsum] at htail
  exact_mod_cast htail

/-- Exact finite form of the outer permutation-concentration step.

The displayed hypothesis is the complete finite union bound over all
`(time, matching-cell)` pairs.  It is the only numerical estimate needed
to obtain one pair of orderings controlling all of them simultaneously. -/
theorem exists_uniformDegreeControlledOrderings {G : SimpleGraph V}
    {scale nW ell K : ℕ} {alpha aDisc aDiv b : ℝ}
    (S : StructuralWitness G scale nW ell K alpha aDisc aDiv b)
    (hnW : 0 < nW) (hK : 0 < K) (t : ℝ) (ht : 0 ≤ t)
    (hunion : (((nW + 1) * S.matching.card : ℕ) : ℝ) *
      (2 * Real.exp (-t ^ 2 /
        (2 * (2 * nW) * (2 * K : ℕ) ^ 2))) < 1) :
    Nonempty (UniformDegreeControlledOrderings S t) := by
  classical
  let J := Fin (nW + 1) × {x // x ∈ S.matching}
  let prob : ℝ := 2 * Real.exp (-t ^ 2 /
    (2 * (2 * nW) * (2 * K : ℕ) ^ 2))
  let bad : J → Finset (OrderingSampler S) := fun j ↦
    Finset.univ.filter fun sigma ↦
      t ≤ |(degreeInto G ((sampledOrderings S sigma).state j.1) j.2.1 : ℝ) -
        expectedDegree S j.1|
  have hbad (j : J) :
      ((bad j).card : ℝ) ≤ prob * Fintype.card (OrderingSampler S) := by
    have htail := degreeInto_sampled_state_tail S hnW hK
      j.1 (by omega) j.2.1 j.2.2 t ht
    rw [Erdos88.Concentration.uniformProbability] at htail
    have hcardpos : (0 : ℝ) < Fintype.card (OrderingSampler S) := by
      exact_mod_cast Fintype.card_pos
    apply (div_le_iff₀ hcardpos).mp
    simpa [bad, prob] using htail
  let allBad : Finset (OrderingSampler S) := Finset.univ.biUnion bad
  have hallBad : ((allBad.card : ℕ) : ℝ) <
      Fintype.card (OrderingSampler S) := by
    calc
      ((allBad.card : ℕ) : ℝ) ≤ ∑ j : J, ((bad j).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _j : J, prob * Fintype.card (OrderingSampler S) := by
        apply Finset.sum_le_sum
        intro j _hj
        exact hbad j
      _ = (Fintype.card J : ℝ) * prob *
          Fintype.card (OrderingSampler S) := by simp; ring
      _ < Fintype.card (OrderingSampler S) := by
        have hsamp : (0 : ℝ) < Fintype.card (OrderingSampler S) := by
          exact_mod_cast Fintype.card_pos
        have hfactor : (Fintype.card J : ℝ) * prob < 1 := by
          simpa [J, prob, Fintype.card_coe] using hunion
        simpa [mul_assoc] using mul_lt_mul_of_pos_right hfactor hsamp
  have hallBadNat : allBad.card <
      (Finset.univ : Finset (OrderingSampler S)).card := by
    exact_mod_cast hallBad
  obtain ⟨sigma, _hsigma, hsigmaBad⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hallBadNat
  refine ⟨{
    toSwitchingOrderings := sampledOrderings S sigma
    expected := expectedDegree S
    degree_control := ?_ }⟩
  intro i hi x hx
  let j : J := (⟨i, by omega⟩, ⟨x, hx⟩)
  have hnot : sigma ∉ bad j := by
    intro h
    exact hsigmaBad (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, h⟩)
  exact (not_le.mp (by simpa [bad, j] using hnot)).le

/-! ## Deterministic consequences for downstream switching -/

@[simp] lemma UniformDegreeControlledOrderings.state_zero
    {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b error : ℝ}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    (Q : UniformDegreeControlledOrderings S error) :
    Q.toSwitchingOrderings.state 0 = S.Wminus :=
  Q.toSwitchingOrderings.state_zero

@[simp] lemma UniformDegreeControlledOrderings.state_last
    {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b error : ℝ}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    (Q : UniformDegreeControlledOrderings S error) :
    Q.toSwitchingOrderings.state nW = S.Wplus :=
  Q.toSwitchingOrderings.state_last

lemma UniformDegreeControlledOrderings.state_card
    {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b error : ℝ}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    (Q : UniformDegreeControlledOrderings S error) (i : ℕ) :
    (Q.toSwitchingOrderings.state i).card = nW :=
  Q.toSwitchingOrderings.state_card S.disjoint_Wminus_Wplus i

lemma UniformDegreeControlledOrderings.disjoint_state_U0
    {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b error : ℝ}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    (Q : UniformDegreeControlledOrderings S error) (i : ℕ) :
    Disjoint (Q.toSwitchingOrderings.state i) S.U0 := by
  apply Q.toSwitchingOrderings.disjoint_state_of_disjoint_union
  exact Finset.disjoint_union_left.mpr
    ⟨S.disjoint_Wminus_U0, S.disjoint_Wplus_U0⟩

/-- Uniform control around one common center forces every pair of matching
cells to have degrees differing by at most twice the error. -/
lemma UniformDegreeControlledOrderings.degree_spread
    {G : SimpleGraph V} {scale nW ell K : ℕ}
    {alpha aDisc aDiv b error : ℝ}
    {S : StructuralWitness G scale nW ell K alpha aDisc aDiv b}
    (Q : UniformDegreeControlledOrderings S error)
    (i : ℕ) (hi : i ≤ nW) (x y : Finset V)
    (hx : x ∈ S.matching) (hy : y ∈ S.matching) :
    |(degreeInto G (Q.toSwitchingOrderings.state i) x : ℝ) -
        degreeInto G (Q.toSwitchingOrderings.state i) y| ≤ 2 * error := by
  have hxControl := Q.degree_control i hi x hx
  have hyControl := Q.degree_control i hi y hy
  calc
    |(degreeInto G (Q.toSwitchingOrderings.state i) x : ℝ) -
        degreeInto G (Q.toSwitchingOrderings.state i) y| =
        |((degreeInto G (Q.toSwitchingOrderings.state i) x : ℝ) - Q.expected i) +
          (Q.expected i -
            degreeInto G (Q.toSwitchingOrderings.state i) y)| := by ring_nf
    _ ≤ |(degreeInto G (Q.toSwitchingOrderings.state i) x : ℝ) - Q.expected i| +
        |Q.expected i -
          degreeInto G (Q.toSwitchingOrderings.state i) y| := abs_add_le ..
    _ ≤ error + error := by
      gcongr
      simpa [abs_sub_comm] using hyControl
    _ = 2 * error := by ring


end

end StructuralOuterConcentration
end Erdos636
