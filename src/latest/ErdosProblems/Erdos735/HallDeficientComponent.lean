/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos735.HallFailureExtraction

/-!
# The deficient path component behind a failed Hall inequality

For a finite bipartite graph in which evil degrees lie in `[1,2]` and helper
degrees are at most two, choose a Hall-deficient evil set of least
cardinality.  It has exactly one more evil than helper, every helper has two
neighbors in the set, and exactly two evils have degree one.  These are the
two endpoints of the alternating component used in Stage 4.
-/

open Classical
noncomputable section

namespace Erdos735.ABKPR.HelpingGraph

universe uH uE

variable {Help : Type uH} {Evil : Type uE}
variable [Fintype Help] [Fintype Evil]
variable [DecidableEq Help] [DecidableEq Evil]
variable (G : HelpingGraph Help Evil)

local instance : DecidableRel G.Adj := G.adjDecidable

def neighborsOf (S : Finset Evil) : Finset Help :=
  Finset.univ.filter fun h ↦ ∃ e ∈ S, G.Adj e h

def evilNeighborsIn (S : Finset Evil) (h : Help) : Finset Evil :=
  S.filter fun e ↦ G.Adj e h

def HallDeficient (S : Finset Evil) : Prop :=
  (G.neighborsOf S).card < S.card

/-- Two evil vertices are joined by one alternating evil--helper--evil
step. -/
def LinkedEvil (e e' : Evil) : Prop :=
  ∃ h : Help, G.Adj e h ∧ G.Adj e' h

instance hallDeficientDecidable (S : Finset Evil) : Decidable (G.HallDeficient S) :=
  inferInstance

@[simp] theorem mem_neighborsOf {S : Finset Evil} {h : Help} :
    h ∈ G.neighborsOf S ↔ ∃ e ∈ S, G.Adj e h := by
  simp [neighborsOf]

@[simp] theorem mem_evilNeighborsIn {S : Finset Evil} {h : Help} {e : Evil} :
    e ∈ G.evilNeighborsIn S h ↔ e ∈ S ∧ G.Adj e h := by
  simp [evilNeighborsIn]

theorem neighborsOf_mono {S T : Finset Evil} (hST : S ⊆ T) :
    G.neighborsOf S ⊆ G.neighborsOf T := by
  intro h hh
  obtain ⟨e, heS, heh⟩ := G.mem_neighborsOf.mp hh
  exact G.mem_neighborsOf.mpr ⟨e, hST heS, heh⟩

theorem exists_minimal_hallDeficient
    (hHall : ¬ G.NoEvilEvilPath) :
    ∃ S : Finset Evil, G.HallDeficient S ∧
      ∀ T : Finset Evil, G.HallDeficient T → S.card ≤ T.card := by
  simp only [NoEvilEvilPath, not_forall] at hHall
  obtain ⟨S₀, hS₀⟩ := hHall
  have hdef₀ : G.HallDeficient S₀ := Nat.lt_of_not_ge hS₀
  let V : Finset (Finset Evil) :=
    Finset.univ.filter fun S ↦ G.HallDeficient S
  have hV : V.Nonempty := ⟨S₀, Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, hdef₀⟩⟩
  obtain ⟨S, hSV, hmin⟩ := V.exists_min_image Finset.card hV
  refine ⟨S, (Finset.mem_filter.mp hSV).2, ?_⟩
  intro T hT
  exact hmin T (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hT⟩)

theorem hallDeficient_nonempty {S : Finset Evil}
    (hS : G.HallDeficient S) : S.Nonempty := by
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty.mp h] at hS
  simp [HallDeficient, neighborsOf] at hS

theorem neighborsOf_erase_eq_of_minimal
    {S : Finset Evil} (hS : G.HallDeficient S)
    (hmin : ∀ T : Finset Evil, G.HallDeficient T → S.card ≤ T.card)
    {e : Evil} (he : e ∈ S) :
    G.neighborsOf (S.erase e) = G.neighborsOf S := by
  have hnot : ¬ G.HallDeficient (S.erase e) := by
    intro hdef
    have hle := hmin (S.erase e) hdef
    have hpos : 0 < S.card := Finset.card_pos.mpr ⟨e, he⟩
    rw [Finset.card_erase_of_mem he] at hle
    omega
  have herase_le : (S.erase e).card ≤ (G.neighborsOf (S.erase e)).card := by
    change ¬ (G.neighborsOf (S.erase e)).card < (S.erase e).card at hnot
    exact Nat.le_of_not_gt hnot
  have hsub : G.neighborsOf (S.erase e) ⊆ G.neighborsOf S :=
    G.neighborsOf_mono (Finset.erase_subset _ _)
  have hcard_le := Finset.card_le_card hsub
  have hupper : (G.neighborsOf S).card ≤ S.card - 1 := by
    exact Nat.le_pred_of_lt hS
  have herase : (S.erase e).card = S.card - 1 :=
    Finset.card_erase_of_mem he
  have hcard : (G.neighborsOf (S.erase e)).card =
      (G.neighborsOf S).card := by
    omega
  exact Finset.eq_of_subset_of_card_le hsub (by omega)

theorem neighborsOf_card_add_one_eq_of_minimal
    {S : Finset Evil} (hS : G.HallDeficient S)
    (hmin : ∀ T : Finset Evil, G.HallDeficient T → S.card ≤ T.card) :
    (G.neighborsOf S).card + 1 = S.card := by
  obtain ⟨e, he⟩ := G.hallDeficient_nonempty hS
  have heq := G.neighborsOf_erase_eq_of_minimal hS hmin he
  have hnot : ¬ G.HallDeficient (S.erase e) := by
    intro hdef
    have hle := hmin (S.erase e) hdef
    have hpos : 0 < S.card := Finset.card_pos.mpr ⟨e, he⟩
    rw [Finset.card_erase_of_mem he] at hle
    omega
  have hlower : S.card - 1 ≤ (G.neighborsOf S).card := by
    have hnot' : ¬ (G.neighborsOf (S.erase e)).card < (S.erase e).card := hnot
    have := Nat.le_of_not_gt hnot'
    rw [Finset.card_erase_of_mem he, heq] at this
    exact this
  change (G.neighborsOf S).card < S.card at hS
  have hpos : 0 < S.card := Finset.card_pos.mpr ⟨e, he⟩
  omega

theorem linkedEvil_symmetric : Symmetric G.LinkedEvil := by
  intro e e' h
  obtain ⟨a, he, he'⟩ := h
  exact ⟨a, he', he⟩

/-- A least-cardinality Hall-deficient set is one alternating connected
component on its evil vertices. -/
theorem minimal_hallDeficient_connected
    {S : Finset Evil} (hS : G.HallDeficient S)
    (hmin : ∀ T : Finset Evil, G.HallDeficient T → S.card ≤ T.card)
    {root : Evil} (hroot : root ∈ S) :
    ∀ e ∈ S, Relation.ReflTransGen G.LinkedEvil root e := by
  let R : Finset Evil := S.filter fun e ↦
    Relation.ReflTransGen G.LinkedEvil root e
  have hRsub : R ⊆ S := Finset.filter_subset _ _
  have hrootR : root ∈ R := by
    exact Finset.mem_filter.mpr ⟨hroot, Relation.ReflTransGen.refl⟩
  have hclosed {e e' : Evil} (heR : e ∈ R) (he'S : e' ∈ S)
      (hlink : G.LinkedEvil e e') : e' ∈ R := by
    apply Finset.mem_filter.mpr
    exact ⟨he'S, Relation.ReflTransGen.tail (Finset.mem_filter.mp heR).2 hlink⟩
  have hReq : R = S := by
    by_contra hne
    let U : Finset Evil := S \ R
    have hRssub : R ⊂ S := Finset.ssubset_iff_subset_ne.mpr ⟨hRsub, hne⟩
    have hRcard : R.card < S.card := Finset.card_lt_card hRssub
    have hUsub : U ⊆ S := Finset.sdiff_subset
    have hrootU : root ∉ U := by simp [U, hrootR]
    have hUne : U ≠ S := by
      intro h
      exact hrootU (h ▸ hroot)
    have hUssub : U ⊂ S := Finset.ssubset_iff_subset_ne.mpr ⟨hUsub, hUne⟩
    have hUcard : U.card < S.card := Finset.card_lt_card hUssub
    have hnR : ¬ G.HallDeficient R := by
      intro hd
      exact (not_le_of_gt hRcard) (hmin R hd)
    have hnU : ¬ G.HallDeficient U := by
      intro hd
      exact (not_le_of_gt hUcard) (hmin U hd)
    have hRle : R.card ≤ (G.neighborsOf R).card := by
      change ¬ (G.neighborsOf R).card < R.card at hnR
      exact Nat.le_of_not_gt hnR
    have hUle : U.card ≤ (G.neighborsOf U).card := by
      change ¬ (G.neighborsOf U).card < U.card at hnU
      exact Nat.le_of_not_gt hnU
    have hNdisj : Disjoint (G.neighborsOf R) (G.neighborsOf U) := by
      rw [Finset.disjoint_left]
      intro h hhR hhU
      obtain ⟨e, heR, heh⟩ := G.mem_neighborsOf.mp hhR
      obtain ⟨e', he'U, he'h⟩ := G.mem_neighborsOf.mp hhU
      have he'S : e' ∈ S := (Finset.mem_sdiff.mp he'U).1
      have he'R := hclosed heR he'S ⟨h, heh, he'h⟩
      exact (Finset.mem_sdiff.mp he'U).2 he'R
    have hNunion : G.neighborsOf R ∪ G.neighborsOf U = G.neighborsOf S := by
      ext h
      simp only [Finset.mem_union, G.mem_neighborsOf]
      constructor
      · rintro (⟨e, heR, heh⟩ | ⟨e, heU, heh⟩)
        · exact ⟨e, hRsub heR, heh⟩
        · exact ⟨e, hUsub heU, heh⟩
      · rintro ⟨e, heS, heh⟩
        by_cases heR : e ∈ R
        · exact Or.inl ⟨e, heR, heh⟩
        · exact Or.inr ⟨e, Finset.mem_sdiff.mpr ⟨heS, heR⟩, heh⟩
    have hScard : U.card + R.card = S.card := by
      simpa [U] using Finset.card_sdiff_add_card_eq_card hRsub
    have hNcard : (G.neighborsOf R).card + (G.neighborsOf U).card =
        (G.neighborsOf S).card := by
      rw [← hNunion, Finset.card_union_of_disjoint hNdisj]
    change (G.neighborsOf S).card < S.card at hS
    omega
  intro e heS
  have heR : e ∈ R := hReq.symm ▸ heS
  exact (Finset.mem_filter.mp heR).2

theorem evilNeighborsIn_card_eq_two_of_minimal
    {S : Finset Evil} (hS : G.HallDeficient S)
    (hmin : ∀ T : Finset Evil, G.HallDeficient T → S.card ≤ T.card)
    {h : Help} (hh : h ∈ G.neighborsOf S) :
    (G.evilNeighborsIn S h).card = 2 := by
  obtain ⟨e, heS, heh⟩ := G.mem_neighborsOf.mp hh
  have herase := G.neighborsOf_erase_eq_of_minimal hS hmin heS
  have hh' : h ∈ G.neighborsOf (S.erase e) := by
    rw [herase]
    exact hh
  obtain ⟨e', he'S, he'h⟩ := G.mem_neighborsOf.mp hh'
  have he'ne : e' ≠ e := (Finset.mem_erase.mp he'S).1
  have he'mem : e' ∈ S := (Finset.mem_erase.mp he'S).2
  have hpair : ({e, e'} : Finset Evil) ⊆ G.evilNeighborsIn S h := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact G.mem_evilNeighborsIn.mpr ⟨heS, heh⟩
    · exact G.mem_evilNeighborsIn.mpr ⟨he'mem, he'h⟩
  have hlower := Finset.card_le_card hpair
  have hpaircard : ({e, e'} : Finset Evil).card = 2 := by
    simp [he'ne.symm]
  have hsub : G.evilNeighborsIn S h ⊆ G.helpingNeighbors h := by
    intro x hx
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (G.mem_evilNeighborsIn.mp hx).2⟩
  have hupper := (Finset.card_le_card hsub).trans (G.helping_degree_le_two h)
  omega

theorem sum_evilDegrees_eq_two_mul_neighborsOf_card_of_minimal
    {S : Finset Evil} (hS : G.HallDeficient S)
    (hmin : ∀ T : Finset Evil, G.HallDeficient T → S.card ≤ T.card) :
    ∑ e ∈ S, (G.evilNeighbors e).card = 2 * (G.neighborsOf S).card := by
  calc
    ∑ e ∈ S, (G.evilNeighbors e).card =
        ∑ e ∈ S, ∑ h : Help, if G.Adj e h then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro e he
      simp [evilNeighbors]
    _ = ∑ h : Help, ∑ e ∈ S, if G.Adj e h then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ h : Help, (G.evilNeighborsIn S h).card := by
      apply Finset.sum_congr rfl
      intro h hh
      simp [evilNeighborsIn]
    _ = ∑ h ∈ G.neighborsOf S, (G.evilNeighborsIn S h).card := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro h hhU hhN
      have hempty : G.evilNeighborsIn S h = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro e he
        exact hhN (G.mem_neighborsOf.mpr
          ⟨e, (G.mem_evilNeighborsIn.mp he).1,
            (G.mem_evilNeighborsIn.mp he).2⟩)
      simp [hempty]
    _ = ∑ _h ∈ G.neighborsOf S, 2 := by
      apply Finset.sum_congr rfl
      intro h hh
      exact G.evilNeighborsIn_card_eq_two_of_minimal hS hmin hh
    _ = 2 * (G.neighborsOf S).card := by simp [Nat.mul_comm]

def degreeOneEvils (S : Finset Evil) : Finset Evil :=
  S.filter fun e ↦ (G.evilNeighbors e).card = 1

theorem degreeOneEvils_card_eq_two_of_minimal
    {S : Finset Evil} (hS : G.HallDeficient S)
    (hmin : ∀ T : Finset Evil, G.HallDeficient T → S.card ≤ T.card) :
    (G.degreeOneEvils S).card = 2 := by
  let O := G.degreeOneEvils S
  let T := S.filter (fun e ↦ (G.evilNeighbors e).card ≠ 1)
  have hdeg (e : Evil) (he : e ∈ S) :
      (G.evilNeighbors e).card = 1 ∨ (G.evilNeighbors e).card = 2 := by
    have hlo := G.evil_degree_one_le e
    have hhi := G.evil_degree_le_two e
    omega
  have hsumO : ∑ e ∈ O, (G.evilNeighbors e).card = O.card := by
    calc
      ∑ e ∈ O, (G.evilNeighbors e).card = ∑ _e ∈ O, 1 := by
        apply Finset.sum_congr rfl
        intro e he
        exact (Finset.mem_filter.mp he).2
      _ = O.card := by simp
  have hsumN : ∑ e ∈ T, (G.evilNeighbors e).card = 2 * T.card := by
    calc
      ∑ e ∈ T,
          (G.evilNeighbors e).card =
          ∑ _e ∈ T, 2 := by
        apply Finset.sum_congr rfl
        intro e he
        have he' : e ∈ S.filter (fun e ↦ (G.evilNeighbors e).card ≠ 1) := by
          simpa [T] using he
        exact (hdeg e (Finset.mem_filter.mp he').1).resolve_left
          (Finset.mem_filter.mp he').2
      _ = 2 * T.card := by
        simp [Nat.mul_comm]
  have hsplit := Finset.sum_filter_add_sum_filter_not S
    (fun e ↦ (G.evilNeighbors e).card = 1)
    (fun e ↦ (G.evilNeighbors e).card)
  have hcardSplit := Finset.card_filter_add_card_filter_not
    (s := S) (p := fun e ↦ (G.evilNeighbors e).card = 1)
  have hdegreeSum := G.sum_evilDegrees_eq_two_mul_neighborsOf_card_of_minimal hS hmin
  have hneighbor := G.neighborsOf_card_add_one_eq_of_minimal hS hmin
  have hsplit' :
      (∑ e ∈ O, (G.evilNeighbors e).card) +
          ∑ e ∈ T, (G.evilNeighbors e).card =
        ∑ e ∈ S, (G.evilNeighbors e).card := by
    simpa only [O, T, degreeOneEvils] using hsplit
  have hcardSplit' : O.card + T.card = S.card := by
    simpa only [O, T, degreeOneEvils] using hcardSplit
  change O.card = 2
  omega

/-- A canonical minimal deficient set and its two evil endpoints. -/
structure DeficientPathComponent where
  evils : Finset Evil
  hallDeficient : G.HallDeficient evils
  minimalCard : ∀ T : Finset Evil, G.HallDeficient T → evils.card ≤ T.card
  helper_card_add_one : (G.neighborsOf evils).card + 1 = evils.card
  helper_two_neighbors : ∀ h ∈ G.neighborsOf evils,
    (G.evilNeighborsIn evils h).card = 2
  endpoint : Fin 2 → Evil
  endpoint_injective : Function.Injective endpoint
  endpoint_mem : ∀ k, endpoint k ∈ evils
  endpoint_degree_one : ∀ k, (G.evilNeighbors (endpoint k)).card = 1
  every_degree_one_is_endpoint : ∀ e ∈ evils,
    (G.evilNeighbors e).card = 1 → ∃ k, endpoint k = e
  evils_reachable_from_first : ∀ e ∈ evils,
    Relation.ReflTransGen G.LinkedEvil (endpoint 0) e

theorem deficientPathComponent_nonempty
    (hHall : ¬ G.NoEvilEvilPath) : Nonempty (DeficientPathComponent G) := by
  obtain ⟨S, hS, hmin⟩ := G.exists_minimal_hallDeficient hHall
  have htwo := G.degreeOneEvils_card_eq_two_of_minimal hS hmin
  let E : Fin 2 ≃ G.degreeOneEvils S :=
    (Fintype.equivFinOfCardEq (by
      simpa only [Fintype.card_coe] using htwo)).symm
  exact ⟨
    { evils := S
      hallDeficient := hS
      minimalCard := hmin
      helper_card_add_one := G.neighborsOf_card_add_one_eq_of_minimal hS hmin
      helper_two_neighbors := fun h hh ↦
        G.evilNeighborsIn_card_eq_two_of_minimal hS hmin (h := h) hh
      endpoint := fun k ↦ (E k).1
      endpoint_injective := fun i j hij ↦ E.injective (Subtype.ext hij)
      endpoint_mem := fun k ↦ (Finset.mem_filter.mp (E k).2).1
      endpoint_degree_one := fun k ↦ (Finset.mem_filter.mp (E k).2).2
      every_degree_one_is_endpoint := by
        intro e heS heone
        let x : G.degreeOneEvils S :=
          ⟨e, Finset.mem_filter.mpr ⟨heS, heone⟩⟩
        exact ⟨E.symm x, congrArg Subtype.val (E.apply_symm_apply x)⟩
      evils_reachable_from_first := fun e he ↦
        G.minimal_hallDeficient_connected hS hmin
          ((Finset.mem_filter.mp (E 0).2).1) e he }⟩

noncomputable def deficientPathComponent
    (hHall : ¬ G.NoEvilEvilPath) : DeficientPathComponent G :=
  Classical.choice (G.deficientPathComponent_nonempty hHall)

end Erdos735.ABKPR.HelpingGraph
