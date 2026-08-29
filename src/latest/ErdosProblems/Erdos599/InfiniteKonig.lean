/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.Stationary
import ErdosProblems.Erdos599.FamilyTools
import ErdosProblems.Erdos599.PathTools

/-!
# Infinite Kőnig selection lemmas

This file isolates the set-family selection input used in the popular-vertex
argument of Aharoni--Berger.  In particular, the theorem
`large_family_exists_sdr_covering_member` is the corollary on page 5 of
Aharoni's 1984 proof of Kőnig duality: a sufficiently large family of subsets
of a fixed set has a partial system of distinct representatives whose range
contains one whole member of the family.

The proof below is self-contained.  It chooses an inclusion-maximal partial
system of distinct representatives by Zorn's lemma; every unrepresented index
then has all its candidates already in the range.
-/

noncomputable section

open Cardinal Function Order Set

namespace Erdos599
namespace InfiniteKonig

universe u v

variable {C D : Type u}

open DirectedPath

/-! ## Stationary transversals -/

/-- Aharoni--Berger Lemma 8.5.  If nonstationary subsets of a regular
uncountable cardinal have stationary union, they support a choice function
whose range is stationary. -/
theorem stationary_range_choice {κ : Cardinal.{u}}
    (hunc : ℵ₀ < κ) (hreg : κ.IsRegular)
    {ι : Type v} (Ξ : ι → Set (Stationary.Below κ))
    (hne : ∀ i, (Ξ i).Nonempty)
    (hnon : ∀ i, ¬ Stationary.IsStationaryBelow κ (Ξ i))
    (hunion : Stationary.IsStationaryBelow κ (⋃ i, Ξ i)) :
    ∃ g : ι → Stationary.Below κ,
      (∀ i, g i ∈ Ξ i) ∧
        Stationary.IsStationaryBelow κ (Set.range g) := by
  classical
  open Stationary in
    let S : Set (Below κ) := ⋃ i, Ξ i
    have hS : IsStationaryBelow κ S := hunion
    obtain ⟨a0, ha0S⟩ := hS.nonempty
    obtain ⟨i0, _⟩ := Set.mem_iUnion.mp ha0S
    let owner : Below κ → ι := fun a ↦
      if ha : a ∈ S then Classical.choose (Set.mem_iUnion.mp ha) else i0
    have owner_mem {a : Below κ} (ha : a ∈ S) : a ∈ Ξ (owner a) := by
      dsimp only [owner]
      rw [dif_pos ha]
      exact Classical.choose_spec (Set.mem_iUnion.mp ha)
    let fiber : ι → Set (Below κ) := fun i ↦ {a | a ∈ S ∧ owner a = i}
    have fiber_nonempty {a : Below κ} (ha : a ∈ S) :
        (fiber (owner a)).Nonempty :=
      ⟨a, ha, rfl⟩
    let fallback : ι → Below κ := fun i ↦ Classical.choose (hne i)
    let g : ι → Below κ := fun i ↦
      if hi : (fiber i).Nonempty then wellFounded_lt.min (fiber i) hi
      else fallback i
    have g_mem_fiber (i : ι) (hi : (fiber i).Nonempty) : g i ∈ fiber i := by
      dsimp only [g]
      rw [dif_pos hi]
      exact wellFounded_lt.min_mem (fiber i) hi
    have hgΞ : ∀ i, g i ∈ Ξ i := by
      intro i
      by_cases hi : (fiber i).Nonempty
      · have hgi := g_mem_fiber i hi
        have hmem : g i ∈ Ξ (owner (g i)) := owner_mem hgi.1
        simpa only [hgi.2] using hmem
      · dsimp only [g]
        rw [dif_neg hi]
        exact Classical.choose_spec (hne i)
    have g_owner_le {a : Below κ} (ha : a ∈ S) : g (owner a) ≤ a := by
      have hfa : a ∈ fiber (owner a) := ⟨ha, rfl⟩
      have hfne : (fiber (owner a)).Nonempty := ⟨a, hfa⟩
      dsimp only [g]
      rw [dif_pos hfne]
      exact WellFounded.min_le wellFounded_lt hfa
    let R : Set (Below κ) := {a | a ∈ S ∧ g (owner a) = a}
    have hRstat : IsStationaryBelow κ R := by
      by_contra hR
      let T : Set (Below κ) := S \ R
      have hTstat : IsStationaryBelow κ T := by
        by_contra hT
        obtain ⟨CR, hCRclub, hRCR⟩ := not_isStationary_iff.mp hR
        obtain ⟨CT, hCTclub, hTCT⟩ := not_isStationary_iff.mp hT
        have hcof : Order.cof (Below κ) ≠ ℵ₀ := by
          rw [cof_below_eq_lift hreg]
          rw [← Cardinal.lift_aleph0.{u + 1, u}]
          exact (Cardinal.lift_lt.mpr hunc).ne'
        obtain ⟨a, haS, haC⟩ := hS (hCRclub.inter hcof hCTclub)
        by_cases haeq : g (owner a) = a
        · exact Set.disjoint_left.mp hRCR ⟨haS, haeq⟩ haC.1
        · exact Set.disjoint_left.mp hTCT
            ⟨haS, fun haR ↦ haeq haR.2⟩ haC.2
      have hregressive : IsRegressiveOn T (fun a ↦ g (owner a)) := by
        intro a haT
        have hle : g (owner a) ≤ a := g_owner_le haT.1
        have hne' : g (owner a) ≠ a := by
          intro heq
          exact haT.2 ⟨haT.1, heq⟩
        exact lt_of_le_of_ne hle hne'
      obtain ⟨b, hbstat⟩ :=
        pressingDown hunc hreg hTstat hregressive
      have hsub : T ∩ {a | g (owner a) = b} ⊆ Ξ (owner b) := by
        intro a ha
        have hgf := g_mem_fiber (owner a) (fiber_nonempty ha.1.1)
        rw [ha.2] at hgf
        have hamem : a ∈ Ξ (owner a) := owner_mem ha.1.1
        simpa only [hgf.2] using hamem
      exact hnon (owner b) (hbstat.mono hsub)
    refine ⟨g, hgΞ, hRstat.mono ?_⟩
    intro a haR
    exact ⟨owner a, haR.2⟩

/-! ## The finite-support congestion dichotomy -/

/-- An inclusion-maximal pairwise-disjoint subfamily exists in every family
of sets.  This is the Zorn step in Aharoni's Lemma 2.4. -/
theorem exists_maximal_pairwiseDisjoint {P V : Type u}
    (paths : Set P) (support : P → Set V) :
    ∃ M : Set P,
      Maximal (fun N ↦ N ⊆ paths ∧ N.PairwiseDisjoint support) M := by
  apply zorn_subset
  intro c hc hchain
  refine ⟨⋃₀ c, ?_, ?_⟩
  · constructor
    · intro p hp
      obtain ⟨M, hMc, hpM⟩ := Set.mem_sUnion.1 hp
      exact (hc hMc).1 hpM
    · rintro p hp q hq hpq
      obtain ⟨M, hMc, hpM⟩ := Set.mem_sUnion.1 hp
      obtain ⟨N, hNc, hqN⟩ := Set.mem_sUnion.1 hq
      rcases hchain.total hMc hNc with hMN | hNM
      · exact (hc hNc).2 (hMN hpM) hqN hpq
      · exact (hc hMc).2 hpM (hNM hqN) hpq
  · intro M hMc
    exact Set.subset_sUnion_of_mem hMc

/-- Aharoni's Lemma 2.4 in the form used by Lemma 2.5.  At a regular
cardinal `ρ`, a family of at least `ρ` nonempty finite supports either contains
`ρ` pairwise-disjoint members, or one point belongs to at least `ρ` members.

The conclusion uses the actual subtypes, so it is directly usable for cardinal
bookkeeping without selecting enumerations. -/
theorem large_pairwiseDisjoint_or_highDegree
    {P V : Type u} {ρ : Cardinal.{u}}
    (hρ : ρ.IsRegular) (paths : Set P) (support : P → Set V)
    (hsupport_finite : ∀ p, (support p).Finite)
    (hsupport_nonempty : ∀ p ∈ paths, (support p).Nonempty)
    (hlarge : ρ ≤ #paths) :
    (∃ M : Set P, M ⊆ paths ∧ M.PairwiseDisjoint support ∧ ρ ≤ #M) ∨
      ∃ y : V, ρ ≤ #{p : paths | y ∈ support p.1} := by
  classical
  obtain ⟨M, hM⟩ := exists_maximal_pairwiseDisjoint paths support
  by_cases hMlarge : ρ ≤ #M
  · exact Or.inl ⟨M, hM.prop.1, hM.prop.2, hMlarge⟩
  · right
    have hMsmall : #M < ρ := lt_of_not_ge hMlarge
    let U : Set V := ⋃ p ∈ M, support p
    have hUsmall : #U < ρ := by
      dsimp only [U]
      exact FamilyTools.mk_biUnion_lt_of_finite_of_isRegular hρ hMsmall
        (fun p _ ↦ hsupport_finite p)
    have every_meets : ∀ p ∈ paths, (support p ∩ U).Nonempty := by
      intro p hp
      by_contra hdisj'
      have hdisjU : Disjoint (support p) U :=
        Set.disjoint_iff_inter_eq_empty.2
          (Set.not_nonempty_iff_eq_empty.mp hdisj')
      by_cases hpM : p ∈ M
      · obtain ⟨x, hx⟩ := hsupport_nonempty p hp
        apply Set.disjoint_left.1 hdisjU hx
        exact Set.mem_iUnion.2 ⟨p, Set.mem_iUnion.2 ⟨hpM, hx⟩⟩
      · have hadd : insert p M ⊆ paths ∧
            (insert p M).PairwiseDisjoint support := by
          constructor
          · exact Set.insert_subset hp hM.prop.1
          · rintro a ha b hb hab
            rcases ha with rfl | ha
            · rcases hb with rfl | hb
              · exact (hab rfl).elim
              · apply Set.disjoint_left.2
                intro x hxp hxb
                exact Set.disjoint_left.1 hdisjU hxp
                  (Set.mem_iUnion.2 ⟨b, Set.mem_iUnion.2 ⟨hb, hxb⟩⟩)
            · rcases hb with rfl | hb
              · apply Set.disjoint_left.2
                intro x hxa hxp
                exact Set.disjoint_left.1 hdisjU hxp
                  (Set.mem_iUnion.2 ⟨a, Set.mem_iUnion.2 ⟨ha, hxa⟩⟩)
              · exact hM.prop.2 ha hb hab
        have hle : insert p M ⊆ M :=
          hM.2 hadd (Set.subset_insert p M)
        exact hpM (hle (Set.mem_insert p M))
    by_contra hdegree
    push Not at hdegree
    let incident : V → Set paths := fun y ↦ {p | y ∈ support p.1}
    have hincident : ∀ y ∈ U, #(incident y) < ρ := by
      intro y _
      exact hdegree y
    have hunion_small : #(⋃ y ∈ U, incident y) < ρ :=
      FamilyTools.mk_biUnion_lt_of_isRegular hρ hUsmall hincident
    have hsubset : Set.univ ⊆ ⋃ y ∈ U, incident y := by
      intro p _
      obtain ⟨y, hyp, hyU⟩ := every_meets p.1 p.2
      exact Set.mem_iUnion.2 ⟨y, Set.mem_iUnion.2 ⟨hyU, hyp⟩⟩
    have hpath_small : #paths < ρ := by
      rw [← Cardinal.mk_univ]
      exact (Cardinal.mk_le_mk_of_subset hsubset).trans_lt hunion_small
    exact hpath_small.2 hlarge

/-- A countable cover of a set of size at least a regular uncountable
cardinal has one part of that size. -/
theorem exists_large_nat_fiber {A : Type u} {ρ : Cardinal.{u}}
    (hρ : ρ.IsRegular) (hρu : ℵ₀ < ρ) (S : Set A) (F : ℕ → Set A)
    (hlarge : ρ ≤ #S) (hcover : S ⊆ ⋃ n, F n) :
    ∃ n, ρ ≤ #(F n) := by
  by_contra h
  push Not at h
  let F' : ULift.{u} ℕ → Set A := fun n ↦ F n.down
  have hsmall : #(⋃ n, F n) < ρ := by
    have huniv : #(Set.univ : Set (ULift.{u} ℕ)) < ρ := by
      simpa using hρu
    have hbi0 := FamilyTools.mk_biUnion_lt_of_isRegular hρ huniv
      (fun n _ ↦ h n.down)
    have hbi : #(⋃ n, F' n) < ρ := by
      have heq' : (⋃ n : ULift.{u} ℕ, ⋃ _ : n ∈ (Set.univ : Set (ULift.{u} ℕ)),
          F n.down) = ⋃ n, F' n := by
        ext x
        simp only [Set.mem_iUnion, Set.mem_univ, F']
        constructor
        · rintro ⟨n, _, hxn⟩
          exact ⟨n, hxn⟩
        · rintro ⟨n, hxn⟩
          exact ⟨n, trivial, hxn⟩
      rwa [heq'] at hbi0
    have heq : (⋃ n, F' n) = ⋃ n, F n := by
      apply Set.Subset.antisymm
      · intro x hx
        obtain ⟨n, hxn⟩ := Set.mem_iUnion.1 hx
        exact Set.mem_iUnion.2 ⟨n.down, hxn⟩
      · intro x hx
        obtain ⟨n, hxn⟩ := Set.mem_iUnion.1 hx
        exact Set.mem_iUnion.2 ⟨ULift.up n, hxn⟩
    rwa [heq] at hbi
  have hle : #S ≤ #(⋃ n, F n) := Cardinal.mk_le_mk_of_subset hcover
  exact (hle.trans_lt hsmall).2 hlarge

/-! ## Cardinally imbalanced joined path families -/

/-- A family of finite directed paths joined at their common initial
vertex.  This is the directed version of the `c`-joined families in
Aharoni's Lemma 2.5. -/
structure OutFan {V : Type u} (G : Digraph V) (c : V) (D : Set V) where
  paths : Set (FinitePath G)
  starts_at : ∀ {p}, p ∈ paths → p.start = c
  finishes_in : ∀ {p}, p ∈ paths → p.finish ∈ D
  joined : ∀ {p}, p ∈ paths → ∀ {q}, q ∈ paths → p ≠ q →
    p.support ∩ q.support ⊆ {c}

namespace OutFan

variable {V : Type u} {G : Digraph V} {c : V} {T : Set V}

/-- Distinct members of an out-fan have distinct terminal vertices whenever
the terminal set misses the common initial vertex. -/
def finishEmbedding (F : OutFan G c T) (hdisjoint : Disjoint ({c} : Set V) T) :
    F.paths ↪ T where
  toFun p := ⟨p.1.finish, F.finishes_in p.2⟩
  inj' := by
    intro p q hfinish
    apply Subtype.ext
    by_contra hpq
    have hfinishEq : p.1.finish = q.1.finish := congrArg Subtype.val hfinish
    have hfinishC : p.1.finish ∈ ({c} : Set V) :=
      F.joined p.2 q.2 hpq
        ⟨p.1.finish_mem_support, hfinishEq ▸ q.1.finish_mem_support⟩
    exact Set.disjoint_left.1 hdisjoint hfinishC (F.finishes_in p.2)

theorem paths_card_le (F : OutFan G c T)
    (hdisjoint : Disjoint ({c} : Set V) T) : #F.paths ≤ #T :=
  Cardinal.mk_le_of_injective (F.finishEmbedding hdisjoint).injective

/-- In a joined family, a set of vertices outside the join point can spoil
at most one member per vertex.  Thus a family larger than a forbidden set
contains a path meeting that set only at the join point. -/
theorem exists_member_inter_subset_singleton (F : OutFan G c T)
    (Z : Set V) (hcard : #Z < #F.paths) :
    ∃ p ∈ F.paths, p.support ∩ Z ⊆ {c} := by
  classical
  by_contra h
  push Not at h
  have hmeet : ∀ p ∈ F.paths, ∃ x ∈ Z \ {c}, x ∈ p.support := by
    intro p hp
    obtain ⟨x, ⟨hxp, hxZ⟩, hxc⟩ := Set.not_subset.mp (h p hp)
    exact ⟨x, ⟨hxZ, fun hxc' ↦ hxc (Set.mem_singleton_iff.2 hxc')⟩, hxp⟩
  let select : F.paths → (Z \ {c} : Set V) := fun p ↦
    ⟨Classical.choose (hmeet p.1 p.2),
      (Classical.choose_spec (hmeet p.1 p.2)).1⟩
  have hinj : Function.Injective select := by
    intro p q hpq
    apply Subtype.ext
    by_contra hpqPath
    have hxP : (select p : V) ∈ p.1.support :=
      (Classical.choose_spec (hmeet p.1 p.2)).2
    have hxQ : (select p : V) ∈ q.1.support := by
      rw [hpq]
      exact (Classical.choose_spec (hmeet q.1 q.2)).2
    have hxC : (select p : V) ∈ ({c} : Set V) :=
      F.joined p.2 q.2 hpqPath ⟨hxP, hxQ⟩
    exact (select p).2.2 (Set.mem_singleton_iff.1 hxC)
  have hle : #F.paths ≤ #(Z \ {c} : Set V) :=
    Cardinal.mk_le_of_injective hinj
  exact (not_lt_of_ge (hle.trans (Cardinal.mk_le_mk_of_subset Set.sdiff_subset))) hcard

end OutFan

/-- A relation is a partial system of distinct representatives for `T` when
it is single-valued in both coordinates and every selected pair follows
membership in `T`. -/
def IsPartialSDR (T : C → Set D) (R : Set (C × D)) : Prop :=
  (∀ p ∈ R, p.2 ∈ T p.1) ∧
    (∀ p ∈ R, ∀ q ∈ R, p.1 = q.1 → p.2 = q.2) ∧
    (∀ p ∈ R, ∀ q ∈ R, p.2 = q.2 → p.1 = q.1)

theorem isPartialSDR_empty (T : C → Set D) : IsPartialSDR T ∅ := by
  simp [IsPartialSDR]

/-- A union of a chain of partial SDRs is again a partial SDR. -/
theorem isPartialSDR_sUnion_of_chain (T : C → Set D)
    {c : Set (Set (C × D))} (hcsub : c ⊆ {R | IsPartialSDR T R})
    (hchain : IsChain (· ⊆ ·) c) : IsPartialSDR T (⋃₀ c) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨a, d⟩ had
    obtain ⟨R, hRc, hadR⟩ := Set.mem_sUnion.1 had
    exact (hcsub hRc).1 ⟨a, d⟩ hadR
  · rintro ⟨a, d⟩ had ⟨a', d'⟩ ha'd' haa'
    obtain ⟨R, hRc, hadR⟩ := Set.mem_sUnion.1 had
    obtain ⟨S, hSc, ha'd'S⟩ := Set.mem_sUnion.1 ha'd'
    rcases hchain.total hRc hSc with hRS | hSR
    · exact (hcsub hSc).2.1 ⟨a, d⟩ (hRS hadR) ⟨a', d'⟩ ha'd'S haa'
    · exact (hcsub hRc).2.1 ⟨a, d⟩ hadR ⟨a', d'⟩ (hSR ha'd'S) haa'
  · rintro ⟨a, d⟩ had ⟨a', d'⟩ ha'd' hdd'
    obtain ⟨R, hRc, hadR⟩ := Set.mem_sUnion.1 had
    obtain ⟨S, hSc, ha'd'S⟩ := Set.mem_sUnion.1 ha'd'
    rcases hchain.total hRc hSc with hRS | hSR
    · exact (hcsub hSc).2.2 ⟨a, d⟩ (hRS hadR) ⟨a', d'⟩ ha'd'S hdd'
    · exact (hcsub hRc).2.2 ⟨a, d⟩ hadR ⟨a', d'⟩ (hSR ha'd'S) hdd'

/-- Every set system has an inclusion-maximal partial system of distinct
representatives. -/
theorem exists_maximal_partialSDR (T : C → Set D) :
    ∃ R : Set (C × D), Maximal (IsPartialSDR T) R := by
  apply zorn_subset
  intro c hcsub hchain
  by_cases hcne : c.Nonempty
  · exact ⟨⋃₀ c, isPartialSDR_sUnion_of_chain T hcsub hchain,
      fun R hRc ↦ Set.subset_sUnion_of_mem hRc⟩
  · have hcempty : c = ∅ := Set.not_nonempty_iff_eq_empty.mp hcne
    exact ⟨∅, isPartialSDR_empty T, by simp [hcempty]⟩

/-- The represented indices of a partial SDR. -/
def domain (R : Set (C × D)) : Set C :=
  {c | ∃ d, (c, d) ∈ R}

/-- The used representatives of a partial SDR. -/
def range (R : Set (C × D)) : Set D :=
  {d | ∃ c, (c, d) ∈ R}

/-- The representative selected by a partial SDR at a represented index. -/
def representative {T : C → Set D} {R : Set (C × D)}
    (_hR : IsPartialSDR T R) (c : domain R) : D :=
  Classical.choose c.2

theorem representative_mem_relation {T : C → Set D}
    {R : Set (C × D)} (hR : IsPartialSDR T R) (c : domain R) :
    (c.1, representative hR c) ∈ R :=
  Classical.choose_spec c.2

theorem representative_mem {T : C → Set D} {R : Set (C × D)}
    (hR : IsPartialSDR T R) (c : domain R) : representative hR c ∈ T c.1 :=
  hR.1 _ (representative_mem_relation hR c)

theorem representative_injective {T : C → Set D}
    {R : Set (C × D)} (hR : IsPartialSDR T R) :
    Function.Injective (representative hR) := by
  intro c c' hcc'
  apply Subtype.ext
  exact hR.2.2 _ (representative_mem_relation hR c) _
    (representative_mem_relation hR c') hcc'

theorem range_eq_range_representative {T : C → Set D}
    {R : Set (C × D)} (hR : IsPartialSDR T R) :
    range R = Set.range (representative hR) := by
  ext d
  constructor
  · rintro ⟨c, hcd⟩
    let c' : domain R := ⟨c, d, hcd⟩
    refine ⟨c', ?_⟩
    exact hR.2.1 _ (representative_mem_relation hR c') _ hcd rfl
  · rintro ⟨c, rfl⟩
    exact ⟨c.1, representative_mem_relation hR c⟩

/-- Maximality says that every candidate belonging to an unrepresented
index is already used as a representative. -/
theorem subset_range_of_maximal_of_not_mem_domain {T : C → Set D}
    {R : Set (C × D)} (hR : Maximal (IsPartialSDR T) R)
    {c : C} (hc : c ∉ domain R) : T c ⊆ range R := by
  intro d hdT
  by_contra hdR
  have hadd : IsPartialSDR T (insert (c, d) R) := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨a, b⟩ hab
      rcases hab with hab | hab
      · rcases Prod.mk.inj hab with ⟨rfl, rfl⟩
        exact hdT
      · exact hR.prop.1 _ hab
    · rintro ⟨a, b⟩ hab ⟨a', b'⟩ ha'b' haa'
      rcases hab with hab | hab
      · rcases Prod.mk.inj hab with ⟨rfl, rfl⟩
        rcases ha'b' with ha'b' | ha'b'
        · rcases Prod.mk.inj ha'b' with ⟨rfl, rfl⟩
          rfl
        · exfalso
          apply hc
          have hcoord : a = a' := by simpa using haa'
          exact ⟨b', hcoord.symm ▸ ha'b'⟩
      · rcases ha'b' with ha'b' | ha'b'
        · rcases Prod.mk.inj ha'b' with ⟨rfl, rfl⟩
          exfalso
          apply hc
          have hcoord : a = a' := by simpa using haa'
          exact ⟨b, hcoord ▸ hab⟩
        · exact hR.prop.2.1 _ hab _ ha'b' haa'
    · rintro ⟨a, b⟩ hab ⟨a', b'⟩ ha'b' hbb'
      rcases hab with hab | hab
      · rcases Prod.mk.inj hab with ⟨rfl, rfl⟩
        rcases ha'b' with ha'b' | ha'b'
        · rcases Prod.mk.inj ha'b' with ⟨rfl, rfl⟩
          rfl
        · exfalso
          apply hdR
          have hcoord : b = b' := by simpa using hbb'
          exact ⟨a', hcoord.symm ▸ ha'b'⟩
      · rcases ha'b' with ha'b' | ha'b'
        · rcases Prod.mk.inj ha'b' with ⟨rfl, rfl⟩
          exfalso
          apply hdR
          have hcoord : b = b' := by simpa using hbb'
          exact ⟨a, hcoord ▸ hab⟩
        · exact hR.prop.2.2 _ hab _ ha'b' hbb'
  have hsubset : R ⊆ insert (c, d) R := Set.subset_insert _ _
  have heq := hR.eq_of_le hadd hsubset
  have hmem : (c, d) ∈ R := heq ▸ Set.mem_insert (c, d) R
  exact hdR ⟨c, hmem⟩

/-- Aharoni's maximal-SDR corollary: if the index family is larger than
the common ground set, some member is entirely covered by the range of a
partial system of distinct representatives. -/
theorem large_family_exists_sdr_covering_member (T : C → Set D)
    (hcard : #D < #C) :
    ∃ (c : C) (I : Set C) (g : I → D),
      Function.Injective g ∧ (∀ i, g i ∈ T i.1) ∧ T c ⊆ Set.range g := by
  obtain ⟨R, hR⟩ := exists_maximal_partialSDR T
  let I : Set C := domain R
  let g : I → D := representative hR.prop
  have hg : Function.Injective g := representative_injective hR.prop
  have hIcard : #I ≤ #D := Cardinal.mk_le_of_injective hg
  have hIne : I ≠ Set.univ := by
    intro hI
    have hCI : #C = #I := by simp [hI]
    have hCD : #C ≤ #D := hCI.trans_le hIcard
    exact (not_lt_of_ge hCD) hcard
  obtain ⟨c, hc⟩ : ∃ c, c ∉ I := by
    by_contra h
    push Not at h
    exact hIne (Set.eq_univ_of_forall h)
  refine ⟨c, I, g, hg, fun i ↦ representative_mem hR.prop i, ?_⟩
  rw [← range_eq_range_representative hR.prop]
  exact subset_range_of_maximal_of_not_mem_domain hR hc

end InfiniteKonig
end Erdos599

noncomputable section

open Cardinal Function Order Set

namespace Erdos599
namespace Aharoni25

open DirectedPath

universe u

variable {V : Type u} {G : Digraph V}

/-- A normalized `c`-joined family of paths from `C` to `D`.

Every path starts at `c`; distinct paths meet only at `c`; and no path
returns to `C` after its first vertex.  This is the concrete directed-path
version of the fans used in Aharoni's Lemma 2.5. -/
structure InFan (G : Digraph V) (C D : Set V) (c : V) where
  paths : Set (FinitePath G)
  start_eq : ∀ {p}, p ∈ paths → p.start = c
  join_mem : c ∈ C
  finish_mem : ∀ {p}, p ∈ paths → p.finish ∈ D
  normalized : ∀ {p}, p ∈ paths → p.support ∩ C ⊆ {c}
  joined : ∀ {p}, p ∈ paths → ∀ {q}, q ∈ paths → p ≠ q →
    p.support ∩ q.support ⊆ {c}

/-- A normalized outward fan from `C` into `x`. -/
structure OutFan (G : Digraph V) (C : Set V) (x : V) where
  paths : Set (FinitePath G)
  start_mem : ∀ {p}, p ∈ paths → p.start ∈ C
  finish_eq : ∀ {p}, p ∈ paths → p.finish = x
  normalized : ∀ {p}, p ∈ paths → p.support ∩ C ⊆ {p.start}
  joined : ∀ {p}, p ∈ paths → ∀ {q}, q ∈ paths → p ≠ q →
    p.support ∩ q.support ⊆ {x}

/-- A finite warp from `C` to `D`. -/
structure CDWarp (G : Digraph V) (C D : Set V) where
  paths : Set (FinitePath G)
  disjoint : paths.PairwiseDisjoint FinitePath.support
  start_mem : ∀ {p}, p ∈ paths → p.start ∈ C
  finish_mem : ∀ {p}, p ∈ paths → p.finish ∈ D

namespace InFan

theorem finish_injective {C D : Set V} {c : V} (F : InFan G C D c)
    (hCD : Disjoint C D) :
    Function.Injective (fun p : F.paths ↦ p.1.finish) := by
  intro p q hfinish
  apply Subtype.ext
  by_contra hpq
  change p.1.finish = q.1.finish at hfinish
  have hmeet : p.1.finish ∈ p.1.support ∩ q.1.support :=
    ⟨p.1.finish_mem_support, by simpa [hfinish] using q.1.finish_mem_support⟩
  have heq : p.1.finish = c := Set.mem_singleton_iff.1
    (F.joined p.2 q.2 hpq hmeet)
  exact Set.disjoint_left.1 hCD F.join_mem (heq ▸ F.finish_mem p.2)

theorem card_paths_le_target {C D : Set V} {c : V} (F : InFan G C D c)
    (hCD : Disjoint C D) : #F.paths ≤ #D := by
  let e : F.paths ↪ D :=
    ⟨fun p ↦ ⟨p.1.finish, F.finish_mem p.2⟩, fun _ _ h ↦
      F.finish_injective hCD (congrArg Subtype.val h)⟩
  exact Cardinal.mk_le_of_injective e.injective

end InFan

namespace OutFan

/-- Outside its common terminal, the paths of an outward fan are pairwise
disjoint. -/
theorem away_pairwiseDisjoint {C : Set V} {x : V} (H : OutFan G C x) :
    H.paths.PairwiseDisjoint (fun p ↦ p.support \ {x}) := by
  intro p hp q hq hpq
  apply Set.disjoint_left.2
  intro y hyp hyq
  have hyx : y ∈ ({x} : Set V) := H.joined hp hq hpq ⟨hyp.1, hyq.1⟩
  exact hyp.2 hyx

/-- A fan of successor-cardinal size has a branch avoiding any prescribed
set of size at most the predecessor cardinal, except at the common terminal.
This is the cardinal-choice step used at every stage of Aharoni's splicing
construction. -/
theorem exists_path_inter_subset_singleton {C : Set V} {x : V}
    (H : OutFan G C x) {l : Cardinal.{u}} (hlarge : succ l ≤ #H.paths)
    {Z : Set V} (hZ : #Z ≤ l) :
    ∃ p ∈ H.paths, p.support ∩ Z ⊆ {x} := by
  by_contra hex
  push Not at hex
  have hmeet : ∀ p ∈ H.paths,
      ∃ y ∈ Z \ {x}, y ∈ p.support \ {x} := by
    intro p hp
    obtain ⟨y, hypZ, hyx⟩ := Set.not_subset.1 (hex p hp)
    exact ⟨y, ⟨hypZ.2, hyx⟩, hypZ.1, hyx⟩
  let Z' : Set V := Z \ {x}
  have hcard : #H.paths ≤ #Z' :=
    FamilyTools.mk_le_of_pairwiseDisjoint_of_meets
      H.away_pairwiseDisjoint (by simpa [Z'] using hmeet)
  have hle : #H.paths ≤ l :=
    hcard.trans ((Cardinal.mk_le_mk_of_subset (by simp [Z'] : Z' ⊆ Z)).trans hZ)
  exact (lt_succ l).2 (hlarge.trans hle)

end OutFan

/-- The union of at most `λ` finite supports has cardinal at most `λ`, for
infinite `λ`. -/
theorem card_biUnion_finite_le {I : Type u} {A : Set I}
    (support : I → Set V) {l : Cardinal.{u}} (hl : ℵ₀ ≤ l)
    (hA : #A ≤ l) (hfin : ∀ i ∈ A, (support i).Finite) :
    #(⋃ i ∈ A, support i) ≤ l := by
  calc
    #(⋃ i ∈ A, support i) ≤ #A * (⨆ i : A, #(support i.1) : Cardinal.{u}) :=
      Cardinal.mk_biUnion_le support A
    _ ≤ l * ℵ₀ := by
      apply mul_le_mul' hA
      have hiSup : (⨆ i : A, #(support i.1) : Cardinal.{u}) ≤ ℵ₀ := by
        by_cases hne : A.Nonempty
        · letI : Nonempty A := Set.nonempty_coe_sort.mpr hne
          apply ciSup_le
          intro i
          exact (hfin i.1 i.2).countable.le_aleph0
        · have hAempty : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
          simp [hAempty]
      exact hiSup
    _ = l := Cardinal.mul_eq_left hl hl aleph0_ne_zero

/-- Splice a path ending at `x` to the suffix of `P` beginning at its last
visit to `x`. -/
def castWalkStart {a b c : V} (p : Walk G a c) (h : b = a) :
    Walk G b c := h ▸ p

@[simp] theorem support_castWalkStart {a b c : V} (p : Walk G a c)
    (h : b = a) : (castWalkStart p h).support = p.support := by
  subst b
  rfl

theorem isPath_castWalkStart {a b c : V} {p : Walk G a c}
    (hp : p.IsPath) (h : b = a) : (castWalkStart p h).IsPath := by
  rw [Walk.IsPath, support_castWalkStart]
  exact hp

theorem exists_splice {T P : FinitePath G} {x : V}
    (hTx : T.finish = x) (hxP : x ∈ P.support)
    (hxstart : x ≠ P.start)
    (hinter : T.support ∩ P.support ⊆ {x}) :
    ∃ Q : FinitePath G,
      Q.start = T.start ∧ Q.finish = P.finish ∧
        Q.support ⊆ T.support ∪ (P.support \ {P.start}) := by
  have hm : P.walk.Meets ({x} : Set V) := ⟨x, hxP, Set.mem_singleton x⟩
  let L := P.lastHit ({x} : Set V) hm
  have hLstart : L.start = x := Set.mem_singleton_iff.1
    (FinitePath.lastHit_start_mem P {x} hm)
  have hLsuffix : L.walk.support <:+ P.walk.support := by
    exact (P.walk.lastHit ({x} : Set V) hm).support_suffix
  have hstart_not_L : P.start ∉ L.support := by
    intro hstart
    change P.start ∈ L.walk.support at hstart
    have hheadmem : P.walk.support.head P.walk.support_ne_nil ∈ L.walk.support :=
      P.walk.head_support.symm ▸ hstart
    have heq : L.walk.support = P.walk.support :=
      P.isPath.eq_of_head_mem_of_suffix hLsuffix hheadmem
    have hstarts : L.start = P.start := by
      have hhead := L.walk.head_support
      simp only [heq] at hhead
      exact hhead.symm.trans P.walk.head_support
    exact hxstart (hLstart ▸ hstarts)
  have hmatch : T.finish = L.start := hTx.trans hLstart.symm
  let w : Walk G T.finish P.finish := castWalkStart L.walk hmatch
  have hwpath : w.IsPath := by
    exact isPath_castWalkStart L.isPath hmatch
  have hdisj : T.walk.support.Disjoint w.support.tail := by
    rw [List.disjoint_left]
    intro y hyT hyw
    have hwSupport : w.support = L.walk.support := by
      exact support_castWalkStart L.walk hmatch
    have hyLtail : y ∈ L.walk.support.tail := by simpa [hwSupport] using hyw
    have hyL : y ∈ L.support := by
      change y ∈ L.walk.support
      exact List.mem_of_mem_tail hyLtail
    have hyP : y ∈ P.support := FinitePath.lastHit_support_subset P {x} hm hyL
    have hyx : y = x := Set.mem_singleton_iff.1 (hinter ⟨hyT, hyP⟩)
    subst y
    have hxLstart : x = L.start := hLstart.symm
    have hxhead : x = L.walk.support.head L.walk.support_ne_nil :=
      hxLstart.trans L.walk.head_support.symm
    have hnodup : L.walk.support.Nodup := L.isPath
    rw [← List.cons_head_tail L.walk.support_ne_nil] at hnodup
    apply (List.nodup_cons.mp hnodup).1
    have hxhead' : x = L.walk.support.head L.walk.support_ne_nil :=
      hLstart.symm.trans L.walk.head_support.symm
    simpa [hxhead'] using hyLtail
  let Q := T.appendWalkOfDisjoint w hwpath hdisj
  refine ⟨Q, rfl, rfl, ?_⟩
  intro y hyQ
  have hyappend : y ∈ T.walk.support ++ w.support.tail := by
    simpa [Q, FinitePath.support, FinitePath.appendWalkOfDisjoint,
      FinitePath.appendWalk] using hyQ
  rcases List.mem_append.1 hyappend with hyT | hyw
  · exact Or.inl hyT
  · right
    have hwSupport : w.support = L.walk.support := by
      exact support_castWalkStart L.walk hmatch
    have hyL : y ∈ L.support := by
      change y ∈ L.walk.support
      exact List.mem_of_mem_tail (by simpa [hwSupport] using hyw)
    exact ⟨FinitePath.lastHit_support_subset P {x} hm hyL,
      fun hyStart ↦ hstart_not_L (hyStart ▸ hyL)⟩

/-! ### The maximal splicing construction -/

/-- A partial assignment of pairwise-disjoint replacement paths to members
of one fixed in-fan.  A replacement avoids the common source and every
other member of the original fan. -/
def IsSpliceAssignment {C D : Set V} {c : V} (F : InFan G C D c)
    (R : Set (FinitePath G × FinitePath G)) : Prop :=
  (∀ a ∈ R, a.1 ∈ F.paths ∧ a.2.start ∈ C ∧ a.2.finish = a.1.finish ∧
      c ∉ a.2.support ∧
      ∀ p ∈ F.paths, p ≠ a.1 → Disjoint a.2.support p.support) ∧
    (∀ a ∈ R, ∀ b ∈ R, a.1 = b.1 → a.2 = b.2) ∧
    (∀ a ∈ R, ∀ b ∈ R, a ≠ b → Disjoint a.2.support b.2.support)

theorem isSpliceAssignment_empty {C D : Set V} {c : V}
    (F : InFan G C D c) : IsSpliceAssignment F ∅ := by
  simp [IsSpliceAssignment]

theorem isSpliceAssignment_sUnion_of_chain {C D : Set V} {c : V}
    (F : InFan G C D c) {K : Set (Set (FinitePath G × FinitePath G))}
    (hK : K ⊆ {R | IsSpliceAssignment F R})
    (hchain : IsChain (· ⊆ ·) K) : IsSpliceAssignment F (⋃₀ K) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨R, hRK, haR⟩ := Set.mem_sUnion.1 ha
    exact (hK hRK).1 a haR
  · intro a ha b hb hab
    obtain ⟨R, hRK, haR⟩ := Set.mem_sUnion.1 ha
    obtain ⟨S, hSK, hbS⟩ := Set.mem_sUnion.1 hb
    rcases hchain.total hRK hSK with hRS | hSR
    · exact (hK hSK).2.1 a (hRS haR) b hbS hab
    · exact (hK hRK).2.1 a haR b (hSR hbS) hab
  · intro a ha b hb hab
    obtain ⟨R, hRK, haR⟩ := Set.mem_sUnion.1 ha
    obtain ⟨S, hSK, hbS⟩ := Set.mem_sUnion.1 hb
    rcases hchain.total hRK hSK with hRS | hSR
    · exact (hK hSK).2.2 a (hRS haR) b hbS hab
    · exact (hK hRK).2.2 a haR b (hSR hbS) hab

theorem exists_maximal_spliceAssignment {C D : Set V} {c : V}
    (F : InFan G C D c) :
    ∃ R, Maximal (IsSpliceAssignment F) R := by
  apply zorn_subset
  intro K hK hchain
  by_cases hne : K.Nonempty
  · exact ⟨⋃₀ K, isSpliceAssignment_sUnion_of_chain F hK hchain,
      fun R hRK ↦ Set.subset_sUnion_of_mem hRK⟩
  · have hKempty : K = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    exact ⟨∅, isSpliceAssignment_empty F, by simp [hKempty]⟩

theorem assignment_fst_injective {C D : Set V} {c : V}
    (F : InFan G C D c) {R : Set (FinitePath G × FinitePath G)}
    (hR : IsSpliceAssignment F R) :
    Function.Injective (fun a : R ↦ a.1.1) := by
  intro a b hab
  apply Subtype.ext
  apply Prod.ext hab
  exact hR.2.1 a.1 a.2 b.1 b.2 hab

theorem assignment_card_le_fan {C D : Set V} {c : V}
    (F : InFan G C D c) {R : Set (FinitePath G × FinitePath G)}
    (hR : IsSpliceAssignment F R) : #R ≤ #F.paths := by
  let e : R ↪ F.paths :=
    ⟨fun a ↦ ⟨a.1.1, (hR.1 a.1 a.2).1⟩, fun _ _ h ↦
      assignment_fst_injective F hR (congrArg Subtype.val h)⟩
  exact Cardinal.mk_le_of_injective e.injective

/-- Vertices occurring on the assigned replacement paths. -/
def assignmentVertices (R : Set (FinitePath G × FinitePath G)) : Set V :=
  ⋃ a ∈ R, a.2.support

theorem card_assignmentVertices_le {C D : Set V} {c : V}
    (F : InFan G C D c) {R : Set (FinitePath G × FinitePath G)}
    (hR : IsSpliceAssignment F R) {l : Cardinal.{u}} (hl : ℵ₀ ≤ l)
    (hF : #F.paths ≤ l) : #(assignmentVertices R) ≤ l := by
  exact card_biUnion_finite_le (fun a : FinitePath G × FinitePath G ↦ a.2.support)
    hl ((assignment_card_le_fan F hR).trans hF) (fun a _ ↦ a.2.support_finite)

/-- Vertices occurring on the fixed original fan. -/
def fanVertices {C D : Set V} {c : V} (F : InFan G C D c) : Set V :=
  ⋃ p ∈ F.paths, p.support

theorem card_fanVertices_le {C D : Set V} {c : V}
    (F : InFan G C D c) {l : Cardinal.{u}} (hl : ℵ₀ ≤ l)
    (hF : #F.paths ≤ l) : #(fanVertices F) ≤ l := by
  exact card_biUnion_finite_le FinitePath.support hl hF
    (fun p _ ↦ p.support_finite)

theorem card_forbiddenVertices_le {C D : Set V} {c : V}
    (F : InFan G C D c) {R : Set (FinitePath G × FinitePath G)}
    (hR : IsSpliceAssignment F R) {l : Cardinal.{u}} (hl : ℵ₀ ≤ l)
    (hF : #F.paths ≤ l) :
    #(↥((assignmentVertices R) ∪ (fanVertices F))) ≤ l := by
  calc
    #(↥((assignmentVertices R) ∪ (fanVertices F))) ≤
        #(assignmentVertices R) + #(fanVertices F) := Cardinal.mk_union_le _ _
    _ ≤ l + l := add_le_add (card_assignmentVertices_le F hR hl hF)
      (card_fanVertices_le F hl hF)
    _ = l := Cardinal.add_eq_self hl

/-- A vertex outside `C` carrying an outward fan of successor-cardinal
size. -/
def IsLargeFanPoint (G : Digraph V) (C : Set V) (l : Cardinal.{u})
    (x : V) : Prop :=
  x ∉ C ∧ ∃ H : OutFan G C x, succ l ≤ #H.paths

/-- The second (splicing) half of Aharoni's Lemma 2.5.  Once one fixed
in-fan meets the large-fan core on every branch, a maximal splicing
assignment yields a disjoint `C`--`D` warp covering all its terminals. -/
theorem exists_warp_covering_of_hits_largeFanPoints
    {C D : Set V} {c : V} {l : Cardinal.{u}}
    (hl : ℵ₀ ≤ l) (hCD : Disjoint C D) (hD : #D ≤ l)
    (F : InFan G C D c)
    (hhit : ∀ p ∈ F.paths,
      ∃ x ∈ p.support, IsLargeFanPoint G C l x) :
    ∃ W : CDWarp G C D,
      ∀ p ∈ F.paths, ∃ q ∈ W.paths, q.finish = p.finish := by
  classical
  have hFcard : #F.paths ≤ l := (F.card_paths_le_target hCD).trans hD
  obtain ⟨R, hRmax⟩ := exists_maximal_spliceAssignment F
  have hrepresented : ∀ p ∈ F.paths,
      ∃ q : FinitePath G, (p, q) ∈ R := by
    intro p hp
    by_contra hmissing
    push Not at hmissing
    obtain ⟨x, hxP, hxC, H, hHlarge⟩ := hhit p hp
    let Z : Set V := assignmentVertices R ∪ fanVertices F
    have hZcard : #Z ≤ l := by
      exact card_forbiddenVertices_le F hRmax.prop hl hFcard
    obtain ⟨T, hTH, hTZ⟩ := H.exists_path_inter_subset_singleton hHlarge hZcard
    have hPZ : p.support ⊆ Z := by
      intro y hy
      exact Or.inr (Set.mem_iUnion.2 ⟨p, Set.mem_iUnion.2 ⟨hp, hy⟩⟩)
    have hTP : T.support ∩ p.support ⊆ {x} := by
      intro y hy
      exact hTZ ⟨hy.1, hPZ hy.2⟩
    have hxstart : x ≠ p.start := by
      intro h
      exact hxC (h ▸ F.start_eq hp ▸ F.join_mem)
    obtain ⟨Q, hQstart, hQfinish, hQsupport⟩ :=
      exists_splice (H.finish_eq hTH) hxP hxstart hTP
    have hxc : x ≠ c := by
      intro h
      exact hxC (h ▸ F.join_mem)
    have hcZ : c ∈ Z := by
      right
      exact Set.mem_iUnion.2 ⟨p, Set.mem_iUnion.2
        ⟨hp, F.start_eq hp ▸ p.start_mem_support⟩⟩
    have hcT : c ∉ T.support := by
      intro hc
      exact hxc (Set.mem_singleton_iff.1 (hTZ ⟨hc, hcZ⟩)).symm
    have hx_not_other {p' : FinitePath G} (hp' : p' ∈ F.paths)
        (hne : p' ≠ p) : x ∉ p'.support := by
      intro hx'
      have hxc' : x = c := Set.mem_singleton_iff.1
        (F.joined hp' hp hne ⟨hx', hxP⟩)
      exact hxc hxc'
    have hT_other {p' : FinitePath G} (hp' : p' ∈ F.paths)
        (hne : p' ≠ p) : Disjoint T.support p'.support := by
      apply Set.disjoint_left.2
      intro y hyT hyp'
      have hp'Z : y ∈ Z := Or.inr (Set.mem_iUnion.2 ⟨p',
        Set.mem_iUnion.2 ⟨hp', hyp'⟩⟩)
      have hyx : y = x := Set.mem_singleton_iff.1 (hTZ ⟨hyT, hp'Z⟩)
      exact hx_not_other hp' hne (hyx ▸ hyp')
    have hPtail_other {p' : FinitePath G} (hp' : p' ∈ F.paths)
        (hne : p' ≠ p) : Disjoint (p.support \ {p.start}) p'.support := by
      apply Set.disjoint_left.2
      intro y hyp hyp'
      have hyc : y = c := Set.mem_singleton_iff.1
        (F.joined hp hp' hne.symm ⟨hyp.1, hyp'⟩)
      exact hyp.2 (Set.mem_singleton_iff.2
        (hyc.trans (F.start_eq hp).symm))
    have hQ_other {p' : FinitePath G} (hp' : p' ∈ F.paths)
        (hne : p' ≠ p) : Disjoint Q.support p'.support := by
      apply Set.disjoint_left.2
      intro y hyQ hyp'
      rcases hQsupport hyQ with hyT | hyPtail
      · exact Set.disjoint_left.1 (hT_other hp' hne) hyT hyp'
      · exact Set.disjoint_left.1 (hPtail_other hp' hne) hyPtail hyp'
    have hcQ : c ∉ Q.support := by
      intro hc
      rcases hQsupport hc with hcT' | hcP
      · exact hcT hcT'
      · exact hcP.2 (Set.mem_singleton_iff.2 (F.start_eq hp).symm)
    have hQ_old (a : FinitePath G × FinitePath G) (ha : a ∈ R) :
        Disjoint Q.support a.2.support := by
      have hpa : a.1 ≠ p := by
        intro heq
        exact hmissing a.2 (heq ▸ ha)
      have hx_not_a2 : x ∉ a.2.support := by
        intro hxa
        exact Set.disjoint_left.1 ((hRmax.prop.1 a ha).2.2.2.2 p hp hpa.symm)
          hxa hxP
      apply Set.disjoint_left.2
      intro y hyQ hya
      rcases hQsupport hyQ with hyT | hyPtail
      · have hyaZ : y ∈ Z := Or.inl (Set.mem_iUnion.2 ⟨a,
          Set.mem_iUnion.2 ⟨ha, hya⟩⟩)
        have hyx : y = x := Set.mem_singleton_iff.1 (hTZ ⟨hyT, hyaZ⟩)
        exact hx_not_a2 (hyx ▸ hya)
      · exact Set.disjoint_left.1
          (((hRmax.prop.1 a ha).2.2.2.2 p hp hpa.symm).symm) hyPtail.1 hya
    have hadd : IsSpliceAssignment F (insert (p, Q) R) := by
      refine ⟨?_, ?_, ?_⟩
      · intro a ha
        rcases Set.mem_insert_iff.1 ha with rfl | ha
        · exact ⟨hp, hQstart ▸ H.start_mem hTH, hQfinish,
            hcQ, fun p' hp' hne ↦ hQ_other hp' hne⟩
        · exact hRmax.prop.1 a ha
      · intro a ha b hb hab
        rcases Set.mem_insert_iff.1 ha with rfl | ha
        · rcases Set.mem_insert_iff.1 hb with rfl | hb
          · rfl
          · exfalso
            apply hmissing b.2
            rw [show (p, b.2) = b from Prod.ext hab rfl]
            exact hb
        · rcases Set.mem_insert_iff.1 hb with rfl | hb
          · exfalso
            apply hmissing a.2
            rw [show (p, a.2) = a from Prod.ext hab.symm rfl]
            exact ha
          · exact hRmax.prop.2.1 a ha b hb hab
      · intro a ha b hb hab
        rcases Set.mem_insert_iff.1 ha with rfl | ha
        · rcases Set.mem_insert_iff.1 hb with rfl | hb
          · exact (hab rfl).elim
          · exact hQ_old b hb
        · rcases Set.mem_insert_iff.1 hb with rfl | hb
          · exact (hQ_old a ha).symm
          · exact hRmax.prop.2.2 a ha b hb hab
    have hsub : R ⊆ insert (p, Q) R := Set.subset_insert _ _
    have heq := hRmax.eq_of_le hadd hsub
    exact hmissing Q (heq ▸ Set.mem_insert (p, Q) R)
  let W : CDWarp G C D :=
    { paths := Prod.snd '' R
      disjoint := by
        intro q hq q' hq' hne
        obtain ⟨a, ha, rfl⟩ := hq
        obtain ⟨b, hb, rfl⟩ := hq'
        have hab : a ≠ b := fun heq ↦ hne (congrArg Prod.snd heq)
        exact hRmax.prop.2.2 a ha b hb hab
      start_mem := by
        intro q hq
        obtain ⟨a, ha, rfl⟩ := hq
        exact (hRmax.prop.1 a ha).2.1
      finish_mem := by
        intro q hq
        obtain ⟨a, ha, rfl⟩ := hq
        rw [(hRmax.prop.1 a ha).2.2.1]
        exact F.finish_mem (hRmax.prop.1 a ha).1 }
  refine ⟨W, ?_⟩
  intro p hp
  obtain ⟨q, hpq⟩ := hrepresented p hp
  exact ⟨q, ⟨(p, q), hpq, rfl⟩, (hRmax.prop.1 (p, q) hpq).2.2.1⟩

/-! ### The finite-length descent -/

/-- Every vertex of a first-hit prefix other than its terminal occurs before
the prescribed occurrence of that terminal in the original path. -/
theorem mem_take_of_mem_firstHit_singleton_of_ne
    (p : FinitePath G) (y x : V) (n : ℕ)
    (hn : n < p.walk.support.length) (hny : p.walk.support[n] = y)
    (hxp : x ∈ (p.firstHit {y}
      ⟨y, hny ▸ List.getElem_mem hn, Set.mem_singleton y⟩).support)
    (hxy : x ≠ y) : x ∈ p.walk.support.take n := by
  classical
  let hm : p.walk.Meets ({y} : Set V) :=
    ⟨y, hny ▸ List.getElem_mem hn, Set.mem_singleton y⟩
  let q := p.firstHit {y} hm
  have hqprefix : q.walk.support <+: p.walk.support :=
    (p.walk.firstHit {y} hm).support_prefix
  have hqfinish : q.finish = y := Set.mem_singleton_iff.mp
    (p.firstHit_finish_mem {y} hm)
  have hxq : x ∈ q.walk.support := hxp
  have hqget : q.walk.support.getLast q.walk.support_ne_nil = y := by
    rw [q.walk.getLast_support]
    exact hqfinish
  have hxdrop : x ∈ q.walk.support.dropLast :=
    List.mem_dropLast_of_mem_of_ne_getLast hxq (fun h ↦ hxy (h.trans hqget))
  have hxorig : x ∈ p.walk.support := hqprefix.subset hxq
  rw [List.mem_take_iff_idxOf_lt hxorig]
  have hxidx : q.walk.support.idxOf x < q.walk.support.length - 1 :=
    (List.mem_dropLast_iff_idxOf_lt hxq).mp hxdrop
  have hyqmem : y ∈ q.walk.support := by
    rw [← hqfinish]
    exact q.finish_mem_support
  have hyidxq : q.walk.support.idxOf y = q.walk.support.length - 1 := by
    rw [← hqget]
    apply List.idxOf_getLast
    have hnod := q.isPath
    change q.walk.support.Nodup at hnod
    have hnod' := (List.nodup_concat q.walk.support.dropLast
      (q.walk.support.getLast q.walk.support_ne_nil)).mp (by
        simpa only [List.concat_eq_append, List.dropLast_append_getLast]
          using hnod)
    exact hnod'.1
  have hyidxp : p.walk.support.idxOf y = n := by
    rw [← hny]
    exact p.isPath.idxOf_getElem n hn
  rw [← hqprefix.idxOf_eq_of_mem hxq, ← hyidxp, ←
    hqprefix.idxOf_eq_of_mem hyqmem, hyidxq]
  exact hxidx

/-- Aharoni's finite-length descent: among more than `λ` normalized input
fans toward a set of size at most `λ`, one fan meets the successor-sized
fan core on every branch. -/
theorem exists_fan_hitting_largeFanPoints
    {C D : Set V} {l : Cardinal.{u}}
    (hl : ℵ₀ ≤ l) (hCD : Disjoint C D) (hD : #D ≤ l)
    (hC : l < #C) (Fs : ∀ c : C, InFan G C D c.1) :
    ∃ c : C, ∀ p ∈ (Fs c).paths,
      ∃ x ∈ p.support, IsLargeFanPoint G C l x := by
  classical
  by_contra hresult
  push Not at hresult
  let chosen : C → FinitePath G := fun c ↦ Classical.choose (hresult c)
  have chosen_mem (c : C) : chosen c ∈ (Fs c).paths :=
    (Classical.choose_spec (hresult c)).1
  have chosen_avoids (c : C) :
      ∀ x ∈ (chosen c).support, ¬ IsLargeFanPoint G C l x :=
    (Classical.choose_spec (hresult c)).2
  have chosen_injective : Function.Injective chosen := by
    intro c d hcd
    apply Subtype.ext
    calc
      c.1 = (chosen c).start := (Fs c).start_eq (chosen_mem c) |>.symm
      _ = (chosen d).start := congrArg FinitePath.start hcd
      _ = d.1 := (Fs d).start_eq (chosen_mem d)
  let E : Set (FinitePath G) := Set.range chosen
  have hEcard : #E = #C := Cardinal.mk_range_eq chosen chosen_injective
  let ρ : Cardinal.{u} := succ l
  have hρreg : ρ.IsRegular := Cardinal.isRegular_succ hl
  have hρunc : ℵ₀ < ρ := hl.trans_lt (lt_succ l)
  have hρE : ρ ≤ #E := by
    rw [hEcard]
    exact succ_le_of_lt hC
  have no_large_disjoint : ¬ ∃ M : Set (FinitePath G), M ⊆ E ∧
      M.PairwiseDisjoint FinitePath.support ∧ ρ ≤ #M := by
    rintro ⟨M, hME, hMdisj, hρM⟩
    have hmeet : ∀ p ∈ M, ∃ x ∈ D, x ∈ p.support := by
      intro p hp
      obtain ⟨c, rfl⟩ := hME hp
      exact ⟨(chosen c).finish, (Fs c).finish_mem (chosen_mem c),
        (chosen c).finish_mem_support⟩
    have hMD : #M ≤ #D :=
      FamilyTools.mk_le_of_pairwiseDisjoint_of_meets hMdisj hmeet
    exact (not_lt_of_ge (hρM.trans (hMD.trans hD))) (lt_succ l)
  obtain ⟨y₀, hy₀⟩ := (InfiniteKonig.large_pairwiseDisjoint_or_highDegree
      hρreg E FinitePath.support (fun p ↦ p.support_finite)
      (fun p _ ↦ p.support_nonempty) hρE).resolve_left no_large_disjoint
  let LargeAt : ℕ → Prop := fun n ↦
    ∃ y : V, ρ ≤ #{p : E |
      ∃ hn : n < p.1.walk.support.length, p.1.walk.support[n] = y}
  have largeAt_nonempty : ∃ n, LargeAt n := by
    let S : Set E := {p | y₀ ∈ p.1.support}
    let pos : ℕ → Set E := fun n ↦ {p | ∃ hn : n < p.1.walk.support.length,
      p.1.walk.support[n] = y₀}
    have hcover : S ⊆ ⋃ n, pos n := by
      intro p hp
      obtain ⟨n, hn, hny⟩ := List.mem_iff_getElem.mp hp
      exact Set.mem_iUnion.2 ⟨n, hn, hny⟩
    obtain ⟨n, hn⟩ := InfiniteKonig.exists_large_nat_fiber
      hρreg hρunc S pos hy₀ hcover
    exact ⟨n, y₀, hn⟩
  let n : ℕ := Nat.find largeAt_nonempty
  have hnlarge : LargeAt n := Nat.find_spec largeAt_nonempty
  obtain ⟨y, hy⟩ := hnlarge
  let A : Set E := {p | ∃ hn : n < p.1.walk.support.length,
    p.1.walk.support[n] = y}
  have hA : ρ ≤ #A := hy
  have n_pos : 0 < n := by
    by_contra hn0
    have hnzero : n = 0 := Nat.eq_zero_of_not_pos hn0
    have hsubsingle : Subsingleton A := by
      constructor
      intro p q
      apply Subtype.ext
      apply Subtype.ext
      obtain ⟨hp0, hpval⟩ := p.2
      obtain ⟨hq0, hqval⟩ := q.2
      have hpstart : p.1.1.start = y := by
        have hpval0 : p.1.1.walk.support[0] = y := by
          simpa [hnzero] using hpval
        exact p.1.1.support_getElem_zero.symm.trans hpval0
      have hqstart : q.1.1.start = y := by
        have hqval0 : q.1.1.walk.support[0] = y := by
          simpa [hnzero] using hqval
        exact q.1.1.support_getElem_zero.symm.trans hqval0
      obtain ⟨cp, hcp⟩ := p.1.2
      obtain ⟨cq, hcq⟩ := q.1.2
      have hcpq : cp = cq := by
        apply Subtype.ext
        calc
          cp.1 = (chosen cp).start := (Fs cp).start_eq (chosen_mem cp) |>.symm
          _ = p.1.1.start := congrArg FinitePath.start hcp
          _ = y := hpstart
          _ = q.1.1.start := hqstart.symm
          _ = (chosen cq).start := congrArg FinitePath.start hcq.symm
          _ = cq.1 := (Fs cq).start_eq (chosen_mem cq)
      exact hcp.symm.trans ((congrArg chosen hcpq).trans hcq)
    let e : A ↪ PUnit :=
      ⟨fun _ ↦ PUnit.unit, fun p q _ ↦ Subsingleton.elim p q⟩
    have hAone : #A ≤ 1 := by
      simpa using Cardinal.mk_le_of_injective e.injective
    have : ρ ≤ 1 := hA.trans hAone
    exact (not_lt_of_ge this)
      ((Cardinal.one_lt_aleph0.trans_le hl).trans (lt_succ l))
  let before : A → Set V := fun p ↦ {x | x ∈ p.1.1.walk.support.take n}
  have before_finite (p : A) : (before p).Finite := by
    exact (p.1.1.walk.support.take n).finite_toSet
  have before_nonempty (p : A) : (before p).Nonempty := by
    obtain ⟨hnlen, _⟩ := p.2
    refine ⟨p.1.1.walk.support[0], ?_⟩
    change p.1.1.walk.support[0] ∈ p.1.1.walk.support.take n
    rw [List.mem_take_iff_getElem]
    exact ⟨0, by simp [n_pos, Nat.zero_lt_of_lt hnlen]⟩
  have hunivlarge : ρ ≤ #(Set.univ : Set A) := by
    simpa only [Cardinal.mk_univ] using hA
  have hdich :
      (∃ M : Set A, M ⊆ Set.univ ∧ M.PairwiseDisjoint before ∧ ρ ≤ #M) ∨
        ∃ z : V, ρ ≤ #{p : (Set.univ : Set A) | z ∈ before p.1} :=
    InfiniteKonig.large_pairwiseDisjoint_or_highDegree
      (P := A) (V := V) (ρ := ρ) hρreg (Set.univ : Set A)
        before (fun p ↦ before_finite p) (fun p _ ↦ before_nonempty p)
        hunivlarge
  rcases hdich with hdisj | hdegree
  · obtain ⟨pathsM, hMuniv, hMdisj, hρM⟩ := hdisj
    let pref : (Subtype (fun p : ↥A => p ∈ pathsM)) → FinitePath G := by
      intro p
      exact p.1.1.1.firstHit {y}
        ⟨y, p.1.2.2 ▸ List.getElem_mem p.1.2.1, Set.mem_singleton y⟩
    have pref_mem_C
        (p : Subtype (fun p : ↥A => p ∈ pathsM)) : (pref p).start ∈ C := by
      obtain ⟨c, hc⟩ := p.1.1.2
      rw [show (pref p).start = p.1.1.1.start from rfl, ← hc,
        (Fs c).start_eq (chosen_mem c)]
      exact c.2
    have pref_finish
        (p : Subtype (fun p : ↥A => p ∈ pathsM)) :
        (pref p).finish = y := by
      exact Set.mem_singleton_iff.mp (FinitePath.firstHit_finish_mem _ _ _)
    have pref_injective : Function.Injective pref := by
      intro p q hpq
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      obtain ⟨cp, hcp⟩ := p.1.1.2
      obtain ⟨cq, hcq⟩ := q.1.1.2
      have hstart := congrArg FinitePath.start hpq
      change p.1.1.1.start = q.1.1.1.start at hstart
      rw [← hcp, ← hcq, (Fs cp).start_eq (chosen_mem cp),
        (Fs cq).start_eq (chosen_mem cq)] at hstart
      have hcc : cp = cq := Subtype.ext hstart
      exact hcp.symm.trans ((congrArg chosen hcc).trans hcq)
    let H : OutFan G C y :=
      { paths := Set.range pref
        start_mem := by
          rintro _ ⟨p, rfl⟩
          exact pref_mem_C p
        finish_eq := by
          rintro _ ⟨p, rfl⟩
          exact pref_finish p
        normalized := by
          rintro _ ⟨p, rfl⟩ x hx
          obtain ⟨c, hc⟩ := p.1.1.2
          have hxorig : x ∈ p.1.1.1.support :=
            FinitePath.firstHit_support_subset _ _ _ hx.1
          have hxc : x = c.1 := Set.mem_singleton_iff.mp
            ((Fs c).normalized (hc ▸ chosen_mem c) ⟨hc ▸ hxorig, hx.2⟩)
          apply Set.mem_singleton_iff.2
          calc
            x = c.1 := hxc
            _ = (chosen c).start := (Fs c).start_eq (chosen_mem c) |>.symm
            _ = p.1.1.1.start := congrArg FinitePath.start hc
            _ = (pref p).start := rfl
        joined := by
          rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩ hpq x hx
          by_cases hxy : x = y
          · exact Set.mem_singleton_iff.2 hxy
          · exfalso
            have hxp : x ∈ before p.1 :=
              mem_take_of_mem_firstHit_singleton_of_ne _ y x n
                p.1.2.1 p.1.2.2 hx.1 hxy
            have hxq : x ∈ before q.1 :=
              mem_take_of_mem_firstHit_singleton_of_ne _ y x n
                q.1.2.1 q.1.2.2 hx.2 hxy
            exact Set.disjoint_left.1 (hMdisj p.2 q.2
              (fun heq ↦ hpq (congrArg pref (Subtype.ext heq)))) hxp hxq }
    have hHlarge : ρ ≤ #H.paths := by
      rw [Cardinal.mk_range_eq pref pref_injective]
      exact hρM
    have hMsetne : pathsM.Nonempty := by
      apply Set.nonempty_coe_sort.mp
      rw [← Cardinal.mk_ne_zero_iff]
      exact ne_of_gt ((Cardinal.succ_pos l).trans_le hρM)
    let p : Subtype (fun p : ↥A => p ∈ pathsM) := ⟨Classical.choose hMsetne,
      Classical.choose_spec hMsetne⟩
    have hyC : y ∉ C := by
      intro hyC
      obtain ⟨c, hc⟩ := p.1.1.2
      have hynorm : y = c.1 := Set.mem_singleton_iff.mp
        ((Fs c).normalized (hc ▸ chosen_mem c)
          ⟨p.1.2.2 ▸ List.getElem_mem p.1.2.1, hyC⟩)
      have hyStart : p.1.1.1.start = y := by
        rw [← hc, (Fs c).start_eq (chosen_mem c), ← hynorm]
      have hidx0 : p.1.1.1.walk.support.idxOf y = 0 := by
        have hidx := p.1.1.1.isPath.idxOf_getElem 0
          p.1.1.1.support_length_pos
        rw [p.1.1.1.support_getElem_zero] at hidx
        exact (congrArg (fun z : V ↦ p.1.1.1.walk.support.idxOf z)
          hyStart.symm).trans hidx
      have hidxn : p.1.1.1.walk.support.idxOf y = n := by
        rw [← p.1.2.2]
        exact p.1.1.1.isPath.idxOf_getElem n p.1.2.1
      exact n_pos.ne' (hidxn.symm.trans hidx0)
    obtain ⟨c, hc⟩ := p.1.1.2
    exact chosen_avoids c y
      (hc ▸ p.1.2.2 ▸ List.getElem_mem p.1.2.1)
      ⟨hyC, H, hHlarge⟩
  · obtain ⟨z, hz⟩ := hdegree
    let S : Set A := {p | z ∈ before p}
    let pos : ℕ → Set A := fun j ↦ {p | p ∈ S ∧
      ∃ hj : j < p.1.1.walk.support.length, p.1.1.walk.support[j] = z}
    have hcover : S ⊆ ⋃ j, pos j := by
      intro p hp
      obtain ⟨j, hj, hjz⟩ := List.mem_iff_getElem.mp hp
      have hjorig : j < p.1.1.walk.support.length :=
        hj.trans_le (List.length_take_le' n p.1.1.walk.support)
      have hjz' : p.1.1.walk.support[j] = z := by
        rw [← List.getElem_take]
        exact hjz
      exact Set.mem_iUnion.2 ⟨j, hp, hjorig, hjz'⟩
    let univToS : {p : (Set.univ : Set A) // z ∈ before p.1} ↪ S :=
      { toFun := fun p ↦ ⟨p.1.1, p.2⟩
        inj' := by
          intro p q hpq
          apply Subtype.ext
          apply Subtype.ext
          exact congrArg (fun z : S ↦ z.1) hpq }
    have hScard : ρ ≤ #S :=
      hz.trans (Cardinal.mk_le_of_injective univToS.injective)
    obtain ⟨j, hjlarge⟩ := InfiniteKonig.exists_large_nat_fiber
      hρreg hρunc S pos hScard hcover
    have hjn : j < n := by
      have hposne : (pos j).Nonempty := by
        apply Set.nonempty_coe_sort.mp
        rw [← Cardinal.mk_ne_zero_iff]
        exact ne_of_gt ((Cardinal.succ_pos l).trans_le hjlarge)
      obtain ⟨p, hpS, hjlen, hjz⟩ := hposne
      have hzmem : z ∈ p.1.1.walk.support.take n := hpS
      have hzidx : p.1.1.walk.support.idxOf z < n :=
        (List.mem_take_iff_idxOf_lt (List.mem_of_mem_take hzmem)).mp hzmem
      have hzidxj : p.1.1.walk.support.idxOf z = j := by
        rw [← hjz]
        exact p.1.1.isPath.idxOf_getElem j hjlen
      rwa [hzidxj] at hzidx
    let target : Set E := {p | ∃ hj : j < p.1.walk.support.length,
      p.1.walk.support[j] = z}
    let emb : (pos j) ↪ target :=
      { toFun := fun p ↦ ⟨p.1.1, p.2.2⟩
        inj' := by
          intro p q hpq
          apply Subtype.ext
          apply Subtype.ext
          exact congrArg (fun z : target ↦ z.1) hpq }
    have htarget : ρ ≤ #target :=
      hjlarge.trans (Cardinal.mk_le_of_injective emb.injective)
    have hgoodj : LargeAt j := ⟨z, htarget⟩
    exact (not_le_of_gt hjn) (Nat.find_min' largeAt_nonempty hgoodj)

/-- Aharoni's Lemma 2.5: among more than `l` normalized in-fans from `C`
to a set `D` of size at most `l`, one fan's terminal set is covered by a
pairwise-disjoint `C`--`D` warp. -/
theorem exists_warp_covering_one_fan
    {C D : Set V} {l : Cardinal.{u}}
    (hl : ℵ₀ ≤ l) (hCD : Disjoint C D) (hD : #D ≤ l)
    (hC : l < #C) (Fs : ∀ c : C, InFan G C D c.1) :
    ∃ (c : C) (W : CDWarp G C D),
      ∀ p ∈ (Fs c).paths, ∃ q ∈ W.paths, q.finish = p.finish := by
  obtain ⟨c, hc⟩ := exists_fan_hitting_largeFanPoints hl hCD hD hC Fs
  obtain ⟨W, hW⟩ :=
    exists_warp_covering_of_hits_largeFanPoints hl hCD hD (Fs c) hc
  exact ⟨c, W, hW⟩

end Aharoni25
end Erdos599
