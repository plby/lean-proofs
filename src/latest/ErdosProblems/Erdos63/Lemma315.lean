/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos63.BoundedExpansions
import ErdosProblems.Erdos63.AvoidanceDeep

/-!
# Two disjoint connectors (Liu--Montgomery Corollary 3.15)

This file contains the finite combinatorial form of Lemmas 3.12--3.14 and
Corollary 3.15 from Liu--Montgomery.  All occurrences of ``sufficiently
large'' are represented by explicit natural-number or real inequalities.
In particular, none of the conclusions below assumes the availability of a
path or of an auxiliary expansion.
-/

open Finset Set SimpleGraph
open scoped BigOperators SimpleGraph

namespace Erdos63

universe u v

variable {V : Type u} {Key : Type v} {G : SimpleGraph V}

attribute [local instance] Classical.propDecidable Classical.decEq

/-! ## Elementary path and expansion operations -/

private theorem Walk.avoids_empty_of_endpoints_outside {x y : V}
    {W : Set V} {p : G.Walk x y}
    (hp : p.Avoids W ({x, y} : Set V)) (hx : x ∉ W) (hy : y ∉ W) :
    p.Avoids W (∅ : Set V) := by
  intro z hz hzW
  have hzxy := hp z hz hzW
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hzxy
  rcases hzxy with rfl | rfl
  · exact (hx hzW).elim
  · exact (hy hzW).elim

theorem Walk.IsPath.append_of_inter_eq_end {x y z : V}
    {p : G.Walk x y} {q : G.Walk y z}
    (hp : p.IsPath) (hq : q.IsPath)
    (hinter : ∀ w : V, w ∈ p.support → w ∈ q.support → w = y) :
    (p.append q).IsPath := by
  apply Walk.IsPath.mk'
  rw [Walk.support_append, List.nodup_append']
  refine ⟨hp.support_nodup, hq.support_nodup.tail, ?_⟩
  rw [List.disjoint_left]
  intro w hwp hwq
  have hwq' : w ∈ q.support := List.tail_subset _ hwq
  have hwy : w = y := hinter w hwp hwq'
  subst w
  have hn := hq.support_nodup
  rw [← q.cons_tail_support, List.nodup_cons] at hn
  exact hn.1 hwq

theorem Walk.support_take_subset_support {x y : V}
    (p : G.Walk x y) (n : ℕ) : (p.take n).support ⊆ p.support := by
  rw [Walk.support_take]
  exact (List.take_prefix (n + 1) p.support).subset

/-- Re-root a bounded expansion at any one of its vertices, paying a factor
two in the radius. -/
private noncomputable def VertexExpansion.reroot {root y : V} {D r : ℕ}
    (E : VertexExpansion G root D r) (hy : y ∈ E.verts) :
    VertexExpansion G y D (2 * r) where
  vertices := E.verts
  root_mem := hy
  card_vertices := E.card_verts
  path_to := by
    intro z hz
    obtain ⟨py, hpy, hpylen, hpysupp⟩ := E.exists_path hy
    obtain ⟨pz, hpz, hpzlen, hpzsupp⟩ := E.exists_path hz
    let w : G.Walk y z := py.reverse.append pz
    refine ⟨w.bypass, w.bypass_isPath, ?_, ?_⟩
    · calc
        w.bypass.length ≤ w.length := w.length_bypass_le_length
        _ = py.length + pz.length := by simp [w]
        _ ≤ 2 * r := by omega
    · intro a ha
      have ha' := w.support_bypass_subset_support ha
      change a ∈ (py.reverse.append pz).support at ha'
      rw [Walk.mem_support_append_iff] at ha'
      rcases ha' with ha' | ha'
      · exact hpysupp a (by simpa [py.support_reverse] using ha')
      · exact hpzsupp a ha'

@[simp] private theorem VertexExpansion.verts_reroot {root y : V} {D r : ℕ}
    (E : VertexExpansion G root D r) (hy : y ∈ E.verts) :
    (E.reroot hy).verts = E.verts := rfl

/-- The prefix ending at the first vertex of `S`. -/
private theorem exists_first_entry_prefix {x y : V} (p : G.Walk x y)
    (hp : p.IsPath) (S : Finset V) (hy : y ∈ S) :
    ∃ z ∈ S, ∃ q : G.Walk x z,
      q.IsPath ∧ q.length ≤ p.length ∧
        q.support ⊆ p.support ∧
        (∀ w : V, w ∈ q.support → w ∈ S → w = z) := by
  classical
  let P : ℕ → Prop := fun i ↦ i ≤ p.length ∧ p.getVert i ∈ S
  have hP : ∃ i, P i := by
    refine ⟨p.length, le_rfl, ?_⟩
    simpa using hy
  let i := Nat.find hP
  have hi : i ≤ p.length ∧ p.getVert i ∈ S := Nat.find_spec hP
  let z := p.getVert i
  let q : G.Walk x z := p.take i
  have hqlen : q.length = i := by
    simp [q, Walk.take_length, Nat.min_eq_left hi.1]
  refine ⟨z, hi.2, q, hp.take i, by omega, ?_, ?_⟩
  · intro w hw
    exact Walk.support_take_subset_support p i hw
  intro w hwq hwS
  obtain ⟨j, hjw, hjle⟩ :=
    (Walk.mem_support_iff_exists_getVert (p := q)).1 hwq
  have hji : j ≤ i := by simpa [hqlen] using hjle
  have hqget : q.getVert j = p.getVert j := by
    simp [q, Walk.take_getVert, Nat.min_eq_right hji]
  have hjP : P j := by
    refine ⟨hji.trans hi.1, ?_⟩
    simpa [← hjw, hqget] using hwS
  have hij : i ≤ j := Nat.find_min' hP hjP
  have hjiEq : j = i := Nat.le_antisymm hji hij
  rw [← hjw, hqget, hjiEq]

/-- Trim a path to the segment from its last visit to `A` before its first
visit to `B`.  Consequently the trimmed path meets each set only at the
corresponding endpoint. -/
private theorem exists_minimal_subpath {x y : V} (p : G.Walk x y)
    (hp : p.IsPath) (A B : Finset V) (hx : x ∈ A) (hy : y ∈ B) :
    ∃ a ∈ A, ∃ b ∈ B, ∃ q : G.Walk a b,
      q.IsPath ∧ q.length ≤ p.length ∧ q.support ⊆ p.support ∧
        (∀ z : V, z ∈ q.support → z ∈ A → z = a) ∧
        (∀ z : V, z ∈ q.support → z ∈ B → z = b) := by
  obtain ⟨b, hb, q₀, hq₀, hq₀len, hq₀sub, hq₀B⟩ :=
    exists_first_entry_prefix p hp B hy
  obtain ⟨a, ha, r, hr, hrlen, hrsub, hrA⟩ :=
    exists_first_entry_prefix q₀.reverse hq₀.reverse A hx
  let q : G.Walk a b := r.reverse
  refine ⟨a, ha, b, hb, q, hr.reverse, ?_, ?_, ?_, ?_⟩
  · calc
      q.length = r.length := by simp [q]
      _ ≤ q₀.reverse.length := hrlen
      _ = q₀.length := by simp
      _ ≤ p.length := hq₀len
  · intro z hz
    have hzr : z ∈ r.support := by simpa [q] using hz
    have hzq₀rev := hrsub hzr
    have hzq₀ : z ∈ q₀.support := by simpa using hzq₀rev
    exact hq₀sub hzq₀
  · intro z hz hzA
    have hzr : z ∈ r.support := by simpa [q] using hz
    exact hrA z hzr hzA
  · intro z hz hzB
    have hzr : z ∈ r.support := by simpa [q] using hz
    have hzq₀rev := hrsub hzr
    have hzq₀ : z ∈ q₀.support := by simpa using hzq₀rev
    exact hq₀B z hzq₀ hzB

/-- Attach a rooted path to an expansion and retain an expansion of the old
order.  Loop erasure makes no disjointness assumption between the two pieces
necessary. -/
private theorem exists_attached_expansion {x y : V} {D rp rE R : ℕ}
    (p : G.Walk x y) (hp : p.IsPath) (hplen : p.length ≤ rp)
    (E : VertexExpansion G y D rE) (hR : rp + rE ≤ R) :
    ∃ F : VertexExpansion G x D R,
      F.verts ⊆ p.support.toFinset ∪ E.verts := by
  classical
  let S : Finset V := p.support.toFinset ∪ E.verts
  have hxS : x ∈ S := by
    exact Finset.mem_union_left _ (by simp)
  let Ffull : VertexExpansion G x S.card (rp + rE) :=
    { vertices := S
      root_mem := hxS
      card_vertices := rfl
      path_to := by
        intro z hz
        rw [Finset.mem_union] at hz
        rcases hz with hzp | hzE
        · have hzp' : z ∈ p.support := by simpa using hzp
          let q := p.takeUntil z hzp'
          exact ⟨q, hp.takeUntil hzp',
            ((p.length_takeUntil_le_length hzp').trans hplen).trans
              (Nat.le_add_right rp rE),
            fun w hw ↦ Finset.mem_union_left _ <| by
              simp only [List.mem_toFinset]
              exact p.support_takeUntil_subset_support hzp' hw⟩
        · obtain ⟨q, hq, hqlen, hqsupp⟩ := E.exists_path hzE
          let w : G.Walk x z := p.append q
          refine ⟨w.bypass, w.bypass_isPath, ?_, ?_⟩
          · calc
              w.bypass.length ≤ w.length := w.length_bypass_le_length
              _ = p.length + q.length := by simp [w]
              _ ≤ rp + rE := Nat.add_le_add hplen hqlen
          · intro a ha
            have ha' := w.support_bypass_subset_support ha
            change a ∈ (p.append q).support at ha'
            rw [Walk.mem_support_append_iff] at ha'
            rcases ha' with ha' | ha'
            · exact Finset.mem_union_left _ (by simpa using ha')
            · exact Finset.mem_union_right _ (hqsupp a ha') }
  have hDcard : D ≤ S.card := by
    rw [← E.card_verts]
    exact Finset.card_le_card (Finset.subset_union_right)
  obtain ⟨Fsmall, hsmall⟩ := Ffull.proposition3_10 E.size_pos hDcard
  let F : VertexExpansion G x D R := Fsmall.radiusMono hR
  exact ⟨F, by simpa [F] using hsmall⟩

/-! ## A quantitative finite form of Lemma 3.12 -/

/-- Numeric data for the repeated halving argument which turns a large ball
grown from several centres into a large ball about one centre. -/
structure HalvingSchedule (L rounds : ℕ) where
  centers : ℕ → ℕ
  zero : L ≤ centers 0
  step : ∀ i < rounds, (centers i + 1) / 2 ≤ centers (i + 1)
  last : centers rounds ≤ 1

/-- A concrete lower curve for the successive sizes of an avoiding ball.
Unlike a fixed additive increment, this permits the geometrically increasing
curves used in the Komlós--Szemerédi connection lemma. -/
structure BallGrowthSchedule [Fintype V] (G : SimpleGraph V)
    (epsilon kappa : ℝ) (start workspace radius : ℕ) where
  size : ℕ → ℕ
  initial : size 0 ≤ start
  lower : ∀ i ≤ radius, kappa / 2 ≤ (size i : ℝ)
  target : Fintype.card V / 2 + 1 ≤ size radius
  step : ∀ i < radius, ∀ s : ℕ,
    size i ≤ s → s ≤ Fintype.card V / 2 →
      ((((workspace + (size (i + 1) - s) : ℕ) : ℝ)) ≤
        expansionEpsilon epsilon kappa s * (s : ℝ))

/-- An explicit growth curve plus `IsLMExpander` forces an avoiding ball
past half the ambient vertex set. -/
theorem BallGrowthSchedule.grow [Fintype V]
    {epsilon kappa : ℝ} {start workspace radius : ℕ}
    (S : BallGrowthSchedule G epsilon kappa start workspace radius)
    (hexp : IsLMExpander G epsilon kappa)
    (W A : Finset V) (hW : W.card ≤ workspace) (hA : start ≤ A.card) :
    Fintype.card V / 2 + 1 ≤
      (ballAvoidingFrom G (W : Set V) A radius).card := by
  let cap := Fintype.card V / 2 + 1
  have hind : ∀ i ≤ radius,
      min (S.size i) cap ≤
        (ballAvoidingFrom G (W : Set V) A i).card := by
    intro i hi
    induction i with
    | zero =>
        exact (min_le_left _ _).trans <|
          S.initial.trans <| hA.trans <|
            Finset.card_le_card (subset_ballAvoidingFrom G (W : Set V) A 0)
    | succ i ih =>
        have hi' : i ≤ radius := Nat.le_of_succ_le hi
        have ih' := ih hi'
        let current := ballAvoidingFrom G (W : Set V) A i
        by_cases hcap : cap ≤ current.card
        · exact (min_le_right _ cap).trans <|
            hcap.trans <| Finset.card_le_card <|
              ballAvoidingFrom_radius_mono G (W : Set V) A (Nat.le_succ i)
        · have hcurrentUpper : current.card ≤ Fintype.card V / 2 := by
            dsimp [cap] at hcap
            omega
          have hsizeCurrent : S.size i ≤ current.card := by
            by_contra hnot
            have hcapSize : cap ≤ S.size i := by
              by_contra hnotcap
              have : S.size i < cap := Nat.lt_of_not_ge hnotcap
              apply hnot
              simpa [min_eq_left (Nat.le_of_lt this)] using ih'
            have : cap ≤ current.card :=
              (by simpa [min_eq_right hcapSize] using ih')
            exact hcap this
          let gain := S.size (i + 1) - current.card
          have hlower : kappa / 2 ≤ (current.card : ℝ) :=
            (S.lower i hi').trans (by exact_mod_cast hsizeCurrent)
          have hexternalReal : (((workspace + gain : ℕ) : ℝ)) ≤
              (externalNeighborhood G current).card := by
            exact (S.step i (Nat.lt_of_succ_le hi) current.card hsizeCurrent
              hcurrentUpper).trans (hexp.expands hlower (by
                have htwice : 2 * current.card ≤ Fintype.card V := by omega
                have htwiceReal : ((2 * current.card : ℕ) : ℝ) ≤
                    (Fintype.card V : ℝ) := by exact_mod_cast htwice
                norm_num at htwiceReal ⊢
                linarith))
          have hexternal : workspace + gain ≤
              (externalNeighborhood G current).card := by
            exact_mod_cast hexternalReal
          have hblocked :
              (blockedExternalNeighborhood G (W : Set V) current).card ≤
                workspace :=
            (Finset.card_le_card
              (blockedExternalNeighborhood_subset_deleted G W current)).trans hW
          have hnext : current.card + gain ≤
              (ballAvoidingFrom G (W : Set V) A (i + 1)).card := by
            apply card_ballAvoidingFrom_add_le_succ_of_external
              G (W : Set V) A i gain
            calc
              gain + (blockedExternalNeighborhood G (W : Set V) current).card
                  ≤ gain + workspace := Nat.add_le_add_left hblocked gain
              _ = workspace + gain := Nat.add_comm _ _
              _ ≤ (externalNeighborhood G current).card := hexternal
          have hgain : S.size (i + 1) ≤ current.card + gain := by
            dsimp [gain]
            omega
          exact (min_le_left _ _).trans (hgain.trans hnext)
  have hfinal := hind radius le_rfl
  have hmin : min (S.size radius) cap = cap := min_eq_right S.target
  rw [hmin] at hfinal
  exact hfinal

/-- Grow from a set which either already reaches the expander cutoff or
reaches it after one radius-one minimum-degree bootstrap.  The extra unit of
radius is retained in both cases so that callers need not split on the two
regimes. -/
theorem BallGrowthSchedule.grow_one_more [Fintype V] [DecidableRel G.Adj]
    {epsilon kappa : ℝ} {start workspace radius degreeScale : ℕ}
    (S : BallGrowthSchedule G epsilon kappa start workspace radius)
    (hexp : IsLMExpander G epsilon kappa)
    (hdegree : ∀ v : V, degreeScale ≤ G.degree v)
    (W A : Finset V) (hW : W.card ≤ workspace)
    (hAW : Disjoint A W) (hA : A.Nonempty)
    (hseed : start ≤ A.card ∨ start + workspace ≤ degreeScale) :
    Fintype.card V / 2 + 1 ≤
      (ballAvoidingFrom G (W : Set V) A (radius + 1)).card := by
  rcases hseed with hseed | hbootstrap
  · exact (S.grow hexp W A hW hseed).trans <| Finset.card_le_card <|
      ballAvoidingFrom_radius_mono G (W : Set V) A (by omega)
  · obtain ⟨a, ha⟩ := hA
    let A₁ := ballAvoidingFrom G (W : Set V) A 1
    let Ea : VertexExpansion G a 1 0 := VertexExpansion.singleton G a 0
    have hroot : degreeScale - workspace ≤
        (ballAvoidingFrom G (W : Set V) Ea.verts 1).card := by
      have h := Ea.minDegree_sub_budget_le_card_ballAvoidingFrom_one
        G W (d := degreeScale + 1) (budget := workspace)
        (by simpa using hdegree a) hW
      simpa using h
    have hrootSub : ballAvoidingFrom G (W : Set V) Ea.verts 1 ⊆ A₁ := by
      intro z hz
      obtain ⟨u, huEa, huz⟩ := (mem_ballAvoidingFrom G (W : Set V)
        Ea.verts 1 z).1 hz
      have hua : u = a := by
        change u ∈ ({a} : Finset V) at huEa
        simpa using huEa
      exact (mem_ballAvoidingFrom G (W : Set V) A 1 z).2
        ⟨u, hua ▸ ha, huz⟩
    have hA₁card : start ≤ A₁.card := by
      have := hroot.trans (Finset.card_le_card hrootSub)
      omega
    have hAavoids : ∀ z ∈ A, z ∉ (W : Set V) := by
      intro z hz hzW
      exact Finset.disjoint_left.1 hAW hz hzW
    have hlarge := S.grow hexp W A₁ hW hA₁card
    have hsub : ballAvoidingFrom G (W : Set V) A₁ radius ⊆
        ballAvoidingFrom G (W : Set V) A (1 + radius) := by
      exact ballAvoidingFrom_ballAvoidingFrom_subset
        G (W : Set V) A 1 radius hAavoids
    have := hlarge.trans (Finset.card_le_card hsub)
    simpa [Nat.add_comm] using this

/-- Splitting the centres into two almost equal pieces leaves one piece whose
ball has at least half the cardinality of the original union. -/
private theorem exists_half_centres_with_large_ball [Fintype V]
    (G : SimpleGraph V) (W : Set V) (A : Finset V) (r L : ℕ)
    (hlarge : 2 * L ≤ (ballAvoidingFrom G W A r).card) :
    ∃ B ⊆ A, B.card ≤ (A.card + 1) / 2 ∧
      L ≤ (ballAvoidingFrom G W B r).card := by
  classical
  obtain ⟨B, hBA, hBcard⟩ :=
    Finset.exists_subset_card_eq (Nat.div_le_self A.card 2)
  let C := A \ B
  have hCcard : C.card = A.card - B.card := by
    dsimp [C]
    exact Finset.card_sdiff_of_subset hBA
  have hsplit : ballAvoidingFrom G W A r =
      ballAvoidingFrom G W B r ∪ ballAvoidingFrom G W C r := by
    ext z
    simp only [mem_ballAvoidingFrom, Finset.mem_union]
    constructor
    · rintro ⟨a, ha, haz⟩
      by_cases haB : a ∈ B
      · exact Or.inl ⟨a, haB, haz⟩
      · exact Or.inr ⟨a, Finset.mem_sdiff.2 ⟨ha, haB⟩, haz⟩
    · rintro (⟨a, ha, haz⟩ | ⟨a, ha, haz⟩)
      · exact ⟨a, hBA ha, haz⟩
      · exact ⟨a, (Finset.mem_sdiff.1 ha).1, haz⟩
  have hsum : 2 * L ≤
      (ballAvoidingFrom G W B r).card +
        (ballAvoidingFrom G W C r).card := by
    calc
      2 * L ≤ (ballAvoidingFrom G W A r).card := hlarge
      _ = (ballAvoidingFrom G W B r ∪
          ballAvoidingFrom G W C r).card := by rw [hsplit]
      _ ≤ _ := Finset.card_union_le _ _
  have hcase : L ≤ (ballAvoidingFrom G W B r).card ∨
      L ≤ (ballAvoidingFrom G W C r).card := by omega
  rcases hcase with hcase | hcase
  · refine ⟨B, hBA, ?_, hcase⟩
    omega
  · refine ⟨C, Finset.sdiff_subset, ?_, hcase⟩
    have hBdiv : B.card = A.card / 2 := hBcard
    omega

/-- Liu--Montgomery Lemma 3.12 with every suppressed estimate exposed.
It produces a genuinely new bounded expansion outside an arbitrary deleted
set; no expansion-existence premise occurs in the hypotheses. -/
theorem liuMontgomery_lemma3_12_finite [Fintype V]
    (G : SimpleGraph V) (epsilon kappa : ℝ)
    (hexp : IsLMExpander G epsilon kappa)
    (W : Finset V) (workspace K L radius rounds m : ℕ)
    (schedule : HalvingSchedule K rounds)
    (growth : BallGrowthSchedule G epsilon kappa K workspace radius)
    (hW : W.card ≤ workspace)
    (hroom : workspace + K ≤ Fintype.card V)
    (hKpos : 0 < K) (hLpos : 0 < L) (hLK : L ≤ K)
    (hhalve : 2 * K ≤ Fintype.card V / 2 + 1)
    (hradius : radius * rounds ≤ m) :
    ∃ root : V, ∃ E : VertexExpansion G root L m,
      Disjoint E.verts W := by
  classical
  let P : ℕ → Prop := fun i ↦ ∃ A : Finset V,
    A ⊆ (Finset.univ : Finset V) \ W ∧
      A.card ≤ schedule.centers i ∧
      K ≤ (ballAvoidingFrom G (W : Set V) A (radius * i)).card
  have hcompl : K ≤ ((Finset.univ : Finset V) \ W).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ W), Finset.card_univ]
    omega
  obtain ⟨A0, hA0, hA0card⟩ := Finset.exists_subset_card_eq hcompl
  have hP0 : P 0 := by
    refine ⟨A0, hA0, hA0card.le.trans schedule.zero, ?_⟩
    simpa [hA0card] using
      Finset.card_le_card (subset_ballAvoidingFrom G (W : Set V) A0 0)
  let i := Nat.findGreatest P rounds
  have hiP : P i := Nat.findGreatest_spec (P := P) (Nat.zero_le _) hP0
  have hirounds : i ≤ rounds := Nat.findGreatest_le rounds
  obtain ⟨A, hAW, hAcard, hAball⟩ := hiP
  have hAne : A.Nonempty := by
    by_contra hAempty
    rw [Finset.not_nonempty_iff_eq_empty.1 hAempty] at hAball
    have hzero : K ≤ 0 := by simpa [ballAvoidingFrom] using hAball
    omega
  have hAone : A.card ≤ 1 := by
    by_contra hnot
    have hAtwo : 2 ≤ A.card := by omega
    have hilt : i < rounds := by
      by_contra h
      have hieq : i = rounds := Nat.le_antisymm hirounds (Nat.le_of_not_gt h)
      have hcenters : schedule.centers i ≤ 1 := by
        simpa [hieq] using schedule.last
      have := hAcard.trans hcenters
      omega
    let current := ballAvoidingFrom G (W : Set V) A (radius * i)
    have hcurrentLower : K ≤ current.card := hAball
    have hhalf : Fintype.card V / 2 + 1 ≤
        (ballAvoidingFrom G (W : Set V) current radius).card :=
      growth.grow hexp W current hW hcurrentLower
    have hAavoids : ∀ a ∈ A, a ∉ (W : Set V) := by
      intro a ha haW
      exact (Finset.mem_sdiff.1 (hAW ha)).2 haW
    have hsemigroup := ballAvoidingFrom_ballAvoidingFrom_subset
      G (W : Set V) A (radius * i) radius hAavoids
    have hbig : 2 * K ≤
        (ballAvoidingFrom G (W : Set V) A (radius * (i + 1))).card := by
      calc
        2 * K ≤ Fintype.card V / 2 + 1 := hhalve
        _ ≤ (ballAvoidingFrom G (W : Set V) current radius).card := hhalf
        _ ≤ (ballAvoidingFrom G (W : Set V) A
            (radius * i + radius)).card := Finset.card_le_card hsemigroup
        _ = (ballAvoidingFrom G (W : Set V) A
            (radius * (i + 1))).card := by ring_nf
    obtain ⟨B, hBA, hBcard, hBball⟩ :=
      exists_half_centres_with_large_ball G (W : Set V) A
        (radius * (i + 1)) K hbig
    have hBbound : B.card ≤ schedule.centers (i + 1) := by
      calc
        B.card ≤ (A.card + 1) / 2 := hBcard
        _ ≤ (schedule.centers i + 1) / 2 :=
          Nat.div_le_div_right (Nat.add_le_add_right hAcard 1)
        _ ≤ schedule.centers (i + 1) := schedule.step i hilt
    have hPnext : P (i + 1) :=
      ⟨B, hBA.trans hAW, hBbound, hBball⟩
    have hmax := Nat.le_findGreatest (P := P) (Nat.succ_le_iff.2 hilt) hPnext
    omega
  obtain ⟨root, hrootA⟩ := hAne
  have hAeq : A = {root} := by
    apply Finset.eq_singleton_iff_unique_mem.2
    exact ⟨hrootA, fun z hz ↦
      Finset.card_le_one.mp hAone z hz root hrootA⟩
  have hrootW : root ∉ W := (Finset.mem_sdiff.1 (hAW hrootA)).2
  have hLball : L ≤ (ballAvoiding G (W : Set V) root (radius * i)).card := by
    exact hLK.trans (by simpa [hAeq, ballAvoidingFrom] using hAball)
  let Efull := VertexExpansion.ofBallAvoiding G (W : Set V) root (radius * i)
  obtain ⟨Esmall, hsmall⟩ := Efull.proposition3_10 hLpos hLball
  have hirad : radius * i ≤ m :=
    (Nat.mul_le_mul_left radius hirounds).trans hradius
  let E : VertexExpansion G root L m := Esmall.radiusMono hirad
  refine ⟨root, E, ?_⟩
  rw [Finset.disjoint_left]
  intro z hzE hzW
  have hzball : z ∈ ballAvoiding G (W : Set V) root (radius * i) :=
    hsmall (by simpa [E] using hzE)
  have hzReach :=
    (mem_ballAvoiding G (W : Set V) root (radius * i) z).1 hzball
  rcases hzReach.eq_root_or_not_mem with rfl | hznot
  · exact hrootW hzW
  · exact hznot hzW

/-! ## Concrete set and root connectors -/

private theorem exists_short_set_connector [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (epsilon kappa : ℝ)
    (hexp : IsLMExpander G epsilon kappa)
    (degreeScale : ℕ) (hdegree : ∀ v : V, degreeScale ≤ G.degree v)
    (W A B : Finset V) (start workspace radius : ℕ)
    (hW : W.card ≤ workspace)
    (hAW : Disjoint A W) (hBW : Disjoint B W)
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hAseed : start ≤ A.card ∨ start + workspace ≤ degreeScale)
    (hBseed : start ≤ B.card ∨ start + workspace ≤ degreeScale)
    (growth : BallGrowthSchedule G epsilon kappa start workspace radius) :
    ∃ a ∈ A, ∃ b ∈ B, ∃ p : G.Walk a b,
      p.IsAvoidingPath (W : Set V) ({a, b} : Set V) ∧
        p.length ≤ 2 * (radius + 1) := by
  have hAball := growth.grow_one_more hexp hdegree W A hW hAW hA hAseed
  have hBball := growth.grow_one_more hexp hdegree W B hW hBW hB hBseed
  obtain ⟨a, ha, b, hb, p, hp, hplen⟩ :=
    exists_avoiding_path_between_of_large_balls
      G (W : Set V) A B (radius + 1) (radius + 1) (by omega)
  exact ⟨a, ha, b, hb, p, hp, by omega⟩

private theorem exists_path_to_first_entry [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (epsilon kappa : ℝ)
    (hexp : IsLMExpander G epsilon kappa)
    (degreeScale : ℕ) (hdegree : ∀ v : V, degreeScale ≤ G.degree v)
    {x y : V} {D L rE : ℕ}
    (E : VertexExpansion G x D rE)
    (F : VertexExpansion G y L rE)
    (W : Finset V) (workspace radius : ℕ)
    (hEW : Disjoint E.verts W) (hFW : Disjoint F.verts W)
    (hEF : Disjoint E.verts F.verts)
    (hW : W.card ≤ workspace)
    (start : ℕ)
    (hDseed : start ≤ D ∨ start + workspace ≤ degreeScale)
    (hLseed : start ≤ L ∨ start + workspace ≤ degreeScale)
    (growth : BallGrowthSchedule G epsilon kappa start workspace radius) :
    ∃ b ∈ F.verts, ∃ p : G.Walk x b,
      p.IsPath ∧ p.Avoids (W : Set V) (∅ : Set V) ∧
        p.length ≤ rE + 2 * (radius + 1) ∧
        (∀ z : V, z ∈ p.support → z ∈ F.verts → z = b) := by
  let originalDecAdj : DecidableRel G.Adj := inferInstance
  classical
  letI : DecidableRel G.Adj := originalDecAdj
  obtain ⟨a, ha, b0, hb0, raw, hraw, hrawlen⟩ :=
    exists_short_set_connector G epsilon kappa hexp degreeScale hdegree
      W E.verts F.verts start workspace radius hW hEW hFW
      ⟨x, E.root_mem⟩ ⟨y, F.root_mem⟩
      (hDseed.imp (fun h ↦ by simpa [E.card_verts] using h) id)
      (hLseed.imp (fun h ↦ by simpa [F.card_verts] using h) id) growth
  obtain ⟨px, hpx, hpxlen, hpxsupp⟩ := E.exists_path ha
  let w : G.Walk x b0 := px.append raw
  have hrawEmpty : raw.Avoids (W : Set V) (∅ : Set V) := by
    apply Walk.avoids_empty_of_endpoints_outside hraw.2
    · exact fun haW ↦ Finset.disjoint_left.1 hEW ha haW
    · exact fun hbW ↦ Finset.disjoint_left.1 hFW hb0 hbW
  have hwEmpty : w.Avoids (W : Set V) (∅ : Set V) := by
    intro z hz hzW
    change z ∈ (px.append raw).support at hz
    rw [Walk.mem_support_append_iff] at hz
    rcases hz with hz | hz
    · exact (Finset.disjoint_left.1 hEW
        (hpxsupp z hz) hzW).elim
    · exact hrawEmpty z hz hzW
  obtain ⟨b, hbF, p, hp, hplen, hpsub, hfirst⟩ :=
    exists_first_entry_prefix w.bypass w.bypass_isPath F.verts (by
      simpa using hb0)
  refine ⟨b, hbF, p, hp, ?_, ?_, hfirst⟩
  · intro z hz hzW
    exact hwEmpty z (w.support_bypass_subset_support (hpsub hz)) hzW
  · calc
      p.length ≤ w.bypass.length := hplen
      _ ≤ w.length := w.length_bypass_le_length
      _ = px.length + raw.length := by simp [w]
      _ ≤ rE + 2 * (radius + 1) := Nat.add_le_add hpxlen hrawlen

/-! ## Enlarging four prescribed expansions (Lemma 3.13) -/

/-- The purely numerical assumptions shared by Lemmas 3.12--3.15.  The
parameter `D` is the order of the prescribed small expansions and `L` the
order of the enlarged expansions. -/
structure LM315Numerics [Fintype V] (G : SimpleGraph V)
    (epsilon kappa : ℝ)
    (D K L m freshRadius pathRadius rounds freshWorkspace pathWorkspace : ℕ) where
  /-- The small seed used only for the source-to-reservoir routing in
  Lemma 3.13.  It is deliberately independent of the bulk scale `K`. -/
  routeStart : ℕ
  /-- The minimum-degree scale used by the radius-one bootstrap. -/
  degreeScale : ℕ
  /-- The expander-scale seed for the long-path connectors. -/
  pathStart : ℕ
  /-- Workspace for the short routing arms.  It is separate from
  `pathWorkspace`, which must also accommodate the much longer path in
  Lemma 3.14. -/
  routeWorkspace : ℕ
  schedule : HalvingSchedule K rounds
  room : freshWorkspace + K ≤ Fintype.card V
  D_pos : 0 < D
  K_pos : 0 < K
  L_pos : 0 < L
  m_pos : 0 < m
  routeStart_pos : 0 < routeStart
  L_le_K : L ≤ K
  growth_path :
    BallGrowthSchedule G epsilon kappa pathStart pathWorkspace pathRadius
  growth_route :
    BallGrowthSchedule G epsilon kappa routeStart routeWorkspace pathRadius
  growth_K : BallGrowthSchedule G epsilon kappa K freshWorkspace freshRadius
  route_source_survives : 1 + routeWorkspace ≤ D
  route_target_survives : 1 + routeWorkspace ≤ L
  route_source_seed :
    routeStart + routeWorkspace ≤ D ∨
      routeStart + routeWorkspace ≤ degreeScale
  route_target_seed :
    routeStart + routeWorkspace ≤ L ∨
      routeStart + routeWorkspace ≤ degreeScale
  path_seed : pathStart ≤ L ∨ pathStart + pathWorkspace ≤ degreeScale
  halve : 2 * K ≤ Fintype.card V / 2 + 1
  fresh_radius : 2 * (freshRadius * rounds) ≤ m
  connector_radius : 2 * (pathRadius + 1) ≤ m

namespace LM315Numerics

variable [Fintype V]
variable {epsilon kappa : ℝ}
variable {D K L m freshRadius pathRadius rounds freshWorkspace pathWorkspace : ℕ}

theorem fresh_radius_le
    (N : LM315Numerics G epsilon kappa D K L m freshRadius pathRadius rounds
      freshWorkspace pathWorkspace) :
    freshRadius * rounds ≤ m := by
  exact (Nat.le_mul_of_pos_left (freshRadius * rounds)
    (by omega : 0 < 2)).trans N.fresh_radius

end LM315Numerics

/-- Construct a finite family of pairwise disjoint fresh expansions.  The
large bulk scale `K` is what makes paying for the previously constructed
members numerically possible. -/
private theorem exists_fresh_expansion_family [Fintype V]
    (G : SimpleGraph V) (epsilon kappa : ℝ)
    (hexp : IsLMExpander G epsilon kappa)
    {K L radius rounds freshWorkspace : ℕ}
    (base : Finset V) (t : ℕ)
    (schedule : HalvingSchedule K rounds)
    (growth : BallGrowthSchedule G epsilon kappa K freshWorkspace radius)
    (hbudget : base.card + t * L ≤ freshWorkspace)
    (hroom : freshWorkspace + K ≤ Fintype.card V)
    (hKpos : 0 < K) (hLpos : 0 < L) (hLK : L ≤ K)
    (hhalve : 2 * K ≤ Fintype.card V / 2 + 1) :
    ∃ root : Fin t → V,
      ∃ B : ∀ i : Fin t, VertexExpansion G (root i) L (radius * rounds),
        (∀ i : Fin t, Disjoint (B i).verts base) ∧
        (((Finset.univ : Finset (Fin t)) : Set (Fin t)).PairwiseDisjoint
          fun i ↦ (B i).verts) := by
  classical
  induction t with
  | zero =>
      exact ⟨fun i ↦ Fin.elim0 i, fun i ↦ Fin.elim0 i,
        fun i ↦ Fin.elim0 i, fun i ↦ Fin.elim0 i⟩
  | succ t ih =>
      have hbudgetOld : base.card + t * L ≤ freshWorkspace := by
        exact (Nat.add_le_add_left
          (Nat.mul_le_mul_right L (Nat.le_succ t)) base.card).trans hbudget
      obtain ⟨rootOld, BOld, hOldBase, hOldPair⟩ := ih hbudgetOld
      let oldVerts := Finset.univ.biUnion fun i : Fin t ↦ (BOld i).verts
      have holdCard : oldVerts.card ≤ t * L := by
        calc
          oldVerts.card ≤ ∑ i ∈ (Finset.univ : Finset (Fin t)), (BOld i).verts.card :=
            Finset.card_biUnion_le
          _ = t * L := by simp [VertexExpansion.card_verts]
      let W := base ∪ oldVerts
      have hW : W.card ≤ freshWorkspace := by
        have hu := Finset.card_union_le base oldVerts
        dsimp [W]
        omega
      obtain ⟨rNew, BNew, hNewW⟩ := liuMontgomery_lemma3_12_finite
        G epsilon kappa hexp W freshWorkspace K L radius rounds (radius * rounds)
          schedule growth hW hroom hKpos hLpos hLK hhalve le_rfl
      let root : Fin (t + 1) → V :=
        fun i ↦ Fin.cases rNew rootOld i
      let B : ∀ i : Fin (t + 1),
          VertexExpansion G (root i) L (radius * rounds) :=
        fun i ↦ Fin.cases
          (by simpa [root] using BNew)
          (fun j ↦ by simpa [root] using BOld j) i
      refine ⟨root, B, ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · change Disjoint BNew.verts base
          exact hNewW.mono_right Finset.subset_union_left
        · change Disjoint (BOld j).verts base
          exact hOldBase j
      · intro i hi j hj
        clear hi hj
        change i ≠ j → Disjoint (B i).verts (B j).verts
        revert j
        refine Fin.cases ?_ (fun i' ↦ ?_) i
        · intro j
          refine Fin.cases ?_ (fun j' ↦ ?_) j
          · intro hij
            exact (hij rfl).elim
          · intro _
            change Disjoint BNew.verts (BOld j').verts
            apply hNewW.mono_right
            intro z hz
            apply Finset.mem_union_right
            change z ∈ (Finset.univ.biUnion fun a : Fin t ↦ (BOld a).verts)
            rw [Finset.mem_biUnion]
            exact ⟨j', by simp, hz⟩
        · intro j
          refine Fin.cases ?_ (fun j' ↦ ?_) j
          · intro _
            change Disjoint (BOld i').verts BNew.verts
            apply (hNewW.mono_right ?_).symm
            intro z hz
            apply Finset.mem_union_right
            change z ∈ (Finset.univ.biUnion fun a : Fin t ↦ (BOld a).verts)
            rw [Finset.mem_biUnion]
            exact ⟨i', by simp, hz⟩
          · intro hij
            change Disjoint (BOld i').verts (BOld j').verts
            exact hOldPair (by simp) (by simp) (by
              intro h
              apply hij
              exact congrArg Fin.succ h)

/-- A maximal conflict-free family exists when candidates have keys in a
finite type and equal keys force a conflict.  The candidate type itself need
not be finite. -/
theorem exists_finite_maximal_conflictFree_family
    {Candidate Key : Type*} [Fintype Key]
    (key : Candidate → Key) (Conflict : Candidate → Candidate → Prop)
    (hsame : ∀ a b, key a = key b → Conflict a b)
    (hsymm : ∀ a b, Conflict a b → Conflict b a) :
    ∃ S : Finset Candidate,
      ((S : Set Candidate).Pairwise fun a b ↦ ¬ Conflict a b) ∧
        ∀ a : Candidate, ∃ b ∈ S, Conflict a b := by
  classical
  have aux : ∀ keys : Finset Key, ∃ S : Finset Candidate,
      ((S : Set Candidate).Pairwise fun a b ↦ ¬ Conflict a b) ∧
      (∀ a : Candidate, key a ∈ keys → ∃ b ∈ S, Conflict a b) := by
    intro keys
    induction keys using Finset.induction with
    | empty =>
        refine ⟨∅, ?_, ?_⟩
        · simp
        · intro a ha
          simp at ha
    | @insert k keys hk ih =>
        obtain ⟨S, hSpair, hSmax⟩ := ih
        by_cases hnew : ∃ a : Candidate,
            key a = k ∧ ∀ b ∈ S, ¬ Conflict a b
        · obtain ⟨a, hakey, haconflict⟩ := hnew
          refine ⟨insert a S, ?_, ?_⟩
          · intro x hx y hy hxy
            simp only [Finset.coe_insert, Set.mem_insert_iff] at hx hy
            rcases hx with rfl | hx <;> rcases hy with rfl | hy
            · exact (hxy rfl).elim
            · exact haconflict y hy
            · intro hxa
              exact haconflict x hx (hsymm _ _ hxa)
            · exact hSpair hx hy hxy
          · intro x hxkey
            rw [Finset.mem_insert] at hxkey
            rcases hxkey with hxk | hxkeys
            · refine ⟨a, Finset.mem_insert_self a S, ?_⟩
              exact hsame x a (hxk.trans hakey.symm)
            · obtain ⟨b, hbS, hxb⟩ := hSmax x hxkeys
              exact ⟨b, Finset.mem_insert_of_mem hbS, hxb⟩
        · refine ⟨S, hSpair, ?_⟩
          intro a hakeys
          rw [Finset.mem_insert] at hakeys
          rcases hakeys with hak | hakeys
          · have hnotall : ¬ ∀ b ∈ S, ¬ Conflict a b := by
              intro hall
              exact hnew ⟨a, hak, hall⟩
            push_neg at hnotall
            obtain ⟨b, hbS, hab⟩ := hnotall
            exact ⟨b, hbS, hab⟩
          · exact hSmax a hakeys
  obtain ⟨S, hpair, hmax⟩ := aux (Finset.univ : Finset Key)
  exact ⟨S, hpair, fun a ↦ hmax a (Finset.mem_univ _)⟩

/-! ### Short set connectors with lower cardinality bounds -/

/-- Variant of the connector in `Lemma315` in which both endpoint sets are
only required to have cardinality at least the schedule's starting size. -/
theorem exists_short_set_connector_ge [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (epsilon kappa : ℝ)
    (hexp : IsLMExpander G epsilon kappa)
    (degreeScale : ℕ) (hdegree : ∀ v : V, degreeScale ≤ G.degree v)
    (W A B : Finset V) (start workspace radius : ℕ)
    (hW : W.card ≤ workspace)
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hAseed : start ≤ A.card ∨ start + workspace ≤ degreeScale)
    (hBseed : start ≤ B.card ∨ start + workspace ≤ degreeScale)
    (hAW : Disjoint A W) (hBW : Disjoint B W)
    (growth : BallGrowthSchedule G epsilon kappa start workspace radius) :
    ∃ a ∈ A, ∃ b ∈ B, ∃ p : G.Walk a b,
      p.IsPath ∧ p.Avoids (W : Set V) (∅ : Set V) ∧
        p.length ≤ 2 * (radius + 1) := by
  obtain ⟨a, ha, b, hb, p, hp, hplen⟩ :=
    exists_short_set_connector G epsilon kappa hexp degreeScale hdegree
      W A B start workspace radius hW hAW hBW hA hB hAseed hBseed growth
  have hpempty : p.Avoids (W : Set V) (∅ : Set V) := by
    apply Walk.avoids_empty_of_endpoints_outside hp.2
    · exact fun haW ↦ Finset.disjoint_left.1 hAW ha haW
    · exact fun hbW ↦ Finset.disjoint_left.1 hBW hb hbW
  exact ⟨a, ha, b, hb, p, hp.1, hpempty, hplen⟩

structure RawArm [Fintype V] (G : SimpleGraph V)
    (source forbidden : Finset V) (target : Key → Finset V)
    (keys : Finset Key) (m : ℕ) where
  key : Key
  key_mem : key ∈ keys
  start : V
  finish : V
  start_mem : start ∈ source
  finish_mem : finish ∈ target key
  path : G.Walk start finish
  isPath : path.IsPath
  length_le : path.length ≤ m
  avoids : path.Avoids (forbidden : Set V) (∅ : Set V)
  only_start_in_source :
    ∀ z : V, z ∈ path.support → z ∈ source → z = start

namespace RawArm

variable [Fintype V]
variable {source forbidden : Finset V} {target : Key → Finset V}
variable {keys : Finset Key} {m : ℕ}

/-- The vertices of the arm outside its common source. -/
noncomputable def external
    (A : RawArm G source forbidden target keys m) : Finset V :=
  A.path.support.toFinset \ source

theorem external_subset_support
    (A : RawArm G source forbidden target keys m) :
    A.external ⊆ A.path.support.toFinset := by
  exact Finset.sdiff_subset

theorem external_card_le
    (A : RawArm G source forbidden target keys m) :
    A.external.card ≤ m + 1 := by
  calc
    A.external.card ≤ A.path.support.toFinset.card :=
      Finset.card_le_card A.external_subset_support
    _ ≤ A.path.support.length := List.toFinset_card_le A.path.support
    _ = A.path.length + 1 := by simp
    _ ≤ m + 1 := Nat.add_le_add_right A.length_le 1

/-- Equal keys or intersecting external carriers are the two conflicts. -/
def Conflict
    (A B : RawArm G source forbidden target keys m) : Prop :=
  A.key = B.key ∨ ¬ Disjoint A.external B.external

theorem Conflict.symm
    {A B : RawArm G source forbidden target keys m}
    (h : Conflict A B) : Conflict B A := by
  rcases h with hkey | hinter
  · exact Or.inl hkey.symm
  · exact Or.inr fun hdisj ↦ hinter hdisj.symm

/-- A maximal pairwise externally disjoint raw-arm family. -/
theorem exists_maximal_family [Fintype Key] :
    ∃ S : Finset (RawArm G source forbidden target keys m),
      ((S : Set (RawArm G source forbidden target keys m)).Pairwise
        fun A B ↦ ¬ Conflict A B) ∧
      ∀ A : RawArm G source forbidden target keys m,
        ∃ B ∈ S, Conflict A B := by
  apply exists_finite_maximal_conflictFree_family
    (fun A : RawArm G source forbidden target keys m ↦ A.key) Conflict
  · intro A B h
    exact Or.inl h
  · intro A B h
    exact h.symm

theorem key_injOn_of_pairwise
    {S : Finset (RawArm G source forbidden target keys m)}
    (hpair : ((S : Set (RawArm G source forbidden target keys m)).Pairwise
      fun A B ↦ ¬ Conflict A B)) :
    Set.InjOn (fun A : RawArm G source forbidden target keys m ↦ A.key)
      (S : Set (RawArm G source forbidden target keys m)) := by
  intro A hAS B hBS hkey
  by_contra hAB
  exact hpair hAS hBS hAB (Or.inl hkey)

theorem card_le_keys_of_pairwise
    {S : Finset (RawArm G source forbidden target keys m)}
    (hpair : ((S : Set (RawArm G source forbidden target keys m)).Pairwise
      fun A B ↦ ¬ Conflict A B)) :
    S.card ≤ keys.card := by
  apply Finset.card_le_card_of_injOn
    (fun A : RawArm G source forbidden target keys m ↦ A.key)
  · intro A hAS
    exact A.key_mem
  · exact key_injOn_of_pairwise hpair

/-- The union of all external carriers in a finite arm family. -/
noncomputable def externalUnion
    (S : Finset (RawArm G source forbidden target keys m)) : Finset V :=
  S.biUnion external

theorem external_subset_externalUnion
    {S : Finset (RawArm G source forbidden target keys m)}
    {A : RawArm G source forbidden target keys m} (hAS : A ∈ S) :
    A.external ⊆ externalUnion S := by
  intro z hz
  exact Finset.mem_biUnion.2 ⟨A, hAS, hz⟩

theorem externalUnion_card_le
    (S : Finset (RawArm G source forbidden target keys m)) :
    (externalUnion S).card ≤ S.card * (m + 1) := by
  calc
    (externalUnion S).card ≤ ∑ A ∈ S, A.external.card := by
      exact Finset.card_biUnion_le
    _ ≤ ∑ _A ∈ S, (m + 1) :=
      Finset.sum_le_sum fun A _ ↦ A.external_card_le
    _ = S.card * (m + 1) := by simp

/-! ### Constructing a raw arm from a clean short connector -/

/-- Reverse a clean connector, stop on its first entry into `source`, and
reverse back.  The resulting arm meets `source` only at its start. -/
theorem of_connector
    (forbidden' : Finset V) (hforbidden : forbidden ⊆ forbidden')
    (k : Key) (hk : k ∈ keys)
    {a b : V} (ha : a ∈ source) (hb : b ∈ target k)
    (p : G.Walk a b) (hp : p.IsPath)
    (hpavoid : p.Avoids (forbidden' : Set V) (∅ : Set V))
    (hplen : p.length ≤ m) :
    ∃ A : RawArm G source forbidden target keys m,
      A.key = k ∧ A.external ⊆ p.support.toFinset := by
  classical
  obtain ⟨s, hs, q₀, hq₀, hq₀len, hq₀sub, hfirst⟩ :=
    exists_first_entry_prefix p.reverse hp.reverse source ha
  let q : G.Walk s b := q₀.reverse
  have hqsub : q.support ⊆ p.support := by
    intro z hz
    have hz₀ : z ∈ q₀.support := by simpa [q] using hz
    have hzrev : z ∈ p.reverse.support := hq₀sub hz₀
    simpa using hzrev
  have hqavoid' : q.Avoids (forbidden' : Set V) (∅ : Set V) := by
    intro z hz hzforbidden
    exact hpavoid z (hqsub hz) hzforbidden
  let A : RawArm G source forbidden target keys m :=
    { key := k
      key_mem := hk
      start := s
      finish := b
      start_mem := hs
      finish_mem := hb
      path := q
      isPath := hq₀.reverse
      length_le := by
        have hq₀len' : q₀.length ≤ p.length := by simpa using hq₀len
        simpa [q] using hq₀len'.trans hplen
      avoids := hqavoid'.mono_forbidden (by
        intro z hz
        exact hforbidden hz)
      only_start_in_source := by
        intro z hz hzsource
        have hz₀ : z ∈ q₀.support := by simpa [q] using hz
        exact hfirst z hz₀ hzsource }
  refine ⟨A, rfl, ?_⟩
  intro z hz
  have hzq : z ∈ q.support := by
    exact List.mem_toFinset.1 (A.external_subset_support hz)
  exact List.mem_toFinset.2 (hqsub hzq)

/-! ### Saturating all available target keys -/

/-- The source-faithful one-stage routing lemma.  The deletion paid to the
ball-growth argument consists only of the fixed forbidden set and the
external carriers of the already selected arms.  Neither `source` nor any
target is charged to the workspace.

The two reserve inequalities are simple cardinal forms of the source
estimates `D-|W| >= x` and `|B_k|-|W| >= x`. -/
theorem exists_saturated_family
    [Fintype Key] [DecidableRel G.Adj]
    (epsilon kappa : ℝ) (hexp : IsLMExpander G epsilon kappa)
    (degreeScale : ℕ) (hdegree : ∀ v : V, degreeScale ≤ G.degree v)
    (start workspace radius : ℕ)
    (growth : BallGrowthSchedule G epsilon kappa start workspace radius)
    (hstart : 0 < start)
    (hradius : 2 * (radius + 1) ≤ m)
    (hfixed : forbidden.card + keys.card * (m + 1) ≤ workspace)
    (hsourceSurvives : 1 + workspace ≤ source.card)
    (htargetSurvives : ∀ k ∈ keys, 1 + workspace ≤ (target k).card)
    (hsourceSeed : start + workspace ≤ source.card ∨
      start + workspace ≤ degreeScale)
    (htargetSeed : ∀ k ∈ keys, start + workspace ≤ (target k).card ∨
      start + workspace ≤ degreeScale) :
    ∃ S : Finset (RawArm G source forbidden target keys m),
      ((S : Set (RawArm G source forbidden target keys m)).Pairwise
        fun A B ↦ ¬ Conflict A B) ∧
      S.image (fun A ↦ A.key) = keys ∧
      S.card = keys.card := by
  let originalDecAdj : DecidableRel G.Adj := inferInstance
  classical
  letI : DecidableRel G.Adj := originalDecAdj
  obtain ⟨S, hpair, hmax⟩ :=
    (exists_maximal_family
      (G := G) (source := source) (forbidden := forbidden)
      (target := target) (keys := keys) (m := m))
  have hScard : S.card ≤ keys.card := card_le_keys_of_pairwise hpair
  have hImageSubset : S.image (fun A ↦ A.key) ⊆ keys := by
    intro k hk
    obtain ⟨A, hAS, rfl⟩ := Finset.mem_image.1 hk
    exact A.key_mem
  have hKeysSubset : keys ⊆ S.image (fun A ↦ A.key) := by
    intro k hk
    by_contra hkImage
    let used : Finset V := forbidden ∪ externalUnion S
    have husedCard : used.card ≤ workspace := by
      have hunion := Finset.card_union_le forbidden (externalUnion S)
      have hext := externalUnion_card_le S
      have hmul : S.card * (m + 1) ≤ keys.card * (m + 1) :=
        Nat.mul_le_mul_right (m + 1) hScard
      dsimp [used]
      omega
    have hsourceNonempty : (source \ used).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      have hzero : (source \ used).card = 0 := by simp [hempty]
      have hinter : (source ∩ used).card ≤ used.card :=
        Finset.card_le_card Finset.inter_subset_right
      have hdecomp := Finset.card_sdiff_add_card_inter source used
      omega
    have htargetNonempty : (target k \ used).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      have hzero : (target k \ used).card = 0 := by simp [hempty]
      have hinter : (target k ∩ used).card ≤ used.card :=
        Finset.card_le_card Finset.inter_subset_right
      have hdecomp := Finset.card_sdiff_add_card_inter (target k) used
      have hsurvive := htargetSurvives k hk
      omega
    have hsourceCard : start ≤ (source \ used).card ∨
        start + workspace ≤ degreeScale := by
      rcases hsourceSeed with hdirect | hbootstrap
      · left
        have hinter : (source ∩ used).card ≤ used.card :=
          Finset.card_le_card Finset.inter_subset_right
        have hdecomp := Finset.card_sdiff_add_card_inter source used
        omega
      · exact Or.inr hbootstrap
    have htargetCard : start ≤ (target k \ used).card ∨
        start + workspace ≤ degreeScale := by
      rcases htargetSeed k hk with hdirect | hbootstrap
      · left
        have hinter : (target k ∩ used).card ≤ used.card :=
          Finset.card_le_card Finset.inter_subset_right
        have hdecomp := Finset.card_sdiff_add_card_inter (target k) used
        omega
      · exact Or.inr hbootstrap
    have hSourceUsed : Disjoint (source \ used) used := by
      exact (Finset.disjoint_sdiff (s := used) (t := source)).symm
    have hTargetUsed : Disjoint (target k \ used) used := by
      exact (Finset.disjoint_sdiff (s := used) (t := target k)).symm
    obtain ⟨a, ha, b, hb, p, hp, hpavoid, hplen⟩ :=
      exists_short_set_connector_ge G epsilon kappa hexp degreeScale hdegree used
        (source \ used) (target k \ used) start workspace radius
        husedCard hsourceNonempty htargetNonempty hsourceCard htargetCard
        hSourceUsed hTargetUsed growth
    obtain ⟨A, hAkey, hAexternal⟩ :=
      of_connector used Finset.subset_union_left k hk
        (Finset.sdiff_subset ha) (Finset.sdiff_subset hb)
        p hp hpavoid (hplen.trans hradius)
    have hAconflict : ∀ B ∈ S, ¬ Conflict A B := by
      intro B hBS hconflict
      rcases hconflict with hkey | hinter
      · apply hkImage
        apply Finset.mem_image.2
        exact ⟨B, hBS, hkey.symm.trans hAkey⟩
      · apply hinter
        rw [Finset.disjoint_left]
        intro z hzA hzB
        have hzP : z ∈ p.support.toFinset := hAexternal hzA
        have hzUsed : z ∈ used := by
          exact Finset.mem_union_right _
            (external_subset_externalUnion hBS hzB)
        exact hpavoid z (by simpa using hzP) hzUsed
    obtain ⟨B, hBS, hAB⟩ := hmax A
    exact hAconflict B hBS hAB
  have hImage : S.image (fun A ↦ A.key) = keys :=
    Finset.Subset.antisymm hImageSubset hKeysSubset
  have hKeysCardLe : keys.card ≤ S.card := by
    calc
      keys.card = (S.image (fun A ↦ A.key)).card := congrArg Finset.card hImage.symm
      _ ≤ S.card := Finset.card_image_le
  exact ⟨S, hpair, hImage, Nat.le_antisymm hScard hKeysCardLe⟩

end RawArm

/-! ### Aggregate four-product selection -/

/-- If each arm has at most `q` bad targets in the union of the other three
blocks, then fewer than all four-tuples are bad as soon as
`4*q*M^3 < M^4`.  Crucially, the three destination blocks are aggregated
before applying the degree bound. -/
theorem exists_good_four_of_total_bad_degree
    {α : Type*} [DecidableEq α]
    (C₀ C₁ C₂ C₃ : Finset α) (Bad : α → α → Prop)
    (M q : ℕ)
    (h₀ : C₀.card = M) (h₁ : C₁.card = M)
    (h₂ : C₂.card = M) (h₃ : C₃.card = M)
    (hout₀ : ∀ a ∈ C₀,
      (C₁.filter (Bad a)).card + (C₂.filter (Bad a)).card +
        (C₃.filter (Bad a)).card ≤ q)
    (hout₁ : ∀ a ∈ C₁,
      (C₀.filter (Bad a)).card + (C₂.filter (Bad a)).card +
        (C₃.filter (Bad a)).card ≤ q)
    (hout₂ : ∀ a ∈ C₂,
      (C₀.filter (Bad a)).card + (C₁.filter (Bad a)).card +
        (C₃.filter (Bad a)).card ≤ q)
    (hout₃ : ∀ a ∈ C₃,
      (C₀.filter (Bad a)).card + (C₁.filter (Bad a)).card +
        (C₂.filter (Bad a)).card ≤ q)
    (hsmall : 4 * q * M ^ 3 < M ^ 4) :
    ∃ a₀ ∈ C₀, ∃ a₁ ∈ C₁, ∃ a₂ ∈ C₂, ∃ a₃ ∈ C₃,
      ¬ Bad a₀ a₁ ∧ ¬ Bad a₀ a₂ ∧ ¬ Bad a₀ a₃ ∧
      ¬ Bad a₁ a₀ ∧ ¬ Bad a₁ a₂ ∧ ¬ Bad a₁ a₃ ∧
      ¬ Bad a₂ a₀ ∧ ¬ Bad a₂ a₁ ∧ ¬ Bad a₂ a₃ ∧
      ¬ Bad a₃ a₀ ∧ ¬ Bad a₃ a₁ ∧ ¬ Bad a₃ a₂ := by
  classical
  have sourceBound (S T U Z : Finset α)
      (hS : S.card = M) (hT : T.card = M)
      (hU : U.card = M) (hZ : Z.card = M)
      (hout : ∀ a ∈ S,
        (T.filter (Bad a)).card + (U.filter (Bad a)).card +
          (Z.filter (Bad a)).card ≤ q) :
      ((S ×ˢ (T ×ˢ (U ×ˢ Z))).filter fun x ↦
        Bad x.1 x.2.1 ∨ Bad x.1 x.2.2.1 ∨ Bad x.1 x.2.2.2).card ≤
        q * M ^ 3 := by
    let hitT := fun a ↦ T.filter (Bad a)
    let hitU := fun a ↦ U.filter (Bad a)
    let hitZ := fun a ↦ Z.filter (Bad a)
    let fiber := fun a ↦
      (hitT a ×ˢ (U ×ˢ Z)) ∪
        (T ×ˢ (hitU a ×ˢ Z)) ∪
          (T ×ˢ (U ×ˢ hitZ a))
    let cover : Finset (α × (α × (α × α))) :=
      S.biUnion fun a ↦ (fiber a).image fun y ↦ (a, y)
    have hsub :
        ((S ×ˢ (T ×ˢ (U ×ˢ Z))).filter fun x ↦
          Bad x.1 x.2.1 ∨ Bad x.1 x.2.2.1 ∨ Bad x.1 x.2.2.2) ⊆ cover := by
      intro x hx
      obtain ⟨hxΩ, hbad⟩ := Finset.mem_filter.1 hx
      obtain ⟨hxS, hxT, hxU, hxZ⟩ :
          x.1 ∈ S ∧ x.2.1 ∈ T ∧ x.2.2.1 ∈ U ∧ x.2.2.2 ∈ Z := by
        simpa only [Finset.mem_product] using hxΩ
      apply Finset.mem_biUnion.2
      refine ⟨x.1, hxS, Finset.mem_image.2 ⟨x.2, ?_, rfl⟩⟩
      rcases hbad with hbad | hbad | hbad
      · exact Finset.mem_union.2 <| Or.inl <| Finset.mem_union.2 <| Or.inl <|
          Finset.mem_product.2 ⟨Finset.mem_filter.2 ⟨hxT, hbad⟩,
            Finset.mem_product.2 ⟨hxU, hxZ⟩⟩
      · exact Finset.mem_union.2 <| Or.inl <| Finset.mem_union.2 <| Or.inr <|
          Finset.mem_product.2 ⟨hxT,
            Finset.mem_product.2 ⟨Finset.mem_filter.2 ⟨hxU, hbad⟩, hxZ⟩⟩
      · exact Finset.mem_union.2 <| Or.inr <|
          Finset.mem_product.2 ⟨hxT,
            Finset.mem_product.2 ⟨hxU, Finset.mem_filter.2 ⟨hxZ, hbad⟩⟩⟩
    have hfiber : ∀ a ∈ S, (fiber a).card ≤ q * M ^ 2 := by
      intro a ha
      let X := hitT a ×ˢ (U ×ˢ Z)
      let Y := T ×ˢ (hitU a ×ˢ Z)
      let Q := T ×ˢ (U ×ˢ hitZ a)
      have hXY := Finset.card_union_le X Y
      have hXYZ := Finset.card_union_le (X ∪ Y) Q
      have hdeg := hout a ha
      change (X ∪ Y ∪ Q).card ≤ q * M ^ 2
      calc
        (X ∪ Y ∪ Q).card ≤ (X ∪ Y).card + Q.card := hXYZ
        _ ≤ (X.card + Y.card) + Q.card :=
          Nat.add_le_add_right hXY Q.card
        _ = ((hitT a).card + (hitU a).card + (hitZ a).card) * M ^ 2 := by
          simp only [X, Y, Q, Finset.card_product, hT, hU, hZ]
          ring
        _ ≤ q * M ^ 2 := Nat.mul_le_mul_right (M ^ 2) hdeg
    calc
      ((S ×ˢ (T ×ˢ (U ×ˢ Z))).filter fun x ↦
          Bad x.1 x.2.1 ∨ Bad x.1 x.2.2.1 ∨ Bad x.1 x.2.2.2).card
          ≤ cover.card := Finset.card_le_card hsub
      _ ≤ ∑ a ∈ S, ((fiber a).image fun y ↦ (a, y)).card := by
        dsimp [cover]
        exact Finset.card_biUnion_le
      _ ≤ ∑ a ∈ S, (fiber a).card :=
        Finset.sum_le_sum fun _ _ ↦ Finset.card_image_le
      _ ≤ ∑ _a ∈ S, q * M ^ 2 :=
        Finset.sum_le_sum fun a ha ↦ hfiber a ha
      _ = S.card * (q * M ^ 2) := by simp
      _ = q * M ^ 3 := by rw [hS]; ring
  let Ω := C₀ ×ˢ (C₁ ×ˢ (C₂ ×ˢ C₃))
  let RawBad₀ := Ω.filter fun x ↦
    Bad x.1 x.2.1 ∨ Bad x.1 x.2.2.1 ∨ Bad x.1 x.2.2.2
  let Ω₁ := C₁ ×ˢ (C₀ ×ˢ (C₂ ×ˢ C₃))
  let RawBad₁ := Ω₁.filter fun x ↦
    Bad x.1 x.2.1 ∨ Bad x.1 x.2.2.1 ∨ Bad x.1 x.2.2.2
  let Ω₂ := C₂ ×ˢ (C₀ ×ˢ (C₁ ×ˢ C₃))
  let RawBad₂ := Ω₂.filter fun x ↦
    Bad x.1 x.2.1 ∨ Bad x.1 x.2.2.1 ∨ Bad x.1 x.2.2.2
  let Ω₃ := C₃ ×ˢ (C₀ ×ˢ (C₁ ×ˢ C₂))
  let RawBad₃ := Ω₃.filter fun x ↦
    Bad x.1 x.2.1 ∨ Bad x.1 x.2.2.1 ∨ Bad x.1 x.2.2.2
  let Bad₀ := RawBad₀
  let Bad₁ := RawBad₁.image fun x ↦
    (x.2.1, (x.1, (x.2.2.1, x.2.2.2)))
  let Bad₂ := RawBad₂.image fun x ↦
    (x.2.1, (x.2.2.1, (x.1, x.2.2.2)))
  let Bad₃ := RawBad₃.image fun x ↦
    (x.2.1, (x.2.2.1, (x.2.2.2, x.1)))
  have hb₀ : Bad₀.card ≤ q * M ^ 3 := by
    exact sourceBound C₀ C₁ C₂ C₃ h₀ h₁ h₂ h₃ hout₀
  have hb₁ : Bad₁.card ≤ q * M ^ 3 := by
    exact Finset.card_image_le.trans
      (sourceBound C₁ C₀ C₂ C₃ h₁ h₀ h₂ h₃ hout₁)
  have hb₂ : Bad₂.card ≤ q * M ^ 3 := by
    exact Finset.card_image_le.trans
      (sourceBound C₂ C₀ C₁ C₃ h₂ h₀ h₁ h₃ hout₂)
  have hb₃ : Bad₃.card ≤ q * M ^ 3 := by
    exact Finset.card_image_le.trans
      (sourceBound C₃ C₀ C₁ C₂ h₃ h₀ h₁ h₂ hout₃)
  let AllBad := Bad₀ ∪ Bad₁ ∪ Bad₂ ∪ Bad₃
  have hAllBad : AllBad.card ≤ 4 * (q * M ^ 3) := by
    dsimp [AllBad]
    calc
      (Bad₀ ∪ Bad₁ ∪ Bad₂ ∪ Bad₃).card ≤
          (Bad₀ ∪ Bad₁ ∪ Bad₂).card + Bad₃.card := Finset.card_union_le _ _
      _ ≤ ((Bad₀ ∪ Bad₁).card + Bad₂.card) + Bad₃.card :=
        Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ ≤ (((Bad₀.card + Bad₁.card) + Bad₂.card) + Bad₃.card) :=
        Nat.add_le_add_right
          (Nat.add_le_add_right (Finset.card_union_le _ _) _) _
      _ ≤ 4 * (q * M ^ 3) := by omega
  have hΩ : Ω.card = M ^ 4 := by
    simp only [Ω, Finset.card_product, h₀, h₁, h₂, h₃]
    ring
  have hAllBadLt : AllBad.card < Ω.card := by
    rw [hΩ]
    exact hAllBad.trans_lt (by simpa [Nat.mul_assoc] using hsmall)
  have hnsub : ¬ Ω ⊆ AllBad := by
    intro hsub
    exact (Nat.not_le_of_gt hAllBadLt) (Finset.card_le_card hsub)
  obtain ⟨x, hxΩ, hxGood⟩ := Finset.not_subset.mp hnsub
  rcases x with ⟨a₀, a₁, a₂, a₃⟩
  obtain ⟨ha₀, ha₁, ha₂, ha₃⟩ :
      a₀ ∈ C₀ ∧ a₁ ∈ C₁ ∧ a₂ ∈ C₂ ∧ a₃ ∈ C₃ := by
    simpa only [Ω, Finset.mem_product] using hxΩ
  have hnot₀ : (a₀, (a₁, (a₂, a₃))) ∉ Bad₀ := by
    intro h
    exact hxGood (by simp [AllBad, h])
  have hnot₁ : (a₀, (a₁, (a₂, a₃))) ∉ Bad₁ := by
    intro h
    exact hxGood (by simp [AllBad, h])
  have hnot₂ : (a₀, (a₁, (a₂, a₃))) ∉ Bad₂ := by
    intro h
    exact hxGood (by simp [AllBad, h])
  have hnot₃ : (a₀, (a₁, (a₂, a₃))) ∉ Bad₃ := by
    intro h
    exact hxGood (by simp [AllBad, h])
  have hg₀ : ¬ (Bad a₀ a₁ ∨ Bad a₀ a₂ ∨ Bad a₀ a₃) := by
    intro h
    exact hnot₀ (Finset.mem_filter.2 ⟨hxΩ, h⟩)
  have hg₁ : ¬ (Bad a₁ a₀ ∨ Bad a₁ a₂ ∨ Bad a₁ a₃) := by
    intro h
    apply hnot₁
    exact Finset.mem_image.2 ⟨(a₁, (a₀, (a₂, a₃))),
      Finset.mem_filter.2 ⟨by simp [Ω₁, ha₀, ha₁, ha₂, ha₃], h⟩, rfl⟩
  have hg₂ : ¬ (Bad a₂ a₀ ∨ Bad a₂ a₁ ∨ Bad a₂ a₃) := by
    intro h
    apply hnot₂
    exact Finset.mem_image.2 ⟨(a₂, (a₀, (a₁, a₃))),
      Finset.mem_filter.2 ⟨by simp [Ω₂, ha₀, ha₁, ha₂, ha₃], h⟩, rfl⟩
  have hg₃ : ¬ (Bad a₃ a₀ ∨ Bad a₃ a₁ ∨ Bad a₃ a₂) := by
    intro h
    apply hnot₃
    exact Finset.mem_image.2 ⟨(a₃, (a₀, (a₁, a₂))),
      Finset.mem_filter.2 ⟨by simp [Ω₃, ha₀, ha₁, ha₂, ha₃], h⟩, rfl⟩
  simp only [not_or] at hg₀ hg₁ hg₂ hg₃
  exact ⟨a₀, ha₀, a₁, ha₁, a₂, ha₂, a₃, ha₃,
    hg₀.1, hg₀.2.1, hg₀.2.2,
    hg₁.1, hg₁.2.1, hg₁.2.2,
    hg₂.1, hg₂.2.1, hg₂.2.2,
    hg₃.1, hg₃.2.1, hg₃.2.2⟩

/-- A contact set of size at most `m+1`, already containing the arm's own
target point, meets at most `m` other pairwise-disjoint keyed targets. -/
theorem card_target_hits_le
    {Arm Key₀ V₀ : Type*} [DecidableEq Arm] [DecidableEq Key₀]
    [DecidableEq V₀] [Fintype Key₀]
    (C : Finset Arm) (key : Arm → Key₀)
    (target : Key₀ → Finset V₀)
    (contact : Finset V₀) (finish : V₀) (ownKey : Key₀) (m : ℕ)
    (hkeyInj : Set.InjOn key C)
    (hkeyNe : ∀ b ∈ C, key b ≠ ownKey)
    (hTargets : ((Finset.univ : Finset Key₀) : Set Key₀).PairwiseDisjoint target)
    (hfinishContact : finish ∈ contact)
    (hfinishTarget : finish ∈ target ownKey)
    (hcontactCard : contact.card ≤ m + 1) :
    (C.filter fun b ↦ ¬ Disjoint contact (target (key b))).card ≤ m := by
  classical
  let H := C.filter fun b ↦ ¬ Disjoint contact (target (key b))
  let f := fun b : Arm ↦ contact ∩ target (key b)
  have hPair : ((H : Set Arm).PairwiseDisjoint f) := by
    intro b hb c hc hbc
    have hbC : b ∈ C := (Finset.mem_filter.1 hb).1
    have hcC : c ∈ C := (Finset.mem_filter.1 hc).1
    have hkey : key b ≠ key c := by
      intro h
      exact hbc (hkeyInj hbC hcC h)
    exact (hTargets (by simp) (by simp) hkey).mono
      Finset.inter_subset_right Finset.inter_subset_right
  have hNonempty : ∀ b ∈ H, (f b).Nonempty := by
    intro b hb
    exact Finset.not_disjoint_iff_nonempty_inter.1
      (Finset.mem_filter.1 hb).2
  have hHunion : H.card ≤ (H.biUnion f).card :=
    Finset.card_le_card_biUnion hPair hNonempty
  have hUnionSub : H.biUnion f ⊆ contact.erase finish := by
    intro z hz
    obtain ⟨b, hbH, hzf⟩ := Finset.mem_biUnion.1 hz
    obtain ⟨hzContact, hzTarget⟩ := Finset.mem_inter.1 hzf
    refine Finset.mem_erase.2 ⟨?_, hzContact⟩
    intro hzfinish
    subst z
    have hbC : b ∈ C := (Finset.mem_filter.1 hbH).1
    have hdisj : Disjoint (target ownKey) (target (key b)) :=
      hTargets (by simp) (by simp) (hkeyNe b hbC).symm
    exact Finset.disjoint_left.1 hdisj hfinishTarget hzTarget
  change H.card ≤ m
  calc
    H.card ≤ (H.biUnion f).card := hHunion
    _ ≤ (contact.erase finish).card := Finset.card_le_card hUnionSub
    _ ≤ m := by
      rw [Finset.card_erase_of_mem hfinishContact]
      omega

/-! ### Pigeonholing a saturated stage -/

/-- A saturated family whose arms are assigned to a nonempty finite set of
remaining roots contains a block of `armsPerRoot` arms assigned to one root.
This is the exact finite pigeonhole step in each of the four routing stages. -/
theorem exists_popular_owner
    {Candidate Owner : Type*} [DecidableEq Candidate] [DecidableEq Owner]
    (S : Finset Candidate) (remaining : Finset Owner)
    (owner : Candidate → Owner) (armsPerRoot : ℕ)
    (hremaining : remaining.Nonempty)
    (howner : ∀ A ∈ S, owner A ∈ remaining)
    (hcount : remaining.card * armsPerRoot ≤ S.card) :
    ∃ i ∈ remaining, ∃ T ⊆ S,
      T.card = armsPerRoot ∧ ∀ A ∈ T, owner A = i := by
  classical
  obtain ⟨i, hi, hifiber⟩ :=
    Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
      (s := S) (t := remaining) (f := owner) (n := armsPerRoot)
      howner hremaining hcount
  let fiber := S.filter fun A ↦ owner A = i
  have hfiber : armsPerRoot ≤ fiber.card := by
    simpa [fiber] using hifiber
  obtain ⟨T, hTf, hTcard⟩ := Finset.exists_subset_card_eq hfiber
  refine ⟨i, hi, T, hTf.trans (Finset.filter_subset _ _), hTcard, ?_⟩
  intro A hAT
  exact (Finset.mem_filter.1 (hTf hAT)).2

/-! ### Attaching a selected system of four arms -/

/-- The geometric output of the final four-tuple selection.  Every
cross-intersection needed for attaching the large targets is stated
literally. -/
structure SelectedFourArmSystem [Fintype V]
    (G : SimpleGraph V) (forbidden : Finset V) (root : Fin 4 → V)
    (Key : Type*) (targetRoot : Key → V) (targetRadius L m : ℕ)
    (target : ∀ k : Key,
      VertexExpansion G (targetRoot k) L targetRadius) where
  key : Fin 4 → Key
  key_injective : Function.Injective key
  finish : Fin 4 → V
  finish_mem : ∀ i, finish i ∈ (target (key i)).verts
  path : ∀ i, G.Walk (root i) (finish i)
  path_isPath : ∀ i, (path i).IsPath
  path_length : ∀ i, (path i).length ≤ 2 * m
  path_avoids : ∀ i z, z ∈ (path i).support → z ∉ forbidden
  target_avoids : ∀ i, Disjoint (target (key i)).verts forbidden
  paths_disjoint : ∀ i j, i ≠ j →
    Disjoint (path i).support.toFinset (path j).support.toFinset
  path_target_disjoint : ∀ i j, i ≠ j →
    Disjoint (path i).support.toFinset (target (key j)).verts
  targets_disjoint : ∀ i j, i ≠ j →
    Disjoint (target (key i)).verts (target (key j)).verts

/-! ### Array-shaped target for the eventual four-stage construction -/

/-- Public array form of the desired Lemma 3.13 conclusion.  This is useful
for implementing the four routing stages over `Fin 4`; the user-facing
four-expansion theorem is just an unpacking of this proposition. -/
def EnlargedFourConclusion [Fintype V]
    (G : SimpleGraph V) (A : Finset V) (root : Fin 4 → V)
    (L m : ℕ) : Prop :=
  ∃ F : ∀ i : Fin 4, VertexExpansion G (root i) L (3 * m),
    (∀ i, Disjoint (F i).verts A) ∧
    ((Finset.univ : Finset (Fin 4)) : Set (Fin 4)).PairwiseDisjoint
      (fun i ↦ (F i).verts)

/-- Once the source-faithful routing construction and four-tuple selection
have produced `SelectedFourArmSystem`, attaching the four target expansions
gives the exact array form of Lemma 3.13. -/
theorem SelectedFourArmSystem.enlarge [Fintype V]
    {forbidden : Finset V} {root : Fin 4 → V}
    {Key : Type*} {targetRoot : Key → V}
    {targetRadius L m : ℕ}
    {target : ∀ k : Key,
      VertexExpansion G (targetRoot k) L targetRadius}
    (S : SelectedFourArmSystem G forbidden root Key targetRoot
      targetRadius L m target)
    (hradius : 2 * targetRadius ≤ m) :
    EnlargedFourConclusion G forbidden root L m := by
  classical
  let rerooted : ∀ i : Fin 4, VertexExpansion G (S.finish i) L m :=
    fun i ↦ ((target (S.key i)).reroot (S.finish_mem i)).radiusMono hradius
  have hattach (i : Fin 4) :
      ∃ F : VertexExpansion G (root i) L (3 * m),
        F.verts ⊆ (S.path i).support.toFinset ∪ (target (S.key i)).verts := by
    obtain ⟨F, hF⟩ := exists_attached_expansion
      (S.path i) (S.path_isPath i) (S.path_length i) (rerooted i)
        (by omega : 2 * m + m ≤ 3 * m)
    exact ⟨F, by simpa [rerooted] using hF⟩
  let F : ∀ i : Fin 4, VertexExpansion G (root i) L (3 * m) :=
    fun i ↦ Classical.choose (hattach i)
  have hFsub (i : Fin 4) :
      (F i).verts ⊆ (S.path i).support.toFinset ∪
        (target (S.key i)).verts :=
    Classical.choose_spec (hattach i)
  refine ⟨F, ?_, ?_⟩
  · intro i
    rw [Finset.disjoint_left]
    intro z hzF hzA
    rcases Finset.mem_union.1 (hFsub i hzF) with hzP | hzB
    · exact S.path_avoids i z (by simpa using hzP) hzA
    · exact Finset.disjoint_left.1 (S.target_avoids i) hzB hzA
  · intro i _ j _ hij
    change Disjoint (F i).verts (F j).verts
    rw [Finset.disjoint_left]
    intro z hzi hzj
    rcases Finset.mem_union.1 (hFsub i hzi) with hziP | hziB <;>
      rcases Finset.mem_union.1 (hFsub j hzj) with hzjP | hzjB
    · exact Finset.disjoint_left.1 (S.paths_disjoint i j hij) hziP hzjP
    · exact Finset.disjoint_left.1 (S.path_target_disjoint i j hij) hziP hzjB
    · exact Finset.disjoint_left.1
        (S.path_target_disjoint j i hij.symm) hzjP hziB
    · exact Finset.disjoint_left.1 (S.targets_disjoint i j hij) hziB hzjB

structure RoutedArm [Fintype V] (G : SimpleGraph V)
    (A : Finset V) (root : Fin 4 → V) (Key : Type*)
    (target : Key → Finset V) (m : ℕ) where
  owner : Fin 4
  key : Key
  finish : V
  finish_mem : finish ∈ target key
  path : G.Walk (root owner) finish
  isPath : path.IsPath
  length_le : path.length ≤ 2 * m
  avoids_A : ∀ z ∈ path.support, z ∉ A
  protectedSet : Finset V
  path_avoids_protected : ∀ z ∈ path.support, z ∉ protectedSet
  sourceCarrier : Finset V
  ownerPiece : Finset V
  exposure : Finset V
  finish_mem_exposure : finish ∈ exposure
  carrier_subset : path.support.toFinset ⊆
    sourceCarrier ∪ exposure
  source_contact_owner : ∀ z ∈ path.support,
    z ∈ sourceCarrier → z ∈ ownerPiece
  exposure_card : exposure.card ≤ m + 1
  target_contact_exposed : ∀ k z,
    z ∈ path.support → z ∈ target k → z ∈ exposure

namespace RoutedArm

variable [Fintype V]
variable {A : Finset V} {root : Fin 4 → V}
variable {target : Key → Finset V} {m : ℕ}

/-- Prefix a raw arm by a path in its owning prescribed expansion. -/
noncomputable def ofRaw
    (source forbidden : Finset V) (keys : Finset Key)
    (E : ∀ i : Fin 4, VertexExpansion G (root i) D m)
    (hEA : ∀ i, Disjoint (E i).verts A)
    (hAforbidden : A ⊆ forbidden)
    (hTargetSource : ∀ k, Disjoint (target k) source)
    (P : RawArm G source forbidden target keys m)
    (i : Fin 4) (hPi : P.start ∈ (E i).verts)
    (hPieceForbidden : Disjoint (E i).verts forbidden)
    (hsourcePiece : (E i).verts ⊆ source) :
    RoutedArm G A root Key target m := by
  classical
  let q : G.Walk (root i) P.start :=
    Classical.choose ((E i).exists_path hPi)
  have hq : q.IsPath :=
    (Classical.choose_spec ((E i).exists_path hPi)).1
  have hqlen : q.length ≤ m :=
    (Classical.choose_spec ((E i).exists_path hPi)).2.1
  have hqsupp : ∀ z ∈ q.support, z ∈ (E i).verts :=
    (Classical.choose_spec ((E i).exists_path hPi)).2.2
  let w : G.Walk (root i) P.finish := q.append P.path
  let p : G.Walk (root i) P.finish := w.bypass
  exact
    { owner := i
      key := P.key
      finish := P.finish
      finish_mem := P.finish_mem
      path := p
      isPath := w.bypass_isPath
      length_le := by
        calc
          p.length ≤ w.length := w.length_bypass_le_length
          _ = q.length + P.path.length := by simp [w]
          _ ≤ m + m := Nat.add_le_add hqlen P.length_le
          _ = 2 * m := by omega
      avoids_A := by
        intro z hz hzA
        have hzw : z ∈ w.support := w.support_bypass_subset_support hz
        change z ∈ (q.append P.path).support at hzw
        rw [Walk.mem_support_append_iff] at hzw
        rcases hzw with hzq | hzP
        · exact Finset.disjoint_left.1 (hEA i) (hqsupp z hzq) hzA
        · exact P.avoids z hzP (hAforbidden hzA)
      protectedSet := forbidden
      path_avoids_protected := by
        intro z hz hzForbidden
        have hzw : z ∈ w.support := w.support_bypass_subset_support hz
        change z ∈ (q.append P.path).support at hzw
        rw [Walk.mem_support_append_iff] at hzw
        rcases hzw with hzq | hzP
        · exact Finset.disjoint_left.1 hPieceForbidden
            (hqsupp z hzq) hzForbidden
        · exact P.avoids z hzP hzForbidden
      sourceCarrier := source
      ownerPiece := (E i).verts
      exposure := P.external
      finish_mem_exposure := by
        apply Finset.mem_sdiff.2
        refine ⟨by simp, ?_⟩
        intro hsourceFinish
        exact Finset.disjoint_left.1 (hTargetSource P.key)
          P.finish_mem hsourceFinish
      carrier_subset := by
        intro z hzp
        have hzw : z ∈ w.support := w.support_bypass_subset_support (by simpa using hzp)
        change z ∈ (q.append P.path).support at hzw
        rw [Walk.mem_support_append_iff] at hzw
        rcases hzw with hzq | hzP
        · exact Finset.mem_union_left _ (hsourcePiece (hqsupp z hzq))
        · by_cases hzs : z ∈ source
          · exact Finset.mem_union_left _ hzs
          · exact Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨by simpa using hzP, hzs⟩)
      source_contact_owner := by
        intro z hzp hzs
        have hzw : z ∈ w.support := w.support_bypass_subset_support hzp
        change z ∈ (q.append P.path).support at hzw
        rw [Walk.mem_support_append_iff] at hzw
        rcases hzw with hzq | hzP
        · exact hqsupp z hzq
        · have hzstart := P.only_start_in_source z hzP hzs
          simpa [hzstart] using hPi
      exposure_card := P.external_card_le
      target_contact_exposed := by
        intro k z hzp hzt
        have hzw : z ∈ w.support := w.support_bypass_subset_support hzp
        change z ∈ (q.append P.path).support at hzw
        rw [Walk.mem_support_append_iff] at hzw
        have hznotSource : z ∉ source := by
          intro hzs
          exact Finset.disjoint_left.1 (hTargetSource k) hzt hzs
        rcases hzw with hzq | hzP
        · exact (hznotSource (hsourcePiece (hqsupp z hzq))).elim
        · exact Finset.mem_sdiff.2 ⟨by simpa using hzP, hznotSource⟩ }

end RoutedArm

/-- A routed arm that avoids a protected set is disjoint from every earlier
path whose support is already contained in that set.  Factoring this tiny
geometric step keeps the four-stage selection proof below from repeatedly
elaborating the same walk-support argument. -/
theorem RoutedArm.disjoint_of_support_subset_protected [Fintype V]
    {A : Finset V} {root : Fin 4 → V} {target : Key → Finset V}
    {m : ℕ}
    (P Q : RoutedArm G A root Key target m) (W : Finset V)
    (hPW : P.path.support.toFinset ⊆ W)
    (hQW : Q.protectedSet = W) :
    Disjoint P.path.support.toFinset Q.path.support.toFinset := by
  rw [Finset.disjoint_left]
  intro z hzP hzQ
  exact Q.path_avoids_protected z (by simpa using hzQ) (hQW ▸ hPW hzP)

noncomputable def routedPathUnion [Fintype V]
    {A : Finset V} {root : Fin 4 → V} {target : Key → Finset V}
    {m : ℕ} (C : Finset (RoutedArm G A root Key target m)) : Finset V :=
  C.biUnion fun P ↦ P.path.support.toFinset

theorem routedPathUnion_card_le [Fintype V]
    {A : Finset V} {root : Fin 4 → V} {target : Key → Finset V}
    {m : ℕ} (C : Finset (RoutedArm G A root Key target m)) :
    (routedPathUnion C).card ≤ C.card * (2 * m + 1) := by
  calc
    (routedPathUnion C).card ≤
        ∑ P ∈ C, P.path.support.toFinset.card := Finset.card_biUnion_le
    _ ≤ ∑ _P ∈ C, (2 * m + 1) := by
      apply Finset.sum_le_sum
      intro P hP
      calc
        P.path.support.toFinset.card ≤ P.path.support.length :=
          List.toFinset_card_le _
        _ = P.path.length + 1 := by simp
        _ ≤ 2 * m + 1 := Nat.add_le_add_right P.length_le 1
    _ = C.card * (2 * m + 1) := by simp

theorem mem_routedPathUnion [Fintype V]
    {A : Finset V} {root : Fin 4 → V} {target : Key → Finset V}
    {m : ℕ} {C : Finset (RoutedArm G A root Key target m)}
    {P : RoutedArm G A root Key target m} (hP : P ∈ C) :
    P.path.support.toFinset ⊆ routedPathUnion C := by
  intro z hz
  exact Finset.mem_biUnion.2 ⟨P, hP, hz⟩

/-! ### One literal routing stage -/

noncomputable def expansionUnion [Fintype V]
    {root : Fin 4 → V} {D m : ℕ}
    (E : ∀ i : Fin 4, VertexExpansion G (root i) D m)
    (R : Finset (Fin 4)) : Finset V :=
  R.biUnion fun i ↦ (E i).verts

theorem expansionUnion_card_ge [Fintype V]
    {root : Fin 4 → V} {D m : ℕ}
    (E : ∀ i : Fin 4, VertexExpansion G (root i) D m)
    (R : Finset (Fin 4)) (hR : R.Nonempty) :
    D ≤ (expansionUnion E R).card := by
  obtain ⟨i, hi⟩ := hR
  calc
    D = (E i).verts.card := (E i).card_verts.symm
    _ ≤ (expansionUnion E R).card := Finset.card_le_card (by
      intro z hz
      exact Finset.mem_biUnion.2 ⟨i, hi, hz⟩)

theorem RoutedArm.disjoint_other_expansion [Fintype V]
    {A : Finset V} {root : Fin 4 → V} {target : Key → Finset V}
    {m D : ℕ}
    (E : ∀ i : Fin 4, VertexExpansion G (root i) D m)
    (hEpair : ∀ i j, i ≠ j → Disjoint (E i).verts (E j).verts)
    (R : Finset (Fin 4))
    (P : RoutedArm G A root Key target m) (i j : Fin 4)
    (howner : P.owner = i)
    (hsource : P.sourceCarrier = expansionUnion E R)
    (hpiece : P.ownerPiece = (E i).verts)
    (hjR : j ∈ R) (hij : i ≠ j) :
    Disjoint P.path.support.toFinset (E j).verts := by
  rw [Finset.disjoint_left]
  intro z hzP hzj
  have hzsource : z ∈ P.sourceCarrier := by
    rw [hsource]
    exact Finset.mem_biUnion.2 ⟨j, hjR, hzj⟩
  have hzpiece := P.source_contact_owner z (by simpa using hzP) hzsource
  rw [hpiece] at hzpiece
  exact Finset.disjoint_left.1 (hEpair i j hij) hzpiece hzj

/-- The exposed part of one routed arm meets at most `m` targets among any
three disjoint blocks of other arms.  This is the degree estimate used by the
four-partite counting argument, isolated from the much larger stage-building
proof so that Lean only elaborates it once. -/
theorem RoutedArm.total_other_target_hits_le [Fintype V] [Fintype Key]
    {A : Finset V} {root : Fin 4 → V} {target : Key → Finset V}
    {m : ℕ}
    (Call C X Y Z : Finset (RoutedArm G A root Key target m))
    (hCallInj : Set.InjOn
      (fun P : RoutedArm G A root Key target m ↦ P.key) Call)
    (hCsub : C ⊆ Call) (hXsub : X ⊆ Call) (hYsub : Y ⊆ Call)
    (hZsub : Z ⊆ Call)
    (hCX : Disjoint C X) (hCY : Disjoint C Y) (hCZ : Disjoint C Z)
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z)
    (htargetPair : ∀ k l, k ≠ l → Disjoint (target k) (target l)) :
    ∀ a ∈ C,
      (X.filter fun b ↦ ¬ Disjoint a.exposure (target b.key)).card +
        (Y.filter fun b ↦ ¬ Disjoint a.exposure (target b.key)).card +
        (Z.filter fun b ↦ ¬ Disjoint a.exposure (target b.key)).card ≤ m := by
  classical
  intro a ha
  let O := X ∪ Y ∪ Z
  have hOsub : O ⊆ Call := by
    intro b hb
    rcases Finset.mem_union.1 hb with hxy | hz
    · rcases Finset.mem_union.1 hxy with hx | hy
      · exact hXsub hx
      · exact hYsub hy
    · exact hZsub hz
  have hOinj : Set.InjOn
      (fun P : RoutedArm G A root Key target m ↦ P.key) O :=
    fun a ha b hb ↦ hCallInj (hOsub ha) (hOsub hb)
  have hCO : Disjoint C O := by
    rw [Finset.disjoint_left]
    intro c hc ho
    rcases Finset.mem_union.1 ho with hxy | hz
    · rcases Finset.mem_union.1 hxy with hx | hy
      · exact Finset.disjoint_left.1 hCX hc hx
      · exact Finset.disjoint_left.1 hCY hc hy
    · exact Finset.disjoint_left.1 hCZ hc hz
  have hOne :
      (O.filter fun b ↦ ¬ Disjoint a.exposure (target b.key)).card ≤ m := by
    apply card_target_hits_le O (fun P ↦ P.key) target
      a.exposure a.finish a.key m hOinj
    · intro b hb hkey
      have hba := hCallInj (hOsub hb) (hCsub ha) hkey
      exact Finset.disjoint_left.1 hCO ha (hba ▸ hb)
    · intro k hk l hl hkl
      exact htargetPair k l hkl
    · exact a.finish_mem_exposure
    · exact a.finish_mem
    · exact a.exposure_card
  have hfilters :
      (O.filter fun b ↦ ¬ Disjoint a.exposure (target b.key)).card =
        (X.filter fun b ↦ ¬ Disjoint a.exposure (target b.key)).card +
          (Y.filter fun b ↦ ¬ Disjoint a.exposure (target b.key)).card +
          (Z.filter fun b ↦ ¬ Disjoint a.exposure (target b.key)).card := by
    dsimp [O]
    rw [Finset.filter_union, Finset.filter_union]
    rw [Finset.card_union_of_disjoint]
    · rw [Finset.card_union_of_disjoint]
      exact hXY.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    · rw [Finset.disjoint_left]
      intro b hbXY hbZ
      have hbZ' : b ∈ Z := (Finset.mem_filter.1 hbZ).1
      rcases Finset.mem_union.1 hbXY with hbX | hbY
      · exact Finset.disjoint_left.1 hXZ (Finset.mem_filter.1 hbX).1 hbZ'
      · exact Finset.disjoint_left.1 hYZ (Finset.mem_filter.1 hbY).1 hbZ'
  rw [← hfilters]
  exact hOne

/-- Reindex four selected routed arms by their distinct owners and attach
their target expansions.  Keeping this finite reindexing separate prevents
the source-faithful four-stage construction from becoming one enormous
elaboration unit. -/
theorem enlargedFourConclusion_of_routed_permutation
    [Fintype V] [Fintype Key]
    {A : Finset V} {root : Fin 4 → V}
    {targetRoot : Key → V} {targetRadius L m : ℕ}
    (B : ∀ k : Key, VertexExpansion G (targetRoot k) L targetRadius)
    (hBA : ∀ k, Disjoint (B k).verts A)
    (hBpair : ∀ k l, k ≠ l → Disjoint (B k).verts (B l).verts)
    (hTargetRadius : 2 * targetRadius ≤ m)
    (ownerPermutation : Fin 4 → Fin 4)
    (hownerPermutation : Function.Injective ownerPermutation)
    (stageArm : Fin 4 →
      RoutedArm G A root Key (fun k ↦ (B k).verts) m)
    (hstageOwner : ∀ s, (stageArm s).owner = ownerPermutation s)
    (hstageKey : Function.Injective fun s ↦ (stageArm s).key)
    (hstagePaths : ∀ s t, s ≠ t →
      Disjoint (stageArm s).path.support.toFinset
        (stageArm t).path.support.toFinset)
    (hstageExposure : ∀ s t, s ≠ t →
      Disjoint (stageArm s).exposure (B (stageArm t).key).verts) :
    EnlargedFourConclusion G A root L m := by
  classical
  let e : Fin 4 ≃ Fin 4 := Equiv.ofBijective ownerPermutation
    ⟨hownerPermutation,
      Finite.injective_iff_surjective.mp hownerPermutation⟩
  let chosen : Fin 4 →
      RoutedArm G A root Key (fun k ↦ (B k).verts) m :=
    fun i ↦ stageArm (e.symm i)
  have hchosenOwner (i : Fin 4) : (chosen i).owner = i := by
    calc
      (chosen i).owner = ownerPermutation (e.symm i) :=
        hstageOwner (e.symm i)
      _ = e (e.symm i) := rfl
      _ = i := e.apply_symm_apply i
  have castWalk_support {a b c : V} (h : a = b) (p : G.Walk a c) :
      (h ▸ p : G.Walk b c).support = p.support := by
    cases h
    rfl
  have castWalk_isPath {a b c : V} (h : a = b) (p : G.Walk a c)
      (hp : p.IsPath) : (h ▸ p : G.Walk b c).IsPath := by
    cases h
    exact hp
  have castWalk_length {a b c : V} (h : a = b) (p : G.Walk a c) :
      (h ▸ p : G.Walk b c).length = p.length := by
    cases h
    rfl
  let chosenRootEq (i : Fin 4) : root (chosen i).owner = root i :=
    congrArg root (hchosenOwner i)
  let chosenPath : ∀ i : Fin 4, G.Walk (root i) (chosen i).finish :=
    fun i ↦ chosenRootEq i ▸ (chosen i).path
  have hchosenSupport (i : Fin 4) :
      (chosenPath i).support = (chosen i).path.support :=
    castWalk_support (chosenRootEq i) (chosen i).path
  have hchosenKeyInj : Function.Injective fun i ↦ (chosen i).key := by
    intro i j hkey
    exact e.symm.injective (hstageKey (by simpa only [chosen] using hkey))
  have hchosenPaths (i j : Fin 4) (hij : i ≠ j) :
      Disjoint (chosenPath i).support.toFinset
        (chosenPath j).support.toFinset := by
    have hstageNe : e.symm i ≠ e.symm j := fun h ↦ hij (e.symm.injective h)
    rw [hchosenSupport i, hchosenSupport j]
    simpa only [chosen] using hstagePaths (e.symm i) (e.symm j) hstageNe
  have hchosenPathTarget (i j : Fin 4) (hij : i ≠ j) :
      Disjoint (chosenPath i).support.toFinset (B (chosen j).key).verts := by
    have hstageNe : e.symm i ≠ e.symm j := fun h ↦ hij (e.symm.injective h)
    have hexposure := hstageExposure (e.symm i) (e.symm j) hstageNe
    rw [Finset.disjoint_left]
    intro z hzP hzB
    rw [hchosenSupport i] at hzP
    have hzExposure : z ∈ (chosen i).exposure :=
      (chosen i).target_contact_exposed (chosen j).key z
        (by simpa using hzP) hzB
    exact Finset.disjoint_left.1 hexposure
      (by simpa only [chosen] using hzExposure)
      (by simpa only [chosen] using hzB)
  let T : SelectedFourArmSystem G A root Key targetRoot targetRadius L m B :=
    { key := fun i ↦ (chosen i).key
      key_injective := hchosenKeyInj
      finish := fun i ↦ (chosen i).finish
      finish_mem := fun i ↦ (chosen i).finish_mem
      path := chosenPath
      path_isPath := fun i ↦
        castWalk_isPath (chosenRootEq i) (chosen i).path (chosen i).isPath
      path_length := fun i ↦ by
        rw [castWalk_length (chosenRootEq i) (chosen i).path]
        exact (chosen i).length_le
      path_avoids := fun i z hz hzA ↦ by
        rw [hchosenSupport i] at hz
        exact (chosen i).avoids_A z hz hzA
      target_avoids := fun i ↦ hBA (chosen i).key
      paths_disjoint := hchosenPaths
      path_target_disjoint := hchosenPathTarget
      targets_disjoint := by
        intro i j hij
        exact hBpair (chosen i).key (chosen j).key
          (fun h ↦ hij (hchosenKeyInj h)) }
  exact T.enlarge hTargetRadius

namespace RawArm

variable [Fintype V]
variable {A : Finset V} {root : Fin 4 → V}
variable {target : Key → Finset V} {m D : ℕ}

noncomputable def owner
    (E : ∀ i : Fin 4, VertexExpansion G (root i) D m)
    (R : Finset (Fin 4)) (forbidden : Finset V) (keys : Finset Key)
    (P : RawArm G (expansionUnion E R) forbidden target keys m) : Fin 4 :=
  Classical.choose (Finset.mem_biUnion.1 P.start_mem)

theorem owner_mem
    (E : ∀ i : Fin 4, VertexExpansion G (root i) D m)
    (R : Finset (Fin 4)) (forbidden : Finset V) (keys : Finset Key)
    (P : RawArm G (expansionUnion E R) forbidden target keys m) :
    P.owner E R forbidden keys ∈ R :=
  (Classical.choose_spec (Finset.mem_biUnion.1 P.start_mem)).1

theorem start_mem_owner
    (E : ∀ i : Fin 4, VertexExpansion G (root i) D m)
    (R : Finset (Fin 4)) (forbidden : Finset V) (keys : Finset Key)
    (P : RawArm G (expansionUnion E R) forbidden target keys m) :
    P.start ∈ (E (P.owner E R forbidden keys)).verts :=
  (Classical.choose_spec (Finset.mem_biUnion.1 P.start_mem)).2

/-- One actual `8m`-arm stage: saturate all available keys, pigeonhole the
owner, prefix the retained raw arms inside that owner's prescribed expansion,
and forget the heterogeneous raw-arm type.  This is the reusable unit called
four times with remaining-root cardinalities `4,3,2,1`. -/
theorem exists_routed_block
    [Fintype Key] [DecidableRel G.Adj]
    (epsilon kappa : ℝ) (hexp : IsLMExpander G epsilon kappa)
    (degreeScale : ℕ) (hdegree : ∀ v : V, degreeScale ≤ G.degree v)
    (start workspace radius q : ℕ)
    (growth : BallGrowthSchedule G epsilon kappa start workspace radius)
    (hstart : 0 < start)
    (hradius : 2 * (radius + 1) ≤ m)
    (E : ∀ i : Fin 4, VertexExpansion G (root i) D m)
    (hEA : ∀ i, Disjoint (E i).verts A)
    (hEpair : ∀ i j, i ≠ j → Disjoint (E i).verts (E j).verts)
    (R : Finset (Fin 4)) (hR : R.Nonempty)
    (forbidden : Finset V) (hAforbidden : A ⊆ forbidden)
    (hEforbidden : ∀ i ∈ R, Disjoint (E i).verts forbidden)
    (keys : Finset Key)
    (hfixed : forbidden.card + keys.card * (m + 1) ≤ workspace)
    (hsourceSurvives : 1 + workspace ≤ (expansionUnion E R).card)
    (htargetSurvives : ∀ k ∈ keys,
      1 + workspace ≤ (target k).card)
    (hsourceSeed : start + workspace ≤ (expansionUnion E R).card ∨
      start + workspace ≤ degreeScale)
    (htargetSeed : ∀ k ∈ keys,
      start + workspace ≤ (target k).card ∨
        start + workspace ≤ degreeScale)
    (htargetPair : ∀ k ∈ keys, ∀ l ∈ keys, k ≠ l →
      Disjoint (target k) (target l))
    (htargetSource : ∀ k, Disjoint (target k) (expansionUnion E R))
    (hcount : R.card * q ≤ keys.card) :
    ∃ i ∈ R, ∃ C : Finset (RoutedArm G A root Key target m),
      C.card = q ∧
      (∀ P ∈ C, P.owner = i) ∧
      Set.InjOn (fun P : RoutedArm G A root Key target m ↦ P.key) C ∧
      (∀ P ∈ C, P.key ∈ keys) ∧
      (∀ P ∈ C,
        P.protectedSet = forbidden ∧
        P.sourceCarrier = expansionUnion E R ∧
        P.ownerPiece = (E i).verts) := by
  let originalDecAdj : DecidableRel G.Adj := inferInstance
  classical
  letI : DecidableRel G.Adj := originalDecAdj
  obtain ⟨S, hSpair, hSkeys, hScard⟩ :=
    RawArm.exists_saturated_family (G := G)
      (source := expansionUnion E R) (forbidden := forbidden)
      (target := target) (keys := keys) (m := m)
      epsilon kappa hexp degreeScale hdegree start workspace radius growth hstart
      hradius hfixed hsourceSurvives htargetSurvives hsourceSeed htargetSeed
  let own : RawArm G (expansionUnion E R) forbidden target keys m → Fin 4 :=
    fun P ↦ P.owner E R forbidden keys
  have hown : ∀ P ∈ S, own P ∈ R := by
    intro P hP
    exact P.owner_mem E R forbidden keys
  obtain ⟨i, hi, T, hTS, hTcard, hTown⟩ :=
    exists_popular_owner S R own q hR hown (by omega)
  have hTpair :
      ((T : Set (RawArm G (expansionUnion E R) forbidden target keys m)).Pairwise
        fun P Q ↦ ¬ Conflict P Q) := by
    intro P hPT Q hQT hPQ
    exact hSpair (hTS hPT) (hTS hQT) hPQ
  let routed : RawArm G (expansionUnion E R) forbidden target keys m →
      RoutedArm G A root Key target m := fun P ↦
    RoutedArm.ofRaw (G := G) (D := D)
      (expansionUnion E R) forbidden keys E hEA hAforbidden
      htargetSource P (P.owner E R forbidden keys)
      (P.start_mem_owner E R forbidden keys) (by
        exact hEforbidden (P.owner E R forbidden keys)
          (P.owner_mem E R forbidden keys)) (by
        intro z hz
        exact Finset.mem_biUnion.2
          ⟨P.owner E R forbidden keys, P.owner_mem E R forbidden keys, hz⟩)
  have routed_key (P : RawArm G (expansionUnion E R) forbidden target keys m) :
      (routed P).key = P.key := by simp only [routed, RoutedArm.ofRaw]
  have routed_owner (P : RawArm G (expansionUnion E R) forbidden target keys m) :
      (routed P).owner = P.owner E R forbidden keys := by
    simp only [routed, RoutedArm.ofRaw]
  have routed_protected
      (P : RawArm G (expansionUnion E R) forbidden target keys m) :
      (routed P).protectedSet = forbidden := by simp only [routed, RoutedArm.ofRaw]
  have routed_source
      (P : RawArm G (expansionUnion E R) forbidden target keys m) :
      (routed P).sourceCarrier = expansionUnion E R := by
    simp only [routed, RoutedArm.ofRaw]
  have routed_piece
      (P : RawArm G (expansionUnion E R) forbidden target keys m) :
      (routed P).ownerPiece = (E (P.owner E R forbidden keys)).verts := by
    simp only [routed, RoutedArm.ofRaw]
  have hroutedInj : Set.InjOn routed T := by
    intro P hPT Q hQT hPQ
    apply RawArm.key_injOn_of_pairwise hTpair hPT hQT
    have hkey := congrArg
      (fun Z : RoutedArm G A root Key target m ↦ Z.key) hPQ
    rw [routed_key P, routed_key Q] at hkey
    exact hkey
  let C := T.image routed
  have hCcard : C.card = q := by
    dsimp [C]
    rw [Finset.card_image_iff.mpr hroutedInj, hTcard]
  refine ⟨i, hi, C, hCcard, ?_, ?_, ?_, ?_⟩
  · intro P hPC
    change P ∈ T.image routed at hPC
    obtain ⟨Q, hQT, rfl⟩ := Finset.mem_image.1 hPC
    rw [routed_owner]
    exact hTown Q hQT
  · intro P hPC Q hQC hkey
    change P ∈ T.image routed at hPC
    change Q ∈ T.image routed at hQC
    obtain ⟨P₀, hP₀T, rfl⟩ := Finset.mem_image.1 hPC
    obtain ⟨Q₀, hQ₀T, rfl⟩ := Finset.mem_image.1 hQC
    apply congrArg routed
    apply RawArm.key_injOn_of_pairwise hTpair hP₀T hQ₀T
    change (routed P₀).key = (routed Q₀).key at hkey
    rw [routed_key P₀, routed_key Q₀] at hkey
    exact hkey
  · intro P hPC
    change P ∈ T.image routed at hPC
    obtain ⟨Q, hQT, rfl⟩ := Finset.mem_image.1 hPC
    rw [routed_key]
    exact Q.key_mem
  · intro P hPC
    change P ∈ T.image routed at hPC
    obtain ⟨Q, hQT, rfl⟩ := Finset.mem_image.1 hPC
    have howner := hTown Q hQT
    change Q.owner E R forbidden keys = i at howner
    refine ⟨routed_protected Q, routed_source Q, ?_⟩
    rw [routed_piece Q, howner]

end RawArm

private theorem enlargedFourConclusion_of_candidates
    [Fintype V] [Fintype Key]
    (G : SimpleGraph V) [DecidableRel G.Adj] (epsilon kappa : ℝ)
    (hexp : IsLMExpander G epsilon kappa)
    (A : Finset V) (root : Fin 4 → V)
    (D L targetRadius m start workspace radius : ℕ)
    (hm : 0 < m)
    (degreeScale : ℕ) (hdegree : ∀ v : V, degreeScale ≤ G.degree v)
    (growth : BallGrowthSchedule G epsilon kappa start workspace radius)
    (hstart : 0 < start) (hrouteRadius : 2 * (radius + 1) ≤ m)
    (hpathBudget : A.card + (8 * m) * (7 * m + 4) ≤ workspace)
    (hsourceSurvives : 1 + workspace ≤ D)
    (htargetSurvives : 1 + workspace ≤ L)
    (hsourceSeed : start + workspace ≤ D ∨
      start + workspace ≤ degreeScale)
    (htargetSeed : start + workspace ≤ L ∨
      start + workspace ≤ degreeScale)
    (hTargetRadius : 2 * targetRadius ≤ m)
    (hKeyCard : Fintype.card Key = 32 * m)
    (targetRoot : Key → V)
    (B : ∀ k : Key, VertexExpansion G (targetRoot k) L targetRadius)
    (hBA : ∀ k, Disjoint (B k).verts A)
    (hBpair : ∀ k l, k ≠ l → Disjoint (B k).verts (B l).verts)
    (E : ∀ i : Fin 4, VertexExpansion G (root i) D m)
    (hEA : ∀ i, Disjoint (E i).verts A)
    (hEpair : ∀ i j, i ≠ j → Disjoint (E i).verts (E j).verts)
    (hBE : ∀ k i, Disjoint (B k).verts (E i).verts) :
    EnlargedFourConclusion G A root L m := by
  let originalDecAdj : DecidableRel G.Adj := inferInstance
  classical
  letI : DecidableRel G.Adj := originalDecAdj
  let target : Key → Finset V := fun k ↦ (B k).verts
  let M := 8 * m
  have hMpos : 0 < M := by dsimp [M]; omega
  have htargetPair : ∀ k l, k ≠ l → Disjoint (target k) (target l) := by
    intro k l hkl
    exact hBpair k l hkl
  have htargetSource (R : Finset (Fin 4)) (k : Key) :
      Disjoint (target k) (expansionUnion E R) := by
    rw [Finset.disjoint_left]
    intro z hzB hzU
    obtain ⟨i, hiR, hzE⟩ := Finset.mem_biUnion.1 hzU
    exact Finset.disjoint_left.1 (hBE k i) hzB hzE
  have hsourceSurvival (R : Finset (Fin 4)) (hR : R.Nonempty) :
      1 + workspace ≤ (expansionUnion E R).card :=
    hsourceSurvives.trans (expansionUnion_card_ge E R hR)
  have htargetSurvival (K : Finset Key) : ∀ k ∈ K,
      1 + workspace ≤ (target k).card := by
    intro k hk
    simpa [target, (B k).card_verts] using htargetSurvives
  have hsourceCard (R : Finset (Fin 4)) (hR : R.Nonempty) :
      start + workspace ≤ (expansionUnion E R).card ∨
        start + workspace ≤ degreeScale :=
    hsourceSeed.imp (fun h ↦ h.trans (expansionUnion_card_ge E R hR)) id
  have htargetCard (K : Finset Key) : ∀ k ∈ K,
      start + workspace ≤ (target k).card ∨
        start + workspace ≤ degreeScale := by
    intro k hk
    exact htargetSeed.imp (fun h ↦ by
      simpa [target, (B k).card_verts] using h) id
  let R₀ : Finset (Fin 4) := Finset.univ
  let K₀ : Finset Key := Finset.univ
  let W₀ : Finset V := A
  have hR₀ : R₀.Nonempty := by simp [R₀]
  have hK₀card : K₀.card = 4 * M := by
    calc
      K₀.card = Fintype.card Key := by simp [K₀]
      _ = 32 * m := hKeyCard
      _ = 4 * M := by dsimp [M]; ring
  have hW₀card : W₀.card + K₀.card * (m + 1) ≤ workspace := by
    dsimp [W₀]
    rw [hK₀card]
    dsimp [M] at *
    nlinarith
  have hE₀W₀ : ∀ i ∈ R₀, Disjoint (E i).verts W₀ := by
    intro i hi
    exact hEA i
  obtain ⟨i₀, hi₀, C₀, hC₀card, hC₀owner, hC₀inj, hC₀keys, hC₀meta⟩ :=
    RawArm.exists_routed_block (G := G) (A := A) (root := root)
      (target := target) epsilon kappa hexp degreeScale hdegree
      start workspace radius M growth
      hstart hrouteRadius E hEA hEpair R₀ hR₀ W₀ (by simp [W₀])
      hE₀W₀ K₀ hW₀card (hsourceSurvival R₀ hR₀) (htargetSurvival K₀)
      (hsourceCard R₀ hR₀) (htargetCard K₀)
      (fun k hk l hl hkl ↦ htargetPair k l hkl)
      (htargetSource R₀) (by
        calc
          R₀.card * M = 4 * M := by simp [R₀]
          _ ≤ K₀.card := by rw [hK₀card])
  let J₀ := C₀.image fun P ↦ P.key
  have hJ₀card : J₀.card = M := by
    dsimp [J₀]
    rw [Finset.card_image_iff.mpr hC₀inj, hC₀card]
  have hJ₀sub : J₀ ⊆ K₀ := by
    intro k hk
    obtain ⟨P, hPC, rfl⟩ := Finset.mem_image.1 hk
    exact hC₀keys P hPC
  let R₁ := R₀.erase i₀
  let K₁ := K₀ \ J₀
  let W₁ := W₀ ∪ routedPathUnion C₀
  have hR₁card : R₁.card = 3 := by
    simp [R₁, Finset.card_erase_of_mem hi₀, R₀]
  have hR₁ : R₁.Nonempty := by rw [Finset.nonempty_iff_ne_empty]; intro h; simp [h] at hR₁card
  have hK₁card : K₁.card = 3 * M := by
    dsimp [K₁]
    rw [Finset.card_sdiff_of_subset hJ₀sub, hK₀card, hJ₀card]
    omega
  have hW₁bound : W₁.card ≤ A.card + M * (2 * m + 1) := by
    have hu := Finset.card_union_le W₀ (routedPathUnion C₀)
    have hp := routedPathUnion_card_le C₀
    rw [hC₀card] at hp
    calc
      W₁.card ≤ W₀.card + (routedPathUnion C₀).card := by
        simpa [W₁] using hu
      _ ≤ W₀.card + M * (2 * m + 1) := Nat.add_le_add_left hp _
      _ = A.card + M * (2 * m + 1) := by simp [W₀]
  have hAW₁ : A ⊆ W₁ := by
    intro z hz
    exact Finset.mem_union_left _ hz
  have hE₁W₁ : ∀ i ∈ R₁, Disjoint (E i).verts W₁ := by
    intro i hi
    have hiR₀ : i ∈ R₀ := Finset.mem_of_mem_erase hi
    have hii₀ : i ≠ i₀ := (Finset.mem_erase.1 hi).1
    rw [Finset.disjoint_left]
    intro z hzE hzW
    rcases Finset.mem_union.1 hzW with hzA | hzP
    · exact Finset.disjoint_left.1 (hEA i) hzE hzA
    · obtain ⟨P, hPC, hzPsupp⟩ := Finset.mem_biUnion.1 hzP
      obtain ⟨hprot, hsource, hpiece⟩ := hC₀meta P hPC
      exact Finset.disjoint_left.1
        (P.disjoint_other_expansion E hEpair R₀ i₀ i
          (hC₀owner P hPC) hsource hpiece hiR₀ hii₀.symm)
        hzPsupp hzE
  have hW₁fixed : W₁.card + K₁.card * (m + 1) ≤ workspace := by
    rw [hK₁card]
    calc
      W₁.card + 3 * M * (m + 1) ≤
          (A.card + M * (2 * m + 1)) + 3 * M * (m + 1) :=
        Nat.add_le_add_right hW₁bound _
      _ ≤ A.card + M * (7 * m + 4) := by nlinarith
      _ ≤ workspace := hpathBudget
  obtain ⟨i₁, hi₁, C₁, hC₁card, hC₁owner, hC₁inj, hC₁keys, hC₁meta⟩ :=
    RawArm.exists_routed_block (G := G) (A := A) (root := root)
      (target := target) epsilon kappa hexp degreeScale hdegree
      start workspace radius M growth
      hstart hrouteRadius E hEA hEpair R₁ hR₁ W₁ hAW₁
      hE₁W₁ K₁ hW₁fixed (hsourceSurvival R₁ hR₁) (htargetSurvival K₁)
      (hsourceCard R₁ hR₁) (htargetCard K₁)
      (fun k hk l hl hkl ↦ htargetPair k l hkl)
      (htargetSource R₁) (by
        calc
          R₁.card * M = 3 * M := by rw [hR₁card]
          _ ≤ K₁.card := by rw [hK₁card])
  let J₁ := C₁.image fun P ↦ P.key
  have hJ₁card : J₁.card = M := by
    dsimp [J₁]
    rw [Finset.card_image_iff.mpr hC₁inj, hC₁card]
  have hJ₁sub : J₁ ⊆ K₁ := by
    intro k hk
    obtain ⟨P, hPC, rfl⟩ := Finset.mem_image.1 hk
    exact hC₁keys P hPC
  let R₂ := R₁.erase i₁
  let K₂ := K₁ \ J₁
  let W₂ := W₁ ∪ routedPathUnion C₁
  have hR₂card : R₂.card = 2 := by
    simp [R₂, Finset.card_erase_of_mem hi₁, hR₁card]
  have hR₂ : R₂.Nonempty := by rw [Finset.nonempty_iff_ne_empty]; intro h; simp [h] at hR₂card
  have hK₂card : K₂.card = 2 * M := by
    dsimp [K₂]
    rw [Finset.card_sdiff_of_subset hJ₁sub, hK₁card, hJ₁card]
    omega
  have hW₂bound : W₂.card ≤ A.card + 2 * M * (2 * m + 1) := by
    have hu := Finset.card_union_le W₁ (routedPathUnion C₁)
    have hp := routedPathUnion_card_le C₁
    rw [hC₁card] at hp
    have hu' : W₂.card ≤ W₁.card + (routedPathUnion C₁).card := by
      simpa [W₂] using hu
    calc
      W₂.card ≤ W₁.card + (routedPathUnion C₁).card := hu'
      _ ≤ (A.card + M * (2 * m + 1)) + M * (2 * m + 1) :=
        Nat.add_le_add hW₁bound hp
      _ = A.card + 2 * M * (2 * m + 1) := by ring
  have hAW₂ : A ⊆ W₂ := hAW₁.trans Finset.subset_union_left
  have hE₂W₂ : ∀ i ∈ R₂, Disjoint (E i).verts W₂ := by
    intro i hi
    have hiR₁ : i ∈ R₁ := Finset.mem_of_mem_erase hi
    have hii₁ : i ≠ i₁ := (Finset.mem_erase.1 hi).1
    rw [Finset.disjoint_left]
    intro z hzE hzW
    rcases Finset.mem_union.1 hzW with hzOld | hzP
    · exact Finset.disjoint_left.1 (hE₁W₁ i hiR₁) hzE hzOld
    · obtain ⟨P, hPC, hzPsupp⟩ := Finset.mem_biUnion.1 hzP
      obtain ⟨hprot, hsource, hpiece⟩ := hC₁meta P hPC
      exact Finset.disjoint_left.1
        (P.disjoint_other_expansion E hEpair R₁ i₁ i
          (hC₁owner P hPC) hsource hpiece hiR₁ hii₁.symm)
        hzPsupp hzE
  have hW₂fixed : W₂.card + K₂.card * (m + 1) ≤ workspace := by
    rw [hK₂card]
    calc
      W₂.card + 2 * M * (m + 1) ≤
          (A.card + 2 * M * (2 * m + 1)) + 2 * M * (m + 1) :=
        Nat.add_le_add_right hW₂bound _
      _ ≤ A.card + M * (7 * m + 4) := by nlinarith
      _ ≤ workspace := hpathBudget
  obtain ⟨i₂, hi₂, C₂, hC₂card, hC₂owner, hC₂inj, hC₂keys, hC₂meta⟩ :=
    RawArm.exists_routed_block (G := G) (A := A) (root := root)
      (target := target) epsilon kappa hexp degreeScale hdegree
      start workspace radius M growth
      hstart hrouteRadius E hEA hEpair R₂ hR₂ W₂ hAW₂
      hE₂W₂ K₂ hW₂fixed (hsourceSurvival R₂ hR₂) (htargetSurvival K₂)
      (hsourceCard R₂ hR₂) (htargetCard K₂)
      (fun k hk l hl hkl ↦ htargetPair k l hkl)
      (htargetSource R₂) (by
        calc
          R₂.card * M = 2 * M := by rw [hR₂card]
          _ ≤ K₂.card := by rw [hK₂card])
  let J₂ := C₂.image fun P ↦ P.key
  have hJ₂card : J₂.card = M := by
    dsimp [J₂]
    rw [Finset.card_image_iff.mpr hC₂inj, hC₂card]
  have hJ₂sub : J₂ ⊆ K₂ := by
    intro k hk
    obtain ⟨P, hPC, rfl⟩ := Finset.mem_image.1 hk
    exact hC₂keys P hPC
  let R₃ := R₂.erase i₂
  let K₃ := K₂ \ J₂
  let W₃ := W₂ ∪ routedPathUnion C₂
  have hR₃card : R₃.card = 1 := by
    simp [R₃, Finset.card_erase_of_mem hi₂, hR₂card]
  have hR₃ : R₃.Nonempty := by rw [Finset.nonempty_iff_ne_empty]; intro h; simp [h] at hR₃card
  have hK₃card : K₃.card = M := by
    dsimp [K₃]
    rw [Finset.card_sdiff_of_subset hJ₂sub, hK₂card, hJ₂card]
    omega
  have hW₃bound : W₃.card ≤ A.card + 3 * M * (2 * m + 1) := by
    have hu := Finset.card_union_le W₂ (routedPathUnion C₂)
    have hp := routedPathUnion_card_le C₂
    rw [hC₂card] at hp
    have hu' : W₃.card ≤ W₂.card + (routedPathUnion C₂).card := by
      simpa [W₃] using hu
    calc
      W₃.card ≤ W₂.card + (routedPathUnion C₂).card := hu'
      _ ≤ (A.card + 2 * M * (2 * m + 1)) + M * (2 * m + 1) :=
        Nat.add_le_add hW₂bound hp
      _ = A.card + 3 * M * (2 * m + 1) := by ring
  have hAW₃ : A ⊆ W₃ := hAW₂.trans Finset.subset_union_left
  have hE₃W₃ : ∀ i ∈ R₃, Disjoint (E i).verts W₃ := by
    intro i hi
    have hiR₂ : i ∈ R₂ := Finset.mem_of_mem_erase hi
    have hii₂ : i ≠ i₂ := (Finset.mem_erase.1 hi).1
    rw [Finset.disjoint_left]
    intro z hzE hzW
    rcases Finset.mem_union.1 hzW with hzOld | hzP
    · exact Finset.disjoint_left.1 (hE₂W₂ i hiR₂) hzE hzOld
    · obtain ⟨P, hPC, hzPsupp⟩ := Finset.mem_biUnion.1 hzP
      obtain ⟨hprot, hsource, hpiece⟩ := hC₂meta P hPC
      exact Finset.disjoint_left.1
        (P.disjoint_other_expansion E hEpair R₂ i₂ i
          (hC₂owner P hPC) hsource hpiece hiR₂ hii₂.symm)
        hzPsupp hzE
  have hW₃fixed : W₃.card + K₃.card * (m + 1) ≤ workspace := by
    rw [hK₃card]
    calc
      W₃.card + M * (m + 1) ≤
          (A.card + 3 * M * (2 * m + 1)) + M * (m + 1) :=
        Nat.add_le_add_right hW₃bound _
      _ = A.card + M * (7 * m + 4) := by ring
      _ ≤ workspace := hpathBudget
  obtain ⟨i₃, hi₃, C₃, hC₃card, hC₃owner, hC₃inj, hC₃keys, hC₃meta⟩ :=
    RawArm.exists_routed_block (G := G) (A := A) (root := root)
      (target := target) epsilon kappa hexp degreeScale hdegree
      start workspace radius M growth
      hstart hrouteRadius E hEA hEpair R₃ hR₃ W₃ hAW₃
      hE₃W₃ K₃ hW₃fixed (hsourceSurvival R₃ hR₃) (htargetSurvival K₃)
      (hsourceCard R₃ hR₃) (htargetCard K₃)
      (fun k hk l hl hkl ↦ htargetPair k l hkl)
      (htargetSource R₃) (by
        calc
          R₃.card * M = M := by rw [hR₃card]; simp
          _ ≤ K₃.card := by rw [hK₃card])
  have hkey₀later : ∀ a ∈ C₀, ∀ b ∈ C₁ ∪ C₂ ∪ C₃,
      a.key ≠ b.key := by
    intro a ha b hb hab
    have haJ : a.key ∈ J₀ := Finset.mem_image.2 ⟨a, ha, rfl⟩
    have hbK₁ : b.key ∈ K₁ := by
      simp only [Finset.mem_union] at hb
      rcases hb with (hb1 | hb2) | hb3
      · exact hC₁keys b hb1
      · exact Finset.sdiff_subset (hC₂keys b hb2)
      · exact Finset.sdiff_subset (Finset.sdiff_subset (hC₃keys b hb3))
    exact (Finset.mem_sdiff.1 hbK₁).2 (hab ▸ haJ)
  have hkey₁later : ∀ a ∈ C₁, ∀ b ∈ C₂ ∪ C₃,
      a.key ≠ b.key := by
    intro a ha b hb hab
    have haJ : a.key ∈ J₁ := Finset.mem_image.2 ⟨a, ha, rfl⟩
    have hbK₂ : b.key ∈ K₂ := by
      simp only [Finset.mem_union] at hb
      rcases hb with hb2 | hb3
      · exact hC₂keys b hb2
      · exact Finset.sdiff_subset (hC₃keys b hb3)
    exact (Finset.mem_sdiff.1 hbK₂).2 (hab ▸ haJ)
  have hkey₂later : ∀ a ∈ C₂, ∀ b ∈ C₃,
      a.key ≠ b.key := by
    intro a ha b hb hab
    have haJ : a.key ∈ J₂ := Finset.mem_image.2 ⟨a, ha, rfl⟩
    have hbK₃ := hC₃keys b hb
    exact (Finset.mem_sdiff.1 hbK₃).2 (hab ▸ haJ)
  have hC₀C₁ : Disjoint C₀ C₁ := by
    rw [Finset.disjoint_left]
    intro a ha0 ha1
    exact hkey₀later a ha0 a (Finset.mem_union_left _ <|
      Finset.mem_union_left _ ha1) rfl
  have hC₀C₂ : Disjoint C₀ C₂ := by
    rw [Finset.disjoint_left]
    intro a ha0 ha2
    exact hkey₀later a ha0 a (Finset.mem_union_left _ <|
      Finset.mem_union_right _ ha2) rfl
  have hC₀C₃ : Disjoint C₀ C₃ := by
    rw [Finset.disjoint_left]
    intro a ha0 ha3
    exact hkey₀later a ha0 a (Finset.mem_union_right _ ha3) rfl
  have hC₁C₂ : Disjoint C₁ C₂ := by
    rw [Finset.disjoint_left]
    intro a ha1 ha2
    exact hkey₁later a ha1 a (Finset.mem_union_left _ ha2) rfl
  have hC₁C₃ : Disjoint C₁ C₃ := by
    rw [Finset.disjoint_left]
    intro a ha1 ha3
    exact hkey₁later a ha1 a (Finset.mem_union_right _ ha3) rfl
  have hC₂C₃ : Disjoint C₂ C₃ := by
    rw [Finset.disjoint_left]
    intro a ha2 ha3
    exact hkey₂later a ha2 a ha3 rfl
  let Call := C₀ ∪ C₁ ∪ C₂ ∪ C₃
  have hCallInj : Set.InjOn
      (fun P : RoutedArm G A root Key target m ↦ P.key) Call := by
    intro a ha b hb hkey
    change a ∈ C₀ ∪ C₁ ∪ C₂ ∪ C₃ at ha
    change b ∈ C₀ ∪ C₁ ∪ C₂ ∪ C₃ at hb
    have ha' : ((a ∈ C₀ ∨ a ∈ C₁) ∨ a ∈ C₂) ∨ a ∈ C₃ := by
      simpa only [Call, Finset.mem_union] using ha
    have hb' : ((b ∈ C₀ ∨ b ∈ C₁) ∨ b ∈ C₂) ∨ b ∈ C₃ := by
      simpa only [Call, Finset.mem_union] using hb
    rcases ha' with ((ha0 | ha1) | ha2) | ha3 <;>
      rcases hb' with ((hb0 | hb1) | hb2) | hb3
    · exact hC₀inj ha0 hb0 hkey
    · exact (hkey₀later a ha0 b (by simp [hb1]) hkey).elim
    · exact (hkey₀later a ha0 b (by simp [hb2]) hkey).elim
    · exact (hkey₀later a ha0 b (by simp [hb3]) hkey).elim
    · exact (hkey₀later b hb0 a (by simp [ha1]) hkey.symm).elim
    · exact hC₁inj ha1 hb1 hkey
    · exact (hkey₁later a ha1 b (by simp [hb2]) hkey).elim
    · exact (hkey₁later a ha1 b (by simp [hb3]) hkey).elim
    · exact (hkey₀later b hb0 a (by simp [ha2]) hkey.symm).elim
    · exact (hkey₁later b hb1 a (by simp [ha2]) hkey.symm).elim
    · exact hC₂inj ha2 hb2 hkey
    · exact (hkey₂later a ha2 b hb3 hkey).elim
    · exact (hkey₀later b hb0 a (by simp [ha3]) hkey.symm).elim
    · exact (hkey₁later b hb1 a (by simp [ha3]) hkey.symm).elim
    · exact (hkey₂later b hb2 a ha3 hkey.symm).elim
    · exact hC₃inj ha3 hb3 hkey
  let Bad : RoutedArm G A root Key target m →
      RoutedArm G A root Key target m → Prop :=
    fun a b ↦ ¬ Disjoint a.exposure (target b.key)
  have hC₀sub : C₀ ⊆ Call := by intro a ha; simp [Call, ha]
  have hC₁sub : C₁ ⊆ Call := by intro a ha; simp [Call, ha]
  have hC₂sub : C₂ ⊆ Call := by intro a ha; simp [Call, ha]
  have hC₃sub : C₃ ⊆ Call := by intro a ha; simp [Call, ha]
  have hout₀ : ∀ a ∈ C₀,
      (C₁.filter (Bad a)).card + (C₂.filter (Bad a)).card +
        (C₃.filter (Bad a)).card ≤ m := by
    simpa only [Bad] using RoutedArm.total_other_target_hits_le
      Call C₀ C₁ C₂ C₃ hCallInj hC₀sub hC₁sub hC₂sub hC₃sub
      hC₀C₁ hC₀C₂ hC₀C₃ hC₁C₂ hC₁C₃ hC₂C₃ htargetPair
  have hout₁ : ∀ a ∈ C₁,
      (C₀.filter (Bad a)).card + (C₂.filter (Bad a)).card +
        (C₃.filter (Bad a)).card ≤ m := by
    simpa only [Bad] using RoutedArm.total_other_target_hits_le
      Call C₁ C₀ C₂ C₃ hCallInj hC₁sub hC₀sub hC₂sub hC₃sub
      hC₀C₁.symm hC₁C₂ hC₁C₃ hC₀C₂ hC₀C₃ hC₂C₃
      htargetPair
  have hout₂ : ∀ a ∈ C₂,
      (C₀.filter (Bad a)).card + (C₁.filter (Bad a)).card +
        (C₃.filter (Bad a)).card ≤ m := by
    simpa only [Bad] using RoutedArm.total_other_target_hits_le
      Call C₂ C₀ C₁ C₃ hCallInj hC₂sub hC₀sub hC₁sub hC₃sub
      hC₀C₂.symm hC₁C₂.symm hC₂C₃ hC₀C₁ hC₀C₃ hC₁C₃
      htargetPair
  have hout₃ : ∀ a ∈ C₃,
      (C₀.filter (Bad a)).card + (C₁.filter (Bad a)).card +
        (C₂.filter (Bad a)).card ≤ m := by
    simpa only [Bad] using RoutedArm.total_other_target_hits_le
      Call C₃ C₀ C₁ C₂ hCallInj hC₃sub hC₀sub hC₁sub hC₂sub
      hC₀C₃.symm hC₁C₃.symm hC₂C₃.symm hC₀C₁ hC₀C₂ hC₁C₂
      htargetPair
  have hselectSmall : 4 * m * M ^ 3 < M ^ 4 := by
    dsimp [M]
    calc
      4 * m * (8 * m) ^ 3 = 2048 * m ^ 4 := by ring
      _ < 4096 * m ^ 4 := by
        have hm4 : 0 < m ^ 4 := pow_pos hm 4
        omega
      _ = (8 * m) ^ 4 := by ring
  have badFilterCard_eq
      (a : RoutedArm G A root Key target m)
      (s : Finset (RoutedArm G A root Key target m)) :
      (@Finset.filter _ (Bad a) (fun _ ↦ instDecidableNot) s).card =
        (@Finset.filter _ (Bad a)
          (fun b ↦ Classical.propDecidable (Bad a b)) s).card := by
    exact congrArg Finset.card
      (@Finset.filter_congr_decidable _ s (Bad a)
        (fun _ ↦ instDecidableNot)
        (fun b ↦ Classical.propDecidable (Bad a b)))
  obtain ⟨c₀, hc₀, c₁, hc₁, c₂, hc₂, c₃, hc₃,
      h₀₁, h₀₂, h₀₃, h₁₀, h₁₂, h₁₃,
      h₂₀, h₂₁, h₂₃, h₃₀, h₃₁, h₃₂⟩ :=
    exists_good_four_of_total_bad_degree C₀ C₁ C₂ C₃ Bad M m
      hC₀card hC₁card hC₂card hC₃card
      (fun a ha ↦ by
        rw [← badFilterCard_eq a C₁, ← badFilterCard_eq a C₂,
          ← badFilterCard_eq a C₃]
        exact hout₀ a ha)
      (fun a ha ↦ by
        rw [← badFilterCard_eq a C₀, ← badFilterCard_eq a C₂,
          ← badFilterCard_eq a C₃]
        exact hout₁ a ha)
      (fun a ha ↦ by
        rw [← badFilterCard_eq a C₀, ← badFilterCard_eq a C₁,
          ← badFilterCard_eq a C₃]
        exact hout₂ a ha)
      (fun a ha ↦ by
        rw [← badFilterCard_eq a C₀, ← badFilterCard_eq a C₁,
          ← badFilterCard_eq a C₂]
        exact hout₃ a ha)
      hselectSmall
  have hpath₀₁ : Disjoint c₀.path.support.toFinset c₁.path.support.toFinset := by
    obtain ⟨hprot, -, -⟩ := hC₁meta c₁ hc₁
    apply RoutedArm.disjoint_of_support_subset_protected c₀ c₁ W₁
    · exact Finset.subset_union_right.trans' (mem_routedPathUnion hc₀)
    · exact hprot
  have hpath₀₂ : Disjoint c₀.path.support.toFinset c₂.path.support.toFinset := by
    obtain ⟨hprot, -, -⟩ := hC₂meta c₂ hc₂
    apply RoutedArm.disjoint_of_support_subset_protected c₀ c₂ W₂
    · exact (mem_routedPathUnion hc₀).trans <| by
        intro z hz
        exact Finset.mem_union_left _ (Finset.mem_union_right _ hz)
    · exact hprot
  have hpath₁₂ : Disjoint c₁.path.support.toFinset c₂.path.support.toFinset := by
    obtain ⟨hprot, -, -⟩ := hC₂meta c₂ hc₂
    apply RoutedArm.disjoint_of_support_subset_protected c₁ c₂ W₂
    · exact Finset.subset_union_right.trans' (mem_routedPathUnion hc₁)
    · exact hprot
  have hpath₀₃ : Disjoint c₀.path.support.toFinset c₃.path.support.toFinset := by
    obtain ⟨hprot, -, -⟩ := hC₃meta c₃ hc₃
    apply RoutedArm.disjoint_of_support_subset_protected c₀ c₃ W₃
    · intro z hz
      exact Finset.mem_union_left _ <| Finset.mem_union_left _ <|
        Finset.mem_union_right _ (mem_routedPathUnion hc₀ hz)
    · exact hprot
  have hpath₁₃ : Disjoint c₁.path.support.toFinset c₃.path.support.toFinset := by
    obtain ⟨hprot, -, -⟩ := hC₃meta c₃ hc₃
    apply RoutedArm.disjoint_of_support_subset_protected c₁ c₃ W₃
    · intro z hz
      exact Finset.mem_union_left _ <| Finset.mem_union_right _
        (mem_routedPathUnion hc₁ hz)
    · exact hprot
  have hpath₂₃ : Disjoint c₂.path.support.toFinset c₃.path.support.toFinset := by
    obtain ⟨hprot, -, -⟩ := hC₃meta c₃ hc₃
    apply RoutedArm.disjoint_of_support_subset_protected c₂ c₃ W₃
    · exact Finset.subset_union_right.trans' (mem_routedPathUnion hc₂)
    · exact hprot
  have hi₁₀ : i₁ ≠ i₀ := (Finset.mem_erase.1 hi₁).1
  have hi₂₁ : i₂ ≠ i₁ := (Finset.mem_erase.1 hi₂).1
  have hi₂₀ : i₂ ≠ i₀ :=
    (Finset.mem_erase.1 (Finset.mem_of_mem_erase hi₂)).1
  have hi₃₂ : i₃ ≠ i₂ := (Finset.mem_erase.1 hi₃).1
  have hi₃₁ : i₃ ≠ i₁ :=
    (Finset.mem_erase.1 (Finset.mem_of_mem_erase hi₃)).1
  have hi₃₀ : i₃ ≠ i₀ :=
    (Finset.mem_erase.1 (Finset.mem_of_mem_erase
      (Finset.mem_of_mem_erase hi₃))).1
  let σ : Fin 4 → Fin 4 := ![i₀, i₁, i₂, i₃]
  have hσinj : Function.Injective σ := by
    intro s t hst
    fin_cases s <;> fin_cases t <;> simp only [σ, Matrix.cons_val_zero,
      Matrix.cons_val_one, Fin.isValue] at hst
    · rfl
    · exact (hi₁₀ hst.symm).elim
    · exact (hi₂₀ hst.symm).elim
    · exact (hi₃₀ hst.symm).elim
    · exact (hi₁₀ hst).elim
    · rfl
    · exact (hi₂₁ hst.symm).elim
    · exact (hi₃₁ hst.symm).elim
    · exact (hi₂₀ hst).elim
    · exact (hi₂₁ hst).elim
    · rfl
    · exact (hi₃₂ hst.symm).elim
    · exact (hi₃₀ hst).elim
    · exact (hi₃₁ hst).elim
    · exact (hi₃₂ hst).elim
    · rfl
  let stageArm : Fin 4 → RoutedArm G A root Key target m := ![c₀, c₁, c₂, c₃]
  have hstageMem (s : Fin 4) : stageArm s ∈ Call := by
    fin_cases s <;> simp [stageArm, Call, hc₀, hc₁, hc₂, hc₃]
  have hstageOwner (s : Fin 4) : (stageArm s).owner = σ s := by
    fin_cases s <;> simp [stageArm, σ, hC₀owner c₀ hc₀,
      hC₁owner c₁ hc₁, hC₂owner c₂ hc₂,
      hC₃owner c₃ hc₃]
  have hstagePaths (s t : Fin 4) (hst : s ≠ t) :
      Disjoint (stageArm s).path.support.toFinset
        (stageArm t).path.support.toFinset := by
    fin_cases s <;> fin_cases t
    · exact (hst rfl).elim
    · exact hpath₀₁
    · exact hpath₀₂
    · exact hpath₀₃
    · exact hpath₀₁.symm
    · exact (hst rfl).elim
    · exact hpath₁₂
    · exact hpath₁₃
    · exact hpath₀₂.symm
    · exact hpath₁₂.symm
    · exact (hst rfl).elim
    · exact hpath₂₃
    · exact hpath₀₃.symm
    · exact hpath₁₃.symm
    · exact hpath₂₃.symm
    · exact (hst rfl).elim
  have hstageExposure (s t : Fin 4) (hst : s ≠ t) :
      Disjoint (stageArm s).exposure (target (stageArm t).key) := by
    fin_cases s <;> fin_cases t
    · exact (hst rfl).elim
    · change Disjoint c₀.exposure (target c₁.key)
      exact not_not.mp (by simpa only [Bad] using h₀₁)
    · change Disjoint c₀.exposure (target c₂.key)
      exact not_not.mp (by simpa only [Bad] using h₀₂)
    · change Disjoint c₀.exposure (target c₃.key)
      exact not_not.mp (by simpa only [Bad] using h₀₃)
    · change Disjoint c₁.exposure (target c₀.key)
      exact not_not.mp (by simpa only [Bad] using h₁₀)
    · exact (hst rfl).elim
    · change Disjoint c₁.exposure (target c₂.key)
      exact not_not.mp (by simpa only [Bad] using h₁₂)
    · change Disjoint c₁.exposure (target c₃.key)
      exact not_not.mp (by simpa only [Bad] using h₁₃)
    · change Disjoint c₂.exposure (target c₀.key)
      exact not_not.mp (by simpa only [Bad] using h₂₀)
    · change Disjoint c₂.exposure (target c₁.key)
      exact not_not.mp (by simpa only [Bad] using h₂₁)
    · exact (hst rfl).elim
    · change Disjoint c₂.exposure (target c₃.key)
      exact not_not.mp (by simpa only [Bad] using h₂₃)
    · change Disjoint c₃.exposure (target c₀.key)
      exact not_not.mp (by simpa only [Bad] using h₃₀)
    · change Disjoint c₃.exposure (target c₁.key)
      exact not_not.mp (by simpa only [Bad] using h₃₁)
    · change Disjoint c₃.exposure (target c₂.key)
      exact not_not.mp (by simpa only [Bad] using h₃₂)
    · exact (hst rfl).elim
  have hstageKey : Function.Injective fun s ↦ (stageArm s).key := by
    intro s t hkey
    have harm : stageArm s = stageArm t :=
      hCallInj (hstageMem s) (hstageMem t) hkey
    apply hσinj
    rw [← hstageOwner s, ← hstageOwner t]
    exact congrArg
      (fun P : RoutedArm G A root Key target m ↦ P.owner) harm
  exact enlargedFourConclusion_of_routed_permutation (G := G)
    B hBA hBpair hTargetRadius σ hσinj stageArm hstageOwner hstageKey
      hstagePaths (by simpa only [target] using hstageExposure)



/-- Concrete source-faithful Liu--Montgomery Lemma 3.13. -/
theorem liuMontgomery_lemma3_13_finite [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (epsilon kappa : ℝ)
    (hexp : IsLMExpander G epsilon kappa)
    {v₁ v₂ v₃ v₄ : V}
    {D K L m freshRadius pathRadius rounds freshWorkspace pathWorkspace : ℕ}
    (N : LM315Numerics G epsilon kappa D K L m freshRadius pathRadius rounds
      freshWorkspace pathWorkspace)
    (hdegree : ∀ v : V, N.degreeScale ≤ G.degree v)
    (A : Finset V)
    (E₁ : VertexExpansion G v₁ D m)
    (E₂ : VertexExpansion G v₂ D m)
    (E₃ : VertexExpansion G v₃ D m)
    (E₄ : VertexExpansion G v₄ D m)
    (hA₁ : Disjoint E₁.verts A) (hA₂ : Disjoint E₂.verts A)
    (hA₃ : Disjoint E₃.verts A) (hA₄ : Disjoint E₄.verts A)
    (h₁₂ : Disjoint E₁.verts E₂.verts)
    (h₁₃ : Disjoint E₁.verts E₃.verts)
    (h₁₄ : Disjoint E₁.verts E₄.verts)
    (h₂₃ : Disjoint E₂.verts E₃.verts)
    (h₂₄ : Disjoint E₂.verts E₄.verts)
    (h₃₄ : Disjoint E₃.verts E₄.verts)
    (hfreshWorkspace : A.card + 4 * D + (32 * m) * L ≤ freshWorkspace)
    (hrouteWorkspace :
      A.card + (8 * m) * (7 * m + 4) ≤ N.routeWorkspace) :
    ∃ F₁ : VertexExpansion G v₁ L (3 * m),
      ∃ F₂ : VertexExpansion G v₂ L (3 * m),
      ∃ F₃ : VertexExpansion G v₃ L (3 * m),
      ∃ F₄ : VertexExpansion G v₄ L (3 * m),
        Disjoint F₁.verts A ∧ Disjoint F₂.verts A ∧
        Disjoint F₃.verts A ∧ Disjoint F₄.verts A ∧
        Disjoint F₁.verts F₂.verts ∧ Disjoint F₁.verts F₃.verts ∧
        Disjoint F₁.verts F₄.verts ∧ Disjoint F₂.verts F₃.verts ∧
        Disjoint F₂.verts F₄.verts ∧ Disjoint F₃.verts F₄.verts := by
  let originalDecAdj : DecidableRel G.Adj := inferInstance
  classical
  letI : DecidableRel G.Adj := originalDecAdj
  let data : Fin 4 → Σ v : V, VertexExpansion G v D m :=
    ![⟨v₁, E₁⟩, ⟨v₂, E₂⟩, ⟨v₃, E₃⟩, ⟨v₄, E₄⟩]
  let root : Fin 4 → V := fun i ↦ (data i).1
  let E : ∀ i : Fin 4, VertexExpansion G (root i) D m :=
    fun i ↦ (data i).2
  have hEA : ∀ i, Disjoint (E i).verts A := by
    intro i
    fin_cases i
    · change Disjoint E₁.verts A
      exact hA₁
    · change Disjoint E₂.verts A
      exact hA₂
    · change Disjoint E₃.verts A
      exact hA₃
    · change Disjoint E₄.verts A
      exact hA₄
  have hEpair : ∀ i j, i ≠ j → Disjoint (E i).verts (E j).verts := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · change Disjoint E₁.verts E₂.verts
      exact h₁₂
    · change Disjoint E₁.verts E₃.verts
      exact h₁₃
    · change Disjoint E₁.verts E₄.verts
      exact h₁₄
    · change Disjoint E₂.verts E₁.verts
      exact h₁₂.symm
    · exact (hij rfl).elim
    · change Disjoint E₂.verts E₃.verts
      exact h₂₃
    · change Disjoint E₂.verts E₄.verts
      exact h₂₄
    · change Disjoint E₃.verts E₁.verts
      exact h₁₃.symm
    · change Disjoint E₃.verts E₂.verts
      exact h₂₃.symm
    · exact (hij rfl).elim
    · change Disjoint E₃.verts E₄.verts
      exact h₃₄
    · change Disjoint E₄.verts E₁.verts
      exact h₁₄.symm
    · change Disjoint E₄.verts E₂.verts
      exact h₂₄.symm
    · change Disjoint E₄.verts E₃.verts
      exact h₃₄.symm
    · exact (hij rfl).elim
  let base := A ∪ Finset.univ.biUnion fun i : Fin 4 ↦ (E i).verts
  have hbaseCard : base.card ≤ A.card + 4 * D := by
    have hu := Finset.card_union_le A
      (Finset.univ.biUnion fun i : Fin 4 ↦ (E i).verts)
    have hb :
        (Finset.univ.biUnion fun i : Fin 4 ↦ (E i).verts).card ≤ 4 * D := by
      calc
        _ ≤ ∑ i ∈ (Finset.univ : Finset (Fin 4)), (E i).verts.card :=
          Finset.card_biUnion_le
        _ = 4 * D := by simp [VertexExpansion.card_verts]
    calc
      base.card ≤ A.card +
          (Finset.univ.biUnion fun i : Fin 4 ↦ (E i).verts).card := by
        simpa [base] using hu
      _ ≤ A.card + 4 * D := Nat.add_le_add_left hb A.card
  have hfresh : base.card + (32 * m) * L ≤ freshWorkspace := by omega
  obtain ⟨targetRoot, B, hBbase, hBpair⟩ :=
    exists_fresh_expansion_family G epsilon kappa hexp base (32 * m)
      N.schedule N.growth_K hfresh N.room N.K_pos N.L_pos N.L_le_K N.halve
  have hBA : ∀ k, Disjoint (B k).verts A := by
    intro k
    exact hBbase k |>.mono_right Finset.subset_union_left
  have hBE : ∀ k i, Disjoint (B k).verts (E i).verts := by
    intro k i
    apply (hBbase k).mono_right
    intro z hz
    exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨i, by simp, hz⟩)
  have hBpair' : ∀ k l, k ≠ l → Disjoint (B k).verts (B l).verts := by
    intro k l hkl
    exact hBpair (by simp) (by simp) hkl
  obtain ⟨F, hFA, hFpair⟩ :=
    enlargedFourConclusion_of_candidates G epsilon kappa hexp A root D L
      (freshRadius * rounds) m N.routeStart N.routeWorkspace pathRadius
      N.m_pos N.degreeScale hdegree N.growth_route N.routeStart_pos
      N.connector_radius hrouteWorkspace N.route_source_survives
      N.route_target_survives N.route_source_seed N.route_target_seed N.fresh_radius
      (by simp) targetRoot B hBA hBpair' E hEA hEpair hBE
  let F₁ := F 0
  let F₂ := F 1
  let F₃ := F 2
  let F₄ := F 3
  refine ⟨F₁, F₂, F₃, F₄, hFA 0, hFA 1, hFA 2, hFA 3, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hFpair (by simp) (by simp) (by decide)
  · exact hFpair (by simp) (by simp) (by decide)
  · exact hFpair (by simp) (by simp) (by decide)
  · exact hFpair (by simp) (by simp) (by decide)
  · exact hFpair (by simp) (by simp) (by decide)
  · exact hFpair (by simp) (by simp) (by decide)

/-! ## Long paths between two expansions (Lemma 3.14) -/

/-- Two disjoint partial paths together with large expansions at their moving
ends.  This is the paired state used in the source proof of Lemma 3.14. -/
structure PairedLongConnectorState (G : SimpleGraph V) (X : Finset V)
    (start₁ : V) (start₂ : V) (L m : ℕ) where
  finish₁ : V
  finish₂ : V
  path₁ : G.Walk start₁ finish₁
  path₂ : G.Walk start₂ finish₂
  end₁ : VertexExpansion G finish₁ L (3 * m)
  end₂ : VertexExpansion G finish₂ L (3 * m)
  path₁_isPath : path₁.IsPath
  path₂_isPath : path₂.IsPath
  path₁_avoids : ∀ z ∈ path₁.support, z ∉ X
  path₂_avoids : ∀ z ∈ path₂.support, z ∉ X
  path₁_meets_end₁ : ∀ z ∈ path₁.support, z ∈ end₁.verts → z = finish₁
  path₂_meets_end₂ : ∀ z ∈ path₂.support, z ∈ end₂.verts → z = finish₂
  paths_disjoint : Disjoint path₁.support.toFinset path₂.support.toFinset
  path₁_disjoint_end₂ : Disjoint path₁.support.toFinset end₂.verts
  path₂_disjoint_end₁ : Disjoint path₂.support.toFinset end₁.verts
  end₁_avoids : Disjoint end₁.verts X
  end₂_avoids : Disjoint end₂.verts X
  ends_disjoint : Disjoint end₁.verts end₂.verts

namespace PairedLongConnectorState

variable [Fintype V]
variable {epsilon kappa : ℝ}
variable {D K L m freshRadius pathRadius rounds freshWorkspace pathWorkspace : ℕ}
variable {X : Finset V} {start₁ start₂ : V}

private def total (S : PairedLongConnectorState G X start₁ start₂ L m) : ℕ :=
  S.path₁.length + S.path₂.length

/-
/-- One concrete extension step.  A new expansion is first constructed
outside all vertices currently in use, then connected to the moving end. -/
private theorem extend [DecidableRel G.Adj]
    (hexp : IsLMExpander G epsilon kappa)
    (N : LM315Numerics G epsilon kappa D K L m freshRadius pathRadius rounds
      freshWorkspace pathWorkspace)
    (hdegree : ∀ v : V, N.degreeScale ≤ G.degree v)
    (S : LongConnectorState G X start fixedRoot L m fixed)
    (hfreshBudget :
      (X ∪ S.path.support.toFinset ∪ S.endExpansion.verts ∪ fixed.verts).card ≤
        freshWorkspace)
    (hpathBudget :
      (X ∪ S.path.support.toFinset ∪ fixed.verts).card ≤ pathWorkspace) :
    ∃ T : LongConnectorState G X start fixedRoot L m fixed,
      S.path.length < T.path.length ∧
        T.path.length ≤ S.path.length + 4 * m := by
  classical
  let used := X ∪ S.path.support.toFinset ∪ S.endExpansion.verts ∪ fixed.verts
  obtain ⟨b0, B, hBused⟩ := liuMontgomery_lemma3_12_finite
    G epsilon kappa hexp used freshWorkspace K L freshRadius rounds
      (freshRadius * rounds)
      N.schedule N.growth_K hfreshBudget N.room N.K_pos N.L_pos N.L_le_K
      N.halve le_rfl
  have hBX : Disjoint B.verts X :=
    hBused.mono_right (by intro z hz; simp [used, hz])
  have hBpath : Disjoint B.verts S.path.support.toFinset :=
    hBused.mono_right (by intro z hz; simp [used, hz])
  have hBE : Disjoint B.verts S.endExpansion.verts :=
    hBused.mono_right (by intro z hz; simp [used, hz])
  have hBfixed : Disjoint B.verts fixed.verts :=
    hBused.mono_right (by intro z hz; simp [used, hz])
  let barrier := X ∪ (S.path.support.toFinset.erase S.finish) ∪ fixed.verts
  have hEbarrier : Disjoint S.endExpansion.verts barrier := by
    rw [Finset.disjoint_left]
    intro z hzE hzbar
    simp only [barrier, Finset.mem_union] at hzbar
    rcases hzbar with (hzX | hzpath) | hzfixed
    · exact Finset.disjoint_left.1 S.end_avoids hzE hzX
    · have hzsupport : z ∈ S.path.support := by
        simpa using (Finset.mem_erase.1 hzpath).2
      have hzfinish := S.path_meets_end z hzsupport hzE
      exact (Finset.mem_erase.1 hzpath).1 hzfinish
    · exact Finset.disjoint_left.1 S.end_disjoint_fixed hzE hzfixed
  have hBbarrier : Disjoint B.verts barrier := by
    rw [Finset.disjoint_left]
    intro z hzB hzbar
    simp only [barrier, Finset.mem_union] at hzbar
    rcases hzbar with (hzX | hzpath) | hzfixed
    · exact Finset.disjoint_left.1 hBX hzB hzX
    · exact Finset.disjoint_left.1 hBpath hzB (by
        simpa using (Finset.mem_erase.1 hzpath).2)
    · exact Finset.disjoint_left.1 hBfixed hzB hzfixed
  have hbarrier : barrier.card ≤ pathWorkspace := by
    apply (Finset.card_le_card ?_).trans hpathBudget
    intro z hz
    simp only [barrier, used, Finset.mem_union] at hz ⊢
    rcases hz with (hzX | hzpath) | hzfixed
    · exact Or.inl (Or.inl (Or.inl hzX))
    · exact Or.inl (Or.inl (Or.inr (Finset.mem_erase.1 hzpath).2))
    · exact Or.inr hzfixed
  let Bm : VertexExpansion G b0 L (3 * m) :=
    B.radiusMono (by omega : freshRadius * rounds ≤ 3 * m)
  have hBmBarrier : Disjoint Bm.verts barrier := by simpa [Bm] using hBbarrier
  have hEBm : Disjoint S.endExpansion.verts Bm.verts := by
    simpa [Bm] using hBE.symm
  obtain ⟨b, hb, q, hq, hqbarrier, hqlen, hqfirst⟩ :=
    exists_path_to_first_entry G epsilon kappa hexp S.endExpansion Bm
      barrier pathWorkspace pathRadius hEbarrier hBmBarrier hEBm hbarrier
      N.growth_L N.growth_L
  have hqlen4 : q.length ≤ 4 * m := by omega
  have hinter : ∀ z : V, z ∈ S.path.support → z ∈ q.support → z = S.finish := by
    intro z hzp hzq
    by_cases hzfinish : z = S.finish
    · exact hzfinish
    · have hzbarrier : z ∈ barrier := by
        simp [barrier, hzp, hzfinish]
      exact (hqbarrier z hzq hzbarrier).elim
  let newPath : G.Walk start b := S.path.append q
  have hnewPath : newPath.IsPath :=
    S.path_isPath.append_of_inter_eq_end hq hinter
  have hbB : b ∈ B.verts := by simpa [Bm] using hb
  let newEnd : VertexExpansion G b L (3 * m) :=
    (B.reroot hbB).radiusMono
      (by omega : 2 * (freshRadius * rounds) ≤ 3 * m)
  have hnewAvoids : ∀ z ∈ newPath.support, z ∉ X := by
    intro z hz hzX
    rw [newPath, Walk.mem_support_append_iff] at hz
    rcases hz with hz | hz
    · exact S.path_avoids z hz hzX
    · exact hqbarrier z hz (by simp [barrier, hzX])
  have hnewMeets : ∀ z ∈ newPath.support, z ∈ newEnd.verts → z = b := by
    intro z hz hzB
    have hzB' : z ∈ B.verts := by simpa [newEnd] using hzB
    rw [newPath, Walk.mem_support_append_iff] at hz
    rcases hz with hz | hz
    · exact (Finset.disjoint_left.1 hBpath hzB' (by simpa using hz)).elim
    · exact hqfirst z hz (by simpa [Bm] using hzB')
  have hnewFixed : Disjoint newPath.support.toFinset fixed.verts := by
    rw [Finset.disjoint_left]
    intro z hz hzfixed
    have hz' : z ∈ newPath.support := by simpa using hz
    rw [newPath, Walk.mem_support_append_iff] at hz'
    rcases hz' with hz' | hz'
    · exact Finset.disjoint_left.1 S.path_disjoint_fixed (by simpa using hz') hzfixed
    · exact hqbarrier z hz' (by simp [barrier, hzfixed])
  let T : LongConnectorState G X start fixedRoot L m fixed :=
    { finish := b
      path := newPath
      endExpansion := newEnd
      path_isPath := hnewPath
      path_avoids := hnewAvoids
      path_meets_end := hnewMeets
      path_disjoint_fixed := hnewFixed
      end_avoids := by simpa [newEnd] using hBX
      end_disjoint_fixed := by simpa [newEnd] using hBfixed }
  refine ⟨T, ?_, ?_⟩
  · have hne : S.finish ≠ b := by
      intro heq
      have hfinishE := S.endExpansion.root_mem
      have hbB' : b ∈ B.verts := hbB
      exact Finset.disjoint_left.1 hBE hbB' (heq ▸ hfinishE)
    have hqpos : 0 < q.length := by
      by_contra h
      exact hne (q.eq_of_length_eq_zero (Nat.eq_zero_of_not_pos h))
    simp only [T, newPath, Walk.length_append]
    omega
  · simp only [T, newPath, Walk.length_append]
    omega

-/

private def swap
    (S : PairedLongConnectorState G X start₁ start₂ L m) :
    PairedLongConnectorState G X start₂ start₁ L m where
  finish₁ := S.finish₂
  finish₂ := S.finish₁
  path₁ := S.path₂
  path₂ := S.path₁
  end₁ := S.end₂
  end₂ := S.end₁
  path₁_isPath := S.path₂_isPath
  path₂_isPath := S.path₁_isPath
  path₁_avoids := S.path₂_avoids
  path₂_avoids := S.path₁_avoids
  path₁_meets_end₁ := S.path₂_meets_end₂
  path₂_meets_end₂ := S.path₁_meets_end₁
  paths_disjoint := S.paths_disjoint.symm
  path₁_disjoint_end₂ := S.path₂_disjoint_end₁
  path₂_disjoint_end₁ := S.path₁_disjoint_end₂
  end₁_avoids := S.end₂_avoids
  end₂_avoids := S.end₁_avoids
  ends_disjoint := S.ends_disjoint.symm

@[simp] private theorem total_swap
    (S : PairedLongConnectorState G X start₁ start₂ L m) :
    S.swap.total = S.total := by
  simp [PairedLongConnectorState.swap, PairedLongConnectorState.total,
    Nat.add_comm]

/-- Update the first arm once a clean link to a new end expansion has been
constructed.  The symmetric update is obtained by `swap`. -/
private theorem extendLeft
    (S : PairedLongConnectorState G X start₁ start₂ L m)
    {b : V} (newEnd : VertexExpansion G b L (3 * m))
    (q : G.Walk S.finish₁ b)
    (hq : q.IsPath) (hqpos : 0 < q.length) (hqlen : q.length ≤ 4 * m)
    (hqX : ∀ z ∈ q.support, z ∉ X)
    (hinter : ∀ z, z ∈ S.path₁.support → z ∈ q.support → z = S.finish₁)
    (hqPath₂ : Disjoint q.support.toFinset S.path₂.support.toFinset)
    (hqEnd₂ : Disjoint q.support.toFinset S.end₂.verts)
    (hqNew : ∀ z ∈ q.support, z ∈ newEnd.verts → z = b)
    (hOldNew : Disjoint S.path₁.support.toFinset newEnd.verts)
    (hPath₂New : Disjoint S.path₂.support.toFinset newEnd.verts)
    (hNewX : Disjoint newEnd.verts X)
    (hNewEnd₂ : Disjoint newEnd.verts S.end₂.verts) :
    ∃ T : PairedLongConnectorState G X start₁ start₂ L m,
      S.total < T.total ∧ T.total ≤ S.total + 4 * m := by
  let originalDecAdj : DecidableRel G.Adj := inferInstance
  classical
  letI : DecidableRel G.Adj := originalDecAdj
  let newPath : G.Walk start₁ b := S.path₁.append q
  let T : PairedLongConnectorState G X start₁ start₂ L m :=
    { finish₁ := b
      finish₂ := S.finish₂
      path₁ := newPath
      path₂ := S.path₂
      end₁ := newEnd
      end₂ := S.end₂
      path₁_isPath :=
        Walk.IsPath.append_of_inter_eq_end S.path₁_isPath hq hinter
      path₂_isPath := S.path₂_isPath
      path₁_avoids := by
        intro z hz hzX
        change z ∈ (S.path₁.append q).support at hz
        rw [Walk.mem_support_append_iff] at hz
        rcases hz with hz | hz
        · exact S.path₁_avoids z hz hzX
        · exact hqX z hz hzX
      path₂_avoids := S.path₂_avoids
      path₁_meets_end₁ := by
        intro z hz hzB
        change z ∈ (S.path₁.append q).support at hz
        rw [Walk.mem_support_append_iff] at hz
        rcases hz with hz | hz
        · exact (Finset.disjoint_left.1 hOldNew (by simpa using hz) hzB).elim
        · exact hqNew z hz hzB
      path₂_meets_end₂ := S.path₂_meets_end₂
      paths_disjoint := by
        rw [Finset.disjoint_left]
        intro z hz hz₂
        have hz' : z ∈ newPath.support := by simpa using hz
        change z ∈ (S.path₁.append q).support at hz'
        rw [Walk.mem_support_append_iff] at hz'
        rcases hz' with hz' | hz'
        · exact Finset.disjoint_left.1 S.paths_disjoint (by simpa using hz') hz₂
        · exact Finset.disjoint_left.1 hqPath₂ (by simpa using hz') hz₂
      path₁_disjoint_end₂ := by
        rw [Finset.disjoint_left]
        intro z hz hz₂
        have hz' : z ∈ newPath.support := by simpa using hz
        change z ∈ (S.path₁.append q).support at hz'
        rw [Walk.mem_support_append_iff] at hz'
        rcases hz' with hz' | hz'
        · exact Finset.disjoint_left.1 S.path₁_disjoint_end₂
            (by simpa using hz') hz₂
        · exact Finset.disjoint_left.1 hqEnd₂ (by simpa using hz') hz₂
      path₂_disjoint_end₁ := hPath₂New
      end₁_avoids := hNewX
      end₂_avoids := S.end₂_avoids
      ends_disjoint := hNewEnd₂ }
  refine ⟨T, ?_, ?_⟩
  · simp only [T, PairedLongConnectorState.total, newPath, Walk.length_append]
    omega
  · simp only [T, PairedLongConnectorState.total, newPath, Walk.length_append]
    omega

/-- Attach a clean end-to-fresh-expansion segment to the first arm. -/
private theorem extendViaFirst
    (S : PairedLongConnectorState G X start₁ start₂ L m)
    {a b : V} (newEnd : VertexExpansion G b L (3 * m))
    (q : G.Walk a b) (ha : a ∈ S.end₁.verts)
    (hq : q.IsPath) (hqlen : q.length ≤ m)
    (hqX : ∀ z ∈ q.support, z ∉ X)
    (hqEnd₁ : ∀ z ∈ q.support, z ∈ S.end₁.verts → z = a)
    (hqEnd₂ : Disjoint q.support.toFinset S.end₂.verts)
    (hqPath₁ : ∀ z ∈ q.support, z ∈ S.path₁.support → z = S.finish₁)
    (hqPath₂ : Disjoint q.support.toFinset S.path₂.support.toFinset)
    (hqNew : ∀ z ∈ q.support, z ∈ newEnd.verts → z = b)
    (hOldNew : Disjoint S.path₁.support.toFinset newEnd.verts)
    (hPath₂New : Disjoint S.path₂.support.toFinset newEnd.verts)
    (hNewX : Disjoint newEnd.verts X)
    (hNewEnd₁ : Disjoint newEnd.verts S.end₁.verts)
    (hNewEnd₂ : Disjoint newEnd.verts S.end₂.verts) :
    ∃ T : PairedLongConnectorState G X start₁ start₂ L m,
      S.total < T.total ∧ T.total ≤ S.total + 4 * m := by
  obtain ⟨px, hpx, hpxlen, hpxsupp⟩ := S.end₁.exists_path ha
  let link : G.Walk S.finish₁ b := px.append q
  have hpxq : ∀ z, z ∈ px.support → z ∈ q.support → z = a := by
    intro z hzpx hzq
    exact hqEnd₁ z hzq (hpxsupp z hzpx)
  have hlink : link.IsPath :=
    Walk.IsPath.append_of_inter_eq_end hpx hq hpxq
  have hlinklen : link.length ≤ 4 * m := by
    calc
      link.length = px.length + q.length := by simp [link]
      _ ≤ 3 * m + m := Nat.add_le_add hpxlen hqlen
      _ = 4 * m := by omega
  have hlinkpos : 0 < link.length := by
    have hne : S.finish₁ ≠ b := by
      intro heq
      exact Finset.disjoint_left.1 hNewEnd₁ newEnd.root_mem
        (heq ▸ S.end₁.root_mem)
    by_contra h
    exact hne (link.eq_of_length_eq_zero (Nat.eq_zero_of_not_pos h))
  have hlinkX : ∀ z ∈ link.support, z ∉ X := by
    intro z hz hzX
    change z ∈ (px.append q).support at hz
    rw [Walk.mem_support_append_iff] at hz
    rcases hz with hz | hz
    · exact Finset.disjoint_left.1 S.end₁_avoids (hpxsupp z hz) hzX
    · exact hqX z hz hzX
  have hOldInter : ∀ z, z ∈ S.path₁.support →
      z ∈ link.support → z = S.finish₁ := by
    intro z hzold hzlink
    change z ∈ (px.append q).support at hzlink
    rw [Walk.mem_support_append_iff] at hzlink
    rcases hzlink with hzpx | hzq
    · exact S.path₁_meets_end₁ z hzold (hpxsupp z hzpx)
    · exact hqPath₁ z hzq hzold
  have hLinkPath₂ : Disjoint link.support.toFinset S.path₂.support.toFinset := by
    rw [Finset.disjoint_left]
    intro z hzlink hzP₂
    have hzlink' : z ∈ link.support := by simpa using hzlink
    change z ∈ (px.append q).support at hzlink'
    rw [Walk.mem_support_append_iff] at hzlink'
    rcases hzlink' with hzpx | hzq
    · exact Finset.disjoint_left.1 S.path₂_disjoint_end₁ hzP₂
        (hpxsupp z hzpx)
    · exact Finset.disjoint_left.1 hqPath₂ (by simpa using hzq) hzP₂
  have hLinkEnd₂ : Disjoint link.support.toFinset S.end₂.verts := by
    rw [Finset.disjoint_left]
    intro z hzlink hzE₂
    have hzlink' : z ∈ link.support := by simpa using hzlink
    change z ∈ (px.append q).support at hzlink'
    rw [Walk.mem_support_append_iff] at hzlink'
    rcases hzlink' with hzpx | hzq
    · exact Finset.disjoint_left.1 S.ends_disjoint (hpxsupp z hzpx) hzE₂
    · exact Finset.disjoint_left.1 hqEnd₂ (by simpa using hzq) hzE₂
  have hLinkNew : ∀ z ∈ link.support, z ∈ newEnd.verts → z = b := by
    intro z hz hzB
    change z ∈ (px.append q).support at hz
    rw [Walk.mem_support_append_iff] at hz
    rcases hz with hzpx | hzq
    · exact (Finset.disjoint_left.1 hNewEnd₁ hzB (hpxsupp z hzpx)).elim
    · exact hqNew z hzq hzB
  exact S.extendLeft newEnd link hlink hlinkpos hlinklen hlinkX hOldInter
    hLinkPath₂ hLinkEnd₂ hLinkNew hOldNew hPath₂New hNewX hNewEnd₂

/-- One paired extension step.  The fresh construction pays for both moving
ends; the connector itself pays only for `X` and the two path interiors. -/
private theorem extend [DecidableRel G.Adj]
    (hexp : IsLMExpander G epsilon kappa)
    (N : LM315Numerics G epsilon kappa D K L m freshRadius pathRadius rounds
      freshWorkspace pathWorkspace)
    (hdegree : ∀ v : V, N.degreeScale ≤ G.degree v)
    (S : PairedLongConnectorState G X start₁ start₂ L m)
    (hfreshBudget :
      (X ∪ S.path₁.support.toFinset ∪ S.path₂.support.toFinset ∪
        S.end₁.verts ∪ S.end₂.verts).card ≤ freshWorkspace)
    (hpathBudget :
      (X ∪ S.path₁.support.toFinset ∪ S.path₂.support.toFinset).card ≤
        pathWorkspace) :
    ∃ T : PairedLongConnectorState G X start₁ start₂ L m,
      S.total < T.total ∧ T.total ≤ S.total + 4 * m := by
  let originalDecAdj : DecidableRel G.Adj := inferInstance
  classical
  letI : DecidableRel G.Adj := originalDecAdj
  let used := X ∪ S.path₁.support.toFinset ∪ S.path₂.support.toFinset ∪
    S.end₁.verts ∪ S.end₂.verts
  obtain ⟨b₀, B, hBused⟩ := liuMontgomery_lemma3_12_finite
    G epsilon kappa hexp used freshWorkspace K L freshRadius rounds
      (freshRadius * rounds)
      N.schedule N.growth_K hfreshBudget N.room N.K_pos N.L_pos N.L_le_K
      N.halve le_rfl
  have hBX : Disjoint B.verts X :=
    hBused.mono_right (by intro z hz; simp [used, hz])
  have hBP₁ : Disjoint B.verts S.path₁.support.toFinset :=
    hBused.mono_right (by intro z hz; simp [used, hz])
  have hBP₂ : Disjoint B.verts S.path₂.support.toFinset :=
    hBused.mono_right (by intro z hz; simp [used, hz])
  have hBE₁ : Disjoint B.verts S.end₁.verts :=
    hBused.mono_right (by intro z hz; simp [used, hz])
  have hBE₂ : Disjoint B.verts S.end₂.verts :=
    hBused.mono_right (by intro z hz; simp [used, hz])
  let barrier := X ∪ (S.path₁.support.toFinset.erase S.finish₁) ∪
    (S.path₂.support.toFinset.erase S.finish₂)
  have hE₁Barrier : Disjoint S.end₁.verts barrier := by
    rw [Finset.disjoint_left]
    intro z hzE hz
    simp only [barrier, Finset.mem_union] at hz
    rcases hz with (hzX | hzP₁) | hzP₂
    · exact Finset.disjoint_left.1 S.end₁_avoids hzE hzX
    · exact (Finset.mem_erase.1 hzP₁).1 <|
        S.path₁_meets_end₁ z
          (List.mem_toFinset.1 (Finset.mem_erase.1 hzP₁).2) hzE
    · exact Finset.disjoint_left.1 S.path₂_disjoint_end₁
        (Finset.mem_erase.1 hzP₂).2 hzE
  have hE₂Barrier : Disjoint S.end₂.verts barrier := by
    rw [Finset.disjoint_left]
    intro z hzE hz
    simp only [barrier, Finset.mem_union] at hz
    rcases hz with (hzX | hzP₁) | hzP₂
    · exact Finset.disjoint_left.1 S.end₂_avoids hzE hzX
    · exact Finset.disjoint_left.1 S.path₁_disjoint_end₂
        (Finset.mem_erase.1 hzP₁).2 hzE
    · exact (Finset.mem_erase.1 hzP₂).1 <|
        S.path₂_meets_end₂ z
          (List.mem_toFinset.1 (Finset.mem_erase.1 hzP₂).2) hzE
  have hBBarrier : Disjoint B.verts barrier := by
    rw [Finset.disjoint_left]
    intro z hzB hz
    simp only [barrier, Finset.mem_union] at hz
    rcases hz with (hzX | hzP₁) | hzP₂
    · exact Finset.disjoint_left.1 hBX hzB hzX
    · exact Finset.disjoint_left.1 hBP₁ hzB (Finset.mem_erase.1 hzP₁).2
    · exact Finset.disjoint_left.1 hBP₂ hzB (Finset.mem_erase.1 hzP₂).2
  have hbarrier : barrier.card ≤ pathWorkspace := by
    apply (Finset.card_le_card ?_).trans hpathBudget
    intro z hz
    simp only [barrier, Finset.mem_union] at hz
    rcases hz with (hzX | hzP₁) | hzP₂
    · simp [hzX]
    · simp [(Finset.mem_erase.1 hzP₁).2]
    · simp [(Finset.mem_erase.1 hzP₂).2]
  let ends := S.end₁.verts ∪ S.end₂.verts
  have hEndsBarrier : Disjoint ends barrier :=
    Finset.disjoint_union_left.2 ⟨hE₁Barrier, hE₂Barrier⟩
  have hEndsCard : L ≤ ends.card := by
    rw [← S.end₁.card_verts]
    exact Finset.card_le_card Finset.subset_union_left
  let Bm : VertexExpansion G b₀ L (3 * m) :=
    B.radiusMono (N.fresh_radius_le.trans <|
      Nat.le_mul_of_pos_left m (by omega : 0 < 3))
  have hBmBarrier : Disjoint Bm.verts barrier := by simpa [Bm] using hBBarrier
  obtain ⟨a₀, ha₀, b₁, hb₁, raw, hraw, hrawlen⟩ :=
    exists_short_set_connector G epsilon kappa hexp N.degreeScale hdegree
      barrier ends Bm.verts N.pathStart pathWorkspace pathRadius hbarrier
      hEndsBarrier hBmBarrier
      ⟨S.finish₁, Finset.mem_union_left _ S.end₁.root_mem⟩
      ⟨b₀, by simpa [Bm] using B.root_mem⟩
      (N.path_seed.imp (fun h ↦ h.trans hEndsCard) id)
      (N.path_seed.imp (fun h ↦ by simpa [Bm, B.card_verts] using h) id)
      N.growth_path
  have hrawEmpty : raw.Avoids (barrier : Set V) (∅ : Set V) := by
    apply Walk.avoids_empty_of_endpoints_outside hraw.2
    · exact fun haB ↦ Finset.disjoint_left.1 hEndsBarrier ha₀ haB
    · exact fun hbB ↦ Finset.disjoint_left.1 hBmBarrier hb₁ hbB
  obtain ⟨a, haEnds, b, hbB, q, hq, hqlen, hqsub, hqEnds, hqB⟩ :=
    exists_minimal_subpath raw hraw.1 ends Bm.verts ha₀ hb₁
  have hqBarrier : q.Avoids (barrier : Set V) (∅ : Set V) := by
    intro z hz hzBarrier
    exact hrawEmpty z (hqsub hz) hzBarrier
  have hqlenM : q.length ≤ m := hqlen.trans <| hrawlen.trans N.connector_radius
  have hbB' : b ∈ B.verts := by simpa [Bm] using hbB
  let newEnd : VertexExpansion G b L (3 * m) :=
    (B.reroot hbB').radiusMono
      (N.fresh_radius.trans <|
        Nat.le_mul_of_pos_left m (by omega : 0 < 3))
  have hNewX : Disjoint newEnd.verts X := by simpa [newEnd] using hBX
  have hNewE₁ : Disjoint newEnd.verts S.end₁.verts := by
    simpa [newEnd] using hBE₁
  have hNewE₂ : Disjoint newEnd.verts S.end₂.verts := by
    simpa [newEnd] using hBE₂
  have hNewP₁ : Disjoint S.path₁.support.toFinset newEnd.verts := by
    simpa [newEnd] using hBP₁.symm
  have hNewP₂ : Disjoint S.path₂.support.toFinset newEnd.verts := by
    simpa [newEnd] using hBP₂.symm
  have hqX : ∀ z ∈ q.support, z ∉ X := by
    intro z hz hzX
    exact hqBarrier z hz (by simp [barrier, hzX])
  have hqNew : ∀ z ∈ q.support, z ∈ newEnd.verts → z = b := by
    intro z hz hzBnew
    apply hqB z hz
    simpa [newEnd, Bm] using hzBnew
  rcases Finset.mem_union.1 haEnds with ha₁ | ha₂
  · have hqE₁ : ∀ z ∈ q.support, z ∈ S.end₁.verts → z = a := by
      intro z hz hzE
      exact hqEnds z hz (Finset.mem_union_left _ hzE)
    have hqE₂ : Disjoint q.support.toFinset S.end₂.verts := by
      rw [Finset.disjoint_left]
      intro z hz hzE₂
      have hza := hqEnds z (by simpa using hz) (Finset.mem_union_right _ hzE₂)
      subst z
      exact Finset.disjoint_left.1 S.ends_disjoint ha₁ hzE₂
    have hqP₁ : ∀ z ∈ q.support, z ∈ S.path₁.support →
        z = S.finish₁ := by
      intro z hz hzP
      by_cases hzf : z = S.finish₁
      · exact hzf
      · exact (hqBarrier z hz (by simp [barrier, hzP, hzf])).elim
    have hqP₂ : Disjoint q.support.toFinset S.path₂.support.toFinset := by
      rw [Finset.disjoint_left]
      intro z hz hzP
      have hzq : z ∈ q.support := by simpa using hz
      by_cases hzf : z = S.finish₂
      · have hza := hqEnds z hzq
            (Finset.mem_union_right _ (hzf.symm ▸ S.end₂.root_mem))
        have haeq : a = S.finish₂ := hza.symm.trans hzf
        exact Finset.disjoint_left.1 S.ends_disjoint ha₁
          (haeq.symm ▸ S.end₂.root_mem)
      · exact hqBarrier z hzq (by
          change z ∈ barrier
          exact Finset.mem_union_right _ <|
            Finset.mem_erase.2 ⟨hzf, by simpa using hzP⟩)
    exact S.extendViaFirst newEnd q ha₁ hq hqlenM hqX hqE₁ hqE₂
      hqP₁ hqP₂ hqNew hNewP₁ hNewP₂ hNewX hNewE₁ hNewE₂
  · have hqE₂ : ∀ z ∈ q.support, z ∈ S.end₂.verts → z = a := by
      intro z hz hzE
      exact hqEnds z hz (Finset.mem_union_right _ hzE)
    have hqE₁ : Disjoint q.support.toFinset S.end₁.verts := by
      rw [Finset.disjoint_left]
      intro z hz hzE₁
      have hza := hqEnds z (by simpa using hz) (Finset.mem_union_left _ hzE₁)
      subst z
      exact Finset.disjoint_left.1 S.ends_disjoint hzE₁ ha₂
    have hqP₂ : ∀ z ∈ q.support, z ∈ S.path₂.support →
        z = S.finish₂ := by
      intro z hz hzP
      by_cases hzf : z = S.finish₂
      · exact hzf
      · exact (hqBarrier z hz (by simp [barrier, hzP, hzf])).elim
    have hqP₁ : Disjoint q.support.toFinset S.path₁.support.toFinset := by
      rw [Finset.disjoint_left]
      intro z hz hzP
      have hzq : z ∈ q.support := by simpa using hz
      by_cases hzf : z = S.finish₁
      · have hza := hqEnds z hzq
            (Finset.mem_union_left _ (hzf.symm ▸ S.end₁.root_mem))
        have haeq : a = S.finish₁ := hza.symm.trans hzf
        exact Finset.disjoint_left.1 S.ends_disjoint
          (haeq.symm ▸ S.end₁.root_mem) ha₂
      · exact hqBarrier z hzq (by
          change z ∈ barrier
          exact Finset.mem_union_left _ <| Finset.mem_union_right _ <|
            Finset.mem_erase.2 ⟨hzf, by simpa using hzP⟩)
    obtain ⟨U, hSU, hUupper⟩ := S.swap.extendViaFirst newEnd q ha₂ hq
      hqlenM hqX hqE₂ hqE₁ hqP₂ hqP₁ hqNew hNewP₂ hNewP₁
      hNewX hNewE₂ hNewE₁
    refine ⟨U.swap, ?_, ?_⟩
    · simpa using hSU
    · simpa using hUupper

end PairedLongConnectorState

/-- A short root-to-root connector through two large expansions. -/
private theorem exists_short_root_connector [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (epsilon kappa : ℝ)
    (hexp : IsLMExpander G epsilon kappa)
    (degreeScale : ℕ) (hdegree : ∀ v : V, degreeScale ≤ G.degree v)
    {x y : V} {L m radius workspace : ℕ}
    (E : VertexExpansion G x L (3 * m))
    (F : VertexExpansion G y L (3 * m))
    (W : Finset V) (hEW : Disjoint E.verts W) (hFW : Disjoint F.verts W)
    (hW : W.card ≤ workspace)
    (start : ℕ) (hseed : start ≤ L ∨ start + workspace ≤ degreeScale)
    (growth : BallGrowthSchedule G epsilon kappa start workspace radius) :
    ∃ p : G.Walk x y, p.IsPath ∧
      (∀ z ∈ p.support, z ∉ W) ∧
        p.length ≤ 6 * m + 2 * (radius + 1) := by
  have hseedE : start ≤ E.verts.card ∨ start + workspace ≤ degreeScale :=
    hseed.imp (fun h ↦ by simpa [E.card_verts] using h) id
  have hseedF : start ≤ F.verts.card ∨ start + workspace ≤ degreeScale :=
    hseed.imp (fun h ↦ by simpa [F.card_verts] using h) id
  have hEhalf := growth.grow_one_more hexp hdegree W E.verts hW hEW
    ⟨x, E.root_mem⟩ hseedE
  have hFhalf := growth.grow_one_more hexp hdegree W F.verts hW hFW
    ⟨y, F.root_mem⟩ hseedF
  obtain ⟨p, hp, hplen, hpW⟩ :=
    E.exists_path_between_roots_of_large_balls
      (r := radius + 1) (s := radius + 1)
      F W hEW.symm hFW.symm (by omega)
  refine ⟨p, hp, hpW, ?_⟩
  omega

/-
/-- Concrete Liu--Montgomery Lemma 3.14.  The source obtains `5m`; the
slightly roomier `11m` here is still more than sufficient for the source's
`22m` corollary and follows from exactly the same extend-then-close argument. -/
theorem liuMontgomery_lemma3_14_finite [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (epsilon kappa : ℝ)
    (hexp : IsLMExpander G epsilon kappa)
    {v₁ v₂ : V}
    {D K L m freshRadius pathRadius rounds freshWorkspace pathWorkspace ell : ℕ}
    (N : LM315Numerics G epsilon kappa D K L m freshRadius pathRadius rounds
      freshWorkspace pathWorkspace)
    (hdegree : ∀ v : V, N.degreeScale ≤ G.degree v)
    (X : Finset V)
    (E₁ : VertexExpansion G v₁ L (3 * m))
    (E₂ : VertexExpansion G v₂ L (3 * m))
    (hE₁X : Disjoint E₁.verts X) (hE₂X : Disjoint E₂.verts X)
    (hE₁E₂ : Disjoint E₁.verts E₂.verts)
    (hfreshWorkspace : X.card + ell + 2 * L + 4 ≤ freshWorkspace)
    (hpathWorkspace : X.card + ell + 2 * L + 4 ≤ pathWorkspace) :
    ∃ p : G.Walk v₁ v₂, p.IsPath ∧
      (∀ z ∈ p.support, z ∉ X) ∧
      ell ≤ p.length ∧ p.length ≤ ell + 11 * m := by
  let originalDecAdj : DecidableRel G.Adj := inferInstance
  classical
  letI : DecidableRel G.Adj := originalDecAdj
  let StateAt : ℕ → Prop := fun n ↦
    ∃ S : LongConnectorState G X v₁ v₂ L m E₂, S.path.length = n
  let S0 : LongConnectorState G X v₁ v₂ L m E₂ :=
    { finish := v₁
      path := Walk.nil
      endExpansion := E₁
      path_isPath := Walk.IsPath.nil
      path_avoids := by
        intro z hz hzX
        have hzv : z = v₁ := by simpa using hz
        subst z
        exact Finset.disjoint_left.1 hE₁X E₁.root_mem hzX
      path_meets_end := by
        intro z hz -
        simpa using hz
      path_disjoint_fixed := by
        rw [Finset.disjoint_left]
        intro z hz hzE₂
        have hzv : z = v₁ := by simpa using hz
        subst z
        exact Finset.disjoint_left.1 hE₁E₂ E₁.root_mem hzE₂
      end_avoids := hE₁X
      end_disjoint_fixed := hE₁E₂ }
  have hState0 : StateAt 0 := ⟨S0, rfl⟩
  let n := Nat.findGreatest StateAt ell
  have hnState : StateAt n :=
    Nat.findGreatest_spec (P := StateAt) (Nat.zero_le _) hState0
  have hnle : n ≤ ell := Nat.findGreatest_le ell
  obtain ⟨S, hSlen⟩ := hnState
  have hSupper : S.path.length ≤ ell := by simpa [hSlen] using hnle
  have hsupportCard : S.path.support.toFinset.card = S.path.length + 1 := by
    rw [List.toFinset_card_of_nodup S.path_isPath.support_nodup,
      S.path.length_support]
  have hstateBudget :
      (X ∪ S.path.support.toFinset ∪ S.endExpansion.verts ∪ E₂.verts).card ≤
        freshWorkspace := by
    have h0 := Finset.card_union_le X S.path.support.toFinset
    have h1 := Finset.card_union_le (X ∪ S.path.support.toFinset)
      S.endExpansion.verts
    have h2 := Finset.card_union_le
      (X ∪ S.path.support.toFinset ∪ S.endExpansion.verts) E₂.verts
    simp only [hsupportCard, S.endExpansion.card_verts, E₂.card_verts] at h0 h1 h2
    omega
  have hstatePathBudget :
      (X ∪ S.path.support.toFinset ∪ E₂.verts).card ≤ pathWorkspace := by
    have h0 := Finset.card_union_le X S.path.support.toFinset
    have h1 := Finset.card_union_le (X ∪ S.path.support.toFinset) E₂.verts
    simp only [hsupportCard, E₂.card_verts] at h0 h1
    omega
  have hexState : ∃ T : LongConnectorState G X v₁ v₂ L m E₂,
      ell ≤ T.path.length ∧ T.path.length ≤ ell + 4 * m := by
    by_cases hell : ell ≤ S.path.length
    · exact ⟨S, hell, by omega⟩
    · obtain ⟨T, hST, hTupper⟩ :=
        S.extend hexp N hstateBudget hstatePathBudget
      by_cases hTell : T.path.length ≤ ell
      · have hStateT : StateAt T.path.length := ⟨T, rfl⟩
        have hmax := Nat.le_findGreatest (P := StateAt) hTell hStateT
        omega
      · exact ⟨T, Nat.le_of_not_ge hTell, by omega⟩
  obtain ⟨T, hTell, hTupper⟩ := hexState
  let barrier := X ∪ T.path.support.toFinset.erase T.finish
  have hEbarrier : Disjoint T.endExpansion.verts barrier := by
    rw [Finset.disjoint_left]
    intro z hzE hz
    simp only [barrier, Finset.mem_union] at hz
    rcases hz with hzX | hzpath
    · exact Finset.disjoint_left.1 T.end_avoids hzE hzX
    · have hzsupp : z ∈ T.path.support := by
        simpa using (Finset.mem_erase.1 hzpath).2
      exact (Finset.mem_erase.1 hzpath).1 (T.path_meets_end z hzsupp hzE)
  have hFbarrier : Disjoint E₂.verts barrier := by
    rw [Finset.disjoint_left]
    intro z hzF hz
    simp only [barrier, Finset.mem_union] at hz
    rcases hz with hzX | hzpath
    · exact Finset.disjoint_left.1 hE₂X hzF hzX
    · exact Finset.disjoint_left.1 T.path_disjoint_fixed
        (by simpa using (Finset.mem_erase.1 hzpath).2) hzF
  have hbarrierCard : barrier.card ≤ pathWorkspace := by
    apply (Finset.card_le_card ?_).trans hstatePathBudget
    intro z hz
    simp only [barrier, Finset.mem_union] at hz
    rcases hz with hzX | hzpath
    · simp [hzX]
    · simp [(Finset.mem_erase.1 hzpath).2]
  obtain ⟨q, hq, hqbarrier, hqlen⟩ :=
    exists_short_root_connector G epsilon kappa hexp T.endExpansion E₂ barrier
      hEbarrier hFbarrier hbarrierCard N.growth_L
  have hqlen7 : q.length ≤ 7 * m := by omega
  have hinter : ∀ z : V, z ∈ T.path.support → z ∈ q.support → z = T.finish := by
    intro z hzp hzq
    by_cases hzfinish : z = T.finish
    · exact hzfinish
    · exact (hqbarrier z hzq (by simp [barrier, hzp, hzfinish])).elim
  let p : G.Walk v₁ v₂ := T.path.append q
  refine ⟨p, T.path_isPath.append_of_inter_eq_end hq hinter, ?_, ?_, ?_⟩
  · intro z hz hzX
    rw [p, Walk.mem_support_append_iff] at hz
    rcases hz with hz | hz
    · exact T.path_avoids z hz hzX
    · exact hqbarrier z hz (by simp [barrier, hzX])
  · simp only [p, Walk.length_append]
    omega
  · simp only [p, Walk.length_append]
    omega
  · exact (hF₃W₃.mono_right (by intro x hx; simp [W₃, hx])).symm
  · exact (hF₄W₄.mono_right (by intro x hx; simp [W₄, hx])).symm
  · exact (hF₄W₄.mono_right (by intro x hx; simp [W₄, hx])).symm
-/

/-- Concrete paired-path form of Liu--Montgomery Lemma 3.14.  The constants
are deliberately recorded in the `11m` form used by Corollary 3.15. -/
theorem liuMontgomery_lemma3_14_finite [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (epsilon kappa : ℝ)
    (hexp : IsLMExpander G epsilon kappa)
    {v₁ v₂ : V}
    {D K L m freshRadius pathRadius rounds freshWorkspace pathWorkspace ell : ℕ}
    (N : LM315Numerics G epsilon kappa D K L m freshRadius pathRadius rounds
      freshWorkspace pathWorkspace)
    (hdegree : ∀ v : V, N.degreeScale ≤ G.degree v)
    (X : Finset V)
    (E₁ : VertexExpansion G v₁ L (3 * m))
    (E₂ : VertexExpansion G v₂ L (3 * m))
    (hE₁X : Disjoint E₁.verts X) (hE₂X : Disjoint E₂.verts X)
    (hE₁E₂ : Disjoint E₁.verts E₂.verts)
    (hfreshWorkspace : X.card + ell + 2 * L + 2 ≤ freshWorkspace)
    (hpathWorkspace : X.card + ell + 4 * m + 2 ≤ pathWorkspace) :
    ∃ p : G.Walk v₁ v₂, p.IsPath ∧
      (∀ z ∈ p.support, z ∉ X) ∧
      ell ≤ p.length ∧ p.length ≤ ell + 11 * m := by
  classical
  let StateAt : ℕ → Prop := fun n ↦
    ∃ S : PairedLongConnectorState G X v₁ v₂ L m, S.total = n
  let S₀ : PairedLongConnectorState G X v₁ v₂ L m :=
    { finish₁ := v₁
      finish₂ := v₂
      path₁ := Walk.nil
      path₂ := Walk.nil
      end₁ := E₁
      end₂ := E₂
      path₁_isPath := Walk.IsPath.nil
      path₂_isPath := Walk.IsPath.nil
      path₁_avoids := by
        intro z hz hzX
        have hzv : z = v₁ := by simpa using hz
        subst z
        exact Finset.disjoint_left.1 hE₁X E₁.root_mem hzX
      path₂_avoids := by
        intro z hz hzX
        have hzv : z = v₂ := by simpa using hz
        subst z
        exact Finset.disjoint_left.1 hE₂X E₂.root_mem hzX
      path₁_meets_end₁ := by
        intro z hz _
        simpa using hz
      path₂_meets_end₂ := by
        intro z hz _
        simpa using hz
      paths_disjoint := by
        rw [Finset.disjoint_left]
        intro z hz₁ hz₂
        have hzv₁ : z = v₁ := by simpa using hz₁
        have hzv₂ : z = v₂ := by simpa using hz₂
        have hvne : v₁ ≠ v₂ := by
          intro h
          exact Finset.disjoint_left.1 hE₁E₂ E₁.root_mem (h ▸ E₂.root_mem)
        exact hvne (hzv₁.symm.trans hzv₂)
      path₁_disjoint_end₂ := by
        rw [Finset.disjoint_left]
        intro z hz hzE₂
        have hzv : z = v₁ := by simpa using hz
        subst z
        exact Finset.disjoint_left.1 hE₁E₂ E₁.root_mem hzE₂
      path₂_disjoint_end₁ := by
        rw [Finset.disjoint_left]
        intro z hz hzE₁
        have hzv : z = v₂ := by simpa using hz
        subst z
        exact Finset.disjoint_left.1 hE₁E₂ hzE₁ E₂.root_mem
      end₁_avoids := hE₁X
      end₂_avoids := hE₂X
      ends_disjoint := hE₁E₂ }
  have hState₀ : StateAt 0 := ⟨S₀, by simp [S₀, PairedLongConnectorState.total]⟩
  let n := Nat.findGreatest StateAt ell
  have hnState : StateAt n :=
    Nat.findGreatest_spec (P := StateAt) (Nat.zero_le _) hState₀
  have hnle : n ≤ ell := Nat.findGreatest_le ell
  obtain ⟨S, hSlen⟩ := hnState
  have hStotal : S.total ≤ ell := by simpa [hSlen] using hnle
  have hcard₁ : S.path₁.support.toFinset.card = S.path₁.length + 1 := by
    rw [List.toFinset_card_of_nodup S.path₁_isPath.support_nodup,
      S.path₁.length_support]
  have hcard₂ : S.path₂.support.toFinset.card = S.path₂.length + 1 := by
    rw [List.toFinset_card_of_nodup S.path₂_isPath.support_nodup,
      S.path₂.length_support]
  have hfreshBudget :
      (X ∪ S.path₁.support.toFinset ∪ S.path₂.support.toFinset ∪
        S.end₁.verts ∪ S.end₂.verts).card ≤ freshWorkspace := by
    have h₀ := Finset.card_union_le X S.path₁.support.toFinset
    have h₁ := Finset.card_union_le (X ∪ S.path₁.support.toFinset)
      S.path₂.support.toFinset
    have h₂ := Finset.card_union_le
      (X ∪ S.path₁.support.toFinset ∪ S.path₂.support.toFinset) S.end₁.verts
    have h₃ := Finset.card_union_le
      (X ∪ S.path₁.support.toFinset ∪ S.path₂.support.toFinset ∪
        S.end₁.verts) S.end₂.verts
    simp only [hcard₁, hcard₂, S.end₁.card_verts, S.end₂.card_verts,
      PairedLongConnectorState.total] at h₀ h₁ h₂ h₃ hStotal
    omega
  have hpathBudget :
      (X ∪ S.path₁.support.toFinset ∪ S.path₂.support.toFinset).card ≤
        pathWorkspace := by
    have h₀ := Finset.card_union_le X S.path₁.support.toFinset
    have h₁ := Finset.card_union_le (X ∪ S.path₁.support.toFinset)
      S.path₂.support.toFinset
    simp only [hcard₁, hcard₂, PairedLongConnectorState.total] at h₀ h₁ hStotal
    omega
  have hexState : ∃ T : PairedLongConnectorState G X v₁ v₂ L m,
      ell ≤ T.total ∧ T.total ≤ ell + 4 * m := by
    by_cases hell : ell ≤ S.total
    · exact ⟨S, hell, by omega⟩
    · obtain ⟨T, hST, hTupper⟩ :=
        S.extend hexp N hdegree hfreshBudget hpathBudget
      by_cases hTell : T.total ≤ ell
      · have hStateT : StateAt T.total := ⟨T, rfl⟩
        have hmax := Nat.le_findGreatest (P := StateAt) hTell hStateT
        omega
      · exact ⟨T, Nat.le_of_not_ge hTell, by omega⟩
  obtain ⟨T, hTell, hTupper⟩ := hexState
  let barrier := X ∪ (T.path₁.support.toFinset.erase T.finish₁) ∪
    (T.path₂.support.toFinset.erase T.finish₂)
  have hE₁Barrier : Disjoint T.end₁.verts barrier := by
    rw [Finset.disjoint_left]
    intro z hzE hz
    simp only [barrier, Finset.mem_union] at hz
    rcases hz with (hzX | hzP₁) | hzP₂
    · exact Finset.disjoint_left.1 T.end₁_avoids hzE hzX
    · exact (Finset.mem_erase.1 hzP₁).1 <|
        T.path₁_meets_end₁ z
          (List.mem_toFinset.1 (Finset.mem_erase.1 hzP₁).2) hzE
    · exact Finset.disjoint_left.1 T.path₂_disjoint_end₁
        (Finset.mem_erase.1 hzP₂).2 hzE
  have hE₂Barrier : Disjoint T.end₂.verts barrier := by
    rw [Finset.disjoint_left]
    intro z hzE hz
    simp only [barrier, Finset.mem_union] at hz
    rcases hz with (hzX | hzP₁) | hzP₂
    · exact Finset.disjoint_left.1 T.end₂_avoids hzE hzX
    · exact Finset.disjoint_left.1 T.path₁_disjoint_end₂
        (Finset.mem_erase.1 hzP₁).2 hzE
    · exact (Finset.mem_erase.1 hzP₂).1 <|
        T.path₂_meets_end₂ z
          (List.mem_toFinset.1 (Finset.mem_erase.1 hzP₂).2) hzE
  have hTcard₁ : T.path₁.support.toFinset.card = T.path₁.length + 1 := by
    rw [List.toFinset_card_of_nodup T.path₁_isPath.support_nodup,
      T.path₁.length_support]
  have hTcard₂ : T.path₂.support.toFinset.card = T.path₂.length + 1 := by
    rw [List.toFinset_card_of_nodup T.path₂_isPath.support_nodup,
      T.path₂.length_support]
  have hbarrier : barrier.card ≤ pathWorkspace := by
    have h₀ := Finset.card_union_le X T.path₁.support.toFinset
    have h₁ := Finset.card_union_le (X ∪ T.path₁.support.toFinset)
      T.path₂.support.toFinset
    have hsub : barrier ⊆
        X ∪ T.path₁.support.toFinset ∪ T.path₂.support.toFinset := by
      intro z hz
      simp only [barrier, Finset.mem_union] at hz
      rcases hz with (hzX | hzP₁) | hzP₂
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ hzX)
      · exact Finset.mem_union_left _ <| Finset.mem_union_right _ <|
          (Finset.mem_erase.1 hzP₁).2
      · exact Finset.mem_union_right _ (Finset.mem_erase.1 hzP₂).2
    apply (Finset.card_le_card hsub).trans
    simp only [hTcard₁, hTcard₂, PairedLongConnectorState.total] at h₀ h₁ hTupper
    omega
  obtain ⟨q, hq, hqBarrier, hqlen⟩ :=
    exists_short_root_connector G epsilon kappa hexp N.degreeScale hdegree
      T.end₁ T.end₂ barrier hE₁Barrier hE₂Barrier hbarrier
      N.pathStart N.path_seed N.growth_path
  have hqlen₇ : q.length ≤ 7 * m := by
    calc
      q.length ≤ 6 * m + 2 * (pathRadius + 1) := hqlen
      _ ≤ 6 * m + m := Nat.add_le_add_left N.connector_radius (6 * m)
      _ = 7 * m := by omega
  have hinter₁ : ∀ z, z ∈ T.path₁.support → z ∈ q.support →
      z = T.finish₁ := by
    intro z hzP hzq
    by_cases hzf : z = T.finish₁
    · exact hzf
    · exact (hqBarrier z hzq (by simp [barrier, hzP, hzf])).elim
  let left : G.Walk v₁ T.finish₂ := T.path₁.append q
  have hleft : left.IsPath :=
    Walk.IsPath.append_of_inter_eq_end T.path₁_isPath hq hinter₁
  have hinter₂ : ∀ z, z ∈ left.support → z ∈ T.path₂.reverse.support →
      z = T.finish₂ := by
    intro z hzleft hzP₂
    have hzP₂' : z ∈ T.path₂.support := by simpa using hzP₂
    change z ∈ (T.path₁.append q).support at hzleft
    rw [Walk.mem_support_append_iff] at hzleft
    rcases hzleft with hzP₁ | hzq
    · exact (Finset.disjoint_left.1 T.paths_disjoint
        (by simpa using hzP₁) (by simpa using hzP₂')).elim
    · by_cases hzf : z = T.finish₂
      · exact hzf
      · exact (hqBarrier z hzq (by simp [barrier, hzP₂', hzf])).elim
  let p : G.Walk v₁ v₂ := left.append T.path₂.reverse
  refine ⟨p, Walk.IsPath.append_of_inter_eq_end hleft T.path₂_isPath.reverse hinter₂,
    ?_, ?_, ?_⟩
  · intro z hz hzX
    change z ∈ (left.append T.path₂.reverse).support at hz
    rw [Walk.mem_support_append_iff] at hz
    rcases hz with hzleft | hzP₂
    · change z ∈ (T.path₁.append q).support at hzleft
      rw [Walk.mem_support_append_iff] at hzleft
      rcases hzleft with hzP₁ | hzq
      · exact T.path₁_avoids z hzP₁ hzX
      · exact hqBarrier z hzq (by simp [barrier, hzX])
    · exact T.path₂_avoids z (by simpa using hzP₂) hzX
  · calc
      ell ≤ T.total := hTell
      _ ≤ p.length := by
        simp only [p, left, Walk.length_append, Walk.length_reverse,
          PairedLongConnectorState.total]
        omega
  · calc
      p.length = T.total + q.length := by
        simp only [p, left, Walk.length_append, Walk.length_reverse,
          PairedLongConnectorState.total]
        omega
      _ ≤ (ell + 4 * m) + 7 * m := Nat.add_le_add hTupper hqlen₇
      _ = ell + 11 * m := by omega

/-! ## The two-connector corollary -/

/-- Attach the roots of two expansions to a clean segment between them. -/
private theorem exists_root_path_through_segment
    {x y a b : V} {L m r : ℕ}
    (E : VertexExpansion G x L (3 * m))
    (F : VertexExpansion G y L (3 * m))
    (q : G.Walk a b) (hq : q.IsPath) (hqlen : q.length ≤ r)
    (ha : a ∈ E.verts) (hb : b ∈ F.verts)
    (hEF : Disjoint E.verts F.verts)
    (hqE : ∀ z ∈ q.support, z ∈ E.verts → z = a)
    (hqF : ∀ z ∈ q.support, z ∈ F.verts → z = b) :
    ∃ p : G.Walk x y, p.IsPath ∧ p.length ≤ 6 * m + r ∧
      p.support.toFinset ⊆ E.verts ∪ q.support.toFinset ∪ F.verts := by
  classical
  obtain ⟨px, hpx, hpxlen, hpxsupp⟩ := E.exists_path ha
  obtain ⟨py, hpy, hpylen, hpysupp⟩ := F.exists_path hb
  have hpxq : ∀ z, z ∈ px.support → z ∈ q.support → z = a := by
    intro z hzpx hzq
    exact hqE z hzq (hpxsupp z hzpx)
  let left : G.Walk x b := px.append q
  have hleft : left.IsPath :=
    Walk.IsPath.append_of_inter_eq_end hpx hq hpxq
  have hleftpy : ∀ z, z ∈ left.support → z ∈ py.reverse.support → z = b := by
    intro z hzleft hzpy
    have hzpy' : z ∈ py.support := by simpa using hzpy
    change z ∈ (px.append q).support at hzleft
    rw [Walk.mem_support_append_iff] at hzleft
    rcases hzleft with hzpx | hzq
    · exact (Finset.disjoint_left.1 hEF (hpxsupp z hzpx) (hpysupp z hzpy')).elim
    · exact hqF z hzq (hpysupp z hzpy')
  let p : G.Walk x y := left.append py.reverse
  refine ⟨p, Walk.IsPath.append_of_inter_eq_end hleft hpy.reverse hleftpy, ?_, ?_⟩
  · simp only [p, left, Walk.length_append, Walk.length_reverse]
    omega
  · intro z hz
    have hz' : z ∈ p.support := by simpa using hz
    change z ∈ (left.append py.reverse).support at hz'
    rw [Walk.mem_support_append_iff] at hz'
    rcases hz' with hzleft | hzpy
    · change z ∈ (px.append q).support at hzleft
      rw [Walk.mem_support_append_iff] at hzleft
      rcases hzleft with hzpx | hzq
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (hpxsupp z hzpx))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (by simpa using hzq))
    · exact Finset.mem_union_right _ (hpysupp z (by simpa using hzpy))

/-- The short first connector, with the two unused expansions recorded. -/
private def ShortCrossConclusion (G : SimpleGraph V) (A : Finset V)
    (v₁ v₂ v₃ v₄ : V) (F₁ F₂ F₃ F₄ : Finset V) (m : ℕ) : Prop :=
  (∃ p : G.Walk v₁ v₃, p.IsPath ∧ (∀ z ∈ p.support, z ∉ A) ∧
      p.length ≤ 7 * m ∧ Disjoint p.support.toFinset F₂ ∧
      Disjoint p.support.toFinset F₄) ∨
  (∃ p : G.Walk v₁ v₄, p.IsPath ∧ (∀ z ∈ p.support, z ∉ A) ∧
      p.length ≤ 7 * m ∧ Disjoint p.support.toFinset F₂ ∧
      Disjoint p.support.toFinset F₃) ∨
  (∃ p : G.Walk v₂ v₃, p.IsPath ∧ (∀ z ∈ p.support, z ∉ A) ∧
      p.length ≤ 7 * m ∧ Disjoint p.support.toFinset F₁ ∧
      Disjoint p.support.toFinset F₄) ∨
  (∃ p : G.Walk v₂ v₄, p.IsPath ∧ (∀ z ∈ p.support, z ∉ A) ∧
      p.length ≤ 7 * m ∧ Disjoint p.support.toFinset F₁ ∧
      Disjoint p.support.toFinset F₃)

private theorem exists_short_cross [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (epsilon kappa : ℝ)
    (hexp : IsLMExpander G epsilon kappa)
    (degreeScale : ℕ) (hdegree : ∀ v : V, degreeScale ≤ G.degree v)
    {v₁ v₂ v₃ v₄ : V} {L m radius pathWorkspace : ℕ}
    (A : Finset V)
    (E₁ : VertexExpansion G v₁ L (3 * m))
    (E₂ : VertexExpansion G v₂ L (3 * m))
    (E₃ : VertexExpansion G v₃ L (3 * m))
    (E₄ : VertexExpansion G v₄ L (3 * m))
    (hA₁ : Disjoint E₁.verts A) (hA₂ : Disjoint E₂.verts A)
    (hA₃ : Disjoint E₃.verts A) (hA₄ : Disjoint E₄.verts A)
    (h₁₂ : Disjoint E₁.verts E₂.verts)
    (h₁₃ : Disjoint E₁.verts E₃.verts)
    (h₁₄ : Disjoint E₁.verts E₄.verts)
    (h₂₃ : Disjoint E₂.verts E₃.verts)
    (h₂₄ : Disjoint E₂.verts E₄.verts)
    (h₃₄ : Disjoint E₃.verts E₄.verts)
    (hAcard : A.card ≤ pathWorkspace)
    (start : ℕ) (hseed : start ≤ L ∨ start + pathWorkspace ≤ degreeScale)
    (growth : BallGrowthSchedule G epsilon kappa start pathWorkspace radius)
    (hradius : 2 * (radius + 1) ≤ m) :
    ShortCrossConclusion G A v₁ v₂ v₃ v₄
      E₁.verts E₂.verts E₃.verts E₄.verts m := by
  let originalDecAdj : DecidableRel G.Adj := inferInstance
  classical
  letI : DecidableRel G.Adj := originalDecAdj
  let left := E₁.verts ∪ E₂.verts
  let right := E₃.verts ∪ E₄.verts
  have hleftA : Disjoint left A :=
    Finset.disjoint_union_left.2 ⟨hA₁, hA₂⟩
  have hrightA : Disjoint right A :=
    Finset.disjoint_union_left.2 ⟨hA₃, hA₄⟩
  have hleftCard : L ≤ left.card := by
    rw [← E₁.card_verts]
    exact Finset.card_le_card Finset.subset_union_left
  have hrightCard : L ≤ right.card := by
    rw [← E₃.card_verts]
    exact Finset.card_le_card Finset.subset_union_left
  obtain ⟨a₀, ha₀, b₀, hb₀, raw, hraw, hrawlen⟩ :=
    exists_short_set_connector G epsilon kappa hexp degreeScale hdegree
      A left right start pathWorkspace radius hAcard hleftA hrightA
      ⟨v₁, Finset.mem_union_left _ E₁.root_mem⟩
      ⟨v₃, Finset.mem_union_left _ E₃.root_mem⟩
      (hseed.imp (fun h ↦ h.trans hleftCard) id)
      (hseed.imp (fun h ↦ h.trans hrightCard) id) growth
  have hrawEmpty : raw.Avoids (A : Set V) (∅ : Set V) := by
    apply Walk.avoids_empty_of_endpoints_outside hraw.2
    · exact fun haA ↦ Finset.disjoint_left.1 hleftA ha₀ haA
    · exact fun hbA ↦ Finset.disjoint_left.1 hrightA hb₀ hbA
  obtain ⟨a, ha, b, hb, q, hq, hqlen, hqsub, hqLeft, hqRight⟩ :=
    exists_minimal_subpath raw hraw.1 left right ha₀ hb₀
  have hqlenM : q.length ≤ m := by omega
  have hqA : q.Avoids (A : Set V) (∅ : Set V) := by
    intro z hz hzA
    exact hrawEmpty z (hqsub hz) hzA
  have package {x y : V} (E : VertexExpansion G x L (3 * m))
      (F : VertexExpansion G y L (3 * m))
      (haE : a ∈ E.verts) (hbF : b ∈ F.verts)
      (hEF : Disjoint E.verts F.verts)
      (hELeft : E.verts ⊆ left) (hFRight : F.verts ⊆ right) :
      ∃ p : G.Walk x y, p.IsPath ∧ (∀ z ∈ p.support, z ∉ A) ∧
        p.length ≤ 7 * m ∧
        p.support.toFinset ⊆ E.verts ∪ q.support.toFinset ∪ F.verts := by
    have hqE : ∀ z ∈ q.support, z ∈ E.verts → z = a := by
      intro z hz hzE
      exact hqLeft z hz (hELeft hzE)
    have hqF : ∀ z ∈ q.support, z ∈ F.verts → z = b := by
      intro z hz hzF
      exact hqRight z hz (hFRight hzF)
    obtain ⟨p, hp, hplen, hpsub⟩ :=
      exists_root_path_through_segment E F q hq hqlenM haE hbF hEF hqE hqF
    refine ⟨p, hp, ?_, by omega, hpsub⟩
    intro z hz hzA
    have hzset := hpsub (by simpa using hz)
    simp only [Finset.mem_union] at hzset
    rcases hzset with (hzE | hzq) | hzF
    · exact Finset.disjoint_left.1
        (hleftA.mono_left hELeft) hzE hzA
    · exact hqA z (by simpa using hzq) hzA
    · exact Finset.disjoint_left.1
        (hrightA.mono_left hFRight) hzF hzA
  rcases Finset.mem_union.1 ha with ha₁ | ha₂ <;>
    rcases Finset.mem_union.1 hb with hb₃ | hb₄
  · obtain ⟨p, hp, hpA, hplen, hpsub⟩ := package E₁ E₃ ha₁ hb₃ h₁₃
      Finset.subset_union_left Finset.subset_union_left
    refine Or.inl ⟨p, hp, hpA, hplen, ?_, ?_⟩
    · rw [Finset.disjoint_left]
      intro z hz hzE₂
      have hzset := hpsub hz
      simp only [Finset.mem_union] at hzset
      rcases hzset with (hzE₁ | hzq) | hzE₃
      · exact Finset.disjoint_left.1 h₁₂ hzE₁ hzE₂
      · have hza := hqLeft z (by simpa using hzq)
            (Finset.mem_union_right _ hzE₂)
        subst z
        exact Finset.disjoint_left.1 h₁₂ ha₁ hzE₂
      · exact Finset.disjoint_left.1 h₂₃ hzE₂ hzE₃
    · rw [Finset.disjoint_left]
      intro z hz hzE₄
      have hzset := hpsub hz
      simp only [Finset.mem_union] at hzset
      rcases hzset with (hzE₁ | hzq) | hzE₃
      · exact Finset.disjoint_left.1 h₁₄ hzE₁ hzE₄
      · have hzb := hqRight z (by simpa using hzq)
            (Finset.mem_union_right _ hzE₄)
        subst z
        exact Finset.disjoint_left.1 h₃₄ hb₃ hzE₄
      · exact Finset.disjoint_left.1 h₃₄ hzE₃ hzE₄

  · obtain ⟨p, hp, hpA, hplen, hpsub⟩ := package E₁ E₄ ha₁ hb₄ h₁₄
      Finset.subset_union_left Finset.subset_union_right
    refine Or.inr <| Or.inl ⟨p, hp, hpA, hplen, ?_, ?_⟩
    · rw [Finset.disjoint_left]
      intro z hz hzE₂
      have hzset := hpsub hz
      simp only [Finset.mem_union] at hzset
      rcases hzset with (hzE₁ | hzq) | hzE₄
      · exact Finset.disjoint_left.1 h₁₂ hzE₁ hzE₂
      · have hza := hqLeft z (by simpa using hzq)
            (Finset.mem_union_right _ hzE₂)
        subst z
        exact Finset.disjoint_left.1 h₁₂ ha₁ hzE₂
      · exact Finset.disjoint_left.1 h₂₄ hzE₂ hzE₄
    · rw [Finset.disjoint_left]
      intro z hz hzE₃
      have hzset := hpsub hz
      simp only [Finset.mem_union] at hzset
      rcases hzset with (hzE₁ | hzq) | hzE₄
      · exact Finset.disjoint_left.1 h₁₃ hzE₁ hzE₃
      · have hzb := hqRight z (by simpa using hzq)
            (Finset.mem_union_left _ hzE₃)
        subst z
        exact Finset.disjoint_left.1 h₃₄ hzE₃ hb₄
      · exact Finset.disjoint_left.1 h₃₄ hzE₃ hzE₄
  · obtain ⟨p, hp, hpA, hplen, hpsub⟩ := package E₂ E₃ ha₂ hb₃ h₂₃
      Finset.subset_union_right Finset.subset_union_left
    refine Or.inr <| Or.inr <| Or.inl ⟨p, hp, hpA, hplen, ?_, ?_⟩
    · rw [Finset.disjoint_left]
      intro z hz hzE₁
      have hzset := hpsub hz
      simp only [Finset.mem_union] at hzset
      rcases hzset with (hzE₂ | hzq) | hzE₃
      · exact Finset.disjoint_left.1 h₁₂ hzE₁ hzE₂
      · have hza := hqLeft z (by simpa using hzq)
            (Finset.mem_union_left _ hzE₁)
        subst z
        exact Finset.disjoint_left.1 h₁₂ hzE₁ ha₂
      · exact Finset.disjoint_left.1 h₁₃ hzE₁ hzE₃
    · rw [Finset.disjoint_left]
      intro z hz hzE₄
      have hzset := hpsub hz
      simp only [Finset.mem_union] at hzset
      rcases hzset with (hzE₂ | hzq) | hzE₃
      · exact Finset.disjoint_left.1 h₂₄ hzE₂ hzE₄
      · have hzb := hqRight z (by simpa using hzq)
            (Finset.mem_union_right _ hzE₄)
        subst z
        exact Finset.disjoint_left.1 h₃₄ hb₃ hzE₄
      · exact Finset.disjoint_left.1 h₃₄ hzE₃ hzE₄
  · obtain ⟨p, hp, hpA, hplen, hpsub⟩ := package E₂ E₄ ha₂ hb₄ h₂₄
      Finset.subset_union_right Finset.subset_union_right
    refine Or.inr <| Or.inr <| Or.inr ⟨p, hp, hpA, hplen, ?_, ?_⟩
    · rw [Finset.disjoint_left]
      intro z hz hzE₁
      have hzset := hpsub hz
      simp only [Finset.mem_union] at hzset
      rcases hzset with (hzE₂ | hzq) | hzE₄
      · exact Finset.disjoint_left.1 h₁₂ hzE₁ hzE₂
      · have hza := hqLeft z (by simpa using hzq)
            (Finset.mem_union_left _ hzE₁)
        subst z
        exact Finset.disjoint_left.1 h₁₂ hzE₁ ha₂
      · exact Finset.disjoint_left.1 h₁₄ hzE₁ hzE₄
    · rw [Finset.disjoint_left]
      intro z hz hzE₃
      have hzset := hpsub hz
      simp only [Finset.mem_union] at hzset
      rcases hzset with (hzE₂ | hzq) | hzE₄
      · exact Finset.disjoint_left.1 h₂₃ hzE₂ hzE₃
      · have hzb := hqRight z (by simpa using hzq)
            (Finset.mem_union_left _ hzE₃)
        subst z
        exact Finset.disjoint_left.1 h₃₄ hzE₃ hb₄
      · exact Finset.disjoint_left.1 h₃₄ hzE₃ hzE₄

/-- Complete a short connector by a long connector between the two unused
expansions. -/
private theorem exists_long_complement [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (epsilon kappa : ℝ)
    (hexp : IsLMExpander G epsilon kappa)
    {x y u v : V}
    {D K L m freshRadius pathRadius rounds freshWorkspace pathWorkspace ell : ℕ}
    (N : LM315Numerics G epsilon kappa D K L m freshRadius pathRadius rounds
      freshWorkspace pathWorkspace)
    (hdegree : ∀ z : V, N.degreeScale ≤ G.degree z)
    (A : Finset V) (p : G.Walk x y)
    (hp : p.IsPath) (hpA : ∀ z ∈ p.support, z ∉ A)
    (hplen : p.length ≤ 7 * m)
    (E : VertexExpansion G u L (3 * m))
    (F : VertexExpansion G v L (3 * m))
    (hEA : Disjoint E.verts A) (hFA : Disjoint F.verts A)
    (hEF : Disjoint E.verts F.verts)
    (hpE : Disjoint p.support.toFinset E.verts)
    (hpF : Disjoint p.support.toFinset F.verts)
    (hfresh : A.card + ell + 14 * m + 2 * L + 3 ≤ freshWorkspace)
    (hpath : A.card + ell + 14 * m + 3 ≤ pathWorkspace) :
    ∃ q : G.Walk u v, q.IsPath ∧ p.support.Disjoint q.support ∧
      (∀ z ∈ q.support, z ∉ A) ∧
      ell ≤ p.length + q.length ∧
      p.length + q.length ≤ ell + 22 * m := by
  let originalDecAdj : DecidableRel G.Adj := inferInstance
  classical
  letI : DecidableRel G.Adj := originalDecAdj
  let X := A ∪ p.support.toFinset
  let target := ell + 7 * m - p.length
  have hEX : Disjoint E.verts X := by
    exact Finset.disjoint_union_right.2 ⟨hEA, hpE.symm⟩
  have hFX : Disjoint F.verts X := by
    exact Finset.disjoint_union_right.2 ⟨hFA, hpF.symm⟩
  have hpCard : p.support.toFinset.card = p.length + 1 := by
    rw [List.toFinset_card_of_nodup hp.support_nodup, p.length_support]
  have hXcard : X.card ≤ A.card + p.length + 1 := by
    have := Finset.card_union_le A p.support.toFinset
    simpa [X, hpCard, Nat.add_assoc] using this
  have htarget : p.length + target = ell + 7 * m := by
    dsimp [target]
    omega
  have hfresh' : X.card + target + 2 * L + 2 ≤ freshWorkspace := by
    omega
  have hpath' : X.card + target + 4 * m + 2 ≤ pathWorkspace := by
    omega
  obtain ⟨q, hq, hqX, hqlower, hqupper⟩ :=
    liuMontgomery_lemma3_14_finite G epsilon kappa hexp N hdegree X E F
      hEX hFX hEF hfresh' hpath'
  refine ⟨q, hq, ?_, ?_, ?_, ?_⟩
  · rw [List.disjoint_left]
    intro z hzp hzq
    exact hqX z hzq (by simp [X, hzp])
  · intro z hz hzA
    exact hqX z hz (by simp [X, hzA])
  · omega
  · omega

/-- Concrete Liu--Montgomery Corollary 3.15. -/
theorem liuMontgomery_corollary3_15_finite [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (epsilon kappa : ℝ)
    (hexp : IsLMExpander G epsilon kappa)
    {v₁ v₂ v₃ v₄ : V}
    {D K L m freshRadius pathRadius rounds freshWorkspace pathWorkspace ell : ℕ}
    (N : LM315Numerics G epsilon kappa D K L m freshRadius pathRadius rounds
      freshWorkspace pathWorkspace)
    (hdegree : ∀ z : V, N.degreeScale ≤ G.degree z)
    (A : Finset V)
    (E₁ : VertexExpansion G v₁ D m)
    (E₂ : VertexExpansion G v₂ D m)
    (E₃ : VertexExpansion G v₃ D m)
    (E₄ : VertexExpansion G v₄ D m)
    (hA₁ : Disjoint E₁.verts A) (hA₂ : Disjoint E₂.verts A)
    (hA₃ : Disjoint E₃.verts A) (hA₄ : Disjoint E₄.verts A)
    (h₁₂ : Disjoint E₁.verts E₂.verts)
    (h₁₃ : Disjoint E₁.verts E₃.verts)
    (h₁₄ : Disjoint E₁.verts E₄.verts)
    (h₂₃ : Disjoint E₂.verts E₃.verts)
    (h₂₄ : Disjoint E₂.verts E₄.verts)
    (h₃₄ : Disjoint E₃.verts E₄.verts)
    (h₁₃fresh : A.card + 4 * D + (32 * m) * L ≤ freshWorkspace)
    (h₁₃path : A.card + (8 * m) * (7 * m + 4) ≤ N.routeWorkspace)
    (hcorFresh : A.card + ell + 14 * m + 2 * L + 3 ≤ freshWorkspace)
    (hcorPath : A.card + ell + 14 * m + 3 ≤ pathWorkspace) :
    LM315Conclusion G A v₁ v₂ v₃ v₄ ell m := by
  let originalDecAdj : DecidableRel G.Adj := inferInstance
  classical
  letI : DecidableRel G.Adj := originalDecAdj
  obtain ⟨F₁, F₂, F₃, F₄, hF₁A, hF₂A, hF₃A, hF₄A,
      hF₁₂, hF₁₃, hF₁₄, hF₂₃, hF₂₄, hF₃₄⟩ :=
    liuMontgomery_lemma3_13_finite G epsilon kappa hexp N hdegree A E₁ E₂ E₃ E₄
      hA₁ hA₂ hA₃ hA₄ h₁₂ h₁₃ h₁₄ h₂₃ h₂₄ h₃₄ h₁₃fresh h₁₃path
  have hAcard : A.card ≤ pathWorkspace := by omega
  have hcross := exists_short_cross G epsilon kappa hexp N.degreeScale hdegree
    A F₁ F₂ F₃ F₄
    hF₁A hF₂A hF₃A hF₄A hF₁₂ hF₁₃ hF₁₄ hF₂₃ hF₂₄ hF₃₄
    hAcard N.pathStart N.path_seed N.growth_path N.connector_radius
  rcases hcross with h₁₃ | h₁₄ | h₂₃ | h₂₄
  · obtain ⟨p, hp, hpA, hplen, hpF₂, hpF₄⟩ := h₁₃
    obtain ⟨q, hq, hpq, hqA, hlower, hupper⟩ :=
      exists_long_complement G epsilon kappa hexp N hdegree A p hp hpA hplen F₂ F₄
        hF₂A hF₄A hF₂₄ hpF₂ hpF₄ hcorFresh hcorPath
    refine Or.inl ⟨{
      left := p
      right := q
      left_isPath := hp
      right_isPath := hq
      disjoint := hpq
      left_avoids := hpA
      right_avoids := hqA
      lower_length := hlower
      upper_length := hupper }⟩
  · obtain ⟨p, hp, hpA, hplen, hpF₂, hpF₃⟩ := h₁₄
    obtain ⟨q, hq, hpq, hqA, hlower, hupper⟩ :=
      exists_long_complement G epsilon kappa hexp N hdegree A p hp hpA hplen F₂ F₃
        hF₂A hF₃A hF₂₃ hpF₂ hpF₃ hcorFresh hcorPath
    refine Or.inr ⟨{
      left := p
      right := q
      left_isPath := hp
      right_isPath := hq
      disjoint := hpq
      left_avoids := hpA
      right_avoids := hqA
      lower_length := hlower
      upper_length := hupper }⟩
  · obtain ⟨p, hp, hpA, hplen, hpF₁, hpF₄⟩ := h₂₃
    obtain ⟨q, hq, hpq, hqA, hlower, hupper⟩ :=
      exists_long_complement G epsilon kappa hexp N hdegree A p hp hpA hplen F₁ F₄
        hF₁A hF₄A hF₁₄ hpF₁ hpF₄ hcorFresh hcorPath
    refine Or.inr ⟨{
      left := q
      right := p
      left_isPath := hq
      right_isPath := hp
      disjoint := hpq.symm
      left_avoids := hqA
      right_avoids := hpA
      lower_length := by simpa [Nat.add_comm] using hlower
      upper_length := by simpa [Nat.add_comm] using hupper }⟩
  · obtain ⟨p, hp, hpA, hplen, hpF₁, hpF₃⟩ := h₂₄
    obtain ⟨q, hq, hpq, hqA, hlower, hupper⟩ :=
      exists_long_complement G epsilon kappa hexp N hdegree A p hp hpA hplen F₁ F₃
        hF₁A hF₃A hF₁₃ hpF₁ hpF₃ hcorFresh hcorPath
    refine Or.inl ⟨{
      left := q
      right := p
      left_isPath := hq
      right_isPath := hp
      disjoint := hpq.symm
      left_avoids := hqA
      right_avoids := hpA
      lower_length := by simpa [Nat.add_comm] using hlower
      upper_length := by simpa [Nat.add_comm] using hupper }⟩
/-
  · obtain ⟨p, hp, hpA, hplen, hpsub⟩ := package E₁ E₄ ha₁ hb₄ h₁₄
      Finset.subset_union_left Finset.subset_union_right
    refine Or.inr <| Or.inl ⟨p, hp, hpA, hplen, ?_, ?_⟩
    · rw [Finset.disjoint_left]
      intro z hz hzE₂
      have hzset := hpsub hz
      simp only [Finset.mem_union] at hzset
      rcases hzset with (hzE₁ | hzq) | hzE₄
      · exact Finset.disjoint_left.1 h₁₂ hzE₁ hzE₂
      · have hza := hqLeft z (by simpa using hzq)
            (Finset.mem_union_right _ hzE₂)
        subst z
        exact Finset.disjoint_left.1 h₁₂ ha₁ hzE₂
      · exact Finset.disjoint_left.1 h₂₄ hzE₂ hzE₄
    · rw [Finset.disjoint_left]
      intro z hz hzE₃
      have hzset := hpsub hz
      simp only [Finset.mem_union] at hzset
      rcases hzset with (hzE₁ | hzq) | hzE₄
      · exact Finset.disjoint_left.1 h₁₃ hzE₁ hzE₃
      · have hzb := hqRight z (by simpa using hzq)
            (Finset.mem_union_left _ hzE₃)
        subst z
        exact Finset.disjoint_left.1 h₃₄ hzE₃ hb₄
      · exact Finset.disjoint_left.1 h₃₄ hzE₃ hzE₄
  · obtain ⟨p, hp, hpA, hplen, hpsub⟩ := package E₂ E₃ ha₂ hb₃ h₂₃
      Finset.subset_union_right Finset.subset_union_left
    refine Or.inr <| Or.inr <| Or.inl ⟨p, hp, hpA, hplen, ?_, ?_⟩
    · rw [Finset.disjoint_left]
      intro z hz hzE₁
      have hzset := hpsub hz
      simp only [Finset.mem_union] at hzset
      rcases hzset with (hzE₂ | hzq) | hzE₃
      · exact Finset.disjoint_left.1 h₁₂ hzE₁ hzE₂
      · have hza := hqLeft z (by simpa using hzq)
            (Finset.mem_union_left _ hzE₁)
        subst z
        exact Finset.disjoint_left.1 h₁₂ hzE₁ ha₂
      · exact Finset.disjoint_left.1 h₁₃ hzE₁ hzE₃
    · rw [Finset.disjoint_left]
      intro z hz hzE₄
      have hzset := hpsub hz
      simp only [Finset.mem_union] at hzset
      rcases hzset with (hzE₂ | hzq) | hzE₃
      · exact Finset.disjoint_left.1 h₂₄ hzE₂ hzE₄
      · have hzb := hqRight z (by simpa using hzq)
            (Finset.mem_union_right _ hzE₄)
        subst z
        exact Finset.disjoint_left.1 h₃₄ hb₃ hzE₄
      · exact Finset.disjoint_left.1 h₃₄ hzE₃ hzE₄
  · obtain ⟨p, hp, hpA, hplen, hpsub⟩ := package E₂ E₄ ha₂ hb₄ h₂₄
      Finset.subset_union_right Finset.subset_union_right
    refine Or.inr <| Or.inr <| Or.inr ⟨p, hp, hpA, hplen, ?_, ?_⟩
    · rw [Finset.disjoint_left]
      intro z hz hzE₁
      have hzset := hpsub hz
      simp only [Finset.mem_union] at hzset
      rcases hzset with (hzE₂ | hzq) | hzE₄
      · exact Finset.disjoint_left.1 h₁₂ hzE₁ hzE₂
      · have hza := hqLeft z (by simpa using hzq)
            (Finset.mem_union_left _ hzE₁)
        subst z
        exact Finset.disjoint_left.1 h₁₂ hzE₁ ha₂
      · exact Finset.disjoint_left.1 h₁₄ hzE₁ hzE₄
    · rw [Finset.disjoint_left]
      intro z hz hzE₃
      have hzset := hpsub hz
      simp only [Finset.mem_union] at hzset
      rcases hzset with (hzE₂ | hzq) | hzE₄
      · exact Finset.disjoint_left.1 h₂₃ hzE₂ hzE₃
      · have hzb := hqRight z (by simpa using hzq)
            (Finset.mem_union_left _ hzE₃)
        subst z
        exact Finset.disjoint_left.1 h₃₄ hzE₃ hb₄
      · exact Finset.disjoint_left.1 h₃₄ hzE₃ hzE₄
  · simp only [p, left, Walk.length_append, Walk.length_reverse,
      PairedLongConnectorState.total]
    omega
-/

end Erdos63
