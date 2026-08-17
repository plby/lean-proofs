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

import ErdosProblems.Erdos182.KeyRestrictionCore

/-!
# The active-set form of the Janzer--Sudakov restriction lemma

This file transports the relation-form restriction lemma to specified active
left and right vertex sets.  The support hypothesis ensures that restricting
the ambient relation to the two subtype vertex sets loses no incidences.
-/

open Finset Fintype
open scoped BigOperators

namespace Erdos182

section ActiveRestriction

variable {A B : Type*} [Fintype A] [Fintype B]

private abbrev activeRelation (R : A → B → Prop)
    (A₀ : Finset A) (B₀ : Finset B) : (↑A₀) → (↑B₀) → Prop :=
  fun u v ↦ R u.1 v.1

private def activeEmbedding (S : Finset A) : (↑S) ↪ A :=
  ⟨Subtype.val, Subtype.val_injective⟩

@[simp] private theorem activeEmbedding_apply (S : Finset A) (u : ↑S) :
    activeEmbedding S u = u.1 := rfl

private theorem active_degreeA_eq
    (R : A → B → Prop) [DecidableRel R]
    (A₀ : Finset A) (B₀ : Finset B)
    (hsupport : ∀ u v, R u v → u ∈ A₀ ∧ v ∈ B₀) (u : ↑A₀) :
    bipDegreeA (activeRelation R A₀ B₀) u = bipDegreeA R u.1 := by
  classical
  let eB : (↑B₀) ↪ B := activeEmbedding B₀
  have hmap :
      (bipNeighborsA (activeRelation R A₀ B₀) u).map eB =
        bipNeighborsA R u.1 := by
    ext v
    constructor
    · intro hv
      rcases Finset.mem_map.mp hv with ⟨v₀, hv₀, hval⟩
      apply mem_bipNeighborsA.mpr
      have hvR : R u.1 v₀.1 := by
        simpa [bipNeighborsA] using hv₀
      simpa [eB] using hval ▸ hvR
    · intro hv
      have hvR : R u.1 v := mem_bipNeighborsA.mp hv
      let v₀ : ↑B₀ := ⟨v, (hsupport u.1 v hvR).2⟩
      exact Finset.mem_map.mpr ⟨v₀, mem_bipNeighborsA.mpr hvR, rfl⟩
  calc
    bipDegreeA (activeRelation R A₀ B₀) u =
        (bipNeighborsA (activeRelation R A₀ B₀) u).card := rfl
    _ = ((bipNeighborsA (activeRelation R A₀ B₀) u).map eB).card :=
      (Finset.card_map _).symm
    _ = (bipNeighborsA R u.1).card := congrArg Finset.card hmap
    _ = bipDegreeA R u.1 := rfl

private theorem active_degreeB_eq
    (R : A → B → Prop) [DecidableRel R]
    (A₀ : Finset A) (B₀ : Finset B)
    (hsupport : ∀ u v, R u v → u ∈ A₀ ∧ v ∈ B₀) (v : ↑B₀) :
    bipDegreeB (activeRelation R A₀ B₀) v = bipDegreeB R v.1 := by
  classical
  let eA : (↑A₀) ↪ A := activeEmbedding A₀
  have hmap :
      (bipNeighborsB (activeRelation R A₀ B₀) v).map eA =
        bipNeighborsB R v.1 := by
    ext u
    constructor
    · intro hu
      rcases Finset.mem_map.mp hu with ⟨u₀, hu₀, hval⟩
      apply mem_bipNeighborsB.mpr
      have huR : R u₀.1 v.1 := by
        simpa [bipNeighborsB] using hu₀
      simpa [eA] using hval ▸ huR
    · intro hu
      have huR : R u v.1 := mem_bipNeighborsB.mp hu
      let u₀ : ↑A₀ := ⟨u, (hsupport u v.1 huR).1⟩
      exact Finset.mem_map.mpr ⟨u₀, mem_bipNeighborsB.mpr huR, rfl⟩
  calc
    bipDegreeB (activeRelation R A₀ B₀) v =
        (bipNeighborsB (activeRelation R A₀ B₀) v).card := rfl
    _ = ((bipNeighborsB (activeRelation R A₀ B₀) v).map eA).card :=
      (Finset.card_map _).symm
    _ = (bipNeighborsB R v.1).card := congrArg Finset.card hmap
    _ = bipDegreeB R v.1 := rfl

private theorem active_codegree_eq
    (R : A → B → Prop) [DecidableRel R]
    (A₀ : Finset A) (B₀ : Finset B)
    (hsupport : ∀ u v, R u v → u ∈ A₀ ∧ v ∈ B₀) (u w : ↑A₀) :
    bipCodegree (activeRelation R A₀ B₀) u w = bipCodegree R u.1 w.1 := by
  classical
  let eB : (↑B₀) ↪ B := activeEmbedding B₀
  let C₀ := Finset.univ.filter fun v : ↑B₀ ↦
    activeRelation R A₀ B₀ u v ∧ activeRelation R A₀ B₀ w v
  let C := Finset.univ.filter fun v : B ↦ R u.1 v ∧ R w.1 v
  have hmap : C₀.map eB = C := by
    ext v
    constructor
    · intro hv
      rcases Finset.mem_map.mp hv with ⟨v₀, hv₀, hval⟩
      have hv₀' : R u.1 v₀.1 ∧ R w.1 v₀.1 := by
        change v₀ ∈ Finset.univ.filter (fun z : ↑B₀ ↦
          R u.1 z.1 ∧ R w.1 z.1) at hv₀
        exact (Finset.mem_filter.mp hv₀).2
      change v ∈ Finset.univ.filter fun z : B ↦ R u.1 z ∧ R w.1 z
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      simpa [eB] using hval ▸ hv₀'
    · intro hv
      have hv' : R u.1 v ∧ R w.1 v := by simpa [C] using hv
      let v₀ : ↑B₀ := ⟨v, (hsupport u.1 v hv'.1).2⟩
      refine Finset.mem_map.mpr ⟨v₀, ?_, rfl⟩
      change v₀ ∈ Finset.univ.filter (fun z : ↑B₀ ↦
        R u.1 z.1 ∧ R w.1 z.1)
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv'⟩
  calc
    bipCodegree (activeRelation R A₀ B₀) u w = C₀.card := rfl
    _ = (C₀.map eB).card := (Finset.card_map _).symm
    _ = C.card := congrArg Finset.card hmap
    _ = bipCodegree R u.1 w.1 := rfl

private theorem active_edgeCount_eq
    (R : A → B → Prop) [DecidableRel R]
    (A₀ : Finset A) (B₀ : Finset B) (r : ℕ)
    (hsupport : ∀ u v, R u v → u ∈ A₀ ∧ v ∈ B₀)
    (hregular : ∀ v ∈ B₀, bipDegreeB R v = r) :
    bipEdgeCount (activeRelation R A₀ B₀) = bipEdgeCount R := by
  classical
  have hregular₀ : ∀ v : ↑B₀,
      bipDegreeB (activeRelation R A₀ B₀) v = r := by
    intro v
    rw [active_degreeB_eq R A₀ B₀ hsupport v]
    exact hregular v.1 v.2
  have houtside : ∀ v ∉ B₀, bipDegreeB R v = 0 := by
    intro v hv
    have hfalse : ∀ u, ¬ R u v := by
      intro u huv
      exact hv ((hsupport u v huv).2)
    simp [bipDegreeB, bipNeighborsB, hfalse]
  rw [bipEdgeCount_eq_sum_degreeB, bipEdgeCount_eq_sum_degreeB]
  calc
    (∑ v : ↑B₀, bipDegreeB (activeRelation R A₀ B₀) v) =
        B₀.card * r := by simp [hregular₀]
    _ = ∑ v ∈ B₀, bipDegreeB R v := by
      symm
      calc
        (∑ v ∈ B₀, bipDegreeB R v) = ∑ _v ∈ B₀, r := by
          apply Finset.sum_congr rfl
          intro v hv
          exact hregular v hv
        _ = B₀.card * r := by simp
    _ = ∑ v : B, bipDegreeB R v := by
      apply Finset.sum_subset (Finset.subset_univ B₀)
      intro v hvuniv hvnot
      exact houtside v hvnot

private theorem active_restrictedDegree_map
    (R : A → B → Prop) [DecidableRel R]
    (A₀ : Finset A) (B₀ : Finset B)
    (S : Finset (↑A₀)) (T : Finset (↑B₀)) (u : ↑A₀) :
    bipRestrictedDegreeA R (T.map (activeEmbedding B₀)) u.1 =
      bipRestrictedDegreeA (activeRelation R A₀ B₀) T u := by
  classical
  let eB : (↑B₀) ↪ B := activeEmbedding B₀
  have hmap :
      (T.filter fun v ↦ activeRelation R A₀ B₀ u v).map eB =
        (T.map eB).filter (R u.1) := by
    ext v
    simp [eB, activeRelation]
  change ((T.map eB).filter (R u.1)).card =
    (T.filter fun v ↦ activeRelation R A₀ B₀ u v).card
  rw [← hmap, Finset.card_map]

private theorem active_restrictedEdgeCount_map
    (R : A → B → Prop) [DecidableRel R]
    (A₀ : Finset A) (B₀ : Finset B)
    (S : Finset (↑A₀)) (T : Finset (↑B₀)) :
    bipRestrictedEdgeCount R (S.map (activeEmbedding A₀))
        (T.map (activeEmbedding B₀)) =
      bipRestrictedEdgeCount (activeRelation R A₀ B₀) S T := by
  classical
  let eA : (↑A₀) ↪ A := activeEmbedding A₀
  let eB : (↑B₀) ↪ B := activeEmbedding B₀
  change (∑ u ∈ S.map eA, bipRestrictedDegreeA R (T.map eB) u) =
    ∑ u ∈ S, bipRestrictedDegreeA (activeRelation R A₀ B₀) T u
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro u hu
  exact active_restrictedDegree_map R A₀ B₀ S T u

/-- **Janzer--Sudakov Lemma 4.1 on active vertex sets.**

The ambient relation is assumed to be supported on `A₀ × B₀`.  Thus the
right-regularity, left maximum-degree, and codegree hypotheses only have to be
checked on the current active sets.  The resulting restriction is returned as
ambient finsets, together with containment in the active sets. -/
theorem exists_keyRestriction_active
    (R : A → B → Prop) [DecidableRel R]
    (A₀ : Finset A) (B₀ : Finset B)
    (r s t : ℕ) (hr : 0 < r) (hs : 0 < s) (hst : s < t)
    (hsupport : ∀ u v, R u v → u ∈ A₀ ∧ v ∈ B₀)
    (hA₀ : A₀.Nonempty)
    (hregular : ∀ v ∈ B₀, bipDegreeB R v = r)
    (hmax : ∀ u ∈ A₀, bipDegreeA R u ≤ 2 ^ t)
    (hcodeg : ∀ u ∈ A₀, ∀ w ∈ A₀, u ≠ w →
      bipCodegree R u w ≤ 2 ^ (r * s - (r - 1) * t))
    (hdensity : 2 ^ s * A₀.card ≤ bipEdgeCount R) :
    ∃ A' B', A' ⊆ A₀ ∧ B' ⊆ B₀ ∧
      IsKeyRestriction R r (t - s)
        (2 ^ (r * s - (r - 1) * t)) A' B' := by
  classical
  let R₀ : (↑A₀) → (↑B₀) → Prop := activeRelation R A₀ B₀
  have hnonempty₀ : Nonempty (↑A₀) := by
    rcases hA₀ with ⟨u, hu⟩
    exact ⟨⟨u, hu⟩⟩
  have hregular₀ : ∀ v, bipDegreeB R₀ v = r := by
    intro v
    rw [active_degreeB_eq R A₀ B₀ hsupport v]
    exact hregular v.1 v.2
  have hmax₀ : ∀ u, bipDegreeA R₀ u ≤ 2 ^ t := by
    intro u
    rw [active_degreeA_eq R A₀ B₀ hsupport u]
    exact hmax u.1 u.2
  have hcodeg₀ : ∀ u w, u ≠ w →
      bipCodegree R₀ u w ≤ 2 ^ (r * s - (r - 1) * t) := by
    intro u w huw
    rw [active_codegree_eq R A₀ B₀ hsupport u w]
    apply hcodeg u.1 u.2 w.1 w.2
    intro heq
    exact huw (Subtype.ext heq)
  have hedge₀ : bipEdgeCount R₀ = bipEdgeCount R :=
    active_edgeCount_eq R A₀ B₀ r hsupport hregular
  have hdensity₀ : 2 ^ s * Fintype.card (↑A₀) ≤ bipEdgeCount R₀ := by
    simpa [hedge₀] using hdensity
  obtain ⟨S, T, hkey⟩ := exists_keyRestriction_core R₀ r s t hr hs hst
    hnonempty₀ hregular₀ hmax₀ hcodeg₀ hdensity₀
  let eA : (↑A₀) ↪ A := activeEmbedding A₀
  let eB : (↑B₀) ↪ B := activeEmbedding B₀
  let A' : Finset A := S.map eA
  let B' : Finset B := T.map eB
  have hAcard : A'.card = S.card := by simp [A']
  have hedgeMap : bipRestrictedEdgeCount R A' B' =
      bipRestrictedEdgeCount R₀ S T := by
    exact active_restrictedEdgeCount_map R A₀ B₀ S T
  rcases hkey with ⟨hSne, hclosed₀, hlower, hdegree⟩
  refine ⟨A', B', ?_, ?_, ?_⟩
  · intro u hu
    rcases Finset.mem_map.mp hu with ⟨u₀, hu₀, rfl⟩
    exact u₀.2
  · intro v hv
    rcases Finset.mem_map.mp hv with ⟨v₀, hv₀, rfl⟩
    exact v₀.2
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rcases hSne with ⟨u, hu⟩
      exact ⟨eA u, Finset.mem_map.mpr ⟨u, hu, rfl⟩⟩
    · intro v u huv
      rcases Finset.mem_map.mp v.2 with ⟨v₀, hv₀, hval⟩
      let u₀ : ↑A₀ := ⟨u, (hsupport u v.1 huv).1⟩
      have huv₀ : R₀ u₀ v₀ := by
        change R u v₀.1
        have hval' : v₀.1 = v.1 := by exact hval
        rw [hval']
        exact huv
      have huS := hclosed₀ ⟨v₀, hv₀⟩ u₀ huv₀
      exact Finset.mem_map.mpr ⟨u₀, huS, rfl⟩
    · simpa only [hAcard, hedgeMap] using hlower
    · intro u huA'
      rcases Finset.mem_map.mp huA' with ⟨u₀, huS, hval⟩
      have hdu := hdegree u₀ huS
      have hval' : u₀.1 = u := by exact hval
      subst u
      change bipRestrictedDegreeA R (T.map (activeEmbedding B₀)) u₀.1 *
          A'.card ≤
        40 * (t - s) * r ^ 2 * bipRestrictedEdgeCount R A' B'
      rw [active_restrictedDegree_map R A₀ B₀ S T u₀, hAcard, hedgeMap]
      exact hdu

#print axioms exists_keyRestriction_active

end ActiveRestriction

end Erdos182
