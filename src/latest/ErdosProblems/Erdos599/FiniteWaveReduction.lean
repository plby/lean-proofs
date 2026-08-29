/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.WaveLimits

/-!
# Finite-member reduction of concrete waves

The terminal frontier of a concrete path family only records finite members.
Consequently, deleting every ray from a wave preserves its terminal frontier
and hence preserves the wave property.  The retained family has finite
character by construction.
-/

namespace Erdos599

open Set DirectedPath

universe u

namespace DWeb

variable {V : Type u} (G : DWeb V)

/-- The subfamily consisting of the finite members of `W`. -/
def finitePathSubfamily (W : Set G.DPath) : Set G.DPath :=
  {p | p ∈ W ∧ ∃ q : DirectedPath.FinitePath G.graph, p = .inl q}

@[simp]
theorem mem_finitePathSubfamily {W : Set G.DPath} {p : G.DPath} :
    p ∈ G.finitePathSubfamily W ↔
      p ∈ W ∧ ∃ q : DirectedPath.FinitePath G.graph, p = .inl q :=
  Iff.rfl

theorem finitePathSubfamily_subset (W : Set G.DPath) :
    G.finitePathSubfamily W ⊆ W :=
  fun _ hp ↦ hp.1

/-- The finite-member restriction has finite character by definition. -/
theorem hasFiniteCharacter_finitePathSubfamily (W : Set G.DPath) :
    G.HasFiniteCharacter (G.finitePathSubfamily W) := by
  intro p hp
  exact hp.2

/-- Rays never contribute to a terminal frontier, so discarding all of them
leaves that frontier unchanged. -/
@[simp]
theorem terminalFrontier_finitePathSubfamily (W : Set G.DPath) :
    G.terminalFrontier (G.finitePathSubfamily W) = G.terminalFrontier W := by
  apply Set.Subset.antisymm
  · rintro x ⟨p, hp, hpx⟩
    exact ⟨p, hp.1, hpx⟩
  · rintro x ⟨p, hp, hpx⟩
    rcases p with p | r
    · exact ⟨.inl p, ⟨hp, p, rfl⟩, hpx⟩
    · rw [G.terminal?_ray] at hpx
      cases hpx

/-- Removing all ray members of a concrete wave yields another wave with the
same terminal frontier. -/
theorem IsWave.finitePathSubfamily {W : Set G.DPath} (hW : G.IsWave W) :
    G.IsWave (G.finitePathSubfamily W) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p hp q hq hpq
    exact hW.1 hp.1 hq.1 hpq
  · rintro x ⟨p, hp, rfl⟩
    exact hW.2.1 ⟨p, hp.1, rfl⟩
  · rw [G.terminalFrontier_finitePathSubfamily]
    exact hW.2.2

/-- Bundled finite-member restriction of a concrete wave. -/
def Wave.finitePathSubfamily (W : G.Wave) : G.Wave :=
  ⟨G.finitePathSubfamily W.1, W.2.finitePathSubfamily⟩

@[simp]
theorem Wave.finitePathSubfamily_paths (W : G.Wave) :
    W.finitePathSubfamily.1 = G.finitePathSubfamily W.1 :=
  rfl

theorem Wave.finitePathSubfamily_hasFiniteCharacter (W : G.Wave) :
    G.HasFiniteCharacter W.finitePathSubfamily.1 :=
  G.hasFiniteCharacter_finitePathSubfamily W.1

@[simp]
theorem Wave.finitePathSubfamily_terminalFrontier (W : G.Wave) :
    G.terminalFrontier W.finitePathSubfamily.1 = G.terminalFrontier W.1 :=
  G.terminalFrontier_finitePathSubfamily W.1

/-! ## Finite-character roof-maximal extensions -/

/-- The chosen maximal forward extension used to build a finite-character
roof-maximal extension.  This witness is deliberately kept separate from the
final construction: deleting its rays preserves its terminal frontier, while
the source arrow preserves the old finite paths. -/
noncomputable def finiteMaximalExtensionWitness (U : G.Wave) : G.Wave :=
  Classical.choose (G.exists_maximal_wave_extending U)

theorem le_finiteMaximalExtensionWitness (U : G.Wave) :
    U ≤ G.finiteMaximalExtensionWitness U :=
  (Classical.choose_spec (G.exists_maximal_wave_extending U)).1

theorem finiteMaximalExtensionWitness_isMax (U : G.Wave) :
    IsMax (G.finiteMaximalExtensionWitness U) :=
  (Classical.choose_spec (G.exists_maximal_wave_extending U)).2

/-- Arrow preserves finite character when both input families have finite
character.  This local version lives with the finite-wave construction so it
does not require the later slicing development. -/
theorem appendAt_hasFiniteCharacter
    (p : DirectedPath.FinitePath G.graph)
    (q : DirectedPath.Path G.graph) (hx : p.finish ∈ q.support)
    (happend : DirectedPath.Path.Appendable p q hx)
    (hq : ∃ g : DirectedPath.FinitePath G.graph, q = .inl g) :
    ∃ g : DirectedPath.FinitePath G.graph,
      DirectedPath.Path.appendAt p q hx happend = .inl g := by
  rcases q with q | r
  · exact ⟨p.appendSuffix q hx
      (p.disjoint_tail_of_appendableFinite q hx happend), rfl⟩
  · obtain ⟨g, hg⟩ := hq
    cases hg

theorem hasFiniteCharacter_arrow_of_finite
    {U W : Set G.DPath}
    (hU : G.HasFiniteCharacter U) (hW : G.HasFiniteCharacter W) :
    G.HasFiniteCharacter (G.arrow U W) := by
  rintro r ⟨p, rfl⟩
  rcases p with ⟨p, hpU⟩
  obtain ⟨f, rfl⟩ := hU hpU
  rcases G.arrowPath_finite_cases U W f hpU with heq | ⟨c, heq⟩
  · exact ⟨f, heq⟩
  · rw [heq]
    exact G.appendAt_hasFiniteCharacter f c.path c.finish_mem
      (c.appendable hpU) (hW c.mem_path)

/-- A finite-character wave that forward-extends `U` and retains the roof of
a maximal forward extension.  The arrow is essential here: simply deleting
rays from the maximal extension would lose pathwise preservation of `U`. -/
noncomputable def finiteRoofMaximalExtension
    (U : G.Wave) : G.Wave := by
  let Mfinite := (G.finiteMaximalExtensionWitness U).finitePathSubfamily
  exact ⟨G.arrow U.1 Mfinite.1, G.isWave_arrow U.2 Mfinite.2⟩

theorem le_finiteRoofMaximalExtension (U : G.Wave) :
    U ≤ G.finiteRoofMaximalExtension U :=
  G.forwardExtension_arrow U.1
    (G.finiteMaximalExtensionWitness U).finitePathSubfamily.1

theorem finiteRoofMaximalExtension_hasFiniteCharacter
    (U : G.Wave) (hU : G.HasFiniteCharacter U.1) :
    G.HasFiniteCharacter (G.finiteRoofMaximalExtension U).1 := by
  exact G.hasFiniteCharacter_arrow_of_finite hU
    (G.finiteMaximalExtensionWitness U).finitePathSubfamily_hasFiniteCharacter

/-- The finite extension roofs every wave.  This is the universal roof
maximality property needed by the Section 6 recursion; it intentionally does
not claim forward-extension maximality, which can fail after rays are
discarded. -/
theorem roofLE_finiteRoofMaximalExtension
    (U W : G.Wave) :
    G.RoofLE W.1 (G.finiteRoofMaximalExtension U).1 := by
  let M := G.finiteMaximalExtensionWitness U
  let Mf := M.finitePathSubfamily
  have hWM : G.RoofLE W.1 M.1 :=
    G.roofLE_of_isMax (G.finiteMaximalExtensionWitness_isMax U) W
  have hWMf : G.RoofLE W.1 Mf.1 := by
    simpa only [RoofLE, Mf, Wave.finitePathSubfamily_terminalFrontier] using hWM
  exact hWMf.trans (G.roofLE_arrow_right U.2 Mf.2)

theorem finiteRoofMaximalExtension_isRoofMaximal (U : G.Wave) :
    G.IsRoofMaximal (G.finiteRoofMaximalExtension U) := by
  intro W _
  exact G.roofLE_finiteRoofMaximalExtension U W

end DWeb

end Erdos599
