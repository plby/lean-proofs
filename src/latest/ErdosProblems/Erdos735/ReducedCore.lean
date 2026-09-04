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

import ErdosProblems.Erdos735.ConcretePolarEndpointRestriction
import ErdosProblems.Erdos735.ConcreteStage3Local
import ErdosProblems.Erdos735.CyclicPacking
import ErdosProblems.Erdos735.LeviProjective

/-!
# Assembly of the concrete reduced ABKPR core

This module records the first assumption-free assembly step from a reduced
magic configuration.  It extracts a noncollinear blue triple, constructs the
literal polar cellulation and its concrete `ABKPR.Data`, and installs the
proved endpoint restriction together with its finite-cycle packing
consequence.
-/

open Classical
noncomputable section

namespace Erdos735.ReducedCore

open ProjectiveArrangement ProjectiveBoundaryExtraction

abbrev Point := ProjectiveArrangement.Point

/-- A noncollinear reduced blue class contains a concrete noncollinear
triple.  This is stated with the projective determinant predicate used by
the polar construction. -/
theorem exists_noncollinear_nonordinary_triple
    {P : Finset Point} {w : Point → ℝ} {c : ℝ}
    (hAcard : 2 ≤ (ordinaryPoints P).card)
    (hB : (nonordinaryPoints P).Nonempty)
    (hred : IsReducedMagic P w c) :
    ∃ a ∈ nonordinaryPoints P, ∃ b ∈ nonordinaryPoints P,
      ∃ d ∈ nonordinaryPoints P,
        ¬ ProjectiveDuality.Collinear3 a b d := by
  have hncol : ¬ Collinear ℝ (nonordinaryPoints P : Set Point) :=
    not_collinear_nonordinaryPoints_of_reducedMagic hAcard hB hred
  obtain ⟨a, ha, b, hb, hab⟩ :=
    SylvesterGallai.exists_ne_of_not_collinear hncol
  by_cases hthird : ∃ d ∈ nonordinaryPoints P,
      ¬ ProjectiveDuality.Collinear3 a b d
  · obtain ⟨d, hd, hnd⟩ := hthird
    exact ⟨a, ha, b, hb, d, hd, hnd⟩
  · exfalso
    apply hncol
    apply SylvesterGallai.collinear_of_subset_line
    intro p hp
    have hpcol : ProjectiveDuality.Collinear3 a b p := by
      by_contra hnp
      exact hthird ⟨p, hp, hnp⟩
    have hpaff : p ∈ line[ℝ, a, b] :=
      (collinear3_iff_mem_affineSpan_pair hab).mp hpcol
    apply (SylvesterGallai.mem_lineThrough_iff
      (p := p) (a := a) (b := b)).2
    rw [mem_affineSpan_pair_iff_exists_lineMap_eq] at hpaff
    obtain ⟨t, ht⟩ := hpaff
    refine ⟨t, ?_⟩
    rw [← ht]
    simp [AffineMap.lineMap_apply_module']

/-- The concrete discharging objects attached to a fixed noncollinear blue
triple satisfy both the geometric endpoint restriction and the resulting
cyclic neighbor-packing inequalities. -/
def HasConcreteABKPRSetup
    {P : Finset Point} {w : Point → ℝ} {c : ℝ}
    (hred : IsReducedMagic P w c)
    {a b d : Point}
    (ha : a ∈ nonordinaryPoints P) (hb : b ∈ nonordinaryPoints P)
    (hd : d ∈ nonordinaryPoints P)
    (hncol : ¬ ProjectiveDuality.Collinear3 a b d) : Prop :=
  letI : Nonempty (ProjectiveBoundaryExtraction.Line (nonordinaryPoints P)) :=
    ⟨⟨a, ha⟩⟩
  let C := ConcretePolarCellulation.blueCellulation
    (nonordinaryPoints P) ha hb hd hncol
  let D : ABKPR.Data C :=
    ConcretePolarABKPRData.concreteData hred ha hb hd hncol
  D.EndpointRestriction ∧ D.NeighborPacking ∧
    SignVectorArrangement.HasProjectiveSignVectorLeviProperty
      (ProjectiveBoundaryExtraction.normals (nonordinaryPoints P))

theorem hasConcreteABKPRSetup
    {P : Finset Point} {w : Point → ℝ} {c : ℝ}
    (hred : IsReducedMagic P w c)
    {a b d : Point}
    (ha : a ∈ nonordinaryPoints P) (hb : b ∈ nonordinaryPoints P)
    (hd : d ∈ nonordinaryPoints P)
    (hncol : ¬ ProjectiveDuality.Collinear3 a b d) :
    HasConcreteABKPRSetup hred ha hb hd hncol := by
  let : Nonempty (ProjectiveBoundaryExtraction.Line (nonordinaryPoints P)) :=
    ⟨⟨a, ha⟩⟩
  let C := ConcretePolarCellulation.blueCellulation
    (nonordinaryPoints P) ha hb hd hncol
  let D : ABKPR.Data C :=
    ConcretePolarABKPRData.concreteData hred ha hb hd hncol
  change D.EndpointRestriction ∧ D.NeighborPacking ∧
    SignVectorArrangement.HasProjectiveSignVectorLeviProperty
      (ProjectiveBoundaryExtraction.normals (nonordinaryPoints P))
  have hrest : D.EndpointRestriction :=
    ConcretePolarEndpointRestriction.concreteData_endpointRestriction
      hred ha hb hd hncol
  exact ⟨hrest, D.neighborPacking_of_endpointRestriction hrest,
    LeviExteriorSector.hasProjectiveSignVectorLeviProperty_of_noncollinear_triple
      (nonordinaryPoints P) ha hb hd hncol⟩

/-- The checked setup carried by every instance of the reduced-core input
appearing in `classified_of_magic_of_reduced_core_all`. -/
structure Setup (P : Finset Point) (w : Point → ℝ) (c : ℝ) where
  hAcard : 3 ≤ (ordinaryPoints P).card
  hB : (nonordinaryPoints P).Nonempty
  hred : IsReducedMagic P w c
  a : Point
  ha : a ∈ nonordinaryPoints P
  b : Point
  hb : b ∈ nonordinaryPoints P
  d : Point
  hd : d ∈ nonordinaryPoints P
  hncol : ¬ ProjectiveDuality.Collinear3 a b d
  concrete : HasConcreteABKPRSetup hred ha hb hd hncol

namespace Setup

variable {P : Finset Point} {w : Point → ℝ} {c : ℝ}

/-- The nonempty line index type supplied by the selected first blue
point. -/
theorem lineNonempty (S : Setup P w c) :
    Nonempty (ProjectiveBoundaryExtraction.Line (nonordinaryPoints P)) :=
  ⟨⟨S.a, S.ha⟩⟩

/-- The literal polar blue cellulation selected by the setup. -/
noncomputable abbrev C (S : Setup P w c) :=
  letI := S.lineNonempty
  ConcretePolarCellulation.blueCellulation
    (nonordinaryPoints P) S.ha S.hb S.hd S.hncol

/-- The concrete ABKPR data on the selected polar cellulation. -/
noncomputable abbrev D (S : Setup P w c) : ABKPR.Data S.C :=
  letI := S.lineNonempty
  ConcretePolarABKPRData.concreteData S.hred S.ha S.hb S.hd S.hncol

theorem endpointRestriction (S : Setup P w c) : S.D.EndpointRestriction := by
  let := S.lineNonempty
  exact
    ConcretePolarEndpointRestriction.concreteData_endpointRestriction
      S.hred S.ha S.hb S.hd S.hncol

theorem neighborPacking (S : Setup P w c) : S.D.NeighborPacking := by
  let := S.lineNonempty
  exact S.D.neighborPacking_of_endpointRestriction S.endpointRestriction

theorem leviProperty (S : Setup P w c) :
    SignVectorArrangement.HasProjectiveSignVectorLeviProperty
      (ProjectiveBoundaryExtraction.normals (nonordinaryPoints P)) :=
  LeviExteriorSector.hasProjectiveSignVectorLeviProperty_of_noncollinear_triple
    (nonordinaryPoints P) S.ha S.hb S.hd S.hncol

/-- The exact next proof split: either one of the four explicit local
Stage-3 obstructions occurs, or the complete reduced Stage-3 geometry has
already been constructed. -/
theorem stage3Dichotomy (S : Setup P w c) :
    S.D.Stage3LocalObstruction ∨ Nonempty S.D.ReducedStage3Geometry := by
  let := S.lineNonempty
  exact ConcreteStage3Local.localObstruction_or_reducedStage3Geometry
    S.hred S.ha S.hb S.hd S.hncol

end Setup

/-- Assemble the concrete reduced-core package from exactly the hypotheses
of the final reduced-core interface. -/
theorem setup_nonempty
    {P : Finset Point} {w : Point → ℝ} {c : ℝ}
    (hAcard : 3 ≤ (ordinaryPoints P).card)
    (hB : (nonordinaryPoints P).Nonempty)
    (hred : IsReducedMagic P w c) : Nonempty (Setup P w c) := by
  obtain ⟨a, ha, b, hb, d, hd, hncol⟩ :=
    exists_noncollinear_nonordinary_triple (le_trans (by omega) hAcard) hB hred
  exact ⟨
    { hAcard := hAcard
      hB := hB
      hred := hred
      a := a
      ha := ha
      b := b
      hb := hb
      d := d
      hd := hd
      hncol := hncol
      concrete := hasConcreteABKPRSetup hred ha hb hd hncol }⟩

/-- A selected concrete setup, for use by the downstream assembly without
repeating witness extraction. -/
noncomputable def setup
    {P : Finset Point} {w : Point → ℝ} {c : ℝ}
    (hAcard : 3 ≤ (ordinaryPoints P).card)
    (hB : (nonordinaryPoints P).Nonempty)
    (hred : IsReducedMagic P w c) : Setup P w c :=
  Classical.choice (setup_nonempty hAcard hB hred)

end Erdos735.ReducedCore
