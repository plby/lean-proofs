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

import ErdosProblems.Erdos735.ConcreteBadReceiver
import ErdosProblems.Erdos735.ConcreteDoubleCornerSector

/-!
# Red feasibility of the sector opposite a double corner

An incident red projective line enters exactly two sectors at a double blue
crossing.  The adjacent-sector exclusion forces these to be opposite
sectors.  This file records the resulting pointwise statement, which is the
red-diagonal input for the Stage-4 helping-opposite exclusion.
-/

open Classical
noncomputable section
open scoped LinearAlgebra.Projectivization

namespace Erdos735.ConcreteRedOppositeSector

open ChartOrder ProjectiveArrangement ProjectiveBoundaryExtraction
open SignVector SignVector.RedChordSector
open ConcretePolarOrientedVertex

abbrev Point := ProjectiveArrangement.Point
abbrev Line (B : Finset Point) := ProjectiveBoundaryExtraction.Line B

/-- At a double blue corner, flipping both incident owner signs preserves
feasibility on an incident red line. -/
theorem restrictedRealizable_opposite_sector
    {P : Finset Point}
    [Nonempty (Line (nonordinaryPoints P))]
    (v : OrientedVertex (nonordinaryPoints P))
    (hmult : lineMultiplicity (OnLine (nonordinaryPoints P)) v.1 = 2)
    (s t : Line (nonordinaryPoints P)) (hst : s ≠ t)
    (hvs : OnLine (nonordinaryPoints P) v.1 s)
    (hvt : OnLine (nonordinaryPoints P) v.1 t)
    (f g : StrictFace (normals (nonordinaryPoints P)))
    (hwf : WeaklyRealizes (normals (nonordinaryPoints P)) f.1
      (orientedRep v))
    (hwg : WeaklyRealizes (normals (nonordinaryPoints P)) g.1
      (orientedRep v))
    (hsg : f.1 s ≠ g.1 s) (htg : f.1 t ≠ g.1 t)
    (a : Point) (ha : a ∈ ordinaryPoints P)
    (hfrest : RestrictedRealizable (normals (nonordinaryPoints P))
      (normalVec a) f.1)
    (hav : Incident v.1.1 a) :
    RestrictedRealizable (normals (nonordinaryPoints P))
      (normalVec a) g.1 := by
  let n := normals (nonordinaryPoints P)
  let S := SignVector.LocalReceiver.localReceiverFaces n
    (normalVec a) (orientedRep v)
  have hs0 : dotProduct (n s) (orientedRep v) = 0 := by
    apply (onProjectiveLine_mk_iff _ _ (orientedRep_ne_zero v)).mp
    rw [orientedRep_projectivization]
    exact hvs
  have ht0 : dotProduct (n t) (orientedRep v) = 0 := by
    apply (onProjectiveLine_mk_iff _ _ (orientedRep_ne_zero v)).mp
    rw [orientedRep_projectivization]
    exact hvt
  have ha0 : dotProduct (normalVec a) (orientedRep v) = 0 := by
    apply (onProjectiveLine_mk_iff _ _ (orientedRep_ne_zero v)).mp
    rw [orientedRep_projectivization]
    exact hav
  have hcard : S.card = 2 := by
    exact ConcreteBadReceiver.localReceiverFaces_card_eq_two_at_badVertex
      v hmult ha hav
  have hfmem : f ∈ S := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwf, hfrest⟩
  have hfg : f ≠ g := by
    intro h
    exact hsg (congrArg (fun q : StrictFace n ↦ q.1 s) h)
  have hsub : S ⊆ {f, g} := by
    intro x hx
    have hxdata := Finset.mem_filter.mp hx
    have hwx : WeaklyRealizes n x.1 (orientedRep v) := hxdata.2.1
    have hxrest : RestrictedRealizable n (normalVec a) x.1 := hxdata.2.2
    by_cases hxs : x.1 s = f.1 s
    · by_cases hxt : x.1 t = f.1 t
      · simp only [Finset.mem_insert, Finset.mem_singleton]
        left
        exact ConcreteDoubleCornerSector.face_eq_of_common_double_corner_of_owner_signs
          v hmult s t hst hvs hvt x f hwx hwf hxs hxt
      · exfalso
        exact RedBlueDualIncidence.not_restrictedRealizable_of_flip_right
          n (normalVec a) (orientedRep v) s t f.1 x.1
          (orientedRep_ne_zero v) (normalVec_ne_zero a)
          hs0 ht0 ha0 hxs
          (SignVector.LocalReceiver.bool_eq_not_of_ne hxt)
          hfrest hxrest
    · by_cases hxt : x.1 t = f.1 t
      · exfalso
        exact RedBlueDualIncidence.not_restrictedRealizable_of_flip_left
          n (normalVec a) (orientedRep v) s t f.1 x.1
          (orientedRep_ne_zero v) (normalVec_ne_zero a)
          hs0 ht0 ha0
          (SignVector.LocalReceiver.bool_eq_not_of_ne hxs) hxt
          hfrest hxrest
      · simp only [Finset.mem_insert, Finset.mem_singleton]
        right
        apply ConcreteDoubleCornerSector.face_eq_of_common_double_corner_of_owner_signs
          v hmult s t hst hvs hvt x g hwx hwg
        · exact (SignVector.LocalReceiver.bool_eq_of_ne_ne
            hxs hsg.symm).symm
        · exact (SignVector.LocalReceiver.bool_eq_of_ne_ne
            hxt htg.symm).symm
  have hpaircard : ({f, g} : Finset (StrictFace n)).card = 2 :=
    Finset.card_pair hfg
  have heq : S = {f, g} := by
    exact Finset.Subset.antisymm hsub
      (Finset.eq_of_subset_of_card_le hsub (by omega) |>.symm.subset)
  have hgmem : g ∈ S := by
    rw [heq]
    simp
  exact (Finset.mem_filter.mp hgmem).2.2

end Erdos735.ConcreteRedOppositeSector
