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

import ErdosProblems.Erdos735.ConcreteDonationPacking
import ErdosProblems.Erdos735.ConcreteDoubleCornerSector

/-!
# Recognition of the remaining donation-packing obstructions

This file isolates the elementary local-sector uniqueness needed for the
donation-vertex and consecutive-bad-edge cases.  At a double blue corner,
there are exactly two incident blue owners.  Consequently the face opposite
a fixed face across both owners is unique, even when the two owners are
presented in a different order.
-/

open Classical
noncomputable section

namespace Erdos735.ConcreteDonationObstructionRecognition

open ChartOrder ProjectiveArrangement ProjectiveBoundaryExtraction
open SignVector SignVector.RedChordSector
open SignVector.PolarBoundaryAcross SignVector.PolarBoundaryOrder
open ConcretePolarOrientedVertex

abbrev Point := ProjectiveArrangement.Point
abbrev Line (B : Finset Point) := ProjectiveBoundaryExtraction.Line B

private lemma bool_eq_of_both_ne
    {a b c : Bool} (hab : a ≠ b) (hcb : c ≠ b) : a = c := by
  cases a <;> cases b <;> cases c <;> simp_all

/-- At a double corner there is a unique strict face which has the opposite
sign from `f` on both incident owners.  The second presentation may list
the same two owners in the other order. -/
theorem opposite_sector_unique_at_double_corner
    {B : Finset Point} [Nonempty (Line B)]
    (v : OrientedVertex B)
    (hmult : lineMultiplicity (OnLine B) v.1 = 2)
    (f x y : StrictFace (normals B))
    (hwx : WeaklyRealizes (normals B) x.1 (orientedRep v))
    (hwy : WeaklyRealizes (normals B) y.1 (orientedRep v))
    (s t : Line B) (hst : s ≠ t)
    (hvs : OnLine B v.1 s) (hvt : OnLine B v.1 t)
    (hfsx : f.1 s ≠ x.1 s) (hftx : f.1 t ≠ x.1 t)
    (r u : Line B) (hru : r ≠ u)
    (hvr : OnLine B v.1 r) (hvu : OnLine B v.1 u)
    (hfry : f.1 r ≠ y.1 r) (hfuy : f.1 u ≠ y.1 u) :
    x = y := by
  let S := Finset.univ.filter fun q : Line B ↦ OnLine B v.1 q
  have hpair : ({r, u} : Finset (Line B)) ⊆ S := by
    intro q hq
    simp only [Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl <;> simp [S, hvr, hvu]
  have hcard : S.card = 2 := hmult
  have hpCard : ({r, u} : Finset (Line B)).card = 2 :=
    Finset.card_pair hru
  have hset : S = {r, u} := by
    exact Finset.Subset.antisymm
      (Finset.eq_of_subset_of_card_le hpair (by omega) |>.symm.subset) hpair
  have howners (q : Line B) (hvq : OnLine B v.1 q) : q = r ∨ q = u := by
    have hq : q ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvq⟩
    rw [hset] at hq
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hq
  have hsxy : x.1 s = y.1 s := by
    rcases howners s hvs with rfl | rfl
    · exact bool_eq_of_both_ne hfsx.symm hfry.symm
    · exact bool_eq_of_both_ne hfsx.symm hfuy.symm
  have htxy : x.1 t = y.1 t := by
    rcases howners t hvt with rfl | rfl
    · exact bool_eq_of_both_ne hftx.symm hfry.symm
    · exact bool_eq_of_both_ne hftx.symm hfuy.symm
  exact ConcreteDoubleCornerSector.face_eq_of_common_double_corner_of_owner_signs
    v hmult s t hst hvs hvt x y hwx hwy hsxy htxy

/-- Two presentations of the sector opposite a fixed face at the same
double corner have the same opposite face.  This is the indexed polar form
used by donation geometry. -/
theorem opposite_across_face_unique_at_double_corner
    {B : Finset Point} [Nonempty (Line B)]
    (hspan : Submodule.span ℝ (Set.range (normals B)) = ⊤)
    (d₁ : StrictFace (normals B))
    (i₁ j₁ : BoundaryIndex (normals B) d₁) (hij₁ : i₁ ≠ j₁)
    (p₁ : BoundaryIndex (normals B)
      (PolarBoundaryAcross.across (normals B) (normals_ne_zero B)
        normal_cross hspan ⟨d₁, i₁⟩).1)
    (q₁ : BoundaryIndex (normals B)
      (PolarBoundaryAcross.across (normals B) (normals_ne_zero B)
        normal_cross hspan ⟨d₁, j₁⟩).1)
    (hpq₁ : boundaryOrientedVertex hspan
        (PolarBoundaryAcross.across (normals B) (normals_ne_zero B)
          normal_cross hspan ⟨d₁, i₁⟩).1 p₁ =
      boundaryOrientedVertex hspan
        (PolarBoundaryAcross.across (normals B) (normals_ne_zero B)
          normal_cross hspan ⟨d₁, j₁⟩).1 q₁)
    (d₂ : StrictFace (normals B))
    (i₂ j₂ : BoundaryIndex (normals B) d₂) (hij₂ : i₂ ≠ j₂)
    (p₂ : BoundaryIndex (normals B)
      (PolarBoundaryAcross.across (normals B) (normals_ne_zero B)
        normal_cross hspan ⟨d₂, i₂⟩).1)
    (q₂ : BoundaryIndex (normals B)
      (PolarBoundaryAcross.across (normals B) (normals_ne_zero B)
        normal_cross hspan ⟨d₂, j₂⟩).1)
    (hpq₂ : boundaryOrientedVertex hspan
        (PolarBoundaryAcross.across (normals B) (normals_ne_zero B)
          normal_cross hspan ⟨d₂, i₂⟩).1 p₂ =
      boundaryOrientedVertex hspan
        (PolarBoundaryAcross.across (normals B) (normals_ne_zero B)
          normal_cross hspan ⟨d₂, j₂⟩).1 q₂)
    (hface :
      (PolarBoundaryAcross.across (normals B) (normals_ne_zero B)
        normal_cross hspan ⟨d₁, i₁⟩).1 =
      (PolarBoundaryAcross.across (normals B) (normals_ne_zero B)
        normal_cross hspan ⟨d₂, i₂⟩).1)
    (hcorner : boundaryOrientedVertex hspan
        (PolarBoundaryAcross.across (normals B) (normals_ne_zero B)
          normal_cross hspan ⟨d₁, i₁⟩).1 p₁ =
      boundaryOrientedVertex hspan
        (PolarBoundaryAcross.across (normals B) (normals_ne_zero B)
          normal_cross hspan ⟨d₂, i₂⟩).1 p₂)
    (hmult : lineMultiplicity (OnLine B)
      (boundaryOrientedVertex hspan
        (PolarBoundaryAcross.across (normals B) (normals_ne_zero B)
          normal_cross hspan ⟨d₁, i₁⟩).1 p₁).1 = 2) :
    (PolarBoundaryAcross.across (normals B) (normals_ne_zero B)
      normal_cross hspan ⟨d₁, j₁⟩).1 =
    (PolarBoundaryAcross.across (normals B) (normals_ne_zero B)
      normal_cross hspan ⟨d₂, j₂⟩).1 := by
  let f₁ := (PolarBoundaryAcross.across (normals B) (normals_ne_zero B)
    normal_cross hspan ⟨d₁, i₁⟩).1
  let x := (PolarBoundaryAcross.across (normals B) (normals_ne_zero B)
    normal_cross hspan ⟨d₁, j₁⟩).1
  let f₂ := (PolarBoundaryAcross.across (normals B) (normals_ne_zero B)
    normal_cross hspan ⟨d₂, i₂⟩).1
  let y := (PolarBoundaryAcross.across (normals B) (normals_ne_zero B)
    normal_cross hspan ⟨d₂, j₂⟩).1
  let v := boundaryOrientedVertex hspan f₁ p₁
  let s : Line B := ⟨(boundaryEdge (normals B) normal_cross hspan d₁ i₁).1.1.1,
    (boundaryEdge (normals B) normal_cross hspan d₁ i₁).1.1.2⟩
  let t : Line B := ⟨(boundaryEdge (normals B) normal_cross hspan d₁ j₁).1.1.1,
    (boundaryEdge (normals B) normal_cross hspan d₁ j₁).1.1.2⟩
  let r : Line B := ⟨(boundaryEdge (normals B) normal_cross hspan d₂ i₂).1.1.1,
    (boundaryEdge (normals B) normal_cross hspan d₂ i₂).1.1.2⟩
  let u : Line B := ⟨(boundaryEdge (normals B) normal_cross hspan d₂ j₂).1.1.1,
    (boundaryEdge (normals B) normal_cross hspan d₂ j₂).1.1.2⟩
  have hst : s ≠ t := by
    intro h
    apply hij₁
    apply (boundaryOwnerEquiv d₁ (faceWitness_realizes (normals B) d₁)
      normal_cross hspan).injective
    apply Subtype.ext
    exact h
  have hru : r ≠ u := by
    intro h
    apply hij₂
    apply (boundaryOwnerEquiv d₂ (faceWitness_realizes (normals B) d₂)
      normal_cross hspan).injective
    apply Subtype.ext
    exact h
  have hsupp₁ := ConcretePolarLocalSector.common_across_corner_on_both_supports
    hspan d₁ i₁ j₁ hij₁ p₁ q₁ hpq₁
  have hsupp₂ := ConcretePolarLocalSector.common_across_corner_on_both_supports
    hspan d₂ i₂ j₂ hij₂ p₂ q₂ hpq₂
  have hvs : OnLine B v.1 s := hsupp₁.1
  have hvt : OnLine B v.1 t := hsupp₁.2
  have hvr : OnLine B v.1 r := by
    change Incident v.1.1 r.1
    simpa [v, r, f₁, f₂, hcorner] using hsupp₂.1
  have hvu : OnLine B v.1 u := by
    change Incident v.1.1 u.1
    simpa [v, u, f₁, f₂, hcorner] using hsupp₂.2
  have hwx : WeaklyRealizes (normals B) x.1 (orientedRep v) := by
    have h := orientedRep_boundaryOrientedVertex_weaklyRealizes hspan x q₁
    simpa [v, x, f₁, hpq₁] using h
  have hwy : WeaklyRealizes (normals B) y.1 (orientedRep v) := by
    have h := orientedRep_boundaryOrientedVertex_weaklyRealizes hspan y q₂
    simpa [v, y, f₁, f₂, hpq₂, hcorner] using h
  apply opposite_sector_unique_at_double_corner v hmult f₁ x y hwx hwy
      s t hst hvs hvt
      (ConcretePolarLocalSector.across_sign_ne_at_first_owner
        hspan d₁ i₁ j₁ hij₁)
      ((ConcretePolarLocalSector.across_sign_ne_at_first_owner
        hspan d₁ j₁ i₁ hij₁.symm).symm)
      r u hru hvr hvu
  · simpa [f₁, f₂, y, hface] using
      (ConcretePolarLocalSector.across_sign_ne_at_first_owner
        hspan d₂ i₂ j₂ hij₂)
  · simpa [f₁, f₂, y, hface] using
      ((ConcretePolarLocalSector.across_sign_ne_at_first_owner
        hspan d₂ j₂ i₂ hij₂.symm).symm)

end Erdos735.ConcreteDonationObstructionRecognition

namespace Erdos735.ConcretePolarABKPRData

open ProjectiveArrangement ProjectiveBoundaryExtraction SignVector ChartOrder
open SignVector.PolarBoundaryAcross SignVector.PolarBoundaryOrder
open ConcretePolarOrientedVertex

abbrev DonationSectorPoint := ProjectiveArrangement.Point

variable {P : Finset DonationSectorPoint} {w : DonationSectorPoint → ℝ} {c : ℝ}
variable (hred : IsReducedMagic P w c)
variable {a b d : DonationSectorPoint}
variable (ha : a ∈ nonordinaryPoints P) (hb : b ∈ nonordinaryPoints P)
variable (hd : d ∈ nonordinaryPoints P)
variable (hncol : ¬ ProjectiveDuality.Collinear3 a b d)
variable [Nonempty (ProjectiveBoundaryExtraction.Line (nonordinaryPoints P))]

private abbrev B₀ := nonordinaryPoints P
private abbrev C₀ := ConcretePolarCellulation.blueCellulation
  (B₀ (P := P)) ha hb hd hncol
private abbrev D₀ := concreteData hred ha hb hd hncol
private abbrev vd₀ := ConcretePolarVertexDegree.concreteVertexEdges_card_eq
  (B₀ (P := P)) ha hb hd hncol

/-- A shared corner of two concrete across faces is a boundary corner of
the original concrete face. -/
theorem concreteData_exists_boundaryVertex_eq_common_across_corner
    (f : StrictFace (normals (B₀ (P := P))))
    (i j : Fin ((C₀ (P := P) ha hb hd hncol).faceDegree f)) (hij : i ≠ j)
    (p : Fin ((C₀ (P := P) ha hb hd hncol).faceDegree
      ((D₀ hred ha hb hd hncol).across ⟨f, i⟩).1))
    (q : Fin ((C₀ (P := P) ha hb hd hncol).faceDegree
      ((D₀ hred ha hb hd hncol).across ⟨f, j⟩).1))
    (hpq : (D₀ hred ha hb hd hncol).boundaryVertex
        ((D₀ hred ha hb hd hncol).across ⟨f, i⟩).1 p =
      (D₀ hred ha hb hd hncol).boundaryVertex
        ((D₀ hred ha hb hd hncol).across ⟨f, j⟩).1 q) :
    ∃ u : Fin ((C₀ (P := P) ha hb hd hncol).faceDegree f),
      (D₀ hred ha hb hd hncol).boundaryVertex f u =
        (D₀ hred ha hb hd hncol).boundaryVertex
          ((D₀ hred ha hb hd hncol).across ⟨f, i⟩).1 p := by
  let E := indexEquiv (vertex_degree := vd₀ ha hb hd hncol)
    ha hb hd hncol
  have hmap (r : FaceDart (vertex_degree := vd₀ ha hb hd hncol)
      ha hb hd hncol) :
      dartEquiv (vertex_degree := vd₀ ha hb hd hncol) ha hb hd hncol
        ((D₀ hred ha hb hd hncol).across r) =
      PolarBoundaryAcross.across (normals (B₀ (P := P)))
        (normals_ne_zero (B₀ (P := P))) normal_cross
        (hspan ha hb hd hncol)
        (dartEquiv (vertex_degree := vd₀ ha hb hd hncol)
          ha hb hd hncol r) := by
    simp [D₀, concreteData, toData, ConcretePolarABKPRData.across]
  have hfi : ((D₀ hred ha hb hd hncol).across ⟨f, i⟩).1 =
      (PolarBoundaryAcross.across (normals (B₀ (P := P)))
        (normals_ne_zero (B₀ (P := P))) normal_cross
        (hspan ha hb hd hncol) ⟨f, E f i⟩).1 :=
    congrArg Sigma.fst (hmap ⟨f, i⟩)
  have hfj : ((D₀ hred ha hb hd hncol).across ⟨f, j⟩).1 =
      (PolarBoundaryAcross.across (normals (B₀ (P := P)))
        (normals_ne_zero (B₀ (P := P))) normal_cross
        (hspan ha hb hd hncol) ⟨f, E f j⟩).1 :=
    congrArg Sigma.fst (hmap ⟨f, j⟩)
  let pp : BoundaryIndex (normals (B₀ (P := P)))
      (PolarBoundaryAcross.across (normals (B₀ (P := P)))
        (normals_ne_zero (B₀ (P := P))) normal_cross
        (hspan ha hb hd hncol) ⟨f, E f i⟩).1 := hfi ▸ E _ p
  let qq : BoundaryIndex (normals (B₀ (P := P)))
      (PolarBoundaryAcross.across (normals (B₀ (P := P)))
        (normals_ne_zero (B₀ (P := P))) normal_cross
        (hspan ha hb hd hncol) ⟨f, E f j⟩).1 := hfj ▸ E _ q
  have hpq' : boundaryOrientedVertex (hspan ha hb hd hncol)
        (PolarBoundaryAcross.across (normals (B₀ (P := P)))
          (normals_ne_zero (B₀ (P := P))) normal_cross
          (hspan ha hb hd hncol) ⟨f, E f i⟩).1 pp =
      boundaryOrientedVertex (hspan ha hb hd hncol)
        (PolarBoundaryAcross.across (normals (B₀ (P := P)))
          (normals_ne_zero (B₀ (P := P))) normal_cross
          (hspan ha hb hd hncol) ⟨f, E f j⟩).1 qq := by
    cases hfi
    cases hfj
    exact hpq
  obtain ⟨u, hu⟩ :=
    ConcretePolarLocalSector.exists_boundaryOrientedVertex_eq_common_across_corner
      (hspan ha hb hd hncol) f (E f i) (E f j)
      (fun h ↦ hij ((E f).injective h)) pp qq hpq'
  refine ⟨(E f).symm u, ?_⟩
  calc
    (D₀ hred ha hb hd hncol).boundaryVertex f ((E f).symm u) =
        boundaryOrientedVertex (hspan ha hb hd hncol) f u := by
      change boundaryOrientedVertex (hspan ha hb hd hncol) f
        (E f ((E f).symm u)) = _
      simp
    _ = boundaryOrientedVertex (hspan ha hb hd hncol)
        (PolarBoundaryAcross.across (normals (B₀ (P := P)))
          (normals_ne_zero (B₀ (P := P))) normal_cross
          (hspan ha hb hd hncol) ⟨f, E f i⟩).1 pp := hu
    _ = (D₀ hred ha hb hd hncol).boundaryVertex
        ((D₀ hred ha hb hd hncol).across ⟨f, i⟩).1 p := by
      cases hfi
      rfl

/-- Reindexed concrete form of opposite-sector uniqueness at a double
corner. -/
theorem concreteData_opposite_across_face_unique_at_double_corner
    (d₁ : StrictFace (normals (B₀ (P := P))))
    (i₁ j₁ : Fin ((C₀ (P := P) ha hb hd hncol).faceDegree d₁))
    (hij₁ : i₁ ≠ j₁)
    (p₁ : Fin ((C₀ (P := P) ha hb hd hncol).faceDegree
      ((D₀ hred ha hb hd hncol).across ⟨d₁, i₁⟩).1))
    (q₁ : Fin ((C₀ (P := P) ha hb hd hncol).faceDegree
      ((D₀ hred ha hb hd hncol).across ⟨d₁, j₁⟩).1))
    (hpq₁ : (D₀ hred ha hb hd hncol).boundaryVertex
        ((D₀ hred ha hb hd hncol).across ⟨d₁, i₁⟩).1 p₁ =
      (D₀ hred ha hb hd hncol).boundaryVertex
        ((D₀ hred ha hb hd hncol).across ⟨d₁, j₁⟩).1 q₁)
    (d₂ : StrictFace (normals (B₀ (P := P))))
    (i₂ j₂ : Fin ((C₀ (P := P) ha hb hd hncol).faceDegree d₂))
    (hij₂ : i₂ ≠ j₂)
    (p₂ : Fin ((C₀ (P := P) ha hb hd hncol).faceDegree
      ((D₀ hred ha hb hd hncol).across ⟨d₂, i₂⟩).1))
    (q₂ : Fin ((C₀ (P := P) ha hb hd hncol).faceDegree
      ((D₀ hred ha hb hd hncol).across ⟨d₂, j₂⟩).1))
    (hpq₂ : (D₀ hred ha hb hd hncol).boundaryVertex
        ((D₀ hred ha hb hd hncol).across ⟨d₂, i₂⟩).1 p₂ =
      (D₀ hred ha hb hd hncol).boundaryVertex
        ((D₀ hred ha hb hd hncol).across ⟨d₂, j₂⟩).1 q₂)
    (hface : ((D₀ hred ha hb hd hncol).across ⟨d₁, i₁⟩).1 =
      ((D₀ hred ha hb hd hncol).across ⟨d₂, i₂⟩).1)
    (hcorner : (D₀ hred ha hb hd hncol).boundaryVertex
        ((D₀ hred ha hb hd hncol).across ⟨d₁, i₁⟩).1 p₁ =
      (D₀ hred ha hb hd hncol).boundaryVertex
        ((D₀ hred ha hb hd hncol).across ⟨d₂, i₂⟩).1 p₂)
    (hmult : lineMultiplicity (OnLine (B₀ (P := P)))
      ((D₀ hred ha hb hd hncol).boundaryVertex
        ((D₀ hred ha hb hd hncol).across ⟨d₁, i₁⟩).1 p₁).1 = 2) :
    ((D₀ hred ha hb hd hncol).across ⟨d₁, j₁⟩).1 =
      ((D₀ hred ha hb hd hncol).across ⟨d₂, j₂⟩).1 := by
  let E := indexEquiv (vertex_degree := vd₀ ha hb hd hncol)
    ha hb hd hncol
  have hmap (r : FaceDart (vertex_degree := vd₀ ha hb hd hncol)
      ha hb hd hncol) :
      dartEquiv (vertex_degree := vd₀ ha hb hd hncol) ha hb hd hncol
        ((D₀ hred ha hb hd hncol).across r) =
      PolarBoundaryAcross.across (normals (B₀ (P := P)))
        (normals_ne_zero (B₀ (P := P))) normal_cross
        (hspan ha hb hd hncol)
        (dartEquiv (vertex_degree := vd₀ ha hb hd hncol)
          ha hb hd hncol r) := by
    simp [D₀, concreteData, toData, ConcretePolarABKPRData.across]
  have hf₁ : ((D₀ hred ha hb hd hncol).across ⟨d₁, i₁⟩).1 =
      (PolarBoundaryAcross.across (normals (B₀ (P := P)))
        (normals_ne_zero (B₀ (P := P))) normal_cross
        (hspan ha hb hd hncol) ⟨d₁, E d₁ i₁⟩).1 :=
    congrArg Sigma.fst (hmap ⟨d₁, i₁⟩)
  have hx₁ : ((D₀ hred ha hb hd hncol).across ⟨d₁, j₁⟩).1 =
      (PolarBoundaryAcross.across (normals (B₀ (P := P)))
        (normals_ne_zero (B₀ (P := P))) normal_cross
        (hspan ha hb hd hncol) ⟨d₁, E d₁ j₁⟩).1 :=
    congrArg Sigma.fst (hmap ⟨d₁, j₁⟩)
  have hf₂ : ((D₀ hred ha hb hd hncol).across ⟨d₂, i₂⟩).1 =
      (PolarBoundaryAcross.across (normals (B₀ (P := P)))
        (normals_ne_zero (B₀ (P := P))) normal_cross
        (hspan ha hb hd hncol) ⟨d₂, E d₂ i₂⟩).1 :=
    congrArg Sigma.fst (hmap ⟨d₂, i₂⟩)
  have hx₂ : ((D₀ hred ha hb hd hncol).across ⟨d₂, j₂⟩).1 =
      (PolarBoundaryAcross.across (normals (B₀ (P := P)))
        (normals_ne_zero (B₀ (P := P))) normal_cross
        (hspan ha hb hd hncol) ⟨d₂, E d₂ j₂⟩).1 :=
    congrArg Sigma.fst (hmap ⟨d₂, j₂⟩)
  let pp₁ : BoundaryIndex (normals (B₀ (P := P)))
      (PolarBoundaryAcross.across (normals (B₀ (P := P)))
        (normals_ne_zero (B₀ (P := P))) normal_cross
        (hspan ha hb hd hncol) ⟨d₁, E d₁ i₁⟩).1 := hf₁ ▸ E _ p₁
  let qq₁ : BoundaryIndex (normals (B₀ (P := P)))
      (PolarBoundaryAcross.across (normals (B₀ (P := P)))
        (normals_ne_zero (B₀ (P := P))) normal_cross
        (hspan ha hb hd hncol) ⟨d₁, E d₁ j₁⟩).1 := hx₁ ▸ E _ q₁
  let pp₂ : BoundaryIndex (normals (B₀ (P := P)))
      (PolarBoundaryAcross.across (normals (B₀ (P := P)))
        (normals_ne_zero (B₀ (P := P))) normal_cross
        (hspan ha hb hd hncol) ⟨d₂, E d₂ i₂⟩).1 := hf₂ ▸ E _ p₂
  let qq₂ : BoundaryIndex (normals (B₀ (P := P)))
      (PolarBoundaryAcross.across (normals (B₀ (P := P)))
        (normals_ne_zero (B₀ (P := P))) normal_cross
        (hspan ha hb hd hncol) ⟨d₂, E d₂ j₂⟩).1 := hx₂ ▸ E _ q₂
  have hpq₁' : boundaryOrientedVertex (hspan ha hb hd hncol)
        (PolarBoundaryAcross.across (normals (B₀ (P := P)))
          (normals_ne_zero (B₀ (P := P))) normal_cross
          (hspan ha hb hd hncol) ⟨d₁, E d₁ i₁⟩).1 pp₁ =
      boundaryOrientedVertex (hspan ha hb hd hncol)
        (PolarBoundaryAcross.across (normals (B₀ (P := P)))
          (normals_ne_zero (B₀ (P := P))) normal_cross
          (hspan ha hb hd hncol) ⟨d₁, E d₁ j₁⟩).1 qq₁ := by
    cases hf₁
    cases hx₁
    exact hpq₁
  have hpq₂' : boundaryOrientedVertex (hspan ha hb hd hncol)
        (PolarBoundaryAcross.across (normals (B₀ (P := P)))
          (normals_ne_zero (B₀ (P := P))) normal_cross
          (hspan ha hb hd hncol) ⟨d₂, E d₂ i₂⟩).1 pp₂ =
      boundaryOrientedVertex (hspan ha hb hd hncol)
        (PolarBoundaryAcross.across (normals (B₀ (P := P)))
          (normals_ne_zero (B₀ (P := P))) normal_cross
          (hspan ha hb hd hncol) ⟨d₂, E d₂ j₂⟩).1 qq₂ := by
    cases hf₂
    cases hx₂
    exact hpq₂
  have hface' :
      (PolarBoundaryAcross.across (normals (B₀ (P := P)))
        (normals_ne_zero (B₀ (P := P))) normal_cross
        (hspan ha hb hd hncol) ⟨d₁, E d₁ i₁⟩).1 =
      (PolarBoundaryAcross.across (normals (B₀ (P := P)))
        (normals_ne_zero (B₀ (P := P))) normal_cross
        (hspan ha hb hd hncol) ⟨d₂, E d₂ i₂⟩).1 :=
    hf₁.symm.trans (hface.trans hf₂)
  have hcorner' : boundaryOrientedVertex (hspan ha hb hd hncol)
        (PolarBoundaryAcross.across (normals (B₀ (P := P)))
          (normals_ne_zero (B₀ (P := P))) normal_cross
          (hspan ha hb hd hncol) ⟨d₁, E d₁ i₁⟩).1 pp₁ =
      boundaryOrientedVertex (hspan ha hb hd hncol)
        (PolarBoundaryAcross.across (normals (B₀ (P := P)))
          (normals_ne_zero (B₀ (P := P))) normal_cross
          (hspan ha hb hd hncol) ⟨d₂, E d₂ i₂⟩).1 pp₂ := by
    cases hf₁
    cases hf₂
    exact hcorner
  have hmult' : lineMultiplicity (OnLine (B₀ (P := P)))
      (boundaryOrientedVertex (hspan ha hb hd hncol)
        (PolarBoundaryAcross.across (normals (B₀ (P := P)))
          (normals_ne_zero (B₀ (P := P))) normal_cross
          (hspan ha hb hd hncol) ⟨d₁, E d₁ i₁⟩).1 pp₁).1 = 2 := by
    cases hf₁
    exact hmult
  have hlit :=
    ConcreteDonationObstructionRecognition.opposite_across_face_unique_at_double_corner
      (hspan ha hb hd hncol) d₁ (E d₁ i₁) (E d₁ j₁)
      (fun h ↦ hij₁ ((E d₁).injective h)) pp₁ qq₁ hpq₁'
      d₂ (E d₂ i₂) (E d₂ j₂)
      (fun h ↦ hij₂ ((E d₂).injective h)) pp₂ qq₂ hpq₂'
      hface' hcorner' hmult'
  exact hx₁.trans (hlit.trans hx₂.symm)

end Erdos735.ConcretePolarABKPRData

namespace Erdos735.ConcreteDonationObstructionRecognition

open ProjectiveArrangement ProjectiveBoundaryExtraction SignVector ChartOrder
open ConcretePolarABKPRData

variable {P : Finset Point} {w : Point → ℝ} {c : ℝ}
variable (hred : IsReducedMagic P w c)
variable {a b d : Point}
variable (ha : a ∈ nonordinaryPoints P) (hb : b ∈ nonordinaryPoints P)
variable (hd : d ∈ nonordinaryPoints P)
variable (hncol : ¬ ProjectiveDuality.Collinear3 a b d)
variable [Nonempty (ProjectiveBoundaryExtraction.Line (nonordinaryPoints P))]

private abbrev B := nonordinaryPoints P
private abbrev C := ConcretePolarCellulation.blueCellulation
  (B (P := P)) ha hb hd hncol
private abbrev D := ConcretePolarABKPRData.concreteData hred ha hb hd hncol

omit [Nonempty (ProjectiveBoundaryExtraction.Line (nonordinaryPoints P))] in
/-- The edge and bad-neighbour witnesses in `DonationGeometry` present the
recipient and donor as opposite across two distinct edges of the same bad
quadrangle. -/
lemma exists_donation_sector_faces
    (f : StrictFace (normals (B (P := P))))
    (x : (D hred ha hb hd hncol).donationRecipients f) :
    ∃ (g : StrictFace (normals (B (P := P))))
      (i j : Fin ((C (P := P) ha hb hd hncol).faceDegree g)),
      i ≠ j ∧ (D hred ha hb hd hncol).IsBadTwoQuadrangle g ∧
      ((D hred ha hb hd hncol).across ⟨g, i⟩).1 = f ∧
      ((D hred ha hb hd hncol).across ⟨g, j⟩).1 = x.1 := by
  let A := D hred ha hb hd hncol
  let C₁ := C (P := P) ha hb hd hncol
  obtain ⟨ix, hix, ji, hedge⟩ := A.donationEdgeOfGeometry_spec f x
  let g := (A.across ⟨x.1, ix⟩).1
  let jj := (A.across ⟨x.1, ix⟩).2
  have hbad : A.IsBadTwoQuadrangle g := (Finset.mem_filter.mp hix).2
  have hgf : g ≠ f := by
    intro h
    have hfour : C₁.faceDegree g = 4 := hbad.1.1
    have hfive : 5 ≤ C₁.faceDegree g := by
      simpa [h] using A.donor_degree_five_le x.2
    omega
  have hgi : (A.across ⟨g, ji⟩).1 = f :=
    A.across_face_eq_of_boundaryEdge_eq hedge.symm (Ne.symm hgf)
  have hgjDart : A.across ⟨g, jj⟩ = ⟨x.1, ix⟩ := A.across_involutive ⟨x.1, ix⟩
  have hgj : (A.across ⟨g, jj⟩).1 = x.1 := congrArg Sigma.fst hgjDart
  have hij : ji ≠ jj := by
    intro h
    have hfaces : f = x.1 := hgi.symm.trans (by rw [h]; exact hgj)
    have hfive : 5 ≤ C₁.faceDegree f := A.donor_degree_five_le x.2
    have htri : C₁.faceDegree x.1 = 3 := (A.recipient_isBadTriangle x.2).1
    have hdegrees := congrArg C₁.faceDegree hfaces
    omega
  exact ⟨g, ji, jj, hij, hbad, hgi, hgj⟩

/-- A common corner of two different faces across a bad concrete
quadrangle has blue multiplicity two. -/
theorem common_across_corner_lineMultiplicity_eq_two_of_bad
    (g : StrictFace (normals (B (P := P))))
    (i j : Fin ((C (P := P) ha hb hd hncol).faceDegree g)) (hij : i ≠ j)
    (p : Fin ((C (P := P) ha hb hd hncol).faceDegree
      ((D hred ha hb hd hncol).across ⟨g, i⟩).1))
    (q : Fin ((C (P := P) ha hb hd hncol).faceDegree
      ((D hred ha hb hd hncol).across ⟨g, j⟩).1))
    (hpq : (D hred ha hb hd hncol).boundaryVertex
        ((D hred ha hb hd hncol).across ⟨g, i⟩).1 p =
      (D hred ha hb hd hncol).boundaryVertex
        ((D hred ha hb hd hncol).across ⟨g, j⟩).1 q)
    (hbad : (D hred ha hb hd hncol).IsBadTwoQuadrangle g) :
    lineMultiplicity (OnLine (B (P := P)))
      ((D hred ha hb hd hncol).boundaryVertex
        ((D hred ha hb hd hncol).across ⟨g, i⟩).1 p).1 = 2 := by
  let A := D hred ha hb hd hncol
  obtain ⟨u, hu⟩ :=
    ConcretePolarABKPRData.concreteData_exists_boundaryVertex_eq_common_across_corner
      hred ha hb hd hncol g i j hij p q hpq
  have hmultU : lineMultiplicity (OnLine (B (P := P)))
      (A.boundaryVertex g u).1 = 2 := by
    have h := A.badTwo_boundaryVertex_multiplicity_two hbad u
    simpa [A, D, C, ConcretePolarABKPRData.concreteData,
      ConcretePolarABKPRData.toData,
      ConcretePolarCellulation.blueCellulation,
      ConcretePolarCellulation.blueCellulationOfVertexDegree,
      ConcretePolarCellulation.boundaryExtractionOfVertexDegree,
      BoundaryExtraction.toBlueCellulation] using h
  rw [← hu]
  exact hmultU

/-- A proposition presenting a donation recipient as the sector opposite
its donor at a corner satisfying an arbitrary `cornerProperty`.  Its single
constructor carries the dependent local indices while still eliminating
directly into the proposition-valued obstruction proofs. -/
inductive DonationOppositeSector
    {Vertex : Type*} {Edge : Type*} {Face : Type*}
    [Fintype Vertex] [Fintype Edge] [Fintype Face]
    [DecidableEq Vertex] [DecidableEq Edge] [DecidableEq Face]
    {C₁ : BlueCellulation Vertex Edge Face}
    (A : ABKPR.Data C₁) (cornerProperty : Vertex → Prop)
    (f : Face) (x : A.donationRecipients f) : Prop
  | intro (g : Face) (i j : Fin (C₁.faceDegree g)) (distinct : i ≠ j)
      (p : Fin (C₁.faceDegree (A.across ⟨g, i⟩).1))
      (q : Fin (C₁.faceDegree (A.across ⟨g, j⟩).1))
      (common : A.boundaryVertex (A.across ⟨g, i⟩).1 p =
        A.boundaryVertex (A.across ⟨g, j⟩).1 q)
      (donor_face : (A.across ⟨g, i⟩).1 = f)
      (recipient_face : (A.across ⟨g, j⟩).1 = x.1)
      (donor_corner : A.boundaryVertex (A.across ⟨g, i⟩).1 p =
        A.boundaryVertex f (A.donationVertexOfGeometry f x))
      (corner_property : cornerProperty
        (A.boundaryVertex (A.across ⟨g, i⟩).1 p))

private theorem boundaryVertex_cast_generic
    {Vertex : Type*} {Edge : Type*} {Face : Type*}
    [Fintype Vertex] [Fintype Edge] [Fintype Face]
    [DecidableEq Vertex] [DecidableEq Edge] [DecidableEq Face]
    {C₁ : BlueCellulation Vertex Edge Face} (A : ABKPR.Data C₁)
    {r s : Face} (hrs : r = s) (k : Fin (C₁.faceDegree r)) :
    A.boundaryVertex s (Fin.cast (congrArg C₁.faceDegree hrs) k) =
      A.boundaryVertex r k := by
  subst s
  rfl

/-- Generic dependent-index transport of a selected donation corner to two
named across faces. -/
theorem exists_common_corner_of_donation_faces
    {Vertex : Type*} {Edge : Type*} {Face : Type*}
    [Fintype Vertex] [Fintype Edge] [Fintype Face]
    [DecidableEq Vertex] [DecidableEq Edge] [DecidableEq Face]
    {C₁ : BlueCellulation Vertex Edge Face} (A : ABKPR.Data C₁)
    (f : Face) (x : A.donationRecipients f) (g : Face)
    (i j : Fin (C₁.faceDegree g))
    (hi : (A.across ⟨g, i⟩).1 = f)
    (hj : (A.across ⟨g, j⟩).1 = x.1) :
    ∃ (p : Fin (C₁.faceDegree (A.across ⟨g, i⟩).1))
      (q : Fin (C₁.faceDegree (A.across ⟨g, j⟩).1)),
      A.boundaryVertex (A.across ⟨g, i⟩).1 p =
          A.boundaryVertex (A.across ⟨g, j⟩).1 q ∧
        A.boundaryVertex (A.across ⟨g, i⟩).1 p =
          A.boundaryVertex f (A.donationVertexOfGeometry f x) := by
  obtain ⟨vx, hvx⟩ := A.donationVertexOfGeometry_spec f x
  let p : Fin (C₁.faceDegree (A.across ⟨g, i⟩).1) :=
    Fin.cast (congrArg C₁.faceDegree hi).symm
      (A.donationVertexOfGeometry f x)
  let q : Fin (C₁.faceDegree (A.across ⟨g, j⟩).1) :=
    Fin.cast (congrArg C₁.faceDegree hj).symm vx
  have hp : A.boundaryVertex (A.across ⟨g, i⟩).1 p =
      A.boundaryVertex f (A.donationVertexOfGeometry f x) := by
    simpa [p, Fin.cast_eq_cast] using
      boundaryVertex_cast_generic A hi.symm (A.donationVertexOfGeometry f x)
  have hq : A.boundaryVertex x.1 vx =
      A.boundaryVertex (A.across ⟨g, j⟩).1 q := by
    simpa [q, Fin.cast_eq_cast] using
      (boundaryVertex_cast_generic A hj.symm vx).symm
  exact ⟨p, q, hp.trans (hvx.trans hq), hp⟩

/-- Construct the canonical opposite-sector package from the witnesses in
`DonationGeometry`. -/
theorem donationOppositeSector
    (f : StrictFace (normals (B (P := P))))
    (x : (D hred ha hb hd hncol).donationRecipients f) :
    DonationOppositeSector (D hred ha hb hd hncol)
      (fun v ↦ lineMultiplicity (OnLine (B (P := P))) v.1 = 2) f x := by
  let A := D hred ha hb hd hncol
  obtain ⟨g, ji, jj, hij, hbad, hgi, hgj⟩ :=
    exists_donation_sector_faces hred ha hb hd hncol f x
  obtain ⟨p, q, hpq, hcornerDonor⟩ :=
    exists_common_corner_of_donation_faces A f x g ji jj hgi hgj
  have hmult : lineMultiplicity (OnLine (B (P := P)))
      (A.boundaryVertex (A.across ⟨g, ji⟩).1 p).1 = 2 := by
    exact common_across_corner_lineMultiplicity_eq_two_of_bad
      hred ha hb hd hncol g ji jj hij p q hpq hbad
  exact .intro g ji jj hij p q hpq hgi hgj hcornerDonor hmult

/-- Two distinct donation recipients cannot select the same donor corner.
Each recipient is the unique sector opposite the donor at a double blue
corner. -/
theorem donationVertexOfGeometry_injective
    (f : StrictFace (normals (B (P := P)))) :
    Function.Injective ((D hred ha hb hd hncol).donationVertexOfGeometry f) := by
  intro x y hvertex
  let A := D hred ha hb hd hncol
  obtain ⟨gx, ix, jx, hijx, px, qx, hpqx, hfx, hxx, hcx, hmultx⟩ :=
    donationOppositeSector hred ha hb hd hncol f x
  obtain ⟨gy, iy, jy, hijy, py, qy, hpqy, hfy, hyy, hcy, -⟩ :=
    donationOppositeSector hred ha hb hd hncol f y
  have hface : (A.across ⟨gx, ix⟩).1 = (A.across ⟨gy, iy⟩).1 :=
    hfx.trans hfy.symm
  have hcorner : A.boundaryVertex (A.across ⟨gx, ix⟩).1 px =
      A.boundaryVertex (A.across ⟨gy, iy⟩).1 py :=
    hcx.trans ((congrArg (A.boundaryVertex f) hvertex).trans hcy.symm)
  have hopposite :=
    ConcretePolarABKPRData.concreteData_opposite_across_face_unique_at_double_corner
      hred ha hb hd hncol gx ix jx hijx px qx hpqx
      gy iy jy hijy py qy hpqy hface hcorner hmultx
  apply Subtype.ext
  exact hxx.symm.trans (hopposite.trans hyy)

end Erdos735.ConcreteDonationObstructionRecognition
