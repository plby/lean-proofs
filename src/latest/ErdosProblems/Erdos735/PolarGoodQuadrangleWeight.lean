/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos735.GoodQuadrangleWeight
import ErdosProblems.Erdos735.PolarRedChordExtraction
import ErdosProblems.Erdos735.ConcretePolarEdgeVertices

/-!
# The good-quadrangle weight obstruction on the literal polar boundary

This file states the local ABKPR quadrangle lemma directly in terms of the
owner-preserving polar boundary and the literal red-chord extraction.  It
does not pass through a rotation realization or require transport
compatibility equalities.
-/

open Classical
noncomputable section
open scoped BigOperators LinearAlgebra.Projectivization

namespace Erdos735.PolarGoodQuadrangleWeight

open ProjectiveArrangement ProjectiveBoundaryExtraction ChartOrder SignVector
open SignVector.PolarBoundaryAcross SignVector.PolarBoundaryOrder SignVector.PolarFace
open SignVector.PolarPlaneChart
open ConcretePolarOrientedVertex ConcretePolarEdgeVertices
open PolarRedChordExtraction RedChordExtraction

abbrev Point := ProjectiveArrangement.Point
abbrev BlueLine (P : Finset Point) := {b // b ∈ nonordinaryPoints P}
abbrev RedLine (P : Finset Point) := {a // a ∈ ordinaryPoints P}

variable {P : Finset Point} {w : Point → ℝ} {c : ℝ}
variable (hred : IsReducedMagic P w c)
variable [Nonempty (BlueLine P)]
variable (hspan : Submodule.span ℝ
  (Set.range (normals (nonordinaryPoints P))) = ⊤)

/-- The literal polar boundary corner packaged as a projective arrangement
vertex. -/
noncomputable def boundaryProjectiveVertex
    (f : StrictFace (normals (nonordinaryPoints P)))
    (i : BoundaryIndex (normals (nonordinaryPoints P)) f) :
    ProjectiveBoundaryExtraction.Vertex (nonordinaryPoints P) :=
  ⟨boundaryVertex (normals (nonordinaryPoints P)) normal_cross hspan f i,
    boundaryVertex_mem_projectiveVertices hspan f i⟩

/-- The primal blue point owning a literal polar boundary edge. -/
def boundaryBlueOwner
    (f : StrictFace (normals (nonordinaryPoints P)))
    (i : BoundaryIndex (normals (nonordinaryPoints P)) f) : BlueLine P :=
  (boundaryEdge (normals (nonordinaryPoints P)) normal_cross hspan f i).1.1

/-- Literal Step-1 corners: red endpoints at which exactly two blue dual
lines meet. -/
noncomputable def stage1Corners
    (f : StrictFace (normals (nonordinaryPoints P))) :
    Finset (BoundaryIndex (normals (nonordinaryPoints P)) f) :=
  (redEndpoints hred hspan f).filter fun i ↦
    lineMultiplicity (OnLine (nonordinaryPoints P))
      (boundaryProjectiveVertex hspan f i) = 2

@[simp] theorem mem_stage1Corners
    (f : StrictFace (normals (nonordinaryPoints P)))
    (i : BoundaryIndex (normals (nonordinaryPoints P)) f) :
    i ∈ stage1Corners hred hspan f ↔
      i ∈ redEndpoints hred hspan f ∧
        lineMultiplicity (OnLine (nonordinaryPoints P))
          (boundaryProjectiveVertex hspan f i) = 2 := by
  simp [stage1Corners]

/-- Four iterations of the literal cyclic successor traverse a
quadrangular polar boundary exactly once. -/
theorem cyclicSucc_four_cycle
    {n : ℕ} (hdeg : n = 4) (i₀ : Fin n) :
    let i₁ := Erdos957.cyclicSucc i₀
    let i₂ := Erdos957.cyclicSucc i₁
    let i₃ := Erdos957.cyclicSucc i₂
    i₀ ≠ i₁ ∧ i₁ ≠ i₂ ∧ i₂ ≠ i₃ ∧ i₃ ≠ i₀ ∧
      i₂ ≠ i₀ ∧ Erdos957.cyclicSucc i₃ = i₀ := by
  dsimp only
  have hsval (i : Fin n) : (Erdos957.cyclicSucc i).val = (i.val + 1) % 4 := by
    have hs : (Erdos957.cyclicSucc i).val = (i.val + 1) % n := by
      let _ : NeZero n := i.neZero
      change (finRotate n i).val = _
      rw [finRotate_apply, Fin.val_add, Fin.val_one']
      nth_rw 1 [← Nat.mod_eq_of_lt i.isLt]
      exact (Nat.add_mod i.val 1 n).symm
    simpa only [hdeg] using hs
  let i₁ := Erdos957.cyclicSucc i₀
  let i₂ := Erdos957.cyclicSucc i₁
  let i₃ := Erdos957.cyclicSucc i₂
  have hi₀lt : i₀.val < 4 := by simpa [hdeg] using i₀.isLt
  have hi₁lt : i₁.val < 4 := by simpa [hdeg] using i₁.isLt
  have hi₂lt : i₂.val < 4 := by simpa [hdeg] using i₂.isLt
  have hi₃lt : i₃.val < 4 := by simpa [hdeg] using i₃.isLt
  have hi₁val : i₁.val = (i₀.val + 1) % 4 := hsval i₀
  have hi₂val : i₂.val = (i₁.val + 1) % 4 := hsval i₁
  have hi₃val : i₃.val = (i₂.val + 1) % 4 := hsval i₂
  have hi₄val : (Erdos957.cyclicSucc i₃).val = (i₃.val + 1) % 4 := hsval i₃
  have h₀₁ : i₀ ≠ i₁ := by
    intro h
    have hv := congrArg Fin.val h
    omega
  have h₁₂ : i₁ ≠ i₂ := by
    intro h
    have hv := congrArg Fin.val h
    omega
  have h₂₃ : i₂ ≠ i₃ := by
    intro h
    have hv := congrArg Fin.val h
    omega
  have h₃₀ : i₃ ≠ i₀ := by
    intro h
    have hv := congrArg Fin.val h
    omega
  have h₂₀ : i₂ ≠ i₀ := by
    intro h
    have hv := congrArg Fin.val h
    omega
  have hcycle : Erdos957.cyclicSucc i₃ = i₀ := by
    apply Fin.ext
    omega
  exact ⟨h₀₁, h₁₂, h₂₃, h₃₀, h₂₀, hcycle⟩

/-- Every literal red endpoint retains an actual ordinary point incident
with the corresponding projective polar corner. -/
theorem exists_incident_red_of_mem_redEndpoints
    (f : StrictFace (normals (nonordinaryPoints P)))
    (i : BoundaryIndex (normals (nonordinaryPoints P)) f)
    (hi : i ∈ redEndpoints hred hspan f) :
    ∃ a : RedLine P,
      a ∈ redChordLines (A := ordinaryPoints P) f ∧
        Incident
          (boundaryVertex (normals (nonordinaryPoints P)) normal_cross hspan f i)
          a.1 := by
  obtain ⟨p, hp, hip⟩ := (mem_redEndpoints_iff hred hspan f i).mp hi
  obtain ⟨a, hpa⟩ := (mem_redChords_iff hred hspan f p).mp hp
  subst p
  have himem : i ∈ endpointIndices hspan f a.1 := by
    rw [chordPair_spec hred hspan f a |>.2]
    rcases hip with rfl | rfl <;> simp
  exact ⟨a.1, (mem_redChordLines_iff f a.1).mpr a.2,
    (Finset.mem_filter.mp himem).2⟩

/-- Literal-polar form of `ABKPR.Data.goodTwoQuadrangle_twoGoodCorners`.

All objects in the statement are the eventual concrete data fields:
`PolarBoundaryAcross` supplies the cyclic face indices and owners,
`PolarRedChordExtraction` supplies chords and endpoints, and the local
blue multiplicity is the genuine projective line multiplicity. -/
theorem goodTwoQuadrangle_twoGoodCorners
    (f : StrictFace (normals (nonordinaryPoints P)))
    (hdegree : Erdos957.hullVertexCount
      (boundaryPolygon (normals (nonordinaryPoints P)) f.1
        (faceWitness (normals (nonordinaryPoints P)) f)) = 4)
    (hchords : (redChords hred hspan f).card = 2)
    (hgood :
      (redEndpoints hred hspan f \ stage1Corners hred hspan f).Nonempty) :
    2 ≤ (redEndpoints hred hspan f \ stage1Corners hred hspan f).card := by
  by_contra hnot
  have hcardpos :
      0 < (redEndpoints hred hspan f \ stage1Corners hred hspan f).card :=
    Finset.card_pos.mpr hgood
  have hcardlt :
      (redEndpoints hred hspan f \ stage1Corners hred hspan f).card < 2 :=
    Nat.lt_of_not_ge hnot
  have hcard :
      (redEndpoints hred hspan f \ stage1Corners hred hspan f).card = 1 := by
    omega
  obtain ⟨i₀, hgood_eq⟩ := Finset.card_eq_one.mp hcard
  let i₁ := Erdos957.cyclicSucc i₀
  let i₂ := Erdos957.cyclicSucc i₁
  let i₃ := Erdos957.cyclicSucc i₂
  have hcyc : i₀ ≠ i₁ ∧ i₁ ≠ i₂ ∧ i₂ ≠ i₃ ∧ i₃ ≠ i₀ ∧
      i₂ ≠ i₀ ∧ Erdos957.cyclicSucc i₃ = i₀ := by
    simpa [i₁, i₂, i₃] using cyclicSucc_four_cycle hdegree i₀
  rcases hcyc with ⟨hi₀i₁, hi₁i₂, hi₂i₃, hi₃i₀, hi₂i₀, hcycle⟩

  have hend_univ : redEndpoints hred hspan f = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [redEndpoints_card hred hspan f, hchords]
    simpa only [Finset.card_univ, Fintype.card_fin, Nat.reduceMul] using hdegree.symm
  have hend (i : BoundaryIndex (normals (nonordinaryPoints P)) f) :
      i ∈ redEndpoints hred hspan f := by
    rw [hend_univ]
    exact Finset.mem_univ i
  have hstage_of_ne
      {i : BoundaryIndex (normals (nonordinaryPoints P)) f} (hi : i ≠ i₀) :
      i ∈ stage1Corners hred hspan f := by
    by_contra histage
    have himem : i ∈ redEndpoints hred hspan f \ stage1Corners hred hspan f :=
      Finset.mem_sdiff.mpr ⟨hend i, histage⟩
    rw [hgood_eq] at himem
    exact hi (Finset.mem_singleton.mp himem)
  have hi₁stage : i₁ ∈ stage1Corners hred hspan f :=
    hstage_of_ne hi₀i₁.symm
  have hi₂stage : i₂ ∈ stage1Corners hred hspan f :=
    hstage_of_ne hi₂i₀
  have hi₃stage : i₃ ∈ stage1Corners hred hspan f :=
    hstage_of_ne hi₃i₀
  have hi₀good :
      i₀ ∈ redEndpoints hred hspan f \ stage1Corners hred hspan f := by
    rw [hgood_eq]
    exact Finset.mem_singleton.mpr rfl
  have hi₀nostage : i₀ ∉ stage1Corners hred hspan f :=
    (Finset.mem_sdiff.mp hi₀good).2
  have hmult₁ : lineMultiplicity (OnLine (nonordinaryPoints P))
      (boundaryProjectiveVertex hspan f i₁) = 2 :=
    (mem_stage1Corners hred hspan f i₁).mp hi₁stage |>.2
  have hmult₂ : lineMultiplicity (OnLine (nonordinaryPoints P))
      (boundaryProjectiveVertex hspan f i₂) = 2 :=
    (mem_stage1Corners hred hspan f i₂).mp hi₂stage |>.2
  have hmult₃ : lineMultiplicity (OnLine (nonordinaryPoints P))
      (boundaryProjectiveVertex hspan f i₃) = 2 :=
    (mem_stage1Corners hred hspan f i₃).mp hi₃stage |>.2
  have hmult₀ne : lineMultiplicity (OnLine (nonordinaryPoints P))
      (boundaryProjectiveVertex hspan f i₀) ≠ 2 := by
    intro hmult
    apply hi₀nostage
    exact (mem_stage1Corners hred hspan f i₀).mpr ⟨hend i₀, hmult⟩
  have hmult₀ : 2 < lineMultiplicity (OnLine (nonordinaryPoints P))
      (boundaryProjectiveVertex hspan f i₀) := by
    have htwo := two_le_lineMultiplicity (nonordinaryPoints P)
      (boundaryProjectiveVertex hspan f i₀)
    omega

  have hredInc (i : BoundaryIndex (normals (nonordinaryPoints P)) f) :
      ∃ a : RedLine P,
        a ∈ redChordLines (A := ordinaryPoints P) f ∧
          RedBlueDualIncidence.vertexHomogeneous
              (boundaryProjectiveVertex hspan f i) ∈
            ProjectiveDuality.dualLine a.1 := by
    obtain ⟨a, ha, hainc⟩ := exists_incident_red_of_mem_redEndpoints
      hred hspan f i (hend i)
    refine ⟨a, ha, ?_⟩
    apply (RedBlueDualIncidence.incident_iff_vertexHomogeneous_mem_dualLine
      (boundaryProjectiveVertex hspan f i) a.1).mp
    simpa [boundaryProjectiveVertex] using hainc
  obtain ⟨a₀, ha₀chord, ha₀inc⟩ := hredInc i₀
  obtain ⟨a₁, ha₁chord, ha₁inc⟩ := hredInc i₁
  obtain ⟨a₂, ha₂chord, ha₂inc⟩ := hredInc i₂
  obtain ⟨a₃, ha₃chord, ha₃inc⟩ := hredInc i₃

  let b₀ : BlueLine P := boundaryBlueOwner hspan f i₀
  let b₁ : BlueLine P := boundaryBlueOwner hspan f i₁
  let b₂ : BlueLine P := boundaryBlueOwner hspan f i₂
  let b₃ : BlueLine P := boundaryBlueOwner hspan f i₃
  have howner_inj : Function.Injective (boundaryBlueOwner hspan f) := by
    intro i j hij
    let E := boundaryOwnerEquiv f (faceWitness_realizes _ f)
      normal_cross hspan
    have hownerval : (E i).1 = (E j).1 := by
      simpa only [E, boundaryBlueOwner, PolarBoundaryAcross.boundaryEdge,
        PolarBoundaryOrder.boundaryEdge, edgeOfOwner_owner] using hij
    exact E.injective (Subtype.ext hownerval)
  have hb₀b₁ : b₀ ≠ b₁ := fun h ↦ hi₀i₁ (howner_inj h)
  have hb₁b₂ : b₁ ≠ b₂ := fun h ↦ hi₁i₂ (howner_inj h)
  have hb₂b₃ : b₂ ≠ b₃ := fun h ↦ hi₂i₃ (howner_inj h)
  have hb₃b₀ : b₃ ≠ b₀ := fun h ↦ hi₃i₀ (howner_inj h)

  have owner_start (i : BoundaryIndex (normals (nonordinaryPoints P)) f) :
      OnLine (nonordinaryPoints P) (boundaryProjectiveVertex hspan f i)
        (boundaryBlueOwner hspan f i) := by
    change Incident
      (boundaryVertex (normals (nonordinaryPoints P)) normal_cross hspan f i)
      (boundaryBlueOwner hspan f i).1
    simpa [Incident, boundaryBlueOwner, normals] using
      (boundaryVertex_on_edge_start (normals (nonordinaryPoints P))
        normal_cross hspan f i)
  have owner_finish (i : BoundaryIndex (normals (nonordinaryPoints P)) f) :
      OnLine (nonordinaryPoints P)
        (boundaryProjectiveVertex hspan f (Erdos957.cyclicSucc i))
        (boundaryBlueOwner hspan f i) := by
    change Incident
      (boundaryVertex (normals (nonordinaryPoints P)) normal_cross hspan f
        (Erdos957.cyclicSucc i))
      (boundaryBlueOwner hspan f i).1
    simpa [Incident, boundaryBlueOwner, normals] using
      (boundaryVertex_on_edge_finish (normals (nonordinaryPoints P))
        normal_cross hspan f i)
  have hb₀i₁ : OnLine (nonordinaryPoints P)
      (boundaryProjectiveVertex hspan f i₁) b₀ := by
    simpa [b₀, i₁] using owner_finish i₀
  have hb₁i₁ : OnLine (nonordinaryPoints P)
      (boundaryProjectiveVertex hspan f i₁) b₁ := by
    simpa [b₁] using owner_start i₁
  have hb₁i₂ : OnLine (nonordinaryPoints P)
      (boundaryProjectiveVertex hspan f i₂) b₁ := by
    simpa [b₁, i₂] using owner_finish i₁
  have hb₂i₂ : OnLine (nonordinaryPoints P)
      (boundaryProjectiveVertex hspan f i₂) b₂ := by
    simpa [b₂] using owner_start i₂
  have hb₂i₃ : OnLine (nonordinaryPoints P)
      (boundaryProjectiveVertex hspan f i₃) b₂ := by
    simpa [b₂, i₃] using owner_finish i₂
  have hb₃i₃ : OnLine (nonordinaryPoints P)
      (boundaryProjectiveVertex hspan f i₃) b₃ := by
    simpa [b₃] using owner_start i₃
  have hb₃i₀ : OnLine (nonordinaryPoints P)
      (boundaryProjectiveVertex hspan f i₀) b₃ := by
    rw [← hcycle]
    simpa [b₃] using owner_finish i₃
  have hb₀i₀ : OnLine (nonordinaryPoints P)
      (boundaryProjectiveVertex hspan f i₀) b₀ := by
    simpa [b₀] using owner_start i₀

  have heq₀₁ :=
    RedBlueDualIncidence.normalized_pair_weight_eq_half_of_multiplicity_two
      hred (boundaryProjectiveVertex hspan f i₁) a₁.2 ha₁inc
      b₀ b₁ hb₀b₁ hb₀i₁ hb₁i₁ hmult₁
  have heq₁₂ :=
    RedBlueDualIncidence.normalized_pair_weight_eq_half_of_multiplicity_two
      hred (boundaryProjectiveVertex hspan f i₂) a₂.2 ha₂inc
      b₁ b₂ hb₁b₂ hb₁i₂ hb₂i₂ hmult₂
  have heq₂₃ :=
    RedBlueDualIncidence.normalized_pair_weight_eq_half_of_multiplicity_two
      hred (boundaryProjectiveVertex hspan f i₃) a₃.2 ha₃inc
      b₂ b₃ hb₂b₃ hb₂i₃ hb₃i₃ hmult₃
  have hextraPos := RedBlueDualIncidence.sum_extraBlueIncidentPoints_pos
    hred (boundaryProjectiveVertex hspan f i₀)
      b₃ b₀ hb₃b₀ hb₃i₀ hb₀i₀ hmult₀
  have hextraNorm : 0 <
      (∑ x ∈ RedBlueDualIncidence.extraBlueIncidentPoints
        (boundaryProjectiveVertex hspan f i₀) b₃ b₀, w x) / c :=
    div_pos hextraPos hred.1
  have heq₃₀ := RedBlueDualIncidence.normalized_pair_add_extra_weight_eq_half
    hred (boundaryProjectiveVertex hspan f i₀) a₀.2 ha₀inc
      b₃ b₀ hb₃b₀ hb₃i₀ hb₀i₀
  exact ABKPR.uniqueGoodQuadrangle_weightContradiction
    ((∑ x ∈ RedBlueDualIncidence.extraBlueIncidentPoints
      (boundaryProjectiveVertex hspan f i₀) b₃ b₀, w x) / c)
    (w b₀.1 / c) (w b₁.1 / c) (w b₂.1 / c) (w b₃.1 / c)
    hextraNorm heq₀₁ heq₁₂ heq₂₃ heq₃₀

/-- Constructor-facing version whose degree hypothesis is the length of the
literal polar face-boundary list.  This is the form definitionally produced
by `ConcretePolarCellulation.blueCellulationOfVertexDegree`. -/
theorem goodTwoQuadrangle_twoGoodCorners_of_faceBoundary_length
    (f : StrictFace (normals (nonordinaryPoints P)))
    (hdegree :
      (PolarBoundaryAcross.faceBoundary (normals (nonordinaryPoints P))
        normal_cross hspan f).length = 4)
    (hchords : (redChords hred hspan f).card = 2)
    (hgood :
      (redEndpoints hred hspan f \ stage1Corners hred hspan f).Nonempty) :
    2 ≤ (redEndpoints hred hspan f \ stage1Corners hred hspan f).card := by
  apply goodTwoQuadrangle_twoGoodCorners hred hspan f
  · simpa [PolarBoundaryAcross.faceBoundary] using hdegree
  · exact hchords
  · exact hgood

/-- An equivalence transports a finite set difference exactly. -/
theorem map_sdiff_equiv
    {J K : Type*} [DecidableEq J] [DecidableEq K]
    (e : J ≃ K) (s t : Finset J) :
    (s \ t).map e.toEmbedding =
      s.map e.toEmbedding \ t.map e.toEmbedding := by
  ext y
  simp only [Finset.mem_map, Finset.mem_sdiff]
  constructor
  · rintro ⟨x, ⟨hxs, hxt⟩, rfl⟩
    refine ⟨⟨x, hxs, rfl⟩, ?_⟩
    rintro ⟨z, hzt, hzx⟩
    have hzx' : z = x := e.injective hzx
    subst z
    exact hxt hzt
  · rintro ⟨⟨x, hxs, hxy⟩, hnot⟩
    subst y
    refine ⟨x, ⟨hxs, ?_⟩, rfl⟩
    intro hxt
    exact hnot ⟨x, hxt, rfl⟩

/-- Equivalence-transport adapter for the reindexed concrete polar
`ABKPR.Data`.  Its only compatibility inputs are the chord-card identity and
the two literal `Finset.map` identities for endpoints and Step-1 corners. -/
theorem goodTwoQuadrangle_twoGoodCorners_of_indexEquiv
    {J : Type*} [DecidableEq J]
    (f : StrictFace (normals (nonordinaryPoints P)))
    (e : J ≃ BoundaryIndex (normals (nonordinaryPoints P)) f)
    (indexedChords : Finset (J × J))
    (indexedEndpoints indexedStage1 : Finset J)
    (hchordCard : indexedChords.card = (redChords hred hspan f).card)
    (hendpointMap : indexedEndpoints.map e.toEmbedding =
      redEndpoints hred hspan f)
    (hstage1Map : indexedStage1.map e.toEmbedding =
      stage1Corners hred hspan f)
    (hdegree :
      (PolarBoundaryAcross.faceBoundary (normals (nonordinaryPoints P))
        normal_cross hspan f).length = 4)
    (hchords : indexedChords.card = 2)
    (hgood : (indexedEndpoints \ indexedStage1).Nonempty) :
    2 ≤ (indexedEndpoints \ indexedStage1).card := by
  have hgoodMap :
      (indexedEndpoints \ indexedStage1).map e.toEmbedding =
        redEndpoints hred hspan f \ stage1Corners hred hspan f := by
    rw [map_sdiff_equiv, hendpointMap, hstage1Map]
  have hliteralChords : (redChords hred hspan f).card = 2 := by
    omega
  have hliteralGood :
      (redEndpoints hred hspan f \ stage1Corners hred hspan f).Nonempty := by
    obtain ⟨i, hi⟩ := hgood
    refine ⟨e i, ?_⟩
    rw [← hgoodMap]
    exact Finset.mem_map.mpr ⟨i, hi, rfl⟩
  have hliteral := goodTwoQuadrangle_twoGoodCorners_of_faceBoundary_length
    hred hspan f hdegree hliteralChords hliteralGood
  have hgoodCard := congrArg Finset.card hgoodMap
  rw [Finset.card_map] at hgoodCard
  omega

end Erdos735.PolarGoodQuadrangleWeight
