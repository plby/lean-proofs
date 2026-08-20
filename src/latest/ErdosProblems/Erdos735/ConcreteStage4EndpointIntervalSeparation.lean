/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos735.ConcreteStage4EndpointSlots
import ErdosProblems.Erdos735.ConcreteStage4BeltNoncollision
import ErdosProblems.Erdos735.ConcreteStage4EndpointBeltClosure

open Classical
noncomputable section

namespace Erdos735.ConcreteStage4EndpointIntervalSeparation

open ProjectiveArrangement ProjectiveBoundaryExtraction
open ChartOrder SignVector SignVectorArrangement
open SignVector.ProjectiveEdgeEndpointEquiv

abbrev Point := ProjectiveArrangement.Point

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
private abbrev Line := ProjectiveBoundaryExtraction.Line (B (P := P))

/-- Evil faces linked through one geometric helper lie on the same side of
their common path owner. -/
theorem evil_sign_eq_of_evilLinked
    (L : (D hred ha hb hd hncol).FlankSystem (Line (P := P)))
    (hedge : L.edgeLine = ConcretePolarFlankBounds.edgeLine)
    {e₀ e₁ : (D hred ha hb hd hncol).EvilFace}
    (hlink : ABKPR.Data.EvilLinked L e₀ e₁) :
    let p := L.edgeLine ((D hred ha hb hd hncol).boundaryEdge
      e₀.1 ((D hred ha hb hd hncol).evilIndex e₀))
    e₀.1.1 p = e₁.1.1 p := by
  let DD := D hred ha hb hd hncol
  let CC := C ha hb hd hncol
  let p := L.edgeLine (DD.boundaryEdge e₀.1 (DD.evilIndex e₀))
  have hp₁ : L.edgeLine (DD.boundaryEdge e₁.1 (DD.evilIndex e₁)) = p :=
    (ABKPR.Data.badEdgeLine_eq_of_evilLinked L hlink).symm
  obtain ⟨h, he₀h, he₁h⟩ := hlink
  have one_side (e : DD.EvilFace) (heh : L.Adj e h)
      (hp : L.edgeLine (DD.boundaryEdge e.1 (DD.evilIndex e)) = p) :
      h.face.1 p = !(e.1.1 p) := by
    obtain ⟨side, hside⟩ := heh
    obtain ⟨⟨j, hadj, hface⟩, _howner⟩ :=
      L.evilFlank_geometric e side h hside
    let bad := DD.across (DD.evilDart e)
    have hbadPath : ConcretePolarFlankBounds.edgeLine
        (DD.boundaryEdge bad.1 bad.2) = p := by
      calc
        ConcretePolarFlankBounds.edgeLine (DD.boundaryEdge bad.1 bad.2) =
            ConcretePolarFlankBounds.edgeLine
              (DD.boundaryEdge e.1 (DD.evilIndex e)) :=
          congrArg ConcretePolarFlankBounds.edgeLine
            (DD.across_sameEdge (DD.evilDart e)).symm
        _ = L.edgeLine (DD.boundaryEdge e.1 (DD.evilIndex e)) := by
          rw [hedge]
        _ = p := hp
    have hsepPath : ConcretePolarFlankBounds.edgeLine
        (DD.boundaryEdge bad.1 j) ≠ p := by
      rw [← hbadPath]
      exact Function.Injective.ne
        (ConcretePolarFlankBounds.data_boundary_edgeLine_injective
          hred ha hb hd hncol bad.1)
        (ABKPR.ne_of_cyclicAdjacent_of_faceDegree_eq_four
          CC (DD.evilDart_across_bad e).1.1 bad.2 j hadj).symm
    have hbadSign : bad.1.1 p = !(e.1.1 p) := by
      have hx := ConcretePolarABKPRData.concreteData_across_face_sign
        hred ha hb hd hncol e.1 (DD.evilIndex e) p
      change bad.1.1 p = if p =
        ConcretePolarFlankBounds.edgeLine
          (DD.boundaryEdge e.1 (DD.evilIndex e))
        then !(e.1.1 p) else e.1.1 p at hx
      have hpConcrete : p = ConcretePolarFlankBounds.edgeLine
          (DD.boundaryEdge e.1 (DD.evilIndex e)) := by
        rw [← hedge]
        exact hp.symm
      simpa [hpConcrete] using hx
    have hhelpSign : h.face.1 p = bad.1.1 p := by
      have hx := ConcretePolarABKPRData.concreteData_across_face_sign
        hred ha hb hd hncol bad.1 j p
      change (DD.across ⟨bad.1, j⟩).1.1 p =
        if p = ConcretePolarFlankBounds.edgeLine
          (DD.boundaryEdge bad.1 j)
        then !(bad.1.1 p) else bad.1.1 p at hx
      rw [hface] at hx
      simpa [Ne.symm hsepPath] using hx
    exact hhelpSign.trans hbadSign
  have hp₀ : L.edgeLine (DD.boundaryEdge e₀.1 (DD.evilIndex e₀)) = p := rfl
  have h₀ := one_side e₀ he₀h hp₀
  have h₁ := one_side e₁ he₁h hp₁
  change e₀.1.1 p = e₁.1.1 p
  apply Bool.not_injective
  exact h₀.symm.trans h₁

/-- The path-side sign is invariant along a finite alternating chain. -/
theorem evil_sign_eq_of_reflTransGen_evilLinked
    (L : (D hred ha hb hd hncol).FlankSystem (Line (P := P)))
    (hedge : L.edgeLine = ConcretePolarFlankBounds.edgeLine)
    {e₀ e₁ : (D hred ha hb hd hncol).EvilFace}
    (hpath : Relation.ReflTransGen (ABKPR.Data.EvilLinked L) e₀ e₁) :
    let p := L.edgeLine ((D hred ha hb hd hncol).boundaryEdge
      e₀.1 ((D hred ha hb hd hncol).evilIndex e₀))
    e₀.1.1 p = e₁.1.1 p := by
  let DD := D hred ha hb hd hncol
  let p := L.edgeLine (DD.boundaryEdge e₀.1 (DD.evilIndex e₀))
  change e₀.1.1 p = e₁.1.1 p
  induction hpath with
  | refl => rfl
  | @tail e₂ e₃ hprefix hstep ih =>
      have hp : L.edgeLine (DD.boundaryEdge e₂.1 (DD.evilIndex e₂)) = p :=
        (ABKPR.Data.badEdgeLine_eq_of_reflTransGen_evilLinked L hprefix).symm
      have hs := evil_sign_eq_of_evilLinked
        hred ha hb hd hncol L hedge hstep
      change e₂.1.1
          (L.edgeLine (DD.boundaryEdge e₂.1 (DD.evilIndex e₂))) =
        e₃.1.1
          (L.edgeLine (DD.boundaryEdge e₂.1 (DD.evilIndex e₂))) at hs
      rw [hp] at hs
      exact ih.trans hs

private abbrev L
    (hAcard : 3 ≤ (ordinaryPoints P).card)
    (hnotFF : ¬ IsFailedFano P) :=
  ConcreteStage4FlankComplete.flankSystem
    hred ha hb hd hncol hAcard hnotFF

private abbrev G
    (hAcard : 3 ≤ (ordinaryPoints P).card)
    (hnotFF : ¬ IsFailedFano P) :=
  (L hred ha hb hd hncol hAcard hnotFF).toHelpingGraph

private abbrev component
    (hAcard : 3 ≤ (ordinaryPoints P).card)
    (hnotFF : ¬ IsFailedFano P)
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath) :=
  (G hred ha hb hd hncol hAcard hnotFF).deficientPathComponent hHall

/-- The two endpoint evils of the canonical deficient component have the
same sign on their common path owner. -/
theorem endpointEvils_path_sign_eq
    (hAcard : 3 ≤ (ordinaryPoints P).card)
    (hnotFF : ¬ IsFailedFano P)
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath) :
    let LL := L hred ha hb hd hncol hAcard hnotFF
    let H := component hred ha hb hd hncol hAcard hnotFF hHall
    let p := LL.edgeLine ((D hred ha hb hd hncol).boundaryEdge
      (H.endpoint 0).1 ((D hred ha hb hd hncol).evilIndex (H.endpoint 0)))
    (H.endpoint 0).1.1 p = (H.endpoint 1).1.1 p := by
  let LL := L hred ha hb hd hncol hAcard hnotFF
  let GG := G hred ha hb hd hncol hAcard hnotFF
  let H := component hred ha hb hd hncol hAcard hnotFF hHall
  have hp := H.evils_reachable_from_first (H.endpoint 1) (H.endpoint_mem 1)
  have hp' : Relation.ReflTransGen (ABKPR.Data.EvilLinked LL)
      (H.endpoint 0) (H.endpoint 1) := by
    refine Relation.ReflTransGen.mono
      (r := GG.LinkedEvil) (p := ABKPR.Data.EvilLinked LL) ?_
        (H.endpoint 0) (H.endpoint 1) hp
    intro x y hs
    exact (ABKPR.Data.linkedEvil_iff_evilLinked
      (D hred ha hb hd hncol) LL x y).mp hs
  exact evil_sign_eq_of_reflTransGen_evilLinked
    hred ha hb hd hncol LL
      (ConcreteStage4FlankComplete.flankSystem_edgeLine
        hred ha hb hd hncol hAcard hnotFF) hp'

/-- A continuation triangle is on the bad-quadrangle side of the common
path owner, hence has the negated path sign of its endpoint evil. -/
theorem endpointTriangle_path_sign_eq_not_evil
    (hAcard : 3 ≤ (ordinaryPoints P).card)
    (hnotFF : ¬ IsFailedFano P)
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath)
    (k : Fin 2) :
    let LL := L hred ha hb hd hncol hAcard hnotFF
    let H := component hred ha hb hd hncol hAcard hnotFF hHall
    let p := LL.edgeLine ((D hred ha hb hd hncol).boundaryEdge
      (H.endpoint 0).1 ((D hred ha hb hd hncol).evilIndex (H.endpoint 0)))
    (ConcreteStage4ContinuationEndpoints.endpointTriangle
        hred ha hb hd hncol hAcard hnotFF hHall k).1 p =
      !((H.endpoint k).1.1 p) := by
  let DD := D hred ha hb hd hncol
  let CC := C ha hb hd hncol
  let LL := L hred ha hb hd hncol hAcard hnotFF
  let H := component hred ha hb hd hncol hAcard hnotFF hHall
  let e := H.endpoint k
  let p := LL.edgeLine (DD.boundaryEdge (H.endpoint 0).1
    (DD.evilIndex (H.endpoint 0)))
  let bad := DD.across (DD.evilDart e)
  let j := ConcreteStage4ContinuationEndpoints.endpointIndex
    hred ha hb hd hncol hAcard hnotFF hHall k
  let q := ConcreteStage4ContinuationEndpoints.endpointTriangle
    hred ha hb hd hncol hAcard hnotFF hHall k
  have hp : LL.edgeLine (DD.boundaryEdge e.1 (DD.evilIndex e)) = p :=
    (ABKPR.Data.deficientPath_endpoints_badEdgeLine_eq
      DD LL hHall k).symm
  have hpConcrete : p = ConcretePolarFlankBounds.edgeLine
      (DD.boundaryEdge e.1 (DD.evilIndex e)) := by
    rw [← ConcreteStage4FlankComplete.flankSystem_edgeLine
      hred ha hb hd hncol hAcard hnotFF]
    exact hp.symm
  have hbadSign : bad.1.1 p = !(e.1.1 p) := by
    have hx := ConcretePolarABKPRData.concreteData_across_face_sign
      hred ha hb hd hncol e.1 (DD.evilIndex e) p
    change bad.1.1 p = if p =
      ConcretePolarFlankBounds.edgeLine
        (DD.boundaryEdge e.1 (DD.evilIndex e))
      then !(e.1.1 p) else e.1.1 p at hx
    simpa [hpConcrete] using hx
  have hsepPath : ConcretePolarFlankBounds.edgeLine
      (DD.boundaryEdge bad.1 j) ≠ p := by
    have hbadPath : ConcretePolarFlankBounds.edgeLine
        (DD.boundaryEdge bad.1 bad.2) = p := by
      calc
        ConcretePolarFlankBounds.edgeLine (DD.boundaryEdge bad.1 bad.2) =
            ConcretePolarFlankBounds.edgeLine
              (DD.boundaryEdge e.1 (DD.evilIndex e)) :=
          congrArg ConcretePolarFlankBounds.edgeLine
            (DD.across_sameEdge (DD.evilDart e)).symm
        _ = p := hpConcrete.symm
    rw [← hbadPath]
    exact Function.Injective.ne
      (ConcretePolarFlankBounds.data_boundary_edgeLine_injective
        hred ha hb hd hncol bad.1)
      (ABKPR.ne_of_cyclicAdjacent_of_faceDegree_eq_four
        CC (DD.evilDart_across_bad e).1.1 bad.2 j
        (ConcreteStage4ContinuationEndpoints.endpointIndex_adjacent
          hred ha hb hd hncol hAcard hnotFF hHall k)).symm
  have hqSign : q.1 p = bad.1.1 p := by
    have hx := ConcretePolarABKPRData.concreteData_across_face_sign
      hred ha hb hd hncol bad.1 j p
    change q.1 p = if p = ConcretePolarFlankBounds.edgeLine
      (DD.boundaryEdge bad.1 j) then !(bad.1.1 p) else bad.1.1 p at hx
    simpa [Ne.symm hsepPath] using hx
  exact hqSign.trans hbadSign

/-- In particular, the endpoint continuation triangles have the same sign
on the common path owner. -/
theorem endpointTriangles_path_sign_eq
    (hAcard : 3 ≤ (ordinaryPoints P).card)
    (hnotFF : ¬ IsFailedFano P)
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath) :
    let LL := L hred ha hb hd hncol hAcard hnotFF
    let H := component hred ha hb hd hncol hAcard hnotFF hHall
    let p := LL.edgeLine ((D hred ha hb hd hncol).boundaryEdge
      (H.endpoint 0).1 ((D hred ha hb hd hncol).evilIndex (H.endpoint 0)))
    (ConcreteStage4ContinuationEndpoints.endpointTriangle
        hred ha hb hd hncol hAcard hnotFF hHall 0).1 p =
      (ConcreteStage4ContinuationEndpoints.endpointTriangle
        hred ha hb hd hncol hAcard hnotFF hHall 1).1 p := by
  let LL := L hred ha hb hd hncol hAcard hnotFF
  let H := component hred ha hb hd hncol hAcard hnotFF hHall
  let p := LL.edgeLine ((D hred ha hb hd hncol).boundaryEdge
    (H.endpoint 0).1 ((D hred ha hb hd hncol).evilIndex (H.endpoint 0)))
  have h₀ := endpointTriangle_path_sign_eq_not_evil
    hred ha hb hd hncol hAcard hnotFF hHall 0
  have h₁ := endpointTriangle_path_sign_eq_not_evil
    hred ha hb hd hncol hAcard hnotFF hHall 1
  have he := endpointEvils_path_sign_eq
    hred ha hb hd hncol hAcard hnotFF hHall
  exact h₀.trans ((congrArg (fun x : Bool ↦ !x) he).trans h₁.symm)

/-- The two endpoint continuations cannot be antipodal: the entire
alternating component stays on one side of its path owner. -/
theorem endpointTriangles_not_antipodal
    (hAcard : 3 ≤ (ordinaryPoints P).card)
    (hnotFF : ¬ IsFailedFano P)
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath) :
    antipodalStrictFace
        (ConcreteStage4ContinuationEndpoints.endpointTriangle
          hred ha hb hd hncol hAcard hnotFF hHall 0) ≠
      ConcreteStage4ContinuationEndpoints.endpointTriangle
        hred ha hb hd hncol hAcard hnotFF hHall 1 := by
  let LL := L hred ha hb hd hncol hAcard hnotFF
  let H := component hred ha hb hd hncol hAcard hnotFF hHall
  let p := LL.edgeLine ((D hred ha hb hd hncol).boundaryEdge
    (H.endpoint 0).1 ((D hred ha hb hd hncol).evilIndex (H.endpoint 0)))
  let q₀ := ConcreteStage4ContinuationEndpoints.endpointTriangle
    hred ha hb hd hncol hAcard hnotFF hHall 0
  let q₁ := ConcreteStage4ContinuationEndpoints.endpointTriangle
    hred ha hb hd hncol hAcard hnotFF hHall 1
  intro hanti
  have hsame : q₀.1 p = q₁.1 p := endpointTriangles_path_sign_eq
    hred ha hb hd hncol hAcard hnotFF hHall
  have hflip : Bool.not (q₀.1 p) = q₁.1 p := by
    have hx := congrArg (fun q : StrictFace (normals (B (P := P))) ↦ q.1 p) hanti
    simpa only [antipodalStrictFace_sign, antipodalSign] using hx
  cases hs : q₀.1 p <;> simp_all

private theorem boundaryEdge_mem_faceEdges
    (q : StrictFace (normals (B (P := P))))
    (i : Fin ((C ha hb hd hncol).faceDegree q)) :
    (D hred ha hb hd hncol).boundaryEdge q i ∈
      faceEdges (normals (B (P := P))) q := by
  rw [← (ConcretePolarCellulation.boundaryExtraction
    (B (P := P)) ha hb hd hncol).faceBoundary_toFinset]
  exact List.mem_toFinset.mpr
    ((D hred ha hb hd hncol).boundaryEdge_mem q i)

/-- The two endpoint continuation faces are distinct.  If they were the
same triangle, its path and opposite-owner edges would agree at the two
ends, forcing the remaining separator edge, then the adjacent bad
quadrangle and finally the endpoint evil itself, to agree. -/
theorem endpointTriangles_ne
    (hAcard : 3 ≤ (ordinaryPoints P).card)
    (hnotFF : ¬ IsFailedFano P)
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath) :
    ConcreteStage4ContinuationEndpoints.endpointTriangle
        hred ha hb hd hncol hAcard hnotFF hHall 0 ≠
      ConcreteStage4ContinuationEndpoints.endpointTriangle
        hred ha hb hd hncol hAcard hnotFF hHall 1 := by
  let DD := D hred ha hb hd hncol
  let CC := C ha hb hd hncol
  let LL := L hred ha hb hd hncol hAcard hnotFF
  let H := component hred ha hb hd hncol hAcard hnotFF hHall
  let e₀ := H.endpoint 0
  let e₁ := H.endpoint 1
  let bad₀ := DD.across (DD.evilDart e₀)
  let bad₁ := DD.across (DD.evilDart e₁)
  let j₀ := ConcreteStage4ContinuationEndpoints.endpointIndex
    hred ha hb hd hncol hAcard hnotFF hHall 0
  let j₁ := ConcreteStage4ContinuationEndpoints.endpointIndex
    hred ha hb hd hncol hAcard hnotFF hHall 1
  let flank₀ := DD.across ⟨bad₀.1, j₀⟩
  let flank₁ := DD.across ⟨bad₁.1, j₁⟩
  let u₀ := ConcreteStage4BeltStep.triangleFlankOppositeIndex
    hred ha hb hd hncol LL
    (ConcreteStage4FlankComplete.flankSystem_edgeLine
      hred ha hb hd hncol hAcard hnotFF)
    e₀ j₀
    (ConcreteStage4ContinuationEndpoints.endpointIndex_adjacent
      hred ha hb hd hncol hAcard hnotFF hHall 0)
    (ConcreteStage4ContinuationEndpoints.endpointTriangle_faceDegree_three
      hred ha hb hd hncol hAcard hnotFF hHall 0)
  let u₁ := ConcreteStage4BeltStep.triangleFlankOppositeIndex
    hred ha hb hd hncol LL
    (ConcreteStage4FlankComplete.flankSystem_edgeLine
      hred ha hb hd hncol hAcard hnotFF)
    e₁ j₁
    (ConcreteStage4ContinuationEndpoints.endpointIndex_adjacent
      hred ha hb hd hncol hAcard hnotFF hHall 1)
    (ConcreteStage4ContinuationEndpoints.endpointTriangle_faceDegree_three
      hred ha hb hd hncol hAcard hnotFF hHall 1)
  intro hq
  change flank₀.1 = flank₁.1 at hq
  have hu₀ := (Classical.choose_spec
    (ConcreteOppositeLineCoherence.triangleFlank_oppositeEdge_bridge
      hred ha hb hd hncol LL
      (ConcreteStage4FlankComplete.flankSystem_edgeLine
        hred ha hb hd hncol hAcard hnotFF)
      e₀ j₀
      (ConcreteStage4ContinuationEndpoints.endpointIndex_adjacent
        hred ha hb hd hncol hAcard hnotFF hHall 0)
      (ConcreteStage4ContinuationEndpoints.endpointTriangle_faceDegree_three
        hred ha hb hd hncol hAcard hnotFF hHall 0))).1
  have hu₁ := (Classical.choose_spec
    (ConcreteOppositeLineCoherence.triangleFlank_oppositeEdge_bridge
      hred ha hb hd hncol LL
      (ConcreteStage4FlankComplete.flankSystem_edgeLine
        hred ha hb hd hncol hAcard hnotFF)
      e₁ j₁
      (ConcreteStage4ContinuationEndpoints.endpointIndex_adjacent
        hred ha hb hd hncol hAcard hnotFF hHall 1)
      (ConcreteStage4ContinuationEndpoints.endpointTriangle_faceDegree_three
        hred ha hb hd hncol hAcard hnotFF hHall 1))).1
  obtain ⟨r₀, hr₀, hr₀u, _⟩ :=
    ConcreteOppositeLineCoherence.triangleFlank_pathEdge_bridge
      hred ha hb hd hncol LL
      (ConcreteStage4FlankComplete.flankSystem_edgeLine
        hred ha hb hd hncol hAcard hnotFF)
      e₀ j₀
      (ConcreteStage4ContinuationEndpoints.endpointIndex_adjacent
        hred ha hb hd hncol hAcard hnotFF hHall 0)
      (ConcreteStage4ContinuationEndpoints.endpointTriangle_faceDegree_three
        hred ha hb hd hncol hAcard hnotFF hHall 0) u₀ hu₀
  obtain ⟨r₁, hr₁, hr₁u, _⟩ :=
    ConcreteOppositeLineCoherence.triangleFlank_pathEdge_bridge
      hred ha hb hd hncol LL
      (ConcreteStage4FlankComplete.flankSystem_edgeLine
        hred ha hb hd hncol hAcard hnotFF)
      e₁ j₁
      (ConcreteStage4ContinuationEndpoints.endpointIndex_adjacent
        hred ha hb hd hncol hAcard hnotFF hHall 1)
      (ConcreteStage4ContinuationEndpoints.endpointTriangle_faceDegree_three
        hred ha hb hd hncol hAcard hnotFF hHall 1) u₁ hu₁
  let opp₀ := DD.boundaryEdge flank₀.1 u₀
  let opp₁ := DD.boundaryEdge flank₁.1 u₁
  let path₀ := DD.boundaryEdge flank₀.1 r₀
  let path₁ := DD.boundaryEdge flank₁.1 r₁
  let sep₀ := DD.boundaryEdge flank₀.1 flank₀.2
  let sep₁ := DD.boundaryEdge flank₁.1 flank₁.2
  have hoppOwner : ConcretePolarFlankBounds.edgeLine opp₀ =
      ConcretePolarFlankBounds.edgeLine opp₁ := by
    calc
      ConcretePolarFlankBounds.edgeLine opp₀ =
          ABKPR.Data.evilOppositeLine DD LL e₀ := hu₀
      _ = ABKPR.Data.evilOppositeLine DD LL e₁ :=
        ABKPR.Data.OppositeLineCoherence.deficientPath_endpoints_oppositeLine_eq
          DD LL
          (ConcreteOppositeLineCoherence.oppositeLineCoherence
            hred ha hb hd hncol LL
            (ConcreteStage4FlankComplete.flankSystem_edgeLine
              hred ha hb hd hncol hAcard hnotFF)) hHall 1
      _ = ConcretePolarFlankBounds.edgeLine opp₁ := hu₁.symm
  have hpathOwner : ConcretePolarFlankBounds.edgeLine path₀ =
      ConcretePolarFlankBounds.edgeLine path₁ := by
    change LL.edgeLine path₀ = LL.edgeLine path₁
    exact hr₀.trans ((ABKPR.Data.deficientPath_endpoints_badEdgeLine_eq
      DD LL hHall 1).trans hr₁.symm)
  have hmemOpp₀ : opp₀ ∈ faceEdges (normals (B (P := P))) flank₀.1 :=
    boundaryEdge_mem_faceEdges hred ha hb hd hncol flank₀.1 u₀
  have hmemPath₀ : path₀ ∈ faceEdges (normals (B (P := P))) flank₀.1 :=
    boundaryEdge_mem_faceEdges hred ha hb hd hncol flank₀.1 r₀
  have hmemSep₀ : sep₀ ∈ faceEdges (normals (B (P := P))) flank₀.1 :=
    boundaryEdge_mem_faceEdges hred ha hb hd hncol flank₀.1 flank₀.2
  have hmemOpp₁ : opp₁ ∈ faceEdges (normals (B (P := P))) flank₀.1 := by
    rw [hq]
    exact boundaryEdge_mem_faceEdges hred ha hb hd hncol flank₁.1 u₁
  have hmemPath₁ : path₁ ∈ faceEdges (normals (B (P := P))) flank₀.1 := by
    rw [hq]
    exact boundaryEdge_mem_faceEdges hred ha hb hd hncol flank₁.1 r₁
  have hmemSep₁ : sep₁ ∈ faceEdges (normals (B (P := P))) flank₀.1 := by
    rw [hq]
    exact boundaryEdge_mem_faceEdges hred ha hb hd hncol flank₁.1 flank₁.2
  have hopp : opp₀ = opp₁ :=
    strictEdge_eq_of_faceEdges_of_owner_eq hmemOpp₀ hmemOpp₁ hoppOwner
  have hpath : path₀ = path₁ :=
    strictEdge_eq_of_faceEdges_of_owner_eq hmemPath₀ hmemPath₁ hpathOwner
  have hu₀bad : ConcretePolarFlankBounds.edgeLine opp₀ =
      ConcretePolarFlankBounds.edgeLine
        (DD.boundaryEdge bad₀.1
          (ABKPR.faceSucc CC bad₀.1 (ABKPR.faceSucc CC bad₀.1 bad₀.2))) := by
    calc
      ConcretePolarFlankBounds.edgeLine opp₀ =
          ABKPR.Data.evilOppositeLine DD LL e₀ := hu₀
      _ = _ := by
        unfold ABKPR.Data.evilOppositeLine ABKPR.Data.evilBadOppositeDart
        rw [ConcreteStage4FlankComplete.flankSystem_edgeLine
          hred ha hb hd hncol hAcard hnotFF]
        rfl
  have hu₁bad : ConcretePolarFlankBounds.edgeLine opp₁ =
      ConcretePolarFlankBounds.edgeLine
        (DD.boundaryEdge bad₁.1
          (ABKPR.faceSucc CC bad₁.1 (ABKPR.faceSucc CC bad₁.1 bad₁.2))) := by
    calc
      ConcretePolarFlankBounds.edgeLine opp₁ =
          ABKPR.Data.evilOppositeLine DD LL e₁ := hu₁
      _ = _ := by
        unfold ABKPR.Data.evilOppositeLine ABKPR.Data.evilBadOppositeDart
        rw [ConcreteStage4FlankComplete.flankSystem_edgeLine
          hred ha hb hd hncol hAcard hnotFF]
        rfl
  have hr₀bad : ConcretePolarFlankBounds.edgeLine path₀ =
      ConcretePolarFlankBounds.edgeLine (DD.boundaryEdge bad₀.1 bad₀.2) := by
    have hr := hr₀
    rw [ConcreteStage4FlankComplete.flankSystem_edgeLine
      hred ha hb hd hncol hAcard hnotFF] at hr
    exact hr.trans (congrArg ConcretePolarFlankBounds.edgeLine
      (DD.across_sameEdge (DD.evilDart e₀)))
  have hr₁bad : ConcretePolarFlankBounds.edgeLine path₁ =
      ConcretePolarFlankBounds.edgeLine (DD.boundaryEdge bad₁.1 bad₁.2) := by
    have hr := hr₁
    rw [ConcreteStage4FlankComplete.flankSystem_edgeLine
      hred ha hb hd hncol hAcard hnotFF] at hr
    exact hr.trans (congrArg ConcretePolarFlankBounds.edgeLine
      (DD.across_sameEdge (DD.evilDart e₁)))
  have hs₀bad : ConcretePolarFlankBounds.edgeLine sep₀ =
      ConcretePolarFlankBounds.edgeLine (DD.boundaryEdge bad₀.1 j₀) :=
    congrArg ConcretePolarFlankBounds.edgeLine
      (DD.across_sameEdge ⟨bad₀.1, j₀⟩).symm
  have hs₁bad : ConcretePolarFlankBounds.edgeLine sep₁ =
      ConcretePolarFlankBounds.edgeLine (DD.boundaryEdge bad₁.1 j₁) :=
    congrArg ConcretePolarFlankBounds.edgeLine
      (DD.across_sameEdge ⟨bad₁.1, j₁⟩).symm
  have hsepPath₀Line : ConcretePolarFlankBounds.edgeLine sep₀ ≠
      ConcretePolarFlankBounds.edgeLine path₀ := by
    calc
      ConcretePolarFlankBounds.edgeLine sep₀ =
          ConcretePolarFlankBounds.edgeLine (DD.boundaryEdge bad₀.1 j₀) := hs₀bad
      _ ≠ ConcretePolarFlankBounds.edgeLine (DD.boundaryEdge bad₀.1 bad₀.2) :=
        Function.Injective.ne
          (ConcretePolarFlankBounds.data_boundary_edgeLine_injective
            hred ha hb hd hncol bad₀.1)
          (ABKPR.ne_of_cyclicAdjacent_of_faceDegree_eq_four
            CC (DD.evilDart_across_bad e₀).1.1 bad₀.2 j₀
            (ConcreteStage4ContinuationEndpoints.endpointIndex_adjacent
              hred ha hb hd hncol hAcard hnotFF hHall 0)).symm
      _ = ConcretePolarFlankBounds.edgeLine path₀ := hr₀bad.symm
  have hsepOpp₀Line : ConcretePolarFlankBounds.edgeLine sep₀ ≠
      ConcretePolarFlankBounds.edgeLine opp₀ := by
    calc
      ConcretePolarFlankBounds.edgeLine sep₀ =
          ConcretePolarFlankBounds.edgeLine (DD.boundaryEdge bad₀.1 j₀) := hs₀bad
      _ ≠ ConcretePolarFlankBounds.edgeLine
          (DD.boundaryEdge bad₀.1
            (ABKPR.faceSucc CC bad₀.1 (ABKPR.faceSucc CC bad₀.1 bad₀.2))) :=
        Function.Injective.ne
          (ConcretePolarFlankBounds.data_boundary_edgeLine_injective
            hred ha hb hd hncol bad₀.1)
          (ABKPR.cyclicAdjacent_ne_secondSucc_of_faceDegree_eq_four
            CC (DD.evilDart_across_bad e₀).1.1 bad₀.2 j₀
            (ConcreteStage4ContinuationEndpoints.endpointIndex_adjacent
              hred ha hb hd hncol hAcard hnotFF hHall 0))
      _ = ConcretePolarFlankBounds.edgeLine opp₀ := hu₀bad.symm
  have hsepPath₁Line : ConcretePolarFlankBounds.edgeLine sep₁ ≠
      ConcretePolarFlankBounds.edgeLine path₁ := by
    calc
      ConcretePolarFlankBounds.edgeLine sep₁ =
          ConcretePolarFlankBounds.edgeLine (DD.boundaryEdge bad₁.1 j₁) := hs₁bad
      _ ≠ ConcretePolarFlankBounds.edgeLine (DD.boundaryEdge bad₁.1 bad₁.2) :=
        Function.Injective.ne
          (ConcretePolarFlankBounds.data_boundary_edgeLine_injective
            hred ha hb hd hncol bad₁.1)
          (ABKPR.ne_of_cyclicAdjacent_of_faceDegree_eq_four
            CC (DD.evilDart_across_bad e₁).1.1 bad₁.2 j₁
            (ConcreteStage4ContinuationEndpoints.endpointIndex_adjacent
              hred ha hb hd hncol hAcard hnotFF hHall 1)).symm
      _ = ConcretePolarFlankBounds.edgeLine path₁ := hr₁bad.symm
  have hsepOpp₁Line : ConcretePolarFlankBounds.edgeLine sep₁ ≠
      ConcretePolarFlankBounds.edgeLine opp₁ := by
    calc
      ConcretePolarFlankBounds.edgeLine sep₁ =
          ConcretePolarFlankBounds.edgeLine (DD.boundaryEdge bad₁.1 j₁) := hs₁bad
      _ ≠ ConcretePolarFlankBounds.edgeLine
          (DD.boundaryEdge bad₁.1
            (ABKPR.faceSucc CC bad₁.1 (ABKPR.faceSucc CC bad₁.1 bad₁.2))) :=
        Function.Injective.ne
          (ConcretePolarFlankBounds.data_boundary_edgeLine_injective
            hred ha hb hd hncol bad₁.1)
          (ABKPR.cyclicAdjacent_ne_secondSucc_of_faceDegree_eq_four
            CC (DD.evilDart_across_bad e₁).1.1 bad₁.2 j₁
            (ConcreteStage4ContinuationEndpoints.endpointIndex_adjacent
              hred ha hb hd hncol hAcard hnotFF hHall 1))
      _ = ConcretePolarFlankBounds.edgeLine opp₁ := hu₁bad.symm
  have hsep : sep₀ = sep₁ := by
    let owners := faceEdgeOwners (normals (B (P := P))) flank₀.1
    have hcard : owners.card = 3 := by
      rw [card_faceEdgeOwners]
      exact ConcreteStage4ContinuationEndpoints.endpointTriangle_degree_three
        hred ha hb hd hncol hAcard hnotFF hHall 0
    by_contra hne
    have hownerNe : strictEdgeOwner sep₀ ≠ strictEdgeOwner sep₁ := by
      intro hs
      exact hne (strictEdge_eq_of_faceEdges_of_owner_eq
        hmemSep₀ hmemSep₁ hs)
    have hopPath : strictEdgeOwner opp₀ ≠ strictEdgeOwner path₀ := by
      intro hs
      exact hr₀u.symm (ConcretePolarFlankBounds.data_boundary_edgeLine_injective
        hred ha hb hd hncol flank₀.1 hs)
    have hopSep₀ : strictEdgeOwner opp₀ ≠ strictEdgeOwner sep₀ := by
      exact hsepOpp₀Line.symm
    have hpathSep₀ : strictEdgeOwner path₀ ≠ strictEdgeOwner sep₀ := by
      exact hsepPath₀Line.symm
    have hopSep₁ : strictEdgeOwner opp₀ ≠ strictEdgeOwner sep₁ := by
      rw [hopp]
      exact hsepOpp₁Line.symm
    have hpathSep₁ : strictEdgeOwner path₀ ≠ strictEdgeOwner sep₁ := by
      rw [hpath]
      exact hsepPath₁Line.symm
    have hsubset : ({strictEdgeOwner opp₀, strictEdgeOwner path₀,
        strictEdgeOwner sep₀, strictEdgeOwner sep₁} :
        Finset (B (P := P))) ⊆ owners := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact Finset.mem_image.mpr ⟨opp₀, hmemOpp₀, rfl⟩
      · exact Finset.mem_image.mpr ⟨path₀, hmemPath₀, rfl⟩
      · exact Finset.mem_image.mpr ⟨sep₀, hmemSep₀, rfl⟩
      · exact Finset.mem_image.mpr ⟨sep₁, hmemSep₁, rfl⟩
    have hc := Finset.card_le_card hsubset
    have hfour : ({strictEdgeOwner opp₀, strictEdgeOwner path₀,
        strictEdgeOwner sep₀, strictEdgeOwner sep₁} :
        Finset (B (P := P))).card = 4 := by
      simp [hopPath, hopSep₀, hopSep₁, hpathSep₀,
        hpathSep₁, hownerNe]
    omega
  have hbadFaces : bad₀.1 = bad₁.1 := by
    have hinv₀ := DD.across_involutive ⟨bad₀.1, j₀⟩
    have hinv₁ := DD.across_involutive ⟨bad₁.1, j₁⟩
    have hb₀ : bad₀.1 = (DD.across ⟨flank₀.1, flank₀.2⟩).1 :=
      (congrArg Sigma.fst hinv₀).symm
    have hb₁ : bad₁.1 = (DD.across ⟨flank₁.1, flank₁.2⟩).1 :=
      (congrArg Sigma.fst hinv₁).symm
    calc
      bad₀.1 = edgeFace (normals (B (P := P))) (normals_ne_zero (B (P := P)))
          sep₀ (!(flank₀.1.1 sep₀.1.1)) := by
        rw [hb₀, ← ConcretePolarABKPRData.concreteData_across_face_eq_edgeFace_flip
          hred ha hb hd hncol flank₀.1 flank₀.2]
      _ = edgeFace (normals (B (P := P))) (normals_ne_zero (B (P := P)))
          sep₁ (!(flank₁.1.1 sep₁.1.1)) := by rw [hsep, hq]
      _ = bad₁.1 := by
        rw [← ConcretePolarABKPRData.concreteData_across_face_eq_edgeFace_flip
          hred ha hb hd hncol flank₁.1 flank₁.2, ← hb₁]
  have hpathBad : DD.boundaryEdge bad₀.1 bad₀.2 =
      DD.boundaryEdge bad₁.1 bad₁.2 := by
    apply strictEdge_eq_of_faceEdges_of_owner_eq
    · exact boundaryEdge_mem_faceEdges hred ha hb hd hncol bad₀.1 bad₀.2
    · rw [hbadFaces]
      exact boundaryEdge_mem_faceEdges hred ha hb hd hncol bad₁.1 bad₁.2
    exact hr₀bad.symm.trans (hpathOwner.trans hr₁bad)
  have heFaces : e₀.1 = e₁.1 := by
    have hinv₀ := DD.across_involutive (DD.evilDart e₀)
    have hinv₁ := DD.across_involutive (DD.evilDart e₁)
    have he₀ : e₀.1 = (DD.across ⟨bad₀.1, bad₀.2⟩).1 :=
      (congrArg Sigma.fst hinv₀).symm
    have he₁ : e₁.1 = (DD.across ⟨bad₁.1, bad₁.2⟩).1 :=
      (congrArg Sigma.fst hinv₁).symm
    calc
      e₀.1 = edgeFace (normals (B (P := P))) (normals_ne_zero (B (P := P)))
          (DD.boundaryEdge bad₀.1 bad₀.2)
          (!(bad₀.1.1 (DD.boundaryEdge bad₀.1 bad₀.2).1.1)) := by
        rw [he₀, ← ConcretePolarABKPRData.concreteData_across_face_eq_edgeFace_flip
          hred ha hb hd hncol bad₀.1 bad₀.2]
      _ = edgeFace (normals (B (P := P))) (normals_ne_zero (B (P := P)))
          (DD.boundaryEdge bad₁.1 bad₁.2)
          (!(bad₁.1.1 (DD.boundaryEdge bad₁.1 bad₁.2).1.1)) := by
        rw [hpathBad, hbadFaces]
      _ = e₁.1 := by
        rw [← ConcretePolarABKPRData.concreteData_across_face_eq_edgeFace_flip
          hred ha hb hd hncol bad₁.1 bad₁.2, ← he₁]
  exact (by decide : (0 : Fin 2) ≠ 1)
    (H.endpoint_injective (Subtype.ext heFaces))

/-- The two endpoint continuation triangles occupy different projective
cyclic intervals.  Indeed, equality of their intervals would put the two
triangles in one antipodal face orbit.  The preceding geometric argument
excludes equality, while path-side sign propagation excludes antipodality. -/
theorem endpointCyclicEdges_ne
    (hAcard : 3 ≤ (ordinaryPoints P).card)
    (hnotFF : ¬ IsFailedFano P)
    (hHall : ¬ (G hred ha hb hd hncol hAcard hnotFF).NoEvilEvilPath) :
    ConcreteStage4OccupiedBelt.endpointCyclicEdge
        hred ha hb hd hncol hAcard hnotFF hHall 0 ≠
      ConcreteStage4OccupiedBelt.endpointCyclicEdge
        hred ha hb hd hncol hAcard hnotFF hHall 1 := by
  intro hbase
  let e₁ := ConcreteStage4OccupiedBelt.endpointStrictEdge
    hred ha hb hd hncol hAcard hnotFF hHall 1
  let q₁ := ConcreteStage4ContinuationEndpoints.endpointTriangle
    hred ha hb hd hncol hAcard hnotFF hHall 1
  have hbase₁ :
      (strictEdgeLiftedCyclicEquiv (B (P := P)) ha hb hd hncol
        (ConcreteStage4OccupiedBelt.pick ha hb hncol) e₁).1 =
      ConcreteStage4OccupiedBelt.endpointCyclicEdge
        hred ha hb hd hncol hAcard hnotFF hHall 0 := by
    rw [ConcreteStage4OccupiedBelt.endpointStrictEdge_lifted_base]
    exact hbase.symm
  have horbit :=
    ConcreteStage4BeltClassification.endpoint_projective_slot_triangle_eq_or_antipode
      hred ha hb hd hncol hAcard hnotFF hHall 0 e₁ q₁ hbase₁
      (ConcreteStage4BeltClassification.endpointStrictEdge_incident
        hred ha hb hd hncol hAcard hnotFF hHall 1)
      (ConcreteStage4EndpointSlots.endpointOpposite_across_not_triangle
        hred ha hb hd hncol hAcard hnotFF hHall 0)
      (ConcreteStage4BeltClassification.endpointTriangle_strictFaceDegree_three
        hred ha hb hd hncol hAcard hnotFF hHall 1)
  rcases horbit with heq | hanti
  · exact endpointTriangles_ne
      hred ha hb hd hncol hAcard hnotFF hHall heq
  · exact endpointTriangles_not_antipodal
      hred ha hb hd hncol hAcard hnotFF hHall hanti

end Erdos735.ConcreteStage4EndpointIntervalSeparation
