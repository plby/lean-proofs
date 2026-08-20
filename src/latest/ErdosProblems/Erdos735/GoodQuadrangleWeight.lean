/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos735.RedChordEndpointRestriction
import ErdosProblems.Erdos735.Discharging12

/-!
# The local weight obstruction for a good two-diagonal quadrangle

At a projective blue vertex incident with an ordinary red line, the blue
weights sum to half the common line weight.  Three multiplicity-two corners
of a quadrangle therefore give the three alternating pair equations.  At a
fourth corner of larger multiplicity, the remaining blue weights form a
strictly positive extra term.  This is the geometric input to
`uniqueGoodQuadrangle_weightContradiction`.
-/

open Classical
open scoped BigOperators LinearAlgebra.Projectivization

namespace Erdos735.RedBlueDualIncidence

open ProjectiveArrangement ProjectiveBoundaryExtraction ChartOrder

/-- Projective incidence with an arbitrary primal point, rather than only
with a point already packaged as a blue arrangement line. -/
lemma incident_iff_vertexHomogeneous_mem_dualLine
    {B : Finset Point} (v : Vertex B) (p : Point) :
    Incident v.1 p ↔
      vertexHomogeneous v ∈ ProjectiveDuality.dualLine p := by
  change normalVec p ⬝ᵥ v.1.rep = 0 ↔ _
  simpa [vertexHomogeneous] using
    (dotProduct_normalVec_toCoordinates_iff p (vertexHomogeneous v))

/-- A crossing of blue dual lines that is incident with a specified
ordinary red line consists of that red point together with precisely its
blue incident points. -/
theorem dualIncidentFiber_eq_insert_blueIncidentPoints
    {P : Finset Point} {w : Point → ℝ} {c : ℝ}
    (hred : IsReducedMagic P w c)
    (v : Vertex (nonordinaryPoints P))
    {a : Point} (ha : a ∈ ordinaryPoints P)
    (hainc : vertexHomogeneous v ∈ ProjectiveDuality.dualLine a) :
    dualIncidentFiber P (vertexHomogeneous v) =
      insert a (blueIncidentPoints P (vertexHomogeneous v)) := by
  have hv := v.2
  unfold projectiveVertices at hv
  obtain ⟨pq, -, hpqv⟩ := Finset.mem_image.mp hv
  let b : Line (nonordinaryPoints P) := pq.1.1
  have hbOn : OnLine (nonordinaryPoints P) v b := by
    change Incident v.1 b.1
    rw [← hpqv]
    exact indexedIntersection_incident_left _ pq
  have hbInc : vertexHomogeneous v ∈ ProjectiveDuality.dualLine b.1 :=
    (onLine_iff_mem_dualLine v b).mp hbOn
  ext p
  simp only [dualIncidentFiber, blueIncidentPoints, Finset.mem_filter,
    Finset.mem_insert]
  constructor
  · rintro ⟨hpP, hpinc⟩
    by_cases hpA : p ∈ ordinaryPoints P
    · left
      exact ordinary_incident_unique_at_blue_crossing hred
        (isDualCrossing_vertex_nonordinary P v) b.2 hbInc hpA ha hpinc hainc
    · right
      exact ⟨Finset.mem_sdiff.mpr ⟨hpP, hpA⟩, hpinc⟩
  · rintro (rfl | ⟨hpB, hpinc⟩)
    · exact ⟨ordinaryPoints_subset P ha, hainc⟩
    · exact ⟨nonordinaryPoints_subset P hpB, hpinc⟩

/-- Removing the unique ordinary weight from the common line sum leaves
exactly half the common weight on the blue incident points. -/
theorem sum_blueIncidentPoints_eq_half
    {P : Finset Point} {w : Point → ℝ} {c : ℝ}
    (hred : IsReducedMagic P w c)
    (v : Vertex (nonordinaryPoints P))
    {a : Point} (ha : a ∈ ordinaryPoints P)
    (hainc : vertexHomogeneous v ∈ ProjectiveDuality.dualLine a) :
    (∑ b ∈ blueIncidentPoints P (vertexHomogeneous v), w b) = c / 2 := by
  have htotal := dualCrossing_weight_eq hred.2.1
    (isDualCrossing_vertex_nonordinary P v)
  have hfiber := dualIncidentFiber_eq_insert_blueIncidentPoints hred v ha hainc
  have hanot : a ∉ blueIncidentPoints P (vertexHomogeneous v) := by
    intro hamem
    have haB := (Finset.mem_filter.mp hamem).1
    exact (Finset.disjoint_left.mp
      (disjoint_ordinaryPoints_nonordinaryPoints P)) ha haB
  rw [hfiber, Finset.sum_insert hanot] at htotal
  rw [hred.2.2.1 a ha] at htotal
  linarith

/-- Two named incident blue lines exhaust a multiplicity-two blue vertex. -/
theorem blueIncidentPoints_eq_pair_of_multiplicity_two
    {P : Finset Point}
    (v : Vertex (nonordinaryPoints P))
    (b d : Line (nonordinaryPoints P)) (hbd : b ≠ d)
    (hb : OnLine (nonordinaryPoints P) v b)
    (hd : OnLine (nonordinaryPoints P) v d)
    (hmult : lineMultiplicity (OnLine (nonordinaryPoints P)) v = 2) :
    blueIncidentPoints P (vertexHomogeneous v) = {b.1, d.1} := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨b.2, (onLine_iff_mem_dualLine v b).mp hb⟩
    · exact Finset.mem_filter.mpr ⟨d.2, (onLine_iff_mem_dualLine v d).mp hd⟩
  · rw [card_blueIncidentPoints_eq_lineMultiplicity P v, hmult]
    have hbdval : b.1 ≠ d.1 := fun h ↦ hbd (Subtype.ext h)
    rw [Finset.card_pair hbdval]

/-- Normalized pair-weight equation at a multiplicity-two blue vertex
carrying an ordinary red line. -/
theorem normalized_pair_weight_eq_half_of_multiplicity_two
    {P : Finset Point} {w : Point → ℝ} {c : ℝ}
    (hred : IsReducedMagic P w c)
    (v : Vertex (nonordinaryPoints P))
    {a : Point} (ha : a ∈ ordinaryPoints P)
    (hainc : vertexHomogeneous v ∈ ProjectiveDuality.dualLine a)
    (b d : Line (nonordinaryPoints P)) (hbd : b ≠ d)
    (hb : OnLine (nonordinaryPoints P) v b)
    (hd : OnLine (nonordinaryPoints P) v d)
    (hmult : lineMultiplicity (OnLine (nonordinaryPoints P)) v = 2) :
    w b.1 / c + w d.1 / c = 1 / 2 := by
  have hsum := sum_blueIncidentPoints_eq_half hred v ha hainc
  rw [blueIncidentPoints_eq_pair_of_multiplicity_two v b d hbd hb hd hmult] at hsum
  have hbdval : b.1 ≠ d.1 := fun h ↦ hbd (Subtype.ext h)
  simp [hbdval] at hsum
  field_simp [hred.1.ne']
  nlinarith

/-- The blue incident points other than two named boundary owners. -/
noncomputable def extraBlueIncidentPoints
    {P : Finset Point} (v : Vertex (nonordinaryPoints P))
    (b d : Line (nonordinaryPoints P)) : Finset Point :=
  blueIncidentPoints P (vertexHomogeneous v) \ {b.1, d.1}

/-- At multiplicity greater than two, two named incident owners leave a
nonempty collection of further blue lines. -/
theorem extraBlueIncidentPoints_nonempty
    {P : Finset Point}
    (v : Vertex (nonordinaryPoints P))
    (b d : Line (nonordinaryPoints P)) (hbd : b ≠ d)
    (hb : OnLine (nonordinaryPoints P) v b)
    (hd : OnLine (nonordinaryPoints P) v d)
    (hmult : 2 < lineMultiplicity (OnLine (nonordinaryPoints P)) v) :
    (extraBlueIncidentPoints v b d).Nonempty := by
  have hpair : ({b.1, d.1} : Finset Point) ⊆
      blueIncidentPoints P (vertexHomogeneous v) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨b.2, (onLine_iff_mem_dualLine v b).mp hb⟩
    · exact Finset.mem_filter.mpr ⟨d.2, (onLine_iff_mem_dualLine v d).mp hd⟩
  apply Finset.nonempty_iff_ne_empty.mpr
  intro hextra
  have hsub : blueIncidentPoints P (vertexHomogeneous v) ⊆ {b.1, d.1} :=
    Finset.sdiff_eq_empty_iff_subset.mp hextra
  have hcard := Finset.card_le_card hsub
  rw [card_blueIncidentPoints_eq_lineMultiplicity P v] at hcard
  have hbdval : b.1 ≠ d.1 := fun h ↦ hbd (Subtype.ext h)
  simp [hbdval] at hcard
  omega

/-- The total weight of the additional blue owners at a larger-multiplicity
corner is strictly positive. -/
theorem sum_extraBlueIncidentPoints_pos
    {P : Finset Point} {w : Point → ℝ} {c : ℝ}
    (hred : IsReducedMagic P w c)
    (v : Vertex (nonordinaryPoints P))
    (b d : Line (nonordinaryPoints P)) (hbd : b ≠ d)
    (hb : OnLine (nonordinaryPoints P) v b)
    (hd : OnLine (nonordinaryPoints P) v d)
    (hmult : 2 < lineMultiplicity (OnLine (nonordinaryPoints P)) v) :
    0 < ∑ x ∈ extraBlueIncidentPoints v b d, w x := by
  apply Finset.sum_pos
  · intro x hx
    have hxS := (Finset.mem_sdiff.mp hx).1
    have hxB := (Finset.mem_filter.mp hxS).1
    exact (hred.2.2.2.1 x hxB).1
  · exact extraBlueIncidentPoints_nonempty v b d hbd hb hd hmult

/-- At a larger-multiplicity red endpoint, the two boundary weights and the
strictly positive sum of all additional blue weights give the fourth
normalized half-weight equation. -/
theorem normalized_pair_add_extra_weight_eq_half
    {P : Finset Point} {w : Point → ℝ} {c : ℝ}
    (hred : IsReducedMagic P w c)
    (v : Vertex (nonordinaryPoints P))
    {a : Point} (ha : a ∈ ordinaryPoints P)
    (hainc : vertexHomogeneous v ∈ ProjectiveDuality.dualLine a)
    (b d : Line (nonordinaryPoints P)) (hbd : b ≠ d)
    (hb : OnLine (nonordinaryPoints P) v b)
    (hd : OnLine (nonordinaryPoints P) v d) :
    w b.1 / c + w d.1 / c +
        (∑ x ∈ extraBlueIncidentPoints v b d, w x) / c = 1 / 2 := by
  have hsum := sum_blueIncidentPoints_eq_half hred v ha hainc
  have hpair : ({b.1, d.1} : Finset Point) ⊆
      blueIncidentPoints P (vertexHomogeneous v) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨b.2, (onLine_iff_mem_dualLine v b).mp hb⟩
    · exact Finset.mem_filter.mpr ⟨d.2, (onLine_iff_mem_dualLine v d).mp hd⟩
  have hsplit := Finset.sum_sdiff (f := w) hpair
  change (∑ x ∈ extraBlueIncidentPoints v b d, w x) +
      ∑ x ∈ ({b.1, d.1} : Finset Point), w x =
      ∑ x ∈ blueIncidentPoints P (vertexHomogeneous v), w x at hsplit
  rw [hsum] at hsplit
  have hbdval : b.1 ≠ d.1 := fun h ↦ hbd (Subtype.ext h)
  simp [hbdval] at hsplit
  field_simp [hred.1.ne']
  nlinarith

end Erdos735.RedBlueDualIncidence

namespace Erdos735.RedChordExtraction.Geometry

open ProjectiveArrangement ProjectiveBoundaryExtraction ChartOrder SignVector
open SignVector.RotationRealization

variable {A B : Finset Point}
variable {G : SimpleGraph (BlueVertex B)} [DecidableRel G.Adj] [Fintype G.edgeSet]
variable (X : RotationRealization (G := G) (blueNormals B) (blueNormals_ne_zero B))

/-- Four successive boundary indices of a quadrangular strict face are
distinct in cyclic order and the fourth successor returns to the first. -/
theorem strictFaceSucc_four_cycle
    (f : StrictFace (blueNormals B))
    (hdeg : X.strictC.faceDegree f = 4)
    (i₀ : Fin (X.strictC.faceDegree f)) :
    let i₁ := X.strictFaceSucc f i₀
    let i₂ := X.strictFaceSucc f i₁
    let i₃ := X.strictFaceSucc f i₂
    i₀ ≠ i₁ ∧ i₁ ≠ i₂ ∧ i₂ ≠ i₃ ∧ i₃ ≠ i₀ ∧
      i₂ ≠ i₀ ∧ X.strictFaceSucc f i₃ = i₀ := by
  dsimp only
  have hsval (i : Fin (X.strictC.faceDegree f)) :
      (X.strictFaceSucc f i).val = (i.val + 1) % 4 := by
    simp only [strictFaceSucc]
    simp only [hdeg]
  let i₁ := X.strictFaceSucc f i₀
  let i₂ := X.strictFaceSucc f i₁
  let i₃ := X.strictFaceSucc f i₂
  have hi₀lt : i₀.val < 4 := by simpa [hdeg] using i₀.isLt
  have hi₁lt : i₁.val < 4 := by simpa [hdeg] using i₁.isLt
  have hi₂lt : i₂.val < 4 := by simpa [hdeg] using i₂.isLt
  have hi₃lt : i₃.val < 4 := by simpa [hdeg] using i₃.isLt
  have hi₁val : i₁.val = (i₀.val + 1) % 4 := hsval i₀
  have hi₂val : i₂.val = (i₁.val + 1) % 4 := hsval i₁
  have hi₃val : i₃.val = (i₂.val + 1) % 4 := hsval i₂
  have hi₄val : (X.strictFaceSucc f i₃).val = (i₃.val + 1) % 4 := hsval i₃
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
  have hcycle : X.strictFaceSucc f i₃ = i₀ := by
    apply Fin.ext
    omega
  exact ⟨h₀₁, h₁₂, h₂₃, h₃₀, h₂₀, hcycle⟩

variable {P : Finset Point} {w : Point → ℝ} {c : ℝ}
variable {Gₚ : SimpleGraph (BlueVertex (nonordinaryPoints P))}
variable [DecidableRel Gₚ.Adj] [Fintype Gₚ.edgeSet]

/-- The exact local reduced-magic input required by
`ABKPR.Data.goodTwoQuadrangle_twoGoodCorners`.

The three compatibility equalities are definitional for the concrete polar
data constructor: it uses the rotation realization's boundary vertices, the
red-sector endpoint finsets, and concrete projective line multiplicity. -/
theorem goodTwoQuadrangle_twoGoodCorners_ofReducedMagic
    (hred : IsReducedMagic P w c)
    (Xₚ : RotationRealization (G := Gₚ)
      (blueNormals (nonordinaryPoints P))
      (blueNormals_ne_zero (nonordinaryPoints P)))
    (Hₚ : Geometry (A := ordinaryPoints P) (B := nonordinaryPoints P) Xₚ)
    (D : ABKPR.Data Xₚ.strictC)
    (hboundaryVertex : ∀ f i, D.boundaryVertex f i = Xₚ.boundaryVertex f i)
    (hendpoints : ∀ f,
      D.redEndpoints f =
        redEndpoints (A := ordinaryPoints P) (B := nonordinaryPoints P) Xₚ Hₚ f)
    (hmultiplicity : ∀ v,
      Xₚ.strictC.blueMultiplicity v =
        lineMultiplicity (OnLine (nonordinaryPoints P)) v) :
    ∀ f, Xₚ.strictC.faceDegree f = 4 → (D.redChords f).card = 2 →
      (D.redEndpoints f \ D.stage1Corners f).Nonempty →
      2 ≤ (D.redEndpoints f \ D.stage1Corners f).card := by
  intro f hdeg hchords hgood
  by_contra hnot
  have hcardpos : 0 < (D.redEndpoints f \ D.stage1Corners f).card :=
    Finset.card_pos.mpr hgood
  have hcardlt : (D.redEndpoints f \ D.stage1Corners f).card < 2 :=
    Nat.lt_of_not_ge hnot
  have hcard : (D.redEndpoints f \ D.stage1Corners f).card = 1 := by omega
  obtain ⟨i₀, hgood_eq⟩ := Finset.card_eq_one.mp hcard
  let i₁ := Xₚ.strictFaceSucc f i₀
  let i₂ := Xₚ.strictFaceSucc f i₁
  let i₃ := Xₚ.strictFaceSucc f i₂
  have hcyc : i₀ ≠ i₁ ∧ i₁ ≠ i₂ ∧ i₂ ≠ i₃ ∧ i₃ ≠ i₀ ∧
      i₂ ≠ i₀ ∧ Xₚ.strictFaceSucc f i₃ = i₀ := by
    simpa [i₁, i₂, i₃] using
      (strictFaceSucc_four_cycle Xₚ f hdeg i₀)
  rcases hcyc with ⟨hi₀i₁, hi₁i₂, hi₂i₃, hi₃i₀, hi₂i₀, hcycle⟩
  have hend_univ : D.redEndpoints f = Finset.univ :=
    D.redEndpoints_eq_univ_of_twoDiagonal ⟨hdeg, hchords⟩
  have hend (i : Fin (Xₚ.strictC.faceDegree f)) : i ∈ D.redEndpoints f := by
    rw [hend_univ]
    exact Finset.mem_univ i
  have hstage_of_ne {i : Fin (Xₚ.strictC.faceDegree f)} (hi : i ≠ i₀) :
      i ∈ D.stage1Corners f := by
    by_contra histage
    have himem : i ∈ D.redEndpoints f \ D.stage1Corners f :=
      Finset.mem_sdiff.mpr ⟨hend i, histage⟩
    rw [hgood_eq] at himem
    exact hi (Finset.mem_singleton.mp himem)
  have hi₁stage : i₁ ∈ D.stage1Corners f :=
    hstage_of_ne hi₀i₁.symm
  have hi₂stage : i₂ ∈ D.stage1Corners f :=
    hstage_of_ne hi₂i₀
  have hi₃stage : i₃ ∈ D.stage1Corners f :=
    hstage_of_ne hi₃i₀
  have hi₀good : i₀ ∈ D.redEndpoints f \ D.stage1Corners f := by
    rw [hgood_eq]
    exact Finset.mem_singleton.mpr rfl
  have hi₀nostage : i₀ ∉ D.stage1Corners f :=
    (Finset.mem_sdiff.mp hi₀good).2

  have hmult₁ : lineMultiplicity (OnLine (nonordinaryPoints P))
      (Xₚ.boundaryVertex f i₁) = 2 := by
    have h := (D.stage1Corner_iff f i₁).mp hi₁stage |>.2
    rw [hboundaryVertex, hmultiplicity] at h
    exact h
  have hmult₂ : lineMultiplicity (OnLine (nonordinaryPoints P))
      (Xₚ.boundaryVertex f i₂) = 2 := by
    have h := (D.stage1Corner_iff f i₂).mp hi₂stage |>.2
    rw [hboundaryVertex, hmultiplicity] at h
    exact h
  have hmult₃ : lineMultiplicity (OnLine (nonordinaryPoints P))
      (Xₚ.boundaryVertex f i₃) = 2 := by
    have h := (D.stage1Corner_iff f i₃).mp hi₃stage |>.2
    rw [hboundaryVertex, hmultiplicity] at h
    exact h
  have hmult₀ne : lineMultiplicity (OnLine (nonordinaryPoints P))
      (Xₚ.boundaryVertex f i₀) ≠ 2 := by
    intro hmult
    apply hi₀nostage
    apply (D.stage1Corner_iff f i₀).mpr
    refine ⟨hend i₀, ?_⟩
    rw [hboundaryVertex, hmultiplicity]
    exact hmult
  have hmult₀ : 2 < lineMultiplicity (OnLine (nonordinaryPoints P))
      (Xₚ.boundaryVertex f i₀) := by
    have htwo := two_le_lineMultiplicity (nonordinaryPoints P)
      (Xₚ.boundaryVertex f i₀)
    omega

  have hredInc (i : Fin (Xₚ.strictC.faceDegree f)) :
      ∃ a : RedLine (ordinaryPoints P),
        a ∈ redChordLines (A := ordinaryPoints P) f ∧
          RedBlueDualIncidence.vertexHomogeneous (Xₚ.boundaryVertex f i) ∈
            ProjectiveDuality.dualLine a.1 := by
    have hiX : i ∈ redEndpoints (A := ordinaryPoints P)
        (B := nonordinaryPoints P) Xₚ Hₚ f := by
      rw [← hendpoints]
      exact hend i
    obtain ⟨a, ha, hainc⟩ :=
      (mem_redEndpoints_iff_exists_feasible_incident
        (A := ordinaryPoints P) (B := nonordinaryPoints P) Xₚ Hₚ f i).mp hiX
    exact ⟨a, ha,
      (RedBlueDualIncidence.incident_iff_vertexHomogeneous_mem_dualLine
        (Xₚ.boundaryVertex f i) a.1).mp hainc⟩
  obtain ⟨a₀, ha₀chord, ha₀inc⟩ := hredInc i₀
  obtain ⟨a₁, ha₁chord, ha₁inc⟩ := hredInc i₁
  obtain ⟨a₂, ha₂chord, ha₂inc⟩ := hredInc i₂
  obtain ⟨a₃, ha₃chord, ha₃inc⟩ := hredInc i₃

  let b₀ : Line (nonordinaryPoints P) := strictEdgeOwner (Xₚ.boundaryEdge f i₀)
  let b₁ : Line (nonordinaryPoints P) := strictEdgeOwner (Xₚ.boundaryEdge f i₁)
  let b₂ : Line (nonordinaryPoints P) := strictEdgeOwner (Xₚ.boundaryEdge f i₂)
  let b₃ : Line (nonordinaryPoints P) := strictEdgeOwner (Xₚ.boundaryEdge f i₃)
  have hb₀b₁ : b₀ ≠ b₁ := by
    intro h
    exact hi₀i₁ (Xₚ.indexedBoundaryOwner_injective f h)
  have hb₁b₂ : b₁ ≠ b₂ := by
    intro h
    exact hi₁i₂ (Xₚ.indexedBoundaryOwner_injective f h)
  have hb₂b₃ : b₂ ≠ b₃ := by
    intro h
    exact hi₂i₃ (Xₚ.indexedBoundaryOwner_injective f h)
  have hb₃b₀ : b₃ ≠ b₀ := by
    intro h
    exact hi₃i₀ (Xₚ.indexedBoundaryOwner_injective f h)

  have hb₀i₁ : OnLine (nonordinaryPoints P) (Xₚ.boundaryVertex f i₁) b₀ := by
    change Incident (Xₚ.boundaryVertex f i₁).1 b₀.1
    simpa [b₀, i₁] using Hₚ.boundary_finish_on_owner f i₀
  have hb₁i₁ : OnLine (nonordinaryPoints P) (Xₚ.boundaryVertex f i₁) b₁ := by
    change Incident (Xₚ.boundaryVertex f i₁).1 b₁.1
    simpa [b₁] using Hₚ.boundary_start_on_owner f i₁
  have hb₁i₂ : OnLine (nonordinaryPoints P) (Xₚ.boundaryVertex f i₂) b₁ := by
    change Incident (Xₚ.boundaryVertex f i₂).1 b₁.1
    simpa [b₁, i₂] using Hₚ.boundary_finish_on_owner f i₁
  have hb₂i₂ : OnLine (nonordinaryPoints P) (Xₚ.boundaryVertex f i₂) b₂ := by
    change Incident (Xₚ.boundaryVertex f i₂).1 b₂.1
    simpa [b₂] using Hₚ.boundary_start_on_owner f i₂
  have hb₂i₃ : OnLine (nonordinaryPoints P) (Xₚ.boundaryVertex f i₃) b₂ := by
    change Incident (Xₚ.boundaryVertex f i₃).1 b₂.1
    simpa [b₂, i₃] using Hₚ.boundary_finish_on_owner f i₂
  have hb₃i₃ : OnLine (nonordinaryPoints P) (Xₚ.boundaryVertex f i₃) b₃ := by
    change Incident (Xₚ.boundaryVertex f i₃).1 b₃.1
    simpa [b₃] using Hₚ.boundary_start_on_owner f i₃
  have hb₃i₀ : OnLine (nonordinaryPoints P) (Xₚ.boundaryVertex f i₀) b₃ := by
    change Incident (Xₚ.boundaryVertex f i₀).1 b₃.1
    rw [← hcycle]
    simpa [b₃] using Hₚ.boundary_finish_on_owner f i₃
  have hb₀i₀ : OnLine (nonordinaryPoints P) (Xₚ.boundaryVertex f i₀) b₀ := by
    change Incident (Xₚ.boundaryVertex f i₀).1 b₀.1
    simpa [b₀] using Hₚ.boundary_start_on_owner f i₀

  have heq₀₁ := RedBlueDualIncidence.normalized_pair_weight_eq_half_of_multiplicity_two
    hred (Xₚ.boundaryVertex f i₁) a₁.2 ha₁inc b₀ b₁ hb₀b₁ hb₀i₁ hb₁i₁ hmult₁
  have heq₁₂ := RedBlueDualIncidence.normalized_pair_weight_eq_half_of_multiplicity_two
    hred (Xₚ.boundaryVertex f i₂) a₂.2 ha₂inc b₁ b₂ hb₁b₂ hb₁i₂ hb₂i₂ hmult₂
  have heq₂₃ := RedBlueDualIncidence.normalized_pair_weight_eq_half_of_multiplicity_two
    hred (Xₚ.boundaryVertex f i₃) a₃.2 ha₃inc b₂ b₃ hb₂b₃ hb₂i₃ hb₃i₃ hmult₃
  have hextraPos := RedBlueDualIncidence.sum_extraBlueIncidentPoints_pos
    hred (Xₚ.boundaryVertex f i₀) b₃ b₀ hb₃b₀ hb₃i₀ hb₀i₀ hmult₀
  have hextraNorm : 0 <
      (∑ x ∈ RedBlueDualIncidence.extraBlueIncidentPoints
        (Xₚ.boundaryVertex f i₀) b₃ b₀, w x) / c :=
    div_pos hextraPos hred.1
  have heq₃₀ := RedBlueDualIncidence.normalized_pair_add_extra_weight_eq_half
    hred (Xₚ.boundaryVertex f i₀) a₀.2 ha₀inc b₃ b₀ hb₃b₀ hb₃i₀ hb₀i₀
  exact ABKPR.uniqueGoodQuadrangle_weightContradiction
    ((∑ x ∈ RedBlueDualIncidence.extraBlueIncidentPoints
      (Xₚ.boundaryVertex f i₀) b₃ b₀, w x) / c)
    (w b₀.1 / c) (w b₁.1 / c) (w b₂.1 / c) (w b₃.1 / c)
    hextraNorm heq₀₁ heq₁₂ heq₂₃ heq₃₀

end Erdos735.RedChordExtraction.Geometry
