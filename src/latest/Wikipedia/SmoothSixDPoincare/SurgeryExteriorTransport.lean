import Wikipedia.SmoothSixDPoincare.SurgeryComplementPieces

/-!
# Transport through the actual common surgery exterior

A map whose whole image lies in the new exterior lifts through its closed
embedding and then maps to the old exterior. Closed embeddings and exact
common-face incidences are retained by this construction.
-/

noncomputable section

open Set Function Topology

namespace Wikipedia.SmoothSixDPoincare.SurgeryBoundaryPair

open PuncturedHandle

variable {N P R X Y Z : Type*} [NormedAddCommGroup N] [NormedAddCommGroup P]
  [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  (d : SurgeryBoundaryPair N P R X Y) (g : C(Z, Y))
  (hg : ∀ z, g z ∈ range d.newExterior)

/-- Actual common-exterior coordinates of the given map. -/
def exteriorCoordinates : C(Z, R) where
  toFun z := d.newExterior_closed.toHomeomorph.symm ⟨g z, hg z⟩
  continuous_toFun := d.newExterior_closed.toHomeomorph.symm.continuous.comp
    (g.continuous.subtype_mk _)

theorem newExterior_exteriorCoordinates (z : Z) :
    d.newExterior (d.exteriorCoordinates g hg z) = g z :=
  congrArg Subtype.val (d.newExterior_closed.toHomeomorph.apply_symm_apply ⟨g z, hg z⟩)

/-- Transport the whole map from the new boundary to the old boundary. -/
def transportExterior : C(Z, X) where
  toFun z := d.oldExterior (d.exteriorCoordinates g hg z)
  continuous_toFun := d.oldExterior_closed.continuous.comp (d.exteriorCoordinates g hg).continuous

theorem transportExterior_eq_of_newExterior_eq {z : Z} {r : R}
    (hr : g z = d.newExterior r) : d.transportExterior g hg z = d.oldExterior r := by
  have hcoords : d.exteriorCoordinates g hg z = r :=
    d.newExterior_closed.injective ((d.newExterior_exteriorCoordinates g hg z).trans hr)
  exact congrArg d.oldExterior hcoords

theorem transportExterior_isClosedEmbedding (hclosed : IsClosedEmbedding g) :
    IsClosedEmbedding (d.transportExterior g hg) := by
  have hcod : IsClosedEmbedding (fun z : Z => (⟨g z, hg z⟩ : range d.newExterior)) :=
    ClosedCover.isClosedEmbedding_codRestrict hclosed hg
  exact d.oldExterior_closed.comp
    (d.newExterior_closed.toHomeomorph.symm.isClosedEmbedding.comp hcod)

/-- A point on the new common face becomes exactly its original old-face point. -/
theorem transportExterior_boundary {z : Z} (q : UnitSphere N × UnitSphere P)
    (hz : g z = d.newPiece (newBoundary q)) :
    d.transportExterior g hg z = d.oldPiece (oldBoundary q) := by
  have hnew : d.newExterior (d.boundary q) = d.newPiece (newBoundary q) :=
    (d.new_overlap _ _).mpr ⟨q, rfl, rfl⟩
  have hold : d.oldExterior (d.boundary q) = d.oldPiece (oldBoundary q) :=
    (d.old_overlap _ _).mpr ⟨q, rfl, rfl⟩
  exact (d.transportExterior_eq_of_newExterior_eq g hg (hz.trans hnew.symm)).trans hold

/-- The complete old-piece overlap is precisely the original common-face
relation, including the full boundary parameters. -/
theorem transportExterior_oldPiece_iff (z : Z) (p : UnitSphere N × UnitBall P) :
    d.transportExterior g hg z = d.oldPiece p ↔
      ∃ q : UnitSphere N × UnitSphere P,
        g z = d.newPiece (newBoundary q) ∧ p = oldBoundary q := by
  constructor
  · intro hz
    obtain ⟨q, hq, hp⟩ := (d.old_overlap (d.exteriorCoordinates g hg z) p).mp hz
    refine ⟨q, ?_, hp⟩
    calc
      g z = d.newExterior (d.exteriorCoordinates g hg z) :=
        (d.newExterior_exteriorCoordinates g hg z).symm
      _ = d.newExterior (d.boundary q) := congrArg d.newExterior hq
      _ = d.newPiece (newBoundary q) := (d.new_overlap _ _).mpr ⟨q, rfl, rfl⟩
  · rintro ⟨q, hz, rfl⟩
    exact d.transportExterior_boundary g hg q hz

end Wikipedia.SmoothSixDPoincare.SurgeryBoundaryPair
