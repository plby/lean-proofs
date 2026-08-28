import Wikipedia.NoExoticSixSphere.JamesSphereConeQuotient

/-!
# Both cell-attachment orders in the actual James cone

The one-letter sphere is identified with the original lower subspace.
Pasting the genuine pushout squares presents the same cone model as a
`2n`-disk attached to the `(n+1)`-disk. The checked punctured-cell
construction therefore supplies the two required strong deformations:
puncturing the cone cell retracts onto the James stage, and puncturing
the James top cell retracts onto the actual cone disk.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Set Metric Topology

namespace NoExoticSixSphere.JamesSphere.SecondStageCone

def lowerSphere (n : ℕ) : Sphere n ≃ₜ StageAttachment.lower n 1 :=
  (FirstStage.homeomorph n).trans (StageAttachment.lowerHomeomorph n 1)

def lowerToCone (n : ℕ) : TopCat.of (StageAttachment.lower n 1) ⟶
    TopCat.of (CompactCellAttachment.Disk (ConeCoordinates n)) :=
  (TopCat.isoOfHomeo (lowerSphere n)).inv ≫ PuncturedCellAttachment.boundary

theorem lowerSphere_factor (n : ℕ) :
    (TopCat.isoOfHomeo (lowerSphere n)).hom ≫ StageAttachment.lowerInclusion n 1 =
      TopCat.ofHom (attaching n) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  rfl

theorem lower_isPushout (n : ℕ) : IsPushout (StageAttachment.lowerInclusion n 1)
    (lowerToCone n) (TopCat.ofHom (base n)) (TopCat.ofHom (cone n)) := by
  apply (isPushout n).of_iso (TopCat.isoOfHomeo (lowerSphere n))
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp only [Iso.refl_hom, Category.comp_id]
    exact (lowerSphere_factor n).symm
  · simp only [Iso.refl_hom, Category.comp_id]
    unfold lowerToCone
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]

def firstAttaching (n : ℕ) : TopCat.of (sphere (0 : PuncturedStage.Coordinates n 1) 1) ⟶
    TopCat.of (CompactCellAttachment.Disk (ConeCoordinates n)) :=
  PuncturedStage.attaching n 1 ≫ lowerToCone n

def firstCell (n : ℕ) : C(PuncturedCellAttachment.Disk (PuncturedStage.Coordinates n 1), Space n) :=
  (base n).comp (Cell.closedPresentation n 2)

theorem first_isPushout (n : ℕ) (hn : 0 < n) : IsPushout (firstAttaching n)
    PuncturedCellAttachment.boundary (TopCat.ofHom (cone n)) (TopCat.ofHom (firstCell n)) :=
  ((PuncturedStage.isPushout n 1 hn).flip.paste_vert (lower_isPushout n)).flip

def firstPunctured (n : ℕ) (p : PuncturedStage.Coordinates n 1) (hp : ‖p‖ < 1) :=
  PuncturedCellAttachment.punctured (j := TopCat.ofHom (firstCell n)) p hp

def firstPunctureInclusion (n : ℕ) (hn : 0 < n)
    (p : PuncturedStage.Coordinates n 1) (hp : ‖p‖ < 1) :
    C(CompactCellAttachment.Disk (ConeCoordinates n), firstPunctured n p hp) :=
  (PuncturedCellAttachment.baseInclusion (first_isPushout n hn) p hp).hom

def firstPunctureRetraction (n : ℕ) (hn : 0 < n)
    (p : PuncturedStage.Coordinates n 1) (hp : ‖p‖ < 1) :
    C(firstPunctured n p hp, CompactCellAttachment.Disk (ConeCoordinates n)) :=
  (PuncturedCellAttachment.retraction (first_isPushout n hn) p hp).hom

theorem firstPunctureInclusion_val (n : ℕ) (hn : 0 < n)
    (p : PuncturedStage.Coordinates n 1) (hp : ‖p‖ < 1)
    (d : CompactCellAttachment.Disk (ConeCoordinates n)) :
    (firstPunctureInclusion n hn p hp d).val = cone n d := rfl

theorem firstPunctureRetraction_inclusion (n : ℕ) (hn : 0 < n)
    (p : PuncturedStage.Coordinates n 1) (hp : ‖p‖ < 1)
    (d : CompactCellAttachment.Disk (ConeCoordinates n)) :
    firstPunctureRetraction n hn p hp (firstPunctureInclusion n hn p hp d) = d :=
  congrArg (fun k ↦ k d)
    (PuncturedCellAttachment.retraction_baseInclusion (first_isPushout n hn) p hp)

def firstPunctureDeformation (n : ℕ) (hn : 0 < n)
    (p : PuncturedStage.Coordinates n 1) (hp : ‖p‖ < 1) :
    (ContinuousMap.id (firstPunctured n p hp)).HomotopyRel
      ((firstPunctureInclusion n hn p hp).comp (firstPunctureRetraction n hn p hp))
        (Set.range (firstPunctureInclusion n hn p hp)) :=
  PuncturedCellAttachment.deformationRel (first_isPushout n hn) p hp

def secondPunctured (n : ℕ) (p : ConeCoordinates n) (hp : ‖p‖ < 1) :=
  PuncturedCellAttachment.punctured (j := TopCat.ofHom (cone n)) p hp

def secondPunctureInclusion (n : ℕ) (p : ConeCoordinates n) (hp : ‖p‖ < 1) :
    C(SecondStage.Space n, secondPunctured n p hp) :=
  (PuncturedCellAttachment.baseInclusion (isPushout n) p hp).hom

def secondPunctureRetraction (n : ℕ) (p : ConeCoordinates n) (hp : ‖p‖ < 1) :
    C(secondPunctured n p hp, SecondStage.Space n) :=
  (PuncturedCellAttachment.retraction (isPushout n) p hp).hom

theorem secondPunctureInclusion_val (n : ℕ) (p : ConeCoordinates n) (hp : ‖p‖ < 1)
    (w : SecondStage.Space n) : (secondPunctureInclusion n p hp w).val = base n w := rfl

theorem secondPunctureRetraction_inclusion (n : ℕ) (p : ConeCoordinates n) (hp : ‖p‖ < 1)
    (w : SecondStage.Space n) :
    secondPunctureRetraction n p hp (secondPunctureInclusion n p hp w) = w :=
  congrArg (fun k ↦ k w) (PuncturedCellAttachment.retraction_baseInclusion (isPushout n) p hp)

def secondPunctureDeformation (n : ℕ) (p : ConeCoordinates n) (hp : ‖p‖ < 1) :
    (ContinuousMap.id (secondPunctured n p hp)).HomotopyRel
      ((secondPunctureInclusion n p hp).comp (secondPunctureRetraction n p hp))
        (Set.range (secondPunctureInclusion n p hp)) :=
  PuncturedCellAttachment.deformationRel (isPushout n) p hp

end NoExoticSixSphere.JamesSphere.SecondStageCone
