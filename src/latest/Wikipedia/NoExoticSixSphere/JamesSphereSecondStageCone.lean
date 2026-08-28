import Wikipedia.NoExoticSixSphere.CompactCellAttachment
import Wikipedia.NoExoticSixSphere.JamesSpherePuncturedStage
import Wikipedia.NoExoticSixSphere.JamesSphereFirstStageHomeomorph
import Wikipedia.NoExoticSixSphere.JamesSphereSecondStageQuotient

/-!
# The actual two-cell cone model for the second James stage

Attach the literal `(n+1)`-disk along the original one-letter sphere in
the second James stage. The resulting concrete space is compact Hausdorff.
The original `2n`-cell and the attached disk interior have disjoint open
Euclidean charts. The map collapsing the attached disk is constructed
with the original second-stage quotient as its exact restriction.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Set Metric Topology TopologicalSpace

namespace NoExoticSixSphere.JamesSphere.SecondStageCone

abbrev ConeCoordinates (n : ℕ) := EuclideanSpace ℝ (Fin (n + 1))

def attaching (n : ℕ) : C(Sphere n, SecondStage.Space n) :=
  (StageAttachment.inclusion n 1).hom.comp (FirstStage.letter n)

theorem attaching_val (n : ℕ) (x : Sphere n) : (attaching n x).val = inclusion n x := rfl

abbrev Space (n : ℕ) := CompactCellAttachment.Space (attaching n)

def base (n : ℕ) : C(SecondStage.Space n, Space n) :=
  CompactCellAttachment.base (attaching n)

def cone (n : ℕ) : C(CompactCellAttachment.Disk (ConeCoordinates n), Space n) :=
  CompactCellAttachment.cell (attaching n)

theorem isPushout (n : ℕ) : IsPushout (TopCat.ofHom (attaching n))
    PuncturedCellAttachment.boundary (TopCat.ofHom (base n)) (TopCat.ofHom (cone n)) :=
  CompactCellAttachment.isPushout (attaching n)

theorem cone_boundary (n : ℕ) (x : Sphere n) :
    cone n (PuncturedCellAttachment.boundary x) = base n (attaching n x) :=
  CompactCellAttachment.cell_boundary (attaching n) x

theorem base_isClosedEmbedding (n : ℕ) : IsClosedEmbedding (base n) :=
  CompactCellAttachment.base_isClosedEmbedding (attaching n)

theorem attaching_injective (n : ℕ) : Function.Injective (attaching n) := by
  intro x y he
  exact inclusion_injective n (congrArg Subtype.val he)

theorem cone_isClosedEmbedding (n : ℕ) : IsClosedEmbedding (cone n) := by
  have ha : IsClosedEmbedding (TopCat.ofHom (attaching n)) :=
    (attaching n).continuous.isClosedEmbedding (attaching_injective n)
  exact Wikipedia.HopfProblem.OrbitPair.ClosedPushout.other_isClosedEmbedding (isPushout n) ha

def firstInterior (n : ℕ) :
    TopCat.of (ball (0 : PuncturedStage.Coordinates n 1) 1) ⟶ TopCat.of (SecondStage.Space n) :=
  CellAttachmentChart.ballInclusion ≫ PuncturedStage.presentation n 1

theorem firstInterior_not_attaching (n : ℕ)
    (x : ball (0 : PuncturedStage.Coordinates n 1) 1) :
    firstInterior n x ∉ Set.range (TopCat.ofHom (attaching n)) := by
  rintro ⟨s, hs⟩
  have hsize := (Cell.size_characteristic_eq_iff n 2 x.val).mpr x.property
  have he : inclusion n s = Cell.characteristic n 2 x.val := congrArg Subtype.val hs
  have hle : James.size (spherePole n) (inclusion n s) ≤ 1 :=
    James.size_letter_le (spherePole n) s
  rw [he, hsize] at hle
  omega

theorem firstInterior_isOpenEmbedding (n : ℕ) (hn : 0 < n) :
    IsOpenEmbedding (firstInterior n) :=
  CellAttachmentChart.characteristic_isOpenEmbedding (PuncturedStage.isPushout n 1 hn)

def firstCharacteristic (n : ℕ) :
    TopCat.of (ball (0 : PuncturedStage.Coordinates n 1) 1) ⟶ TopCat.of (Space n) :=
  firstInterior n ≫ TopCat.ofHom (base n)

theorem firstCharacteristic_isOpenEmbedding (n : ℕ) (hn : 0 < n) :
    IsOpenEmbedding (firstCharacteristic n) :=
  PushoutOutsideAttachment.comp_isOpenEmbedding (isPushout n).flip (firstInterior n)
    (firstInterior_not_attaching n) (firstInterior_isOpenEmbedding n hn)

def firstOpenCell (n : ℕ) (hn : 0 < n) : Opens (Space n) :=
  ⟨Set.range (firstCharacteristic n), (firstCharacteristic_isOpenEmbedding n hn).isOpen_range⟩

def firstChart (n : ℕ) (hn : 0 < n) : (Fin (2 * n) → ℝ) ≃ₜ firstOpenCell n hn :=
  Homeomorph.unitBall.trans (firstCharacteristic_isOpenEmbedding n hn).isEmbedding.toHomeomorph

def secondOpenCell (n : ℕ) : Opens (Space n) := CellAttachmentChart.openCell (isPushout n)

def secondChart (n : ℕ) : (Fin (n + 1) → ℝ) ≃ₜ secondOpenCell n :=
  (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm.toHomeomorph.trans
    (CellAttachmentChart.chart (isPushout n))

theorem firstOpenCell_subset_base (n : ℕ) (hn : 0 < n) :
    (firstOpenCell n hn : Set (Space n)) ⊆ Set.range (base n) := by
  rintro z ⟨x, rfl⟩
  exact Set.mem_range_self (firstInterior n x)

theorem cells_disjoint (n : ℕ) (hn : 0 < n) :
    Disjoint (firstOpenCell n hn : Set (Space n)) (secondOpenCell n : Set (Space n)) :=
  ((CellAttachmentChart.openCell_disjoint_base (isPushout n)).mono_right
    (firstOpenCell_subset_base n hn)).symm

def quotientBasepoint (n : ℕ) : SecondStage.QuotientSpace n :=
  SecondStage.quotientMap n ⟨1, Nat.zero_le 2⟩

theorem quotient_attaching (n : ℕ) (s : Sphere n) :
    SecondStage.quotientMap n (attaching n s) = quotientBasepoint n := by
  apply (SecondStage.quotientMap_eq_iff n _ _).mpr
  exact Or.inr ⟨James.size_letter_le (spherePole n) s, Nat.zero_le 1⟩

def collapse (n : ℕ) : C(Space n, SecondStage.QuotientSpace n) :=
  CompactCellAttachment.glue (attaching n) (SecondStage.quotientMap n)
    (ContinuousMap.const _ (quotientBasepoint n)) (quotient_attaching n)

theorem collapse_base (n : ℕ) (w : SecondStage.Space n) :
    collapse n (base n w) = SecondStage.quotientMap n w :=
  CompactCellAttachment.glue_base (attaching n) (SecondStage.quotientMap n)
    (ContinuousMap.const _ (quotientBasepoint n)) (quotient_attaching n) w

theorem collapse_cone (n : ℕ) (x : CompactCellAttachment.Disk (ConeCoordinates n)) :
    collapse n (cone n x) = quotientBasepoint n :=
  CompactCellAttachment.glue_cell (attaching n) (SecondStage.quotientMap n)
    (ContinuousMap.const _ (quotientBasepoint n)) (quotient_attaching n) x

end NoExoticSixSphere.JamesSphere.SecondStageCone
