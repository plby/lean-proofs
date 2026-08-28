import Wikipedia.NoExoticSixSphere.JamesSphereQuotientTransitions
import Wikipedia.NoExoticSixSphere.JamesSphereCellCharts
import Wikipedia.NoExoticSixSphere.NormedDiskHomology

/-!
# The genuine later cell attachments of the finite James quotient

The original characteristic disk of dimension `(k + 3) * n` presents
the next finite quotient. Its boundary maps precisely into the preceding
quotient; outside the boundary its fibers are singletons. The literal
quotient-attachment square is a pushout with the actual disk cofibration.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Set Metric Topology
open Wikipedia.HopfProblem.OrbitPair

namespace NoExoticSixSphere.JamesSphere.FirstStageQuotient.CellAttachment

def lower (n k : ℕ) : Set (FiniteStage.Space n (k + 2)) :=
  Set.range (FiniteStage.transition n (Nat.le_succ (k + 1)))

def presentation (n k : ℕ) :
    C(NormedDiskHomology.Disk (Fin ((k + 3) * n) → ℝ), FiniteStage.Space n (k + 2)) :=
  (FiniteStage.quotientMap n (k + 2)).comp (Cell.closedPresentation n (k + 3))

theorem presentation_mem_lower_iff (n k : ℕ)
    (x : NormedDiskHomology.Disk (Fin ((k + 3) * n) → ℝ)) :
    presentation n k x ∈ lower n k ↔
      James.size (spherePole n) (Cell.characteristic n (k + 3) x.val) ≤ k + 2 :=
  FiniteStage.quotientMap_mem_range_transition n (Nat.le_succ (k + 1))
    (Cell.closedPresentation n (k + 3) x)

theorem boundary_eq (n k : ℕ) :
    presentation n k ⁻¹' lower n k = NormedDiskHomology.boundary (Fin ((k + 3) * n) → ℝ) := by
  ext x
  change presentation n k x ∈ lower n k ↔ x.val ∈ sphere (0 : Fin ((k + 3) * n) → ℝ) 1
  rw [presentation_mem_lower_iff]
  constructor
  · intro hx
    apply mem_sphere.mpr
    have hle := mem_closedBall.mp x.property
    have hnot : ¬dist x.val 0 < 1 := by
      intro hb
      have he := (Cell.size_characteristic_eq_iff n (k + 3) x.val).mpr hb
      omega
    exact le_antisymm hle (le_of_not_gt hnot)
  · intro hx
    have h := Cell.boundary_size_lt n (k + 3) hx
    omega

theorem presentation_surjective (n k : ℕ) (hn : 0 < n) :
    Function.Surjective (presentation n k) :=
  (CollapsedSubspace.isQuotientMap (FirstStageCofibration.lower n (k + 2))).surjective.comp
    (Cell.closedPresentation_surjective n (k + 3) hn)

theorem isQuotientMap_presentation (n k : ℕ) (hn : 0 < n) :
    IsQuotientMap (presentation n k) :=
  IsQuotientMap.of_surjective_continuous (presentation_surjective n k hn)
    (presentation n k).continuous

theorem fiber_condition (n k : ℕ)
    (x y : NormedDiskHomology.Disk (Fin ((k + 3) * n) → ℝ))
    (h : presentation n k x = presentation n k y) :
    presentation n k x ∈ lower n k ∨ x = y := by
  by_cases hx : presentation n k x ∈ lower n k
  · exact Or.inl hx
  · right
    have hy : presentation n k y ∉ lower n k := h ▸ hx
    have hxle := Cell.characteristic_mem_stage n (k + 3) x.val
    have hyle := Cell.characteristic_mem_stage n (k + 3) y.val
    change James.size (spherePole n) (Cell.characteristic n (k + 3) x.val) ≤ k + 3 at hxle
    change James.size (spherePole n) (Cell.characteristic n (k + 3) y.val) ≤ k + 3 at hyle
    have hxnot := mt (presentation_mem_lower_iff n k x).mpr hx
    have hynot := mt (presentation_mem_lower_iff n k y).mpr hy
    have hxi : x.val ∈ ball 0 1 :=
      (Cell.size_characteristic_eq_iff n (k + 3) x.val).mp (by omega)
    have hyi : y.val ∈ ball 0 1 :=
      (Cell.size_characteristic_eq_iff n (k + 3) y.val).mp (by omega)
    rcases (CollapsedSubspace.quotientMap_eq_iff (FirstStageCofibration.lower n (k + 2))
      (Cell.closedPresentation n (k + 3) x) (Cell.closedPresentation n (k + 3) y)).mp h with
      he | ⟨hxA, _⟩
    · exact Subtype.ext (Cell.injOn_ball n (k + 3) hxi hyi (congrArg Subtype.val he))
    · change James.size (spherePole n) (Cell.characteristic n (k + 3) x.val) ≤ 1 at hxA
      omega

def presentationMorphism (n k : ℕ) :
    TopCat.of (NormedDiskHomology.Disk (Fin ((k + 3) * n) → ℝ)) ⟶
      TopCat.of (FiniteStage.Space n (k + 2)) := TopCat.ofHom (presentation n k)

def lowerInclusion (n k : ℕ) :
    TopCat.of (lower n k) ⟶ TopCat.of (FiniteStage.Space n (k + 2)) :=
  QuotientAttachment.inclusion (Q := TopCat.of (FiniteStage.Space n (k + 2))) (lower n k)

theorem isPushout (n k : ℕ) (hn : 0 < n) :
    IsPushout
      (QuotientAttachment.boundaryInclusion (presentationMorphism n k) (lower n k))
      (QuotientAttachment.boundaryMap (presentationMorphism n k) (lower n k))
      (presentationMorphism n k) (lowerInclusion n k) :=
  (QuotientAttachment.isPushout (presentationMorphism n k) (lower n k)
    (isQuotientMap_presentation n k hn) (fiber_condition n k)).flip

theorem boundary_hasHomotopyExtension (n k : ℕ) :
    HomotopyExtension.HasHomotopyExtension
      (QuotientAttachment.boundaryInclusion (presentationMorphism n k) (lower n k)) := by
  change HomotopyExtension.HasHomotopyExtension
    (SubspaceCofibration.inclusion (presentation n k ⁻¹' lower n k))
  rw [boundary_eq]
  exact NormedDiskHomology.boundary_hasHomotopyExtension (Fin ((k + 3) * n) → ℝ)

def lowerHomeomorph (n k : ℕ) : FiniteStage.Space n (k + 1) ≃ₜ lower n k :=
  FiniteStage.transitionRangeHomeomorph n (Nat.le_succ (k + 1))

theorem transition_factor (n k : ℕ) :
    (lowerInclusion n k).hom.comp (lowerHomeomorph n k : C(_, _)) =
      FiniteStage.transition n (Nat.le_succ (k + 1)) := rfl

end NoExoticSixSphere.JamesSphere.FirstStageQuotient.CellAttachment
