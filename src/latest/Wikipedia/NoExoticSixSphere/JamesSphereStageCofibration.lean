import Wikipedia.NoExoticSixSphere.QuotientAttachment
import Wikipedia.NoExoticSixSphere.FatWedgeCofibration
import Wikipedia.NoExoticSixSphere.JamesSphereSeparation
import Wikipedia.NoExoticSixSphere.JamesWordStrata

/-!
# Cofibrations between successive actual James sphere stages

The Cartesian-power presentation identifies precisely the fat-wedge
locus with the preceding stage. It is injective outside that locus.
The resulting literal quotient-attachment square is a pushout, so the
proved fat-wedge cofibration supplies homotopy extension for the original
stage inclusion. No James comparison equivalence is used.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Set Topology
open Wikipedia.HopfProblem.OrbitPair

namespace NoExoticSixSphere.JamesSphere.StageAttachment

def lower (n k : ℕ) : Set (James.stage (spherePole n) (k + 1)) :=
  {w | w.val ∈ James.stage (spherePole n) k}

def presentation (n k : ℕ) : TopCat.of (Fin (k + 1) → Sphere n) ⟶
    TopCat.of (James.stage (spherePole n) (k + 1)) :=
  TopCat.ofHom (stagePresentation n (k + 1))

def lowerInclusion (n k : ℕ) : TopCat.of (lower n k) ⟶
    TopCat.of (James.stage (spherePole n) (k + 1)) :=
  QuotientAttachment.inclusion (Q := TopCat.of (James.stage (spherePole n) (k + 1))) (lower n k)

theorem boundary_eq (n k : ℕ) :
    stagePresentation n (k + 1) ⁻¹' lower n k = FatWedge.space (spherePole n) (k + 1) := by
  ext v
  change James.size (spherePole n) (James.word (spherePole n) (List.ofFn v)) ≤ k ↔ _
  rw [← Nat.lt_succ_iff, James.size_word_array_lt_iff]
  rfl

theorem fiber_condition (n k : ℕ) (v w : Fin (k + 1) → Sphere n)
    (h : stagePresentation n (k + 1) v = stagePresentation n (k + 1) w) :
    stagePresentation n (k + 1) v ∈ lower n k ∨ v = w := by
  by_cases hv : stagePresentation n (k + 1) v ∈ lower n k
  · exact Or.inl hv
  · right
    have hw : stagePresentation n (k + 1) w ∉ lower n k := h ▸ hv
    have hnv : ∀ i, v i ≠ spherePole n := by
      have hm : v ∉ FatWedge.space (spherePole n) (k + 1) := by
        rw [← boundary_eq]
        exact hv
      exact fun i hi ↦ hm ⟨i, hi⟩
    have hnw : ∀ i, w i ≠ spherePole n := by
      have hm : w ∉ FatWedge.space (spherePole n) (k + 1) := by
        rw [← boundary_eq]
        exact hw
      exact fun i hi ↦ hm ⟨i, hi⟩
    exact James.word_array_injective_of_forall_ne (spherePole n) hnv hnw
      (congrArg Subtype.val h)

theorem isPushout (n k : ℕ) :
    IsPushout
      (QuotientAttachment.boundaryMap (presentation n k) (lower n k))
      (QuotientAttachment.boundaryInclusion (presentation n k) (lower n k))
      (lowerInclusion n k) (presentation n k) :=
  QuotientAttachment.isPushout _ _ (isQuotientMap_stagePresentation n (k + 1))
    (fiber_condition n k)

theorem lower_hasHomotopyExtension (n k : ℕ) :
    HomotopyExtension.HasHomotopyExtension (lowerInclusion n k) := by
  apply QuotientAttachment.hasHomotopyExtension (presentation n k)
    (lower n k) (isQuotientMap_stagePresentation n (k + 1)) (fiber_condition n k)
  change HomotopyExtension.HasHomotopyExtension
    (SubspaceCofibration.inclusion (stagePresentation n (k + 1) ⁻¹' lower n k))
  rw [boundary_eq]
  exact FatWedge.sphere_hasHomotopyExtension (spherePole n) (k + 1)

def lowerHomeomorph (n k : ℕ) : James.stage (spherePole n) k ≃ₜ lower n k where
  toFun w := ⟨⟨w.val, James.stage_mono (spherePole n) (Nat.le_succ k) w.property⟩, w.property⟩
  invFun w := ⟨w.val.val, w.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

def inclusion (n k : ℕ) : TopCat.of (James.stage (spherePole n) k) ⟶
    TopCat.of (James.stage (spherePole n) (k + 1)) :=
  TopCat.ofHom (ContinuousMap.inclusion (James.stage_mono (spherePole n) (Nat.le_succ k)))

theorem inclusion_factor (n k : ℕ) : inclusion n k =
    (TopCat.isoOfHomeo (lowerHomeomorph n k)).hom ≫
      lowerInclusion n k := rfl

theorem hasHomotopyExtension (n k : ℕ) :
    HomotopyExtension.HasHomotopyExtension (inclusion n k) := by
  rw [inclusion_factor]
  exact HomotopyExtension.comp _ _ (HomotopyExtension.of_isIso _)
    (lower_hasHomotopyExtension n k)

theorem isClosedEmbedding (n k : ℕ) : IsClosedEmbedding (inclusion n k) := by
  apply (inclusion n k).hom.continuous.isClosedEmbedding
  intro x y h
  apply Subtype.ext
  exact congrArg (fun w : James.stage (spherePole n) (k + 1) ↦ w.val) h

end NoExoticSixSphere.JamesSphere.StageAttachment
