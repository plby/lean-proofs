import Wikipedia.NoExoticSixSphere.JamesSphereStageCofibration
import Wikipedia.NoExoticSixSphere.CollapsedSubspacePushout

/-!
# Homotopy extension from the first to any finite James stage

This is the literal inclusion, obtained by composing the already proved
successive-stage cofibrations. The lower subspace in each finite stage
is homeomorphic to the original first stage.
-/

noncomputable section

open CategoryTheory
open Wikipedia.HopfProblem.OrbitPair

namespace NoExoticSixSphere.JamesSphere.FirstStageCofibration

abbrev Words (n k : ℕ) := James.stage (spherePole n) (k + 1)

def lower (n k : ℕ) : Set (Words n k) := {w | w.val ∈ James.stage (spherePole n) 1}

def inclusion (n k : ℕ) : TopCat.of (James.stage (spherePole n) 1) ⟶ TopCat.of (Words n k) :=
  TopCat.ofHom (ContinuousMap.inclusion
    (James.stage_mono (spherePole n) (Nat.succ_le_succ (Nat.zero_le k))))

theorem inclusion_next (n k : ℕ) :
    inclusion n (k + 1) = inclusion n k ≫ StageAttachment.inclusion n (k + 1) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro w
  rfl

theorem hasHomotopyExtension (n k : ℕ) :
    HomotopyExtension.HasHomotopyExtension (inclusion n k) := by
  induction k with
  | zero =>
    change HomotopyExtension.HasHomotopyExtension (𝟙 (TopCat.of (James.stage (spherePole n) 1)))
    exact HomotopyExtension.of_isIso _
  | succ k ih =>
    rw [inclusion_next]
    exact HomotopyExtension.comp _ _ ih (StageAttachment.hasHomotopyExtension n (k + 1))

def lowerHomeomorph (n k : ℕ) : James.stage (spherePole n) 1 ≃ₜ lower n k where
  toFun w := ⟨⟨w.val, James.stage_mono (spherePole n)
    (Nat.succ_le_succ (Nat.zero_le k)) w.property⟩, w.property⟩
  invFun w := ⟨w.val.val, w.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

theorem lower_hasHomotopyExtension (n k : ℕ) :
    HomotopyExtension.HasHomotopyExtension (CollapsedSubspacePushout.inclusion (lower n k)) := by
  have he : CollapsedSubspacePushout.inclusion (lower n k) =
      (TopCat.isoOfHomeo (lowerHomeomorph n k)).inv ≫ inclusion n k := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro w
    rfl
  rw [he]
  exact HomotopyExtension.comp _ _ (HomotopyExtension.of_isIso _)
    (hasHomotopyExtension n k)

end NoExoticSixSphere.JamesSphere.FirstStageCofibration
