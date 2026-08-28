import Wikipedia.NoExoticSixSphere.JamesStageHomotopyGluing

/-!
# Homotopy extension from the first stage to the actual full James space

Successive genuine stage cofibrations extend a given homotopy while
preserving its prescribed initial map. The recursively chosen extensions
agree on every preceding stage. The proved continuous gluing theorem
therefore gives homotopy extension for the original full inclusion.
-/

noncomputable section

open CategoryTheory
open scoped unitInterval
open Wikipedia.HopfProblem SingularMayerVietoris OrbitPair

namespace NoExoticSixSphere.JamesSphere.FullFirstStageCofibration

open StageHomotopyGluing

variable (n : ℕ) {Z : TopCat.{0}} (f : C(James.Space (Sphere n) (spherePole n), Z))

abbrev Extension (k : ℕ) :=
  {K : C(I × Stage n k, Z) // ∀ w, K (0, w) = f w.val}

theorem exists_next (k : ℕ) (K : Extension n f k) :
    ∃ L : Extension n f (k + 1),
      ∀ t w, L.val (t, StageAttachment.inclusion n (k + 1) w) = K.val (t, w) := by
  obtain ⟨L, hL0, hLK⟩ := StageAttachment.hasHomotopyExtension n (k + 1) Z
    (f.comp (subtypeInclusion (James.stage (spherePole n) (k + 1 + 1)))) K.val K.property
  exact ⟨⟨L, hL0⟩, hLK⟩

def next (k : ℕ) (K : Extension n f k) : Extension n f (k + 1) :=
  Classical.choose (exists_next n f k K)

theorem next_agrees (k : ℕ) (K : Extension n f k) (t : I) (w : Stage n k) :
    (next n f k K).val (t, StageAttachment.inclusion n (k + 1) w) = K.val (t, w) :=
  Classical.choose_spec (exists_next n f k K) t w

variable (H : C(I × Stage n 0, Z)) (h0 : ∀ w, H (0, w) = f w.val)

def family : (k : ℕ) → Extension n f k
  | 0 => ⟨H, h0⟩
  | k + 1 => next n f k (family k)

theorem family_zero (t : I) (w : Stage n 0) :
    (family n f H h0 0).val (t, w) = H (t, w) := rfl

theorem family_agrees (k : ℕ) (t : I) (w : Stage n k) :
    (family n f H h0 (k + 1)).val (t, StageAttachment.inclusion n (k + 1) w) =
      (family n f H h0 k).val (t, w) :=
  next_agrees n f k (family n f H h0 k) t w

include h0 in
theorem exists_extension :
    ∃ G : C(I × James.Space (Sphere n) (spherePole n), Z),
      (∀ w, G (0, w) = f w) ∧ ∀ (t : I) (w : Stage n 0), G (t, w.val) = H (t, w) := by
  let K : ∀ k, C(I × Stage n k, Z) := fun k ↦ (family n f H h0 k).val
  have hK : ∀ k t w, K (k + 1) (t, StageAttachment.inclusion n (k + 1) w) = K k (t, w) :=
    family_agrees n f H h0
  refine ⟨glue n K hK, ?_, ?_⟩
  · intro w
    let v : Stage n (James.size (spherePole n) w) := ⟨w, Nat.le_succ _⟩
    change glue n K hK (0, v.val) = f v.val
    rw [glue_stage]
    exact (family n f H h0 (James.size (spherePole n) w)).property v
  · intro t w
    rw [glue_stage n K hK 0 w t]
    rfl

def inclusion : TopCat.of (Stage n 0) ⟶ TopCat.of (James.Space (Sphere n) (spherePole n)) :=
  TopCat.ofHom (subtypeInclusion (James.stage (spherePole n) 1))

theorem hasHomotopyExtension : HomotopyExtension.HasHomotopyExtension (inclusion n) := by
  intro Z F H h0
  exact exists_extension n F H h0

end NoExoticSixSphere.JamesSphere.FullFirstStageCofibration
