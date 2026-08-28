import Wikipedia.NoExoticSixSphere.JamesSphereStageCofibration

/-!
# Gluing compatible stage homotopies on the original full James space

The path attached to a word is independent of the sufficiently large
stage used to represent it. Continuity follows from the actual final
word topology, applied to the compact-open path-valued map. Evaluation
then gives a continuous homotopy on the whole space, with exact values
on every original finite stage.
-/

noncomputable section

open scoped unitInterval

namespace NoExoticSixSphere.JamesSphere.StageHomotopyGluing

variable (n : ℕ) {Z : Type*} [TopologicalSpace Z]

abbrev Stage (k : ℕ) := James.stage (spherePole n) (k + 1)

variable (K : ∀ k, C(I × Stage n k, Z))
  (hK : ∀ k t w, K (k + 1) (t, StageAttachment.inclusion n (k + 1) w) = K k (t, w))

include hK in
theorem stage_agreement {k l : ℕ} (hkl : k ≤ l) (t : I) (w : Stage n k) :
    K l (t, ⟨w.val, James.stage_mono (spherePole n) (Nat.succ_le_succ hkl) w.property⟩) =
      K k (t, w) := by
  induction l, hkl using Nat.le_induction with
  | base => rfl
  | succ l hkl ih =>
    exact (hK l t
      ⟨w.val, James.stage_mono (spherePole n) (Nat.succ_le_succ hkl) w.property⟩).trans ih

def stagePath (k : ℕ) (w : Stage n k) : C(I, Z) :=
  (K k).comp ⟨fun t ↦ (t, w), continuous_id.prodMk continuous_const⟩

theorem stagePath_continuous (k : ℕ) : Continuous (stagePath n K k) :=
  ContinuousMap.continuous_of_continuous_uncurry (stagePath n K k)
    ((K k).continuous.comp (continuous_snd.prodMk continuous_fst))

def fullPath (w : James.Space (Sphere n) (spherePole n)) : C(I, Z) :=
  stagePath n K (James.size (spherePole n) w) ⟨w, Nat.le_succ _⟩

include hK in
theorem fullPath_agrees (k : ℕ) (w : Stage n k) (t : I) :
    fullPath n K w.val t = K k (t, w) := by
  have h₁ := stage_agreement n K hK (Nat.le_max_left (James.size (spherePole n) w.val) k)
    t (⟨w.val, Nat.le_succ _⟩ : Stage n (James.size (spherePole n) w.val))
  have h₂ := stage_agreement n K hK (Nat.le_max_right (James.size (spherePole n) w.val) k) t w
  exact h₁.symm.trans h₂

include hK in
theorem fullPath_continuous : Continuous (fullPath n K) := by
  apply (James.continuous_iff_on_words (spherePole n) _).mpr
  intro m
  let W : C(Fin m → Sphere n, Stage n m) :=
    (ContinuousMap.inclusion (James.stage_mono (spherePole n) (Nat.le_succ m))).comp
      (stagePresentation n m)
  have hc := (stagePath_continuous n K m).comp W.continuous
  apply hc.congr
  intro v
  apply ContinuousMap.ext
  intro t
  exact (fullPath_agrees n K hK m (W v) t).symm

def glue : C(I × James.Space (Sphere n) (spherePole n), Z) :=
  ⟨fun p ↦ fullPath n K p.2 p.1,
    continuous_eval.comp (((fullPath_continuous n K hK).comp continuous_snd).prodMk continuous_fst)⟩

theorem glue_stage (k : ℕ) (w : Stage n k) (t : I) :
    glue n K hK (t, w.val) = K k (t, w) :=
  fullPath_agrees n K hK k w t

end NoExoticSixSphere.JamesSphere.StageHomotopyGluing
