import Wikipedia.NoExoticSixSphere.JamesSphereStageCofibration
import Wikipedia.NoExoticSixSphere.JamesLetterAction

/-!
# The actual finite-stage word action and its lower-stage inverse image

Prepending a sphere letter maps the kth stage onto the next stage.
Its value lies in the preceding stage exactly when the tail is shorter
or the prepended letter is the basepoint. These are the attaching maps
and the exact filtration identities for the auxiliary cone spaces.
-/

noncomputable section

open Set Topology

namespace NoExoticSixSphere.JamesSphere

def stageAction (n k : ℕ) : C(Sphere n × James.stage (spherePole n) k,
    James.stage (spherePole n) (k + 1)) :=
  ⟨fun p ↦ ⟨James.letter (spherePole n) p.1 * p.2.val, by
      change James.size (spherePole n) (James.letter (spherePole n) p.1 * p.2.val) ≤ k + 1
      rw [James.size_mul]
      have hl := James.size_letter_le (spherePole n) p.1
      have hw := p.2.property
      change James.size (spherePole n) p.2.val ≤ k at hw
      omega⟩,
    ((James.letterAction (spherePole n)).continuous.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _⟩

theorem stageAction_val (n k : ℕ) (x : Sphere n) (w : James.stage (spherePole n) k) :
    (stageAction n k (x, w)).val = James.letter (spherePole n) x * w.val := rfl

theorem stageAction_pole (n k : ℕ) (w : James.stage (spherePole n) k) :
    stageAction n k (spherePole n, w) = StageAttachment.inclusion n k w := by
  apply Subtype.ext
  change James.letter (spherePole n) (spherePole n) * w.val = w.val
  rw [James.letter_basepoint, one_mul]

theorem stageAction_surjective (n k : ℕ) : Function.Surjective (stageAction n k) := by
  intro w
  obtain ⟨v, hv⟩ := James.exists_array_of_mem_stage (spherePole n) w.property
  refine ⟨(v 0, stagePresentation n k (fun i ↦ v i.succ)), ?_⟩
  apply Subtype.ext
  rw [List.ofFn_succ, James.word_cons] at hv
  exact hv

theorem stageAction_inclusion (n k : ℕ) (x : Sphere n) (w : James.stage (spherePole n) k) :
    StageAttachment.inclusion n (k + 1) (stageAction n k (x, w)) =
      stageAction n (k + 1) (x, StageAttachment.inclusion n k w) := rfl

theorem stageAction_mem_lower_iff (n k : ℕ)
    (x : Sphere n) (w : James.stage (spherePole n) (k + 1)) :
    (stageAction n (k + 1) (x, w)).val ∈ James.stage (spherePole n) (k + 1) ↔
      w.val ∈ James.stage (spherePole n) k ∨ x = spherePole n := by
  by_cases hx : x = spherePole n
  · rw [hx, stageAction_pole]
    exact ⟨fun _ ↦ Or.inr rfl, fun _ ↦ w.property⟩
  · have hs : James.size (spherePole n) (James.letter (spherePole n) x) = 1 := by
      rw [James.letter_of_ne (spherePole n) hx]
      rfl
    change James.size (spherePole n) (James.letter (spherePole n) x * w.val) ≤ k + 1 ↔ _
    rw [James.size_mul, hs, or_iff_left hx]
    change 1 + James.size (spherePole n) w.val ≤ k + 1 ↔ James.size (spherePole n) w.val ≤ k
    omega

end NoExoticSixSphere.JamesSphere
