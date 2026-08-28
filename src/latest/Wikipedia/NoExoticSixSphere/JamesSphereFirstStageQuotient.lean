import Wikipedia.NoExoticSixSphere.JamesSphereSecondStageQuotient

/-!
# The full James quotient by its first stage

This is the quotient of the original, noncompact James space, with the
literal quotient topology. The original James--Hopf map descends because
it kills every word of length at most one. The actual second-stage quotient
injects into this full quotient; no compactification model is substituted.
-/

noncomputable section

namespace NoExoticSixSphere.JamesSphere.FirstStageQuotient

abbrev Space (n : ℕ) := CollapsedSubspace.Space (James.stage (spherePole n) 1)

def quotientMap (n : ℕ) : C(James.Space (Sphere n) (spherePole n), Space n) :=
  CollapsedSubspace.quotientMap (James.stage (spherePole n) 1)

def basepoint (n : ℕ) : Space n := quotientMap n 1

theorem quotientMap_firstStage (n : ℕ) (w : James.Space (Sphere n) (spherePole n))
    (hw : w ∈ James.stage (spherePole n) 1) : quotientMap n w = basepoint n :=
  (CollapsedSubspace.quotientMap_eq_iff (James.stage (spherePole n) 1) w 1).mpr
    (Or.inr ⟨hw, Nat.zero_le 1⟩)

theorem hopf_firstStage (n : ℕ) (w : James.Space (Sphere n) (spherePole n))
    (hw : w ∈ James.stage (spherePole n) 1) : hopf n w = 1 := by
  obtain ⟨v, rfl⟩ := James.exists_array_of_mem_stage (spherePole n) hw
  rw [List.ofFn_succ, List.ofFn_zero, James.word_cons, James.word_nil, mul_one]
  exact hopf_letter n (v 0)

def hopfMap (n : ℕ) : C(Space n, James.Space (Sphere (n + n)) (spherePole (n + n))) :=
  CollapsedSubspace.lift (James.stage (spherePole n) 1) (hopf n)
    (fun w hw z hz ↦ (hopf_firstStage n w hw).trans (hopf_firstStage n z hz).symm)

theorem hopfMap_quotientMap (n : ℕ) (w : James.Space (Sphere n) (spherePole n)) :
    hopfMap n (quotientMap n w) = hopf n w := rfl

theorem hopfMap_basepoint (n : ℕ) : hopfMap n (basepoint n) = 1 := rfl

def stageMap (n : ℕ) : C(SecondStage.QuotientSpace n, Space n) :=
  CollapsedSubspace.lift (StageAttachment.lower n 1)
    ((quotientMap n).comp ⟨Subtype.val, continuous_subtype_val⟩)
    (fun w hw z hz ↦ (CollapsedSubspace.quotientMap_eq_iff
      (James.stage (spherePole n) 1) w.val z.val).mpr (Or.inr ⟨hw, hz⟩))

theorem stageMap_quotientMap (n : ℕ) (w : SecondStage.Space n) :
    stageMap n (SecondStage.quotientMap n w) = quotientMap n w.val := rfl

theorem stageMap_injective (n : ℕ) : Function.Injective (stageMap n) := by
  intro a b
  refine Quotient.inductionOn₂ a b fun w z h ↦ ?_
  change quotientMap n w.val = quotientMap n z.val at h
  rcases (CollapsedSubspace.quotientMap_eq_iff (James.stage (spherePole n) 1)
    w.val z.val).mp h with hwz | ⟨hw, hz⟩
  · exact Quotient.sound (Or.inl (Subtype.ext hwz))
  · exact Quotient.sound (Or.inr ⟨hw, hz⟩)

end NoExoticSixSphere.JamesSphere.FirstStageQuotient
