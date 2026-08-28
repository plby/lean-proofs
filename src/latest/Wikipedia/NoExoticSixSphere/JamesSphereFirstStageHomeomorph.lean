import Wikipedia.NoExoticSixSphere.JamesSphereQuotientBottomSphere

/-!
# The original one-letter map identifies the sphere with the first stage

The homeomorphism has the actual one-letter map as its forward function.
Surjectivity uses the genuine length-one word presentation; compactness
and Hausdorff separation then give continuity of the inverse.
-/

noncomputable section

namespace NoExoticSixSphere.JamesSphere.FirstStage

def letter (n : ℕ) : C(Sphere n, James.stage (spherePole n) 1) :=
  ⟨fun x ↦ ⟨inclusion n x, James.size_letter_le (spherePole n) x⟩,
    (inclusion n).continuous.subtype_mk _⟩

theorem letter_bijective (n : ℕ) : Function.Bijective (letter n) := by
  refine ⟨fun x y h ↦ inclusion_injective n (congrArg Subtype.val h), ?_⟩
  intro w
  obtain ⟨v, hv⟩ := James.exists_array_of_mem_stage (spherePole n) w.property
  refine ⟨v 0, Subtype.ext ?_⟩
  change James.letter (spherePole n) (v 0) = w.val
  simpa only [List.ofFn_succ, List.ofFn_zero, James.word_singleton] using hv

def homeomorph (n : ℕ) : Sphere n ≃ₜ James.stage (spherePole n) 1 :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (letter n) (letter_bijective n)) (letter n).continuous

theorem homeomorph_val (n : ℕ) (x : Sphere n) :
    (homeomorph n x).val = inclusion n x := rfl

theorem homeomorph_pole (n : ℕ) : (homeomorph n (spherePole n)).val = 1 :=
  James.letter_basepoint (spherePole n)

end NoExoticSixSphere.JamesSphere.FirstStage
