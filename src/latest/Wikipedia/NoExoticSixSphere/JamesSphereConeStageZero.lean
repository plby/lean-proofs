import Wikipedia.NoExoticSixSphere.JamesSphereConeStage

/-!
# The first auxiliary James cone space is the actual reduced cone

The zero-word tail is unique. The attaching map on that tail is
injective, so the quotient makes no further identifications in the
cone. The resulting concrete homeomorphism supplies the base case for
the cone-stage contractibility induction.
-/

noncomputable section

open Set Topology

namespace NoExoticSixSphere.JamesSphere.ConeStage

def zeroTail (n : ℕ) : James.stage (spherePole n) 0 :=
  ⟨1, by change James.size (spherePole n) 1 ≤ 0; rw [James.size_one]⟩

theorem zeroTail_val (n : ℕ) (w : James.stage (spherePole n) 0) : w.val = 1 :=
  (James.size_eq_zero_iff (spherePole n) w.val).mp (Nat.eq_zero_of_le_zero w.property)

instance (n : ℕ) : Subsingleton (James.stage (spherePole n) 0) where
  allEq x y := Subtype.ext ((zeroTail_val n x).trans (zeroTail_val n y).symm)

def fromCone (n : ℕ) : C(ReducedCone.Space n, Space n 0) :=
  (quotientMap n 0).comp ⟨fun c ↦ (c, zeroTail n), continuous_id.prodMk continuous_const⟩

theorem stageAction_zero_injective (n : ℕ) : Function.Injective (stageAction n 0) := by
  intro a b h
  apply Prod.ext
  · have hletter : James.letter (spherePole n) a.1 = James.letter (spherePole n) b.1 := by
      have hv := congrArg Subtype.val h
      change James.letter (spherePole n) a.1 * a.2.val =
        James.letter (spherePole n) b.1 * b.2.val at hv
      simpa only [zeroTail_val, mul_one] using hv
    have hm := congrArg (mooreComparison n) hletter
    rw [mooreComparison_letter, mooreComparison_letter] at hm
    exact mooreGenerator_injective n hm
  · exact Subsingleton.elim _ _

theorem fromCone_injective (n : ℕ) : Function.Injective (fromCone n) := by
  intro c d h
  rcases (quotient_eq_iff n 0 (c, zeroTail n) (d, zeroTail n)).mp h with he |
      ⟨a, b, ha, hb, hab⟩
  · exact congrArg Prod.fst he
  · have he := stageAction_zero_injective n hab
    have hc : ReducedCone.boundary n a.1 = c := congrArg Prod.fst ha
    have hd : ReducedCone.boundary n b.1 = d := congrArg Prod.fst hb
    have habx : a.1 = b.1 := congrArg Prod.fst he
    exact hc.symm.trans ((congrArg (ReducedCone.boundary n) habx).trans hd)

theorem fromCone_surjective (n : ℕ) : Function.Surjective (fromCone n) := by
  intro p
  obtain ⟨⟨c, w⟩, rfl⟩ := (quotientMap_isQuotientMap n 0).surjective p
  refine ⟨c, ?_⟩
  exact congrArg (fun z ↦ quotientMap n 0 (c, z)) (Subsingleton.elim (zeroTail n) w)

def zeroHomeomorph (n : ℕ) : ReducedCone.Space n ≃ₜ Space n 0 :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (fromCone n) ⟨fromCone_injective n, fromCone_surjective n⟩)
    (fromCone n).continuous

theorem zeroHomeomorph_apply (n : ℕ) (c : ReducedCone.Space n) :
    zeroHomeomorph n c = quotientMap n 0 (c, zeroTail n) := rfl

instance (n : ℕ) : ContractibleSpace (Space n 0) :=
  (zeroHomeomorph n).symm.contractibleSpace

end NoExoticSixSphere.JamesSphere.ConeStage
