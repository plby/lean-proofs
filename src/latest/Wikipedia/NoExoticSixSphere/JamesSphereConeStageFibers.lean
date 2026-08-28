import Wikipedia.NoExoticSixSphere.JamesSphereConeStagePreimage

/-!
# All nontrivial cone-stage fibers lie over the preceding stage

Two non-basepoint initial letters in a reduced word can be recovered
uniquely, together with their tails. Thus every nontrivial identification
in the cone-stage presentation has a cone-point representative and lies
in the preceding auxiliary stage. This is the exact fiber condition
needed to descend the relative compression homotopy.
-/

noncomputable section

open Set Topology

namespace NoExoticSixSphere.JamesSphere.ConeStage

theorem stageAction_injective_of_nonbase (n k : ℕ)
    {a b : Sphere n × James.stage (spherePole n) k}
    (ha : a.1 ≠ spherePole n) (hb : b.1 ≠ spherePole n)
    (h : stageAction n k a = stageAction n k b) : a = b := by
  have he := congrArg (James.letters (spherePole n)) (congrArg Subtype.val h)
  change James.letters (spherePole n) (James.letter (spherePole n) a.1 * a.2.val) =
    James.letters (spherePole n) (James.letter (spherePole n) b.1 * b.2.val) at he
  rw [James.letters_letter_mul (spherePole n) ha,
    James.letters_letter_mul (spherePole n) hb] at he
  have hc := List.cons.inj he
  apply Prod.ext hc.1
  apply Subtype.ext
  have ht := congrArg (James.word (spherePole n)) hc.2
  simpa only [James.word_letters] using ht

theorem quotient_fiber_condition (n k : ℕ)
    (p q : ReducedCone.Space n × James.stage (spherePole n) (k + 1))
    (h : quotientMap n (k + 1) p = quotientMap n (k + 1) q) :
    quotientMap n (k + 1) p ∈ preceding n k ∨ p = q := by
  rcases (quotient_eq_iff n (k + 1) p q).mp h with he | ⟨a, b, ha, hb, hab⟩
  · exact Or.inr he
  · by_cases hx : a.1 = spherePole n
    · have hc : ReducedCone.boundary n a.1 = p.1 := congrArg Prod.fst ha
      have hp : p.1 = ReducedCone.base n :=
        hc.symm.trans ((congrArg (ReducedCone.boundary n) hx).trans (ReducedCone.boundary_pole n))
      exact Or.inl ((quotient_mem_preceding_iff n k p.1 p.2).mpr (Or.inr hp))
    · by_cases hy : b.1 = spherePole n
      · have hc : ReducedCone.boundary n b.1 = q.1 := congrArg Prod.fst hb
        have hq : q.1 = ReducedCone.base n :=
          hc.symm.trans ((congrArg (ReducedCone.boundary n) hy).trans (ReducedCone.boundary_pole n))
        have hm := (quotient_mem_preceding_iff n k q.1 q.2).mpr (Or.inr hq)
        exact Or.inl (h.symm ▸ hm)
      · have he := stageAction_injective_of_nonbase n (k + 1) hx hy hab
        have he' : (ReducedCone.boundary n a.1, a.2) = (ReducedCone.boundary n b.1, b.2) :=
          congrArg (fun z : Sphere n × James.stage (spherePole n) (k + 1) ↦
            (ReducedCone.boundary n z.1, z.2)) he
        exact Or.inr (ha.symm.trans (he'.trans hb))

end NoExoticSixSphere.JamesSphere.ConeStage
