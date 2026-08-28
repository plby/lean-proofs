import Wikipedia.HopfProblem.OrbitPairHomotopyExtensionProduct

/-!
# Homotopy extension at the bottom of an actual product cylinder

An explicit extension uses the two coordinate differences in the time
square. The formulas agree on the diagonal. The spatial factor is
unchanged, so the argument works for every topological space.
-/

noncomputable section

universe u

open CategoryTheory unitInterval

namespace Wikipedia.HopfProblem.OrbitPair.HomotopyExtension

def cylinderEndpoint (A : TopCat.{u}) (t : I) : A ⟶ TopCat.of (I × A) :=
  TopCat.ofHom ⟨fun a ↦ (t, a), continuous_const.prodMk continuous_id⟩

theorem cylinderEndpoint_zero (A : TopCat.{u}) :
    HasHomotopyExtension (cylinderEndpoint A 0) := by
  intro Z F G h0
  let D : ℝ → I := Set.projIcc 0 1 zero_le_one
  have hD : Continuous D := continuous_projIcc
  have hDz : D 0 = 0 := Set.projIcc_left _
  have hDu (t : I) : D t = t := Set.projIcc_val _ t
  let H : C(I × (I × A), Z) :=
    ⟨fun p ↦ if (p.1 : ℝ) ≤ (p.2.1 : ℝ) then
        F (D ((p.2.1 : ℝ) - p.1), p.2.2)
      else G (D ((p.1 : ℝ) - p.2.1), p.2.2), by
      apply continuous_if_le
        (continuous_subtype_val.comp continuous_fst)
        (continuous_subtype_val.comp continuous_snd.fst)
      · exact (F.continuous.comp
          ((hD.comp ((continuous_subtype_val.comp continuous_snd.fst).sub
            (continuous_subtype_val.comp continuous_fst))).prodMk continuous_snd.snd)).continuousOn
      · exact (G.continuous.comp
          ((hD.comp ((continuous_subtype_val.comp continuous_fst).sub
            (continuous_subtype_val.comp continuous_snd.fst))).prodMk
              continuous_snd.snd)).continuousOn
      · intro p hp
        change (p.1 : ℝ) = (p.2.1 : ℝ) at hp
        rw [hp, sub_self, hDz]
        exact (h0 p.2.2).symm⟩
  refine ⟨H, ?_, ?_⟩
  · rintro ⟨t, a⟩
    change (if (0 : ℝ) ≤ t then F (D ((t : ℝ) - 0), a)
      else G (D (0 - (t : ℝ)), a)) = F (t, a)
    rw [if_pos t.property.1, sub_zero, hDu]
  · intro s a
    change (if (s : ℝ) ≤ 0 then F (D (0 - (s : ℝ)), a)
      else G (D ((s : ℝ) - 0), a)) = G (s, a)
    by_cases hs : (s : ℝ) ≤ 0
    · have hs0 : s = 0 := Subtype.ext (le_antisymm hs s.property.1)
      subst s
      change (if (0 : ℝ) ≤ 0 then F (D (0 - 0), a)
        else G (D (0 - 0), a)) = G (0, a)
      rw [if_pos le_rfl, sub_self, hDz]
      exact (h0 a).symm
    · rw [if_neg hs, sub_zero, hDu]

end Wikipedia.HopfProblem.OrbitPair.HomotopyExtension
