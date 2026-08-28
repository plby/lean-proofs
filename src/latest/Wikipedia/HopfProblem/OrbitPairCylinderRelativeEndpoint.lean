import Wikipedia.HopfProblem.OrbitPairCylinderEndpoint

/-!
# Extending at one cylinder endpoint while fixing the other

The initial path is compressed into the interval ending at `1 - s/2`;
the remaining interval follows the prescribed endpoint homotopy. This
explicit formula keeps the zero endpoint fixed and is jointly continuous
in every spatial parameter.
-/

noncomputable section

universe u v

open unitInterval

namespace Wikipedia.HopfProblem.OrbitPair.HomotopyExtension

theorem extend_cylinder_one_relative_zero {A : Type u} {Z : Type v}
    [TopologicalSpace A] [TopologicalSpace Z]
    (F G : C(I × A, Z)) (h0 : ∀ a, G (0, a) = F (1, a)) :
    ∃ H : C(I × (I × A), Z),
      (∀ t a, H (0, (t, a)) = F (t, a)) ∧
      (∀ s a, H (s, (0, a)) = F (0, a)) ∧
      ∀ s a, H (s, (1, a)) = G (s, a) := by
  let ρ : I → ℝ := fun s ↦ 1 - (s : ℝ) / 2
  have hρ : Continuous ρ := by fun_prop
  have hρpos (s : I) : 0 < ρ s := by
    dsimp [ρ]
    have hs := s.property.2
    linarith
  let D : ℝ → I := Set.projIcc 0 1 zero_le_one
  have hD : Continuous D := continuous_projIcc
  have hDz : D 0 = 0 := Set.projIcc_left _
  have hDo : D 1 = 1 := Set.projIcc_right _
  have hDu (t : I) : D t = t := Set.projIcc_val _ t
  let H : C(I × (I × A), Z) :=
    ⟨fun p ↦ if (p.2.1 : ℝ) ≤ ρ p.1 then
        F (D ((p.2.1 : ℝ) / ρ p.1), p.2.2)
      else G (D (2 * ((p.2.1 : ℝ) - ρ p.1)), p.2.2), by
      apply continuous_if_le
        (continuous_subtype_val.comp continuous_snd.fst) (hρ.comp continuous_fst)
      · exact (F.continuous.comp
          ((hD.comp ((continuous_subtype_val.comp continuous_snd.fst).div
            (hρ.comp continuous_fst) (fun p ↦ (hρpos p.1).ne'))).prodMk
              continuous_snd.snd)).continuousOn
      · exact (G.continuous.comp
          ((hD.comp (continuous_const.mul
            ((continuous_subtype_val.comp continuous_snd.fst).sub
              (hρ.comp continuous_fst)))).prodMk continuous_snd.snd)).continuousOn
      · intro p hp
        change (p.2.1 : ℝ) = ρ p.1 at hp
        rw [hp, div_self (hρpos p.1).ne', sub_self, mul_zero, hDz, hDo]
        exact (h0 p.2.2).symm⟩
  refine ⟨H, ?_, ?_, ?_⟩
  · intro t a
    change (if (t : ℝ) ≤ 1 - (0 : ℝ) / 2 then
      F (D ((t : ℝ) / (1 - (0 : ℝ) / 2)), a) else _) = _
    rw [zero_div, sub_zero, if_pos t.property.2, div_one, hDu]
  · intro s a
    change (if (0 : ℝ) ≤ ρ s then F (D (0 / ρ s), a) else _) = _
    rw [if_pos (hρpos s).le, zero_div, hDz]
  · intro s a
    change (if (1 : ℝ) ≤ ρ s then F (D (1 / ρ s), a)
      else G (D (2 * (1 - ρ s)), a)) = G (s, a)
    by_cases hs : (1 : ℝ) ≤ ρ s
    · have hs0 : s = 0 := by
        apply Subtype.ext
        change (s : ℝ) = 0
        dsimp [ρ] at hs
        have hs' := s.property.1
        linarith
      subst s
      have hρ0 : ρ 0 = 1 := by simp [ρ]
      rw [hρ0, if_pos le_rfl, div_one, hDo]
      exact (h0 a).symm
    · have he : 2 * (1 - ρ s) = (s : ℝ) := by dsimp [ρ]; ring
      rw [if_neg hs, he, hDu]

end Wikipedia.HopfProblem.OrbitPair.HomotopyExtension
