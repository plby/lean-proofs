import ErdosProblems.Erdos1148.CompactCoreLifts

/-! # Uniformly bounded representatives over any compact quotient subset -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

theorem exists_compact_bounded_lifts {K : Set ModularOrbitSpace} (hK : IsCompact K) :
    ∃ A : ℝ, 0 < A ∧ ∀ x ∈ K,
      ∃ g : SL(2, ℝ), modularMk g = x ∧ ∀ i j : Fin 2, |g i j| ≤ A := by
  let U : ℝ → Set ModularOrbitSpace := fun A =>
    modularMk '' {g : SL(2, ℝ) | ∀ i j : Fin 2, |g i j| < A}
  have hopen (A : ℝ) : IsOpen (U A) := by
    apply (MulAction.isOpenQuotientMap_quotientMk (Γ := SL(2, ℤ))
      (T := SL(2, ℝ))).isOpenMap
    simp only [Set.setOf_forall]
    apply isOpen_iInter_of_finite
    intro i
    apply isOpen_iInter_of_finite
    intro j
    exact isOpen_lt (continuous_realMatrixEntry i j).abs continuous_const
  have hmono : Monotone U := by
    intro A B hAB
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨g, fun i j => (hg i j).trans_le hAB, rfl⟩
  have hcover : K ⊆ ⋃ A : ℝ, U A := by
    intro x _
    induction x using Quotient.inductionOn with
    | h g =>
      let A := |g 0 0| + |g 0 1| + |g 1 0| + |g 1 1| + 1
      refine Set.mem_iUnion.mpr ⟨A, ⟨g, ?_, rfl⟩⟩
      simp only [Fin.forall_fin_two]
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> dsimp only [A] <;>
        linarith [abs_nonneg (g 0 0), abs_nonneg (g 0 1),
          abs_nonneg (g 1 0), abs_nonneg (g 1 1)]
  obtain ⟨A, hsub⟩ := hK.elim_directed_cover U hopen hcover
    (fun A B => ⟨max A B, hmono (le_max_left _ _), hmono (le_max_right _ _)⟩)
  refine ⟨max A 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro x hx
  obtain ⟨g, hg, hmk⟩ := hsub hx
  exact ⟨g, hmk, fun i j => (hg i j).le.trans (le_max_left _ _)⟩

theorem exists_compact_integral_bounded_lifts {K : Set ModularOrbitSpace} (hK : IsCompact K) :
    ∃ A : ℝ, 0 < A ∧ ∀ g : SL(2, ℝ), modularMk g ∈ K →
      ∃ γ : SL(2, ℤ), ∀ i j : Fin 2, |((γ : SL(2, ℝ)) * g) i j| ≤ A := by
  obtain ⟨A, hA, hlift⟩ := exists_compact_bounded_lifts hK
  refine ⟨A, hA, ?_⟩
  intro g hg
  obtain ⟨h, hmk, hh⟩ := hlift (modularMk g) hg
  obtain ⟨γ, hγ⟩ := (modularMk_eq_iff g h).mp hmk.symm
  exact ⟨γ, by simpa only [hγ] using hh⟩

end Erdos1148.DukeArithmetic
