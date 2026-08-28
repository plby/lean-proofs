import Wikipedia.HopfProblem.DegreeCollapseIntegralCompactSupportCohomology

/-!
# A fixed actual support computes compact-support cohomology

If the original extension from one compact support is an isomorphism on
a cofinal family of larger compact supports, its original directed-limit
map is bijective. The proof uses original supported representatives and
the actual common-support equality criterion.
-/

noncomputable section

open Function TopologicalSpace

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralCompactSupportCohomology

variable (X : Type) [TopologicalSpace X] (p : ℕ) (K : Compacts X)

theorem of_bijective_of_cofinal_extensions
    (h : ∀ L : Compacts X, ∃ (N : Compacts X) (hK : K ≤ N) (_hL : L ≤ N),
      Bijective (transition X p K N hK)) : Bijective (of X p K) := by
  constructor
  · intro a b hab
    obtain ⟨L, hKL, _, hL⟩ := (of_eq_iff X p K K a b).mp hab
    obtain ⟨N, hKN, hLN, hN⟩ := h L
    apply hN.1
    have ht (c : Component X p K) :
        transition X p K N hKN c =
          transition X p L N hLN (transition X p K L hKL c) :=
      LinearMap.congr_fun (IntegralSupportedCohomology.extend_trans hKL hLN p) c
    exact (ht a).trans ((congrArg (transition X p L N hLN) hL).trans (ht b).symm)
  · intro a
    obtain ⟨L, b, rfl⟩ := exists_representative X p a
    obtain ⟨N, hKN, hLN, hN⟩ := h L
    obtain ⟨c, hc⟩ := hN.2 (transition X p L N hLN b)
    refine ⟨c, (of_transition X p hKN c).symm.trans ?_⟩
    rw [hc]
    exact of_transition X p hLN b

end Wikipedia.HopfProblem.DegreeCollapse.IntegralCompactSupportCohomology
