import Wikipedia.HopfProblem.OrbitPairSimplexInitialFace

/-!
# The actual regularity pushout

Initial-vertex injectivity identifies the pullback of the generated
zeroth-face subcomplex. The characteristic map is surjective onto its
generated subcomplex and injective off that face. The corresponding
degreewise squares of types are pushouts, hence so is the native square
of simplicial sets.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Simplicial

namespace Wikipedia.HopfProblem.OrbitPair.InitialFace

variable {X : SSet.{u}} {n : ℕ} (z : X _⦋n + 1⦌) (hz : InitialInjective z)

include hz

theorem pullback_app (l : ℕ) :
    IsPullback ((SSet.Subcomplex.toOfSimplex (X.δ 0 z)).app (Opposite.op ⦋l⦌))
      ((SSet.stdSimplex.δ (0 : Fin (n + 2))).app (Opposite.op ⦋l⦌))
      ((inclusion z).app (Opposite.op ⦋l⦌))
      ((SSet.Subcomplex.toOfSimplex z).app (Opposite.op ⦋l⦌)) := by
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨NatTrans.congr_app (square z) (Opposite.op ⦋l⦌), ?_, ?_⟩
  · intro a b h
    apply SSet.stdSimplex.objEquiv.injective
    apply (cancel_mono (SimplexCategory.δ (0 : Fin (n + 2)))).mp
    exact congrArg SSet.stdSimplex.objEquiv h.2
  · intro a b h
    have hv : a.val = X.map (SSet.stdSimplex.objEquiv b).op z := congrArg Subtype.val h
    have hm : X.map (SSet.stdSimplex.objEquiv b).op z ∈
        (SSet.Subcomplex.ofSimplex (X.δ 0 z)).obj (Opposite.op ⦋l⦌) := by
      rw [← hv]
      exact a.property
    have hb := (map_mem_initialFace_iff z hz (SSet.stdSimplex.objEquiv b)).mp hm
    obtain ⟨c, hc⟩ := (std_mem_range_delta_zero_iff b).mpr hb
    refine ⟨c, ?_, hc⟩
    apply (injective_of_mono ((inclusion z).app (Opposite.op ⦋l⦌)))
    have hw := congrArg (fun f ↦ f.app (Opposite.op ⦋l⦌) c) (square z)
    change (inclusion z).app (Opposite.op ⦋l⦌)
      ((SSet.Subcomplex.toOfSimplex (X.δ 0 z)).app (Opposite.op ⦋l⦌) c) =
        (SSet.Subcomplex.toOfSimplex z).app (Opposite.op ⦋l⦌)
          ((SSet.stdSimplex.δ (0 : Fin (n + 2))).app (Opposite.op ⦋l⦌) c) at hw
    rw [hc] at hw
    exact hw.trans h.symm

theorem pullback : IsPullback (SSet.Subcomplex.toOfSimplex (X.δ 0 z))
    (SSet.stdSimplex.δ (0 : Fin (n + 2))) (inclusion z) (SSet.Subcomplex.toOfSimplex z) := by
  apply IsPullback.of_forall_isPullback_app
  rintro ⟨⟨l⟩⟩
  exact pullback_app z hz l

theorem pushout_app (l : ℕ) :
    IsPushout ((SSet.Subcomplex.toOfSimplex (X.δ 0 z)).app (Opposite.op ⦋l⦌))
      ((SSet.stdSimplex.δ (0 : Fin (n + 2))).app (Opposite.op ⦋l⦌))
      ((inclusion z).app (Opposite.op ⦋l⦌))
      ((SSet.Subcomplex.toOfSimplex z).app (Opposite.op ⦋l⦌)) := by
  apply Types.isPushout_of_isPullback_of_mono' (pullback_app z hz l)
  · apply Set.eq_univ_of_forall
    intro a
    exact Or.inr (surjective_of_epi ((SSet.Subcomplex.toOfSimplex z).app (Opposite.op ⦋l⦌)) a)
  · intro a b ha hb hab
    apply SSet.stdSimplex.objEquiv.injective
    have hf : (SSet.stdSimplex.objEquiv a).toOrderHom 0 = 0 := by
      by_contra hf
      exact ha ((std_mem_range_delta_zero_iff a).mpr hf)
    apply hz l (SSet.stdSimplex.objEquiv a) (SSet.stdSimplex.objEquiv b) hf
    exact congrArg Subtype.val hab

theorem pushout : IsPushout (SSet.Subcomplex.toOfSimplex (X.δ 0 z))
    (SSet.stdSimplex.δ (0 : Fin (n + 2))) (inclusion z) (SSet.Subcomplex.toOfSimplex z) := by
  apply IsPushout.of_forall_isPushout_app
  rintro ⟨⟨l⟩⟩
  exact pushout_app z hz l

end Wikipedia.HopfProblem.OrbitPair.InitialFace
