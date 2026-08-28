import Wikipedia.HopfProblem.DegreeCollapseIntegralCompactSupportOpenEmbedding

/-!
# The original compact-support map of a homeomorphism is an equivalence

The actual open-embedding maps for a homeomorphism and its inverse are
inverse by the already proved composition and identity formulas. The
resulting equivalence retains the original map on every compact support.
-/

noncomputable section

open TopologicalSpace

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralCompactSupportCohomology

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] [T2Space Y]

omit [T2Space X] in
theorem openMap_congr {f g : C(X, Y)} (hf : Topology.IsOpenEmbedding f)
    (hg : Topology.IsOpenEmbedding g) (hfg : f = g) (p : ℕ) (a : Cohomology X p) :
    openMap f hf p a = openMap g hg p a := by
  subst g
  rfl

theorem homeomorph_left_inverse (e : X ≃ₜ Y) (p : ℕ) :
    Function.LeftInverse (openMap (e.symm : C(Y, X)) e.symm.isOpenEmbedding p)
      (openMap (e : C(X, Y)) e.isOpenEmbedding p) := by
  intro a
  have h := openMap_comp (e : C(X, Y)) e.isOpenEmbedding
    (e.symm : C(Y, X)) e.symm.isOpenEmbedding p a
  exact h.trans ((openMap_congr (e.symm.isOpenEmbedding.comp e.isOpenEmbedding)
    Topology.IsOpenEmbedding.id (Homeomorph.symm_comp_toContinuousMap e) p a).trans
      (openMap_id p a))

def homeomorphEquiv (e : X ≃ₜ Y) (p : ℕ) : Cohomology X p ≃ₗ[ℤ] Cohomology Y p where
  toFun := openMap (e : C(X, Y)) e.isOpenEmbedding p
  invFun := openMap (e.symm : C(Y, X)) e.symm.isOpenEmbedding p
  left_inv := homeomorph_left_inverse e p
  right_inv := homeomorph_left_inverse e.symm p
  map_add' := (openMap (e : C(X, Y)) e.isOpenEmbedding p).map_add
  map_smul' := (openMap (e : C(X, Y)) e.isOpenEmbedding p).map_smul

theorem homeomorphEquiv_toLinearMap (e : X ≃ₜ Y) (p : ℕ) :
    (homeomorphEquiv e p).toLinearMap = openMap (e : C(X, Y)) e.isOpenEmbedding p := rfl

theorem homeomorphEquiv_of (e : X ≃ₜ Y) (p : ℕ) (K : Compacts X) (a : Component X p K) :
    homeomorphEquiv e p (of X p K a) = of Y p (mapCompact (e : C(X, Y)) K)
      (IntegralOpenEmbeddingSupport.extension (e : C(X, Y)) e.isOpenEmbedding
        (K : Set X) K.isCompact (mapCompact (e : C(X, Y)) K : Set Y) rfl p a) := rfl

end Wikipedia.HopfProblem.DegreeCollapse.IntegralCompactSupportCohomology
