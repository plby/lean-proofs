import Wikipedia.NoExoticSixSphere.CompactSupportOpenEmbedding

/-!
# Homeomorphism equivalences for actual compact-support cohomology

The forward and inverse maps are the original open-embedding extensions.
Their actual composition law proves the inverse identities on the
genuine compact-support direct limits.
-/

noncomputable section

namespace NoExoticSixSphere.CompactSupportCohomology

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] [T2Space Y]

/-- The two original extensions for a homeomorphism and its inverse cancel. -/
theorem openMap_homeomorph_inverse (e : X ≃ₜ Y) (p : ℕ) (a : Cohomology X p) :
    openMap (e.symm : C(Y, X)) e.symm.isOpenEmbedding p
        (openMap (e : C(X, Y)) e.isOpenEmbedding p a) = a := by
  have he : (e.symm : C(Y, X)).comp (e : C(X, Y)) = ContinuousMap.id X := by
    ext x
    exact e.symm_apply_apply x
  have hc := openMap_comp (e : C(X, Y)) e.isOpenEmbedding
    (e.symm : C(Y, X)) e.symm.isOpenEmbedding p a
  simpa only [he, openMap_id] using hc

/-- The actual homeomorphism-induced equivalence of the original direct-limit groups. -/
def homeomorphEquiv (e : X ≃ₜ Y) (p : ℕ) : Cohomology X p ≃ₗ[ℤ] Cohomology Y p :=
  { openMap (e : C(X, Y)) e.isOpenEmbedding p with
    invFun := openMap (e.symm : C(Y, X)) e.symm.isOpenEmbedding p
    left_inv := openMap_homeomorph_inverse e p
    right_inv := openMap_homeomorph_inverse e.symm p }

theorem homeomorphEquiv_toLinearMap (e : X ≃ₜ Y) (p : ℕ) :
    (homeomorphEquiv e p).toLinearMap = openMap (e : C(X, Y)) e.isOpenEmbedding p := rfl

end NoExoticSixSphere.CompactSupportCohomology
