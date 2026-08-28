import Wikipedia.HopfProblem.OrbitPairDualSubdivisionCarrierBounds

/-!
# Identifications in dual subdivision avoid the initial vertex

For a nondegenerate dual-subdivision simplex, its characteristic map is
injective on every simplex whose vertex range contains zero. Such a
simplex cannot be identified with one omitting zero. This proves the
precise degreewise identification property needed for the regularity
pushout; it does not assert nonsingularity.
-/

noncomputable section

universe u

open CategoryTheory Simplicial

namespace Wikipedia.HopfProblem.OrbitPair.Subdivision

open SubdivisionParameters SubdivisionSupport

variable (X : SSet.{u})

theorem dual_degree_ne_of_zero_ne {l k : ℕ} (p : Parameters dualStandard X k)
    (hp : IsNormal (dualLaw k) X p)
    (ht : p.2 ∈ (dualStandard.obj ⦋p.1.1⦌).nonDegenerate k)
    (f g : ⦋l⦌ ⟶ ⦋k⦌) (hf : f.toOrderHom 0 = 0) (hg : g.toOrderHom 0 ≠ 0) :
    projection dualStandard dualSd dualSdIso.inv X l (degreeParameters dualStandard X f p) ≠
      projection dualStandard dualSd dualSdIso.inv X l (degreeParameters dualStandard X g p) := by
  intro h
  have hnf := dual_degree_isNormal_of_zero X f hf p hp
  have hn := normalize_eqvGen (dualLaw l) (dualFace l) X
    ((dual_projection_eq_iff X l _ _).mp h)
  rw [normalize_fixed (dualLaw l) (dualFace l) X _ hnf] at hn
  have hdim := congrArg (fun q ↦ q.1.1) hn
  have hlt := dual_normalize_degree_dim_lt X g hg p hp ht
  change p.1.1 = _ at hdim
  rw [← hdim] at hlt
  exact (lt_irrefl p.1.1) hlt

theorem dual_degree_injective_at_zero {l k : ℕ} (p : Parameters dualStandard X k)
    (hp : IsNormal (dualLaw k) X p)
    (ht : p.2 ∈ (dualStandard.obj ⦋p.1.1⦌).nonDegenerate k)
    (f g : ⦋l⦌ ⟶ ⦋k⦌) (hf : f.toOrderHom 0 = 0)
    (h : projection dualStandard dualSd dualSdIso.inv X l (degreeParameters dualStandard X f p) =
      projection dualStandard dualSd dualSdIso.inv X l (degreeParameters dualStandard X g p)) :
    f = g := by
  have hg : g.toOrderHom 0 = 0 := by
    by_contra hg
    exact dual_degree_ne_of_zero_ne X p hp ht f g hf hg h
  have hparams := dual_normal_injective X l
    (dual_degree_isNormal_of_zero X f hf p hp) (dual_degree_isNormal_of_zero X g hg p hp) h
  have htfg : (dualStandard.obj ⦋p.1.1⦌).map f.op p.2 =
      (dualStandard.obj ⦋p.1.1⦌).map g.op p.2 :=
    eq_of_heq (Sigma.mk.inj_iff.mp hparams).2
  have hs := (PartialOrder.mem_nerve_nonDegenerate_iff_strictMono p.2).mp ht
  apply SimplexCategory.Hom.ext
  exact DFunLike.ext _ _ (fun i ↦ hs.injective (congrArg (fun t ↦ t.obj i) htfg))

theorem dual_map_injective_at_initial {l k : ℕ} (z : (dualSd.obj X) _⦋k⦌)
    (hz : z ∈ (dualSd.obj X).nonDegenerate k) (f g : ⦋l⦌ ⟶ ⦋k⦌)
    (hf : f.toOrderHom 0 = 0)
    (h : (dualSd.obj X).map f.op z = (dualSd.obj X).map g.op z) : f = g := by
  obtain ⟨p, hp, _⟩ := dual_existsUnique_normal X k z
  have hnd : p.val.2 ∈ (dualStandard.obj ⦋p.val.1.1⦌).nonDegenerate k :=
    nonDegenerate_parameter_of_projection dualStandard X dualSd dualSdIso.inv p.val
      (by rw [hp]; exact hz)
  apply dual_degree_injective_at_zero X p.val p.property hnd f g hf
  rw [degreeParameters_projection, degreeParameters_projection, hp]
  exact h

theorem dual_map_eq_imp_eq_or_omit_zero {l k : ℕ} (z : (dualSd.obj X) _⦋k⦌)
    (hz : z ∈ (dualSd.obj X).nonDegenerate k) (f g : ⦋l⦌ ⟶ ⦋k⦌)
    (h : (dualSd.obj X).map f.op z = (dualSd.obj X).map g.op z) :
    f = g ∨ (f.toOrderHom 0 ≠ 0 ∧ g.toOrderHom 0 ≠ 0) := by
  by_cases hf : f.toOrderHom 0 = 0
  · exact Or.inl (dual_map_injective_at_initial X z hz f g hf h)
  by_cases hg : g.toOrderHom 0 = 0
  · exact Or.inl (dual_map_injective_at_initial X z hz g f hg h.symm).symm
  exact Or.inr ⟨hf, hg⟩

end Wikipedia.HopfProblem.OrbitPair.Subdivision
