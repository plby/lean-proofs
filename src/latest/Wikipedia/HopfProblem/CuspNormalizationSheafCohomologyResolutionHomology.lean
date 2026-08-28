import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionExt

/-!
# Homology from a kernel and an exact cokernel

This small categorical helper constructs Mathlib's actual homology
isomorphism, retaining its formula on cycles.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyResolution

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- An exact kernel followed by an exact cokernel is actual left
homology data, not a new definition of cohomology. -/
def leftHomologyDataOfExact (S : ShortComplex C) {K H : C}
    (i : K ⟶ S.X₂) (a : S.X₁ ⟶ K) (p : K ⟶ H)
    (wi : i ≫ S.g = 0) (wa : a ≫ i = S.f) (wp : a ≫ p = 0)
    (hi : (ShortComplex.mk i S.g wi).Exact)
    (hp : (ShortComplex.mk a p wp).Exact) [Mono i] [Epi p] :
    S.LeftHomologyData := by
  let hk : IsLimit (KernelFork.ofι i wi) := hi.fIsKernel
  have hfac : hk.lift (KernelFork.ofι S.f S.zero) = a := by
    apply (cancel_mono i).mp
    exact (Fork.IsLimit.lift_ι hk).trans wa.symm
  refine
    { K := K
      H := H
      i := i
      π := p
      wi := wi
      hi := hk
      wπ := by rw [hfac]; exact wp
      hπ := ?_ }
  apply CokernelCofork.IsColimit.ofπ'
  intro Z k hk'
  exact CokernelCofork.IsColimit.desc' hp.gIsCokernel k (by
    change a ≫ k = 0
    exact (congrArg (fun l => l ≫ k) hfac).symm.trans hk')

/-- Applying a homology isomorphism to the class of a chosen cycle
gives its actual cokernel representative. -/
theorem leftHomologyDataOfExact_class (S : ShortComplex C) {K H : C}
    (i : K ⟶ S.X₂) (a : S.X₁ ⟶ K) (p : K ⟶ H)
    (wi : i ≫ S.g = 0) (wa : a ≫ i = S.f) (wp : a ≫ p = 0)
    (hi : (ShortComplex.mk i S.g wi).Exact)
    (hp : (ShortComplex.mk a p wp).Exact) [Mono i] [Epi p] :
    let h := leftHomologyDataOfExact S i a p wi wa wp hi hp
    h.cyclesIso.inv ≫ S.homologyπ ≫ h.homologyIso.hom = p := by
  let h := leftHomologyDataOfExact S i a p wi wa wp hi hp
  change h.cyclesIso.inv ≫ S.homologyπ ≫ h.homologyIso.hom = h.π
  rw [h.homologyπ_comp_homologyIso_hom, Iso.inv_hom_id_assoc]

end Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyResolution
