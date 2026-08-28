import Wikipedia.HopfProblem.DegreeCollapseIntegralEuclideanFundamentalClass
import Wikipedia.NoExoticSixSphere.SupportedHomeomorph
import Wikipedia.NoExoticSixSphere.SupportedNeighborhoodHomology

/-!
# Actual integral support transport through an open chart

Integral excision gives the inclusion equivalence for a closed support
inside an open neighborhood. Its point-evaluation square commutes on
the original maps. Composing with the actual source-target homeomorphism
gives support transport whose local action is exactly the original
partial-homeomorphism local homology equivalence.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralSupportTransport

open SingularMayerVietoris NoExoticSixSphere SupportedRelativeHomology

variable {X : Type} [TopologicalSpace X]

theorem inclusionChain_quasiIso (U K : Set X) (hU : IsOpen U) (hK : IsClosed K)
    (hKU : K ⊆ U) : QuasiIso (inclusionChain (ModuleCat.of ℤ ℤ) U K) :=
  RelativeSingularHomology.excisionChainMap_quasiIso U Kᶜ hU hK.isOpen_compl
    (support_complement_cover U K hKU)

def inclusionEquiv (U K : Set X) (hU : IsOpen U) (hK : IsClosed K) (hKU : K ⊆ U) (n : ℕ) :
    Homology (ModuleCat.of ℤ ℤ) (supportIn U K) n ≃ₗ[ℤ]
      Homology (ModuleCat.of ℤ ℤ) K n := by
  let := inclusionChain_quasiIso U K hU hK hKU
  exact (isoOfQuasiIsoAt (inclusionChain (ModuleCat.of ℤ ℤ) U K) n).toLinearEquiv

theorem inclusionEquiv_toLinearMap (U K : Set X) (hU : IsOpen U) (hK : IsClosed K)
    (hKU : K ⊆ U) (n : ℕ) :
    (inclusionEquiv U K hU hK hKU n).toLinearMap = inclusionMap (ModuleCat.of ℤ ℤ) U K n := rfl

theorem inclusion_evaluation_chain (U K : Set X) (x : U) (hx : (x : X) ∈ K) :
    inclusionChain (ModuleCat.of ℤ ℤ) U K ≫
        restrictChain (ModuleCat.of ℤ ℤ)
          (show {(x : X)} ⊆ K from Set.singleton_subset_iff.mpr hx) =
      restrictChain (ModuleCat.of ℤ ℤ)
          (show {x} ⊆ supportIn U K from Set.singleton_subset_iff.mpr hx) ≫
        RelativeSingularHomology.neighborhoodChainMap U x := by
  have hi : Set.MapsTo (subtypeInclusion U) (supportIn U K)ᶜ Kᶜ := fun _ hy => hy
  have ho : Set.MapsTo (ContinuousMap.id X) Kᶜ ({(x : X)}ᶜ : Set X) := by
    intro y hy he
    change y = (x : X) at he
    subst y
    exact hy hx
  have hu : Set.MapsTo (ContinuousMap.id U) (supportIn U K)ᶜ ({x}ᶜ : Set U) := by
    intro y hy he
    change y = x at he
    subst y
    exact hy hx
  change RelativeSingularHomology.mapChain (subtypeInclusion U) hi ≫
      RelativeSingularHomology.mapChain (ContinuousMap.id X) ho =
    RelativeSingularHomology.mapChain (ContinuousMap.id U) hu ≫
      RelativeSingularHomology.mapChain (subtypeInclusion U)
        (RelativeSingularHomology.inclusion_mapsTo_puncture U x)
  rw [← RelativeSingularHomology.mapChain_comp, ← RelativeSingularHomology.mapChain_comp]
  rfl

theorem evaluate_inclusion (U K : Set X) (x : U) (hx : (x : X) ∈ K) (n : ℕ) :
    (evaluate (ModuleCat.of ℤ ℤ) K (x : X) hx n).comp
        (inclusionMap (ModuleCat.of ℤ ℤ) U K n) =
      (RelativeSingularHomology.neighborhoodMap U x n).comp
        (evaluate (ModuleCat.of ℤ ℤ) (supportIn U K) x hx n) := by
  let l := restrictChain (ModuleCat.of ℤ ℤ)
    (show {(x : X)} ⊆ K from Set.singleton_subset_iff.mpr hx)
  let r := restrictChain (ModuleCat.of ℤ ℤ)
    (show {x} ⊆ supportIn U K from Set.singleton_subset_iff.mpr hx)
  exact (homologyLinearMap_comp (inclusionChain (ModuleCat.of ℤ ℤ) U K) l n).symm.trans
    ((congrArg (fun k => homologyLinearMap k n) (inclusion_evaluation_chain U K x hx)).trans
      (homologyLinearMap_comp r (RelativeSingularHomology.neighborhoodChainMap U x) n))

variable {Y : Type} [TopologicalSpace Y] [T1Space X] [T1Space Y]

def partialHomeomorphEquiv (e : OpenPartialHomeomorph X Y)
    {K : Set X} {L : Set Y} (hK : IsClosed K) (hL : IsClosed L)
    (hKs : K ⊆ e.source) (hLt : L ⊆ e.target)
    (hKL : ∀ x ∈ e.source, x ∈ K ↔ e x ∈ L) (n : ℕ) :
    Homology (ModuleCat.of ℤ ℤ) K n ≃ₗ[ℤ] Homology (ModuleCat.of ℤ ℤ) L n :=
  ((inclusionEquiv e.source K e.open_source hK hKs n).symm.trans
    (homeomorphEquiv (ModuleCat.of ℤ ℤ) e.toHomeomorphSourceTarget
      (K := supportIn e.source K) (L := supportIn e.target L)
      (fun x => hKL x x.property) n)).trans
    (inclusionEquiv e.target L e.open_target hL hLt n)

/-- The support isomorphism retains the local action of the original partial chart. -/
theorem evaluate_partialHomeomorphEquiv (e : OpenPartialHomeomorph X Y)
    {K : Set X} {L : Set Y} (hK : IsClosed K) (hL : IsClosed L)
    (hKs : K ⊆ e.source) (hLt : L ⊆ e.target)
    (hKL : ∀ x ∈ e.source, x ∈ K ↔ e x ∈ L) (x : X) (hx : x ∈ K) (n : ℕ)
    (a : Homology (ModuleCat.of ℤ ℤ) K n) :
    evaluate (ModuleCat.of ℤ ℤ) L (e x) ((hKL x (hKs hx)).mp hx) n
        (partialHomeomorphEquiv e hK hL hKs hLt hKL n a) =
      RelativeSingularHomology.partialHomeomorphEquiv e x (hKs hx) n
        (evaluate (ModuleCat.of ℤ ℤ) K x hx n a) := by
  let u : e.source := ⟨x, hKs hx⟩
  let v := e.toHomeomorphSourceTarget u
  have hxU : (u : X) ∈ K := hx
  have hu : u ∈ supportIn e.source K := hxU
  have hyV : (v : Y) ∈ L := (hKL u u.property).mp hxU
  have hv : v ∈ supportIn e.target L := hyV
  let F := inclusionEquiv e.source K e.open_source hK hKs n
  let G := homeomorphEquiv (ModuleCat.of ℤ ℤ) e.toHomeomorphSourceTarget
    (K := supportIn e.source K) (L := supportIn e.target L)
    (fun z => hKL z z.property) n
  let H := inclusionEquiv e.target L e.open_target hL hLt n
  let f : (RelativeCoefficients.complex (ModuleCat.of ℤ ℤ) ({u}ᶜ : Set e.source)).homology n ≃ₗ[ℤ]
      (RelativeCoefficients.complex (ModuleCat.of ℤ ℤ) ({(u : X)}ᶜ : Set X)).homology n :=
    RelativeSingularHomology.neighborhoodEquiv e.source e.open_source u n
  let g := RelativeCoefficients.localHomeomorphEquiv (ModuleCat.of ℤ ℤ)
    e.toHomeomorphSourceTarget u n
  let h : (RelativeCoefficients.complex (ModuleCat.of ℤ ℤ) ({v}ᶜ : Set e.target)).homology n ≃ₗ[ℤ]
      (RelativeCoefficients.complex (ModuleCat.of ℤ ℤ) ({(v : Y)}ᶜ : Set Y)).homology n :=
    RelativeSingularHomology.neighborhoodEquiv e.target e.open_target v n
  have hs : evaluate (ModuleCat.of ℤ ℤ) (supportIn e.source K) u hu n (F.symm a) =
      f.symm (evaluate (ModuleCat.of ℤ ℤ) K (u : X) hxU n a) := by
    apply f.injective
    rw [LinearEquiv.apply_symm_apply]
    have he := LinearMap.congr_fun (evaluate_inclusion e.source K u hxU n) (F.symm a)
    change evaluate (ModuleCat.of ℤ ℤ) K (u : X) hxU n (F (F.symm a)) =
      f (evaluate (ModuleCat.of ℤ ℤ) (supportIn e.source K) u hu n (F.symm a)) at he
    rw [LinearEquiv.apply_symm_apply] at he
    exact he.symm
  change evaluate (ModuleCat.of ℤ ℤ) L (v : Y) hyV n (H (G (F.symm a))) =
    h (g (f.symm (evaluate (ModuleCat.of ℤ ℤ) K (u : X) hxU n a)))
  calc
    _ = h (evaluate (ModuleCat.of ℤ ℤ) (supportIn e.target L) v
        hv n (G (F.symm a))) :=
      LinearMap.congr_fun (evaluate_inclusion e.target L v hyV n)
        (G (F.symm a))
    _ = h (g (evaluate (ModuleCat.of ℤ ℤ) (supportIn e.source K) u hu n (F.symm a))) :=
      congrArg h (LinearMap.congr_fun (evaluate_homeomorphEquiv (ModuleCat.of ℤ ℤ)
        e.toHomeomorphSourceTarget (K := supportIn e.source K) (L := supportIn e.target L)
        (fun z => hKL z z.property) u hu n) (F.symm a))
    _ = _ := congrArg (fun z => h (g z)) hs

end Wikipedia.HopfProblem.DegreeCollapse.IntegralSupportTransport
