import Wikipedia.SmoothSixDPoincare.CoverOverlapNaturality
import Wikipedia.SmoothSixDPoincare.ConnectingLocalSum

/-!
# A component connecting class is the connecting class of its one-piece cover

Enlarge the first cover member until it and one selected neighborhood cover
the space. Naturality for the two identity cover maps, together with the
actual overlap coordinates, identifies that component of the original
connecting homomorphism with the selected two-set connecting homomorphism.
-/

noncomputable section

open Set Function ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.CoverLocalContributions

open Wikipedia.HopfProblem.SingularMayerVietoris
  Wikipedia.HopfProblem.PeriodTorusHigherHomology

variable {X : Type} [TopologicalSpace X] {ι : Type} [Fintype ι]

theorem componentConnecting_enlarge (U U' : Set X) (V : ι → Set X)
    (hU : IsOpen U) (hU' : IsOpen U') (hV : ∀ i, IsOpen (V i))
    (hd : Pairwise (Disjoint on V)) (hc : U ∪ (⋃ i, V i) = univ)
    (hsub : U ⊆ U') (i : ι) (hci : U' ∪ V i = univ)
    (k : ℕ) (a : SingularHomology X (k + 1)) :
    singularHomologyMap
      (CoverOverlapHomology.componentMap U V U' V (ContinuousMap.id X) hsub
        (fun _ _ hx => hx) i) k
      (componentConnecting U V hU hV hd hc k a i) =
        connectingHomomorphism U' (V i) hU' (hV i) hci k a := by
  classical
  have hc' : U' ∪ (⋃ j, V j) = univ := by
    apply eq_univ_of_forall
    intro x
    have hx : x ∈ U ∪ (⋃ j, V j) := hc.symm ▸ mem_univ x
    exact hx.elim (fun hu => Or.inl (hsub hu)) Or.inr
  have hbig := CoverNaturality.connecting_naturality_apply
    U (⋃ j, V j) U' (⋃ j, V j) (ContinuousMap.id X) hsub (fun _ hx => hx)
    hU (isOpen_iUnion hV) hc hU' (isOpen_iUnion hV) hc' k a
  rw [singularHomologyMap_id, LinearMap.id_apply] at hbig
  change singularHomologyMap
    (CoverOverlapHomology.overlapMap U V U' V (ContinuousMap.id X) hsub (fun _ _ hx => hx)) k
    (connectingHomomorphism U (⋃ j, V j) hU (isOpen_iUnion hV) hc k a) =
      connectingHomomorphism U' (⋃ j, V j) hU' (isOpen_iUnion hV) hc' k a at hbig
  have hcoord := congrArg (fun b => CoverOverlapHomology.homologyEquiv U' V hU' hV hd k b i) hbig
  have hnat := congrFun (CoverOverlapHomology.homologyEquiv_map U V U' V
    (ContinuousMap.id X) hsub (fun _ _ hx => hx) hU hV hd hU' hV hd k
    (connectingHomomorphism U (⋃ j, V j) hU (isOpen_iUnion hV) hc k a)) i
  rw [hnat] at hcoord
  have hsmall := CoverNaturality.connecting_naturality_apply
    U' (V i) U' (⋃ j, V j) (ContinuousMap.id X) (fun _ hx => hx) (subset_iUnion V i)
    hU' (hV i) hci hU' (isOpen_iUnion hV) hc' k a
  rw [singularHomologyMap_id, LinearMap.id_apply] at hsmall
  change singularHomologyMap (CoverOverlapHomology.componentInclusion U' V i) k
    (connectingHomomorphism U' (V i) hU' (hV i) hci k a) =
      connectingHomomorphism U' (⋃ j, V j) hU' (isOpen_iUnion hV) hc' k a at hsmall
  have hsingle := congrArg (fun b => CoverOverlapHomology.homologyEquiv U' V hU' hV hd k b i) hsmall
  rw [CoverOverlapHomology.homologyEquiv_inclusion, Pi.single_eq_same] at hsingle
  exact hcoord.trans hsingle.symm

end Wikipedia.SmoothSixDPoincare.CoverLocalContributions
