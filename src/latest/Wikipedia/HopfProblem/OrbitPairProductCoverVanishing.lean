import Wikipedia.HopfProblem.OrbitPairProductCoverHomology

/-!
# Vanishing from a product cover and an injective overlap projection

If both contractible pieces have zero homology in the desired degree,
and projection detects the preceding overlap group, the actual
Mayer--Vietoris sequence forces ambient homology to vanish.
-/

noncomputable section

open Set Topology ContinuousMap

namespace Wikipedia.HopfProblem.OrbitPair.ProductCover

open SingularMayerVietoris PeriodTorusHigherHomology

variable {Y X : Type} [TopologicalSpace Y] [TopologicalSpace X]

def overlapProjection (U V : Set Y) :
    C((piece (X := X) U ∩ piece V : Set (Y × X)), X) :=
  ⟨fun p => p.val.2, continuous_subtype_val.snd⟩

theorem left_homology_injective_of_overlap_projection (U V : Set Y) (n : ℕ)
    (hp : Function.Injective (singularHomologyMap (overlapProjection (X := X) U V) n)) :
    Function.Injective (leftHomologyMap (piece (X := X) U) (piece V) n) := by
  intro a b hab
  apply hp
  have he := congrArg
    (fun p : SingularHomology (piece (X := X) U) n × SingularHomology (piece V) n =>
      singularHomologyMap (projection U) n p.1) hab
  simp only [leftHomologyMap_apply] at he
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp,
    ← LinearMap.comp_apply, ← singularHomologyMap_comp] at he
  exact he

theorem homology_subsingleton_of_overlap_projection (U V : Set Y)
    (hU : IsOpen U) (hV : IsOpen V) (hc : U ∪ V = univ)
    [ContractibleSpace U] [ContractibleSpace V] (n : ℕ)
    [Subsingleton (SingularHomology X (n + 1))]
    (hp : Function.Injective (singularHomologyMap (overlapProjection (X := X) U V) n)) :
    Subsingleton (SingularHomology (Y × X) (n + 1)) := by
  let _ : Subsingleton (SingularHomology (piece (X := X) U) (n + 1)) :=
    (pieceHomologyEquiv U (n + 1)).injective.subsingleton
  let _ : Subsingleton (SingularHomology (piece (X := X) V) (n + 1)) :=
    (pieceHomologyEquiv V (n + 1)).injective.subsingleton
  have hU' := piece_open (X := X) U hU
  have hV' := piece_open (X := X) V hV
  have hc' := piece_cover (X := X) U V hc
  have hi := left_homology_injective_of_overlap_projection U V n hp
  have hz (a : SingularHomology (Y × X) (n + 1)) : a = 0 := by
    have ha : connectingHomomorphism (piece U) (piece V) hU' hV' hc' n a = 0 := by
      apply hi
      have he : connectingHomomorphism (piece U) (piece V) hU' hV' hc' n a ∈
          LinearMap.range (connectingHomomorphism (piece U) (piece V) hU' hV' hc' n) :=
        ⟨a, rfl⟩
      rw [exact_at_intersection (piece U) (piece V) hU' hV' hc'] at he
      exact he.trans (map_zero _).symm
    have he : a ∈ LinearMap.ker
        (connectingHomomorphism (piece U) (piece V) hU' hV' hc' n) := ha
    rw [← exact_at_ambient (piece U) (piece V) hU' hV' hc' n] at he
    obtain ⟨p, hp⟩ := he
    rw [show p = 0 from Subsingleton.elim _ _, map_zero] at hp
    exact hp.symm
  exact ⟨fun a b => (hz a).trans (hz b).symm⟩

end Wikipedia.HopfProblem.OrbitPair.ProductCover
