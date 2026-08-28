import Wikipedia.HopfProblem.DegreeCollapseIntegralOpenCoverCompactSupports
import Wikipedia.HopfProblem.DegreeCollapseIntegralCompactSupportNestedNeighborhood

/-!
# Realizing equal ambient extensions on a subordinate compact-support pair

An equality of original compact-support direct-limit classes is witnessed
after enlarging to a compact support. A two-open-set cover splits that
support, and the original support maps retain both neighborhood classes.
Their resulting representatives then agree on the actual compact union.
-/

noncomputable section

open NoExoticSixSphere

open TopologicalSpace

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralCompactSupportCohomology

variable {X : Type} [TopologicalSpace X]

theorem imageCompact_subset (U : Set X) (K : Compacts U) : (imageCompact U K : Set X) ⊆ U := by
  rintro _ ⟨x, _, rfl⟩
  exact x.property

end Wikipedia.HopfProblem.DegreeCollapse.IntegralCompactSupportCohomology

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralOpenCoverCompactSupports

open IntegralCompactSupportCohomology
open IntegralSupportedCohomology (extend extend_trans)

variable {X : Type} [TopologicalSpace X] [T2Space X] (U V : Set X)
  (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)

include hcover

/-- Equal actual ambient extensions can be represented by classes agreeing on one compact union. -/
theorem exists_matching_representatives (p : ℕ) (a : Cohomology U p) (b : Cohomology V p)
    (hab : inclusion U hU p a = inclusion V hV p b) :
    ∃ (P : Index U V) (a' : Component X p (imageCompact U P.1))
      (b' : Component X p (imageCompact V P.2)),
      neighborhoodOf U hU (imageCompact U P.1) (imageCompact_subset U P.1) p a' = a ∧
      neighborhoodOf V hV (imageCompact V P.2) (imageCompact_subset V P.2) p b' = b ∧
      extend (show (imageCompact U P.1 : Set X) ⊆ unionCompact U V P from Set.subset_union_left)
          p a' =
        extend (show (imageCompact V P.2 : Set X) ⊆ unionCompact U V P
          from Set.subset_union_right) p b' := by
  obtain ⟨K, a₀, rfl⟩ := IntegralCompactSupportCohomology.exists_representative U p a
  obtain ⟨L, b₀, rfl⟩ := IntegralCompactSupportCohomology.exists_representative V p b
  let a₁ := IntegralOpenSupport.extension U hU (K : Set U) K.isCompact p a₀
  let b₁ := IntegralOpenSupport.extension V hV (L : Set V) L.isCompact p b₀
  change of X p (imageCompact U K) a₁ = of X p (imageCompact V L) b₁ at hab
  obtain ⟨N, hKN, hLN, he⟩ := (IntegralCompactSupportCohomology.of_eq_iff X p
    (imageCompact U K) (imageCompact V L) a₁ b₁).mp hab
  obtain ⟨P, hKP, _, hNP⟩ := exists_common_upper U V hU hV hcover (K, L) (K, L) N
  have hKA : (imageCompact U K : Set X) ⊆ imageCompact U P.1 := Set.image_mono hKP.1
  have hLB : (imageCompact V L : Set X) ⊆ imageCompact V P.2 := Set.image_mono hKP.2
  have hAP : (imageCompact U P.1 : Set X) ⊆ unionCompact U V P := Set.subset_union_left
  have hBP : (imageCompact V P.2 : Set X) ⊆ unionCompact U V P := Set.subset_union_right
  refine ⟨P, extend hKA p a₁, extend hLB p b₁, ?_, ?_, ?_⟩
  · exact (neighborhoodOf_extend U hU hKA (imageCompact_subset U K)
      (imageCompact_subset U P.1) p a₁).trans (neighborhoodOf_extension U hU K p a₀)
  · exact (neighborhoodOf_extend V hV hLB (imageCompact_subset V L)
      (imageCompact_subset V P.2) p b₁).trans (neighborhoodOf_extension V hV L p b₀)
  · have he' := congrArg (extend hNP p) he
    calc
      extend hAP p (extend hKA p a₁) = extend (hKA.trans hAP) p a₁ :=
        (LinearMap.congr_fun (extend_trans hKA hAP p) a₁).symm
      _ = extend hNP p (extend hKN p a₁) := LinearMap.congr_fun (extend_trans hKN hNP p) a₁
      _ = extend hNP p (extend hLN p b₁) := he'
      _ = extend (hLB.trans hBP) p b₁ :=
        (LinearMap.congr_fun (extend_trans hLN hNP p) b₁).symm
      _ = extend hBP p (extend hLB p b₁) := LinearMap.congr_fun (extend_trans hLB hBP p) b₁

end Wikipedia.HopfProblem.DegreeCollapse.IntegralOpenCoverCompactSupports
