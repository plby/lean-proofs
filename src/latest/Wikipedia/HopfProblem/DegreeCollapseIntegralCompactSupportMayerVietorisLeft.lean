import Wikipedia.HopfProblem.DegreeCollapseIntegralCompactSupportMayerVietorisRight

/-!
# Compact-support exactness at the genuine overlap cohomology group

An overlap class killed in both neighborhoods becomes zero on two
actual compact enlargements inside those neighborhoods. Its extension
to their intersection lifts through the proved supported connecting
map. This constructs a preimage under the original compact-support
connecting map, rather than assuming exactness of a replacement row.
-/

noncomputable section

open NoExoticSixSphere

open TopologicalSpace

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralCompactSupportMayerVietoris

open IntegralCompactSupportCohomology IntegralOpenCoverCompactSupports
open IntegralSupportedCohomology (extend extend_trans)

variable {X : Type} [TopologicalSpace X] [T2Space X] (U V : Set X)
  (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)

/-- The constructed connecting map is killed by both original overlap inclusions. -/
theorem first_connecting_zero (p : ℕ) (a : Cohomology X p) :
    firstMap U V hU hV (p + 1) (connecting U V hU hV p hcover a) = 0 := by
  obtain ⟨K, b, rfl⟩ := IntegralOpenCoverCompactSupports.exists_representative U V hU hV hcover p a
  let A := imageCompact U K.1
  let B := imageCompact V K.2
  have hAU := imageCompact_subset U K.1
  have hBV := imageCompact_subset V K.2
  let d := IntegralSupportedCohomology.connecting (A : Set X) (B : Set X)
    A.isCompact.isClosed B.isCompact.isClosed p b
  apply (congrArg (firstMap U V hU hV (p + 1)) (connecting_of U V hU hV p hcover K b)).trans
  apply (firstMap_neighborhood_intersection U V hU hV A B hAU hBV (p + 1) d).trans
  have hd : IntegralSupportedCohomology.intersectionMap (A : Set X) (B : Set X) (p + 1) d = 0 :=
    (IntegralSupportedCohomology.connecting_exact_left (A : Set X) (B : Set X)
      A.isCompact.isClosed B.isCompact.isClosed p).le ⟨b, rfl⟩
  exact Prod.ext
    ((congrArg (neighborhoodOf U hU A hAU (p + 1)) (congrArg Prod.fst hd)).trans
      (neighborhoodOf U hU A hAU (p + 1)).map_zero)
    ((congrArg (neighborhoodOf V hV B hBV (p + 1)) (congrArg Prod.snd hd)).trans
      (neighborhoodOf V hV B hBV (p + 1)).map_zero)

/-- A genuine overlap kernel class has an actual supported representative killed in both pieces. -/
theorem exists_supported_kernel_representative (p : ℕ) (a : Cohomology (U ∩ V : Set X) p)
    (ha : firstMap U V hU hV p a = 0) :
    ∃ (A B : Compacts X) (hAU : (A : Set X) ⊆ U) (hBV : (B : Set X) ⊆ V)
      (d : Component X p (A ⊓ B)),
      IntegralSupportedCohomology.intersectionMap (A : Set X) (B : Set X) p d = 0 ∧
      neighborhoodOf (U ∩ V) (hU.inter hV) (A ⊓ B)
        (fun _ hx => ⟨hAU hx.1, hBV hx.2⟩) p d = a := by
    obtain ⟨K, b, rfl⟩ := IntegralCompactSupportCohomology.exists_representative (U ∩ V : Set X) p a
    let S := imageCompact (U ∩ V) K
    have hSW : (S : Set X) ⊆ U ∩ V := imageCompact_subset (U ∩ V) K
    have hSU : (S : Set X) ⊆ U := fun _ hx => (hSW hx).1
    have hSV : (S : Set X) ⊆ V := fun _ hx => (hSW hx).2
    let c := IntegralOpenSupport.extension (U ∩ V) (hU.inter hV)
      (K : Set (U ∩ V : Set X)) K.isCompact p b
    have hc : neighborhoodOf (U ∩ V) (hU.inter hV) S hSW p c =
        of (U ∩ V : Set X) p K b :=
      neighborhoodOf_extension (U ∩ V) (hU.inter hV) K p b
    have hzU : neighborhoodOf U hU S hSU p c = 0 :=
      (openMap_neighborhoodOf (Set.inter_subset_left : U ∩ V ⊆ U)
        (hU.inter hV) hU S hSW hSU p c).symm.trans
        ((congrArg (leftMap U V hU hV p) hc).trans (congrArg Prod.fst ha))
    have hzV : neighborhoodOf V hV S hSV p c = 0 :=
      (openMap_neighborhoodOf (Set.inter_subset_right : U ∩ V ⊆ V)
        (hU.inter hV) hV S hSW hSV p c).symm.trans
        ((congrArg (rightMap U V hU hV p) hc).trans (congrArg Prod.snd ha))
    obtain ⟨A, hSA, hAU, heA⟩ := (neighborhoodOf_eq_zero_iff U hU S hSU p c).mp hzU
    obtain ⟨B, hSB, hBV, heB⟩ := (neighborhoodOf_eq_zero_iff V hV S hSV p c).mp hzV
    have hSI : S ≤ A ⊓ B := fun _ hx => ⟨hSA hx, hSB hx⟩
    let d := extend hSI p c
    have hdA : extend (show A ⊓ B ≤ A from inf_le_left) p d = 0 :=
      (LinearMap.congr_fun (extend_trans hSI (show A ⊓ B ≤ A from inf_le_left) p) c).symm
        |>.trans heA
    have hdB : extend (show A ⊓ B ≤ B from inf_le_right) p d = 0 :=
      (LinearMap.congr_fun (extend_trans hSI (show A ⊓ B ≤ B from inf_le_right) p) c).symm
        |>.trans heB
    refine ⟨A, B, hAU, hBV, d, Prod.ext hdA hdB, ?_⟩
    exact (neighborhoodOf_extend (U ∩ V) (hU.inter hV) hSI hSW
      (fun _ hx => ⟨hAU hx.1, hBV hx.2⟩) p c).trans hc

/-- Exactness at positive-degree overlap cohomology of the actual compact-support sequence. -/
theorem exact_left (p : ℕ) :
    LinearMap.range (connecting U V hU hV p hcover) =
      LinearMap.ker (firstMap U V hU hV (p + 1)) := by
  apply Submodule.ext
  intro a
  constructor
  · rintro ⟨b, rfl⟩
    exact first_connecting_zero U V hU hV hcover p b
  · intro ha
    obtain ⟨A, B, hAU, hBV, d, hd, hc⟩ :=
      exists_supported_kernel_representative U V hU hV (p + 1) a ha
    obtain ⟨e, he⟩ := (IntegralSupportedCohomology.connecting_exact_left (A : Set X) (B : Set X)
      A.isCompact.isClosed B.isCompact.isClosed p).ge hd
    refine ⟨of X p (A ⊔ B) e, ?_⟩
    apply (connecting_of_supports U V hU hV p hcover A B hAU hBV e).trans
    exact (congrArg (neighborhoodOf (U ∩ V) (hU.inter hV) (A ⊓ B)
      (fun _ hx => ⟨hAU hx.1, hBV hx.2⟩) (p + 1)) he).trans hc

end Wikipedia.HopfProblem.DegreeCollapse.IntegralCompactSupportMayerVietoris
