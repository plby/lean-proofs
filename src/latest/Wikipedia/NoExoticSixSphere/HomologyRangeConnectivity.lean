import Wikipedia.NoExoticSixSphere.NativeHurewiczVanishing
import Wikipedia.NoExoticSixSphere.HomologyEquivalencePiTwo
import Wikipedia.NoExoticSixSphere.HomotopyFiberProjectionThree
import Wikipedia.NoExoticSixSphere.MappingCylinderNativeHomotopy

/-!
# Finite-range homology comparison gives native homotopy comparison

For a simply connected pair, actual inclusion homology isomorphisms
through degree `D + 1` give vanishing native fiber groups through `D`.
The proof uses second Hurewicz to start and the constructed relative
normalization/recovery and vanishing-form Hurewicz to induct. Mapping
cylinder transport returns the original continuous map, not a replacement.
-/

noncomputable section

open scoped Topology
open Wikipedia.HopfProblem SingularMayerVietoris OrbitPair

namespace NoExoticSixSphere.HomologyRangeConnectivity

open RelativeFiberHomology

section Inclusion

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (U : Set X) [SimplyConnectedSpace U] (D : ℕ) (hD : 0 < D)
    (hH : ∀ d, 2 ≤ d → d ≤ D + 1 →
      Function.Bijective (singularHomologyMap (subtypeInclusion U) d))

include hD hH

theorem fiber_pi : ∀ d, 0 < d → d ≤ D → ∀ a : U, ∀ p : Fiber U a,
    Subsingleton (π_ d (Fiber U a) p) := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro hd hdD a p
    let : SimplyConnectedSpace (Fiber U a) :=
      HomotopyFiberConnectivity.simplyConnectedSpace (subtypeInclusion U) a
        (HomologyEquivalence.piTwo_bijective (subtypeInclusion U)
          (hH 2 (by omega) (by omega)) a).surjective
    by_cases h1 : d = 1
    · subst d
      exact HomotopyGroup.pi1EquivFundamentalGroup.injective.subsingleton
    · have h2 : 2 ≤ d := by omega
      have hlow : ∀ k, 0 < k → k < d → ∀ b : U, ∀ q : Fiber U b,
          Subsingleton (π_ k (Fiber U b) q) :=
        fun k hk hkd b q ↦ ih k hkd hk (by omega) b q
      let : Subsingleton (SingularHomology (Fiber U a) d) := by
        let : Subsingleton (RelativeSingularHomology.Homology U (d - 2 + 3)) := by
          have he : d - 2 + 3 = d + 1 := by omega
          rw [he]
          exact RelativeSingularHomology.homologySucc_subsingleton_of_maps U d
            (hH d h2 (by omega)).injective (hH (d + 1) (by omega) (by omega)).surjective
        have hh := RelativeNormalization.fiber_homology_subsingleton_of_fiberConnectivity
          U a (d - 2) (fun k hk hkd b q ↦ hlow k hk (by omega) b q)
        simpa only [Nat.sub_add_cancel h2] using hh
      exact NativeHurewiczVanishing.subsingleton d h2
        (fun k hk hkd q ↦ hlow k hk hkd a q) p

theorem inclusion_pi_surjective (d : ℕ) (hd : 0 < d) (hdD : d ≤ D + 1) (a : U) :
    Function.Surjective
      (HigherHomotopy.map (N := Fin d) (subtypeInclusion U) (y := a) rfl) := by
  cases d with
  | zero => omega
  | succ k =>
    by_cases hk : k = 0
    · subst k
      let : Subsingleton (π_ 1 X ((subtypeInclusion U) a)) :=
        HomotopyGroup.pi1EquivFundamentalGroup.injective.subsingleton
      intro c
      exact ⟨Quotient.mk' GenLoop.const, Subsingleton.elim _ _⟩
    · let : Subsingleton (π_ k
          (HomotopyFiber.Space (subtypeInclusion U) ((subtypeInclusion U) a))
          (HomotopyFiber.basepoint (subtypeInclusion U) a)) :=
        fiber_pi U D hD hH k (by omega) (by omega) a
          (HomotopyFiber.basepoint (subtypeInclusion U) a)
      exact HomotopyFiberConnectivity.map_surjective_of_fiber_subsingleton k
        (subtypeInclusion U) a

theorem inclusion_pi_bijective (d : ℕ) (hd : 0 < d) (hdD : d ≤ D) (a : U) :
    Function.Bijective
      (HigherHomotopy.map (N := Fin d) (subtypeInclusion U) (y := a) rfl) := by
  let : NeZero d := ⟨by omega⟩
  let : Subsingleton (π_ d
      (HomotopyFiber.Space (subtypeInclusion U) ((subtypeInclusion U) a))
      (HomotopyFiber.basepoint (subtypeInclusion U) a)) :=
    fiber_pi U D hD hH d hd hdD a (HomotopyFiber.basepoint (subtypeInclusion U) a)
  exact ⟨HomotopyFiberConnectivity.map_injective_of_fiber_subsingleton d
    (subtypeInclusion U) a, inclusion_pi_surjective U D hD hH d hd (by omega) a⟩

end Inclusion

theorem map_pi_bijective {A B : TopCat.{0}} [SimplyConnectedSpace A] [SimplyConnectedSpace B]
    (f : A ⟶ B) (D : ℕ) (hD : 0 < D)
    (hH : ∀ k, 2 ≤ k → k ≤ D + 1 → Function.Bijective (singularHomologyMap f.hom k))
    (d : ℕ) (hd : 0 < d) (hdD : d ≤ D) (a : A) :
    Function.Bijective (HigherHomotopy.map (N := Fin d) f.hom (y := a) rfl) := by
  let : SimplyConnectedSpace (MappingCylinder.space f) :=
    (MappingCylinder.projectionEquiv f).simplyConnectedSpace
  let : SimplyConnectedSpace (MappingCylinderHomology.sourceImage f) :=
    (MappingCylinderHomology.sourceHomeomorph f).symm.toHomotopyEquiv.simplyConnectedSpace
  exact MappingCylinderNativeHomotopy.original_pi_bijective f d hd
    (inclusion_pi_bijective (MappingCylinderHomology.sourceImage f) D hD
      (fun k hk hkD ↦ (MappingCylinderHomology.inclusion_homology_bijective_iff f k).mpr
        (hH k hk hkD)) d hd hdD) a

end NoExoticSixSphere.HomologyRangeConnectivity
