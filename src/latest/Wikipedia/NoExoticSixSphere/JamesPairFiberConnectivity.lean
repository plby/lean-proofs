import Wikipedia.NoExoticSixSphere.JamesPairFiberHigherDetection
import Wikipedia.NoExoticSixSphere.NativeHurewiczVanishing

/-!
# All positive native homotopy groups of the actual James inclusion fiber vanish

Strong induction now uses the checked all-degree vanishing-form Hurewicz
theorem. The original relative acyclicity and actual normalization supply
the required fiber homology vanishing in each degree. The genuine fiber
sequence proves bijectivity of every positive-degree native inclusion map.
-/

noncomputable section

open scoped Topology
open Wikipedia.HopfProblem SingularMayerVietoris OrbitPair

namespace NoExoticSixSphere.JamesSphere.FiberConnectivity

open ComparisonCylinder

attribute [local instance] PairNormalization.cylinderSimplyConnected
attribute [local instance] PairNormalization.sourceSimplyConnected

theorem fiber_pi (n : ℕ) : ∀ d, 0 < d → ∀ a : sourceImage (n + 2),
    ∀ p : SourceFiber (n + 2) a, Subsingleton (π_ d (SourceFiber (n + 2) a) p) := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro hd a p
    let := sourceFiber_simplyConnected n a
    by_cases h1 : d = 1
    · subst d
      exact HomotopyGroup.pi1EquivFundamentalGroup.injective.subsingleton
    · have h2 : 2 ≤ d := by omega
      have hlow : ∀ k, 0 < k → k < d → ∀ b : sourceImage (n + 2),
          ∀ q : SourceFiber (n + 2) b, Subsingleton (π_ k (SourceFiber (n + 2) b) q) :=
        fun k hk hkd b q ↦ ih k hkd hk b q
      let : Subsingleton (SingularHomology (SourceFiber (n + 2) a) d) := by
        have h := HigherFiberDetection.fiber_homology_subsingleton_of_pi n (d - 2)
          (fun k hk hkd b q ↦ hlow k hk (by omega) b q) a
        simpa only [Nat.sub_add_cancel h2] using h
      exact NativeHurewiczVanishing.subsingleton d h2
        (fun k hk hkd q ↦ hlow k hk hkd a q) p

theorem fiber_homology (n d : ℕ) (hd : 2 ≤ d) (a : sourceImage (n + 2)) :
    Subsingleton (SingularHomology (SourceFiber (n + 2) a) d) := by
  have h := HigherFiberDetection.fiber_homology_subsingleton_of_pi n (d - 2)
    (fun k hk _ b p ↦ fiber_pi n k hk b p) a
  simpa only [Nat.sub_add_cancel hd] using h

theorem inclusion_pi_surjective (n d : ℕ) (hd : 0 < d) (a : sourceImage (n + 2)) :
    Function.Surjective
      (HigherHomotopy.map (N := Fin d) (subtypeInclusion (sourceImage (n + 2)))
        (y := a) rfl) := by
  cases d with
  | zero => omega
  | succ k =>
    by_cases hk : k = 0
    · subst k
      let : Subsingleton (π_ 1 (Cylinder (n + 2))
          ((subtypeInclusion (sourceImage (n + 2))) a)) :=
        HomotopyGroup.pi1EquivFundamentalGroup.injective.subsingleton
      intro c
      exact ⟨Quotient.mk' GenLoop.const, Subsingleton.elim _ _⟩
    · let : Subsingleton (π_ k
          (HomotopyFiber.Space (subtypeInclusion (sourceImage (n + 2)))
            ((subtypeInclusion (sourceImage (n + 2))) a))
          (HomotopyFiber.basepoint (subtypeInclusion (sourceImage (n + 2))) a)) :=
        fiber_pi n k (by omega) a (sourceFiberBasepoint (n + 2) a)
      exact HomotopyFiberConnectivity.map_surjective_of_fiber_subsingleton k
        (subtypeInclusion (sourceImage (n + 2))) a

theorem inclusion_pi_bijective (n d : ℕ) (hd : 0 < d) (a : sourceImage (n + 2)) :
    Function.Bijective
      (HigherHomotopy.map (N := Fin d) (subtypeInclusion (sourceImage (n + 2)))
        (y := a) rfl) := by
  let : NeZero d := ⟨by omega⟩
  let : Subsingleton (π_ d
      (HomotopyFiber.Space (subtypeInclusion (sourceImage (n + 2)))
        ((subtypeInclusion (sourceImage (n + 2))) a))
      (HomotopyFiber.basepoint (subtypeInclusion (sourceImage (n + 2))) a)) :=
    fiber_pi n d hd a (sourceFiberBasepoint (n + 2) a)
  exact ⟨HomotopyFiberConnectivity.map_injective_of_fiber_subsingleton d
    (subtypeInclusion (sourceImage (n + 2))) a, inclusion_pi_surjective n d hd a⟩

end NoExoticSixSphere.JamesSphere.FiberConnectivity
