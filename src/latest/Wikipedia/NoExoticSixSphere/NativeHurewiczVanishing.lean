import Wikipedia.NoExoticSixSphere.PointInclusionFiber
import Wikipedia.NoExoticSixSphere.RelativeNormalizationRecovery
import Wikipedia.NoExoticSixSphere.RelativeContractibleSubspace
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedIso

/-!
# All-degree vanishing-form Hurewicz detection for the actual native groups

For a simply connected space, lower native homotopy vanishing and zero
homology in the next degree force native homotopy vanishing there.
Induction uses the actual point-inclusion pair. Its relative homology is
the original absolute homology, and the checked recovery annihilates the
homology of its genuine loop-space fiber one degree lower. Native currying
then returns the required homotopy group of the original space.
-/

noncomputable section

open scoped Topology
open Wikipedia.HopfProblem SingularMayerVietoris PeriodTorusHigherHomology OrbitPair

namespace NoExoticSixSphere.NativeHurewiczVanishing

theorem in_degree : ∀ (n : ℕ) (X : Type) [TopologicalSpace X] [SimplyConnectedSpace X],
    (∀ k, 0 < k → k < n + 2 → ∀ x : X, Subsingleton (π_ k X x)) →
    Subsingleton (SingularHomology X (n + 2)) → ∀ x : X, Subsingleton (π_ (n + 2) X x) := by
  intro n
  induction n with
  | zero =>
    intro X _ _ _ hH x
    let := hH
    exact (SecondHurewicz.SimplyConnected.hurewiczPi2Equiv x).injective.subsingleton
  | succ n ih =>
    intro X _ _ hpi hH x
    let a : ({x} : Set X) := ⟨x, rfl⟩
    let : Nonempty ({x} : Set X) := ⟨a⟩
    let : ContractibleSpace ({x} : Set X) := inferInstance
    let : SimplyConnectedSpace ({x} : Set X) := inferInstance
    let : Subsingleton (SingularHomology X (n + 3)) := hH
    let : Subsingleton (RelativeSingularHomology.Homology ({x} : Set X) (n + 3)) := by
      let e := RelativeSingularHomology.contractibleSubspaceEquiv ({x} : Set X) (n + 1)
      exact e.symm.injective.subsingleton
    have hFiber :
        Subsingleton (SingularHomology (RelativeFiberHomology.Fiber ({x} : Set X) a) (n + 2)) := by
      apply RelativeNormalization.fiber_homology_subsingleton_of_fiberConnectivity
        ({x} : Set X) a n
      intro k hk hkn b p
      let : Subsingleton (π_ (k + 1) X b.val) := hpi (k + 1) (by omega) (by omega) b.val
      exact PointInclusionFiber.pi_subsingleton x b k hk p
    have hLoops : Subsingleton (SingularHomology (Path x x) (n + 2)) := by
      let := hFiber
      let e := homotopyEquivHomologyEquiv
        (PointInclusionFiber.loopsHomeomorph x a).symm.toHomotopyEquiv (n + 2)
      exact e.injective.subsingleton
    let : SimplyConnectedSpace (Path x x) :=
      loopSpace_simplyConnected x (hpi 2 (by omega) (by omega) x)
    have hLoopPi : ∀ k, 0 < k → k < n + 2 → ∀ p : Path x x,
        Subsingleton (π_ k (Path x x) p) := by
      intro k hk hkn p
      let : Subsingleton (π_ (k + 1) X x) := hpi (k + 1) (by omega) (by omega) x
      exact NativeHomotopyBasepointVanishing.loops_subsingleton k hk x p
    let : Subsingleton (π_ (n + 2) (Path x x) (Path.refl x)) :=
      ih (Path x x) hLoopPi hLoops (Path.refl x)
    exact (GeneralizedLoopCurrying.homotopyEquiv (n + 2) x).symm.injective.subsingleton

theorem subsingleton {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
    (d : ℕ) (hd : 2 ≤ d)
    (hpi : ∀ k, 0 < k → k < d → ∀ x : X, Subsingleton (π_ k X x))
    [Subsingleton (SingularHomology X d)] (x : X) : Subsingleton (π_ d X x) := by
  have hH : Subsingleton (SingularHomology X (d - 2 + 2)) := by
    simpa only [Nat.sub_add_cancel hd] using
      (inferInstanceAs (Subsingleton (SingularHomology X d)))
  have h := in_degree (d - 2) X (fun k hk hkd y ↦ hpi k hk (by omega) y) hH x
  simpa only [Nat.sub_add_cancel hd] using h

end NoExoticSixSphere.NativeHurewiczVanishing
