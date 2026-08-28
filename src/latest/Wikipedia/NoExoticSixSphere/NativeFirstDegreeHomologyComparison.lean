import Wikipedia.NoExoticSixSphere.LoopSpaceHomologyComparison
import Wikipedia.NoExoticSixSphere.HomologyEquivalencePiTwo

/-!
# First-degree homology comparison gives the original native homotopy map

For simply connected spaces whose lower positive native groups vanish,
an isomorphism of the actual homology map in the next degree induces a
native homotopy isomorphism in that degree. Induction descends along the
proved actual loop-homology comparison; second Hurewicz starts the proof.
Naturality of native currying returns the original map at each step.
-/

noncomputable section

open scoped Topology
open Wikipedia.HopfProblem SingularMayerVietoris OrbitPair

namespace NoExoticSixSphere.NativeFirstDegreeHomologyComparison

theorem in_degree : ∀ (n : ℕ) (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    [SimplyConnectedSpace X] [SimplyConnectedSpace Y] (f : C(X, Y)),
    (∀ k, 0 < k → k < n + 2 → ∀ x : X, Subsingleton (π_ k X x)) →
    (∀ k, 0 < k → k < n + 2 → ∀ y : Y, Subsingleton (π_ k Y y)) →
    Function.Bijective (singularHomologyMap f (n + 2)) → ∀ x : X,
      Function.Bijective (HigherHomotopy.map (N := Fin (n + 2)) f (y := x) rfl) := by
  intro n
  induction n with
  | zero =>
    intro X Y _ _ _ _ f _ _ hH x
    exact HomologyEquivalence.piTwo_bijective f hH x
  | succ n ih =>
    intro X Y _ _ _ _ f hX hY hH x
    let : SimplyConnectedSpace (Path x x) :=
      loopSpace_simplyConnected x (hX 2 (by omega) (by omega) x)
    let : SimplyConnectedSpace (Path (f x) (f x)) :=
      loopSpace_simplyConnected (f x) (hY 2 (by omega) (by omega) (f x))
    have hLoopX : ∀ k, 0 < k → k < n + 2 → ∀ p : Path x x,
        Subsingleton (π_ k (Path x x) p) := by
      intro k hk hkn p
      let := hX (k + 1) (by omega) (by omega) x
      exact NativeHomotopyBasepointVanishing.loops_subsingleton k hk x p
    have hLoopY : ∀ k, 0 < k → k < n + 2 → ∀ p : Path (f x) (f x),
        Subsingleton (π_ k (Path (f x) (f x)) p) := by
      intro k hk hkn p
      let := hY (k + 1) (by omega) (by omega) (f x)
      exact NativeHomotopyBasepointVanishing.loops_subsingleton k hk (f x) p
    have hb := ih (Path x x) (Path (f x) (f x)) (LoopSpaceMap.map f x) hLoopX hLoopY
      (LoopSpaceMap.homology_bijective f x n hX hY hH) (Path.refl x)
    exact LoopSpaceMap.pi_bijective_of_loopMap f x (n + 2)
      ((NativeHomotopyTargetEquality.map_bijective_iff (n + 2) (LoopSpaceMap.map f x)
        (LoopSpaceMap.map_refl f x)).mpr hb)

theorem map_bijective {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [SimplyConnectedSpace X] [SimplyConnectedSpace Y] (f : C(X, Y)) (d : ℕ) (hd : 2 ≤ d)
    (hX : ∀ k, 0 < k → k < d → ∀ x : X, Subsingleton (π_ k X x))
    (hY : ∀ k, 0 < k → k < d → ∀ y : Y, Subsingleton (π_ k Y y))
    (hH : Function.Bijective (singularHomologyMap f d)) (x : X) :
    Function.Bijective (HigherHomotopy.map (N := Fin d) f (y := x) rfl) := by
  have he : d - 2 + 2 = d := Nat.sub_add_cancel hd
  rw [← he] at hH ⊢
  exact in_degree (d - 2) X Y f
    (fun k hk hkd y ↦ hX k hk (by omega) y)
    (fun k hk hkd y ↦ hY k hk (by omega) y) hH x

end NoExoticSixSphere.NativeFirstDegreeHomologyComparison
