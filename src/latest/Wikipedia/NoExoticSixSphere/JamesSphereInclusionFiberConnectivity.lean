import Wikipedia.NoExoticSixSphere.JamesSphereInclusionRange
import Wikipedia.NoExoticSixSphere.JamesSphereFiberQuotientMap

/-!
# The genuine one-letter inclusion fiber is highly connected

This is the fiber of `S^n -> J(S^n)`, not the fiber of the James comparison
`J(S^n) -> loops(S^(n+1))`. The actual fiber exact sequence proves native
vanishing only in the stated range, through degree `2 * n - 2`.
-/

noncomputable section

open scoped Topology

namespace NoExoticSixSphere.JamesSphere.FiberQuotient

theorem fiber_pathConnected (n : ℕ) (hn : 2 ≤ n) : PathConnectedSpace (Fiber n) := by
  let : SimplyConnectedSpace (WordHomology.Words n) := by
    have he : n = (n - 2) + 2 := by omega
    rw [he]
    exact JamesSphere.simplyConnectedSpace (n - 2)
  let : PathConnectedSpace (Sphere n) := by
    have he : n = (n - 2) + 2 := by omega
    rw [he]
    infer_instance
  exact HomotopyFiberConnectivity.pathConnectedSpace (inclusion n) (spherePole n)

theorem fiber_pi_basepoint (n d : ℕ) (hn : 2 ≤ n) (hd : 0 < d)
    (hdn : d + 2 ≤ 2 * n) : Subsingleton (π_ d (Fiber n) (basepoint n)) := by
  let : NeZero d := ⟨by omega⟩
  exact HomotopyFiberConnectivity.homotopy_subsingleton_of_maps d (inclusion n)
    (spherePole n) (InclusionRange.inclusion_injective_imageBasepoint n d hn hdn)
    (InclusionRange.inclusion_surjective_imageBasepoint n (d + 1) hn (by omega))

theorem fiber_pi (n d : ℕ) (hn : 2 ≤ n) (hd : 0 < d) (hdn : d + 2 ≤ 2 * n)
    (p : Fiber n) : Subsingleton (π_ d (Fiber n) p) := by
  let := fiber_pathConnected n hn
  let := fiber_pi_basepoint n d hn hd hdn
  exact NativeHomotopyBasepointVanishing.subsingleton d hd (basepoint n) p

theorem fiber_simplyConnected (n : ℕ) (hn : 2 ≤ n) : SimplyConnectedSpace (Fiber n) := by
  let := fiber_pathConnected n hn
  let := fiber_pi_basepoint n 1 hn (by omega) (by omega)
  let : Subsingleton (FundamentalGroup (Fiber n) (basepoint n)) :=
    HomotopyGroup.pi1EquivFundamentalGroup.symm.injective.subsingleton
  exact Wikipedia.HopfProblem.simplyConnectedSpace_of_fundamentalGroup_subsingleton
    (basepoint n)

end NoExoticSixSphere.JamesSphere.FiberQuotient
