import Wikipedia.NoExoticSixSphere.JamesSphereFiberQuotientFirstHomology
import Wikipedia.NoExoticSixSphere.JamesSphereFiberQuotientHomologyRange
import Wikipedia.NoExoticSixSphere.NativeFirstDegreeHomologyComparison

/-!
# The original fiber-to-quotient native map reaches its first nonzero degree

The checked actual homology comparison and lower connectivity give native
bijectivity through degree `2n - 1`. This includes the first potentially
nonzero degree, not just the preceding zero-group range. The remaining
metastable degrees through `3n - 3` are not asserted here.
-/

noncomputable section

namespace NoExoticSixSphere.JamesSphere.FiberQuotient

theorem hom_bijective_first_range (n d : ℕ) [NeZero d] (hn : 2 ≤ n)
    (hdn : d + 1 ≤ 2 * n) : Function.Bijective (hom n d) := by
  by_cases hd : 2 ≤ d
  · let := fiber_simplyConnected n hn
    let := FirstStageQuotient.loops_simplyConnected n hn
    apply (hom_bijective_iff_toLoops n d).mpr
    have hb := NativeFirstDegreeHomologyComparison.map_bijective (toLoops n) d hd
      (fun k hk hkd p ↦ fiber_pi n k hn hk (by omega) p)
      (fun k hk hkd p ↦ FirstStageQuotient.loops_pi_below_bottom n k hn hk (by omega) p)
      (toLoops_homology_bijective_first_range n d hn hd hdn) (basepoint n)
    exact (NativeHomotopyTargetEquality.map_bijective_iff d (toLoops n)
      (toLoops_basepoint n)).mpr hb
  · exact hom_bijective_below_bottom n d hn (by omega)

end NoExoticSixSphere.JamesSphere.FiberQuotient
