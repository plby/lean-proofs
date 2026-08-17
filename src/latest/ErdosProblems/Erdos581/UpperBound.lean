import ErdosProblems.Erdos581.UpperPadding

/-!
# Erdős 581: the uniform upper bound
-/

namespace Erdos581

/-- The upper half of the resolution of Erdős 581. -/
theorem upper_bound (m : ℕ) :
    (f m : ℝ) ≤ (m : ℝ) / 2 +
      1024 * (m : ℝ) ^ ((4 : ℝ) / 5) := by
  rcases uniformUpperWitness m with ⟨V, iV, G, htri, hedge, hcut⟩
  letI : Fintype V := iV
  obtain ⟨H, hHG, hHbip, hfH⟩ := f_spec m V G htri hedge
  obtain ⟨s, hHcut⟩ := ncard_le_cutGraph_of_bipartite hHG hHbip
  have hfHR : (f m : ℝ) ≤ (H.edgeSet.ncard : ℝ) := by exact_mod_cast hfH
  have hHcutR : (H.edgeSet.ncard : ℝ) ≤
      ((cutGraph G s).edgeSet.ncard : ℝ) := by exact_mod_cast hHcut
  exact hfHR.trans (hHcutR.trans (hcut s))

end Erdos581
