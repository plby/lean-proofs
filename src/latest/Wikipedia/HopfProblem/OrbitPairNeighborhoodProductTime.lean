import Wikipedia.HopfProblem.OrbitPairNeighborhoodHomotopyExtension

/-!
# Time parameters for a product-boundary deformation

The factor with smaller height runs for the full time. The other factor
is slowed by the ratio of the two heights. At a zero height the other
factor does not move, so the product-boundary union stays fixed.
-/

noncomputable section

open unitInterval Set Topology

namespace Wikipedia.HopfProblem.OrbitPair.NeighborhoodProduct

def ratio (u v : I) : I :=
  Set.projIcc 0 1 zero_le_one ((v : ℝ) / max (u : ℝ) (v : ℝ))

theorem ratio_right_zero (u : I) : ratio u 0 = 0 := by
  change Set.projIcc 0 1 zero_le_one ((0 : ℝ) / max (u : ℝ) 0) = 0
  rw [zero_div]
  exact Set.projIcc_left _

theorem ratio_of_le (u v : I) (h : u ≤ v) (hv : v ≠ 0) : ratio u v = 1 := by
  have hn : (v : ℝ) ≠ 0 := fun h ↦ hv (Subtype.ext h)
  have h' : (u : ℝ) ≤ (v : ℝ) := h
  change Set.projIcc 0 1 zero_le_one ((v : ℝ) / max (u : ℝ) (v : ℝ)) = 1
  rw [max_eq_right h', div_self hn]
  exact Set.projIcc_right _

theorem ratio_continuousAt (p : I × I) (hp : p.1 ≠ 0) :
    ContinuousAt (fun q : I × I ↦ ratio q.1 q.2) p := by
  have hn : (p.1 : ℝ) ≠ 0 := fun h ↦ hp (Subtype.ext h)
  have hpos : (0 : ℝ) < p.1 := lt_of_le_of_ne p.1.property.1 hn.symm
  have hm : max (p.1 : ℝ) (p.2 : ℝ) ≠ 0 :=
    ne_of_gt (hpos.trans_le (le_max_left _ _))
  exact continuous_projIcc.continuousAt.comp
    ((continuous_subtype_val.comp continuous_snd).continuousAt.div
      ((continuous_subtype_val.comp continuous_fst).max
        (continuous_subtype_val.comp continuous_snd)).continuousAt hm)

theorem smaller_lt_one (u v : I) (h : u ≤ v) (hp : u * v < 1) : u < 1 := by
  apply lt_of_le_of_ne (show u ≤ 1 from u.property.2)
  intro hu
  have hv : v = 1 := le_antisymm (show v ≤ 1 from v.property.2) (hu ▸ h)
  rw [hu, hv, one_mul] at hp
  exact lt_irrefl _ hp

end Wikipedia.HopfProblem.OrbitPair.NeighborhoodProduct
