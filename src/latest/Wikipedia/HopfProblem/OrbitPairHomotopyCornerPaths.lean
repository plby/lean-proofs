import Wikipedia.HopfProblem.OrbitPairHomotopyCornerSweep
import Wikipedia.NoExoticSixSphere.PathFamilyCurrying

/-!
# Based path homotopies from squares with two constant sides

The explicit corner sweep retains joint continuity and every protected
parameter. This is used to extract a based loop homotopy from a nullhomotopy
in an actual homotopy fibre.
-/

noncomputable section

namespace Wikipedia.HopfProblem.OrbitPair.HomotopyCorner

open NoExoticSixSphere

variable {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]

def pathFamilyHomotopy (b : Y) (B L : C(Z, Path b b)) (S : Set Z)
    (H : C(unitInterval × (unitInterval × Z), Y))
    (hbottom : ∀ t z, H (t, (0, z)) = B z t)
    (hleft : ∀ t z, H (0, (t, z)) = L z t)
    (hright : ∀ t z, H (1, (t, z)) = b)
    (htop : ∀ t z, H (t, (1, z)) = b)
    (hfixed : ∀ s t z, z ∈ S → H (s, (t, z)) = b) : B.HomotopyRel L S := by
  apply PathFamilies.curryHomotopy
  refine {
    toFun := fun z ↦ H ((sweep z.1 z.2.1).1, ((sweep z.1 z.2.1).2, z.2.2))
    continuous_toFun := ?_
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }
  · have hs : Continuous (fun z : unitInterval × (unitInterval × Z) ↦ sweep z.1 z.2.1) :=
      continuous_sweep.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
    exact H.continuous.comp ((continuous_fst.comp hs).prodMk
      ((continuous_snd.comp hs).prodMk (continuous_snd.comp continuous_snd)))
  · intro z
    change H ((sweep 0 z.1).1, ((sweep 0 z.1).2, z.2)) = B z.2 z.1
    rw [sweep_zero]
    exact hbottom z.1 z.2
  · intro z
    change H ((sweep 1 z.1).1, ((sweep 1 z.1).2, z.2)) = L z.2 z.1
    rw [sweep_one]
    exact hleft z.1 z.2
  · intro r z hz
    rcases z with ⟨t, z⟩
    change H ((sweep r t).1, ((sweep r t).2, z)) = B z t
    rcases hz with ht | ht | hz
    · change t = 0 at ht
      subst t
      rw [sweep_start]
      exact hbottom 0 z
    · change t = 1 at ht
      subst t
      rw [Path.target]
      rcases sweep_end r with h | h
      · rw [h]
        exact hright _ z
      · rw [h]
        exact htop _ z
    · exact (hfixed _ _ z hz).trans ((hfixed t 0 z hz).symm.trans (hbottom t z))

end Wikipedia.HopfProblem.OrbitPair.HomotopyCorner
