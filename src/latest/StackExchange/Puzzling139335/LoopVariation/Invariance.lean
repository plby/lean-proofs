import StackExchange.Puzzling139335.LoopVariation.Invariance.Rotation
import StackExchange.Puzzling139335.LoopVariation.Invariance.CommonBase

/-!
# Image invariance of cyclic finite-resolution variation

The proof uses actual finite cyclic chains. One loop is rotated to give the
two parametrizations a common starting point; deleting that point gives an
increasing or decreasing change of interval parameters. Rotating or reversing
the resulting finite parameter lists preserves their cyclic scores exactly.
-/

open Set

namespace Puzzling139335.LoopVariation

noncomputable section

variable {X : Type*}

/-- The closing endpoint adds no new image point to a closed interval loop. -/
theorem image_Icc_eq_image_Ico_of_closes {f : ℝ → X} {a b : ℝ}
    (hab : a < b) (hclose : f a = f b) : f '' Icc a b = f '' Ico a b := by
  apply Subset.antisymm
  · rintro z ⟨t, ht, rfl⟩
    by_cases htb : t < b
    · exact ⟨t, ⟨ht.1, htb⟩, rfl⟩
    · have ht' : t = b := le_antisymm ht.2 (le_of_not_gt htb)
      exact ⟨a, ⟨le_rfl, hab⟩, by simpa only [ht'] using hclose⟩
  · exact image_mono Ico_subset_Icc_self

variable [PseudoMetricSpace X] [T2Space X]

/-- Equal-image Jordan-loop parametrizations attain exactly the same concrete
cyclic scores. Their starting points and orientations need not agree. -/
theorem cycleScoresOn_eq_of_loop_image_eq (ε : ℝ) {f g : ℝ → X} {a b c d : ℝ}
    (hab : a < b) (hcd : c < d)
    (hfcont : ContinuousOn f (Icc a b)) (hfclose : f a = f b)
    (hfi : InjOn f (Ico a b))
    (hgcont : ContinuousOn g (Icc c d)) (hgclose : g c = g d)
    (hgi : InjOn g (Ico c d))
    (hfg : f '' Icc a b = g '' Icc c d) :
    cycleScoresOn ε f (Icc a b) = cycleScoresOn ε g (Icc c d) := by
  have hfa : f a ∈ g '' Ico c d := by
    rw [← image_Icc_eq_image_Ico_of_closes hcd hgclose, ← hfg]
    exact mem_image_of_mem f (left_mem_Icc.mpr hab.le)
  obtain ⟨q, hq, hqeq⟩ := hfa
  have hq' : q ∈ Icc c d := Ico_subset_Icc_self hq
  have hfg' : f '' Icc a b = rotateLoop g c d q '' Icc c d :=
    hfg.trans (rotateLoop_image_Icc hq' hgclose).symm
  have hbase : f a = rotateLoop g c d q c :=
    hqeq.symm.trans (rotateLoop_start hq).symm
  obtain ⟨φ, hφ_order, hφ_maps, hφ_surj, hφ_agree⟩ :=
    exists_commonBase_loop_reparam hab hcd hfcont hfclose hfi
      (rotateLoop_continuousOn hq' hgcont hgclose) (rotateLoop_closes hq)
      (rotateLoop_injOn_Ico hq' hgi) hfg' hbase
  calc
    cycleScoresOn ε f (Icc a b) =
        cycleScoresOn ε (rotateLoop g c d q ∘ φ) (Icc a b) :=
      cycleScoresOn_congr (fun x hx => (hφ_agree hx).symm)
    _ = cycleScoresOn ε (rotateLoop g c d q) (Icc c d) := by
      rcases hφ_order with hmono | hanti
      · exact cycleScoresOn_comp_eq_of_monotoneOn_surjOn ε (rotateLoop g c d q)
          hmono hφ_maps hφ_surj
      · exact cycleScoresOn_comp_eq_of_antitoneOn_surjOn ε (rotateLoop g c d q)
          hanti hφ_maps hφ_surj
    _ = cycleScoresOn ε g (Icc c d) := cycleScoresOn_rotateLoop ε g hq' hgclose

/-- Cyclic finite-resolution variation depends only on the image of a Jordan
loop, not on its starting point, speed, orientation, or parameter interval.
No finiteness premise or restriction on the resolution is used. -/
theorem loopVariationOn_eq_of_loop_image_eq (ε : ℝ) {f g : ℝ → X} {a b c d : ℝ}
    (hab : a < b) (hcd : c < d)
    (hfcont : ContinuousOn f (Icc a b)) (hfclose : f a = f b)
    (hfi : InjOn f (Ico a b))
    (hgcont : ContinuousOn g (Icc c d)) (hgclose : g c = g d)
    (hgi : InjOn g (Ico c d))
    (hfg : f '' Icc a b = g '' Icc c d) :
    loopVariationOn ε f (Icc a b) = loopVariationOn ε g (Icc c d) := by
  unfold loopVariationOn
  rw [cycleScoresOn_eq_of_loop_image_eq ε hab hcd hfcont hfclose hfi
    hgcont hgclose hgi hfg]

end

end Puzzling139335.LoopVariation
