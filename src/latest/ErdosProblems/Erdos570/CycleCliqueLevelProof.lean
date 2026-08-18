/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos570.CycleCliqueCycle

/-!
# Independent sets in the early BFS levels

This completes the ordered-level lemma of Erdős--Faudree--Rousseau--Schelp:
color a level vertex by the maximum length of an increasing path from it.
There are at most `m-2` colors, and every color class is independent.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos570

theorem cycleLevelIndependent_of_connected
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) {m : ℕ} (hm : 3 ≤ m) :
    CycleLevelIndependent G m := by
  intro hcycle x i hiPos hiEarly
  let T : BFSTree G x := BFSTree.ofConnected hconn x
  let S := distanceLevel G x i
  let c := m - 2
  have hc : 0 < c := by simp [c]; omega
  have hnoPath : ∀ v ∈ S, ¬ T.MonotonePathFrom i (m - 2) v := by
    intro v hvS hpath
    obtain ⟨f, -, hflevel, hfmono, hfadj⟩ := hpath
    obtain ⟨p, q, d, hpq, hlen, hdle, hcommon, hnotEarlier⟩ :=
      T.exists_exact_merge_segment hconn hm hiEarly f hflevel hfmono
    exact hcycle (T.cycleGraph_isContained_of_exact_merge_segment hm f
      hflevel hfmono hfadj p q d hpq hlen hdle hcommon hnotEarlier)
  have hheight : ∀ v ∈ S, T.monotoneHeight i v < c := by
    intro v hvS
    have hvLevel : G.dist x v = i := mem_distanceLevel.mp hvS
    by_cases hcard : m - 2 ≤ Fintype.card V
    · simpa only [c] using
        T.monotoneHeight_lt_of_not_path hcard hvLevel (hnoPath v hvS)
    · have hle := T.monotoneHeight_le_card i v
      simp only [c]
      omega
  let color : V → Fin c := fun v ↦
    if hv : v ∈ S then ⟨T.monotoneHeight i v, hheight v hv⟩ else ⟨0, hc⟩
  let fiberCard : Fin c → ℕ := fun z ↦
    (S.filter fun v ↦ color v = z).card
  obtain ⟨z, -, hzmax⟩ := Finset.exists_max_image
    (Finset.univ : Finset (Fin c)) fiberCard
    ⟨⟨0, hc⟩, Finset.mem_univ _⟩
  let I := S.filter fun v ↦ color v = z
  refine ⟨I, Finset.filter_subset _ _, ?_, ?_⟩
  · rw [SimpleGraph.isIndepSet_iff]
    intro u huI v hvI huvNe huvAdj
    have huS : u ∈ S := (Finset.mem_filter.mp huI).1
    have hvS : v ∈ S := (Finset.mem_filter.mp hvI).1
    have huColor : color u = z := (Finset.mem_filter.mp huI).2
    have hvColor : color v = z := (Finset.mem_filter.mp hvI).2
    have hheightEq : T.monotoneHeight i u = T.monotoneHeight i v := by
      have hcolorEq : color u = color v := huColor.trans hvColor.symm
      have := congrArg Fin.val hcolorEq
      simpa [color, huS, hvS] using this
    have huLevel : G.dist x u = i := mem_distanceLevel.mp huS
    have hvLevel : G.dist x v = i := mem_distanceLevel.mp hvS
    have hkeyNe : T.orderKey i u ≠ T.orderKey i v := by
      intro hkey
      exact huvAdj.ne (T.orderKey_injective i hkey)
    rcases lt_or_gt_of_ne hkeyNe with huvKey | hvuKey
    · have hgrow := T.monotoneHeight_succ_le huvAdj huLevel hvLevel huvKey
      omega
    · have hgrow := T.monotoneHeight_succ_le huvAdj.symm hvLevel huLevel hvuKey
      omega
  · have hpartition : S.card = ∑ y : Fin c, fiberCard y := by
      rw [Finset.card_eq_sum_card_fiberwise
        (s := S) (t := Finset.univ) (f := color) (by simp)]
    calc
      S.card = ∑ y : Fin c, fiberCard y := hpartition
      _ ≤ ∑ _y : Fin c, fiberCard z :=
        Finset.sum_le_sum fun y hy ↦ hzmax y (Finset.mem_univ y)
      _ = c * I.card := by simp [fiberCard, I]
      _ = (m - 2) * I.card := by simp [c]

end Erdos570
