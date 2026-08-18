/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos570.CycleCliqueMerge
import ErdosProblems.Erdos570.CycleSequence

/-!
# Closing the exact merge segment to a cycle

The cyclic sequence runs along the selected level path, climbs the parent
chain from its right endpoint to the common ancestor, and descends the other
parent chain to the left endpoint.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos570

namespace BFSTree

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {root : V}

theorem cycleGraph_isContained_of_exact_merge_segment
    (T : BFSTree G root)
    {m i : ℕ} (hm : 3 ≤ m)
    (f : Fin ((m - 2) + 1) → V)
    (hflevel : ∀ j, G.dist root (f j) = i)
    (hfmono : StrictMono (fun j ↦ T.orderKey i (f j)))
    (hfadj : ∀ j : Fin (m - 2),
      G.Adj (f j.castSucc) (f j.succ))
    (p q : Fin ((m - 2) + 1)) (d : ℕ)
    (hpq : p.val < q.val)
    (hlen : q.val - p.val + 2 * d = m)
    (hdle : d ≤ i)
    (hcommon : T.ancestor d (f p) = T.ancestor d (f q))
    (hnotEarlier : ∀ r < d,
      T.ancestor r (f p) ≠ T.ancestor r (f q)) :
    SimpleGraph.cycleGraph m ⊑ G := by
  let ell := q.val - p.val
  have hpqle : p.val ≤ q.val := Nat.le_of_lt hpq
  have hpell : p.val + ell = q.val := by
    simpa only [ell] using Nat.add_sub_of_le hpqle
  have hqbound : q.val ≤ m - 2 := by omega
  have hdpos : 0 < d := by
    have hdiff_le : q.val - p.val ≤ m - 2 := by omega
    omega
  have hiPos : 0 < i := hdpos.trans_le hdle
  have hellm : ell + 2 * d = m := by simpa only [ell] using hlen
  let pathAt (n : ℕ) : V :=
    f ⟨min (p.val + n) (m - 2), by omega⟩
  have pathAt_eq (n : ℕ) (hn : n ≤ ell) :
      pathAt n = f ⟨p.val + n, by omega⟩ := by
    have hle : p.val + n ≤ m - 2 := by omega
    simp [pathAt, min_eq_left hle]
  have pathAt_zero : pathAt 0 = f p := by
    rw [pathAt_eq 0 (Nat.zero_le _)]
    congr 1
  have pathAt_ell : pathAt ell = f q := by
    rw [pathAt_eq ell le_rfl]
    apply congrArg f
    apply Fin.ext
    exact hpell
  let cyc : Fin m → V := fun z ↦
    if z.val ≤ ell then pathAt z.val
    else if z.val ≤ ell + d then
      T.ancestor (z.val - ell) (f q)
    else T.ancestor (m - z.val) (f p)
  have hcyc_path (z : Fin m) (hz : z.val ≤ ell) :
      cyc z = pathAt z.val := by simp [cyc, hz]
  have hcyc_right (z : Fin m) (hz₁ : ell < z.val)
      (hz₂ : z.val ≤ ell + d) :
      cyc z = T.ancestor (z.val - ell) (f q) := by
    simp [cyc, Nat.not_le_of_lt hz₁, hz₂]
  have hcyc_left (z : Fin m) (hz : ell + d < z.val) :
      cyc z = T.ancestor (m - z.val) (f p) := by
    have hzell : ¬ z.val ≤ ell := by omega
    have hzright : ¬ z.val ≤ ell + d := Nat.not_le_of_lt hz
    simp [cyc, hzell, hzright]
  have hfinj : Function.Injective f :=
    Function.Injective.of_comp hfmono.injective
  have hdist_path (n : ℕ) (hn : n ≤ ell) :
      G.dist root (pathAt n) = i := by
    rw [pathAt_eq n hn]
    exact hflevel _
  have hdist_q (r : ℕ) (hr : r ≤ d) :
      G.dist root (T.ancestor r (f q)) = i - r := by
    have hr' : r ≤ G.dist root (f q) := by rw [hflevel q]; omega
    rw [T.dist_ancestor (f q) hr', hflevel q]
  have hdist_p (r : ℕ) (hr : r ≤ d) :
      G.dist root (T.ancestor r (f p)) = i - r := by
    have hr' : r ≤ G.dist root (f p) := by rw [hflevel p]; omega
    rw [T.dist_ancestor (f p) hr', hflevel p]
  have hordered : ∀ (a b : Fin m), a.val < b.val → cyc a ≠ cyc b := by
    intro a b hablt hab
    have hcase : a.val ≤ ell ∨ ell < a.val := le_or_gt _ _
    rcases hcase with haPath | haAfter
    · rcases le_or_gt b.val ell with hbPath | hbAfter
      · rw [hcyc_path a haPath, hcyc_path b hbPath] at hab
        have hidx := congrArg Fin.val (hfinj hab)
        have : a.val = b.val := by
          simpa [pathAt, min_eq_left (by omega : p.val + a.val ≤ m - 2),
            min_eq_left (by omega : p.val + b.val ≤ m - 2)] using hidx
        omega
      · rw [hcyc_path a haPath] at hab
        rcases le_or_gt b.val (ell + d) with hbRight | hbLeft
        · have hrpos : 0 < b.val - ell := by omega
          have hrle : b.val - ell ≤ i := by omega
          rw [hcyc_right b hbAfter hbRight] at hab
          have hdist := congrArg (G.dist root) hab
          rw [hdist_path a.val haPath,
            hdist_q (b.val - ell) (by omega)] at hdist
          omega
        · have hspos : 0 < m - b.val := by omega
          have hsle : m - b.val ≤ i := by omega
          rw [hcyc_left b hbLeft] at hab
          have hdist := congrArg (G.dist root) hab
          rw [hdist_path a.val haPath,
            hdist_p (m - b.val) (by omega)] at hdist
          omega
    · rcases le_or_gt a.val (ell + d) with haRight | haLeft
      · rcases le_or_gt b.val (ell + d) with hbRight | hbLeft
        · rw [hcyc_right a haAfter haRight,
            hcyc_right b (haAfter.trans hablt) hbRight] at hab
          have harle : a.val - ell ≤ i := by omega
          have hbrle : b.val - ell ≤ i := by omega
          have hdist := congrArg (G.dist root) hab
          rw [hdist_q (a.val - ell) (by omega),
            hdist_q (b.val - ell) (by omega)] at hdist
          omega
        · rw [hcyc_right a haAfter haRight,
            hcyc_left b hbLeft] at hab
          have hrpos : 0 < a.val - ell := by omega
          have hspos : 0 < m - b.val := by omega
          have hslt : m - b.val < d := by omega
          have hrle : a.val - ell ≤ i := by omega
          have hsle : m - b.val ≤ i := by omega
          have hdist := congrArg (G.dist root) hab
          rw [hdist_q (a.val - ell) (by omega),
            hdist_p (m - b.val) (by omega)] at hdist
          have hrs : a.val - ell = m - b.val := by omega
          rw [hrs] at hab
          exact (hnotEarlier (m - b.val) hslt) hab.symm
      · have hbLeft : ell + d < b.val := haLeft.trans hablt
        rw [hcyc_left a haLeft, hcyc_left b hbLeft] at hab
        have hasle : m - a.val ≤ i := by omega
        have hbsle : m - b.val ≤ i := by omega
        have hdist := congrArg (G.dist root) hab
        rw [hdist_p (m - a.val) (by omega),
          hdist_p (m - b.val) (by omega)] at hdist
        omega
  have hcycinj : Function.Injective cyc := by
    intro a b hab
    apply Fin.ext
    by_contra hne
    rcases lt_or_gt_of_ne hne with hablt | hbalt
    · exact (hordered a b hablt) hab
    · exact (hordered b a hbalt) hab.symm
  apply cycleGraph_isContained_of_sequence cyc hcycinj
  · intro a b habSucc
    have habVal : b.val = a.val + 1 := by omega
    rcases le_or_gt a.val ell with haPath | haAfter
    · by_cases hbPath : b.val ≤ ell
      · rw [hcyc_path a haPath, hcyc_path b hbPath]
        rw [pathAt_eq a.val haPath, pathAt_eq b.val hbPath]
        let j : Fin (m - 2) := ⟨p.val + a.val, by omega⟩
        convert hfadj j using 1 <;> congr 1 <;> apply Fin.ext <;>
          simp [j, habVal] <;> omega
      · have haEq : a.val = ell := by omega
        have hbRight : b.val ≤ ell + d := by omega
        rw [hcyc_path a haPath, hcyc_right b (by omega) hbRight,
          haEq, habVal, pathAt_ell]
        have hdepth : a.val + 1 - ell = 1 := by omega
        rw [hdepth]
        simpa using (T.adj_ancestor_succ (f q) (r := 0)
          (by simpa [hflevel q] using hiPos)).symm
    · rcases le_or_gt a.val (ell + d) with haRight | haLeft
      · by_cases hbRight : b.val ≤ ell + d
        · rw [hcyc_right a haAfter haRight,
            hcyc_right b (by omega) hbRight]
          have hr : b.val - ell = (a.val - ell) + 1 := by omega
          rw [hr]
          exact (T.adj_ancestor_succ (f q) (r := a.val - ell)
            (by rw [hflevel q]; omega)).symm
        · have haEq : a.val = ell + d := by omega
          have hdTwo : 2 ≤ d := by omega
          rw [hcyc_right a haAfter haRight, hcyc_left b (by omega),
            haEq, habVal]
          have hrightDepth : ell + d - ell = d := by omega
          have hleftDepth : m - (ell + d + 1) = d - 1 := by omega
          rw [hrightDepth]
          have hactualLeft : m - (a.val + 1) = d - 1 := by omega
          rw [hactualLeft, ← hcommon]
          have hadj := T.adj_ancestor_succ (f p) (r := d - 1)
            (by rw [hflevel p]; omega)
          simpa [Nat.sub_add_cancel (by omega : 1 ≤ d)] using hadj
      · have hbLeft : ell + d < b.val := haLeft.trans (by omega)
        rw [hcyc_left a haLeft, hcyc_left b hbLeft]
        have hdepth : m - a.val = (m - b.val) + 1 := by omega
        rw [hdepth]
        exact T.adj_ancestor_succ (f p) (r := m - b.val)
          (by rw [hflevel p]; omega)
  · intro a b ha0 hblast
    let z0 : Fin m := ⟨0, by omega⟩
    let zlast : Fin m := ⟨m - 1, by omega⟩
    have ha : a = z0 := Fin.ext ha0
    have hb : b = zlast := Fin.ext (by simp [zlast]; omega)
    have hzero : cyc z0 = f p := by
      rw [hcyc_path z0 (by simp [z0])]
      simp only [z0]
      exact pathAt_zero
    have hlast : cyc zlast = T.ancestor 1 (f p) := by
      by_cases hd1 : d = 1
      · have hright : zlast.val ≤ ell + d := by simp [zlast]; omega
        have hafter : ell < zlast.val := by simp [zlast]; omega
        rw [hcyc_right zlast hafter hright]
        simp only [zlast]
        have hdepth : m - 1 - ell = d := by omega
        rw [hdepth, ← hcommon, hd1]
      · have hd2 : 2 ≤ d := by omega
        have hleft : ell + d < zlast.val := by simp [zlast]; omega
        rw [hcyc_left zlast hleft]
        simp only [zlast]
        have hdepth : m - (m - 1) = 1 := by omega
        rw [hdepth]
    rw [ha, hb, hzero, hlast]
    exact (T.adj_ancestor_succ (f p) (r := 0)
      (by simpa [hflevel p] using hiPos)).symm

end BFSTree

end Erdos570
