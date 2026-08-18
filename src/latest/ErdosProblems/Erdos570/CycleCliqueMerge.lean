/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos570.CycleCliqueMonotone

/-!
# The merge-depth segment in the ordered BFS-level argument

Among consecutive vertices of an increasing path in one BFS level, choose a
pair whose two parent chains merge as late as possible.  A subpath of the
right length around that pair has endpoints whose parent chains merge at
exactly the chosen depth.  This is the numerical/geometric datum from which
the forbidden cycle is assembled.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos570

namespace BFSTree

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {root : V}

/-- A vertex certified to lie in distance level `i`. -/
abbrev LevelVertex (G : SimpleGraph V) (root : V) (i : ℕ) :=
  {v : V // G.dist root v = i}

theorem levelCommonAncestorExists
    (T : BFSTree G root) (hconn : G.Connected) (i : ℕ)
    (u v : LevelVertex G root i) :
    ∃ r : ℕ, T.ancestor r u.1 = T.ancestor r v.1 := by
  refine ⟨i, ?_⟩
  have hu := T.ancestor_dist_eq_root hconn u.1
  have hv := T.ancestor_dist_eq_root hconn v.1
  rw [u.2] at hu
  rw [v.2] at hv
  exact hu.trans hv.symm

/-- The first depth at which the two BFS parent chains meet. -/
def mergeDepth
    (T : BFSTree G root) (hconn : G.Connected) (i : ℕ)
    (u v : LevelVertex G root i) : ℕ :=
  Nat.find (T.levelCommonAncestorExists hconn i u v)

theorem mergeDepth_spec
    (T : BFSTree G root) (hconn : G.Connected) (i : ℕ)
    (u v : LevelVertex G root i) :
    T.ancestor (T.mergeDepth hconn i u v) u.1 =
      T.ancestor (T.mergeDepth hconn i u v) v.1 := by
  simpa only [mergeDepth] using
    (Nat.find_spec (T.levelCommonAncestorExists hconn i u v))

theorem mergeDepth_min
    (T : BFSTree G root) (hconn : G.Connected) (i : ℕ)
    (u v : LevelVertex G root i) {r : ℕ}
    (hr : r < T.mergeDepth hconn i u v) :
    T.ancestor r u.1 ≠ T.ancestor r v.1 := by
  simpa only [mergeDepth] using
    (Nat.find_min (T.levelCommonAncestorExists hconn i u v) hr)

theorem mergeDepth_le_level
    (T : BFSTree G root) (hconn : G.Connected) (i : ℕ)
    (u v : LevelVertex G root i) :
    T.mergeDepth hconn i u v ≤ i := by
  change Nat.find (T.levelCommonAncestorExists hconn i u v) ≤ i
  apply Nat.find_min' (T.levelCommonAncestorExists hconn i u v)
  have hu := T.ancestor_dist_eq_root hconn u.1
  have hv := T.ancestor_dist_eq_root hconn v.1
  rw [u.2] at hu
  rw [v.2] at hv
  exact hu.trans hv.symm

theorem mergeDepth_pos_of_ne
    (T : BFSTree G root) (hconn : G.Connected) (i : ℕ)
    (u v : LevelVertex G root i) (huv : u.1 ≠ v.1) :
    0 < T.mergeDepth hconn i u v := by
  by_contra hnot
  have hd0 : T.mergeDepth hconn i u v = 0 := by omega
  have hspec := T.mergeDepth_spec hconn i u v
  rw [hd0] at hspec
  simpa using huv hspec

/-- The selected subpath and merge depth.  The endpoints are given as
indices into the original path.  Their separation plus the two tree arms is
exactly `m`, their depth-`d` ancestors agree, and they do not agree earlier. -/
theorem exists_exact_merge_segment
    (T : BFSTree G root) (hconn : G.Connected)
    {m i : ℕ} (hm : 3 ≤ m) (hi : i ≤ (m - 1) / 2)
    (f : Fin ((m - 2) + 1) → V)
    (hflevel : ∀ j, G.dist root (f j) = i)
    (hfmono : StrictMono (fun j ↦ T.orderKey i (f j))) :
    ∃ (p q : Fin ((m - 2) + 1)) (d : ℕ),
      p.val < q.val ∧
      q.val - p.val + 2 * d = m ∧
      d ≤ i ∧
      T.ancestor d (f p) = T.ancestor d (f q) ∧
      ∀ r < d, T.ancestor r (f p) ≠ T.ancestor r (f q) := by
  let L := m - 2
  have hL : 0 < L := by simp [L]; omega
  let fp : Fin (L + 1) → LevelVertex G root i :=
    fun j ↦ ⟨f (Fin.cast (by simp [L]) j), hflevel _⟩
  have hfpmono : StrictMono (fun j ↦ T.orderKey i (fp j).1) := by
    intro a b hab
    apply hfmono
    simpa [fp] using hab
  let depth : Fin L → ℕ := fun j ↦
    T.mergeDepth hconn i (fp j.castSucc) (fp j.succ)
  obtain ⟨j, -, hjmax⟩ := Finset.exists_max_image
    (Finset.univ : Finset (Fin L)) depth
    ⟨⟨0, hL⟩, Finset.mem_univ _⟩
  let d := depth j
  have hdle : d ≤ i := T.mergeDepth_le_level hconn i _ _
  have hjne : (fp j.castSucc).1 ≠ (fp j.succ).1 := by
    intro heq
    have hidx : (j.castSucc : Fin (L + 1)) = j.succ := by
      apply hfpmono.injective
      exact congrArg (T.orderKey i) heq
    simpa using congrArg Fin.val hidx
  have hdpos : 0 < d := T.mergeDepth_pos_of_ne hconn i _ _ hjne
  let ell := m - 2 * d
  have hellpos : 0 < ell := by simp [ell]; omega
  have helldef : ell + 2 * d = m := by simp [ell]; omega
  have hellL : ell ≤ L := by simp [ell, L]; omega
  let pNat := min j.val (L - ell)
  let qNat := pNat + ell
  have hpNat_le_j : pNat ≤ j.val := by simp [pNat]
  have hj_lt_qNat : j.val < qNat := by
    simp only [pNat, qNat]
    rcases le_total j.val (L - ell) with h | h
    · rw [min_eq_left h]
      omega
    · rw [min_eq_right h]
      have hjL := j.isLt
      omega
  have hqNat_le : qNat ≤ L := by
    simp only [pNat, qNat]
    exact Nat.add_le_of_le_sub hellL (min_le_right _ _)
  let pL : Fin (L + 1) := ⟨pNat, by omega⟩
  let qL : Fin (L + 1) := ⟨qNat, by omega⟩
  have hcommon : T.ancestor d (fp pL).1 = T.ancestor d (fp qL).1 := by
    have hchain : ∀ (t : ℕ) (ht : t ≤ ell),
        T.ancestor d (fp pL).1 =
          T.ancestor d (fp (⟨pNat + t, by
            have : pNat + t ≤ qNat := by simp [qNat]; omega
            exact this.trans_lt (hqNat_le.trans_lt (Nat.lt_succ_self L))
            ⟩ : Fin (L + 1))).1 := by
      intro t ht
      induction t with
      | zero => rfl
      | succ t iht =>
          have ht' : t ≤ ell := by omega
          rw [iht ht']
          let a : Fin L := ⟨pNat + t, by
            have : pNat + (t + 1) ≤ qNat := by simp [qNat]; omega
            omega⟩
          let da := depth a
          have hdale : da ≤ d := hjmax a (Finset.mem_univ a)
          have hda := T.mergeDepth_spec hconn i (fp a.castSucc) (fp a.succ)
          have hadd := T.ancestor_add_eq_of_ancestor_eq hda (d - da)
          have hsum : da + (d - da) = d := Nat.add_sub_of_le hdale
          change T.ancestor (da + (d - da)) (fp a.castSucc).1 =
            T.ancestor (da + (d - da)) (fp a.succ).1 at hadd
          rw [hsum] at hadd
          convert hadd using 1 <;> simp [a] <;> congr 1
    simpa [qL, qNat] using hchain ell le_rfl
  have hnotEarlier : ∀ r < d,
      T.ancestor r (fp pL).1 ≠ T.ancestor r (fp qL).1 := by
    intro r hrd heq
    have hri : r ≤ i := (Nat.le_of_lt hrd).trans hdle
    have hpj : (pL : Fin (L + 1)) ≤ j.castSucc := by
      exact Fin.mk_le_mk.mpr hpNat_le_j
    have hjq : j.castSucc ≤ qL := by
      exact Fin.mk_le_mk.mpr (Nat.le_of_lt hj_lt_qNat)
    have hjsq : j.succ ≤ qL := by
      exact Fin.mk_le_mk.mpr hj_lt_qNat
    have hkeypj : T.orderKey i (fp pL).1 ≤
        T.orderKey i (fp j.castSucc).1 := by
      exact hfpmono.monotone hpj
    have hkeyjq : T.orderKey i (fp j.castSucc).1 ≤
        T.orderKey i (fp qL).1 := by
      exact hfpmono.monotone hjq
    have hkeypsj : T.orderKey i (fp pL).1 ≤
        T.orderKey i (fp j.succ).1 := by
      have hpjs : pL ≤ j.succ := hpj.trans
        (show j.castSucc ≤ j.succ from Fin.castSucc_lt_succ.le)
      exact hfpmono.monotone hpjs
    have hkeysjq : T.orderKey i (fp j.succ).1 ≤
        T.orderKey i (fp qL).1 := by
      exact hfpmono.monotone hjsq
    have hjAnc := T.ancestor_eq_of_orderKey_closed_between hri
      hkeypj hkeyjq heq
    have hjsAnc := T.ancestor_eq_of_orderKey_closed_between hri
      hkeypsj hkeysjq heq
    exact (T.mergeDepth_min hconn i (fp j.castSucc) (fp j.succ) hrd)
      (hjAnc.trans hjsAnc.symm)
  let p : Fin ((m - 2) + 1) := Fin.cast (by simp [L]) pL
  let q : Fin ((m - 2) + 1) := Fin.cast (by simp [L]) qL
  refine ⟨p, q, d, ?_, ?_, hdle, ?_, ?_⟩
  · simpa [p, q, pL, qL, qNat] using hellpos
  · simp only [p, q, pL, qL, qNat]
    change (pNat + ell) - pNat + 2 * d = m
    have hdiff : (pNat + ell) - pNat = ell := Nat.add_sub_cancel_left _ _
    rw [hdiff]
    exact helldef
  · simpa [p, q, fp, pL, qL] using hcommon
  · intro r hr
    simpa [p, q, fp, pL, qL] using hnotEarlier r hr

end BFSTree

end Erdos570
