/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import Mathlib
import ErdosProblems.Erdos594

/-!
# Canonical breadth-first parent walks for Erdős Problem 752

This file chooses one parent of every non-root vertex in a connected graph.
The parent is one step closer to the root.  Iterating these choices gives a
coherent family of geodesics: whenever a vertex occurs on one of the chosen
root paths, the initial segment ending there is the chosen path to that
vertex.  The construction is classical but deterministic after the choices
have been made.
-/

open Function Set SimpleGraph

namespace Erdos752

noncomputable section

attribute [local instance] Classical.propDecidable

universe u

variable {V : Type u}

/-- A fixed shortest path from `root` to `v`.  This auxiliary choice is used
only to choose the immediate parent of `v`; the coherent paths below are
obtained by iterating the resulting parent map. -/
noncomputable def bfsSeedGeodesic (G : SimpleGraph V) (hconn : G.Connected)
    (root v : V) : G.Walk root v :=
  Classical.choose (hconn.exists_path_of_dist root v)

lemma bfsSeedGeodesic_isPath (G : SimpleGraph V) (hconn : G.Connected)
    (root v : V) : (bfsSeedGeodesic G hconn root v).IsPath :=
  (Classical.choose_spec (hconn.exists_path_of_dist root v)).1

lemma bfsSeedGeodesic_length (G : SimpleGraph V) (hconn : G.Connected)
    (root v : V) :
    (bfsSeedGeodesic G hconn root v).length = G.dist root v :=
  (Classical.choose_spec (hconn.exists_path_of_dist root v)).2

/-- The canonical BFS parent.  At the root it is the root itself. -/
noncomputable def bfsParent (G : SimpleGraph V) (hconn : G.Connected)
    (root v : V) : V :=
  if v = root then root else (bfsSeedGeodesic G hconn root v).penultimate

@[simp]
lemma bfsParent_root (G : SimpleGraph V) (hconn : G.Connected) (root : V) :
    bfsParent G hconn root root = root := by
  simp [bfsParent]

lemma bfsSeedGeodesic_not_nil (G : SimpleGraph V) (hconn : G.Connected)
    (root : V) {v : V} (hv : v ≠ root) :
    ¬(bfsSeedGeodesic G hconn root v).Nil := by
  rw [Walk.not_nil_iff_lt_length, bfsSeedGeodesic_length]
  exact hconn.pos_dist_of_ne hv.symm

lemma bfsParent_eq_penultimate (G : SimpleGraph V) (hconn : G.Connected)
    (root : V) {v : V} (hv : v ≠ root) :
    bfsParent G hconn root v =
      (bfsSeedGeodesic G hconn root v).penultimate := by
  simp [bfsParent, hv]

lemma bfsParent_adj (G : SimpleGraph V) (hconn : G.Connected)
    (root : V) {v : V} (hv : v ≠ root) :
    G.Adj (bfsParent G hconn root v) v := by
  rw [bfsParent_eq_penultimate G hconn root hv]
  exact (bfsSeedGeodesic G hconn root v).adj_penultimate
    (bfsSeedGeodesic_not_nil G hconn root hv)

/-- A non-root vertex is exactly one layer above its chosen parent. -/
lemma bfsParent_dist_add_one (G : SimpleGraph V) (hconn : G.Connected)
    (root : V) {v : V} (hv : v ≠ root) :
    G.dist root (bfsParent G hconn root v) + 1 = G.dist root v := by
  let p := bfsSeedGeodesic G hconn root v
  have hp : p.length = G.dist root v := bfsSeedGeodesic_length G hconn root v
  have hp_nonempty : ¬p.Nil := bfsSeedGeodesic_not_nil G hconn root hv
  have hdrop : p.dropLast.length = G.dist root p.penultimate :=
    length_eq_dist_of_subwalk hp (Walk.isSubwalk_take p (p.length - 1))
  rw [bfsParent_eq_penultimate G hconn root hv]
  change G.dist root p.penultimate + 1 = G.dist root v
  rw [← hdrop, ← hp]
  exact p.length_dropLast_add_one hp_nonempty

lemma bfsParent_dist_lt (G : SimpleGraph V) (hconn : G.Connected)
    (root : V) {v : V} (hv : v ≠ root) :
    G.dist root (bfsParent G hconn root v) < G.dist root v := by
  have := bfsParent_dist_add_one G hconn root hv
  omega

/-- The coherent canonical walk obtained by repeatedly following BFS parents.
It is defined by recursion on distance from the root. -/
noncomputable def bfsParentWalk (G : SimpleGraph V) (hconn : G.Connected)
    (root v : V) : G.Walk root v :=
  if hv : v = root then hv ▸ .nil
  else
    (bfsParentWalk G hconn root (bfsParent G hconn root v)).concat
      (bfsParent_adj G hconn root hv)
termination_by G.dist root v
decreasing_by exact bfsParent_dist_lt G hconn root hv

@[simp]
lemma bfsParentWalk_root (G : SimpleGraph V) (hconn : G.Connected) (root : V) :
    bfsParentWalk G hconn root root = .nil := by
  rw [bfsParentWalk]
  simp

lemma bfsParentWalk_eq_concat (G : SimpleGraph V) (hconn : G.Connected)
    (root : V) {v : V} (hv : v ≠ root) :
    bfsParentWalk G hconn root v =
      (bfsParentWalk G hconn root (bfsParent G hconn root v)).concat
        (bfsParent_adj G hconn root hv) := by
  rw [bfsParentWalk]
  simp [hv]

/-- The canonical parent walk is a geodesic. -/
lemma bfsParentWalk_length (G : SimpleGraph V) (hconn : G.Connected)
    (root v : V) :
    (bfsParentWalk G hconn root v).length = G.dist root v := by
  induction hn : G.dist root v using Nat.strong_induction_on generalizing v with
  | h n ih =>
      by_cases hv : v = root
      · subst v
        simpa using hn
      · rw [bfsParentWalk_eq_concat G hconn root hv, Walk.length_concat]
        have hlt := bfsParent_dist_lt G hconn root hv
        have hlt' : G.dist root (bfsParent G hconn root v) < n := by
          omega
        rw [ih _ hlt' (bfsParent G hconn root v) rfl]
        simpa only [hn] using bfsParent_dist_add_one G hconn root hv

/-- The canonical parent walk has no repeated vertex. -/
lemma bfsParentWalk_isPath (G : SimpleGraph V) (hconn : G.Connected)
    (root v : V) :
    (bfsParentWalk G hconn root v).IsPath :=
  Walk.isPath_of_length_eq_dist _ (bfsParentWalk_length G hconn root v)

/-- The vertex at position `j` of a canonical parent walk lies in BFS layer
`j`. -/
lemma bfsParentWalk_dist_getVert (G : SimpleGraph V) (hconn : G.Connected)
    (root v : V) (j : ℕ)
    (hj : j ≤ (bfsParentWalk G hconn root v).length) :
    G.dist root ((bfsParentWalk G hconn root v).getVert j) = j := by
  let p := bfsParentWalk G hconn root v
  have hgeo : p.length = G.dist root v := bfsParentWalk_length G hconn root v
  have htake : (p.take j).length = G.dist root (p.getVert j) :=
    length_eq_dist_of_subwalk hgeo (p.isSubwalk_take j)
  rw [p.take_length, Nat.min_eq_left hj] at htake
  simpa [p] using htake.symm

/-- Every non-terminal vertex of a canonical parent walk lies strictly below
the terminal BFS layer. -/
lemma bfsParentWalk_internal_dist_lt (G : SimpleGraph V) (hconn : G.Connected)
    (root v x : V) (hx : x ∈ (bfsParentWalk G hconn root v).support)
    (hxv : x ≠ v) :
    G.dist root x < G.dist root v := by
  let p := bfsParentWalk G hconn root v
  have htake : (p.takeUntil x hx).length = G.dist root x :=
    length_eq_dist_of_subwalk (bfsParentWalk_length G hconn root v)
      (p.isSubwalk_takeUntil hx)
  have hlt := p.length_takeUntil_lt_length hx hxv
  simpa [p, bfsParentWalk_length G hconn root v, htake] using hlt

private lemma takeUntil_end_eq_of_geodesic {G : SimpleGraph V} {root v : V}
    (p : G.Walk root v) (hp : p.length = G.dist root v)
    (hv : v ∈ p.support) :
    p.takeUntil v hv = p := by
  have hlen : (p.takeUntil v hv).length = p.length := by
    rw [length_eq_dist_of_subwalk hp (p.isSubwalk_takeUntil hv), hp]
  apply Walk.ext_getVert_le_length hlen
  intro j hj
  exact p.getVert_takeUntil hv (by simpa [hlen] using hj)

/-- Prefix coherence: if `x` occurs on the canonical path to `v`, the
initial segment ending at `x` is definitionally the same chosen path as the
canonical path to `x`. -/
lemma bfsParentWalk_takeUntil (G : SimpleGraph V) (hconn : G.Connected)
    (root v x : V) (hx : x ∈ (bfsParentWalk G hconn root v).support) :
    (bfsParentWalk G hconn root v).takeUntil x hx =
      bfsParentWalk G hconn root x := by
  induction hn : G.dist root v using Nat.strong_induction_on generalizing v x with
  | h n ih =>
      by_cases hv : v = root
      · subst v
        have hxr : x = root := by
          simpa [bfsParentWalk_root] using hx
        subst x
        simp [bfsParentWalk_root]
      · let p := bfsParentWalk G hconn root (bfsParent G hconn root v)
        let e := bfsParent_adj G hconn root hv
        have hwalk : bfsParentWalk G hconn root v = p.concat e :=
          bfsParentWalk_eq_concat G hconn root hv
        have hmem : x ∈ p.support ∨ x = v := by
          rw [hwalk, Walk.support_concat, List.mem_append, List.mem_singleton] at hx
          exact hx
        rcases hmem with hxp | rfl
        · simp only [hwalk, Walk.concat_eq_append]
          rw [Walk.takeUntil_append_of_mem_left p e.toWalk hxp]
          have hlt : G.dist root (bfsParent G hconn root v) < n := by
            have := bfsParent_dist_lt G hconn root hv
            omega
          exact ih _ hlt (bfsParent G hconn root v) x hxp rfl
        · exact takeUntil_end_eq_of_geodesic _
            (bfsParentWalk_length G hconn root _) hx

/-- Membership is inherited by every descendant: if `x` lies on the
canonical root path to `y` and `y` lies on the canonical root path to `v`,
then `x` lies on the canonical root path to `v`. -/
lemma bfsParentWalk_support_trans (G : SimpleGraph V) (hconn : G.Connected)
    (root v y x : V)
    (hy : y ∈ (bfsParentWalk G hconn root v).support)
    (hx : x ∈ (bfsParentWalk G hconn root y).support) :
    x ∈ (bfsParentWalk G hconn root v).support := by
  rw [← bfsParentWalk_takeUntil G hconn root v y hy] at hx
  exact (bfsParentWalk G hconn root v).support_takeUntil_subset_support hy hx

/-- Tree-prefix equality.  If two canonical paths agree at position `k`,
then they agree at every earlier position. -/
lemma bfsParentWalk_getVert_eq_of_eq_at (G : SimpleGraph V)
    (hconn : G.Connected) (root a b : V) {j k : ℕ}
    (hjk : j ≤ k)
    (hka : k ≤ (bfsParentWalk G hconn root a).length)
    (hkb : k ≤ (bfsParentWalk G hconn root b).length)
    (hk : (bfsParentWalk G hconn root a).getVert k =
      (bfsParentWalk G hconn root b).getVert k) :
    (bfsParentWalk G hconn root a).getVert j =
      (bfsParentWalk G hconn root b).getVert j := by
  let pa := bfsParentWalk G hconn root a
  let pb := bfsParentWalk G hconn root b
  let x := pa.getVert k
  have hxa : x ∈ pa.support := pa.getVert_mem_support k
  have hxb : x ∈ pb.support := by
    change pa.getVert k ∈ pb.support
    rw [hk]
    exact pb.getVert_mem_support k
  have hta : (pa.takeUntil x hxa).length = k := by
    apply (bfsParentWalk_isPath G hconn root a).getVert_injOn
      (pa.length_takeUntil_le_length hxa) hka
    exact (pa.getVert_length_takeUntil hxa).trans rfl
  have htb : (pb.takeUntil x hxb).length = k := by
    apply (bfsParentWalk_isPath G hconn root b).getVert_injOn
      (pb.length_takeUntil_le_length hxb) hkb
    exact (pb.getVert_length_takeUntil hxb).trans hk
  have hprefix : pa.takeUntil x hxa = pb.takeUntil x hxb := by
    rw [bfsParentWalk_takeUntil G hconn root a x hxa,
      bfsParentWalk_takeUntil G hconn root b x hxb]
  calc
    pa.getVert j = (pa.takeUntil x hxa).getVert j :=
      (pa.getVert_takeUntil hxa (by omega)).symm
    _ = (pb.takeUntil x hxb).getVert j := congrArg (fun q ↦ q.getVert j) hprefix
    _ = pb.getVert j := pb.getVert_takeUntil hxb (by omega)

/-- Once two canonical root paths choose different children immediately
after a common depth `j`, their suffixes from the common vertex are disjoint
apart from that common initial vertex.  The `tail` on the second support
removes precisely this permitted intersection. -/
lemma bfsParentWalk_dropUntil_disjoint_tail (G : SimpleGraph V)
    (hconn : G.Connected) (root a b z : V) (j : ℕ)
    (hja : j < (bfsParentWalk G hconn root a).length)
    (hjb : j < (bfsParentWalk G hconn root b).length)
    (hza : (bfsParentWalk G hconn root a).getVert j = z)
    (hzb : (bfsParentWalk G hconn root b).getVert j = z)
    (hsplit : (bfsParentWalk G hconn root a).getVert (j + 1) ≠
      (bfsParentWalk G hconn root b).getVert (j + 1)) :
    List.Disjoint
      ((bfsParentWalk G hconn root a).dropUntil z
        (hza ▸ (bfsParentWalk G hconn root a).getVert_mem_support j)).support
      ((bfsParentWalk G hconn root b).dropUntil z
        (hzb ▸ (bfsParentWalk G hconn root b).getVert_mem_support j)).support.tail := by
  let pa := bfsParentWalk G hconn root a
  let pb := bfsParentWalk G hconn root b
  let hza' : z ∈ pa.support := hza ▸ pa.getVert_mem_support j
  let hzb' : z ∈ pb.support := hzb ▸ pb.getVert_mem_support j
  let qa := pa.dropUntil z hza'
  let qb := pb.dropUntil z hzb'
  intro x hxa hxb
  have hxb_qb : x ∈ qb.support := List.mem_of_mem_tail hxb
  have hqb_path : qb.IsPath :=
    (bfsParentWalk_isPath G hconn root b).dropUntil hzb'
  have hz_not_tail : z ∉ qb.support.tail := by
    have hn := hqb_path.support_nodup
    rw [← qb.cons_tail_support] at hn
    exact hn.notMem
  have hxz : x ≠ z := fun hxz ↦ by
    subst x
    exact hz_not_tail hxb
  have hxa_pa : x ∈ pa.support := pa.support_dropUntil_subset_support hza' hxa
  have hxb_pb : x ∈ pb.support := pb.support_dropUntil_subset_support hzb' hxb_qb
  obtain ⟨ka, hka_x, hka⟩ := Walk.mem_support_iff_exists_getVert.mp hxa_pa
  obtain ⟨kb, hkb_x, hkb⟩ := Walk.mem_support_iff_exists_getVert.mp hxb_pb
  have hdist_ka := bfsParentWalk_dist_getVert G hconn root a ka hka
  have hdist_kb := bfsParentWalk_dist_getVert G hconn root b kb hkb
  rw [hka_x] at hdist_ka
  rw [hkb_x] at hdist_kb
  have hkab : ka = kb := by omega
  have hkb' : ka ≤ pb.length := by omega
  have hjka : j < ka := by
    have hlt := Erdos594.length_takeUntil_lt_of_mem_dropUntil
      pa (bfsParentWalk_isPath G hconn root a) hza' hxa hxz
    have htz : (pa.takeUntil z hza').length = G.dist root z :=
      length_eq_dist_of_subwalk (bfsParentWalk_length G hconn root a)
        (pa.isSubwalk_takeUntil hza')
    have htx : (pa.takeUntil x hxa_pa).length = G.dist root x :=
      length_eq_dist_of_subwalk (bfsParentWalk_length G hconn root a)
        (pa.isSubwalk_takeUntil hxa_pa)
    have hdist_z := bfsParentWalk_dist_getVert G hconn root a j hja.le
    rw [hza] at hdist_z
    omega
  apply hsplit
  exact bfsParentWalk_getVert_eq_of_eq_at G hconn root a b
    (by omega) hka hkb' (hka_x.trans (by simpa only [hkab] using hkb_x.symm))

/-- Two vertices in one BFS layer whose canonical root paths first branch
immediately after depth `j` are joined by a simple path of the fixed length
`2 * (i - j)`.  Every internal vertex of this detour lies strictly below
layer `i`. -/
theorem exists_bfsParent_detour_of_split (G : SimpleGraph V)
    (hconn : G.Connected) (root a b z : V) (i j : ℕ)
    (hda : G.dist root a = i) (hdb : G.dist root b = i)
    (hji : j < i)
    (hza : (bfsParentWalk G hconn root a).getVert j = z)
    (hzb : (bfsParentWalk G hconn root b).getVert j = z)
    (hsplit : (bfsParentWalk G hconn root a).getVert (j + 1) ≠
      (bfsParentWalk G hconn root b).getVert (j + 1)) :
    ∃ q : G.Walk a b,
      q.IsPath ∧ q.length = 2 * (i - j) ∧
        ∀ x ∈ q.support, x ≠ a → x ≠ b → G.dist root x < i := by
  let pa := bfsParentWalk G hconn root a
  let pb := bfsParentWalk G hconn root b
  have hja : j < pa.length := by
    rw [bfsParentWalk_length G hconn root a, hda]
    exact hji
  have hjb : j < pb.length := by
    rw [bfsParentWalk_length G hconn root b, hdb]
    exact hji
  let hza' : z ∈ pa.support := hza ▸ pa.getVert_mem_support j
  let hzb' : z ∈ pb.support := hzb ▸ pb.getVert_mem_support j
  let qa := pa.dropUntil z hza'
  let qb := pb.dropUntil z hzb'
  let q : G.Walk a b := qa.reverse.append qb
  have hqa_path : qa.IsPath :=
    (bfsParentWalk_isPath G hconn root a).dropUntil hza'
  have hqb_path : qb.IsPath :=
    (bfsParentWalk_isPath G hconn root b).dropUntil hzb'
  have hdisj : qa.support.Disjoint qb.support.tail := by
    exact bfsParentWalk_dropUntil_disjoint_tail G hconn root a b z j
      hja hjb hza hzb hsplit
  have hq_path : q.IsPath := by
    change (qa.reverse.append qb).IsPath
    rw [Walk.isPath_def, Walk.support_append, List.nodup_append']
    exact ⟨hqa_path.reverse.support_nodup, hqb_path.support_nodup.tail,
      by simpa [Walk.support_reverse] using hdisj⟩
  have hdist_z : G.dist root z = j := by
    have hz := bfsParentWalk_dist_getVert G hconn root a j hja.le
    rw [hza] at hz
    exact hz
  have htake_a : (pa.takeUntil z hza').length = j := by
    rw [length_eq_dist_of_subwalk (bfsParentWalk_length G hconn root a)
      (pa.isSubwalk_takeUntil hza'), hdist_z]
  have htake_b : (pb.takeUntil z hzb').length = j := by
    rw [length_eq_dist_of_subwalk (bfsParentWalk_length G hconn root b)
      (pb.isSubwalk_takeUntil hzb'), hdist_z]
  have hqa_len : qa.length = i - j := by
    have hsplit_a := congrArg Walk.length (pa.take_spec hza')
    simp only [Walk.length_append] at hsplit_a
    rw [bfsParentWalk_length G hconn root a, hda, htake_a] at hsplit_a
    change (pa.dropUntil z hza').length = i - j
    omega
  have hqb_len : qb.length = i - j := by
    have hsplit_b := congrArg Walk.length (pb.take_spec hzb')
    simp only [Walk.length_append] at hsplit_b
    rw [bfsParentWalk_length G hconn root b, hdb, htake_b] at hsplit_b
    change (pb.dropUntil z hzb').length = i - j
    omega
  refine ⟨q, hq_path, ?_, ?_⟩
  · simp only [q, Walk.length_append, Walk.length_reverse, hqa_len, hqb_len]
    omega
  · intro x hx hxa hxb
    change x ∈ (qa.reverse.append qb).support at hx
    rw [Walk.mem_support_append_iff] at hx
    rcases hx with hxqa | hxqb
    · have hxqa' : x ∈ qa.support := by
        simpa [Walk.support_reverse] using hxqa
      have hxpa : x ∈ pa.support :=
        pa.support_dropUntil_subset_support hza' hxqa'
      simpa [hda] using
        bfsParentWalk_internal_dist_lt G hconn root a x hxpa hxa
    · have hxpb : x ∈ pb.support :=
        pb.support_dropUntil_subset_support hzb' hxqb
      simpa [hdb] using
        bfsParentWalk_internal_dist_lt G hconn root b x hxpb hxb

end

end Erdos752
