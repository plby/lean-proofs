import ErdosProblems.Erdos118.Reused591.MacroDescendants

namespace Erdos118.Reused591

/-!
# Root ownership and disjoint numerical supports

An indexed macro block belongs to exactly one root branch. Ancestry is
computed from the fixed pairing schedule; no fresh input is attributed
to two different roots. Combined with chronological strict increase,
this gives disjoint supports, including all label values.
-/

namespace Erdos591.Positive.Game.Macro.Forest

def root : ℕ → ℕ
  | 0 => 0
  | n + 1 => if (Nat.unpair n).1 = 0 then n + 1 else root (Nat.unpair n).1
termination_by n => n
decreasing_by
  have h := Nat.unpair_left_le n
  omega

theorem root_child (p j : ℕ) : root (child p j) = if p = 0 then child p j else root p := by
  simp [child, root]

theorem Descendant.le {p n : ℕ} (h : Descendant p n) : p ≤ n := by
  induction h with
  | refl => exact le_rfl
  | @tail n m _ hm ih =>
      obtain ⟨j, rfl⟩ := hm
      exact ih.trans (parent_lt_child n j).le

theorem Descendant.root_eq {p n : ℕ} (h : Descendant p n) (hp : 0 < p) : root n = root p := by
  induction h with
  | refl => rfl
  | @tail n m hn hm ih =>
      obtain ⟨j, rfl⟩ := hm
      have hn0 : n ≠ 0 := Nat.ne_of_gt (hp.trans_le (Descendant.le hn))
      simpa [root_child, hn0] using ih

theorem raw_segments (xs : List Segment) :
    raw (xs.flatMap Prod.snd) = xs.flatMap (fun s => raw s.2) := by
  induction xs with
  | nil => rfl
  | cons s xs ih => simp [ih]

variable {N H : Set ℕ} (hH : H.Infinite) (b : Concrete.Hist N → ℕ)

theorem log_segment_block (n : ℕ) (s : Segment) (hs : s ∈ (stages hH b n).log) :
    s.2 = (chunkAt hH b s.1).block := by
  induction n with
  | zero => simp [stages, Stage.initial] at hs
  | succ n ih =>
      rw [stages_succ] at hs
      change s ∈ (stages hH b n).log ++
        [((stages hH b n).log.length, (chunkAt hH b n).block)] at hs
      rcases List.mem_append.mp hs with hs | hs
      · exact ih hs
      · have heq : s = (n, (chunkAt hH b n).block) := by simpa using hs
        subst s
        rfl

theorem node_segment_block (n : ℕ) (s : Segment) (hs : s ∈ (node hH b n).segments) :
    s.2 = (chunkAt hH b s.1).block :=
  log_segment_block hH b n s ((node_segments_sublist hH b n n le_rfl).subset hs)

/-- Every block in a stored ancestry has the same root as that node. -/
theorem segment_root (n : ℕ) (s : Segment) (hs : s ∈ (node hH b n).segments) :
    root (s.1 + 1) = root n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => simp [Node.initial] at hs
      | succ n =>
          rw [node_succ_segments] at hs
          rcases List.mem_append.mp hs with hs | hs
          · by_cases hp : (Nat.unpair n).1 = 0
            · simp [hp, Node.initial] at hs
            · have hlt : (Nat.unpair n).1 < n + 1 :=
                Nat.lt_succ_of_le (Nat.unpair_left_le n)
              conv_rhs => rw [root, if_neg hp]
              exact ih _ hlt hs
          · have heq : s = (n, (chunkAt hH b n).block) := by simpa using hs
            simp [heq]

theorem node_inputs_disjoint (n m : ℕ) (hnm : root n ≠ root m) :
    Disjoint (raw (node hH b n).atoms).toFinset (raw (node hH b m).atoms).toFinset := by
  apply Finset.disjoint_left.mpr
  intro x hxn hxm
  have hxn' := List.mem_toFinset.mp hxn
  have hxm' := List.mem_toFinset.mp hxm
  rw [Node.atoms, raw_segments, List.mem_flatMap] at hxn' hxm'
  obtain ⟨s, hs, hxs⟩ := hxn'
  obtain ⟨t, ht, hxt⟩ := hxm'
  have hne : s.1 ≠ t.1 := by
    intro heq
    apply hnm
    exact (segment_root hH b n s hs).symm.trans
      ((congrArg (fun i => root (i + 1)) heq).trans (segment_root hH b m t ht))
  rw [node_segment_block hH b n s hs] at hxs
  rw [node_segment_block hH b m t ht] at hxt
  rcases lt_or_gt_of_ne hne with hst | hts
  · exact Nat.lt_irrefl x (chunks_separated hH b _ _ hst x hxs x hxt)
  · exact Nat.lt_irrefl x (chunks_separated hH b _ _ hts x hxt x hxs)

theorem node_support_disjoint (n m : ℕ) (hnm : root n ≠ root m) :
    Disjoint (node hH b n).cursor.support (node hH b m).cursor.support :=
  (node_inputs_disjoint hH b n m hnm).mono (node hH b n).support (node hH b m).support

theorem different_root_supports {i j n m : ℕ} (hij : i ≠ j)
    (hn : Descendant (child 0 i) n) (hm : Descendant (child 0 j) m) :
    Disjoint (node hH b n).cursor.support (node hH b m).cursor.support := by
  apply node_support_disjoint hH b n m
  rw [hn.root_eq (parent_lt_child 0 i), hm.root_eq (parent_lt_child 0 j)]
  simp only [root_child]
  exact (child_strictMono 0).injective.ne hij

#print axioms segment_root
#print axioms node_inputs_disjoint
#print axioms different_root_supports

end Erdos591.Positive.Game.Macro.Forest

end Erdos118.Reused591
