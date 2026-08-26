import ErdosProblems.Erdos118.NextBodyCuts

/-!
The literal local decoders take the next intrinsic cut. Their successor
property is proved from exact annotations, not imposed on the decoder.
The global chronological pair scheduler remains a separate construction.
-/

namespace Erdos118.CutSuccessors

open Negative Negative.Exact LabelledExtensions LabelledFrames LabelCoarsening
open CutIndices DecisionStates

theorem prefix_of_indices {P Q : InteriorWords.Position} {w : List ℕ}
    (hP : P.word <+: w) (hQ : Q.word <+: w)
    (hindices : P.done.length < Q.done.length ∨
      P.done.length = Q.done.length ∧ P.entries.length ≤ Q.entries.length) : P.word <+: Q.word := by
  rcases List.prefix_or_prefix_of_prefix hP hQ with hpq | hqp
  · exact hpq
  · have hc := CutOrder.interior_prefix_counts hqp
    rcases hindices with hi | ⟨hi, hj⟩
    · omega
    · have hj' := (hc.2 hi.symm).2.2.length_le
      have he := SkippedCuts.interior_prefix_same_indices hqp hi.symm (le_antisymm hj' hj)
      rw [he]

theorem indices_of_length {P Q : InteriorWords.Position} {w : List ℕ}
    (hP : P.word <+: w) (hQ : Q.word <+: w) (hlen : P.word.length < Q.word.length) :
    P.done.length < Q.done.length ∨
      P.done.length = Q.done.length ∧ P.entries.length < Q.entries.length := by
  have hpq := List.prefix_of_prefix_length_le hP hQ hlen.le
  have hc := CutOrder.interior_prefix_counts hpq
  by_cases hi : P.done.length < Q.done.length
  · exact Or.inl hi
  · have he : P.done.length = Q.done.length := by omega
    have hj := (hc.2 he).2.2.length_le
    refine Or.inr ⟨he, ?_⟩
    by_contra hnot
    have heq : P.entries.length = Q.entries.length := by omega
    have hePQ := SkippedCuts.interior_prefix_same_indices hpq he heq
    subst Q
    omega

private theorem cut_prefix {P : Pending} {S : Stem} {hS : S.done.length = S.root}
    {x : ℕ} (hP : JointCut P S hS x) : P.position.toInterior.word <+: S.ordinary := by
  rw [Position.toInterior_word, hP.ordinary]
  exact List.takeWhile_prefix _

private theorem current_label_mem {S T : Stem} {hS : S.done.length = S.root}
    (hexact : ExactAnnotations S T) {P : Pending} {x : ℕ} (hP : JointCut P S hS x)
    {j : ℕ} (hc : Cut S T P.position.stem.done.length j) : j ∈ P.position.label := by
  have hlabels : P.position.bodyLabels <+: S.bodyLabels := hP.labels.bodies
  have hiP : P.position.stem.done.length < P.position.bodyLabels.length := by
    simp [Position.bodyLabels, Stem.bodyLabels]
  have hiS := hiP.trans_le hlabels.length_le
  have hm := (hexact.body P.position.stem.done.length hiS j).mpr hc
  rw [← hlabels.getElem hiP] at hm
  simpa [Position.bodyLabels, Stem.bodyLabels] using hm

theorem empty_roots_bound (S T : Stem) (hS : S.done.length = S.root)
    (hexact : ExactAnnotations S T) (P : Pending) {x : ℕ} (hP : JointCut P S hS x)
    (hslots : ExactSlots.Exact (.leaf P)) (hR : P.roots = [])
    (i j : ℕ) (hc : Cut S T i j) : i ≤ P.position.stem.done.length := by
  by_contra hn
  have hi : P.position.stem.done.length < i := by omega
  have hmS : i + 1 ∈ S.rootLabel := (hexact.root (i + 1)).mpr ⟨i, j, hc, rfl⟩
  have hroot : S.rootLabel = P.position.stem.rootLabel :=
    Option.some.inj (hP.labels.root _ rfl)
  have hm : i + 1 ∈ ExactSlots.above P.position.stem.rootLabel
      (P.position.stem.done.length + 1) :=
    List.mem_filter.mpr ⟨hroot ▸ hmS, decide_eq_true (Nat.add_lt_add_right hi 1)⟩
  rw [← hslots.1, hR] at hm
  exact List.not_mem_nil hm

theorem empty_leaves_bound (S T : Stem) (hS : S.done.length = S.root)
    (hexact : ExactAnnotations S T) (P : Pending) {x : ℕ} (hP : JointCut P S hS x)
    (hslots : ExactSlots.Exact (.leaf P)) (hL : P.leaves = [])
    (j : ℕ) (hc : Cut S T P.position.stem.done.length j) : j ≤ P.position.entries.length := by
  by_contra hn
  have hj : P.position.entries.length < j := by omega
  have hm : j ∈ ExactSlots.above P.position.label P.position.entries.length :=
    List.mem_filter.mpr ⟨current_label_mem hexact hP hc, decide_eq_true hj⟩
  rw [← hslots.2, hL] at hm
  exact List.not_mem_nil hm

theorem leaf_successor (S T : Stem) (hS : S.done.length = S.root)
    (hexact : ExactAnnotations S T) (P Q : Pending) {x y : ℕ}
    (hP : JointCut P S hS x) (hQ : JointCut Q S hS y)
    (hslots : ExactSlots.Exact (.leaf P)) (j : ℕ) (rest : List ℕ)
    (hnext : P.leaves = j :: rest)
    (hiQ : Q.position.stem.done.length = P.position.stem.done.length)
    (hjQ : Q.position.entries.length = j)
    (R : InteriorWords.Position) (hR : R.word <+: S.ordinary)
    (hc : Cut S T R.done.length R.entries.length)
    (hlong : P.position.ordinary.length < R.word.length) : Q.position.ordinary <+: R.word := by
  have hord := indices_of_length (cut_prefix hP) hR (by
    simpa only [Position.toInterior_word] using hlong)
  have hindices : P.position.stem.done.length < R.done.length ∨
      P.position.stem.done.length = R.done.length ∧
        P.position.entries.length < R.entries.length := by
    simpa only [Position.toInterior, List.length_map] using hord
  have hnextIndices : Q.position.toInterior.done.length < R.done.length ∨
      Q.position.toInterior.done.length = R.done.length ∧
        Q.position.toInterior.entries.length ≤ R.entries.length := by
    simp only [Position.toInterior, List.length_map]
    rcases hindices with hi | ⟨hi, hj⟩
    · exact Or.inl (hiQ.trans_lt hi)
    · have hcut : Cut S T P.position.stem.done.length R.entries.length := hi ▸ hc
      have hmin := NextLeafCuts.next_leaf_minimal S T hS hexact P hP hslots j rest hnext
        R.entries.length hcut hj
      exact Or.inr ⟨hiQ.trans hi, hjQ.trans_le hmin⟩
  simpa only [Position.toInterior_word] using
    prefix_of_indices (cut_prefix hQ) hR hnextIndices

private theorem head_le_of_mem (C : List ℕ) (hC : C.Pairwise (· < ·)) (j : ℕ)
    (hj : j ∈ C) : C.headD 0 ≤ j := by
  cases C with
  | nil => simp at hj
  | cons c C => simpa only [List.headD_cons, List.head_cons] using (hC.imp Nat.le_of_lt).rel_head hj

theorem body_successor (S T : Stem) (hS : S.done.length = S.root)
    (hexact : ExactAnnotations S T) (P Q : Pending) {x y : ℕ}
    (hP : JointCut P S hS x) (hQ : JointCut Q S hS y)
    (hslots : ExactSlots.Exact (.leaf P)) (c : ℕ) (rest : List ℕ)
    (hnext : P.roots = c :: rest) (hleaves : P.leaves = [])
    (hiQ : Q.position.stem.done.length = c - 1)
    (hhead : Q.position.entries.length = Q.position.label.headD 0)
    (R : InteriorWords.Position) (hR : R.word <+: S.ordinary)
    (hc : Cut S T R.done.length R.entries.length)
    (hlong : P.position.ordinary.length < R.word.length) : Q.position.ordinary <+: R.word := by
  have hord := indices_of_length (cut_prefix hP) hR (by
    simpa only [Position.toInterior_word] using hlong)
  have hindices : P.position.stem.done.length < R.done.length ∨
      P.position.stem.done.length = R.done.length ∧
        P.position.entries.length < R.entries.length := by
    simpa only [Position.toInterior, List.length_map] using hord
  have hi : P.position.stem.done.length < R.done.length := by
    rcases hindices with hi | ⟨hi, hj⟩
    · exact hi
    · have hc' : Cut S T P.position.stem.done.length R.entries.length := hi ▸ hc
      have hbound := empty_leaves_bound S T hS hexact P hP hslots hleaves R.entries.length hc'
      omega
  have hmin := NextBodyCuts.next_root_minimal S T hS hexact P hP hslots c rest hnext
    R.done.length R.entries.length hc hi
  have hiQR : Q.position.stem.done.length ≤ R.done.length := by omega
  have hnextIndices : Q.position.toInterior.done.length < R.done.length ∨
      Q.position.toInterior.done.length = R.done.length ∧
        Q.position.toInterior.entries.length ≤ R.entries.length := by
    simp only [Position.toInterior, List.length_map]
    by_cases hlt : Q.position.stem.done.length < R.done.length
    · exact Or.inl hlt
    · have he : Q.position.stem.done.length = R.done.length := by omega
      have hc' : Cut S T Q.position.stem.done.length R.entries.length := he ▸ hc
      have hm := current_label_mem hexact hQ hc'
      exact Or.inr ⟨he, hhead.trans_le
        (head_le_of_mem _ Q.position.label_pairwise R.entries.length hm)⟩
  simpa only [Position.toInterior_word] using
    prefix_of_indices (cut_prefix hQ) hR hnextIndices

theorem last_no_successor (S T : Stem) (hS : S.done.length = S.root)
    (hexact : ExactAnnotations S T) (P : Pending) {x : ℕ} (hP : JointCut P S hS x)
    (hslots : ExactSlots.Exact (.leaf P)) (hroots : P.roots = []) (hleaves : P.leaves = [])
    (R : InteriorWords.Position) (hR : R.word <+: S.ordinary)
    (hc : Cut S T R.done.length R.entries.length) : R.word.length ≤ P.position.ordinary.length := by
  by_contra hn
  have hlong : P.position.toInterior.word.length < R.word.length := by
    simpa only [Position.toInterior_word] using Nat.lt_of_not_ge hn
  have hord := indices_of_length (cut_prefix hP) hR hlong
  have hindices : P.position.stem.done.length < R.done.length ∨
      P.position.stem.done.length = R.done.length ∧
        P.position.entries.length < R.entries.length := by
    simpa only [Position.toInterior, List.length_map] using hord
  rcases hindices with hi | ⟨hi, hj⟩
  · have hbound := empty_roots_bound S T hS hexact P hP hslots hroots
      R.done.length R.entries.length hc
    omega
  · have hc' : Cut S T P.position.stem.done.length R.entries.length := hi ▸ hc
    have hbound := empty_leaves_bound S T hS hexact P hP hslots hleaves R.entries.length hc'
    omega

end Erdos118.CutSuccessors
