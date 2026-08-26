import ErdosProblems.Erdos118.CutSuccessors

/-!
Ordinary-coordinate frontiers determine the minimal longer threshold cut.
This does not yet schedule the decorated pair responses.
-/

namespace Erdos118.CutFrontiers

open Negative Negative.Exact LabelledExtensions LabelledFrames LabelCoarsening
open PrefixRealization (below)

theorem joint_cut_length {P : Pending} {S : Stem} {hS : S.done.length = S.root} {x : ℕ}
    (hP : JointCut P S hS x) : P.position.ordinary.length < S.ordinary.length := by
  have he := cutExtension_of_prefix P S hS hP.labels (by
    rw [hP.decorated]; exact List.takeWhile_prefix _)
  obtain ⟨a, as, hdone, _, hsize, v, hv⟩ := he.bodies
  have hlen : (P.position.entries ++ v).length = P.position.size :=
    (congrArg List.length hv).trans hsize
  have hvpos : 0 < v.length := by
    have hp := P.position.unfinished
    simp only [List.length_append] at hlen
    omega
  have hword : S.ordinary = P.position.ordinary ++ (v ++ as.flatMap Body.ordinary) := by
    simp only [Position.ordinary, Stem.ordinary, he.root, hdone, List.flatMap_append,
      List.flatMap_cons, Body.ordinary, levelWord, ← hv, hlen,
      List.cons_append, List.append_assoc]
  rw [hword, List.length_append, List.length_append]
  omega

theorem joint_cut_proper {P : Pending} {S : Stem} {hS : S.done.length = S.root} {x : ℕ}
    (hP : JointCut P S hS x) : ProperBelow x S := by
  refine ⟨?_, ?_⟩
  · rw [← hP.ordinary]
    simp [Position.ordinary, Stem.ordinary]
  · intro he
    have hlen := joint_cut_length hP
    rw [hP.ordinary, he] at hlen
    omega

theorem next_threshold (X Y p q u v : List ℕ) (z w : ℕ)
    (hX : X.Pairwise (· < ·)) (hY : Y.Pairwise (· < ·))
    (hxs : X = p ++ z :: u) (hys : Y = q ++ w :: v)
    (hq : below z Y = q) (hne : z ≠ w) :
    z < w ∧ p.length < (below w X).length ∧
      ∀ y ∈ Y, p.length < (below y X).length → below w X <+: below y X := by
  have hsplitY := below_split_bounds z q (w :: v) (hys ▸ hY) (by rw [← hys]; exact hq)
  have hzw : z < w := Nat.lt_of_le_of_ne (hsplitY.2 w (List.mem_cons_self ..)) hne
  have hbefore : ∀ a ∈ p, a < z :=
    fun a ha ↦ (List.pairwise_append.mp (hxs ▸ hX)).2.2 a ha z (List.mem_cons_self ..)
  have hpz : below z X = p := by
    rw [hxs]
    simp only [below, List.takeWhile_append_of_pos (fun a ha ↦ decide_eq_true (hbefore a ha)),
      List.takeWhile_cons, Nat.lt_irrefl, decide_false, Bool.false_eq_true,
      ↓reduceIte, List.append_nil]
  have hpw : below w X = p ++ z :: below w u := by
    rw [hxs]
    simp only [below, List.takeWhile_append_of_pos
      (fun a ha ↦ decide_eq_true ((hbefore a ha).trans hzw)), List.takeWhile_cons,
      decide_eq_true hzw, ↓reduceIte]
  refine ⟨hzw, ?_, ?_⟩
  · rw [hpw, List.length_append, List.length_cons]
    omega
  · intro y hy hlong
    rw [hys] at hy
    rcases List.mem_append.mp hy with hy | hy
    · have hyz := hsplitY.1 y hy
      have hp := CutOrder.below_prefix hyz.le X
      rw [hpz] at hp
      have hlen := hp.length_le
      omega
    · have htail := (List.pairwise_append.mp (hys ▸ hY)).2.1
      have hwy : w ≤ y := by
        simpa only [List.head_cons] using (htail.imp Nat.le_of_lt).rel_head hy
      exact CutOrder.below_prefix hwy X

theorem successor_eq_frontier (S T : Stem) (hS : S.done.length = S.root)
    (hinterior : CutIndices.InteriorCuts S T) (P Q : Pending) {y : ℕ}
    (hy : y ∈ T.ordinary) (hQ : JointCut Q S hS y)
    (hlong : P.position.ordinary.length < Q.position.ordinary.length)
    (hnext : ∀ R : InteriorWords.Position, R.word <+: S.ordinary →
      CutIndices.Cut S T R.done.length R.entries.length →
      P.position.ordinary.length < R.word.length → Q.position.ordinary <+: R.word)
    (q u v : List ℕ) (z w : ℕ)
    (hxs : S.ordinary = P.position.ordinary ++ z :: u)
    (hys : T.ordinary = q ++ w :: v) (hq : below z T.ordinary = q) (hne : z ≠ w) :
    Q.position.ordinary = below w S.ordinary := by
  have hf := next_threshold S.ordinary T.ordinary P.position.ordinary q u v z w
    (S.increasing.sublist S.ordinary_sublist) (T.increasing.sublist T.ordinary_sublist)
    hxs hys hq hne
  have hrQ : below w S.ordinary <+: Q.position.ordinary := by
    rw [hQ.ordinary]
    apply hf.2.2 y hy
    rw [← hQ.ordinary]
    exact hlong
  have hrproper : ProperBelow w S := by
    refine ⟨?_, ?_⟩
    · intro he
      have hl := hf.2.1
      simp only [he, List.length_nil] at hl
      omega
    · intro he
      have hl := hrQ.length_le
      rw [he] at hl
      have hshort := joint_cut_length hQ
      omega
  have hw : w ∈ T.ordinary := by
    rw [hys]
    exact List.mem_append_right _ (List.mem_cons_self ..)
  obtain ⟨R, hR⟩ := hinterior w hw hrproper
  have hRprefix : R.word <+: S.ordinary := by
    rw [hR]
    exact List.takeWhile_prefix _
  have hc : CutIndices.Cut S T R.done.length R.entries.length :=
    ⟨w, hw, hrproper, R, hR, rfl, rfl⟩
  have hQR := hnext R hRprefix hc (by rw [hR]; exact hf.2.1)
  rw [hR] at hQR
  exact hQR.eq_of_length (le_antisymm hQR.length_le hrQ.length_le)

end Erdos118.CutFrontiers
