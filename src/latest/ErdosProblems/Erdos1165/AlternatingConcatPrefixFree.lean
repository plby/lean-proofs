/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos1165.MarkedBridgeFactorization
import ErdosProblems.Erdos1165.TerminalSkeletonWords

/-!
# Unique parsing of alternating prefix-free words

This file contains the combinatorial part of terminal-skeleton insertion.
Fixed retained lists alternate with variable-length words from prefix-free
stopped-word codes.  Such an alternating concatenation parses uniquely from
left to right.
-/

open Set

namespace Erdos1165.AlternatingConcatPrefixFree

open MarkedBridgeFactorization TerminalSkeletonWords

noncomputable section

/-- A list viewed as a variable-length stopped word. -/
def listStoppedWord (v : List Direction) : StoppedWord :=
  ⟨v.length, fun j ↦ v.get j⟩

@[simp] theorem listStoppedWord_length (v : List Direction) :
    (listStoppedWord v).1 = v.length := rfl

@[simp] theorem listStoppedWord_toList (v : List Direction) :
    List.ofFn (listStoppedWord v).2 = v := by
  exact List.ofFn_get v

@[simp] theorem listStoppedWord_ofFn (w : StoppedWord) :
    listStoppedWord (List.ofFn w.2) = w := by
  apply Sigma.ext (by simp)
  apply (Fin.heq_fun_iff (by simp)).2
  intro i
  simp [listStoppedWord]

/-- Extending a longer list produces a path in the stopped cylinder of each
of its list prefixes. -/
lemma extend_list_mem_stoppedWordCylinder_of_isPrefix
    {u v : List Direction} (huv : u <+: v) :
    extendStoppedWord (listStoppedWord v) ∈
      stoppedWordCylinder (listStoppedWord u) := by
  change stepPrefix u.length
      (extendStoppedWord ⟨v.length, fun j ↦ v.get j⟩) =
    (fun j ↦ u.get j)
  funext i
  have hi : (i : ℕ) < v.length := i.isLt.trans_le huv.length_le
  change extendStoppedWord ⟨v.length, fun j ↦ v.get j⟩ i = u.get i
  unfold extendStoppedWord
  rw [dif_pos hi]
  change v.get ⟨i, hi⟩ = u.get i
  simpa only [List.get_eq_getElem] using (huv.getElem i.isLt).symm

/-- Two members of a prefix-free stopped-word family cannot both occur as
prefixes of one finite list. -/
lemma eq_of_prefixes_of_prefixFree
    {Code : Type*} (word : Code → List Direction)
    (hfree : PrefixFree (fun c ↦ listStoppedWord (word c)))
    {c d : Code} {tailC tailD : List Direction}
    (hconcat : word c ++ tailC = word d ++ tailD) : c = d := by
  by_contra hne
  have hdisj := hfree hne
  change Disjoint (stoppedWordCylinder (listStoppedWord (word c)))
    (stoppedWordCylinder (listStoppedWord (word d))) at hdisj
  rw [Set.disjoint_left] at hdisj
  let omega := extendStoppedWord (listStoppedWord (word c ++ tailC))
  have hc : omega ∈ stoppedWordCylinder (listStoppedWord (word c)) := by
    exact extend_list_mem_stoppedWordCylinder_of_isPrefix
      (by exact List.prefix_append _ _)
  have hd : omega ∈ stoppedWordCylinder (listStoppedWord (word d)) := by
    apply extend_list_mem_stoppedWordCylinder_of_isPrefix
    rw [hconcat]
    exact List.prefix_append _ _
  exact hdisj hc hd

/-- With the retained pieces fixed, an alternating concatenation of
prefix-free variable-length code words has a unique bridge tuple. -/
theorem alternatingConcat_injective_of_prefixFree : ∀ (m : ℕ)
    (pieces : Fin (m + 1) → List Direction)
    (Bridge : Fin m → Type*)
    (word : (j : Fin m) → Bridge j → List Direction),
    (∀ j, PrefixFree (fun b ↦ listStoppedWord (word j b))) →
      Function.Injective
        (fun b : (j : Fin m) → Bridge j ↦
          alternatingConcat m pieces (fun j ↦ word j (b j))) := by
  intro m
  induction m with
  | zero =>
      intro pieces Bridge word hfree b b' _h
      funext j
      exact Fin.elim0 j
  | succ m ih =>
      intro pieces Bridge word hfree b b' hwords
      simp only [alternatingConcat] at hwords
      have htailWords :
          word 0 (b 0) ++
              alternatingConcat m (fun j ↦ pieces j.succ)
                (fun j ↦ word j.succ (b j.succ)) =
            word 0 (b' 0) ++
              alternatingConcat m (fun j ↦ pieces j.succ)
                (fun j ↦ word j.succ (b' j.succ)) := by
        rw [List.append_assoc, List.append_assoc] at hwords
        exact List.append_cancel_left hwords
      have hzero : b 0 = b' 0 :=
        eq_of_prefixes_of_prefixFree (word 0) (hfree 0) htailWords
      have hrest :
          alternatingConcat m (fun j ↦ pieces j.succ)
              (fun j ↦ word j.succ (b j.succ)) =
            alternatingConcat m (fun j ↦ pieces j.succ)
              (fun j ↦ word j.succ (b' j.succ)) := by
        rw [hzero] at htailWords
        exact List.append_cancel_left htailWords
      have hsucc : (fun j : Fin m ↦ b j.succ) =
          (fun j : Fin m ↦ b' j.succ) := by
        exact ih (fun j ↦ pieces j.succ) (fun j ↦ Bridge j.succ)
          (fun j ↦ word j.succ) (fun j ↦ hfree j.succ) hrest
      funext j
      refine Fin.cases hzero (fun k ↦ ?_) j
      exact congrFun hsucc k

end

end Erdos1165.AlternatingConcatPrefixFree
