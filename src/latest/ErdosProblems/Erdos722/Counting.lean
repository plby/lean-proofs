/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import ErdosProblems.Erdos722.Typicality
import Mathlib

/-!
# Sparse-edge extension counting

The central estimate in both regularity boosting and the reserve cover is
that an `r`-graph of maximum `(r-1)`-degree `D` can spoil only
`O(D * n^(q-r-1))` many `q`-extensions of a fixed `r`-edge.  We prove the
finite counting statement by ordering the `q-r` new vertices and recording
one coordinate of a forbidden edge outside the root.
-/

namespace Erdos722.Counting

open Finset

noncomputable section

/-- Maximum `(r-1)`-degree at most `D`, stated without requiring a separate
uniformity proof for the host. -/
def LowerDegreeLE (n r D : ℕ) (F : Finset (Finset (Fin n))) : Prop :=
  ∀ I : Finset (Fin n), I.card = r - 1 →
    (F.filter fun f ↦ I ⊆ f).card ≤ D

/-- All coordinates other than one distinguished coordinate. -/
abbrev OtherIndex (m : ℕ) (j : Fin m) := {i : Fin m // i ≠ j}

lemma card_otherIndex {m : ℕ} (j : Fin m) :
    Fintype.card (OtherIndex m j) = m - 1 := by
  rw [Fintype.card_subtype_compl]
  simp

/-- The root together with all values of a tuple on the nondistinguished
coordinates. -/
def restSupport {n m : ℕ} (e : Finset (Fin n)) (j : Fin m)
    (x : OtherIndex m j → Fin n) : Finset (Fin n) :=
  e ∪ Finset.univ.image x

lemma card_restSupport_le {n q r m : ℕ} (hqr : r < q)
    (hm : m = q - r) {e : Finset (Fin n)} (he : e.card = r)
    (j : Fin m) (x : OtherIndex m j → Fin n) :
    (restSupport e j x).card ≤ q := by
  calc
    (restSupport e j x).card ≤ e.card + (Finset.univ.image x).card :=
      Finset.card_union_le _ _
    _ ≤ e.card + Finset.univ.card :=
      Nat.add_le_add_left Finset.card_image_le _
    _ = r + (m - 1) := by simp [he, card_otherIndex]
    _ ≤ q := by omega

/-- Candidate lower faces supported on the root and the nondistinguished
tuple entries. -/
abbrev LowerFace {n m r : ℕ} (e : Finset (Fin n)) (j : Fin m)
    (x : OtherIndex m j → Fin n) :=
  {I : Finset (Fin n) // I ⊆ restSupport e j x ∧ I.card = r - 1}

lemma card_lowerFace_le {n q r m : ℕ} (hqr : r < q)
    (hm : m = q - r) {e : Finset (Fin n)} (he : e.card = r)
    (j : Fin m) (x : OtherIndex m j → Fin n) :
    Fintype.card (LowerFace (r := r) e j x) ≤ 2 ^ q := by
  let f : LowerFace (r := r) e j x → ↑(restSupport e j x).powerset :=
    fun I ↦ ⟨I.1, Finset.mem_powerset.mpr I.2.1⟩
  have hf : Function.Injective f := by
    intro I J hIJ
    apply Subtype.ext
    exact congrArg
      (fun z : ↑(restSupport e j x).powerset ↦
        (z : Finset (Fin n))) hIJ
  calc
    Fintype.card (LowerFace (r := r) e j x) ≤
        Fintype.card (↑(restSupport e j x).powerset) :=
      Fintype.card_le_of_injective f hf
    _ = 2 ^ (restSupport e j x).card := by
      rw [Fintype.card_coe, Finset.card_powerset]
    _ ≤ 2 ^ q := Nat.pow_le_pow_right (by omega)
      (card_restSupport_le hqr hm he j x)

/-- Vertices extending a fixed `(r-1)`-face to an edge of `F`. -/
abbrev EdgeExtension {n : ℕ} (F : Finset (Finset (Fin n)))
    (I : Finset (Fin n)) := {v : Fin n // insert v I ∈ F}

lemma card_edgeExtension_le {n r D : ℕ}
    {F : Finset (Finset (Fin n))}
    (hr : 0 < r)
    (huniform : ∀ f ∈ F, f.card = r)
    (hdegree : LowerDegreeLE n r D F)
    {I : Finset (Fin n)} (hI : I.card = r - 1) :
    Fintype.card (EdgeExtension F I) ≤ D := by
  let target := F.filter fun f ↦ I ⊆ f
  let f : EdgeExtension F I → ↑target := fun v ↦
    ⟨insert (v : Fin n) I, Finset.mem_filter.mpr
      ⟨v.2, Finset.subset_insert _ _⟩⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have hxnot : (x : Fin n) ∉ I := by
      intro hxI
      have hc := huniform (insert (x : Fin n) I) x.2
      rw [Finset.insert_eq_of_mem hxI, hI] at hc
      omega
    have hins : insert (x : Fin n) I = insert (y : Fin n) I :=
      congrArg (fun z : ↑target ↦ (z : Finset (Fin n))) hxy
    have hxyval : (x : Fin n) = (y : Fin n) :=
      (Finset.insert_inj hxnot).mp hins
    exact Subtype.ext hxyval
  calc
    Fintype.card (EdgeExtension F I) ≤ Fintype.card (↑target) :=
      Fintype.card_le_of_injective f hf
    _ = target.card := Fintype.card_coe _
    _ ≤ D := hdegree I hI

/-- A witness for an ordered extension to contain a forbidden edge, with
one vertex of that edge placed at coordinate `j`. -/
abbrev BadSequenceWitness {n m r : ℕ}
    (e : Finset (Fin n)) (F : Finset (Finset (Fin n))) (j : Fin m) :=
  Σ x : OtherIndex m j → Fin n,
    Σ I : LowerFace (r := r) e j x, EdgeExtension F I.1

lemma card_badSequenceWitness_le {n q r m D : ℕ}
    (hr : 0 < r) (hqr : r < q) (hm : m = q - r)
    {e : Finset (Fin n)} (he : e.card = r)
    {F : Finset (Finset (Fin n))}
    (huniform : ∀ f ∈ F, f.card = r)
    (hdegree : LowerDegreeLE n r D F) (j : Fin m) :
    Fintype.card (BadSequenceWitness (r := r) e F j) ≤
      n ^ (m - 1) * (2 ^ q * D) := by
  rw [Fintype.card_sigma]
  calc
    (∑ x : OtherIndex m j → Fin n,
        Fintype.card (Σ I : LowerFace (r := r) e j x,
          EdgeExtension F I.1)) ≤
        ∑ _x : OtherIndex m j → Fin n, 2 ^ q * D := by
      apply Finset.sum_le_sum
      intro x hx
      rw [Fintype.card_sigma]
      calc
        (∑ I : LowerFace (r := r) e j x,
            Fintype.card (EdgeExtension F I.1)) ≤
            ∑ _I : LowerFace (r := r) e j x, D := by
          apply Finset.sum_le_sum
          intro I hImem
          exact card_edgeExtension_le hr huniform hdegree I.2.2
        _ = Fintype.card (LowerFace (r := r) e j x) * D := by simp
        _ ≤ 2 ^ q * D := Nat.mul_le_mul_right D
          (card_lowerFace_le hqr hm he j x)
    _ = n ^ (m - 1) * (2 ^ q * D) := by
      simp [Fintype.card_fun, card_otherIndex]

/-- Restore the distinguished coordinate of a tuple. -/
def reassemble {n m : ℕ} (j : Fin m)
    (x : OtherIndex m j → Fin n) (v : Fin n) : Fin m → Fin n :=
  fun i ↦ if h : i = j then v else x ⟨i, h⟩

@[simp] lemma reassemble_apply_self {n m : ℕ} (j : Fin m)
    (x : OtherIndex m j → Fin n) (v : Fin n) :
    reassemble j x v j = v := by
  simp [reassemble]

@[simp] lemma reassemble_apply_ne {n m : ℕ} (j i : Fin m)
    (x : OtherIndex m j → Fin n) (v : Fin n) (hi : i ≠ j) :
    reassemble j x v i = x ⟨i, hi⟩ := by
  simp [reassemble, hi]

/-- The vertex set encoded by an ordered extension of a root. -/
def sequenceSet {n m : ℕ} (e : Finset (Fin n))
    (x : Fin m → Fin n) : Finset (Fin n) :=
  e ∪ Finset.univ.image x

/-- `q`-extensions of `e` containing at least one edge of `F`. -/
def spoiledExtensions (n q : ℕ) (F : Finset (Finset (Fin n)))
    (e : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  (Typicality.uniformEdges n q).filter fun Q ↦
    e ⊆ Q ∧ ∃ f ∈ F, f ⊆ Q

private theorem card_mul_le_card_mul_of_relation
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (left : Finset α) (right : Finset β) (rel : α → β → Prop)
    [DecidableRel rel] (a b : ℕ)
    (hleft : ∀ x ∈ left, a ≤ (right.filter (rel x)).card)
    (hright : ∀ y ∈ right, (left.filter fun x ↦ rel x y).card ≤ b) :
    left.card * a ≤ right.card * b := by
  calc
    left.card * a = ∑ _x ∈ left, a := by simp
    _ ≤ ∑ x ∈ left, (right.filter (rel x)).card := by
      apply Finset.sum_le_sum
      exact hleft
    _ = ∑ y ∈ right, (left.filter fun x ↦ rel x y).card := by
      simp only [Finset.card_filter]
      rw [Finset.sum_comm]
    _ ≤ ∑ _y ∈ right, b := by
      apply Finset.sum_le_sum
      exact hright
    _ = right.card * b := by simp

/-- Sparse-edge extension estimate.  The constant is deliberately generous
and entirely explicit; its exponent `q-r-1` is the essential feature. -/
theorem card_spoiledExtensions_le
    {n q r D : ℕ} (hr : 0 < r) (hqr : r < q)
    {F : Finset (Finset (Fin n))}
    (huniform : ∀ f ∈ F, f.card = r)
    (hdegree : LowerDegreeLE n r D F)
    {e : Finset (Fin n)} (hecard : e.card = r) (heF : e ∉ F) :
    (spoiledExtensions n q F e).card ≤
      (q - r) * n ^ (q - r - 1) * (2 ^ q * D) := by
  classical
  let m := q - r
  have hmpos : 0 < m := by omega
  let W := Σ j : Fin m, BadSequenceWitness (r := r) e F j
  let right : Finset W := Finset.univ
  let rel : Finset (Fin n) → W → Prop := fun Q w ↦
    Q = sequenceSet e (reassemble w.1 w.2.1 w.2.2.2.1)
  have hleft : ∀ Q ∈ spoiledExtensions n q F e,
      1 ≤ (right.filter (rel Q)).card := by
    intro Q hQ
    have hQdata := Finset.mem_filter.mp hQ
    have hQcard : Q.card = q := Typicality.mem_uniformEdges.mp hQdata.1
    obtain ⟨f, hfF, hfQ⟩ := hQdata.2.2
    have hfcard : f.card = r := huniform f hfF
    have hfenot : f ≠ e := fun hfe ↦ heF (hfe ▸ hfF)
    have hfnsub : ¬f ⊆ e := by
      intro hsub
      exact hfenot (Finset.eq_of_subset_of_card_le hsub (by
        rw [hecard, hfcard]))
    rw [Finset.not_subset] at hfnsub
    obtain ⟨v, hvf, hve⟩ := hfnsub
    have hvQ : v ∈ Q := hfQ hvf
    let S := Q \ e
    have hScard : S.card = m := by
      rw [Finset.card_sdiff_of_subset hQdata.2.1, hQcard, hecard]
    have hvS : v ∈ S := Finset.mem_sdiff.mpr ⟨hvQ, hve⟩
    let enum : Fin m → Fin n := fun i ↦
      ((S.orderIsoOfFin hScard) i : S)
    have henumRange : Finset.univ.image enum = S := by
      ext z
      constructor
      · intro hz
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
        exact ((S.orderIsoOfFin hScard) i).2
      · intro hz
        obtain ⟨i, hi⟩ := (S.orderIsoOfFin hScard).surjective ⟨z, hz⟩
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i,
          congrArg Subtype.val hi⟩
    obtain ⟨j, hj⟩ : ∃ j : Fin m, enum j = v := by
      obtain ⟨j, hj⟩ := (S.orderIsoOfFin hScard).surjective ⟨v, hvS⟩
      exact ⟨j, congrArg Subtype.val hj⟩
    let rest : OtherIndex m j → Fin n := fun i ↦ enum i.1
    let I : Finset (Fin n) := f.erase v
    have hIcard : I.card = r - 1 := by
      simp [I, Finset.card_erase_of_mem hvf, hfcard]
    have hIsub : I ⊆ restSupport e j rest := by
      intro z hzI
      have hzf : z ∈ f := Finset.mem_of_mem_erase hzI
      have hzv : z ≠ v := Finset.ne_of_mem_erase hzI
      by_cases hze : z ∈ e
      · exact Finset.mem_union_left _ hze
      · have hzS : z ∈ S := Finset.mem_sdiff.mpr ⟨hfQ hzf, hze⟩
        obtain ⟨i, hi⟩ := (S.orderIsoOfFin hScard).surjective ⟨z, hzS⟩
        have hienum : enum i = z := congrArg Subtype.val hi
        have hij : i ≠ j := by
          intro hij
          subst i
          exact hzv (hienum.symm.trans hj)
        apply Finset.mem_union_right
        exact Finset.mem_image.mpr ⟨⟨i, hij⟩, Finset.mem_univ _, hienum⟩
    let lower : LowerFace (r := r) e j rest := ⟨I, hIsub, hIcard⟩
    have hvext : insert v I ∈ F := by
      simpa [I, Finset.insert_erase hvf] using hfF
    let ext : EdgeExtension F I := ⟨v, hvext⟩
    let w : W := ⟨j, rest, lower, ext⟩
    have hreassemble : reassemble j rest v = enum := by
      funext i
      by_cases hij : i = j
      · subst i
        rw [reassemble_apply_self]
        exact hj.symm
      · simp [reassemble, hij, rest]
    have hQeq : Q = sequenceSet e enum := by
      rw [sequenceSet, henumRange]
      exact (Finset.union_sdiff_of_subset hQdata.2.1).symm
    have hrel : rel Q w := by
      change Q = sequenceSet e (reassemble j rest v)
      rw [hreassemble]
      exact hQeq
    rw [show 1 ≤ (right.filter (rel Q)).card ↔
        (right.filter (rel Q)).Nonempty by simp]
    exact ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ w, hrel⟩⟩
  have hright : ∀ w ∈ right,
      ((spoiledExtensions n q F e).filter fun Q ↦ rel Q w).card ≤ 1 := by
    intro w hw
    apply Finset.card_le_one.mpr
    intro Q hQ Q' hQ'
    exact (Finset.mem_filter.mp hQ).2.trans
      (Finset.mem_filter.mp hQ').2.symm
  have hrelcount := card_mul_le_card_mul_of_relation
    (spoiledExtensions n q F e) right rel 1 1 hleft hright
  have hWcard : right.card ≤
      m * (n ^ (m - 1) * (2 ^ q * D)) := by
    change Fintype.card W ≤ _
    rw [Fintype.card_sigma]
    calc
      (∑ j : Fin m,
          Fintype.card (BadSequenceWitness (r := r) e F j)) ≤
          ∑ _j : Fin m, n ^ (m - 1) * (2 ^ q * D) := by
        apply Finset.sum_le_sum
        intro j hj
        exact card_badSequenceWitness_le hr hqr rfl hecard
          huniform hdegree j
      _ = m * (n ^ (m - 1) * (2 ^ q * D)) := by simp
  calc
    (spoiledExtensions n q F e).card ≤ right.card := by simpa using hrelcount
    _ ≤ m * (n ^ (m - 1) * (2 ^ q * D)) := hWcard
    _ = (q - r) * n ^ (q - r - 1) * (2 ^ q * D) := by
      simp [m]
      ring

end

end Erdos722.Counting
