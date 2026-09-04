/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos570.TriangleMiddle
import Mathlib.Order.Interval.Finset.Fin

/-!
# Finite extension lemmas for the triangle case

The Goddard--Kleitman proof first embeds the non-minimum-degree core of
the target in a maximum blue clique and then assigns distinct outside
vertices to the deleted vertices.  This file isolates the finite selection
argument.  Its two endpoint average inequalities imply the descending
``staircase'' of candidate-set sizes needed for Hall's theorem.
-/

open scoped BigOperators

noncomputable section

namespace Erdos570

/-- Enumerate a finite type in weakly decreasing order of a natural-valued
weight.  A fixed enumeration of the type breaks ties. -/
theorem exists_descending_card_order {A : Type*} [Fintype A] [DecidableEq A]
    (g : A → ℕ) :
    ∃ L : List A, L.Nodup ∧ L.length = Fintype.card A ∧
      (L : Multiset A) = (Finset.univ : Finset A).val ∧
      ∀ (i j : Fin L.length), i < j → g (L.get j) ≤ g (L.get i) := by
  classical
  let e : A ≃ Fin (Fintype.card A) := Fintype.equivFin A
  let key : A → Lex (OrderDual ℕ × Fin (Fintype.card A)) :=
    fun a ↦ toLex (g a, e a)
  have hkey : Function.Injective key := by
    intro a b h
    exact e.injective (congrArg Prod.snd h)
  let : LinearOrder A := LinearOrder.lift' key hkey
  let L := (Finset.univ : Finset A).sort (· ≤ ·)
  refine ⟨L, Finset.sort_nodup _ _, ?_, ?_, ?_⟩
  · simp [L]
  · exact Finset.sort_eq _ _
  · intro i j hij
    have hs : List.Pairwise (fun a b : A ↦ a ≤ b) L :=
      Finset.pairwise_sort _ _
    have hle := (List.pairwise_iff_get.mp hs) i j hij
    change key (L.get i) ≤ key (L.get j) at hle
    change Prod.Lex (fun a b : OrderDual ℕ ↦ a < b)
      (fun a b : Fin (Fintype.card A) ↦ a ≤ b)
      (g (L.get i), e (L.get i)) (g (L.get j), e (L.get j)) at hle
    obtain h | ⟨h, _⟩ := Prod.lex_iff.mp hle
    · exact h.le
    · exact Nat.le_of_eq h.symm

/-- A sequence bounded above by `G` cannot fall below the staircase
`f-i` if its sum dominates both endpoint rectangles `s*f` and `f*G`.
This is the numerical heart of the Goddard--Kleitman selection argument. -/
theorem staircase_upper_lt_endpoint_max {s f G i : ℕ}
    (hf : 1 ≤ f) (hfs : f ≤ s) (hi : i < f) :
    i * G + (s - i) * (f - i - 1) < max (s * f) (f * G) := by
  have his : i ≤ s := hi.le.trans hfs
  have hif : i + 1 ≤ f := by omega
  let a := s - i
  let b := f - i - 1
  have hsa : s = a + i := by simp [a, Nat.sub_add_cancel his]
  have hfb : f = b + i + 1 := by dsimp [b]; omega
  by_cases hGi : G ≤ s - i
  · apply lt_of_lt_of_le ?_ (le_max_left _ _)
    rw [show s - i = a by rfl, show f - i - 1 = b by rfl, hsa, hfb]
    have hGa : G ≤ a := by simpa [a] using hGi
    nlinarith
  · apply lt_of_lt_of_le ?_ (le_max_right _ _)
    have hiG : s - i < G := Nat.lt_of_not_ge hGi
    rw [show s - i = a by rfl, show f - i - 1 = b by rfl, hfb]
    have haG : a < G := by simpa [a] using hiG
    nlinarith

/-- The two Goddard--Kleitman endpoint average inequalities force a choice
of `f` distinct indices whose weights dominate the descending staircase. -/
theorem exists_staircase_selection {A : Type*} [Fintype A] [DecidableEq A]
    (g : A → ℕ) {f G : ℕ} (hf : 1 ≤ f) (hfs : f ≤ Fintype.card A)
    (hbound : ∀ a, g a ≤ G)
    (hsf : Fintype.card A * f ≤ ∑ a, g a)
    (hfG : f * G ≤ ∑ a, g a) :
    ∃ pick : Fin f → A, Function.Injective pick ∧
      ∀ i : Fin f, f - i ≤ g (pick i) := by
  classical
  obtain ⟨L, hLn, hLlen, hLval, hsort⟩ := exists_descending_card_order g
  let idx : Fin f → Fin L.length := fun i ↦
    ⟨i, by rw [hLlen]; exact i.2.trans_le hfs⟩
  let pick : Fin f → A := fun i ↦ L.get (idx i)
  refine ⟨pick, ?_, ?_⟩
  · intro i j hij
    have hidx : idx i = idx j := hLn.injective_get hij
    apply Fin.ext
    simpa [idx] using congrArg Fin.val hidx
  have hsumL : (L.map g).sum = ∑ a, g a := by
    have hm := congrArg (fun s : Multiset A ↦ (s.map g).sum) hLval
    simpa using hm
  intro i
  let ii : Fin L.length := idx i
  by_contra hbad
  have hpick : pick i = L.get ii := rfl
  have hgi : g (L.get ii) ≤ f - i - 1 := by rw [← hpick]; omega
  have hpref : ((L.take i).map g).sum ≤ i * G := by
    calc
      ((L.take i).map g).sum ≤ ((L.take i).map fun _ ↦ G).sum := by
        apply List.sum_le_sum
        intro a ha
        exact hbound a
      _ = i * G := by
        have hiL : (i : ℕ) ≤ L.length := by
          rw [hLlen]
          exact i.2.le.trans hfs
        simp [Nat.min_eq_left hiL]
  have hsrel : List.Pairwise (fun a b ↦ g b ≤ g a) L := by
    rw [List.pairwise_iff_get]
    intro a b hab
    exact hsort a b hab
  have hdropEq : L.drop i = L.get ii :: L.drop (i + 1) := by
    simpa [ii, List.get_eq_getElem] using
      (List.drop_eq_getElem_cons (l := L) (i := i) (by omega))
  have hsuffixBound : ∀ a ∈ L.drop i, g a ≤ f - i - 1 := by
    intro a ha
    rw [hdropEq] at ha
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · exact hgi
    · exact ((by
        have hp := hsrel.drop (i := i)
        rw [hdropEq, List.pairwise_cons] at hp
        exact hp.1 _ ha) : g a ≤ g (L.get ii)).trans hgi
  have hsuff : ((L.drop i).map g).sum ≤
      (L.length - i) * (f - i - 1) := by
    calc
      ((L.drop i).map g).sum ≤
          ((L.drop i).map fun _ ↦ f - i - 1).sum := by
        apply List.sum_le_sum
        intro a ha
        exact hsuffixBound a ha
      _ = (L.length - i) * (f - i - 1) := by simp
  have hsumUpper : (L.map g).sum ≤
      i * G + (Fintype.card A - i) * (f - i - 1) := by
    rw [← hLlen]
    rw [← List.sum_take_add_sum_drop (L.map g) i]
    simpa using Nat.add_le_add hpref hsuff
  have hlower : max (Fintype.card A * f) (f * G) ≤ (L.map g).sum := by
    rw [hsumL, max_le_iff]
    exact ⟨hsf, hfG⟩
  have harith := staircase_upper_lt_endpoint_max (G := G) hf hfs i.2
  exact (Nat.not_lt_of_ge hlower) (hsumUpper.trans_lt harith)

/-- Floor-aware version of the endpoint rectangle estimate.  After
subtracting the common floor `σ`, it is exactly
`staircase_upper_lt_endpoint_max`. -/
theorem staircase_floor_upper_lt_endpoint_max {s f G σ i : ℕ}
    (hf : 1 ≤ f) (hfs : f ≤ s) (hσf : σ ≤ f) (hσG : σ ≤ G)
    (hi : i < f - σ) :
    i * G + (s - i) * (f - i - 1) <
      max (s * f) (s * σ + (f - σ) * (G - σ)) := by
  have his : i ≤ s := hi.le.trans (Nat.sub_le f σ) |>.trans hfs
  let F := f - σ
  let G' := G - σ
  let a := s - i
  let b := F - i - 1
  have hFpos : 1 ≤ F := by dsimp only [F]; omega
  have hFs : F ≤ s := by dsimp only [F]; omega
  have hfi : f - i - 1 = σ + b := by dsimp only [F, b]; omega
  have hsa : s = a + i := by dsimp only [a]; omega
  have hfF : f = σ + F := by dsimp only [F]; omega
  have hGG' : G = σ + G' := by dsimp only [G']; omega
  have hFb : F = b + i + 1 := by dsimp only [b]; omega
  by_cases hG'a : G' ≤ a
  · apply lt_of_lt_of_le ?_ (le_max_left _ _)
    nlinarith
  · apply lt_of_lt_of_le ?_ (le_max_right _ _)
    have haG' : a < G' := Nat.lt_of_not_ge hG'a
    nlinarith

/-- Floor-aware staircase selection.  Every weight already supplies the
last `σ` steps; the two shifted endpoint inequalities force the remaining
steps at the beginning of the decreasing order. -/
theorem exists_floor_staircase_selection
    {A : Type*} [Fintype A] [DecidableEq A]
    (g : A → ℕ) {f G σ : ℕ} (hf : 1 ≤ f)
    (hfs : f ≤ Fintype.card A) (hσf : σ ≤ f)
    (hfloor : ∀ a, σ ≤ g a) (hbound : ∀ a, g a ≤ G)
    (hsf : Fintype.card A * f ≤ ∑ a, g a)
    (hshift : Fintype.card A * σ + (f - σ) * (G - σ) ≤ ∑ a, g a) :
    ∃ pick : Fin f → A, Function.Injective pick ∧
      ∀ i : Fin f, f - i ≤ g (pick i) := by
  classical
  obtain ⟨L, hLn, hLlen, hLval, hsort⟩ := exists_descending_card_order g
  let idx : Fin f → Fin L.length := fun i ↦
    ⟨i, by rw [hLlen]; exact i.2.trans_le hfs⟩
  let pick : Fin f → A := fun i ↦ L.get (idx i)
  refine ⟨pick, ?_, ?_⟩
  · intro i j hij
    have hidx : idx i = idx j := hLn.injective_get hij
    apply Fin.ext
    simpa [idx] using congrArg Fin.val hidx
  have hsumL : (L.map g).sum = ∑ a, g a := by
    have hm := congrArg (fun u : Multiset A ↦ (u.map g).sum) hLval
    simpa using hm
  intro i
  let ii : Fin L.length := idx i
  by_contra hbad
  have hpick : pick i = L.get ii := rfl
  have hgi : g (L.get ii) ≤ f - i - 1 := by rw [← hpick]; omega
  have hσgi : σ ≤ g (L.get ii) := hfloor _
  have hiShift : (i : ℕ) < f - σ := by omega
  have hpref : ((L.take i).map g).sum ≤ i * G := by
    calc
      ((L.take i).map g).sum ≤ ((L.take i).map fun _ ↦ G).sum := by
        apply List.sum_le_sum
        intro a ha
        exact hbound a
      _ = i * G := by
        have hiL : (i : ℕ) ≤ L.length := by
          rw [hLlen]
          exact i.2.le.trans hfs
        simp [Nat.min_eq_left hiL]
  have hsrel : List.Pairwise (fun a b ↦ g b ≤ g a) L := by
    rw [List.pairwise_iff_get]
    intro a b hab
    exact hsort a b hab
  have hdropEq : L.drop i = L.get ii :: L.drop (i + 1) := by
    simpa [ii, List.get_eq_getElem] using
      (List.drop_eq_getElem_cons (l := L) (i := i) (by omega))
  have hsuffixBound : ∀ a ∈ L.drop i, g a ≤ f - i - 1 := by
    intro a ha
    rw [hdropEq] at ha
    simp only [List.mem_cons] at ha
    rcases ha with rfl | ha
    · exact hgi
    · exact ((by
        have hp := hsrel.drop (i := i)
        rw [hdropEq, List.pairwise_cons] at hp
        exact hp.1 _ ha) : g a ≤ g (L.get ii)).trans hgi
  have hsuff : ((L.drop i).map g).sum ≤
      (L.length - i) * (f - i - 1) := by
    calc
      ((L.drop i).map g).sum ≤
          ((L.drop i).map fun _ ↦ f - i - 1).sum := by
        apply List.sum_le_sum
        intro a ha
        exact hsuffixBound a ha
      _ = (L.length - i) * (f - i - 1) := by simp
  have hsumUpper : (L.map g).sum ≤
      i * G + (Fintype.card A - i) * (f - i - 1) := by
    rw [← hLlen]
    rw [← List.sum_take_add_sum_drop (L.map g) i]
    simpa using Nat.add_le_add hpref hsuff
  have hlower : max (Fintype.card A * f)
      (Fintype.card A * σ + (f - σ) * (G - σ)) ≤ (L.map g).sum := by
    rw [hsumL, max_le_iff]
    exact ⟨hsf, hshift⟩
  have hcardPos : 0 < Fintype.card A := lt_of_lt_of_le hf hfs
  let a0 : A := Fintype.equivFin A |>.symm ⟨0, by simpa using hcardPos⟩
  have hσG : σ ≤ G := (hfloor a0).trans (hbound a0)
  have harith := staircase_floor_upper_lt_endpoint_max hf hfs hσf hσG hiShift
  exact (Nat.not_lt_of_ge hlower) (hsumUpper.trans_lt harith)

/-- Candidate sets satisfying the descending staircase have distinct
representatives.  This is Hall's theorem, with the Hall inequalities read
off from the least index in each nonempty subfamily. -/
theorem exists_distinct_representatives_of_staircase
    {Y : Type*} [DecidableEq Y] {f : ℕ} (cand : Fin f → Finset Y)
    (hcard : ∀ i : Fin f, f - i ≤ (cand i).card) :
    ∃ choose : Fin f → Y, Function.Injective choose ∧
      ∀ i : Fin f, choose i ∈ cand i := by
  classical
  rw [← Finset.all_card_le_biUnion_card_iff_existsInjective']
  intro S
  by_cases hS : S.Nonempty
  · let i := S.min' hS
    have hSi : i ∈ S := S.min'_mem hS
    have hSsub : S ⊆ Finset.Ici i := by
      intro j hj
      exact Finset.mem_Ici.mpr (S.min'_le j hj)
    calc
      S.card ≤ (Finset.Ici i).card := Finset.card_le_card hSsub
      _ = f - i := Fin.card_Ici i
      _ ≤ (cand i).card := hcard i
      _ ≤ (S.biUnion cand).card := Finset.card_le_card
        (Finset.subset_biUnion_of_mem cand hSi)
  · simp only [Finset.not_nonempty_iff_eq_empty] at hS
    simp [hS]

/-- Combined finite extension lemma: endpoint sum bounds first select the
right `f` indices and then Hall's theorem chooses distinct representatives
from their candidate sets. -/
theorem exists_selected_distinct_representatives
    {A Y : Type*} [Fintype A] [DecidableEq A] [DecidableEq Y]
    (cand : A → Finset Y) {f G : ℕ}
    (hf : 1 ≤ f) (hfs : f ≤ Fintype.card A)
    (hbound : ∀ a, (cand a).card ≤ G)
    (hsf : Fintype.card A * f ≤ ∑ a, (cand a).card)
    (hfG : f * G ≤ ∑ a, (cand a).card) :
    ∃ pick : Fin f → A, ∃ choose : Fin f → Y,
      Function.Injective pick ∧ Function.Injective choose ∧
      ∀ i : Fin f, choose i ∈ cand (pick i) := by
  obtain ⟨pick, hpick, hstair⟩ :=
    exists_staircase_selection (fun a ↦ (cand a).card) hf hfs hbound hsf hfG
  obtain ⟨choose, hchoose, hmem⟩ :=
    exists_distinct_representatives_of_staircase (fun i ↦ cand (pick i)) hstair
  exact ⟨pick, choose, hpick, hchoose, hmem⟩

end Erdos570
