/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos547b.Lemma59
import ErdosProblems.Erdos547b.Lemma51DynamicRegularPair

/-!
# Marked branch embedding through two regular pairs with a common side

Root-colour marked vertices use the intermediate cluster, opposite-colour
vertices use the common side, and the remaining root-colour vertices use
the other matching side. All atypical-vertex losses are explicit.
-/

open scoped SimpleGraph Classical
noncomputable section

namespace Erdos547b.ZhaoMarkedTripleEmbedding

open Finset SimpleGraph Erdos547b.RegularPair Erdos547b.ZhaoLemma59
open Erdos547b.ZhaoLemma51DynamicRegularPair

variable {B : Type*} [Fintype B] [DecidableEq B]
variable (G : SimpleGraph B) [DecidableRel G.Adj]

private theorem cleaned_degree
    (C D U V bad : Finset B) (ε d loss : ℝ) (b : ℕ)
    (hd : d ≤ G.edgeDensity C D) (hbad : (bad.card : ℝ) ≤ loss)
    (hmargin : (b : ℝ) + loss ≤ (d - ε) * V.card)
    {v : B} (hv : v ∈ U \ dynamicLowDegreeVertices G ε C D U V) :
    b ≤ #((V \ bad).filter (G.Adj v)) := by
  have hraw : (G.edgeDensity C D - ε) * (V.card : ℝ) ≤ # (V.filter (G.Adj v)) := by
    apply le_of_not_gt
    intro h
    exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hv).1, h⟩)
  have hmul := mul_le_mul_of_nonneg_right (sub_le_sub_right hd ε) (Nat.cast_nonneg V.card : (0 : ℝ) ≤ V.card)
  have hnat : b + bad.card ≤ # (V.filter (G.Adj v)) := by
    have hreal : (b : ℝ) + bad.card ≤ # (V.filter (G.Adj v)) := by linarith only [hraw, hmul, hmargin, hbad]
    exact_mod_cast hreal
  exact card_neighbors_cleaned_ge G V bad v b hnat

structure TripleCandidates (C' X' Y' : Finset B) (b : ℕ) where
  C : Finset B
  X : Finset B
  Y : Finset B
  C_subset : C ⊆ C'
  X_subset : X ⊆ X'
  Y_subset : Y ⊆ Y'
  C_nonempty : C.Nonempty
  CX : ∀ v ∈ C, b ≤ #(X.filter (G.Adj v))
  YX : ∀ v ∈ Y, b ≤ #(X.filter (G.Adj v))
  XC : ∀ v ∈ X, b ≤ #(C.filter (G.Adj v))
  XY : ∀ v ∈ X, b ≤ #(Y.filter (G.Adj v))

theorem exists_tripleCandidates
    (C X Y C' X' Y' : Finset B) (ε dC dY : ℝ) (b : ℕ)
    (hCX : G.IsUniform ε C X) (hYX : G.IsUniform ε Y X)
    (hC : C' ⊆ C) (hX : X' ⊆ X) (hY : Y' ⊆ Y)
    (hCLarge : ε * C.card < (C'.card : ℝ))
    (hXLarge : ε * X.card ≤ (X'.card : ℝ))
    (hYLarge : ε * Y.card ≤ (Y'.card : ℝ))
    (hdC : dC ≤ G.edgeDensity C X) (hdY : dY ≤ G.edgeDensity Y X)
    (hmCX : (b : ℝ) + 2 * ε * X.card ≤ (dC - ε) * X'.card)
    (hmYX : (b : ℝ) + 2 * ε * X.card ≤ (dY - ε) * X'.card)
    (hmXC : (b : ℝ) + ε * C.card ≤ (dC - ε) * C'.card)
    (hmXY : (b : ℝ) + ε * Y.card ≤ (dY - ε) * Y'.card) :
    Nonempty (TripleCandidates G C' X' Y' b) := by
  let badC := dynamicLowDegreeVertices G ε C X C' X'
  let badY := dynamicLowDegreeVertices G ε Y X Y' X'
  let badXC := dynamicLowDegreeVertices G ε X C X' C'
  let badXY := dynamicLowDegreeVertices G ε X Y X' Y'
  let badX := badXC ∪ badXY
  have hc : (badC.card : ℝ) ≤ ε * C.card := card_lowDegreeVertices_le G hCX hC hX hCLarge.le hXLarge
  have hy : (badY.card : ℝ) ≤ ε * Y.card := card_lowDegreeVertices_le G hYX hY hX hYLarge hXLarge
  have hxc : (badXC.card : ℝ) ≤ ε * X.card := card_lowDegreeVertices_le G hCX.symm hX hC hXLarge hCLarge.le
  have hxy : (badXY.card : ℝ) ≤ ε * X.card := card_lowDegreeVertices_le G hYX.symm hX hY hXLarge hYLarge
  have hx : (badX.card : ℝ) ≤ 2 * ε * X.card := by
    have hcard : (badX.card : ℝ) ≤ badXC.card + badXY.card := by exact_mod_cast Finset.card_union_le badXC badXY
    linarith only [hcard, hxc, hxy]
  have hCnonempty : (C' \ badC).Nonempty := by
    have hlt : badC.card < C'.card := by exact_mod_cast hc.trans_lt hCLarge
    obtain ⟨v, hv, hn⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    exact ⟨v, Finset.mem_sdiff.mpr ⟨hv, hn⟩⟩
  refine ⟨{
    C := C' \ badC
    X := X' \ badX
    Y := Y' \ badY
    C_subset := Finset.sdiff_subset
    X_subset := Finset.sdiff_subset
    Y_subset := Finset.sdiff_subset
    C_nonempty := hCnonempty
    CX := fun _ hv => cleaned_degree G C X C' X' badX ε dC (2 * ε * X.card) b hdC hx hmCX hv
    YX := fun _ hv => cleaned_degree G Y X Y' X' badX ε dY (2 * ε * X.card) b hdY hx hmYX hv
    XC := ?_
    XY := ?_ }⟩
  · intro v hv
    apply cleaned_degree G X C X' C' badC ε dC (ε * C.card) b
      (by simpa only [G.edgeDensity_comm X C] using hdC) hc hmXC
    exact Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hv).1,
      fun h => (Finset.mem_sdiff.mp hv).2 (Finset.mem_union_left _ h)⟩
  · intro v hv
    apply cleaned_degree G X Y X' Y' badY ε dY (ε * Y.card) b
      (by simpa only [G.edgeDensity_comm X Y] using hdY) hy hmXY
    exact Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hv).1,
      fun h => (Finset.mem_sdiff.mp hv).2 (Finset.mem_union_right _ h)⟩

theorem exists_markedCopy_of_candidates
    {A : Type*} [Fintype A] [DecidableEq A]
    (T : SimpleGraph A) (hT : T.IsTree) (root : A) (special : Finset A)
    (hspecial : ∀ a ∈ special, hT.coloringTwoOfVert root a = 0)
    (z : B) (C' X' Y' : Finset B)
    (H : TripleCandidates G C' X' Y' (Fintype.card A))
    (hattach : ∀ v ∈ C', G.Adj z v) :
    ∃ f : T.Copy G, G.Adj z (f root) ∧ f root ∈ C' ∧
      (∀ a ∈ special, f a ∈ C') ∧
      ∀ a, a ≠ root → a ∉ special →
        f a ∈ if hT.coloringTwoOfVert root a = 0 then Y' else X' := by
  let marked := insert root special
  let color := hT.coloringTwoOfVert root
  have hmarked : ∀ a ∈ marked, color a = 0 := by
    intro a ha
    rcases Finset.mem_insert.mp ha with har | ha
    · subst a
      exact coloringTwoOfVert_root T hT root
    · exact hspecial a ha
  let candidate : A → Finset B := fun a => if a ∈ marked then H.C else if color a = 0 then H.Y else H.X
  have hrootCandidate : candidate root = H.C := by simp [candidate, marked]
  have hone (a : A) (ha : color a = 1) : candidate a = H.X := by
    have hnot : a ∉ marked := fun hm => Fin.zero_ne_one ((hmarked a hm).symm.trans ha)
    simp only [candidate, if_neg hnot, ha, if_neg (show (1 : Fin 2) ≠ 0 by decide)]
  have hcross : ∀ ⦃a b⦄, T.Adj a b → ∀ v ∈ candidate a,
      Fintype.card A ≤ #((candidate b).filter (G.Adj v)) := by
    intro a b hab v hv
    have hne : color a ≠ color b := color.valid hab
    rcases OrderedRootedForest.fin_two_eq_zero_or_one (color a) with ha | ha <;>
      rcases OrderedRootedForest.fin_two_eq_zero_or_one (color b) with hb | hb
    · exact (hne (ha.trans hb.symm)).elim
    · rw [hone b hb]
      by_cases hm : a ∈ marked
      · exact H.CX v (by simpa only [candidate, if_pos hm] using hv)
      · exact H.YX v (by simpa only [candidate, if_neg hm, ha, if_true] using hv)
    · rw [hone a ha] at hv
      by_cases hm : b ∈ marked
      · simpa only [candidate, if_pos hm] using H.XC v hv
      · simpa only [candidate, if_neg hm, hb, if_true] using H.XY v hv
    · exact (hne (ha.trans hb.symm)).elim
  obtain ⟨w, hw⟩ := H.C_nonempty
  obtain ⟨f, hroot, hmem⟩ := exists_rooted_candidate_copy T G hT root candidate w
    (fun {a} ha => hcross ha w (hrootCandidate.symm ▸ hw)) (fun {a b} ha _ => hcross ha)
  refine ⟨f, hroot.symm ▸ hattach w (H.C_subset hw), hroot.symm ▸ H.C_subset hw, ?_, ?_⟩
  · intro a ha
    by_cases har : a = root
    · simpa only [har, hroot] using H.C_subset hw
    · apply H.C_subset
      have ham : a ∈ marked := Finset.mem_insert_of_mem ha
      simpa only [candidate, if_pos ham] using hmem a har
  · intro a har ha
    have hnot : a ∉ marked := by simpa only [marked, Finset.mem_insert, not_or] using And.intro har ha
    have hm := hmem a har
    simp only [candidate, if_neg hnot] at hm
    change f a ∈ if color a = 0 then Y' else X'
    by_cases hc : color a = 0
    · simpa only [if_pos hc] using H.Y_subset (by simpa only [if_pos hc] using hm)
    · simpa only [if_neg hc] using H.X_subset (by simpa only [if_neg hc] using hm)

theorem exists_markedCopy_of_uniform
    {A : Type*} [Fintype A] [DecidableEq A]
    (T : SimpleGraph A) (hT : T.IsTree) (root : A) (special : Finset A)
    (hspecial : ∀ a ∈ special, hT.coloringTwoOfVert root a = 0)
    (z : B) (C X Y C' X' Y' : Finset B) (ε dC dY : ℝ)
    (hCX : G.IsUniform ε C X) (hYX : G.IsUniform ε Y X)
    (hC : C' ⊆ C) (hX : X' ⊆ X) (hY : Y' ⊆ Y)
    (hCLarge : ε * C.card < (C'.card : ℝ))
    (hXLarge : ε * X.card ≤ (X'.card : ℝ))
    (hYLarge : ε * Y.card ≤ (Y'.card : ℝ))
    (hdC : dC ≤ G.edgeDensity C X) (hdY : dY ≤ G.edgeDensity Y X)
    (hmCX : (Fintype.card A : ℝ) + 2 * ε * X.card ≤ (dC - ε) * X'.card)
    (hmYX : (Fintype.card A : ℝ) + 2 * ε * X.card ≤ (dY - ε) * X'.card)
    (hmXC : (Fintype.card A : ℝ) + ε * C.card ≤ (dC - ε) * C'.card)
    (hmXY : (Fintype.card A : ℝ) + ε * Y.card ≤ (dY - ε) * Y'.card)
    (hattach : ∀ v ∈ C', G.Adj z v) :
    ∃ f : T.Copy G, G.Adj z (f root) ∧ f root ∈ C' ∧
      (∀ a ∈ special, f a ∈ C') ∧
      ∀ a, a ≠ root → a ∉ special →
        f a ∈ if hT.coloringTwoOfVert root a = 0 then Y' else X' := by
  obtain ⟨H⟩ := exists_tripleCandidates G C X Y C' X' Y' ε dC dY (Fintype.card A)
    hCX hYX hC hX hY hCLarge hXLarge hYLarge hdC hdY hmCX hmYX hmXC hmXY
  exact exists_markedCopy_of_candidates G T hT root special hspecial z C' X' Y' H hattach

end Erdos547b.ZhaoMarkedTripleEmbedding

#print axioms Erdos547b.ZhaoMarkedTripleEmbedding.exists_tripleCandidates
#print axioms Erdos547b.ZhaoMarkedTripleEmbedding.exists_markedCopy_of_candidates
#print axioms Erdos547b.ZhaoMarkedTripleEmbedding.exists_markedCopy_of_uniform
