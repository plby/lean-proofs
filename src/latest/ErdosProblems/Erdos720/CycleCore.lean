import ErdosProblems.Erdos720.Prune
import ErdosProblems.Erdos720.Join
import Mathlib.Combinatorics.SimpleGraph.Bipartite

namespace Erdos720

open Finset SimpleGraph

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

noncomputable def sumLeftPart : Finset (A ⊕ B) :=
  Finset.univ.map ⟨Sum.inl, Sum.inl_injective⟩

noncomputable def sumRightPart : Finset (A ⊕ B) :=
  Finset.univ.map ⟨Sum.inr, Sum.inr_injective⟩

@[simp] lemma mem_sumLeftPart {v : A ⊕ B} :
    v ∈ (sumLeftPart : Finset (A ⊕ B)) ↔ ∃ a, v = Sum.inl a := by
  classical
  simp [sumLeftPart, eq_comm]

@[simp] lemma mem_sumRightPart {v : A ⊕ B} :
    v ∈ (sumRightPart : Finset (A ⊕ B)) ↔ ∃ b, v = Sum.inr b := by
  classical
  simp [sumRightPart, eq_comm]

lemma sumParts_disjoint :
    Disjoint (sumLeftPart : Finset (A ⊕ B)) sumRightPart := by
  classical
  rw [Finset.disjoint_left]
  rintro (_ | _) <;> simp

lemma sumParts_cover :
    (sumLeftPart : Finset (A ⊕ B)) ∪ sumRightPart = univ := by
  classical
  ext (_ | _) <;> simp

@[simp] lemma card_sumLeftPart :
    (sumLeftPart : Finset (A ⊕ B)).card = Fintype.card A := by
  classical
  simp [sumLeftPart]

@[simp] lemma card_sumRightPart :
    (sumRightPart : Finset (A ⊕ B)).card = Fintype.card B := by
  classical
  simp [sumRightPart]

lemma exists_bipartite_connector (m height q : ℕ) (hm : 1 ≤ m)
    (hh : 0 < height) (hq : 0 < q)
    (hcap : 1 + q + 2 * (2 ^ (height + 1) - 2) ≤ 9 * m)
    (G : SimpleGraph (Fin (128 * m) ⊕ Fin (128 * m)))
    (hnoHole : ∀ X Y : Finset (Fin (128 * m) ⊕ Fin (128 * m)),
      X ⊆ sumLeftPart → Y ⊆ sumRightPart → X.card = m → Y.card = m →
      ∃ x ∈ X, ∃ y ∈ Y, G.Adj x y) :
    ∃ Z : Finset (Fin (128 * m) ⊕ Fin (128 * m)),
      Nonempty (RobustConnector (G.induce (↑Z : Set _)) height q) := by
  classical
  obtain ⟨Z, hZcard, hZnonempty, hZexp⟩ :=
    prune_bipartite_no_hole G sumLeftPart sumRightPart m hm
      sumParts_disjoint sumParts_cover (by simp) (by simp) hnoHole
  obtain ⟨root⟩ := hZnonempty
  refine ⟨Z, robust_connector (G.induce (↑Z : Set _)) (9 * m) height q root
    (by omega) hh hq hcap ?_⟩
  intro S hS
  exact hZexp S (by omega)

lemma ExactSimplePath.odd_end_flip {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} (X : Finset V)
    (hflip : ∀ ⦃u v⦄, G.Adj u v → (u ∈ X ↔ v ∉ X))
    (k : ℕ) {a b : V} (P : ExactSimplePath G a (2 * k + 1) b) :
    (a ∈ X ↔ b ∉ X) := by
  induction k generalizing a b with
  | zero =>
      rcases P with ⟨l, hnd, hch, hlen, hhead, hlast⟩
      obtain ⟨ls, rfl⟩ := List.head?_eq_some_iff.mp hhead
      cases ls with
      | nil => simp at hlen
      | cons x xs =>
          cases xs with
          | nil =>
              have hxb : x = b := by simpa using hlast
              subst x
              have hab : G.Adj a b := (List.isChain_cons.mp hch).1 b (by simp)
              exact hflip hab
          | cons y ys => simp at hlen
  | succ k ih =>
      rcases P with ⟨l, hnd, hch, hlen, hhead, hlast⟩
      obtain ⟨ls, rfl⟩ := List.head?_eq_some_iff.mp hhead
      cases ls with
      | nil => simp at hlen
      | cons x xs =>
          cases xs with
          | nil => simp at hlen
          | cons y ys =>
              have htail : ExactSimplePath G y (2 * k + 1) b := by
                refine ⟨y :: ys, hnd.tail.tail, hch.tail.tail, ?_, by simp, ?_⟩
                · simp only [List.length_cons] at hlen ⊢
                  omega
                · simpa using hlast
              have hay : a ∈ X ↔ y ∈ X := by
                have hax : a ∈ X ↔ x ∉ X :=
                  hflip ((List.isChain_cons.mp hch).1 x (by simp))
                have hxy : x ∈ X ↔ y ∉ X :=
                  hflip ((List.isChain_cons.mp hch.tail).1 y (by simp))
                tauto
              exact hay.trans (ih htail)

lemma bipartite_adj_flip
    {G : SimpleGraph (A ⊕ B)} (hG : G ≤ completeBipartiteGraph A B)
    {u v : A ⊕ B} (huv : G.Adj u v) :
    (u ∈ (sumLeftPart : Finset (A ⊕ B)) ↔
      v ∉ (sumLeftPart : Finset (A ⊕ B))) := by
  have h := hG huv
  rcases u with u | u <;> rcases v with v | v <;> simp_all [completeBipartiteGraph]

lemma not_mem_sumLeftPart_iff {v : A ⊕ B} :
    v ∉ (sumLeftPart : Finset (A ⊕ B)) ↔ v ∈ sumRightPart := by
  rcases v with v | v <;> simp

lemma bipartite_connector_closes (m height q k : ℕ) (hm : 1 ≤ m)
    (hh : 0 < height) (hq : 0 < q) (hleaves : m ≤ 2 ^ height)
    (hodd : 2 * height + q = 2 * k + 1)
    (hcap : 1 + q + 2 * (2 ^ (height + 1) - 2) ≤ 9 * m)
    (G : SimpleGraph (Fin (128 * m) ⊕ Fin (128 * m)))
    (hG : G ≤ completeBipartiteGraph (Fin (128 * m)) (Fin (128 * m)))
    (hnoHole : ∀ X Y : Finset (Fin (128 * m) ⊕ Fin (128 * m)),
      X ⊆ sumLeftPart → Y ⊆ sumRightPart → X.card = m → Y.card = m →
      ∃ x ∈ X, ∃ y ∈ Y, G.Adj x y) :
    cycleGraph (2 * height + q + 1) ⊑ G := by
  classical
  obtain ⟨Z, ⟨C⟩⟩ := exists_bipartite_connector m height q hm hh hq hcap G hnoHole
  let XL : Finset {v // v ∈ Z} := univ.filter fun v => v.1 ∈
    (sumLeftPart : Finset (Fin (128 * m) ⊕ Fin (128 * m)))
  have hflipZ : ∀ ⦃u v : {v // v ∈ Z}⦄,
      (G.induce (↑Z : Set _)).Adj u v → (u ∈ XL ↔ v ∉ XL) := by
    intro u v huv
    have h := bipartite_adj_flip hG huv
    simpa [XL] using h
  have hopposite : ∀ ⦃a b⦄, a ∈ C.leftLeaves → b ∈ C.rightLeaves →
      (a ∈ XL ↔ b ∉ XL) := by
    intro a b ha hb
    have P := C.exactSimplePath hh hq ha hb
    rw [hodd] at P
    exact P.odd_end_flip XL hflipZ k
  have hleftCard : m ≤ C.leftLeaves.card := by rw [C.card_left]; exact hleaves
  have hrightCard : m ≤ C.rightLeaves.card := by rw [C.card_right]; exact hleaves
  obtain ⟨a₀, ha₀⟩ := card_pos.mp (lt_of_lt_of_le (by omega) hleftCard)
  obtain ⟨b₀, hb₀⟩ := card_pos.mp (lt_of_lt_of_le (by omega) hrightCard)
  by_cases haSide : a₀ ∈ XL
  · have hleftSide : C.leftLeaves ⊆ XL := by
      intro a ha
      have haopp := hopposite ha hb₀
      have ha₀opp := hopposite ha₀ hb₀
      tauto
    have hrightSide : ∀ ⦃b⦄, b ∈ C.rightLeaves → b ∉ XL := by
      intro b hb
      exact (hopposite ha₀ hb).mp haSide
    obtain ⟨LA, hLA, hLAcard⟩ := exists_subset_card_eq hleftCard
    obtain ⟨RB, hRB, hRBcard⟩ := exists_subset_card_eq hrightCard
    have hLAleft : subtypeFinset LA ⊆
        (sumLeftPart : Finset (Fin (128 * m) ⊕ Fin (128 * m))) := by
      intro v hv
      obtain ⟨hvZ, hvLA⟩ := mem_subtypeFinset.mp hv
      have hvXL := hleftSide (hLA hvLA)
      simpa [XL] using hvXL
    have hRBright : subtypeFinset RB ⊆
        (sumRightPart : Finset (Fin (128 * m) ⊕ Fin (128 * m))) := by
      intro v hv
      obtain ⟨hvZ, hvRB⟩ := mem_subtypeFinset.mp hv
      exact not_mem_sumLeftPart_iff.mp (by
        simpa [XL] using hrightSide (hRB hvRB))
    obtain ⟨a, ha, b, hb, hab⟩ := hnoHole (subtypeFinset LA) (subtypeFinset RB)
      hLAleft hRBright (by simpa [card_subtypeFinset] using hLAcard)
      (by simpa [card_subtypeFinset] using hRBcard)
    obtain ⟨haZ, haLA⟩ := mem_subtypeFinset.mp ha
    obtain ⟨hbZ, hbRB⟩ := mem_subtypeFinset.mp hb
    have P : ExactSimplePath (G.induce (↑Z : Set _)) ⟨a, haZ⟩
        ((2 * height + q + 1) - 1) ⟨b, hbZ⟩ := by
      simpa using C.exactSimplePath hh hq (hLA haLA) (hRB hbRB)
    have hcycle := P.cycleGraph_isContained (n := 2 * height + q + 1) (by omega)
      (show (G.induce (↑Z : Set _)).Adj ⟨a, haZ⟩ ⟨b, hbZ⟩ from hab)
    exact hcycle.trans (Embedding.induce (G := G) (↑Z : Set _)).isContained
  · have hleftSide : ∀ ⦃a⦄, a ∈ C.leftLeaves → a ∉ XL := by
      intro a ha haXL
      have haopp := hopposite ha hb₀
      have ha₀opp := hopposite ha₀ hb₀
      tauto
    have hrightSide : C.rightLeaves ⊆ XL := by
      intro b hb
      have hbopp := hopposite ha₀ hb
      tauto
    obtain ⟨LA, hLA, hLAcard⟩ := exists_subset_card_eq hleftCard
    obtain ⟨RB, hRB, hRBcard⟩ := exists_subset_card_eq hrightCard
    have hRBleft : subtypeFinset RB ⊆
        (sumLeftPart : Finset (Fin (128 * m) ⊕ Fin (128 * m))) := by
      intro v hv
      obtain ⟨hvZ, hvRB⟩ := mem_subtypeFinset.mp hv
      simpa [XL] using hrightSide (hRB hvRB)
    have hLAright : subtypeFinset LA ⊆
        (sumRightPart : Finset (Fin (128 * m) ⊕ Fin (128 * m))) := by
      intro v hv
      obtain ⟨hvZ, hvLA⟩ := mem_subtypeFinset.mp hv
      apply not_mem_sumLeftPart_iff.mp
      simpa [XL] using hleftSide (hLA hvLA)
    obtain ⟨b, hb, a, ha, hba⟩ := hnoHole (subtypeFinset RB) (subtypeFinset LA)
      hRBleft hLAright (by simpa [card_subtypeFinset] using hRBcard)
      (by simpa [card_subtypeFinset] using hLAcard)
    obtain ⟨hbZ, hbRB⟩ := mem_subtypeFinset.mp hb
    obtain ⟨haZ, haLA⟩ := mem_subtypeFinset.mp ha
    have P : ExactSimplePath (G.induce (↑Z : Set _)) ⟨a, haZ⟩
        ((2 * height + q + 1) - 1) ⟨b, hbZ⟩ := by
      simpa using C.exactSimplePath hh hq (hLA haLA) (hRB hbRB)
    have hcycle := P.cycleGraph_isContained (n := 2 * height + q + 1) (by omega)
      (show (G.induce (↑Z : Set _)).Adj ⟨a, haZ⟩ ⟨b, hbZ⟩ from hba.symm)
    exact hcycle.trans (Embedding.induce (G := G) (↑Z : Set _)).isContained

lemma exists_common_external_vertex {V W : Type*}
    [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (m : ℕ) (hm : 1 ≤ m) (hW : Fintype.card W = 2 * m - 1)
    (L R : Finset V) (hL : m ≤ L.card) (hR : m ≤ R.card)
    (E : V → W → Prop) [DecidableRel E]
    (hnoL : ∀ A : Finset V, A ⊆ L → A.card = m →
      ∀ B : Finset W, B.card = m → ∃ a ∈ A, ∃ b ∈ B, E a b)
    (hnoR : ∀ A : Finset V, A ⊆ R → A.card = m →
      ∀ B : Finset W, B.card = m → ∃ a ∈ A, ∃ b ∈ B, E a b) :
    ∃ l ∈ L, ∃ r ∈ R, ∃ z : W, E l z ∧ E r z := by
  classical
  let NL : Finset W := univ.filter fun z => ∃ l ∈ L, E l z
  let NR : Finset W := univ.filter fun z => ∃ r ∈ R, E r z
  have hNL : m ≤ NL.card := by
    by_contra hbad
    have hcomp : m ≤ (univ \ NL).card := by
      rw [card_sdiff_of_subset (subset_univ _), card_univ, hW]
      omega
    obtain ⟨A, hA, hAcard⟩ := exists_subset_card_eq hL
    obtain ⟨B, hB, hBcard⟩ := exists_subset_card_eq hcomp
    obtain ⟨a, ha, z, hz, haz⟩ := hnoL A hA hAcard B hBcard
    have hzcomp := hB hz
    exact (mem_sdiff.mp hzcomp).2 (by
      simp [NL]
      exact ⟨a, hA ha, haz⟩)
  have hNR : m ≤ NR.card := by
    by_contra hbad
    have hcomp : m ≤ (univ \ NR).card := by
      rw [card_sdiff_of_subset (subset_univ _), card_univ, hW]
      omega
    obtain ⟨A, hA, hAcard⟩ := exists_subset_card_eq hR
    obtain ⟨B, hB, hBcard⟩ := exists_subset_card_eq hcomp
    obtain ⟨a, ha, z, hz, haz⟩ := hnoR A hA hAcard B hBcard
    have hzcomp := hB hz
    exact (mem_sdiff.mp hzcomp).2 (by
      simp [NR]
      exact ⟨a, hA ha, haz⟩)
  have hinter : (NL ∩ NR).Nonempty := by
    rw [nonempty_iff_ne_empty]
    intro hempty
    have hcardInter : (NL ∩ NR).card = 0 := by simp [hempty]
    have hunion : (NL ∪ NR).card ≤ Fintype.card W := by
      simpa using card_le_card (subset_univ (NL ∪ NR))
    have hadd := card_union_add_card_inter NL NR
    rw [hcardInter, add_zero] at hadd
    rw [hW] at hunion
    omega
  obtain ⟨z, hz⟩ := hinter
  obtain ⟨hzNL, hzNR⟩ := mem_inter.mp hz
  obtain ⟨l, hl, hlz⟩ := (mem_filter.mp hzNL).2
  obtain ⟨r, hr, hrz⟩ := (mem_filter.mp hzNR).2
  exact ⟨l, hl, r, hr, z, hlz, hrz⟩

end Erdos720
