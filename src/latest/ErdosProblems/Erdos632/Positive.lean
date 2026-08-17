import ErdosProblems.Erdos632.Basic
import ErdosProblems.Erdos632.Graph

/-!
# The positive half of the Dvořák--Hu--Sereni gadget

This file proves that every half-list assignment on the explicit gadget `G₅`
has an ordinary list colouring.  The proof follows the flexible-boundary
argument of Dvořák, Hu, and Sereni.
-/

namespace Erdos632

open Finset G5Vertex

section FiniteChoices

variable {Color : Type*} [DecidableEq Color]

/-- Choose a member of a finite set outside a strictly smaller forbidden set. -/
lemma exists_mem_avoiding {A F : Finset Color} (h : F.card < A.card) :
    ∃ a ∈ A, a ∉ F := by
  exact Finset.exists_mem_notMem_of_card_lt_card h

/-- A list of at least two colours contains a colour different from any fixed one. -/
lemma exists_mem_ne_of_two {A : Finset Color} (hA : 2 ≤ A.card) (q : Color) :
    ∃ a ∈ A, a ≠ q := by
  exact A.exists_mem_ne (by omega) q

lemma card_pair_le_two (a b : Color) : ({a, b} : Finset Color).card ≤ 2 := by
  calc
    ({a, b} : Finset Color).card ≤ ({b} : Finset Color).card + 1 := card_insert_le _ _
    _ = 2 := by simp

lemma card_triple_le_three (a b c : Color) : ({a, b, c} : Finset Color).card ≤ 3 := by
  calc
    ({a, b, c} : Finset Color).card ≤ ({b, c} : Finset Color).card + 1 := card_insert_le _ _
    _ ≤ 3 := by have := card_pair_le_two b c; omega

/-- The elementary triangle-extension lemma used throughout the DHS proof. -/
lemma triangle_extension {A B : Finset Color} (hA : 2 ≤ A.card)
    (hB : 2 ≤ B.card) (hne : A ≠ B) (q : Color) :
    ∃ a ∈ A, ∃ b ∈ B, a ≠ b ∧ a ≠ q ∧ b ≠ q := by
  obtain ⟨a, haA, haq⟩ := exists_mem_ne_of_two hA q
  by_cases hb : ∃ b ∈ B, b ≠ q ∧ b ≠ a
  · obtain ⟨b, hbB, hbq, hba⟩ := hb
    exact ⟨a, haA, b, hbB, hba.symm, haq, hbq⟩
  · push_neg at hb
    have hBsub : B ⊆ {q, a} := by
      intro b hbB
      simp only [mem_insert, mem_singleton]
      by_cases hbq : b = q
      · exact Or.inl hbq
      · exact Or.inr (hb b hbB hbq)
    have hpair : ({q, a} : Finset Color).card = 2 := card_pair haq.symm
    have hBeq : B = {q, a} := by
      apply eq_of_subset_of_card_le hBsub
      omega
    have hAnsub : ¬ A ⊆ B := by
      intro hsub
      apply hne
      apply eq_of_subset_of_card_le hsub
      rw [hBeq, hpair]
      exact hA
    obtain ⟨d, hdA, hdB⟩ := Finset.not_subset.1 hAnsub
    have hdq : d ≠ q := by
      intro hdq
      apply hdB
      rw [hBeq, hdq]
      simp
    have hda : d ≠ a := by
      intro hda
      apply hdB
      rw [hBeq, hda]
      simp
    have haB : a ∈ B := by rw [hBeq]; simp
    exact ⟨d, hdA, a, haB, hda, hdq, haq⟩

/-- Greedily colour a path of length four when the first colour is absent
from the list at the last vertex. -/
lemma cycle5_from_missing {A B C D E : Finset Color}
    (hB : 2 ≤ B.card) (hC : 2 ≤ C.card) (hD : 2 ≤ D.card)
    (hE : 2 ≤ E.card) {a : Color} (haA : a ∈ A) (haE : a ∉ E) :
    ∃ b ∈ B, ∃ c ∈ C, ∃ d ∈ D, ∃ e ∈ E,
      a ≠ b ∧ b ≠ c ∧ c ≠ d ∧ d ≠ e ∧ e ≠ a := by
  obtain ⟨b, hbB, hba⟩ := exists_mem_ne_of_two hB a
  obtain ⟨c, hcC, hcb⟩ := exists_mem_ne_of_two hC b
  obtain ⟨d, hdD, hdc⟩ := exists_mem_ne_of_two hD c
  obtain ⟨e, heE, hed⟩ := exists_mem_ne_of_two hE d
  exact ⟨b, hbB, c, hcC, d, hdD, e, heE,
    hba.symm, hcb.symm, hdc.symm, hed.symm, fun h ↦ haE (h ▸ heE)⟩

/-- A five-cycle whose lists all have size at least two is list-colourable
unless all five lists are equal. -/
lemma cycle5_nonconstant {A B C D E : Finset Color}
    (hA : 2 ≤ A.card) (hB : 2 ≤ B.card) (hC : 2 ≤ C.card)
    (hD : 2 ≤ D.card) (hE : 2 ≤ E.card)
    (hne : ¬ (A = B ∧ B = C ∧ C = D ∧ D = E)) :
    ∃ a ∈ A, ∃ b ∈ B, ∃ c ∈ C, ∃ d ∈ D, ∃ e ∈ E,
      a ≠ b ∧ b ≠ c ∧ c ≠ d ∧ d ≠ e ∧ e ≠ a := by
  have adjacent (P Q R S T : Finset Color)
      (hP : 2 ≤ P.card) (hQ : 2 ≤ Q.card) (hR : 2 ≤ R.card)
      (hS : 2 ≤ S.card) (hT : 2 ≤ T.card) (hPQ : P ≠ Q) :
      ∃ p ∈ P, ∃ q ∈ Q, ∃ r ∈ R, ∃ s ∈ S, ∃ t ∈ T,
        p ≠ q ∧ q ≠ r ∧ r ≠ s ∧ s ≠ t ∧ t ≠ p := by
    by_cases hpq : P ⊆ Q
    · have hqp : ¬ Q ⊆ P := fun h ↦ hPQ (Subset.antisymm hpq h)
      obtain ⟨q, hqQ, hqP⟩ := Finset.not_subset.1 hqp
      obtain ⟨r, hrR, s, hsS, t, htT, p, hpP, hqr, hrs, hst, htp, hpq'⟩ :=
        cycle5_from_missing hR hS hT hP hqQ hqP
      exact ⟨p, hpP, q, hqQ, r, hrR, s, hsS, t, htT,
        hpq', hqr, hrs, hst, htp⟩
    · obtain ⟨p, hpP, hpQ⟩ := Finset.not_subset.1 hpq
      obtain ⟨t, htT, s, hsS, r, hrR, q, hqQ, hpt, hts, hsr, hrq, hqp⟩ :=
        cycle5_from_missing hT hS hR hQ hpP hpQ
      exact ⟨p, hpP, q, hqQ, r, hrR, s, hsS, t, htT,
        hqp.symm, hrq.symm, hsr.symm, hts.symm, hpt.symm⟩
  by_cases hAB : A = B
  · by_cases hBC : B = C
    · by_cases hCD : C = D
      · have hDE : D ≠ E := by
          intro hDE
          exact hne ⟨hAB, hBC, hCD, hDE⟩
        obtain ⟨d, hdD, e, heE, a, haA, b, hbB, c, hcC,
            hde, hea, hab, hbc, hcd⟩ := adjacent D E A B C hD hE hA hB hC hDE
        exact ⟨a, haA, b, hbB, c, hcC, d, hdD, e, heE,
          hab, hbc, hcd, hde, hea⟩
      · obtain ⟨c, hcC, d, hdD, e, heE, a, haA, b, hbB,
          hcd, hde, hea, hab, hbc⟩ := adjacent C D E A B hC hD hE hA hB hCD
        exact ⟨a, haA, b, hbB, c, hcC, d, hdD, e, heE, hab, hbc, hcd, hde, hea⟩
    · obtain ⟨b, hbB, c, hcC, d, hdD, e, heE, a, haA,
        hbc, hcd, hde, hea, hab⟩ := adjacent B C D E A hB hC hD hE hA hBC
      exact ⟨a, haA, b, hbB, c, hcC, d, hdD, e, heE, hab, hbc, hcd, hde, hea⟩
  · exact adjacent A B C D E hA hB hC hD hE hAB

/-- A precolouring of two nonadjacent vertices of a five-cycle extends when
all five lists are a common set of at least three colours. -/
lemma common_cycle5_extension {A : Finset Color} (hA : 3 ≤ A.card)
    {a c : Color} (ha : a ∈ A) (hc : c ∈ A) :
    ∃ b ∈ A, ∃ d ∈ A, ∃ e ∈ A,
      a ≠ b ∧ b ≠ c ∧ c ≠ d ∧ d ≠ e ∧ e ≠ a := by
  obtain ⟨b, hbA, hb⟩ := exists_mem_avoiding
    (A := A) (F := {a, c}) (by have := card_pair_le_two a c; omega)
  obtain ⟨d, hdA, hdc⟩ := exists_mem_ne_of_two (by omega : 2 ≤ A.card) c
  obtain ⟨e, heA, he⟩ := exists_mem_avoiding
    (A := A) (F := {d, a}) (by have := card_pair_le_two d a; omega)
  simp only [mem_insert, mem_singleton, not_or] at hb he
  exact ⟨b, hbA, d, hdA, e, heA,
    Ne.symm hb.1, hb.2, hdc.symm, Ne.symm he.1, he.2⟩

/-- Equal singleton deletions of two equicardinal sets force the original
sets to be equal. -/
lemma eq_of_sdiff_singleton_eq_of_card_eq {A B : Finset Color} {q : Color}
    (hcard : A.card = B.card) (hdel : A \ {q} = B \ {q}) : A = B := by
  by_cases hqA : q ∈ A
  · have hqB : q ∈ B := by
      by_contra hqB
      have hca : (A \ {q}).card = A.card - 1 := by
        simpa [sdiff_singleton_eq_erase] using card_erase_of_mem hqA
      have hcb : B \ {q} = B := by simp [sdiff_singleton_eq_erase, hqB]
      have heq : A.card - 1 = B.card := by
        calc
          A.card - 1 = (A \ {q}).card := hca.symm
          _ = (B \ {q}).card := congrArg Finset.card hdel
          _ = B.card := congrArg Finset.card hcb
      have hlt : A.card - 1 < A.card := Nat.sub_one_lt (by
        exact Nat.ne_of_gt (card_pos.mpr ⟨q, hqA⟩))
      exact (ne_of_lt hlt) (heq.trans hcard.symm)
    ext x
    by_cases hx : x = q
    · subst x; simp [hqA, hqB]
    · have := congrArg (fun S : Finset Color ↦ x ∈ S) hdel
      simpa [hx] using this
  · have hqB : q ∉ B := by
      intro hqB
      have hca : A \ {q} = A := by simp [sdiff_singleton_eq_erase, hqA]
      have hcb : (B \ {q}).card = B.card - 1 := by
        simpa [sdiff_singleton_eq_erase] using card_erase_of_mem hqB
      have heq : A.card = B.card - 1 := by
        calc
          A.card = (A \ {q}).card := congrArg Finset.card hca.symm
          _ = (B \ {q}).card := congrArg Finset.card hdel
          _ = B.card - 1 := hcb
      have hlt : B.card - 1 < B.card := Nat.sub_one_lt (by
        exact Nat.ne_of_gt (card_pos.mpr ⟨q, hqB⟩))
      exact (ne_of_lt hlt) (hcard.symm.trans heq).symm
    simpa [sdiff_singleton_eq_erase, hqA, hqB] using hdel

end FiniteChoices

section StructuredColorings

variable {Color : Type*} [DecidableEq Color]

/-- Dependent case analysis on the two-element type without proposition-based
enumeration. -/
def fin2Cases {motive : Fin 2 → Sort*} (x0 : motive 0) (x1 : motive 1) :
    (i : Fin 2) → motive i :=
  Fin.cases x0 (fun i ↦ Fin.cases x1 (fun j ↦ Fin.elim0 j) i)

/-- The five named colours and edge inequalities of a coloured 5-cycle. -/
structure C5Choice (A B C D E : Finset Color) where
  a : Color
  b : Color
  c : Color
  d : Color
  e : Color
  a_mem : a ∈ A
  b_mem : b ∈ B
  c_mem : c ∈ C
  d_mem : d ∈ D
  e_mem : e ∈ E
  ab : a ≠ b
  bc : b ≠ c
  cd : c ≠ d
  de : d ≠ e
  ea : e ≠ a

lemma exists_c5Choice_of_nonconstant {A B C D E : Finset Color}
    (hA : 2 ≤ A.card) (hB : 2 ≤ B.card) (hC : 2 ≤ C.card)
    (hD : 2 ≤ D.card) (hE : 2 ≤ E.card)
    (hne : ¬ (A = B ∧ B = C ∧ C = D ∧ D = E)) :
    Nonempty (C5Choice A B C D E) := by
  obtain ⟨a, ha, b, hb, c, hc, d, hd, e, he, hab, hbc, hcd, hde, hea⟩ :=
    cycle5_nonconstant hA hB hC hD hE hne
  exact ⟨⟨a, b, c, d, e, ha, hb, hc, hd, he, hab, hbc, hcd, hde, hea⟩⟩

lemma exists_common_c5Choice {A : Finset Color} (hA : 3 ≤ A.card)
    {a c : Color} (ha : a ∈ A) (hc : c ∈ A) :
    ∃ C : C5Choice A A A A A, C.a = a ∧ C.c = c := by
  obtain ⟨b, hb, d, hd, e, he, hab, hbc, hcd, hde, hea⟩ :=
    common_cycle5_extension hA ha hc
  exact ⟨⟨a, b, c, d, e, ha, hb, hc, hd, he, hab, hbc, hcd, hde, hea⟩, rfl, rfl⟩

/-- The three named colours and inequalities of a coloured triangle. -/
structure TriangleChoice (A B C : Finset Color) where
  a : Color
  b : Color
  c : Color
  a_mem : a ∈ A
  b_mem : b ∈ B
  c_mem : c ∈ C
  ab : a ≠ b
  bc : b ≠ c
  ca : c ≠ a

lemma exists_triangleChoice_fixed {A B C : Finset Color}
    (hA : 2 ≤ A.card) (hB : 2 ≤ B.card) (hne : A ≠ B)
    {q : Color} (hq : q ∈ C) :
    ∃ T : TriangleChoice A B C, T.c = q := by
  obtain ⟨a, ha, b, hb, hab, haq, hbq⟩ := triangle_extension hA hB hne q
  exact ⟨⟨a, b, q, ha, hb, hq, hab, hbq, haq.symm⟩, rfl⟩

/-- A triangle with lists of size at least two is colourable as soon as the
three lists are not all the same two-set. -/
lemma exists_triangleChoice_nonconstant {A B C : Finset Color}
    (hA : 2 ≤ A.card) (hB : 2 ≤ B.card) (hC : 2 ≤ C.card)
    (hne : ¬ (A = B ∧ B = C)) : Nonempty (TriangleChoice A B C) := by
  by_cases hAB : A = B
  · have hBC : B ≠ C := fun h ↦ hne ⟨hAB, h⟩
    obtain ⟨a, ha⟩ := card_pos.mp (lt_of_lt_of_le (by omega) hA)
    obtain ⟨b, hb, c, hc, hbc, hba, hca⟩ := triangle_extension hB hC hBC a
    exact ⟨⟨a, b, c, ha, hb, hc, hba.symm, hbc, hca⟩⟩
  · obtain ⟨c, hc⟩ := card_pos.mp (lt_of_lt_of_le (by omega) hC)
    obtain ⟨a, ha, b, hb, hab, hac, hbc⟩ := triangle_extension hA hB hAB c
    exact ⟨⟨a, b, c, ha, hb, hc, hab, hbc, hac.symm⟩⟩

/-- A proper list colouring of the nine-vertex gadget `G₂`, stored in the
decomposition used in its proof. -/
structure G2Choice (L : G5Vertex → Finset Color) where
  cycle : C5Choice (L v1) (L u2) (L v3) (L u4) (L u5)
  hub : Color
  hub_mem : hub ∈ L y1
  hub_v1 : hub ≠ cycle.a
  hub_u2 : hub ≠ cycle.b
  hub_v3 : hub ≠ cycle.c
  hub_u4 : hub ≠ cycle.d
  hub_u5 : hub ≠ cycle.e
  triangle : TriangleChoice (L y2) (L y3) (L y4)
  hub_y2 : hub ≠ triangle.a

/-- The colouring data on one seven-vertex `z`-piece, with the colour of
`y₄` supplied by the `G₂` colouring. -/
structure ZPieceChoice (L : G5Vertex → Finset Color) (i : Fin 2)
    (y4color : Color) where
  c0 : Color
  c1 : Color
  c2 : Color
  c3 : Color
  tail : TriangleChoice (L (z i 4)) (L (z i 5)) (L (z i 6))
  c0_mem : c0 ∈ L (z i 0)
  c1_mem : c1 ∈ L (z i 1)
  c2_mem : c2 ∈ L (z i 2)
  c3_mem : c3 ∈ L (z i 3)
  y4_c0 : y4color ≠ c0
  y4_c1 : y4color ≠ c1
  c0_c2 : c0 ≠ c2
  c0_c3 : c0 ≠ c3
  c1_c2 : c1 ≠ c2
  c1_c3 : c1 ≠ c3
  c2_c3 : c2 ≠ c3
  c3_tail : c3 ≠ tail.a

/-- A proper colouring of `G₃`. -/
structure G3Choice (L : G5Vertex → Finset Color) where
  base : G2Choice L
  piece : (i : Fin 2) → ZPieceChoice L i base.triangle.c

/-- A coloured triangle attached to a prescribed outside colour at its first
vertex. -/
structure AttachedTriangleChoice (A B C : Finset Color) (outside : Color) where
  triangle : TriangleChoice A B C
  outside_first : outside ≠ triangle.a

/-- A proper colouring of `G₄`. -/
structure G4Choice (L : G5Vertex → Finset Color) where
  base : G3Choice L
  main : TriangleChoice (L (w 0)) (L (w 1)) (L (w 2))
  z0_main : (base.piece 0).tail.c ≠ main.a
  z1_main : (base.piece 1).tail.c ≠ main.a
  small : (i : Fin 2) →
    AttachedTriangleChoice (L (wt i 0)) (L (wt i 1)) (L (wt i 2)) main.c

/-- A proper colouring of the seven-vertex `G₁`. -/
structure G1Choice (L : G5Vertex → Finset Color) where
  cycle : C5Choice (L v1) (L v2) (L v3) (L v4) (L v5)
  xcolor : Color
  ycolor : Color
  x_mem : xcolor ∈ L x
  y_mem : ycolor ∈ L y
  v1_x : cycle.a ≠ xcolor
  x_y : xcolor ≠ ycolor
  y_v3 : ycolor ≠ cycle.c

/-- The four extra inequalities joining compatible colourings of `G₄` and
`G₁` into a colouring of `G₅`. -/
structure G5Choice (L : G5Vertex → Finset Color) where
  left : G4Choice L
  right : G1Choice L
  agree_v1 : right.cycle.a = left.base.base.cycle.a
  agree_v3 : right.cycle.c = left.base.base.cycle.c
  cross_v2 : (left.small 0).triangle.c ≠ right.cycle.b
  cross_v4 : (left.small 0).triangle.c ≠ right.cycle.d
  cross_x : (left.small 1).triangle.c ≠ right.xcolor
  cross_y : (left.small 1).triangle.c ≠ right.ycolor

/-- An arbitrary assignment having exactly half the cardinality of the DHS
reference list at every vertex. -/
def IsHalfListAssignment (L : G5Vertex → Finset Color) : Prop :=
  ∀ v, (L v).card = halfSize v

/-- The one-boundary relaxed alternative for `G₂`. -/
def G2Flexible (L : G5Vertex → Finset Color) : Prop :=
  (∃ a ∈ L v1, ∃ c ∈ L v3,
      ∀ q ∈ L y4, ∃ C : G2Choice L,
        C.cycle.a = a ∧ C.cycle.c = c ∧ C.triangle.c = q) ∨
  (L v1 = L v3 ∧ ∃ q ∈ L y4,
      ∀ a ∈ L v1, ∀ c ∈ L v3, ∃ C : G2Choice L,
        C.cycle.a = a ∧ C.cycle.c = c ∧ C.triangle.c = q)

/-- DHS Lemma 5, positive half: `G₂` has the required flexible boundary. -/
theorem g2_flexible {L : G5Vertex → Finset Color} (hL : IsHalfListAssignment L) :
    G2Flexible L := by
  have hv1 : (L v1).card = 3 := by rw [hL]; decide
  have hu2 : (L u2).card = 3 := by rw [hL]; decide
  have hv3 : (L v3).card = 3 := by rw [hL]; decide
  have hu4 : (L u4).card = 3 := by rw [hL]; decide
  have hu5 : (L u5).card = 3 := by rw [hL]; decide
  have hy1 : (L y1).card = 4 := by rw [hL]; decide
  have hy2 : (L y2).card = 3 := by rw [hL]; decide
  have hy3 : (L y3).card = 2 := by rw [hL]; decide
  have hy4 : (L y4).card = 3 := by rw [hL]; decide
  by_cases hcycle : L v1 = L u2 ∧ L u2 = L v3 ∧ L v3 = L u4 ∧ L u4 = L u5
  · right
    have hcommon : L v1 = L v3 := hcycle.1.trans hcycle.2.1
    refine ⟨hcommon, ?_⟩
    obtain ⟨hub, hhub, hhubA⟩ := exists_mem_avoiding
      (A := L y1) (F := L v1) (by omega)
    let A2 := L y2 \ {hub}
    have hA2 : 2 ≤ A2.card := by
      have hbound := card_sub_card_le_card_sdiff (L y2) ({hub} : Finset Color)
      simp only [card_singleton, hy2] at hbound
      exact hbound
    have htriNon : ¬ (A2 = L y3 ∧ L y3 = L y4) := by
      rintro ⟨_, h34⟩
      have := congrArg Finset.card h34
      omega
    obtain ⟨tri⟩ := exists_triangleChoice_nonconstant hA2 (by omega) (by omega) htriNon
    refine ⟨tri.c, tri.c_mem, ?_⟩
    intro a ha c hc
    have hcA : c ∈ L v1 := by rw [hcommon]; exact hc
    obtain ⟨cyc, hca, hcc⟩ := exists_common_c5Choice (by omega) ha hcA
    let cyc' : C5Choice (L v1) (L u2) (L v3) (L u4) (L u5) :=
      ⟨cyc.a, cyc.b, cyc.c, cyc.d, cyc.e, cyc.a_mem,
        by rw [← hcycle.1]; exact cyc.b_mem,
        by rw [← hcommon]; exact cyc.c_mem,
        by rw [← hcycle.2.2.1, ← hcommon]; exact cyc.d_mem,
        by rw [← hcycle.2.2.2, ← hcycle.2.2.1, ← hcommon]; exact cyc.e_mem,
        cyc.ab, cyc.bc, cyc.cd, cyc.de, cyc.ea⟩
    have hhubCycle :
        hub ≠ cyc'.a ∧ hub ≠ cyc'.b ∧ hub ≠ cyc'.c ∧
          hub ≠ cyc'.d ∧ hub ≠ cyc'.e := by
      constructor
      · intro h; exact hhubA (h ▸ cyc'.a_mem)
      constructor
      · intro h; exact hhubA (h ▸ cyc.b_mem)
      constructor
      · intro h; exact hhubA (h ▸ cyc.c_mem)
      constructor
      · intro h; exact hhubA (h ▸ cyc.d_mem)
      · intro h; exact hhubA (h ▸ cyc.e_mem)
    have hhubTri : hub ≠ tri.a := by
      intro h
      exact (mem_sdiff.mp tri.a_mem).2 (by simpa [h] using mem_singleton_self hub)
    refine ⟨⟨cyc', hub, hhub, hhubCycle.1, hhubCycle.2.1,
      hhubCycle.2.2.1, hhubCycle.2.2.2.1, hhubCycle.2.2.2.2,
      ⟨tri.a, tri.b, tri.c, (mem_sdiff.mp tri.a_mem).1, tri.b_mem, tri.c_mem,
        tri.ab, tri.bc, tri.ca⟩, hhubTri⟩, ?_⟩
    exact ⟨by simpa [cyc'] using hca, by simpa [cyc'] using hcc, rfl⟩
  · left
    obtain ⟨hub, hhub, hhub2⟩ := exists_mem_avoiding
      (A := L y1) (F := L y2) (by omega)
    let A := L v1 \ {hub}
    let B := L u2 \ {hub}
    let C := L v3 \ {hub}
    let D := L u4 \ {hub}
    let E := L u5 \ {hub}
    have hA : 2 ≤ A.card := by
      have h := card_sub_card_le_card_sdiff (L v1) ({hub} : Finset Color)
      simp only [card_singleton, hv1] at h
      exact h
    have hB : 2 ≤ B.card := by
      have h := card_sub_card_le_card_sdiff (L u2) ({hub} : Finset Color)
      simp only [card_singleton, hu2] at h
      exact h
    have hC : 2 ≤ C.card := by
      have h := card_sub_card_le_card_sdiff (L v3) ({hub} : Finset Color)
      simp only [card_singleton, hv3] at h
      exact h
    have hD : 2 ≤ D.card := by
      have h := card_sub_card_le_card_sdiff (L u4) ({hub} : Finset Color)
      simp only [card_singleton, hu4] at h
      exact h
    have hE : 2 ≤ E.card := by
      have h := card_sub_card_le_card_sdiff (L u5) ({hub} : Finset Color)
      simp only [card_singleton, hu5] at h
      exact h
    have hresNon : ¬ (A = B ∧ B = C ∧ C = D ∧ D = E) := by
      rintro ⟨hAB, hBC, hCD, hDE⟩
      apply hcycle
      have e1 : L v1 = L u2 := eq_of_sdiff_singleton_eq_of_card_eq
        (by omega) (by simpa [A, B] using hAB)
      have e2 : L u2 = L v3 := eq_of_sdiff_singleton_eq_of_card_eq
        (by omega) (by simpa [B, C] using hBC)
      have e3 : L v3 = L u4 := eq_of_sdiff_singleton_eq_of_card_eq
        (by omega) (by simpa [C, D] using hCD)
      have e4 : L u4 = L u5 := eq_of_sdiff_singleton_eq_of_card_eq
        (by omega) (by simpa [D, E] using hDE)
      exact ⟨e1, e2, e3, e4⟩
    obtain ⟨cyc0⟩ := exists_c5Choice_of_nonconstant hA hB hC hD hE hresNon
    let cyc : C5Choice (L v1) (L u2) (L v3) (L u4) (L u5) :=
      ⟨cyc0.a, cyc0.b, cyc0.c, cyc0.d, cyc0.e,
        (mem_sdiff.mp cyc0.a_mem).1, (mem_sdiff.mp cyc0.b_mem).1,
        (mem_sdiff.mp cyc0.c_mem).1, (mem_sdiff.mp cyc0.d_mem).1,
        (mem_sdiff.mp cyc0.e_mem).1,
        cyc0.ab, cyc0.bc, cyc0.cd, cyc0.de, cyc0.ea⟩
    refine ⟨cyc.a, cyc.a_mem, cyc.c, cyc.c_mem, ?_⟩
    intro q hq
    have hy23 : L y2 ≠ L y3 := by
      intro h
      have := congrArg Finset.card h
      omega
    obtain ⟨tri, htri⟩ := exists_triangleChoice_fixed (by omega) (by omega) hy23 hq
    have hhubCycle :
        hub ≠ cyc.a ∧ hub ≠ cyc.b ∧ hub ≠ cyc.c ∧ hub ≠ cyc.d ∧ hub ≠ cyc.e := by
      exact ⟨by change hub ≠ cyc0.a; intro h; exact (mem_sdiff.mp cyc0.a_mem).2 (by simp [h]),
        by change hub ≠ cyc0.b; intro h; exact (mem_sdiff.mp cyc0.b_mem).2 (by simp [h]),
        by change hub ≠ cyc0.c; intro h; exact (mem_sdiff.mp cyc0.c_mem).2 (by simp [h]),
        by change hub ≠ cyc0.d; intro h; exact (mem_sdiff.mp cyc0.d_mem).2 (by simp [h]),
        by change hub ≠ cyc0.e; intro h; exact (mem_sdiff.mp cyc0.e_mem).2 (by simp [h])⟩
    have hhubTri : hub ≠ tri.a := fun h ↦ hhub2 (h ▸ tri.a_mem)
    refine ⟨⟨cyc, hub, hhub, hhubCycle.1, hhubCycle.2.1,
      hhubCycle.2.2.1, hhubCycle.2.2.2.1, hhubCycle.2.2.2.2,
      tri, hhubTri⟩, rfl, rfl, htri⟩

/-- Once the two shared endpoint colours are fixed, the enlarged `G₁` part
of `G₅` is greedily colourable. -/
lemma g1_from_fixed_ends {L : G5Vertex → Finset Color}
    (hL : IsHalfListAssignment L) {a c : Color} (ha : a ∈ L v1) (hc : c ∈ L v3) :
    ∃ R : G1Choice L, R.cycle.a = a ∧ R.cycle.c = c := by
  have hv2 : (L v2).card = 3 := by rw [hL]; decide
  have hv4 : (L v4).card = 3 := by rw [hL]; decide
  have hv5 : (L v5).card = 2 := by rw [hL]; decide
  have hx : (L x).card = 3 := by rw [hL]; decide
  have hy : (L y).card = 2 := by rw [hL]; decide
  obtain ⟨b, hb, hbavoid⟩ := exists_mem_avoiding
    (A := L v2) (F := {a, c}) (by have := card_pair_le_two a c; omega)
  obtain ⟨e, he, heavoid⟩ := exists_mem_avoiding
    (A := L v5) (F := {a}) (by simp [hv5])
  obtain ⟨d, hd, hdavoid⟩ := exists_mem_avoiding
    (A := L v4) (F := {e, c}) (by have := card_pair_le_two e c; omega)
  obtain ⟨yy, hyy, hyyavoid⟩ := exists_mem_avoiding
    (A := L y) (F := {c}) (by simp [hy])
  obtain ⟨xx, hxx, hxxavoid⟩ := exists_mem_avoiding
    (A := L x) (F := {yy, a}) (by have := card_pair_le_two yy a; omega)
  simp only [mem_insert, mem_singleton, not_or] at hbavoid hdavoid hxxavoid
  simp only [mem_singleton, not_false_eq_true] at heavoid hyyavoid
  let cyc : C5Choice (L v1) (L v2) (L v3) (L v4) (L v5) :=
    ⟨a, b, c, d, e, ha, hb, hc, hd, he,
      Ne.symm hbavoid.1, hbavoid.2, Ne.symm hdavoid.2, hdavoid.1, heavoid⟩
  exact ⟨⟨cyc, xx, yy, hxx, hyy, Ne.symm hxxavoid.2, hxxavoid.1,
    hyyavoid⟩, rfl, rfl⟩

/-- When the shared endpoint lists agree, `G₁` can be coloured while
simultaneously avoiding the two terminal colours on all four cross-edges. -/
lemma g1_equal_avoiding {L : G5Vertex → Finset Color}
    (hL : IsHalfListAssignment L) (heq : L v1 = L v3) (d0 d1 : Color) :
    ∃ R : G1Choice L,
      R.cycle.b ≠ d0 ∧ R.cycle.d ≠ d0 ∧ R.xcolor ≠ d1 ∧ R.ycolor ≠ d1 := by
  have hv1 : (L v1).card = 3 := by rw [hL]; decide
  have hv2 : (L v2).card = 3 := by rw [hL]; decide
  have hv3 : (L v3).card = 3 := by rw [hL]; decide
  have hv4 : (L v4).card = 3 := by rw [hL]; decide
  have hv5 : (L v5).card = 2 := by rw [hL]; decide
  have hx : (L x).card = 3 := by rw [hL]; decide
  have hy : (L y).card = 2 := by rw [hL]; decide
  obtain ⟨yy, hyy, hyyd1⟩ := exists_mem_avoiding
    (A := L y) (F := {d1}) (by simp [hy])
  obtain ⟨xx, hxx, hxxavoid⟩ := exists_mem_avoiding
    (A := L x) (F := {d1, yy}) (by have := card_pair_le_two d1 yy; omega)
  let A := L v1 \ {xx}
  let B := L v2 \ {d0}
  let C := L v3 \ {yy}
  let D := L v4 \ {d0}
  let E := L v5
  have hA : 2 ≤ A.card := by
    have h := card_sub_card_le_card_sdiff (L v1) ({xx} : Finset Color)
    simp only [card_singleton, hv1] at h
    exact h
  have hB : 2 ≤ B.card := by
    have h := card_sub_card_le_card_sdiff (L v2) ({d0} : Finset Color)
    simp only [card_singleton, hv2] at h
    exact h
  have hC : 2 ≤ C.card := by
    have h := card_sub_card_le_card_sdiff (L v3) ({yy} : Finset Color)
    simp only [card_singleton, hv3] at h
    exact h
  have hD : 2 ≤ D.card := by
    have h := card_sub_card_le_card_sdiff (L v4) ({d0} : Finset Color)
    simp only [card_singleton, hv4] at h
    exact h
  have hE : 2 ≤ E.card := by simpa [E, hv5]
  have hnon : ¬ (A = B ∧ B = C ∧ C = D ∧ D = E) := by
    rintro ⟨hAB, hBC, hCD, hDE⟩
    have hAE : A = E := hAB.trans (hBC.trans (hCD.trans hDE))
    have hCE : C = E := hCD.trans hDE
    have hAcard : A.card = 2 := by simpa [E, hv5] using congrArg Finset.card hAE
    have hCcard : C.card = 2 := by simpa [E, hv5] using congrArg Finset.card hCE
    have hxxA : xx ∈ L v1 := by
      by_contra hn
      have : A = L v1 := by simp [A, sdiff_singleton_eq_erase, hn]
      rw [this, hv1] at hAcard
      omega
    have hyyA : yy ∈ L v1 := by
      have hyy3 : yy ∈ L v3 := by
        by_contra hn
        have : C = L v3 := by simp [C, sdiff_singleton_eq_erase, hn]
        rw [this, hv3] at hCcard
        omega
      rw [heq]
      exact hyy3
    have hdel : L v1 \ {xx} = L v1 \ {yy} := by
      calc
        L v1 \ {xx} = A := rfl
        _ = C := hAB.trans hBC
        _ = L v3 \ {yy} := rfl
        _ = L v1 \ {yy} := by rw [heq]
    have hxy := card_three_delete_eq_card_two_unique hv1 (by simpa [A] using hAcard)
      (by rfl) (by simpa using hdel.symm)
    have hxxy : xx ≠ yy := by
      intro h
      exact hxxavoid (by simp [h])
    exact hxxy hxy
  obtain ⟨cyc0⟩ := exists_c5Choice_of_nonconstant hA hB hC hD hE hnon
  let cyc : C5Choice (L v1) (L v2) (L v3) (L v4) (L v5) :=
    ⟨cyc0.a, cyc0.b, cyc0.c, cyc0.d, cyc0.e,
      (mem_sdiff.mp cyc0.a_mem).1, (mem_sdiff.mp cyc0.b_mem).1,
      (mem_sdiff.mp cyc0.c_mem).1, (mem_sdiff.mp cyc0.d_mem).1, cyc0.e_mem,
      cyc0.ab, cyc0.bc, cyc0.cd, cyc0.de, cyc0.ea⟩
  have hv1x : cyc.a ≠ xx := by
    change cyc0.a ≠ xx
    intro h; exact (mem_sdiff.mp cyc0.a_mem).2 (by simp [h])
  have hyvc : yy ≠ cyc.c := by
    change yy ≠ cyc0.c
    intro h; exact (mem_sdiff.mp cyc0.c_mem).2 (by simp [h])
  have hbd0 : cyc.b ≠ d0 := by
    change cyc0.b ≠ d0
    intro h; exact (mem_sdiff.mp cyc0.b_mem).2 (by simp [h])
  have hdd0 : cyc.d ≠ d0 := by
    change cyc0.d ≠ d0
    intro h; exact (mem_sdiff.mp cyc0.d_mem).2 (by simp [h])
  have hxxd1 : xx ≠ d1 := by intro h; exact hxxavoid (by simp [h])
  have hyyd1' : yy ≠ d1 := by intro h; exact hyyd1 (by simp [h])
  have hxxy : xx ≠ yy := by intro h; exact hxxavoid (by simp [h])
  exact ⟨⟨cyc, xx, yy, hxx, hyy, hv1x, hxxy, hyvc⟩,
    hbd0, hdd0, hxxd1, hyyd1'⟩

/-- With the colour of `y₄` fixed, a `z`-piece admits a direct greedy
colouring.  This is the construction used in the second relaxed case. -/
lemma z_piece_greedy {L : G5Vertex → Finset Color}
    (hL : IsHalfListAssignment L) (i : Fin 2) {q : Color} (hq : q ∈ L y4) :
    Nonempty (ZPieceChoice L i q) := by
  have h0 : (L (z i 0)).card = 2 := by rw [hL]; fin_cases i <;> decide
  have h1 : (L (z i 1)).card = 2 := by rw [hL]; fin_cases i <;> decide
  have h2 : (L (z i 2)).card = 3 := by rw [hL]; fin_cases i <;> decide
  have h3 : (L (z i 3)).card = 4 := by rw [hL]; fin_cases i <;> decide
  have h4 : (L (z i 4)).card = 3 := by rw [hL]; fin_cases i <;> decide
  have h5 : (L (z i 5)).card = 2 := by rw [hL]; fin_cases i <;> decide
  have h6 : (L (z i 6)).card = 3 := by rw [hL]; fin_cases i <;> decide
  obtain ⟨c0, hc0, hc0q⟩ := exists_mem_avoiding
    (A := L (z i 0)) (F := {q}) (by simp [h0])
  obtain ⟨c1, hc1, hc1q⟩ := exists_mem_avoiding
    (A := L (z i 1)) (F := {q}) (by simp [h1])
  obtain ⟨c2, hc2, hc2bad⟩ := exists_mem_avoiding
    (A := L (z i 2)) (F := {c0, c1}) (by have := card_pair_le_two c0 c1; omega)
  obtain ⟨c3, hc3, hc3bad⟩ := exists_mem_avoiding
    (A := L (z i 3)) (F := {c0, c1, c2})
      (by have := card_triple_le_three c0 c1 c2; omega)
  obtain ⟨a, ha, hac3⟩ := exists_mem_avoiding
    (A := L (z i 4)) (F := {c3}) (by simp [h4])
  obtain ⟨b, hb, hba⟩ := exists_mem_avoiding
    (A := L (z i 5)) (F := {a}) (by simp [h5])
  obtain ⟨c, hc, hcab⟩ := exists_mem_avoiding
    (A := L (z i 6)) (F := {a, b}) (by have := card_pair_le_two a b; omega)
  simp only [mem_insert, mem_singleton, not_or] at hc2bad hc3bad hcab
  simp only [mem_singleton] at hc0q hc1q hac3 hba
  let tail : TriangleChoice (L (z i 4)) (L (z i 5)) (L (z i 6)) :=
    ⟨a, b, c, ha, hb, hc, Ne.symm hba, Ne.symm hcab.2, hcab.1⟩
  exact ⟨⟨c0, c1, c2, c3, tail, hc0, hc1, hc2, hc3,
    Ne.symm hc0q, Ne.symm hc1q,
    Ne.symm hc2bad.1, Ne.symm hc3bad.1,
    Ne.symm hc2bad.2, Ne.symm hc3bad.2.1,
    Ne.symm hc3bad.2.2, Ne.symm hac3⟩⟩

/-- In the first relaxed case, a `z`-piece has one guard colour at `y₄`;
every other `y₄` colour permits an arbitrary prescribed terminal colour. -/
lemma z_piece_free_terminal {L : G5Vertex → Finset Color}
    (hL : IsHalfListAssignment L) (i : Fin 2) :
    ∃ guard : Color, ∀ q ∈ L y4, q ≠ guard →
      ∀ r ∈ L (z i 6), ∃ Z : ZPieceChoice L i q, Z.tail.c = r := by
  have h0 : (L (z i 0)).card = 2 := by rw [hL]; fin_cases i <;> decide
  have h1 : (L (z i 1)).card = 2 := by rw [hL]; fin_cases i <;> decide
  have h2 : (L (z i 2)).card = 3 := by rw [hL]; fin_cases i <;> decide
  have h3 : (L (z i 3)).card = 4 := by rw [hL]; fin_cases i <;> decide
  have h4 : (L (z i 4)).card = 3 := by rw [hL]; fin_cases i <;> decide
  have h5 : (L (z i 5)).card = 2 := by rw [hL]; fin_cases i <;> decide
  have complete (q c0 c1 : Color) (hq : q ∈ L y4)
      (hc0 : c0 ∈ L (z i 0)) (hc1 : c1 ∈ L (z i 1))
      (hq0 : q ≠ c0) (hq1 : q ≠ c1)
      (hspecial : c0 = c1 ∨ c0 ∉ L (z i 2) ∨ c1 ∉ L (z i 2)) :
      ∀ r ∈ L (z i 6), ∃ Z : ZPieceChoice L i q, Z.tail.c = r := by
    let X := L (z i 3) \ {c0, c1}
    have hX : 2 ≤ X.card := by
      have hb := card_sub_card_le_card_sdiff (L (z i 3)) ({c0, c1} : Finset Color)
      have hp := card_pair_le_two c0 c1
      simp only [h3] at hb
      exact le_trans (by omega : 2 ≤ 4 - ({c0, c1} : Finset Color).card) hb
    obtain ⟨c3, hc3X, hgood⟩ := exists_delete_ne_of_two_le_card h4 h5 hX
    have hc3 : c3 ∈ L (z i 3) := (mem_sdiff.mp hc3X).1
    have hc3bad := (mem_sdiff.mp hc3X).2
    simp only [mem_insert, mem_singleton, not_or] at hc3bad
    obtain ⟨c2, hc2, hc20, hc21, hc23⟩ :
        ∃ c2 ∈ L (z i 2), c2 ≠ c0 ∧ c2 ≠ c1 ∧ c2 ≠ c3 := by
      rcases hspecial with h01 | h0out | h1out
      · obtain ⟨c2, hc2, hbad⟩ := exists_mem_avoiding
          (A := L (z i 2)) (F := {c0, c3})
            (by have := card_pair_le_two c0 c3; omega)
        simp only [mem_insert, mem_singleton, not_or] at hbad
        exact ⟨c2, hc2, hbad.1, by simpa [h01] using hbad.1, hbad.2⟩
      · obtain ⟨c2, hc2, hbad⟩ := exists_mem_avoiding
          (A := L (z i 2)) (F := {c1, c3})
            (by have := card_pair_le_two c1 c3; omega)
        simp only [mem_insert, mem_singleton, not_or] at hbad
        have hc20 : c2 ≠ c0 := fun h ↦ h0out (h ▸ hc2)
        exact ⟨c2, hc2, hc20, hbad.1, hbad.2⟩
      · obtain ⟨c2, hc2, hbad⟩ := exists_mem_avoiding
          (A := L (z i 2)) (F := {c0, c3})
            (by have := card_pair_le_two c0 c3; omega)
        simp only [mem_insert, mem_singleton, not_or] at hbad
        have hc21 : c2 ≠ c1 := fun h ↦ h1out (h ▸ hc2)
        exact ⟨c2, hc2, hbad.1, hc21, hbad.2⟩
    intro r hr
    let A4 := L (z i 4) \ {c3}
    have hA4 : 2 ≤ A4.card := by
      have hb := card_sub_card_le_card_sdiff (L (z i 4)) ({c3} : Finset Color)
      simp only [card_singleton, h4] at hb
      exact hb
    obtain ⟨tri0, htri⟩ := exists_triangleChoice_fixed hA4 (by omega) hgood hr
    let tail : TriangleChoice (L (z i 4)) (L (z i 5)) (L (z i 6)) :=
      ⟨tri0.a, tri0.b, tri0.c, (mem_sdiff.mp tri0.a_mem).1,
        tri0.b_mem, tri0.c_mem, tri0.ab, tri0.bc, tri0.ca⟩
    have hc3tail : c3 ≠ tail.a := by
      change c3 ≠ tri0.a
      intro h
      exact (mem_sdiff.mp tri0.a_mem).2 (by simp [h])
    refine ⟨⟨c0, c1, c2, c3, tail, hc0, hc1, hc2, hc3,
      hq0, hq1, Ne.symm hc20, Ne.symm hc3bad.1,
      Ne.symm hc21, Ne.symm hc3bad.2, hc23, hc3tail⟩, ?_⟩
    simpa [tail] using htri
  by_cases hinter : (L (z i 0) ∩ L (z i 1)).Nonempty
  · obtain ⟨guard, hguard⟩ := hinter
    obtain ⟨hg0, hg1⟩ := mem_inter.mp hguard
    refine ⟨guard, ?_⟩
    intro q hq hqg
    exact complete q guard guard hq hg0 hg1 hqg hqg (Or.inl rfl)
  · have hdis : Disjoint (L (z i 0)) (L (z i 1)) := by
      rw [Finset.disjoint_iff_inter_eq_empty]
      exact not_nonempty_iff_eq_empty.mp hinter
    have hunion : (L (z i 0) ∪ L (z i 1)).card = 4 := by
      rw [card_union_of_disjoint hdis, h0, h1]
    obtain ⟨guard, hgunion, hg2⟩ := exists_mem_avoiding
      (A := L (z i 0) ∪ L (z i 1)) (F := L (z i 2)) (by omega)
    refine ⟨guard, ?_⟩
    intro q hq hqg
    rcases mem_union.mp hgunion with hg0 | hg1
    · obtain ⟨c1, hc1, hc1q⟩ := exists_mem_avoiding
        (A := L (z i 1)) (F := {q}) (by simp [h1])
      simp only [mem_singleton] at hc1q
      exact complete q guard c1 hq hg0 hc1 hqg (Ne.symm hc1q) (Or.inr (Or.inl hg2))
    · obtain ⟨c0, hc0, hc0q⟩ := exists_mem_avoiding
        (A := L (z i 0)) (F := {q}) (by simp [h0])
      simp only [mem_singleton] at hc0q
      exact complete q c0 guard hq hc0 hg1 (Ne.symm hc0q) hqg (Or.inr (Or.inr hg2))

/-- Choose the colour on `w₂` so that both attached triangles remain freely
extendible at their terminal vertices. -/
lemma small_triangles_free_terminal {L : G5Vertex → Finset Color}
    (hL : IsHalfListAssignment L) :
    ∃ r ∈ L (w 2), ∀ (i : Fin 2) (e : Color), e ∈ L (wt i 2) →
      ∃ S : AttachedTriangleChoice (L (wt i 0)) (L (wt i 1)) (L (wt i 2)) r,
        S.triangle.c = e := by
  have hw2 : (L (w 2)).card = 3 := by rw [hL]; decide
  have hi0 (i : Fin 2) : (L (wt i 0)).card = 3 := by rw [hL]; fin_cases i <;> decide
  have hi1 (i : Fin 2) : (L (wt i 1)).card = 2 := by rw [hL]; fin_cases i <;> decide
  obtain ⟨r, hr, hgood0, hgood1⟩ :=
    exists_delete_ne_delete_ne_of_three_le_card
      (hi0 0) (hi1 0) (hi0 1) (hi1 1) (by omega : 3 ≤ (L (w 2)).card)
  refine ⟨r, hr, ?_⟩
  intro i e he
  have hgood : L (wt i 0) \ {r} ≠ L (wt i 1) := by
    fin_cases i
    · exact hgood0
    · exact hgood1
  have hres : 2 ≤ (L (wt i 0) \ {r}).card := by
    have hb := card_sub_card_le_card_sdiff (L (wt i 0)) ({r} : Finset Color)
    simp only [card_singleton, hi0] at hb
    exact hb
  obtain ⟨T0, hT⟩ := exists_triangleChoice_fixed hres (by rw [hi1]) hgood he
  let T : TriangleChoice (L (wt i 0)) (L (wt i 1)) (L (wt i 2)) :=
    ⟨T0.a, T0.b, T0.c, (mem_sdiff.mp T0.a_mem).1, T0.b_mem, T0.c_mem,
      T0.ab, T0.bc, T0.ca⟩
  have hrT : r ≠ T.a := by
    change r ≠ T0.a
    intro h
    exact (mem_sdiff.mp T0.a_mem).2 (by simp [h])
  exact ⟨⟨T, hrT⟩, by simpa [T] using hT⟩

/-- With the `w₂` colour fixed, choose both incoming terminal colours and
complete the main `w`-triangle. -/
lemma main_triangle_free_sources {L : G5Vertex → Finset Color}
    (hL : IsHalfListAssignment L) {r : Color} (hr : r ∈ L (w 2)) :
    ∃ d0 ∈ L (z 0 6), ∃ d1 ∈ L (z 1 6),
      ∃ M : TriangleChoice (L (w 0)) (L (w 1)) (L (w 2)),
        M.c = r ∧ d0 ≠ M.a ∧ d1 ≠ M.a := by
  have hw0 : (L (w 0)).card = 3 := by rw [hL]; decide
  have hw1 : (L (w 1)).card = 2 := by rw [hL]; decide
  have hz0 : (L (z 0 6)).card = 3 := by rw [hL]; decide
  have hz1 : (L (z 1 6)).card = 3 := by rw [hL]; decide
  obtain ⟨d0, hd0, hgood0⟩ := exists_delete_ne_of_two_le_card
    hw0 hw1 (by omega : 2 ≤ (L (z 0 6)).card)
  by_cases hd0w : d0 ∈ L (w 0)
  · have hres0 : (L (w 0) \ {d0}).card = 2 := by
      simpa [sdiff_singleton_eq_erase, hw0] using card_erase_of_mem hd0w
    obtain ⟨d1, hd1, hd1out⟩ := exists_mem_avoiding
      (A := L (z 1 6)) (F := L (w 0) \ {d0}) (by omega)
    have hfinal : L (w 0) \ {d0, d1} = L (w 0) \ {d0} := by
      ext x
      simp only [mem_sdiff, mem_insert, mem_singleton, not_or]
      constructor
      · rintro ⟨hx, hxd0, _⟩; exact ⟨hx, by simp [hxd0]⟩
      · rintro ⟨hx, hxnot⟩
        have hxd0 : x ≠ d0 := by simpa using hxnot
        have hxd1 : x ≠ d1 := by
          intro h
          apply hd1out
          subst x
          exact mem_sdiff.mpr ⟨hx, by simp [hxd0]⟩
        exact ⟨hx, hxd0, hxd1⟩
    have hres : 2 ≤ (L (w 0) \ {d0, d1}).card := by rw [hfinal, hres0]
    have hne : L (w 0) \ {d0, d1} ≠ L (w 1) := by simpa [hfinal] using hgood0
    obtain ⟨M0, hM⟩ := exists_triangleChoice_fixed hres (by omega) hne hr
    let M : TriangleChoice (L (w 0)) (L (w 1)) (L (w 2)) :=
      ⟨M0.a, M0.b, M0.c, (mem_sdiff.mp M0.a_mem).1,
        M0.b_mem, M0.c_mem, M0.ab, M0.bc, M0.ca⟩
    have hd0M : d0 ≠ M.a := by
      change d0 ≠ M0.a
      intro h; exact (mem_sdiff.mp M0.a_mem).2 (by simp [h])
    have hd1M : d1 ≠ M.a := by
      change d1 ≠ M0.a
      intro h; exact (mem_sdiff.mp M0.a_mem).2 (by simp [h])
    exact ⟨d0, hd0, d1, hd1, M, by simpa [M] using hM, hd0M, hd1M⟩
  · obtain ⟨d1, hd1, hgood1⟩ := exists_delete_ne_of_two_le_card
      hw0 hw1 (by omega : 2 ≤ (L (z 1 6)).card)
    have hfinal : L (w 0) \ {d0, d1} = L (w 0) \ {d1} := by
      ext x
      simp only [mem_sdiff, mem_insert, mem_singleton, not_or]
      constructor
      · rintro ⟨hx, _, hxd1⟩; exact ⟨hx, by simp [hxd1]⟩
      · rintro ⟨hx, hxnot⟩
        have hxd1 : x ≠ d1 := by simpa using hxnot
        have hxd0 : x ≠ d0 := fun h ↦ hd0w (h ▸ hx)
        exact ⟨hx, hxd0, hxd1⟩
    have hres : 2 ≤ (L (w 0) \ {d0, d1}).card := by
      rw [hfinal]
      have hb := card_sub_card_le_card_sdiff (L (w 0)) ({d1} : Finset Color)
      simp only [card_singleton, hw0] at hb
      exact hb
    have hne : L (w 0) \ {d0, d1} ≠ L (w 1) := by simpa [hfinal] using hgood1
    obtain ⟨M0, hM⟩ := exists_triangleChoice_fixed hres (by omega) hne hr
    let M : TriangleChoice (L (w 0)) (L (w 1)) (L (w 2)) :=
      ⟨M0.a, M0.b, M0.c, (mem_sdiff.mp M0.a_mem).1,
        M0.b_mem, M0.c_mem, M0.ab, M0.bc, M0.ca⟩
    have hd0M : d0 ≠ M.a := by
      change d0 ≠ M0.a
      intro h; exact (mem_sdiff.mp M0.a_mem).2 (by simp [h])
    have hd1M : d1 ≠ M.a := by
      change d1 ≠ M0.a
      intro h; exact (mem_sdiff.mp M0.a_mem).2 (by simp [h])
    exact ⟨d0, hd0, d1, hd1, M, by simpa [M] using hM, hd0M, hd1M⟩

/-- Greedily colour the three `w`-triangles after the two `z`-pieces have
already been coloured. -/
lemma g4_addition_greedy {L : G5Vertex → Finset Color}
    (hL : IsHalfListAssignment L) {q : Color}
    (Z : (i : Fin 2) → ZPieceChoice L i q) :
    ∃ M : TriangleChoice (L (w 0)) (L (w 1)) (L (w 2)),
      (Z 0).tail.c ≠ M.a ∧ (Z 1).tail.c ≠ M.a ∧
      ∃ S : (i : Fin 2) →
        AttachedTriangleChoice (L (wt i 0)) (L (wt i 1)) (L (wt i 2)) M.c,
        True := by
  have hw0 : (L (w 0)).card = 3 := by rw [hL]; decide
  have hw1 : (L (w 1)).card = 2 := by rw [hL]; decide
  have hw2 : (L (w 2)).card = 3 := by rw [hL]; decide
  obtain ⟨a, ha, habad⟩ := exists_mem_avoiding
    (A := L (w 0)) (F := {(Z 0).tail.c, (Z 1).tail.c})
      (by have := card_pair_le_two (Z 0).tail.c (Z 1).tail.c; omega)
  obtain ⟨b, hb, hba⟩ := exists_mem_avoiding
    (A := L (w 1)) (F := {a}) (by simp [hw1])
  obtain ⟨c, hc, hcab⟩ := exists_mem_avoiding
    (A := L (w 2)) (F := {a, b}) (by have := card_pair_le_two a b; omega)
  simp only [mem_insert, mem_singleton, not_or] at habad hcab
  simp only [mem_singleton] at hba
  let M : TriangleChoice (L (w 0)) (L (w 1)) (L (w 2)) :=
    ⟨a, b, c, ha, hb, hc, Ne.symm hba, Ne.symm hcab.2, hcab.1⟩
  have hsmall : ∀ i : Fin 2,
      ∃ T : AttachedTriangleChoice (L (wt i 0)) (L (wt i 1)) (L (wt i 2)) c,
        True := by
    intro i
    have hi0 : (L (wt i 0)).card = 3 := by rw [hL]; fin_cases i <;> decide
    have hi1 : (L (wt i 1)).card = 2 := by rw [hL]; fin_cases i <;> decide
    have hi2 : (L (wt i 2)).card = 3 := by rw [hL]; fin_cases i <;> decide
    obtain ⟨a0, ha0, ha0c⟩ := exists_mem_avoiding
      (A := L (wt i 0)) (F := {c}) (by simp [hi0])
    obtain ⟨b0, hb0, hb0a⟩ := exists_mem_avoiding
      (A := L (wt i 1)) (F := {a0}) (by simp [hi1])
    obtain ⟨c0, hc0, hc0ab⟩ := exists_mem_avoiding
      (A := L (wt i 2)) (F := {a0, b0})
        (by have := card_pair_le_two a0 b0; omega)
    simp only [mem_singleton] at ha0c hb0a
    simp only [mem_insert, mem_singleton, not_or] at hc0ab
    let T : TriangleChoice (L (wt i 0)) (L (wt i 1)) (L (wt i 2)) :=
      ⟨a0, b0, c0, ha0, hb0, hc0, Ne.symm hb0a, Ne.symm hc0ab.2, hc0ab.1⟩
    exact ⟨⟨T, Ne.symm ha0c⟩, trivial⟩
  choose S hS using hsmall
  refine ⟨M, ?_, ?_, ⟨fun i ↦ by simpa [M] using S i, trivial⟩⟩
  · change (Z 0).tail.c ≠ a
    exact Ne.symm habad.1
  · change (Z 1).tail.c ≠ a
    exact Ne.symm habad.2

/-- The vertex-colouring function represented by a structured `G₅` witness. -/
def G5Choice.color {L : G5Vertex → Finset Color} (C : G5Choice L) :
    G5Vertex → Color
  | .v1 => C.left.base.base.cycle.a
  | .u2 => C.left.base.base.cycle.b
  | .v3 => C.left.base.base.cycle.c
  | .u4 => C.left.base.base.cycle.d
  | .u5 => C.left.base.base.cycle.e
  | .y1 => C.left.base.base.hub
  | .y2 => C.left.base.base.triangle.a
  | .y3 => C.left.base.base.triangle.b
  | .y4 => C.left.base.base.triangle.c
  | .z i j =>
      if j = 0 then (C.left.base.piece i).c0
      else if j = 1 then (C.left.base.piece i).c1
      else if j = 2 then (C.left.base.piece i).c2
      else if j = 3 then (C.left.base.piece i).c3
      else if j = 4 then (C.left.base.piece i).tail.a
      else if j = 5 then (C.left.base.piece i).tail.b
      else (C.left.base.piece i).tail.c
  | .w j =>
      if j = 0 then C.left.main.a
      else if j = 1 then C.left.main.b
      else C.left.main.c
  | .wt i j =>
      if j = 0 then (C.left.small i).triangle.a
      else if j = 1 then (C.left.small i).triangle.b
      else (C.left.small i).triangle.c
  | .v2 => C.right.cycle.b
  | .v4 => C.right.cycle.d
  | .v5 => C.right.cycle.e
  | .x => C.right.xcolor
  | .y => C.right.ycolor

lemma G5Choice.color_mem {L : G5Vertex → Finset Color} (C : G5Choice L) :
    ∀ v, C.color v ∈ L v := by
  intro v
  cases v with
  | v1 => exact C.left.base.base.cycle.a_mem
  | u2 => exact C.left.base.base.cycle.b_mem
  | v3 => exact C.left.base.base.cycle.c_mem
  | u4 => exact C.left.base.base.cycle.d_mem
  | u5 => exact C.left.base.base.cycle.e_mem
  | y1 => exact C.left.base.base.hub_mem
  | y2 => exact C.left.base.base.triangle.a_mem
  | y3 => exact C.left.base.base.triangle.b_mem
  | y4 => exact C.left.base.base.triangle.c_mem
  | z i j =>
      fin_cases j <;> simp [G5Choice.color]
      · exact (C.left.base.piece i).c0_mem
      · exact (C.left.base.piece i).c1_mem
      · exact (C.left.base.piece i).c2_mem
      · exact (C.left.base.piece i).c3_mem
      · exact (C.left.base.piece i).tail.a_mem
      · exact (C.left.base.piece i).tail.b_mem
      · exact (C.left.base.piece i).tail.c_mem
  | w j =>
      fin_cases j <;> simp [G5Choice.color]
      · exact C.left.main.a_mem
      · exact C.left.main.b_mem
      · exact C.left.main.c_mem
  | wt i j =>
      fin_cases j <;> simp [G5Choice.color]
      · exact (C.left.small i).triangle.a_mem
      · exact (C.left.small i).triangle.b_mem
      · exact (C.left.small i).triangle.c_mem
  | v2 => exact C.right.cycle.b_mem
  | v4 => exact C.right.cycle.d_mem
  | v5 => exact C.right.cycle.e_mem
  | x => exact C.right.x_mem
  | y => exact C.right.y_mem

lemma G5Choice.color_ne_of_adj {L : G5Vertex → Finset Color} (C : G5Choice L) :
    ∀ ⦃u v⦄, g5Graph.Adj u v → C.color u ≠ C.color v := by
  intro u v huv
  rw [g5Graph_adj_iff] at huv
  have hneq : ∀ e ∈ g5Edges,
      Sym2.lift ⟨fun a b : G5Vertex ↦ C.color a ≠ C.color b,
        fun _ _ ↦ propext ne_comm⟩ e := by
    intro e he
    simp only [g5Edges, g4Edges, g3Edges, g2Edges, zPieceEdges,
      wTriangleEdges, wtTriangleEdges, g4BridgeEdges, g1Edges, crossEdges,
      mem_union, mem_insert, mem_singleton] at he
    simp only [or_assoc] at he
    rcases he with he | he | he | he | he | he | he | he | he | he | he | he |
      he | he | he | he | he | he | he | he | he | he | he | he | he | he |
      he | he | he | he | he | he | he | he | he | he | he | he | he | he |
      he | he | he | he | he | he | he | he | he | he | he | he | he | he |
      he | he | he | he | he | he | he <;> subst e <;>
      simp only [Sym2.lift_mk, G5Choice.color]
    all_goals first
      | exact C.left.base.base.cycle.ab
      | exact C.left.base.base.cycle.bc
      | exact C.left.base.base.cycle.cd
      | exact C.left.base.base.cycle.de
      | exact C.left.base.base.cycle.ea
      | exact C.left.base.base.hub_v1
      | exact C.left.base.base.hub_u2
      | exact C.left.base.base.hub_v3
      | exact C.left.base.base.hub_u4
      | exact C.left.base.base.hub_u5
      | exact C.left.base.base.triangle.ab
      | exact C.left.base.base.triangle.bc
      | exact C.left.base.base.triangle.ca
      | exact C.left.base.base.hub_y2
      | exact (C.left.base.piece 0).y4_c0
      | exact (C.left.base.piece 0).y4_c1
      | exact (C.left.base.piece 0).c0_c2
      | exact (C.left.base.piece 0).c0_c3
      | exact (C.left.base.piece 0).c1_c2
      | exact (C.left.base.piece 0).c1_c3
      | exact (C.left.base.piece 0).c2_c3
      | exact (C.left.base.piece 0).tail.ab
      | exact (C.left.base.piece 0).tail.bc
      | exact (C.left.base.piece 0).tail.ca
      | exact (C.left.base.piece 0).c3_tail
      | exact (C.left.base.piece 1).y4_c0
      | exact (C.left.base.piece 1).y4_c1
      | exact (C.left.base.piece 1).c0_c2
      | exact (C.left.base.piece 1).c0_c3
      | exact (C.left.base.piece 1).c1_c2
      | exact (C.left.base.piece 1).c1_c3
      | exact (C.left.base.piece 1).c2_c3
      | exact (C.left.base.piece 1).tail.ab
      | exact (C.left.base.piece 1).tail.bc
      | exact (C.left.base.piece 1).tail.ca
      | exact (C.left.base.piece 1).c3_tail
      | exact C.left.main.ab
      | exact C.left.main.bc
      | exact C.left.main.ca
      | exact (C.left.small 0).triangle.ab
      | exact (C.left.small 0).triangle.bc
      | exact (C.left.small 0).triangle.ca
      | exact (C.left.small 0).outside_first
      | exact (C.left.small 1).triangle.ab
      | exact (C.left.small 1).triangle.bc
      | exact (C.left.small 1).triangle.ca
      | exact (C.left.small 1).outside_first
      | exact C.left.z0_main
      | exact C.left.z1_main
      | exact C.right.cycle.de
      | exact C.right.x_y
      | exact C.cross_v2
      | exact C.cross_v4
      | exact C.cross_x
      | exact C.cross_y
      | exact fun h ↦ C.right.cycle.ab (C.agree_v1.trans h)
      | exact fun h ↦ C.right.cycle.bc (h.trans C.agree_v3.symm)
      | exact fun h ↦ C.right.cycle.cd (C.agree_v3.trans h)
      | exact fun h ↦ C.right.cycle.ea (h.trans C.agree_v1.symm)
      | exact fun h ↦ C.right.v1_x (C.agree_v1.trans h)
      | exact fun h ↦ C.right.y_v3 (h.trans C.agree_v3.symm)
  exact hneq _ huv

/-- A structured `G₅` witness is an ordinary list colouring of the explicit
graph. -/
lemma G5Choice.isLColoring {L : G5Vertex → Finset Color} (C : G5Choice L) :
    IsLColoring g5Graph L C.color :=
  ⟨C.color_ne_of_adj, C.color_mem⟩

/-- The full DHS positive construction, packaged as a structured colouring
witness. -/
theorem exists_g5Choice {L : G5Vertex → Finset Color}
    (hL : IsHalfListAssignment L) : Nonempty (G5Choice L) := by
  classical
  rcases g2_flexible hL with hfixed | hequal
  · rcases hfixed with ⟨a, ha, c, hc, hbase⟩
    obtain ⟨R, hRa, hRc⟩ := g1_from_fixed_ends hL ha hc
    have ht0 : (L (wt 0 2)).card = 3 := by rw [hL]; decide
    have ht1 : (L (wt 1 2)).card = 3 := by rw [hL]; decide
    obtain ⟨e0, he0, he0bad⟩ := exists_mem_avoiding
      (A := L (wt 0 2)) (F := {R.cycle.b, R.cycle.d})
        (by have := card_pair_le_two R.cycle.b R.cycle.d; omega)
    obtain ⟨e1, he1, he1bad⟩ := exists_mem_avoiding
      (A := L (wt 1 2)) (F := {R.xcolor, R.ycolor})
        (by have := card_pair_le_two R.xcolor R.ycolor; omega)
    simp only [mem_insert, mem_singleton, not_or] at he0bad he1bad
    obtain ⟨r, hr, hsmall⟩ := small_triangles_free_terminal hL
    obtain ⟨S0, hS0⟩ := hsmall 0 e0 he0
    obtain ⟨S1, hS1⟩ := hsmall 1 e1 he1
    obtain ⟨d0, hd0, d1, hd1, M, hMc, hd0M, hd1M⟩ :=
      main_triangle_free_sources hL hr
    subst r
    obtain ⟨guard0, hpiece0⟩ := z_piece_free_terminal hL 0
    obtain ⟨guard1, hpiece1⟩ := z_piece_free_terminal hL 1
    have hy4 : (L y4).card = 3 := by rw [hL]; decide
    obtain ⟨q, hq, hqbad⟩ := exists_mem_avoiding
      (A := L y4) (F := {guard0, guard1})
        (by have := card_pair_le_two guard0 guard1; omega)
    simp only [mem_insert, mem_singleton, not_or] at hqbad
    obtain ⟨B, hBa, hBc, hBq⟩ := hbase q hq
    subst q
    obtain ⟨Z0, hZ0⟩ := hpiece0 B.triangle.c hq hqbad.1 d0 hd0
    obtain ⟨Z1, hZ1⟩ := hpiece1 B.triangle.c hq hqbad.2 d1 hd1
    let Z : (i : Fin 2) → ZPieceChoice L i B.triangle.c :=
      Fin.cons Z0 (Fin.cons Z1 (fun i ↦ nomatch i))
    have hZ0' : (Z 0).tail.c = d0 := by
      simpa [Z] using hZ0
    have hZ1' : (Z 1).tail.c = d1 := by
      simpa [Z] using hZ1
    let S : (i : Fin 2) →
        AttachedTriangleChoice (L (wt i 0)) (L (wt i 1)) (L (wt i 2)) M.c :=
      Fin.cons S0 (Fin.cons S1 (fun i ↦ nomatch i))
    have hS0' : (S 0).triangle.c = e0 := by
      simpa [S] using hS0
    have hS1' : (S 1).triangle.c = e1 := by
      simpa [S] using hS1
    let G3 : G3Choice L := ⟨B, Z⟩
    have hz0M : (G3.piece 0).tail.c ≠ M.a := by
      change (Z 0).tail.c ≠ M.a
      rw [hZ0']
      exact hd0M
    have hz1M : (G3.piece 1).tail.c ≠ M.a := by
      change (Z 1).tail.c ≠ M.a
      rw [hZ1']
      exact hd1M
    let G4 : G4Choice L := ⟨G3, M, hz0M, hz1M, S⟩
    have hagree1 : R.cycle.a = G4.base.base.cycle.a := by
      change R.cycle.a = B.cycle.a
      exact hRa.trans hBa.symm
    have hagree3 : R.cycle.c = G4.base.base.cycle.c := by
      change R.cycle.c = B.cycle.c
      exact hRc.trans hBc.symm
    have hcross0 : (G4.small 0).triangle.c ≠ R.cycle.b := by
      change (S 0).triangle.c ≠ R.cycle.b
      rw [hS0']
      exact he0bad.1
    have hcross1 : (G4.small 0).triangle.c ≠ R.cycle.d := by
      change (S 0).triangle.c ≠ R.cycle.d
      rw [hS0']
      exact he0bad.2
    have hcrossx : (G4.small 1).triangle.c ≠ R.xcolor := by
      change (S 1).triangle.c ≠ R.xcolor
      rw [hS1']
      exact he1bad.1
    have hcrossy : (G4.small 1).triangle.c ≠ R.ycolor := by
      change (S 1).triangle.c ≠ R.ycolor
      rw [hS1']
      exact he1bad.2
    exact ⟨⟨G4, R, hagree1, hagree3, hcross0, hcross1, hcrossx, hcrossy⟩⟩
  · rcases hequal with ⟨heq, q, hq, hbase⟩
    obtain ⟨Z0⟩ := z_piece_greedy hL 0 hq
    obtain ⟨Z1⟩ := z_piece_greedy hL 1 hq
    let Zq : (i : Fin 2) → ZPieceChoice L i q :=
      Fin.cons Z0 (Fin.cons Z1 (fun i ↦ nomatch i))
    obtain ⟨M, hz0M, hz1M, S, _⟩ := g4_addition_greedy hL Zq
    obtain ⟨R, hRb, hRd, hRx, hRy⟩ :=
      g1_equal_avoiding hL heq (S 0).triangle.c (S 1).triangle.c
    obtain ⟨B, hBa, hBc, hBq⟩ :=
      hbase R.cycle.a R.cycle.a_mem R.cycle.c R.cycle.c_mem
    subst q
    let G3 : G3Choice L := ⟨B, Zq⟩
    have hz0M' : (G3.piece 0).tail.c ≠ M.a := by
      exact hz0M
    have hz1M' : (G3.piece 1).tail.c ≠ M.a := by
      exact hz1M
    let G4 : G4Choice L := ⟨G3, M, hz0M', hz1M', S⟩
    have hagree1 : R.cycle.a = G4.base.base.cycle.a := by
      change R.cycle.a = B.cycle.a
      exact hBa.symm
    have hagree3 : R.cycle.c = G4.base.base.cycle.c := by
      change R.cycle.c = B.cycle.c
      exact hBc.symm
    exact ⟨⟨G4, R, hagree1, hagree3, hRb.symm, hRd.symm, hRx.symm, hRy.symm⟩⟩

/-- Every half-list assignment on the decisive DHS gadget is ordinarily
list-colourable. -/
theorem g5_half_list_colorable (L : G5Vertex → Finset Color)
    (hL : ∀ v, (L v).card = halfSize v) : HasLColoring g5Graph L := by
  obtain ⟨C⟩ := exists_g5Choice (L := L) hL
  exact ⟨C.color, C.isLColoring⟩

end StructuredColorings

end Erdos632
