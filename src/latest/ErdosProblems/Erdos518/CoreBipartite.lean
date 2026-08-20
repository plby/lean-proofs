/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos518.Alternating
import ErdosProblems.Erdos518.Cover

/-!
# The complete-core bipartite path-cover lemma

This file proves the finite lemma used as Lemma 2.4 in the path-cover argument.  The graph
need not be bipartite away from the two displayed parts: only its edges between `X` and `Y`
are used.  Vertices in `leftCore G X Y` see all of `Y`, while vertices in
`rightCore G X Y` see all of `X`.

The conclusion deliberately permits different paths in the cover to meet.  That is the
notion needed for Erdős Problem 518 and is what makes it possible to reuse separator
vertices from `Y` in the several alternating paths.
-/

open scoped SimpleGraph

namespace Erdos518

universe u

variable {V : Type u}

/-- Vertices of `X` adjacent to every vertex of `Y`. -/
noncomputable def leftCore [DecidableEq V] (G : SimpleGraph V) (X Y : Finset V) : Finset V :=
  by
    classical
    exact X.filter fun x ↦ ∀ y ∈ Y, G.Adj x y

/-- Vertices of `X` which are not in the complete left core. -/
noncomputable def leftExceptional [DecidableEq V] (G : SimpleGraph V) (X Y : Finset V) : Finset V :=
  X \ leftCore G X Y

/-- Vertices of `Y` adjacent to every vertex of `X`. -/
noncomputable def rightCore [DecidableEq V] (G : SimpleGraph V) (X Y : Finset V) : Finset V :=
  by
    classical
    exact Y.filter fun y ↦ ∀ x ∈ X, G.Adj x y

/-- Vertices of `Y` which are not in the complete right core. -/
noncomputable def rightExceptional [DecidableEq V] (G : SimpleGraph V) (X Y : Finset V) : Finset V :=
  Y \ rightCore G X Y

section Interlace

/-- Alternate elements of two lists, starting with the first list.  In all applications the
first list has either the same length as the second or one additional element. -/
def interlace {A : Type*} : List A → List A → List A
  | [], _ => []
  | a :: as, [] => [a]
  | a :: as, b :: bs => a :: b :: interlace as bs

@[simp] lemma interlace_nil_left {A : Type*} (bs : List A) :
    interlace ([] : List A) bs = [] := rfl

@[simp] lemma interlace_nil_right {A : Type*} (a : A) (as : List A) :
    interlace (a :: as) [] = [a] := rfl

@[simp] lemma interlace_cons_cons {A : Type*} (a b : A) (as bs : List A) :
    interlace (a :: as) (b :: bs) = a :: b :: interlace as bs := rfl

lemma mem_interlace_iff {A : Type*} {as bs : List A} (h : as.length = bs.length + 1)
    {z : A} : z ∈ interlace as bs ↔ z ∈ as ∨ z ∈ bs := by
  induction as generalizing bs with
  | nil => simp at h
  | cons x xs ih =>
      cases bs with
      | nil =>
          cases xs with
          | nil => simp [interlace]
          | cons z zs => simp at h
      | cons y ys =>
          have h' : xs.length = ys.length + 1 := by simpa using h
          simp [interlace, ih h', or_assoc, or_left_comm]

lemma mem_interlace_left {A : Type*} {as bs : List A} (h : as.length = bs.length + 1)
    {a : A} (ha : a ∈ as) : a ∈ interlace as bs :=
  (mem_interlace_iff h).2 (Or.inl ha)

lemma mem_interlace_right {A : Type*} {as bs : List A} (h : as.length = bs.length + 1)
    {b : A} (hb : b ∈ bs) : b ∈ interlace as bs :=
  (mem_interlace_iff h).2 (Or.inr hb)

lemma interlace_ne_nil_of_left_ne_nil {A : Type*} {as bs : List A} (h : as ≠ []) :
    interlace as bs ≠ [] := by
  cases as with
  | nil => exact False.elim (h rfl)
  | cons a as => cases bs <;> simp [interlace]

lemma head_interlace {A : Type*} {as bs : List A} (h : as ≠ []) :
    (interlace as bs).head (interlace_ne_nil_of_left_ne_nil h) = as.head h := by
  cases as with
  | nil => exact False.elim (h rfl)
  | cons a as => cases bs <;> rfl

lemma nodup_interlace {A : Type*} {as bs : List A} (h : as.length = bs.length + 1)
    (ha : as.Nodup) (hb : bs.Nodup) (hd : List.Disjoint as bs) :
    (interlace as bs).Nodup := by
  induction as generalizing bs with
  | nil => simp at h
  | cons x xs ih =>
      cases bs with
      | nil =>
          cases xs with
          | nil => simp [interlace]
          | cons z zs => simp at h
      | cons y ys =>
          have h' : xs.length = ys.length + 1 := by simpa using h
          have hd' : List.Disjoint xs ys := by
            intro z hzx hzy
            exact hd (a := z) (by simp [hzx]) (by simp [hzy])
          have ht := ih h' ha.tail hb.tail hd'
          have hxy : x ≠ y := by
            intro hxy
            exact hd (a := x) (by simp) (by simp [hxy])
          have hx_tail : x ∉ interlace xs ys := by
            rw [mem_interlace_iff h']
            push_neg
            exact ⟨(List.nodup_cons.mp ha).1,
              fun hxy ↦ hd (a := x) (by simp) (by simp [hxy])⟩
          have hy_tail : y ∉ interlace xs ys := by
            rw [mem_interlace_iff h']
            push_neg
            exact ⟨fun hyx ↦ hd (a := y) (by simp [hyx]) (by simp),
              (List.nodup_cons.mp hb).1⟩
          simp [interlace, hxy, hx_tail, hy_tail, ht]

lemma isChain_interlace {G : SimpleGraph V} {as bs : List V}
    (h : as.length = bs.length + 1)
    (hab : ∀ a ∈ as, ∀ b ∈ bs, G.Adj a b) :
    (interlace as bs).IsChain G.Adj := by
  induction as generalizing bs with
  | nil => simp at h
  | cons x xs ih =>
      cases bs with
      | nil => simp [interlace]
      | cons y ys =>
          have h' : xs.length = ys.length + 1 := by simpa using h
          have hxy : G.Adj x y := hab x (by simp) y (by simp)
          cases xs with
          | nil => simp at h
          | cons z zs =>
              have hyz : G.Adj y z :=
                (hab z (by simp) y (by simp)).symm
              have htail : (interlace (z :: zs) ys).IsChain G.Adj := by
                apply ih h'
                intro a ha b hb
                exact hab a (by simp [ha]) b (by simp [hb])
              have hne : interlace (z :: zs) ys ≠ [] := by
                cases ys <;> simp [interlace]
              have hhead : (interlace (z :: zs) ys).head hne = z := by
                cases ys <;> rfl
              have hychain : (y :: interlace (z :: zs) ys).IsChain G.Adj :=
                htail.cons_of_ne_nil hne (by simpa [hhead] using hyz)
              exact List.isChain_cons_cons.mpr ⟨hxy, hychain⟩

end Interlace

section BoundedGroups

/-- Partition two disjoint lists into `k` labelled groups.  A group contains at most `d`
elements of the first list and at most `c` elements altogether.  This is the elementary
bin-packing fact used in the complete-core argument. -/
lemma exists_bounded_groups {A : Type*} (as bs : List A) (k c d : ℕ)
    (hdc : d ≤ c) (haBound : as.length ≤ k * d)
    (htotal : as.length + bs.length ≤ k * c)
    (haNodup : as.Nodup) (hbNodup : bs.Nodup) (habDisj : List.Disjoint as bs) :
    ∃ gs : List (List A × List A),
      gs.length = k ∧
      (∀ g ∈ gs,
        g.1.length ≤ d ∧ g.1.length + g.2.length ≤ c ∧
        g.1.Nodup ∧ g.2.Nodup ∧ List.Disjoint g.1 g.2 ∧
        (∀ a ∈ g.1, a ∈ as) ∧ (∀ b ∈ g.2, b ∈ bs)) ∧
      (∀ a ∈ as, ∃ g ∈ gs, a ∈ g.1) ∧
      (∀ b ∈ bs, ∃ g ∈ gs, b ∈ g.2) ∧
      (0 < k → c - min d as.length ≤ bs.length →
        ∃ g ∈ gs, g.1.length + g.2.length = c) := by
  induction k generalizing as bs with
  | zero =>
      have ha0 : as.length = 0 := by omega
      have hb0 : bs.length = 0 := by omega
      have has : as = [] := List.length_eq_zero_iff.mp ha0
      have hbs : bs = [] := List.length_eq_zero_iff.mp hb0
      subst as
      subst bs
      exact ⟨[], rfl, by simp⟩
  | succ k ih =>
      let ga := as.take d
      let free := c - ga.length
      let gb := bs.take free
      let ar := as.drop d
      let br := bs.drop free
      have haBound' : as.length ≤ k * d + d := by
        simpa [Nat.succ_mul] using haBound
      have htotal' : as.length + bs.length ≤ k * c + c := by
        simpa [Nat.succ_mul] using htotal
      have hgaLen : ga.length ≤ d := by simp [ga]
      have hgaC : ga.length ≤ c := hgaLen.trans hdc
      have hgbLen : gb.length ≤ free := by simp [gb]
      have hgroup : ga.length + gb.length ≤ c := by
        dsimp only [free] at hgbLen
        omega
      have harBound : ar.length ≤ k * d := by
        simp only [ar, List.length_drop]
        by_cases had : as.length ≤ d
        · have : as.length - d = 0 := Nat.sub_eq_zero_of_le had
          simp [this]
        · have hdle : d ≤ as.length := Nat.le_of_not_ge had
          omega
      have hremTotal : ar.length + br.length ≤ k * c := by
        simp only [ar, br, List.length_drop]
        have hgaEq : ga.length = min d as.length := by simp [ga, Nat.min_comm]
        have hfree : free = c - min d as.length := by simp [free, hgaEq]
        rw [hfree]
        by_cases hbfree : bs.length ≤ c - min d as.length
        · have hbsub : bs.length - (c - min d as.length) = 0 :=
            Nat.sub_eq_zero_of_le hbfree
          rw [hbsub, Nat.add_zero]
          have harD : as.length - d ≤ k * d := by
            by_cases had : as.length ≤ d
            · simp [Nat.sub_eq_zero_of_le had]
            · have hdle : d ≤ as.length := Nat.le_of_not_ge had
              omega
          exact harD.trans (Nat.mul_le_mul_left k hdc)
        · have hfreele : c - min d as.length ≤ bs.length := Nat.le_of_not_ge hbfree
          have hminle : min d as.length ≤ c :=
            (min_le_left d as.length).trans hdc
          have htakeDrop :
              (as.length - d) + (bs.length - (c - min d as.length)) =
                as.length + bs.length - c := by
            by_cases had : d ≤ as.length
            · rw [min_eq_left had]
              omega
            · have hale : as.length ≤ d := Nat.le_of_not_ge had
              rw [min_eq_right hale]
              simp [Nat.sub_eq_zero_of_le hale]
              omega
          rw [htakeDrop]
          omega
      have harNodup : ar.Nodup := by
        dsimp only [ar]
        exact haNodup.drop
      have hbrNodup : br.Nodup := by
        dsimp only [br]
        exact hbNodup.drop
      have harbr : List.Disjoint ar br := by
        intro z hzar hzbr
        exact habDisj (a := z) (List.mem_of_mem_drop hzar) (List.mem_of_mem_drop hzbr)
      obtain ⟨rest, hrestLen, hrestGood, hrestA, hrestB, hrestFull⟩ :=
        ih ar br harBound hremTotal harNodup hbrNodup harbr
      have hgaNodup : ga.Nodup := by
        dsimp only [ga]
        exact haNodup.take
      have hgbNodup : gb.Nodup := by
        dsimp only [gb]
        exact hbNodup.take
      have hgagb : List.Disjoint ga gb := by
        intro z hzga hzgb
        exact habDisj (a := z) (List.mem_of_mem_take hzga) (List.mem_of_mem_take hzgb)
      refine ⟨(ga, gb) :: rest, by simp [hrestLen], ?_, ?_, ?_, ?_⟩
      · intro g hg
        simp only [List.mem_cons] at hg
        rcases hg with hg | hg
        · subst g
          refine ⟨hgaLen, hgroup, hgaNodup, hgbNodup, hgagb, ?_, ?_⟩
          · intro a ha
            exact List.mem_of_mem_take ha
          · intro b hb
            exact List.mem_of_mem_take hb
        · rcases hrestGood g hg with ⟨hgd, hgc, hgna, hgnb, hdisj, hga, hgb⟩
          refine ⟨hgd, hgc, hgna, hgnb, hdisj, ?_, ?_⟩
          · intro a ha
            exact List.mem_of_mem_drop (hga a ha)
          · intro b hb
            exact List.mem_of_mem_drop (hgb b hb)
      · intro a ha
        by_cases haga : a ∈ ga
        · exact ⟨(ga, gb), by simp, haga⟩
        · have har : a ∈ ar := by
            have haa : a ∈ as.take d ++ as.drop d := by
              simpa [List.take_append_drop] using ha
            rcases List.mem_append.mp haa with hat | had
            · exact False.elim (haga (by simpa [ga] using hat))
            · simpa [ar] using had
          obtain ⟨g, hg, hag⟩ := hrestA a har
          exact ⟨g, by simp [hg], hag⟩
      · intro b hb
        by_cases hgbb : b ∈ gb
        · exact ⟨(ga, gb), by simp, hgbb⟩
        · have hbr : b ∈ br := by
            have hbb : b ∈ bs.take free ++ bs.drop free := by
              simpa [List.take_append_drop] using hb
            rcases List.mem_append.mp hbb with hbt | hbd
            · exact False.elim (hgbb (by simpa [gb] using hbt))
            · simpa [br] using hbd
          obtain ⟨g, hg, hbg⟩ := hrestB b hbr
          exact ⟨g, by simp [hg], hbg⟩
      · intro _ hfreeBs
        refine ⟨(ga, gb), by simp, ?_⟩
        have hgaEq : ga.length = min d as.length := by simp [ga]
        have hgbEq : gb.length = free := by
          simp [gb, List.length_take, hfreeBs, free, hgaEq]
        change ga.length + gb.length = c
        rw [hgaEq, hgbEq]
        dsimp only [free]
        rw [hgaEq]
        exact Nat.add_sub_of_le ((min_le_left d as.length).trans hdc)

end BoundedGroups

section CorePaths

/-- Interlacing a prefix controlled by `s₀` with a complete-core suffix controlled by `sr`
gives a chain.  The vertices in `s₀` may be used next to either kind of left vertex; the
vertices in `sr` are only used between suffix vertices. -/
lemma isChain_interlace_append {G : SimpleGraph V}
    {as bs s₀ sr : List V} (hAs : as.length = s₀.length)
    (hBs : bs.length = sr.length + 1) (hbs : bs ≠ [])
    (h₀ : ∀ x ∈ as ++ bs, ∀ y ∈ s₀, G.Adj x y)
    (hr : ∀ x ∈ bs, ∀ y ∈ sr, G.Adj x y) :
    (interlace (as ++ bs) (s₀ ++ sr)).IsChain G.Adj := by
  induction as generalizing s₀ with
  | nil =>
      have hs₀ : s₀ = [] := List.length_eq_zero_iff.mp (by simpa using hAs.symm)
      subst s₀
      simpa using isChain_interlace hBs hr
  | cons a as ih =>
      cases s₀ with
      | nil => simp at hAs
      | cons y ys =>
          have hlen : as.length = ys.length := by simpa using hAs
          have hay : G.Adj a y := h₀ a (by simp) y (by simp)
          have htail :
              (interlace (as ++ bs) (ys ++ sr)).IsChain G.Adj := by
            apply ih hlen
            intro x hx z hz
            exact h₀ x (by simp [hx]) z (by simp [hz])
          have hne : as ++ bs ≠ [] := by
            intro heq
            exact hbs (List.append_eq_nil_iff.mp heq).2
          have hyhead : G.Adj y ((as ++ bs).head hne) := by
            apply (h₀ ((as ++ bs).head hne) (by simp [List.head_mem hne]) y (by simp)).symm
          have htailNe : interlace (as ++ bs) (ys ++ sr) ≠ [] :=
            interlace_ne_nil_of_left_ne_nil hne
          have hhead :
              (interlace (as ++ bs) (ys ++ sr)).head htailNe = (as ++ bs).head hne := by
            exact head_interlace hne
          have hychain :
              (y :: interlace (as ++ bs) (ys ++ sr)).IsChain G.Adj :=
            htail.cons_of_ne_nil htailNe (by simpa [hhead] using hyhead)
          exact List.isChain_cons_cons.mpr ⟨hay, hychain⟩

/-- A list contained in a finset is disjoint from a list contained in a disjoint finset. -/
lemma list_disjoint_of_mem_finsets [DecidableEq V] {A B : Finset V} {as bs : List V}
    (hAB : Disjoint A B) (ha : ∀ a ∈ as, a ∈ A) (hb : ∀ b ∈ bs, b ∈ B) :
    List.Disjoint as bs := by
  intro z hzas hzbs
  exact Finset.disjoint_left.mp hAB (ha z hzas) (hb z hzbs)

/-- Build one alternating path from a bounded group of exceptional and core left vertices.
If the group has the maximum possible size, the path contains every vertex of `Y`. -/
lemma exists_path_for_core_group [DecidableEq V] (G : SimpleGraph V)
    (X Y Y₀ X₀ : Finset V) (hXY : Disjoint X Y)
    (hY₀Y : Y₀ ⊆ Y) (hX₀X : X₀ ⊆ X) (hY₀ne : Y₀.Nonempty)
    (hY₀ : ∀ y ∈ Y₀, ∀ x ∈ X, G.Adj x y)
    (hX₀ : ∀ x ∈ X₀, ∀ y ∈ Y, G.Adj x y)
    (as bs : List V) (haNodup : as.Nodup) (hbNodup : bs.Nodup)
    (habDisj : List.Disjoint as bs) (haX : ∀ a ∈ as, a ∈ X)
    (hbX₀ : ∀ b ∈ bs, b ∈ X₀) (haBound : as.length ≤ Y₀.card)
    (htotal : as.length + bs.length ≤ Y.card + 1) :
    ∃ p : List V, IsPath G p ∧
      (∀ a ∈ as, a ∈ p) ∧ (∀ b ∈ bs, b ∈ p) ∧
      (as.length + bs.length = Y.card + 1 → ∀ y ∈ Y, y ∈ p) := by
  classical
  by_cases hempty : as = [] ∧ bs = []
  · obtain ⟨y, hy⟩ := hY₀ne
    refine ⟨[y], isPath_singleton G y, ?_, ?_, ?_⟩
    · simpa [hempty.1]
    · simpa [hempty.2]
    · intro hfull
      simp [hempty] at hfull
  · let special : ℕ := if bs = [] then as.length - 1 else as.length
    let s₀ : List V := Y₀.toList.take special
    let R : Finset V := Y \ s₀.toFinset
    let need : ℕ := as.length + bs.length - 1 - special
    let sr : List V := R.toList.take need
    have hspecial : special ≤ Y₀.card := by
      dsimp only [special]
      split_ifs
      · exact (Nat.sub_le _ _).trans haBound
      · exact haBound
    have hs₀Len : s₀.length = special := by
      simp [s₀, List.length_take, hspecial]
    have hs₀Y₀ : ∀ y ∈ s₀, y ∈ Y₀ := by
      intro y hy
      exact Finset.mem_toList.mp (List.mem_of_mem_take hy)
    have hs₀Y : ∀ y ∈ s₀, y ∈ Y := fun y hy ↦ hY₀Y (hs₀Y₀ y hy)
    have hs₀Nodup : s₀.Nodup := by
      dsimp only [s₀]
      exact Y₀.nodup_toList.take
    have hs₀card : s₀.toFinset.card = special := by
      rw [List.toFinset_card_of_nodup hs₀Nodup, hs₀Len]
    have hs₀subY : s₀.toFinset ⊆ Y := by
      intro y hy
      exact hs₀Y y (List.mem_toFinset.mp hy)
    have hRcard : R.card = Y.card - special := by
      rw [show R = Y \ s₀.toFinset by rfl, Finset.card_sdiff_of_subset hs₀subY,
        hs₀card]
    have hneed : need ≤ R.card := by
      dsimp only [need]
      rw [hRcard]
      have hspecTotal : special ≤ as.length + bs.length - 1 := by
        dsimp only [special]
        by_cases hbs : bs = []
        · simp [hbs]
        · have hbpos : 0 < bs.length := List.length_pos_of_ne_nil hbs
          simp [hbs]
          omega
      omega
    have hsrLen : sr.length = need := by
      simp [sr, List.length_take, hneed]
    have hsrR : ∀ y ∈ sr, y ∈ R := by
      intro y hy
      exact Finset.mem_toList.mp (List.mem_of_mem_take hy)
    have hsrY : ∀ y ∈ sr, y ∈ Y := by
      intro y hy
      exact Finset.mem_sdiff.mp (hsrR y hy) |>.1
    have hsrNodup : sr.Nodup := by
      dsimp only [sr]
      exact R.nodup_toList.take
    have hs₀sr : List.Disjoint s₀ sr := by
      intro y hys₀ hysr
      exact (Finset.mem_sdiff.mp (hsrR y hysr)).2 (List.mem_toFinset.mpr hys₀)
    have hsepsNodup : (s₀ ++ sr).Nodup := hs₀Nodup.append hsrNodup hs₀sr
    have hsepY : ∀ y ∈ s₀ ++ sr, y ∈ Y := by
      intro y hy
      rcases List.mem_append.mp hy with hy | hy
      · exact hs₀Y y hy
      · exact hsrY y hy
    have hxsNodup : (as ++ bs).Nodup := haNodup.append hbNodup habDisj
    have hxsX : ∀ x ∈ as ++ bs, x ∈ X := by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact haX x hx
      · exact hX₀X (hbX₀ x hx)
    have hxsSep : List.Disjoint (as ++ bs) (s₀ ++ sr) :=
      list_disjoint_of_mem_finsets hXY hxsX hsepY
    have hsepLen : (as ++ bs).length = (s₀ ++ sr).length + 1 := by
      simp only [List.length_append, hs₀Len, hsrLen]
      dsimp only [need]
      have hpos : 0 < as.length + bs.length := by
        by_contra h
        simp only [not_lt, nonpos_iff_eq_zero, Nat.add_eq_zero_iff] at h
        exact hempty ⟨List.length_eq_zero_iff.mp h.1, List.length_eq_zero_iff.mp h.2⟩
      have hspecTotal : special ≤ as.length + bs.length - 1 := by
        dsimp only [special]
        by_cases hbs : bs = []
        · simp [hbs]
        · have hbpos : 0 < bs.length := List.length_pos_of_ne_nil hbs
          simp [hbs]
          omega
      omega
    let p := interlace (as ++ bs) (s₀ ++ sr)
    have hpNodup : p.Nodup := nodup_interlace hsepLen hxsNodup hsepsNodup hxsSep
    have hpChain : p.IsChain G.Adj := by
      by_cases haNil : as = []
      · have hs₀Nil : s₀ = [] := by
          apply List.length_eq_zero_iff.mp
          simp [hs₀Len, special, haNil]
        dsimp only [p]
        simp only [haNil, hs₀Nil, List.nil_append] at hsepLen ⊢
        apply isChain_interlace hsepLen
        intro x hx y hy
        exact hX₀ x (hbX₀ x hx) y (hsrY y hy)
      · by_cases hbNil : bs = []
        · have hsrNil : sr = [] := by
            apply List.length_eq_zero_iff.mp
            simp [hsrLen, need, special, hbNil]
          dsimp only [p]
          simp only [hbNil, hsrNil, List.append_nil] at hsepLen ⊢
          apply isChain_interlace hsepLen
          intro x hx y hy
          exact hY₀ y (hs₀Y₀ y hy) x (haX x hx)
        · have hAs : as.length = s₀.length := by simp [hs₀Len, special, hbNil]
          have hBs : bs.length = sr.length + 1 := by
            rw [hsrLen]
            dsimp only [need, special]
            rw [if_neg hbNil]
            have haPos : 0 < as.length := List.length_pos_of_ne_nil haNil
            have hbPos : 0 < bs.length := List.length_pos_of_ne_nil hbNil
            omega
          dsimp only [p]
          apply isChain_interlace_append hAs hBs hbNil
          · intro x hx y hy
            exact hY₀ y (hs₀Y₀ y hy) x (hxsX x hx)
          · intro x hx y hy
            exact hX₀ x (hbX₀ x hx) y (hsrY y hy)
    have hpNe : p ≠ [] := by
      apply interlace_ne_nil_of_left_ne_nil
      intro hab
      exact hempty (List.append_eq_nil_iff.mp hab)
    refine ⟨p, ⟨hpNe, hpNodup, hpChain⟩, ?_, ?_, ?_⟩
    · intro a ha
      exact mem_interlace_left hsepLen (List.mem_append_left _ ha)
    · intro b hb
      exact mem_interlace_left hsepLen (List.mem_append_right _ hb)
    · intro hfull y hy
      apply mem_interlace_right hsepLen
      have hsub : (s₀ ++ sr).toFinset ⊆ Y := by
        intro z hz
        exact hsepY z (List.mem_toFinset.mp hz)
      have hcard : (s₀ ++ sr).toFinset.card = Y.card := by
        rw [List.toFinset_card_of_nodup hsepsNodup]
        simpa [hfull] using hsepLen.symm
      have heq : (s₀ ++ sr).toFinset = Y :=
        Finset.eq_of_subset_of_card_le hsub hcard.ge
      exact List.mem_toFinset.mp (by simpa [heq] using hy)

end CorePaths

section CompleteCoreCover

/-- The numerical heart of the complete-core lemma. -/
lemma complete_core_arithmetic {x₀ x₁ y₀ y₁ : ℕ} (hy₀ : 0 < y₀)
    (hzero : y₁ = 0 → x₁ = 0)
    (hsize : y₀ + y₁ < x₀ + x₁) (hratio : 2 * x₁ * y₁ < x₀ * y₀) :
    y₁ < x₀ ∧
      x₁ < ((x₀ + x₁) ⌈/⌉ (y₀ + y₁ + 1)) * y₀ := by
  have hy₁x₀ : y₁ < x₀ := by
    by_contra hnot
    have hx₀le : x₀ ≤ y₁ := Nat.le_of_not_gt hnot
    have hy₁pos : 0 < y₁ := by
      by_contra hy₁z
      have hy₁eq : y₁ = 0 := Nat.eq_zero_of_not_pos hy₁z
      have hx₀eq : x₀ = 0 := Nat.eq_zero_of_le_zero (by simpa [hy₁eq] using hx₀le)
      simp [hx₀eq] at hratio
    have hy₀x₁ : y₀ < x₁ := by omega
    have hbad : x₀ * y₀ < 2 * x₁ * y₁ := by
      calc
        x₀ * y₀ ≤ y₁ * y₀ := Nat.mul_le_mul_right y₀ hx₀le
        _ < y₁ * x₁ := (Nat.mul_lt_mul_left hy₁pos).2 hy₀x₁
        _ ≤ 2 * x₁ * y₁ := by
          have hle : y₁ * x₁ ≤ 2 * (y₁ * x₁) :=
            Nat.le_mul_of_pos_left _ (by omega)
          simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hle
    exact (Nat.not_lt_of_ge hbad.le) hratio
  refine ⟨hy₁x₀, ?_⟩
  let c := y₀ + y₁ + 1
  let k := (x₀ + x₁) ⌈/⌉ c
  have hc : 0 < c := by simp [c]
  have hx₁cross : x₁ * c < (x₀ + x₁) * y₀ := by
    by_cases hx₁z : x₁ = 0
    · simpa [hx₁z] using hratio
    · have hy₁pos : 0 < y₁ := by
        by_contra hy₁z
        exact hx₁z (hzero (Nat.eq_zero_of_not_pos hy₁z))
      have htail : x₁ * (y₁ + 1) ≤ 2 * x₁ * y₁ := by
        nlinarith
      dsimp only [c]
      calc
        x₁ * (y₀ + y₁ + 1) = x₁ * y₀ + x₁ * (y₁ + 1) := by ring
        _ ≤ x₁ * y₀ + 2 * x₁ * y₁ := Nat.add_le_add_left htail _
        _ < x₁ * y₀ + x₀ * y₀ := Nat.add_lt_add_left hratio _
        _ = (x₀ + x₁) * y₀ := by ring
  have hxceil : x₀ + x₁ ≤ c * k := by
    exact le_smul_ceilDiv hc
  have hlt : x₁ * c < (k * y₀) * c := by
    calc
      x₁ * c < (x₀ + x₁) * y₀ := hx₁cross
      _ ≤ (c * k) * y₀ := Nat.mul_le_mul_right y₀ hxceil
      _ = (k * y₀) * c := by ring
  have : x₁ < k * y₀ := (Nat.mul_lt_mul_right hc).mp hlt
  simpa [c, k] using this

/-- **Chen--Chen / PVW complete-core bipartite lemma.**

Let `X₀` and `Y₀` be the vertices complete to the opposite part and let `X₁,Y₁`
be their complements inside the two (disjoint) parts.  If `Y₀` is nonempty, `|X|>|Y|`,
and

`|X₀| |Y₀| > 2 |X₁| |Y₁|`,

then `X ∪ Y` is covered by at most `⌈|X|/(|Y|+1)⌉` paths of `G`.  Only edges
between the displayed parts are used, and paths belonging to the list may reuse vertices. -/
theorem complete_core_bipartite_path_cover [DecidableEq V] (G : SimpleGraph V)
    (X Y : Finset V) (hXY : Disjoint X Y)
    (hY₀ne : (rightCore G X Y).Nonempty) (hsize : Y.card < X.card)
    (hcore :
      (leftExceptional G X Y = ∅ ∧ rightExceptional G X Y = ∅) ∨
        2 * (leftExceptional G X Y).card * (rightExceptional G X Y).card <
          (leftCore G X Y).card * (rightCore G X Y).card) :
    HasPathCoverOnAtMost G (((X ∪ Y : Finset V) : Set V))
      (X.card ⌈/⌉ (Y.card + 1)) := by
  classical
  let X₀ := leftCore G X Y
  let X₁ := leftExceptional G X Y
  let Y₀ := rightCore G X Y
  let Y₁ := rightExceptional G X Y
  let k := X.card ⌈/⌉ (Y.card + 1)
  have hX₀sub : X₀ ⊆ X := by
    intro x hx
    exact (Finset.mem_filter.mp hx).1
  have hY₀sub : Y₀ ⊆ Y := by
    intro y hy
    exact (Finset.mem_filter.mp hy).1
  have hX₁eq : X₁ = X \ X₀ := rfl
  have hY₁eq : Y₁ = Y \ Y₀ := rfl
  have hX₁sub : X₁ ⊆ X := by
    rw [hX₁eq]
    exact Finset.sdiff_subset
  have hY₁sub : Y₁ ⊆ Y := by
    rw [hY₁eq]
    exact Finset.sdiff_subset
  have hXparts : X₀.card + X₁.card = X.card := by
    rw [hX₁eq, Finset.card_sdiff_of_subset hX₀sub]
    exact Nat.add_sub_of_le (Finset.card_mono hX₀sub)
  have hYparts : Y₀.card + Y₁.card = Y.card := by
    rw [hY₁eq, Finset.card_sdiff_of_subset hY₀sub]
    exact Nat.add_sub_of_le (Finset.card_mono hY₀sub)
  have hY₀pos : 0 < Y₀.card := Finset.card_pos.mpr hY₀ne
  have hzero : Y₁.card = 0 → X₁.card = 0 := by
    intro hY₁zero
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx₁
    have hxData := Finset.mem_sdiff.mp (hX₁eq ▸ hx₁)
    have hnotAll : ¬ ∀ y ∈ Y, G.Adj x y := by
      intro hall
      exact hxData.2 (Finset.mem_filter.mpr ⟨hxData.1, hall⟩)
    push Not at hnotAll
    obtain ⟨y, hyY, hxy⟩ := hnotAll
    have hyNotCore : y ∉ Y₀ := by
      intro hyCore
      have hallX := (Finset.mem_filter.mp hyCore).2
      exact hxy (hallX x hxData.1)
    have hyY₁ : y ∈ Y₁ := by
      rw [hY₁eq]
      exact Finset.mem_sdiff.mpr ⟨hyY, hyNotCore⟩
    have hY₁empty : Y₁ = ∅ := Finset.card_eq_zero.mp hY₁zero
    simpa [hY₁empty] using hyY₁
  have hsizeParts : Y₀.card + Y₁.card < X₀.card + X₁.card := by omega
  have hratioParts : 2 * X₁.card * Y₁.card < X₀.card * Y₀.card := by
    rcases hcore with hcomplete | hratio
    · have hX₁empty : X₁ = ∅ := by simpa [X₁] using hcomplete.1
      have hY₁empty : Y₁ = ∅ := by simpa [Y₁] using hcomplete.2
      have hX₀pos : 0 < X₀.card := by
        rw [hX₁empty] at hXparts
        simp only [Finset.card_empty, add_zero] at hXparts
        omega
      simpa [hX₁empty, hY₁empty] using Nat.mul_pos hX₀pos hY₀pos
    · simpa [X₀, X₁, Y₀, Y₁] using hratio
  have harith := complete_core_arithmetic hY₀pos hzero hsizeParts hratioParts
  have hX₁slots : X₁.card < k * Y₀.card := by
    dsimp only [k]
    calc
      X₁.card <
          ((X₀.card + X₁.card) ⌈/⌉ (Y₀.card + Y₁.card + 1)) * Y₀.card :=
        harith.2
      _ = (X.card ⌈/⌉ (Y.card + 1)) * Y₀.card := by rw [hXparts, hYparts]
  have hdenom : 0 < Y.card + 1 := by omega
  have hceil : X.card ≤ (Y.card + 1) * k := by
    exact le_smul_ceilDiv hdenom
  have hkpos : 0 < k := by
    have hXpos : 0 < X.card := by omega
    by_contra hk
    have hkzero : k = 0 := Nat.eq_zero_of_not_pos hk
    rw [hkzero, Nat.mul_zero] at hceil
    have : X.card = 0 := Nat.eq_zero_of_le_zero hceil
    omega
  have htotal : X₁.toList.length + X₀.toList.length ≤ k * (Y.card + 1) := by
    simp only [Finset.length_toList]
    rw [Nat.mul_comm]
    omega
  have hfree : Y.card + 1 - min Y₀.card X₁.toList.length ≤ X₀.toList.length := by
    simp only [Finset.length_toList]
    have hy₁x₀ := harith.1
    omega
  obtain ⟨gs, hgsLen, hgsGood, hgsX₁, hgsX₀, hgsFull⟩ :=
    exists_bounded_groups X₁.toList X₀.toList k (Y.card + 1) Y₀.card
      (by omega) (by simpa using hX₁slots.le) htotal X₁.nodup_toList X₀.nodup_toList (by
        intro x hx₁ hx₀
        have hxnot := (Finset.mem_sdiff.mp (hX₁eq ▸ Finset.mem_toList.mp hx₁)).2
        exact hxnot (Finset.mem_toList.mp hx₀))
  have hfull := hgsFull hkpos hfree
  have hY₀complete : ∀ y ∈ Y₀, ∀ x ∈ X, G.Adj x y := by
    intro y hy x hx
    exact (Finset.mem_filter.mp hy).2 x hx
  have hX₀complete : ∀ x ∈ X₀, ∀ y ∈ Y, G.Adj x y := by
    intro x hx y hy
    exact (Finset.mem_filter.mp hx).2 y hy
  have hpath : ∀ g ∈ gs, ∃ p : List V, IsPath G p ∧
      (∀ a ∈ g.1, a ∈ p) ∧ (∀ b ∈ g.2, b ∈ p) ∧
      (g.1.length + g.2.length = Y.card + 1 → ∀ y ∈ Y, y ∈ p) := by
    intro g hg
    rcases hgsGood g hg with ⟨hgd, hgc, hgna, hgnb, hgdisj, hga, hgb⟩
    apply exists_path_for_core_group G X Y Y₀ X₀ hXY hY₀sub hX₀sub
      (by simpa [Y₀] using hY₀ne) hY₀complete hX₀complete g.1 g.2 hgna hgnb hgdisj
    · intro a ha
      exact hX₁sub (Finset.mem_toList.mp (hga a ha))
    · intro b hb
      exact Finset.mem_toList.mp (hgb b hb)
    · exact hgd
    · exact hgc
  let pathOf : {g // g ∈ gs} → List V := fun g ↦ Classical.choose (hpath g.1 g.2)
  have pathOf_spec (g : {g // g ∈ gs}) : IsPath G (pathOf g) ∧
      (∀ a ∈ g.1.1, a ∈ pathOf g) ∧ (∀ b ∈ g.1.2, b ∈ pathOf g) ∧
      (g.1.1.length + g.1.2.length = Y.card + 1 → ∀ y ∈ Y, y ∈ pathOf g) :=
    Classical.choose_spec (hpath g.1 g.2)
  let ps : List (List V) := gs.attach.map pathOf
  refine ⟨ps, ?_, ?_, ?_⟩
  · simp [ps, hgsLen, k]
  · intro p hp
    rcases List.mem_map.mp hp with ⟨g, hg, rfl⟩
    exact (pathOf_spec g).1
  · intro v hv
    rcases Finset.mem_union.mp hv with hvX | hvY
    · by_cases hvX₀ : v ∈ X₀
      · obtain ⟨g, hg, hvg⟩ := hgsX₀ v (Finset.mem_toList.mpr hvX₀)
        let sg : {g // g ∈ gs} := ⟨g, hg⟩
        refine ⟨pathOf sg, ?_, (pathOf_spec sg).2.2.1 v hvg⟩
        exact List.mem_map.mpr ⟨sg, by simp [sg], rfl⟩
      · have hvX₁ : v ∈ X₁ := by
          rw [hX₁eq]
          exact Finset.mem_sdiff.mpr ⟨hvX, hvX₀⟩
        obtain ⟨g, hg, hvg⟩ := hgsX₁ v (Finset.mem_toList.mpr hvX₁)
        let sg : {g // g ∈ gs} := ⟨g, hg⟩
        refine ⟨pathOf sg, ?_, (pathOf_spec sg).2.1 v hvg⟩
        exact List.mem_map.mpr ⟨sg, by simp [sg], rfl⟩
    · obtain ⟨g, hg, hgfull⟩ := hfull
      let sg : {g // g ∈ gs} := ⟨g, hg⟩
      refine ⟨pathOf sg, ?_, (pathOf_spec sg).2.2.2 hgfull v hvY⟩
      exact List.mem_map.mpr ⟨sg, by simp [sg], rfl⟩

/-- Alias matching the numbering in the Chen--Chen and PVW arguments. -/
theorem chen_lemma_2_4 [DecidableEq V] (G : SimpleGraph V) (X Y : Finset V)
    (hXY : Disjoint X Y) (hY₀ne : (rightCore G X Y).Nonempty) (hsize : Y.card < X.card)
    (hcore :
      (leftExceptional G X Y = ∅ ∧ rightExceptional G X Y = ∅) ∨
        2 * (leftExceptional G X Y).card * (rightExceptional G X Y).card <
          (leftCore G X Y).card * (rightCore G X Y).card) :
    HasPathCoverOnAtMost G (((X ∪ Y : Finset V) : Set V))
      (X.card ⌈/⌉ (Y.card + 1)) :=
  complete_core_bipartite_path_cover G X Y hXY hY₀ne hsize hcore

end CompleteCoreCover

end Erdos518
