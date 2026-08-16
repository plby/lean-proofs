import ErdosProblems.Erdos965.Countability
import ErdosProblems.Erdos965.CriticalPair
import ErdosProblems.Erdos965.UniformPrefix
import ErdosProblems.Erdos965.CoordinateNormalize
import ErdosProblems.Erdos965.CylinderSplit

open Function Set

universe u

namespace Erdos965

noncomputable section

/-! ## Simultaneous splitting of the varying coordinates -/

structure FiniteSplitWitness {ι : Type u} {n : ℕ}
    (p : Fin n → ι → HamelIndex) (D : Set ι) (M : Finset (Fin n)) where
  left : Set ι
  right : Set ι
  left_subset : left ⊆ D
  right_subset : right ⊆ D
  left_uncountable : ¬ left.Countable
  right_uncountable : ¬ right.Countable
  level : Fin n → ℕ
  split : ∀ j ∈ M,
    (∀ a ∈ left, ∀ b ∈ right, firstDiff (p j a) (p j b) = level j) ∧
      ((∀ a ∈ left, ∀ b ∈ right, p j a < p j b) ∨
        ∀ a ∈ left, ∀ b ∈ right, p j b < p j a)

theorem exists_finiteSplitWitness {ι : Type u} {n : ℕ}
    (p : Fin n → ι → HamelIndex) (D : Set ι) (M : Finset (Fin n))
    (hD : ¬ D.Countable) (hinj : ∀ j ∈ M, InjOn (p j) D) :
    Nonempty (FiniteSplitWitness p D M) := by
  classical
  induction M using Finset.induction_on with
  | empty =>
      exact ⟨{
        left := D
        right := D
        left_subset := Set.Subset.rfl
        right_subset := Set.Subset.rfl
        left_uncountable := hD
        right_uncountable := hD
        level := fun _ ↦ 0
        split := by simp }⟩
  | @insert j M hjM ih =>
      have hinjM : ∀ k ∈ M, InjOn (p k) D := by
        intro k hk
        exact hinj k (Finset.mem_insert_of_mem hk)
      obtain ⟨W⟩ := ih hinjM
      obtain ⟨U, V, N, hUW, hVW, hUunc, hVunc, hdiff, hord⟩ :=
        uncountable_cylinder_split (p j) (hinj j (Finset.mem_insert_self j M))
          W.left_subset W.right_subset W.left_uncountable W.right_uncountable
      refine ⟨{
        left := U
        right := V
        left_subset := hUW.trans W.left_subset
        right_subset := hVW.trans W.right_subset
        left_uncountable := hUunc
        right_uncountable := hVunc
        level := Function.update W.level j N
        split := ?_ }⟩
      intro k hk
      rw [Finset.mem_insert] at hk
      rcases hk with rfl | hk
      · simpa using And.intro hdiff hord
      · obtain ⟨hkdiff, hkord⟩ := W.split k hk
        have hkj : k ≠ j := fun h ↦ hjM (h ▸ hk)
        constructor
        · simpa [Function.update, hkj] using
            (fun a ha b hb ↦ hkdiff a (hUW ha) b (hVW hb))
        · rcases hkord with hkord | hkord
          · exact Or.inl fun a ha b hb ↦ hkord a (hUW ha) b (hVW hb)
          · exact Or.inr fun a ha b hb ↦ hkord a (hUW ha) b (hVW hb)

/-! ## Structural lemmas for one uniform family -/

private theorem commonPrefix_crossCoordinate_lt {ι : Type u} {n : ℕ}
    (F : ι → Finset HamelIndex) (hcard : ∀ i, (F i).card = n)
    (W : UniformPrefixWitness F hcard) {a b : ι}
    (ha : a ∈ W.carrier) (hb : b ∈ W.carrier) {j k : Fin n} (hjk : j < k) :
    finsetCoord F hcard a j < finsetCoord F hcard b k := by
  let x := finsetCoord F hcard a j
  let y := finsetCoord F hcard a k
  let x' := finsetCoord F hcard a j
  let y' := finsetCoord F hcard b k
  have hxy : x < y := finsetCoord_strictMono F hcard a hjk
  have hN : firstDiff x y < W.L :=
    W.crossCoordinate_firstDiff_lt F hcard ha ha hjk.ne
  have hbits := binaryCode_firstDiff_of_lt hxy
  have hy' : binaryCode y' (firstDiff x y) = binaryCode y (firstDiff x y) := by
    apply PiNat.res_eq_res.mp
      ((W.prefix_eq b hb k).trans (W.prefix_eq a ha k).symm)
    exact hN
  exact lt_of_binaryCode_eq_false_true hbits.1 (hy'.trans hbits.2)

theorem finset_eq_of_all_coords_eq {ι : Type u} {n : ℕ}
    (F : ι → Finset HamelIndex) (hcard : ∀ i, (F i).card = n) {a b : ι}
    (h : ∀ j, finsetCoord F hcard a j = finsetCoord F hcard b j) :
    F a = F b := by
  ext x
  constructor
  · intro hx
    have hx' : x ∈ (F a : Set HamelIndex) := hx
    rw [← range_finsetCoord F hcard a] at hx'
    obtain ⟨j, rfl⟩ := hx'
    rw [h j]
    exact finsetCoord_mem F hcard b j
  · intro hx
    have hx' : x ∈ (F b : Set HamelIndex) := hx
    rw [← range_finsetCoord F hcard b] at hx'
    obtain ⟨j, rfl⟩ := hx'
    rw [← h j]
    exact finsetCoord_mem F hcard a j

theorem criticalPair_crossUnion {ι : Type u} {n : ℕ}
    (F : ι → Finset HamelIndex) (hcard : ∀ i, (F i).card = n)
    (W : UniformPrefixWitness F hcard) {D : Set ι} {M : Finset (Fin n)}
    (hDW : D ⊆ W.carrier)
    (hconst : ∀ j ∉ M, ∃ c, ∀ i ∈ D, finsetCoord F hcard i j = c)
    (S : FiniteSplitWitness (fun j i ↦ finsetCoord F hcard i j) D M)
    {jstar : Fin n} (hjstarM : jstar ∈ M)
    (hlevel_le : ∀ j ∈ M, S.level j ≤ S.level jstar)
    (hlevel_ge : ∀ j ∈ M, W.L ≤ S.level j)
    (hjstarleast : ∀ j ∈ M, S.level j = S.level jstar → jstar ≤ j)
    {a b : ι} (ha : a ∈ S.left) (hb : b ∈ S.right) :
    criticalPair (F a ∪ F b) =
      (min (finsetCoord F hcard a jstar) (finsetCoord F hcard b jstar),
        max (finsetCoord F hcard a jstar) (finsetCoord F hcard b jstar)) := by
  classical
  let p : Fin n → ι → HamelIndex := fun j i ↦ finsetCoord F hcard i j
  let m := S.level jstar
  have haD : a ∈ D := S.left_subset ha
  have hbD : b ∈ D := S.right_subset hb
  have haW : a ∈ W.carrier := hDW haD
  have hbW : b ∈ W.carrier := hDW hbD
  have hLm : W.L ≤ m := hlevel_ge jstar hjstarM
  have hjstarsplit := S.split jstar hjstarM
  have hjstardiff : firstDiff (p jstar a) (p jstar b) = m :=
    hjstarsplit.1 a ha b hb
  have hcoord : ∀ {z}, z ∈ F a ∪ F b →
      ∃ j, z = p j a ∨ z = p j b := by
    intro z hz
    rw [Finset.mem_union] at hz
    rcases hz with hz | hz
    · have hz' : z ∈ (F a : Set HamelIndex) := hz
      rw [← range_finsetCoord F hcard a] at hz'
      obtain ⟨j, rfl⟩ := hz'
      exact ⟨j, Or.inl rfl⟩
    · have hz' : z ∈ (F b : Set HamelIndex) := hz
      rw [← range_finsetCoord F hcard b] at hz'
      obtain ⟨j, rfl⟩ := hz'
      exact ⟨j, Or.inr rfl⟩
  have hcross_lt : ∀ {r s : ι}, r ∈ D → s ∈ D →
      ∀ {j k : Fin n}, j ≠ k → firstDiff (p j r) (p k s) < W.L := by
    intro r s hr hs j k hjk
    exact W.crossCoordinate_firstDiff_lt F hcard (hDW hr) (hDW hs) hjk
  have hbound : ∀ {z}, z ∈ F a ∪ F b → ∀ {w}, w ∈ F a ∪ F b → z ≠ w →
      firstDiff z w ≤ m := by
    intro z hz w hw hzw
    obtain ⟨j, hzj⟩ := hcoord hz
    obtain ⟨k, hwk⟩ := hcoord hw
    rcases hzj with rfl | rfl <;> rcases hwk with rfl | rfl
    · by_cases hjk : j = k
      · subst k
        exact (hzw rfl).elim
      · exact (hcross_lt haD haD hjk).le.trans hLm
    · by_cases hjk : j = k
      · subst k
        by_cases hjM : j ∈ M
        · exact (S.split j hjM).1 a ha b hb ▸ hlevel_le j hjM
        · obtain ⟨c, hc⟩ := hconst j hjM
          exact (hzw ((hc a haD).trans (hc b hbD).symm)).elim
      · exact (hcross_lt haD hbD hjk).le.trans hLm
    · by_cases hjk : j = k
      · subst k
        by_cases hjM : j ∈ M
        · rw [firstDiff_comm]
          exact (S.split j hjM).1 a ha b hb ▸ hlevel_le j hjM
        · obtain ⟨c, hc⟩ := hconst j hjM
          exact (hzw ((hc b hbD).trans (hc a haD).symm)).elim
      · exact (hcross_lt hbD haD hjk).le.trans hLm
    · by_cases hjk : j = k
      · subst k
        exact (hzw rfl).elim
      · exact (hcross_lt hbD hbD hjk).le.trans hLm
  have hlo_le_of_max : ∀ {z}, z ∈ F a ∪ F b → ∀ {w}, w ∈ F a ∪ F b →
      z < w → firstDiff z w = m →
      min (p jstar a) (p jstar b) ≤ z := by
    intro z hz w hw hzw hzwm
    obtain ⟨j, hzj⟩ := hcoord hz
    obtain ⟨k, hwk⟩ := hcoord hw
    have hcoord_le_a {j : Fin n} (hjM : j ∈ M) (hjm : S.level j = m) :
        min (p jstar a) (p jstar b) ≤ p j a := by
      have hjstarj : jstar ≤ j := hjstarleast j hjM hjm
      rcases hjstarj.eq_or_lt with hEq | hlt
      · subst j
        exact min_le_left _ _
      · exact (min_le_left _ _).trans
          (by simpa only [p] using
            (commonPrefix_crossCoordinate_lt F hcard W haW haW hlt).le)
    have hcoord_le_b {j : Fin n} (hjM : j ∈ M) (hjm : S.level j = m) :
        min (p jstar a) (p jstar b) ≤ p j b := by
      have hjstarj : jstar ≤ j := hjstarleast j hjM hjm
      rcases hjstarj.eq_or_lt with hEq | hlt
      · subst j
        exact min_le_right _ _
      · exact (min_le_left _ _).trans
          (by simpa only [p] using
            (commonPrefix_crossCoordinate_lt F hcard W haW hbW hlt).le)
    rcases hzj with rfl | rfl <;> rcases hwk with rfl | rfl
    · by_cases hjk : j = k
      · subst k
        exact (hzw.false).elim
      · have hlt := hcross_lt haD haD hjk
        omega
    · by_cases hjk : j = k
      · subst k
        by_cases hjM : j ∈ M
        · have hjm : S.level j = m := by
            exact ((S.split j hjM).1 a ha b hb).symm.trans hzwm
          exact hcoord_le_a hjM hjm
        · obtain ⟨c, hc⟩ := hconst j hjM
          exact (hzw.ne ((hc a haD).trans (hc b hbD).symm)).elim
      · have hlt := hcross_lt haD hbD hjk
        omega
    · by_cases hjk : j = k
      · subst k
        by_cases hjM : j ∈ M
        · have hjm : S.level j = m := by
            have hforward : firstDiff (p j a) (p j b) = m := by
              rw [firstDiff_comm]
              exact hzwm
            exact ((S.split j hjM).1 a ha b hb).symm.trans hforward
          exact hcoord_le_b hjM hjm
        · obtain ⟨c, hc⟩ := hconst j hjM
          exact (hzw.ne ((hc b hbD).trans (hc a haD).symm)).elim
      · have hlt := hcross_lt hbD haD hjk
        omega
    · by_cases hjk : j = k
      · subst k
        exact (hzw.false).elim
      · have hlt := hcross_lt hbD hbD hjk
        omega
  rcases hjstarsplit.2 with hord | hord
  · have hs : 2 ≤ (F a ∪ F b).card := by
      have hcard' : 1 < (F a ∪ F b).card := Finset.one_lt_card.mpr
        ⟨p jstar a, Finset.mem_union_left _ (finsetCoord_mem F hcard a jstar),
          p jstar b, Finset.mem_union_right _ (finsetCoord_mem F hcard b jstar),
          (hord a ha b hb).ne⟩
      omega
    have hp := criticalPair_eq_of_maximal_least hs
      (Finset.mem_union_left _ (finsetCoord_mem F hcard a jstar))
      (Finset.mem_union_right _ (finsetCoord_mem F hcard b jstar))
      (hord a ha b hb)
      (by
        intro z hz w hw hzw
        exact (hbound hz hw hzw).trans_eq hjstardiff.symm)
      (by
        intro z hz w hw hzw hdiff
        have hlo := hlo_le_of_max hz hw hzw (hdiff.trans hjstardiff)
        rw [min_eq_left (hord a ha b hb).le] at hlo
        exact hlo)
    simpa [min_eq_left (hord a ha b hb).le, max_eq_right (hord a ha b hb).le] using hp
  · have hs : 2 ≤ (F a ∪ F b).card := by
      have hcard' : 1 < (F a ∪ F b).card := Finset.one_lt_card.mpr
        ⟨p jstar b, Finset.mem_union_right _ (finsetCoord_mem F hcard b jstar),
          p jstar a, Finset.mem_union_left _ (finsetCoord_mem F hcard a jstar),
          (hord a ha b hb).ne⟩
      omega
    have hreverseDiff : firstDiff (p jstar b) (p jstar a) = m := by
      rw [firstDiff_comm]
      exact hjstardiff
    have hp := criticalPair_eq_of_maximal_least hs
      (Finset.mem_union_right _ (finsetCoord_mem F hcard b jstar))
      (Finset.mem_union_left _ (finsetCoord_mem F hcard a jstar))
      (hord a ha b hb)
      (by
        intro z hz w hw hzw
        exact (hbound hz hw hzw).trans_eq hreverseDiff.symm)
      (by
        intro z hz w hw hzw hdiff
        have hlo := hlo_le_of_max hz hw hzw (hdiff.trans hreverseDiff)
        rw [min_eq_right (hord a ha b hb).le] at hlo
        exact hlo)
    simpa [min_eq_right (hord a ha b hb).le, max_eq_left (hord a ha b hb).le] using hp

end

end Erdos965
