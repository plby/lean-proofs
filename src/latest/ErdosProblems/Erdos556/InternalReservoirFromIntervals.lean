import ErdosProblems.Erdos556.InternalCycleReservoir

/-!
# Turning two cycle intervals into a complete bipartite reservoir
-/

namespace Erdos556

open SimpleGraph Finset

theorem exists_internal_reservoir_from_intervals {V : Type*} [DecidableEq V]
    {G : SimpleGraph V} {z : V} (c : G.Walk z z) (hc : c.IsCycle)
    (A B : Finset ℕ) (Q M H : ℕ) (hQ : 0 < Q)
    (hA : A.card = Q + 2) (hB : B.card = Q + 3) (hM : M < c.length)
    (hAM : ∀ a ∈ A, a ≤ M) (hBM : ∀ b ∈ B, M < b ∧ b < c.length)
    (hparA : ∀ a ∈ A, ∀ b ∈ A, a % 2 = b % 2)
    (hparB : ∀ a ∈ B, ∀ b ∈ B, a % 2 = b % 2)
    (hdiam : ∀ a ∈ B, ∀ b ∈ B, b < a + H)
    (hcomplete : ∀ a ∈ A, ∀ b ∈ B, G.Adj (c.getVert a) (c.getVert b)) :
    ∃ X Y : Finset V, X.card = Q + 2 ∧ Y.card = Q ∧ Disjoint X Y ∧
      (∀ x ∈ X, ∀ y ∈ Y, G.Adj x y) ∧
      ∃ u ∈ X, ∃ v ∈ X, u ≠ v ∧ ∃ p : G.Walk u v, p.IsPath ∧
        c.length ≤ p.length + M + H ∧ p.length % 2 = c.length % 2 ∧
        ∀ w ∈ p.support, w ∈ X ∪ Y → w = u ∨ w = v := by
  classical
  have hAn : A.Nonempty := card_pos.mp (by omega)
  have hBn : B.Nonempty := card_pos.mp (by omega)
  let a := A.min' hAn
  let b := A.max' hAn
  let w := B.min' hBn
  let w' := B.max' hBn
  have ha : a ∈ A := A.min'_mem hAn
  have hb : b ∈ A := A.max'_mem hAn
  have hw : w ∈ B := B.min'_mem hBn
  have hw' : w' ∈ B := B.max'_mem hBn
  have hab : a < b := A.min'_lt_max'_of_card (by omega)
  have hww : w < w' := B.min'_lt_max'_of_card (by omega)
  have hmiddle : (B \ {w, w'}).Nonempty := by
    apply card_pos.mp
    have hpair : ({w, w'} : Finset ℕ).card ≤ 2 := (card_insert_le _ _).trans (by simp)
    have hint := card_le_card (show ({w, w'} : Finset ℕ) ∩ B ⊆ {w, w'} from inter_subset_left)
    rw [card_sdiff]
    omega
  obtain ⟨y, hy⟩ := hmiddle
  have hyB := (mem_sdiff.mp hy).1
  have hyw : y ≠ w := fun h => (mem_sdiff.mp hy).2 (by simp [h])
  have hyw' : y ≠ w' := fun h => (mem_sdiff.mp hy).2 (by simp [h])
  have hwy : w < y := lt_of_le_of_ne (B.min'_le y hyB) hyw.symm
  have hywlt : y < w' := lt_of_le_of_ne (B.le_max' y hyB) hyw'
  have hbM := hAM b hb
  have haM := hAM a ha
  have hwM := (hBM w hw).1
  have hwlen := (hBM w' hw').2
  have hallA (i : ℕ) (hi : i ∈ A) : i < c.length := (hAM i hi).trans_lt hM
  have hinjA : Set.InjOn c.getVert (A : Set ℕ) := by
    intro i hi j hj hij
    exact hc.getVert_injOn' (by change i ≤ c.length - 1; have h := hallA i hi; omega)
      (by change j ≤ c.length - 1; have h := hallA j hj; omega) hij
  have hinjB : Set.InjOn c.getVert (B : Set ℕ) := by
    intro i hi j hj hij
    exact hc.getVert_injOn' (by change i ≤ c.length - 1; have h := (hBM i hi).2; omega)
      (by change j ≤ c.length - 1; have h := (hBM j hj).2; omega) hij
  have habv : c.getVert a ≠ c.getVert b := fun h => (ne_of_lt hab) (hinjA ha hb h)
  have hwyv : c.getVert w ≠ c.getVert y := fun h => hyw (hinjB hw hyB h).symm
  have hw'yv : c.getVert w' ≠ c.getVert y := fun h => hyw' (hinjB hw' hyB h).symm
  let X := (B.image c.getVert).erase (c.getVert y)
  let Y := ((A.image c.getVert).erase (c.getVert a)).erase (c.getVert b)
  have hX : X.card = Q + 2 := by
    dsimp [X]
    rw [card_erase_of_mem (mem_image.mpr ⟨y, hyB, rfl⟩), card_image_of_injOn hinjB, hB]
    omega
  have hY : Y.card = Q := by
    dsimp [Y]
    rw [card_erase_of_mem (mem_erase.mpr ⟨habv.symm, mem_image.mpr ⟨b, hb, rfl⟩⟩),
      card_erase_of_mem (mem_image.mpr ⟨a, ha, rfl⟩), card_image_of_injOn hinjA, hA]
    omega
  have hXYcomplete (x : V) (hx : x ∈ X) (v : V) (hv : v ∈ Y) : G.Adj x v := by
    obtain ⟨i, hi, rfl⟩ := mem_image.mp (mem_of_mem_erase hx)
    obtain ⟨j, hj, rfl⟩ := mem_image.mp (mem_of_mem_erase (mem_of_mem_erase hv))
    exact (hcomplete j hj i hi).symm
  have hXY : Disjoint X Y := by
    rw [Finset.disjoint_left]
    intro x hx hy
    exact (hXYcomplete x hx x hy).ne rfl
  obtain ⟨p, hp, hlen, havoidA, havoidB⟩ := exists_long_path_between_cycle_intervals c hc a b w y w'
    hab (by omega) hwy hywlt hwlen (hcomplete a ha y hyB) (hcomplete b hb y hyB)
  refine ⟨X, Y, hX, hY, hXY, hXYcomplete, c.getVert w',
    mem_erase.mpr ⟨hw'yv, mem_image.mpr ⟨w', hw', rfl⟩⟩,
    c.getVert w, mem_erase.mpr ⟨hwyv, mem_image.mpr ⟨w, hw, rfl⟩⟩,
    (fun h => (ne_of_lt hww) (hinjB hw' hw h).symm), p, hp, ?_, ?_, ?_⟩
  · have hd := hdiam w hw w' hw'
    omega
  · have h₁ := hparA a ha b hb
    have h₂ := hparB w hw w' hw'
    omega
  · intro v hv hvXY
    rcases mem_union.mp hvXY with hvX | hvY
    · have hvy := (mem_erase.mp hvX).1
      obtain ⟨i, hi, hiv⟩ := mem_image.mp (mem_of_mem_erase hvX)
      by_cases hiw : i = w
      · right
        rw [← hiv, hiw]
      by_cases hiw' : i = w'
      · left
        rw [← hiv, hiw']
      have hwil : w ≤ i := B.min'_le i hi
      have hiwl : i ≤ w' := B.le_max' i hi
      have hiy : i ≠ y := fun h => hvy (by rw [← hiv, h])
      exact (havoidB i (by omega) (by omega) hiy (hiv ▸ hv)).elim
    · have hvb := (mem_erase.mp hvY).1
      have hva := (mem_erase.mp (mem_of_mem_erase hvY)).1
      obtain ⟨i, hi, hiv⟩ := mem_image.mp (mem_of_mem_erase (mem_of_mem_erase hvY))
      have hai : a ≤ i := A.min'_le i hi
      have hib : i ≤ b := A.le_max' i hi
      have hia : i ≠ a := fun h => hva (by rw [← hiv, h])
      have hib' : i ≠ b := fun h => hvb (by rw [← hiv, h])
      exact (havoidA i (by omega) (by omega) (hiv ▸ hv)).elim

#print axioms exists_internal_reservoir_from_intervals

end Erdos556
