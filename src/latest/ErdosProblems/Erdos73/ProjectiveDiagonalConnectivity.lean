import ErdosProblems.Erdos73.ProjectiveDiagonals

/-! Explicit paths to the root in the selected projective-grid diagonals. -/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

theorem projectiveDiagonal_top_even_reachable {n : ℕ} (hn : 2 ≤ n) (c : ℕ)
    (hc : c < n) (heven : c % 2 = 0) :
    (projectiveDiagonalGraph hn).Reachable (⟨0, by omega⟩, ⟨c, hc⟩) (projectiveRoot hn) := by
  induction c using Nat.strong_induction_on with
  | h c ih =>
    by_cases hz : c = 0
    · subst c
      exact .refl _
    have htwo : 2 ≤ c := by omega
    have hrec := ih (c - 2) (by omega) (by omega) (by omega)
    have hfirst := projectiveDiagonal_adj_top_switch hn (c - 1) (by omega) (by omega)
    have hsecond := projectiveDiagonal_adj_southeast hn 0 (c - 2) (by omega)
      (by omega) (Or.inr (by omega))
    have he₁ : c - 1 + 1 = c := by omega
    have he₂ : c - 2 + 1 = c - 1 := by omega
    simp only [he₁] at hfirst
    simp only [he₂] at hsecond
    exact hfirst.reachable.trans (hsecond.reachable.symm.trans hrec)

theorem projectiveDiagonal_even_reachable {n : ℕ} (hn : 2 ≤ n) (r c : ℕ)
    (hr : r < n) (hc : c < n) (heven : (r + c) % 2 = 0) :
    (projectiveDiagonalGraph hn).Reachable (⟨r, hr⟩, ⟨c, hc⟩) (projectiveRoot hn) := by
  induction r using Nat.strong_induction_on generalizing c with
  | h r ih =>
    by_cases hr0 : r = 0
    · subst r
      exact projectiveDiagonal_top_even_reachable hn c hc (by omega)
    by_cases hc0 : c = 0
    · subst c
      exact (projectiveDiagonal_adj_left_even hn ⟨r, hr⟩
        (show 0 < r by omega) (by simpa only [Nat.add_zero] using heven)).reachable.symm
    have hrec := ih (r - 1) (by omega) (c - 1) (by omega) (by omega) (by omega)
    have hadj := projectiveDiagonal_adj_southeast hn (r - 1) (c - 1)
      (by omega) (by omega) (by omega)
    have her : r - 1 + 1 = r := by omega
    have hec : c - 1 + 1 = c := by omega
    simp only [her, hec] at hadj
    exact hadj.reachable.symm.trans hrec

theorem projectiveDiagonal_odd_positive_row_reachable {n : ℕ} (hn : 2 ≤ n)
    (hnEven : n % 2 = 0) (r c : ℕ) (hr0 : 0 < r) (hr : r < n) (hc : c < n)
    (hodd : (r + c) % 2 = 1) :
    (projectiveDiagonalGraph hn).Reachable (⟨r, hr⟩, ⟨c, hc⟩) (projectiveRoot hn) := by
  generalize hm : n - r = m
  induction m using Nat.strong_induction_on generalizing r c with
  | h m ih =>
    by_cases hright : c + 1 = n
    · have her : r % 2 = 0 := by omega
      have hh := (projectiveDiagonal_adj_right_even hn hnEven ⟨r, hr⟩ her).reachable.symm
      convert hh using 1
      apply Prod.ext <;> apply Fin.ext <;> dsimp only <;> omega
    by_cases hbottom : r + 1 = n
    · have hec : c % 2 = 0 := by omega
      have hc' : c + 1 < n := by omega
      have hadj := projectiveDiagonal_adj_wrap hn c hc'
      have ht := projectiveDiagonal_top_even_reachable hn (n - 2 - c) (by omega) (by omega)
      have hh := hadj.reachable.trans ht
      convert hh using 1
      apply Prod.ext <;> apply Fin.ext <;> dsimp only <;> omega
    have hrec := ih (n - (r + 1)) (by omega) (r + 1) (c + 1)
      (by omega) (by omega) (by omega) (by omega) rfl
    have hadj := projectiveDiagonal_adj_southeast hn r c (by omega) (by omega)
      (Or.inl (by omega))
    exact hadj.reachable.trans hrec

theorem projectiveDiagonal_reachable_root {n : ℕ} (hn : 2 ≤ n) (hnEven : n % 2 = 0)
    (v : Fin n × Fin n) :
    (projectiveDiagonalGraph hn).Reachable v (projectiveRoot hn) := by
  rcases v with ⟨⟨r, hr⟩, ⟨c, hc⟩⟩
  by_cases heven : (r + c) % 2 = 0
  · exact projectiveDiagonal_even_reachable hn r c hr hc heven
  have hodd : (r + c) % 2 = 1 := by omega
  by_cases hr0 : 0 < r
  · exact projectiveDiagonal_odd_positive_row_reachable hn hnEven r c hr0 hr hc hodd
  have hrzero : r = 0 := by omega
  subst r
  by_cases hright : c + 1 = n
  · have hh := (projectiveDiagonal_adj_right_even hn hnEven ⟨0, by omega⟩ rfl).reachable.symm
    convert hh using 1
    apply Prod.ext <;> apply Fin.ext <;> dsimp only <;> omega
  have hwrap := projectiveDiagonal_adj_wrap hn (n - 2 - c) (by omega)
  have hbot := projectiveDiagonal_even_reachable hn (n - 1) (n - 2 - c)
    (by omega) (by omega) (by omega)
  have hh := hwrap.reachable.symm.trans hbot
  convert hh using 1
  apply Prod.ext <;> apply Fin.ext <;> dsimp only <;> omega

theorem projectiveDiagonal_connected {n : ℕ} (hn : 2 ≤ n) (hnEven : n % 2 = 0) :
    (projectiveDiagonalGraph hn).Connected := by
  let : Nonempty (Fin n × Fin n) := ⟨projectiveRoot hn⟩
  refine ⟨fun u v => ?_⟩
  exact (projectiveDiagonal_reachable_root hn hnEven u).trans
    (projectiveDiagonal_reachable_root hn hnEven v).symm

end
end Erdos73
