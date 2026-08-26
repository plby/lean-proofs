import ErdosProblems.Erdos192.ShortCheck
import ErdosProblems.Erdos192.Spanning
import ErdosProblems.Erdos192.Localization

namespace Erdos192

theorem morphism_preserves_le2 (w : List (Fin 4)) (hw : FinAbelianSquareFree w)
    (hlen : w.length ≤ 2) : FinAbelianSquareFree (applyKeranenG w) := by
  cases w with
  | nil => intro i l hl h; simp [applyKeranenG] at h; omega
  | cons a w =>
    cases w with
    | nil =>
      have hab : a ≠ a + 1 := by fin_cases a <;> decide
      have h := finASF_prefix (applyKeranenG [a, a + 1]) (keranen_pair_asf a (a + 1) hab)
        85 (by simp [applyKeranenG_length])
      simpa [applyKeranenG, List.take_append, keranenG_length,
        List.take_of_length_le (le_of_eq (keranenG_length a))] using h
    | cons b w =>
      cases w with
      | nil =>
        apply keranen_pair_asf a b
        intro hab
        subst b
        exact hw 0 1 (by decide) (by simp) (List.Perm.refl [a])
      | cons c w => simp at hlen

/-- Any square spanning at least three blocks descends to the preimage;
the remaining one- and two-block cases are checked by a streaming certificate. -/
theorem keranenG_preserves_ASF (w : List (Fin 4)) (hw : FinAbelianSquareFree w) :
    FinAbelianSquareFree (applyKeranenG w) := by
  intro i L hL hlen hperm
  let a := i / 85
  let m := (i + 2 * L - 1) / 85 - a + 1
  let r := i % 85
  let w' := w.drop a |>.take m
  have ham : a + m ≤ w.length := by
    rw [applyKeranenG_length] at hlen
    dsimp [a, m]
    omega
  have hw' : FinAbelianSquareFree w' := finASF_subword w hw a m ham
  have hwlen : w'.length = m := by
    simp only [w', List.length_take, List.length_drop]
    omega
  obtain ⟨hlen', hperm'⟩ := abelianSquare_localize_explicit w i L hL hlen hperm
  have hspan : (r + 2 * L - 1) / 85 + 1 = w'.length := by
    rw [hwlen]
    exact localized_block_span w i L hL hlen
  by_cases hm : m ≤ 2
  · exact morphism_preserves_le2 w' hw' (by omega) r L hL hlen' hperm'
  · exact no_spanning_large w' hw' (by omega) r L hL
      (Nat.mod_lt _ (by decide)) hlen' hspan hperm'

end Erdos192
