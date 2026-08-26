import ErdosProblems.Erdos192.Core

namespace Erdos192

theorem abelianSquare_localize_explicit (w : List (Fin 4))
    (i L : ℕ) (hL : L > 0)
    (hlen : i + 2 * L ≤ (applyKeranenG w).length)
    (hperm : ((applyKeranenG w).drop i |>.take L).Perm
             ((applyKeranenG w).drop (i + L) |>.take L)) :
    let a := i / 85
    let m := (i + 2 * L - 1) / 85 - a + 1
    let r := i % 85
    let w' := w.drop a |>.take m
    (r + 2 * L ≤ (applyKeranenG w').length) ∧
    ((applyKeranenG w').drop r |>.take L).Perm
      ((applyKeranenG w').drop (r + L) |>.take L) := by
  refine' ⟨ _, _ ⟩;
  · rw [ applyKeranenG_length ] at *;
    simp +arith +decide [ List.length_take, List.length_drop ];
    omega;
  · have h_localize : List.drop i (applyKeranenG w) = List.drop (i % 85) (applyKeranenG (List.drop (i / 85) w)) ∧ List.drop (i + L) (applyKeranenG w) = List.drop (i % 85 + L) (applyKeranenG (List.drop (i / 85) w)) := by
      have h_localize : ∀ (a : ℕ) (w : List (Fin 4)), List.drop (85 * a) (applyKeranenG w) = applyKeranenG (List.drop a w) := by
        intro a w; induction' a with a ih generalizing w <;> simp_all +decide [ List.drop ] ;
        rcases w <;> simp_all +decide [ Nat.mul_succ, List.drop ];
        · rfl;
        · simp_all +decide [ applyKeranenG, List.drop_append ];
          simp_all +decide [ keranenG_length ];
      rw [ ← h_localize ];
      constructor <;> rw [ List.drop_drop ] <;> congr 1 <;> omega;
    have h_localize : applyKeranenG (List.drop (i / 85) w) = applyKeranenG (List.take ((i + 2 * L - 1) / 85 - i / 85 + 1) (List.drop (i / 85) w)) ++ applyKeranenG (List.drop ((i + 2 * L - 1) / 85 - i / 85 + 1) (List.drop (i / 85) w)) := by
      unfold applyKeranenG; simp +decide ;
      rw [ ← List.take_append_drop ( ( i + 2 * L - 1 ) / 85 - i / 85 + 1 ) ( List.drop ( i / 85 ) w ), List.flatMap_append ];
      simp +decide [ List.drop_drop ];
    have h_localize : List.take L (List.drop (i % 85) (applyKeranenG (List.drop (i / 85) w))) = List.take L (List.drop (i % 85) (applyKeranenG (List.take ((i + 2 * L - 1) / 85 - i / 85 + 1) (List.drop (i / 85) w)))) ∧ List.take L (List.drop (i % 85 + L) (applyKeranenG (List.drop (i / 85) w))) = List.take L (List.drop (i % 85 + L) (applyKeranenG (List.take ((i + 2 * L - 1) / 85 - i / 85 + 1) (List.drop (i / 85) w)))) := by
      rw [ h_localize ];
      rw [ List.drop_append, List.drop_append ];
      constructor <;> rw [ List.take_append_of_le_length ];
      · simp +arith +decide [ applyKeranenG_length ];
        rw [ applyKeranenG_length ] at hlen;
        omega;
      · simp +arith +decide [ applyKeranenG_length ];
        rw [ applyKeranenG_length ] at hlen;
        omega;
    lia

theorem localized_block_span (w : List (Fin 4)) (i L : ℕ) (_hL : L > 0)
    (_hlen : i + 2 * L ≤ (applyKeranenG w).length) :
    let a := i / 85
    let m := (i + 2 * L - 1) / 85 - a + 1
    let r := i % 85
    (r + 2 * L - 1) / 85 + 1 = m := by
  omega

/-! ### Spanning contradiction lemmas -/

/-
No ASF word of length 6 has a spanning Perm-based abelian square.
-/
end Erdos192
