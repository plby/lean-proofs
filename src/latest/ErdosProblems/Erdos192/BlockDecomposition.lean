import ErdosProblems.Erdos192.Core

namespace Erdos192

theorem applyKeranenG_take_blocks (w : List (Fin 4)) (k s : ℕ)
    (hk : k < w.length) (hs : s ≤ 85) :
    (applyKeranenG w).take (85 * k + s) =
    applyKeranenG (w.take k) ++ (keranenG (w.get ⟨k, hk⟩)).take s := by
  induction' k with k ih generalizing w s
  · rcases w with ( _ | ⟨ x, _ | ⟨ y, w ⟩ ⟩ ) <;> simp_all +decide [ applyKeranenG ]
    · contradiction
    · exact Or.inr ( by rw [ keranenG_length ] ; linarith )
  · rcases w with ( _ | ⟨ a, _ | ⟨ b, w ⟩ ⟩ ) <;> simp_all +decide [ Nat.mul_succ, List.take_append_of_le_length ]
    · contradiction
    · contradiction
    · simp_all +decide [ applyKeranenG ]
      rw [ ← ih ]
      · simp +arith +decide [ List.take_append, keranenG_length ]
      · grind
      · grind

/-- Count in a slice of g(w) equals the take-difference. -/
theorem count_applyKeranenG_slice (w : List (Fin 4)) (a b : ℕ) (c : Fin 4)
    (hab : a ≤ b) (hb : b ≤ (applyKeranenG w).length) :
    ((applyKeranenG w).drop a |>.take (b - a)).count c =
    ((applyKeranenG w).take b).count c -
    ((applyKeranenG w).take a).count c := by
  rw [ eq_comm, tsub_eq_of_eq_add ]
  rw [ show List.take b ( applyKeranenG w ) = List.take a ( applyKeranenG w ) ++ List.take ( b - a ) ( List.drop a ( applyKeranenG w ) ) from ?_, List.count_append ]
  · ring
  · rw [ ← List.take_add, Nat.add_sub_of_le hab ]

end Erdos192
