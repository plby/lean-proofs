import ErdosProblems.Erdos192.BlockDecomposition
import ErdosProblems.Erdos192.BoundaryDefs

namespace Erdos192

theorem count_flatMap_sum {α β : Type*} [DecidableEq β]
    (l : List α) (f : α → List β) (b : β) :
    (l.flatMap f).count b = (l.map (fun a => (f a).count b)).sum := by
  induction l <;> aesop

theorem applyKeranenG_append (l1 l2 : List (Fin 4)) :
    applyKeranenG (l1 ++ l2) = applyKeranenG l1 ++ applyKeranenG l2 := by
  simp [applyKeranenG, List.flatMap_append]

/-! ### List splitting -/

theorem list_take_split {α : Type*} (l : List α) (a b : ℕ) (h : a + b ≤ l.length) :
    l.take (a + b) = l.take a ++ (l.drop a |>.take b) := by
  rw [ List.take_add ]

theorem applyKeranenG_singleton (a : Fin 4) :
    applyKeranenG [a] = keranenG a := by
  simp [applyKeranenG]

/-! ### Count decomposition lemmas -/

/-
Count of g(w.take k) = g(w[0]).count + g(inner_left).count, for k ≥ 1.
-/
theorem count_take_split_head (w : List (Fin 4)) (k : ℕ) (c : Fin 4)
    (hk : 1 ≤ k) (hkw : k ≤ w.length) :
    (applyKeranenG (w.take k)).count c =
    (keranenG (w.get ⟨0, by omega⟩)).count c +
    (applyKeranenG (w.drop 1 |>.take (k - 1))).count c := by
  cases w with
  | nil => simp at hkw; omega
  | cons a w =>
    cases k with
    | zero => omega
    | succ k => simp [applyKeranenG, List.count_append]

/-
Count of g(w.take (m-1)) splits as g(w[0]) + g(inner_left) + g(w[k]) + g(inner_right).
-/
theorem count_take_full_split (w : List (Fin 4)) (k m : ℕ) (c : Fin 4)
    (hk1 : 1 ≤ k) (hk2 : k + 2 ≤ m) (hm : m ≤ w.length) :
    (applyKeranenG (w.take (m - 1))).count c =
    (keranenG (w.get ⟨0, by omega⟩)).count c +
    (applyKeranenG (w.drop 1 |>.take (k - 1))).count c +
    (keranenG (w.get ⟨k, by omega⟩)).count c +
    (applyKeranenG (w.drop (k + 1) |>.take (m - 2 - k))).count c := by
  -- Apply the count_take_split_head lemma to split the count into the sum of the counts of the individual parts.
  have h_split : List.count c (applyKeranenG (List.take (m - 1) w)) = List.count c (applyKeranenG (List.take k w)) + List.count c (applyKeranenG (List.take (m - 1 - k) (List.drop k w))) := by
    rw [ show List.take ( m - 1 ) w = List.take k w ++ List.take ( m - 1 - k ) ( List.drop k w ) from ?_, applyKeranenG_append ];
    · rw [ List.count_append ];
    · rw [ ← List.take_add, Nat.add_sub_of_le ( by omega ) ];
  rw [ h_split, count_take_split_head ];
  convert congr_arg _ ( count_take_split_head _ _ _ _ _ ) using 1;
  all_goals norm_num [ Nat.sub_sub ];
  grind;
  · omega;
  · omega;
  · linarith;
  · linarith

/-! ### Parikh matrix identity -/

def parikhM (c a : Fin 4) : ℕ := (keranenG a).count c

def adjRow (row : Fin 4) (v : Fin 4 → Int) : Int :=
  match row with
  | 0 => -701 * v 0 + (-531) * v 1 + 4059 * v 2 + (-2316) * v 3
  | 1 => (-2316) * v 0 + (-701) * v 1 + (-531) * v 2 + 4059 * v 3
  | 2 => 4059 * v 0 + (-2316) * v 1 + (-701) * v 2 + (-531) * v 3
  | 3 => (-531) * v 0 + 4059 * v 1 + (-2316) * v 2 + (-701) * v 3

theorem adj_times_M :
    ∀ c d : Fin 4,
      adjRow c (fun j => (parikhM j d : Int)) =
      43435 * (if c = d then 1 else 0) := by decide +kernel

/-! ### Map sum regrouping -/

/-
For Fin 4 lists: (l.map f).sum = Σ_a f(a) * l.count a
-/
theorem map_sum_eq_weighted_count (l : List (Fin 4)) (f : Fin 4 → ℕ) :
    (l.map f).sum = f 0 * l.count 0 + f 1 * l.count 1 + f 2 * l.count 2 + f 3 * l.count 3 := by
  induction' l with x xs ih;
  · rfl;
  · fin_cases x <;> simp +decide only [Fin.mk_one, Fin.isValue, List.map_cons, List.sum_cons, ne_eq, one_ne_zero,
    not_false_eq_true, List.count_cons_of_ne, List.count_cons_self, Fin.reduceEq, Fin.reduceFinMk,
    Fin.zero_eta, zero_ne_one] <;> linarith!

/-! ### Main bridge -/

/-
Core inner count identity: the Parikh bridge equation.
-/
theorem inner_count_bridge (w : List (Fin 4)) (r L : ℕ) (c : Fin 4)
    (hm_ge : w.length ≥ 3) (hL : L > 0) (hr : r < 85)
    (hlen : r + 2 * L ≤ 85 * w.length)
    (hspan : (r + 2 * L - 1) / 85 + 1 = w.length)
    (hperm : ((applyKeranenG w).drop r |>.take L).Perm
             ((applyKeranenG w).drop (r + L) |>.take L)) :
    let k := (r + L) / 85
    let s := (r + L) % 85
    let m := w.length
    let t := r + 2 * L - 85 * (m - 1)
    ((applyKeranenG (w.drop 1 |>.take (k - 1))).count c : Int) -
    ((applyKeranenG (w.drop (k + 1) |>.take (m - 2 - k))).count c : Int) =
    boundaryDelta (w.get ⟨0, by omega⟩) (w.get ⟨k, by omega⟩) (w.get ⟨m - 1, by omega⟩) r s c +
    (if t = 85 then ((keranenG (w.get ⟨m - 1, by omega⟩)).count c : Int) else 0) := by
  refine' Eq.symm ( _ );
  have h_eq : 2 * ((applyKeranenG (w.take ((r + L) / 85))).count c + ((keranenG (w.get ⟨(r + L) / 85, by
    omega⟩)).take ((r + L) % 85)).count c) =
    ((keranenG (w.get ⟨0, by
      linarith⟩)).take r).count c +
    ((applyKeranenG (w.take (w.length - 1))).count c) +
    ((keranenG (w.get ⟨w.length - 1, by
      exact Nat.pred_lt ( ne_bot_of_gt hm_ge )⟩)).take (r + 2 * L - 85 * (w.length - 1))).count c := by
      all_goals generalize_proofs at *;
      have h_eq : 2 * ((applyKeranenG w).take (r + L)).count c = ((applyKeranenG w).take r).count c + ((applyKeranenG w).take (r + 2 * L)).count c := by
        have h_eq : ((applyKeranenG w).take (r + L)).count c - ((applyKeranenG w).take r).count c = ((applyKeranenG w).take (r + 2 * L)).count c - ((applyKeranenG w).take (r + L)).count c := by
          have h_eq : ((applyKeranenG w).drop r |>.take L).count c = ((applyKeranenG w).drop (r + L) |>.take L).count c := by
            exact hperm.count_eq _;
          convert h_eq using 1;
          · grind;
          · rw [ show r + 2 * L = ( r + L ) + L by ring, List.take_add ];
            rw [ List.count_append, add_tsub_cancel_left ];
        grind;
      have h_eq : ((applyKeranenG w).take (r + L)).count c = ((applyKeranenG (w.take ((r + L) / 85))).count c) + ((keranenG (w.get ⟨(r + L) / 85, by
        assumption⟩)).take ((r + L) % 85)).count c := by
        all_goals generalize_proofs at *;
        rw [ ← List.count_append, ← applyKeranenG_take_blocks ];
        · rw [ Nat.div_add_mod ];
        · exact Nat.le_of_lt ( Nat.mod_lt _ ( by decide ) )
      generalize_proofs at *;
      have h_eq : ((applyKeranenG w).take (r + 2 * L)).count c = ((applyKeranenG (w.take (w.length - 1))).count c) + ((keranenG (w.get ⟨w.length - 1, by
        grind +splitImp⟩)).take (r + 2 * L - 85 * (w.length - 1))).count c := by
        all_goals generalize_proofs at *;
        have h_eq : (applyKeranenG w).take (r + 2 * L) = applyKeranenG (w.take (w.length - 1)) ++ (keranenG (w.get ⟨w.length - 1, by
          grind +splitImp⟩)).take (r + 2 * L - 85 * (w.length - 1)) := by
          all_goals generalize_proofs at *;
          convert applyKeranenG_take_blocks w ( w.length - 1 ) ( r + 2 * L - 85 * ( w.length - 1 ) ) _ _ using 1 <;> norm_num [ hspan.symm ];
          · rw [ Nat.add_sub_of_le ( by omega ) ];
          · omega
        generalize_proofs at *;
        rw [ h_eq, List.count_append ]
      generalize_proofs at *;
      have h_eq : ((applyKeranenG w).take r).count c = ((keranenG (w.get ⟨0, by
        linarith⟩)).take r).count c := by
        all_goals generalize_proofs at *;
        have h_eq : (applyKeranenG w).take r = (keranenG (w.get ⟨0, by
          linarith⟩)).take r := by
          all_goals generalize_proofs at *;
          convert applyKeranenG_take_blocks w 0 r (by omega) hr.le using 1 <;> simp [applyKeranenG]
        generalize_proofs at *;
        rw [h_eq]
      generalize_proofs at *;
      grind
  generalize_proofs at *;
  by_cases hk : 1 ≤ (r + L) / 85;
  · have h_eq : (applyKeranenG (w.take ((r + L) / 85))).count c = ((keranenG (w.get ⟨0, by
      linarith⟩)).count c) + ((applyKeranenG (w.drop 1 |>.take ((r + L) / 85 - 1))).count c) := by
      all_goals generalize_proofs at *;
      convert count_take_split_head w ( ( r + L ) / 85 ) c hk ( by omega ) using 1
    generalize_proofs at *;
    have h_eq : (applyKeranenG (w.take (w.length - 1))).count c = ((keranenG (w.get ⟨0, by
      linarith⟩)).count c) + ((applyKeranenG (w.drop 1 |>.take ((r + L) / 85 - 1))).count c) + ((keranenG (w.get ⟨(r + L) / 85, by
      assumption⟩)).count c) + ((applyKeranenG (w.drop ((r + L) / 85 + 1) |>.take (w.length - 2 - (r + L) / 85))).count c) := by
      all_goals generalize_proofs at *;
      convert count_take_full_split w ( ( r + L ) / 85 ) w.length c hk ( by omega ) ( by omega ) using 1
    generalize_proofs at *;
    unfold boundaryDelta;
    unfold sliceParikhCount;
    unfold cumParikhCount;
    split_ifs <;> simp_all +decide only [List.get_eq_getElem, Nat.reduceMul, List.take_zero, List.nodup_nil,
    List.count_nil, CharP.cast_eq_zero, sub_zero, List.drop_one, add_zero];
    · rw [ show ( 2 * ( ( r + L ) % 85 ) + 85000 - r ) % 85 = 0 from ?_ ] ; norm_num ; ring_nf;
      · rw [ show List.take 85 ( keranenG w[0] ) = keranenG w[0] from ?_, show List.take 85 ( keranenG w[w.length - 1] ) = keranenG w[w.length - 1] from ?_ ] at * <;> norm_num at *;
        · rw [ show List.take 85 ( keranenG w[(r + L) / 85] ) = keranenG w[(r + L) / 85] from ?_ ] at * ; norm_num at *;
          · grind;
          · rw [ List.take_of_length_le ] ; norm_num [ keranenG_length ];
        · exact le_of_eq ( keranenG_length _ );
        · exact le_of_eq ( keranenG_length _ );
      · omega;
    · rw [ show List.take 85 ( keranenG w[(r + L) / 85] ) = keranenG w[(r + L) / 85] from ?_, show List.take 85 ( keranenG w[0] ) = keranenG w[0] from ?_ ];
      · rw [ show ( 2 * ( ( r + L ) % 85 ) + 85000 - r ) % 85 = ( r + 2 * L - 85 * ( w.length - 1 ) ) % 85 from ?_ ];
        · rw [ show ( r + 2 * L - 85 * ( w.length - 1 ) ) % 85 = ( r + 2 * L - 85 * ( w.length - 1 ) ) from ?_ ];
          · grind;
          · omega;
        · omega;
      · exact List.take_of_length_le ( by simp +decide [ keranenG_length ] );
      · exact List.take_of_length_le ( by simp +decide [ keranenG_length ] );
  · omega

/-! ### Helper lemmas for the algebraic chain -/

/-- flatMap count = Parikh matrix times letter-count vector -/
theorem applyKeranenG_count_as_sum (l : List (Fin 4)) (c : Fin 4) :
    (applyKeranenG l).count c =
    parikhM c 0 * l.count 0 + parikhM c 1 * l.count 1 +
    parikhM c 2 * l.count 2 + parikhM c 3 * l.count 3 := by
  unfold applyKeranenG parikhM
  rw [count_flatMap_sum, map_sum_eq_weighted_count]

/-- adjRow is linear over 4 terms -/
private theorem adjRow_linear4 (d : Fin 4) (x : Fin 4 → Int) (f : Fin 4 → Fin 4 → Int) :
    adjRow d (fun c => x 0 * f 0 c + x 1 * f 1 c + x 2 * f 2 c + x 3 * f 3 c) =
    x 0 * adjRow d (f 0) + x 1 * adjRow d (f 1) + x 2 * adjRow d (f 2) + x 3 * adjRow d (f 3) := by
  fin_cases d <;> simp [adjRow] <;> ring

/-- If M·x = δ (as Fin 4 sums), then 43435 * x d = adjRow d δ -/
theorem adj_solve (v : Fin 4 → Int) (δ : Fin 4 → Int) (d : Fin 4)
    (h : ∀ c : Fin 4, (parikhM c 0 : Int) * v 0 + (parikhM c 1 : Int) * v 1 +
                       (parikhM c 2 : Int) * v 2 + (parikhM c 3 : Int) * v 3 = δ c) :
    43435 * v d = adjRow d δ := by
  have hd : δ = fun c => (parikhM c 0 : Int) * v 0 + (parikhM c 1 : Int) * v 1 +
                 (parikhM c 2 : Int) * v 2 + (parikhM c 3 : Int) * v 3 := by
    ext c; exact (h c).symm
  subst hd
  rw [show (fun c => (↑(parikhM c 0)) * v 0 + (↑(parikhM c 1)) * v 1 +
                 (↑(parikhM c 2)) * v 2 + (↑(parikhM c 3)) * v 3) =
    (fun c => v 0 * (↑(parikhM c 0)) + v 1 * (↑(parikhM c 1)) +
              v 2 * (↑(parikhM c 2)) + v 3 * (↑(parikhM c 3))) from by ext; ring]
  rw [adjRow_linear4 d v (fun a c => (parikhM c a : Int))]
  simp only [adj_times_M]
  fin_cases d <;> simp <;> ring

/-- adjMTtimesDelta equals adjRow applied to boundaryDelta -/
theorem adjMTtimesDelta_eq_adjRow (wa wb we : Fin 4) (r s : ℕ) (d : Fin 4) :
    adjMTtimesDelta wa wb we r s d = adjRow d (boundaryDelta wa wb we r s) := by
  fin_cases d <;> simp [adjMTtimesDelta, adjRow]

/-- adjRow is additive -/
theorem adjRow_add (d : Fin 4) (f g : Fin 4 → Int) :
    adjRow d (fun c => f c + g c) = adjRow d f + adjRow d g := by
  fin_cases d <;> simp [adjRow] <;> ring

/-- adjRow of scaled indicator -/
theorem adjRow_ite_parikhM (d we : Fin 4) :
    adjRow d (fun c => (parikhM c we : Int)) = 43435 * if d = we then 1 else 0 := by
  exact adj_times_M d we

end Erdos192
