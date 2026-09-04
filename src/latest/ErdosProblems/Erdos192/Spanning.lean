import ErdosProblems.Erdos192.SpanningAlgebra
import ErdosProblems.Erdos192.BoundaryCheck

namespace Erdos192

theorem inner_defect_gives_AS (w : List (Fin 4))
    (hm_ge : w.length ≥ 3) (r L : ℕ) (hL : L > 0) (hr : r < 85)
    (hlen : r + 2 * L ≤ 85 * w.length)
    (hspan : (r + 2 * L - 1) / 85 + 1 = w.length)
    (hperm : ((applyKeranenG w).drop r |>.take L).Perm
             ((applyKeranenG w).drop (r + L) |>.take L)) :
    let k := (r + L) / 85
    let s := (r + L) % 85
    let m := w.length
    let t := r + 2 * L - 85 * (m - 1)
    let wa := w.get ⟨0, by omega⟩
    let wb := w.get ⟨k, by omega⟩
    let we := w.get ⟨m - 1, by omega⟩
    let inner_left := w.drop 1 |>.take (k - 1)
    let inner_right := w.drop (k + 1) |>.take (m - 2 - k)
    let v : Fin 4 → Int := fun a => (inner_left.count a : Int) - (inner_right.count a : Int)
    vGivesSomeAS wa wb we v = true := by
  have h_inner_count_bridge : ∀ c : Fin 4, ((List.count c (applyKeranenG (w.drop 1 |>.take ((r + L) / 85 - 1))) : Int) - (List.count c (applyKeranenG (w.drop ((r + L) / 85 + 1) |>.take (w.length - 2 - ((r + L) / 85)))) : Int)) = boundaryDelta (w.get ⟨0, by omega⟩) (w.get ⟨(r + L) / 85, by omega⟩) (w.get ⟨w.length - 1, by omega⟩) r ((r + L) % 85) c + (if (r + 2 * L - 85 * (w.length - 1)) = 85 then (List.count c (keranenG (w.get ⟨w.length - 1, by omega⟩)) : Int) else 0) := by
    intros c
    apply inner_count_bridge w r L c hm_ge hL hr hlen hspan hperm;
  have h_parikhSolutionVec_applyKeranenG : ∀ a : Fin 4, ∀ l : List (Fin 4), (List.count a (applyKeranenG l) : Int) = ∑ c : Fin 4, (parikhM a c : Int) * (List.count c l) := by
    intros a l
    have h_applyKeranenG_count_as_sum : (List.count a (applyKeranenG l) : Int) = ∑ c : Fin 4, (parikhM a c : Int) * (List.count c l) := by
      have := applyKeranenG_count_as_sum l a
      simp +decide [ this, Fin.sum_univ_four ];
    convert h_applyKeranenG_count_as_sum using 1;
  have h_adj_solve : ∀ a : Fin 4, 43435 * (List.count a (List.take ((r + L) / 85 - 1) (List.drop 1 w)) - List.count a (List.take (w.length - 2 - ((r + L) / 85)) (List.drop ((r + L) / 85 + 1) w)) : ℤ) = adjRow a (boundaryDelta (w.get ⟨0, by omega⟩) (w.get ⟨(r + L) / 85, by omega⟩) (w.get ⟨w.length - 1, by omega⟩) r ((r + L) % 85)) + (if (r + 2 * L - 85 * (w.length - 1)) = 85 then adjRow a (fun c => (parikhM c (w.get ⟨w.length - 1, by omega⟩) : ℤ)) else 0) := by
    intro a
    have h_adj_solve_step : ∑ c : Fin 4, (parikhM a c : ℤ) * (List.count c (List.take ((r + L) / 85 - 1) (List.drop 1 w)) - List.count c (List.take (w.length - 2 - ((r + L) / 85)) (List.drop ((r + L) / 85 + 1) w)) : ℤ) = boundaryDelta (w.get ⟨0, by omega⟩) (w.get ⟨(r + L) / 85, by omega⟩) (w.get ⟨w.length - 1, by omega⟩) r ((r + L) % 85) a + (if (r + 2 * L - 85 * (w.length - 1)) = 85 then (List.count a (keranenG (w.get ⟨w.length - 1, by omega⟩)) : ℤ) else 0) := by
      convert h_inner_count_bridge a using 1;
      simp +decide [ h_parikhSolutionVec_applyKeranenG, mul_sub ];
    convert adj_solve ( fun c => ( List.count c ( List.take ( ( r + L ) / 85 - 1 ) ( List.drop 1 w ) ) - List.count c ( List.take ( w.length - 2 - ( r + L ) / 85 ) ( List.drop ( ( r + L ) / 85 + 1 ) w ) ) : ℤ ) ) ( fun c => boundaryDelta ( w.get ⟨ 0, by omega ⟩ ) ( w.get ⟨ ( r + L ) / 85, by omega ⟩ ) ( w.get ⟨ w.length - 1, by omega ⟩ ) r ( ( r + L ) % 85 ) c + if r + 2 * L - 85 * ( w.length - 1 ) = 85 then ( List.count c ( keranenG ( w.get ⟨ w.length - 1, by omega ⟩ ) ) : ℤ ) else 0 ) a _ using 1;
    · split_ifs <;> simp +decide [ *, adjRow_add ];
      rfl;
    · intro c; specialize h_inner_count_bridge c; simp_all +decide [ Fin.sum_univ_four ] ;
      grind;
  have h_adj_solve : ∀ a : Fin 4, adjRow a (boundaryDelta (w.get ⟨0, by omega⟩) (w.get ⟨(r + L) / 85, by omega⟩) (w.get ⟨w.length - 1, by omega⟩) r ((r + L) % 85)) % 43435 = 0 := by
    intro a
    specialize h_adj_solve a
    have h_div : 43435 ∣ adjRow a (boundaryDelta (w.get ⟨0, by omega⟩) (w.get ⟨(r + L) / 85, by omega⟩) (w.get ⟨w.length - 1, by omega⟩) r ((r + L) % 85)) := by
      split_ifs at h_adj_solve <;> norm_num [ adjRow_ite_parikhM ] at h_adj_solve ⊢ <;> omega
    exact Int.emod_eq_zero_of_dvd h_div;
  by_cases h : r + 2 * L - 85 * ( w.length - 1 ) = 85 <;> simp_all +decide only [List.get_eq_getElem, List.drop_one];
  · have := v_pattern_gives_AS_t85 w[0] w[(r + L) / 85] w[w.length - 1] ⟨r, hr⟩ ⟨(r + L) % 85, Nat.mod_lt _ (by decide)⟩; simp_all +decide [ hasParikhSolution ] ;
    convert this _ _ _ _ _ using 2;
    any_goals omega;
    · ext c; specialize ‹∀ a : Fin 4, 43435 * ( ↑ ( List.count a ( List.take ( ( r + L ) / 85 - 1 ) w.tail ) ) - ↑ ( List.count a ( List.take ( w.length - 2 - ( r + L ) / 85 ) ( List.drop ( ( r + L ) / 85 + 1 ) w ) ) ) ) = adjRow a ( boundaryDelta w[0] w[( r + L ) / 85] w[w.length - 1] r ( ( r + L ) % 85 ) ) + if a = w[w.length - 1] then 43435 else 0› c; simp_all +decide [ parikhSolutionVec ] ;
      rw [ adjMTtimesDelta_eq_adjRow ];
      split_ifs at * <;> omega;
    · simpa only [adjMTtimesDelta_eq_adjRow] using h_adj_solve 0;
    · simpa only [adjMTtimesDelta_eq_adjRow] using h_adj_solve 1;
    · simpa only [adjMTtimesDelta_eq_adjRow] using h_adj_solve 2;
    · simpa only [adjMTtimesDelta_eq_adjRow] using h_adj_solve 3;
  · convert v_pattern_gives_AS_normal w[0] w[(r + L) / 85] w[w.length - 1] ⟨r, hr⟩ ⟨(r + L) % 85, Nat.mod_lt _ (by decide)⟩ _ using 1;
    · unfold parikhSolutionVec; simp +decide [ *, adjMTtimesDelta_eq_adjRow ] ;
      congr! 2;
      exact Eq.symm ( Int.ediv_eq_of_eq_mul_left ( by decide ) ( by linarith [ ‹∀ a : Fin 4, 43435 * ( ↑ ( List.count a ( List.take ( ( r + L ) / 85 - 1 ) w.tail ) ) - ↑ ( List.count a ( List.take ( w.length - 2 - ( r + L ) / 85 ) ( List.drop ( ( r + L ) / 85 + 1 ) w ) ) ) ) = adjRow a ( boundaryDelta w[0] w[( r + L ) / 85] w[w.length - 1] r ( ( r + L ) % 85 ) ) › ‹_› ] ) );
    · unfold hasParikhSolution; simp +decide [ h_adj_solve ] ;
      exact ⟨ ⟨ ⟨ h_adj_solve 0, h_adj_solve 1 ⟩, h_adj_solve 2 ⟩, h_adj_solve 3 ⟩

/-! ### List counting helpers -/

theorem sum_count_eq_length (l : List (Fin 4)) :
    (l.count 0 : Int) + l.count 1 + l.count 2 + l.count 3 = l.length := by
  induction l <;> simp +decide only [Fin.isValue, List.length_cons, Nat.cast_add, Nat.cast_one] ; ring_nf;
  rename_i k hk ih; fin_cases k <;> simp +decide [ List.count_cons ] at ih ⊢ <;> linarith;

private theorem indicator_sum_fin4 (a : Fin 4) :
    (if (0:Fin 4) = a then (1:Int) else 0) + (if 1 = a then 1 else 0) +
    (if 2 = a then 1 else 0) + (if 3 = a then 1 else 0) = 1 := by
  fin_cases a <;> simp

/-! ### Pattern-specific contradiction lemmas -/

private theorem case1_false (w : List (Fin 4)) (hw : FinAbelianSquareFree w)
    (k : ℕ) (hk1 : 1 ≤ k) (hkm : k < w.length) (hm : w.length = 2 * k + 1)
    (h : ∀ c : Fin 4, (if c = w.get ⟨0, by omega⟩ then (1:Int) else 0) -
      (if c = w.get ⟨k, hkm⟩ then 1 else 0) +
      ((w.drop 1 |>.take (k - 1)).count c : Int) -
      ((w.drop (k + 1) |>.take (k - 1)).count c : Int) = 0) : False := by
  -- Apply `hw` with `i = 0` and `l = k` to derive a contradiction.
  specialize hw 0 k hk1 (by linarith);
  contrapose! hw;
  rw [ List.perm_iff_count ];
  intro c; specialize h c; rcases k with ( _ | k ) <;> simp_all +decide only [List.drop_zero, zero_add] ;
  rcases w with ( _ | ⟨ x, _ | ⟨ y, w ⟩ ⟩ ) <;> simp_all +decide [ List.take_succ_cons ];
  · cases hm;
  · rw [ List.drop_eq_getElem_cons ];
    grind +qlia;
    grind

private theorem case2_false (w : List (Fin 4)) (hw : FinAbelianSquareFree w)
    (k : ℕ) (hk1 : 1 ≤ k) (hkm : k < w.length) (hm : w.length = 2 * k + 1)
    (h : ∀ c : Fin 4,
      ((w.drop 1 |>.take (k - 1)).count c : Int) -
      ((w.drop (k + 1) |>.take (k - 1)).count c : Int) +
      (if c = w.get ⟨k, hkm⟩ then (1:Int) else 0) -
      (if c = w.get ⟨w.length - 1, by omega⟩ then 1 else 0) = 0) : False := by
  convert hw 1 k ?_ ?_ using 1;
  · simp +zetaDelta only [List.drop_one, false_iff, Decidable.not_not] at *;
    rw [ List.perm_iff_count ];
    intro c; specialize h c; rcases k with ( _ | k ) <;> simp_all +decide [ List.take_add_one ] ;
    simp_all +decide [ two_mul, add_assoc, List.count ];
    grind;
  · linarith;
  · grind

private theorem case3_false (w : List (Fin 4)) (hw : FinAbelianSquareFree w)
    (k : ℕ) (hk1 : 2 ≤ k) (hkm : k < w.length) (hm : w.length = 2 * k)
    (h : ∀ c : Fin 4,
      ((w.drop 1 |>.take (k - 1)).count c : Int) -
      ((w.drop (k + 1) |>.take (k - 2)).count c : Int) -
      (if c = w.get ⟨k, hkm⟩ then (1:Int) else 0) = 0) : False := by
  have hbad := hw 1 (k - 1) (by omega) (by omega)
  apply hbad
  rw [List.perm_iff_count]
  intro c
  specialize h c
  have hsecond :
      (w.drop (1 + (k - 1)) |>.take (k - 1)) =
        w.get ⟨k, hkm⟩ :: (w.drop (k + 1) |>.take (k - 2)) := by
    rw [show 1 + (k - 1) = k by omega, List.drop_eq_getElem_cons hkm,
      show k - 1 = Nat.succ (k - 2) by omega]
    rfl
  grind

private theorem case4_false (w : List (Fin 4)) (hw : FinAbelianSquareFree w)
    (k : ℕ) (hk1 : 1 ≤ k) (hkm : k < w.length) (hm : w.length = 2 * k + 2)
    (h : ∀ c : Fin 4,
      ((w.drop 1 |>.take (k - 1)).count c : Int) -
      ((w.drop (k + 1) |>.take k).count c : Int) +
      (if c = w.get ⟨k, hkm⟩ then (1:Int) else 0) = 0) : False := by
  convert hw 1 k ?_ ?_ using 1;
  · simp +decide only [List.drop_one, false_iff, Decidable.not_not];
    intro c; specialize h c; rcases k with ( _ | k ) <;> simp_all +decide [ List.take_add_one ] ;
    grind +qlia;
  · linarith;
  · lia

private theorem case5_false (w : List (Fin 4)) (hw : FinAbelianSquareFree w)
    (k : ℕ) (hk1 : 1 ≤ k) (hkm : k < w.length) (hm : w.length = 2 * k)
    (h : ∀ c : Fin 4, (if c = w.get ⟨0, by omega⟩ then (1:Int) else 0) -
      (if c = w.get ⟨k, hkm⟩ then 1 else 0) -
      (if c = w.get ⟨w.length - 1, by omega⟩ then 1 else 0) +
      ((w.drop 1 |>.take (k - 1)).count c : Int) -
      ((w.drop (k + 1) |>.take (k - 2)).count c : Int) = 0) : False := by
  have := hw 0 k ( by linarith ) ( by linarith ) ; simp_all +decide ;
  contrapose! this; simp_all +decide [ List.perm_iff_count ] ;
  intro c; specialize h c; rcases k with ( _ | _ | k ) <;> simp_all +decide [ List.take ] ;
  · rcases w with ( _ | ⟨ a, _ | ⟨ b, _ | w ⟩ ⟩ ) <;> simp_all +decide [ List.count ];
    · lia;
    · lia;
    · lia;
  · rcases w with ( _ | ⟨ x, _ | ⟨ y, w ⟩ ⟩ ) <;> simp_all +decide [ Nat.mul_succ ];
    · cases hm;
    · rw [ List.drop_eq_getElem_cons ];
      rw [ List.take_cons ] ; norm_num [ List.count_cons ] ; ring_nf;
      all_goals norm_num [ add_comm 1, List.take_add_one ] at *;
      grind +splitImp;
      grind +splitImp

private theorem case6_false (w : List (Fin 4)) (hw : FinAbelianSquareFree w)
    (k : ℕ) (hk1 : 1 ≤ k) (hkm : k < w.length) (hm : w.length = 2 * k + 2)
    (h : ∀ c : Fin 4, (if c = w.get ⟨0, by omega⟩ then (1:Int) else 0) +
      (if c = w.get ⟨k, hkm⟩ then (1:Int) else 0) +
      ((w.drop 1 |>.take (k - 1)).count c : Int) -
      ((w.drop (k + 1) |>.take k).count c : Int) -
      (if c = w.get ⟨w.length - 1, by omega⟩ then 1 else 0) = 0) : False := by
  have := hw 0 ( k + 1 ) ?_ ?_ <;> simp_all +decide [ List.take_add ];
  · refine' this ( List.perm_iff_count.mpr _ );
    intro c; specialize h c; rcases k with ( _ | k ) <;> simp_all +decide [ Nat.mul_succ, List.count ] ;
    · contradiction;
    · rcases w with ( _ | ⟨ x, _ | ⟨ y, w ⟩ ⟩ ) <;> simp_all +decide [ List.take ];
      · grind;
      · simp_all +decide [ List.countP_cons, List.take_add_one ];
        grind;
  · linarith

/-! ### Main bridge -/

private theorem vGivesSomeAS_cases (wa wb we : Fin 4) (v : Fin 4 → Int)
    (h : vGivesSomeAS wa wb we v = true) :
    (∀ c : Fin 4, (if c = wa then (1:Int) else 0) - (if c = wb then 1 else 0) + v c = 0) ∨
    (∀ c : Fin 4, v c + (if c = wb then (1:Int) else 0) - (if c = we then 1 else 0) = 0) ∨
    (∀ c : Fin 4, v c - (if c = wb then (1:Int) else 0) = 0) ∨
    (∀ c : Fin 4, v c + (if c = wb then (1:Int) else 0) = 0) ∨
    (∀ c : Fin 4, (if c = wa then (1:Int) else 0) - (if c = wb then 1 else 0) - (if c = we then 1 else 0) + v c = 0) ∨
    (∀ c : Fin 4, (if c = wa then (1:Int) else 0) + (if c = wb then 1 else 0) + v c - (if c = we then 1 else 0) = 0) := by
  unfold vGivesSomeAS at h
  repeat rw [Bool.or_eq_true] at h
  rcases h with ((((h | h) | h) | h) | h) | h <;>
    simp only [List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq] at h
  · left; exact fun c => by linarith [h c]
  · right; left; exact fun c => by linarith [h c]
  · right; right; left; exact fun c => by linarith [h c]
  · right; right; right; left; exact fun c => by linarith [h c]
  · right; right; right; right; left; exact fun c => by linarith [h c]
  · right; right; right; right; right; exact fun c => by linarith [h c]

theorem no_spanning_large (w : List (Fin 4)) (hw : FinAbelianSquareFree w)
    (hm : w.length ≥ 3)
    (r L : ℕ) (hL : L > 0) (hr : r < 85)
    (hlen : r + 2 * L ≤ (applyKeranenG w).length)
    (hspan : (r + 2 * L - 1) / 85 + 1 = w.length)
    (hperm : ((applyKeranenG w).drop r |>.take L).Perm
             ((applyKeranenG w).drop (r + L) |>.take L)) :
    False := by
  rw [applyKeranenG_length] at hlen
  set k := (r + L) / 85
  have hk1 : k ≥ 1 := by omega
  have hkm : k < w.length := by omega
  -- Get vGivesSomeAS
  have hvas := inner_defect_gives_AS w hm r L hL hr hlen hspan hperm
  -- Extract Prop-level conditions
  obtain hc1 | hc2 | hc3 | hc4 | hc5 | hc6 := vGivesSomeAS_cases _ _ _ _ hvas
  -- For each case: derive length constraint, apply case lemma
  -- Helper for sum(v)
  all_goals (
    set il := w.drop 1 |>.take (k - 1)
    set ir := w.drop (k + 1) |>.take (w.length - 2 - k)
    have hil : il.length = k - 1 := by simp [il, List.length_take]; omega
    have hir : ir.length = w.length - 2 - k := by simp [ir, List.length_take, List.length_drop]; omega
    have hil_cast : (↑(il.length) : Int) = (k : Int) - 1 := by omega
    have hir_cast : (↑(ir.length) : Int) = (w.length : Int) - 2 - k := by omega
    )
  · -- Pattern 1: sum(v) = 0, m = 2k+1
    have hmeq : w.length = 2 * k + 1 := by
      have := hc1 0; have := hc1 1; have := hc1 2; have := hc1 3
      have := indicator_sum_fin4 (w.get ⟨0, by omega⟩)
      have := indicator_sum_fin4 (w.get ⟨k, by omega⟩)
      have h1 := sum_count_eq_length il; rw [hil] at h1
      have h2 := sum_count_eq_length ir; rw [hir] at h2
      linarith [hil_cast, hir_cast]
    have hirk : w.length - 2 - k = k - 1 := by omega
    exact case1_false w hw k hk1 hkm hmeq (fun c => by
      have := hc1 c; simp only [ir, hirk] at this; linarith)
  · -- Pattern 2: sum(v) = 0, m = 2k+1
    have hmeq : w.length = 2 * k + 1 := by
      have := hc2 0; have := hc2 1; have := hc2 2; have := hc2 3
      have := indicator_sum_fin4 (w.get ⟨k, by omega⟩)
      have := indicator_sum_fin4 (w.get ⟨w.length - 1, by omega⟩)
      have h1 := sum_count_eq_length il; rw [hil] at h1
      have h2 := sum_count_eq_length ir; rw [hir] at h2
      linarith [hil_cast, hir_cast]
    have hirk : w.length - 2 - k = k - 1 := by omega
    exact case2_false w hw k hk1 hkm hmeq (fun c => by
      have := hc2 c; simp only [ir, hirk] at this; linarith)
  · -- Pattern 3: sum(v) = 1, m = 2k
    have hmeq : w.length = 2 * k := by
      have := hc3 0; have := hc3 1; have := hc3 2; have := hc3 3
      have := indicator_sum_fin4 (w.get ⟨k, by omega⟩)
      have h1 := sum_count_eq_length il; rw [hil] at h1
      have h2 := sum_count_eq_length ir; rw [hir] at h2
      linarith [hil_cast, hir_cast]
    have hirk : w.length - 2 - k = k - 2 := by omega
    exact case3_false w hw k (by omega) hkm hmeq (fun c => by
      have := hc3 c; simp only [ir, hirk] at this; linarith)
  · -- Pattern 4: sum(v) = -1, m = 2k+2
    have hmeq : w.length = 2 * k + 2 := by
      have := hc4 0; have := hc4 1; have := hc4 2; have := hc4 3
      have := indicator_sum_fin4 (w.get ⟨k, by omega⟩)
      have h1 := sum_count_eq_length il; rw [hil] at h1
      have h2 := sum_count_eq_length ir; rw [hir] at h2
      linarith [hil_cast, hir_cast]
    have hirk : w.length - 2 - k = k := by omega
    exact case4_false w hw k hk1 hkm hmeq (fun c => by
      have := hc4 c; simp only [ir, hirk] at this; linarith)
  · -- Pattern 5: sum(v) = 1, m = 2k
    have hmeq : w.length = 2 * k := by
      have := hc5 0; have := hc5 1; have := hc5 2; have := hc5 3
      have := indicator_sum_fin4 (w.get ⟨0, by omega⟩)
      have := indicator_sum_fin4 (w.get ⟨k, by omega⟩)
      have := indicator_sum_fin4 (w.get ⟨w.length - 1, by omega⟩)
      have h1 := sum_count_eq_length il; rw [hil] at h1
      have h2 := sum_count_eq_length ir; rw [hir] at h2
      linarith [hil_cast, hir_cast]
    have hirk : w.length - 2 - k = k - 2 := by omega
    exact case5_false w hw k (by omega) hkm hmeq (fun c => by
      have := hc5 c; simp only [ir, hirk] at this; linarith)
  · -- Pattern 6: sum(v) = -1, m = 2k+2
    have hmeq : w.length = 2 * k + 2 := by
      have := hc6 0; have := hc6 1; have := hc6 2; have := hc6 3
      have := indicator_sum_fin4 (w.get ⟨0, by omega⟩)
      have := indicator_sum_fin4 (w.get ⟨k, by omega⟩)
      have := indicator_sum_fin4 (w.get ⟨w.length - 1, by omega⟩)
      have h1 := sum_count_eq_length il; rw [hil] at h1
      have h2 := sum_count_eq_length ir; rw [hir] at h2
      linarith [hil_cast, hir_cast]
    have hirk : w.length - 2 - k = k := by omega
    exact case6_false w hw k hk1 hkm hmeq (fun c => by
      have := hc6 c; simp only [ir, hirk] at this; linarith)

end Erdos192
