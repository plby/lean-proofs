import ErdosProblems.Erdos192.Core

namespace Erdos192

def isFinASF3 (word : List (Fin 3)) : Bool :=
  !(List.range word.length |>.any fun i =>
    List.range word.length |>.any fun l =>
      let l := l + 1
      if i + 2 * l > word.length then false
      else (word.drop i |>.take l).isPerm (word.drop (i + l) |>.take l))

/-- **3-letter ASF bound.** No ASF word on 3 letters has length ≥ 8. -/
theorem max_asf_3letters :
    ∀ a b c d e f g h : Fin 3,
      isFinASF3 [a, b, c, d, e, f, g, h] = false := by decide +kernel

theorem isFinASF3_complete (w : List (Fin 3)) (hw : FinAbelianSquareFree w) :
    isFinASF3 w = true := by
  unfold isFinASF3;
  simp +zetaDelta only [gt_iff_lt, Bool.if_false_left, Bool.not_eq_eq_eq_not, Bool.not_true, List.any_eq_false,
    List.mem_range, List.any_eq_true, Bool.and_eq_true, decide_eq_false_iff_not, not_lt, not_exists, not_and,
    Bool.not_eq_true] at *;
  intro i hi j hj hij; contrapose! hw;
  exact fun h => h i ( j + 1 ) ( Nat.succ_pos _ ) hij ( by simpa [ List.isPerm_iff ] using hw )

/-
`infBlock` of `e ∘ f` is the map of `infBlock` of `f`.
-/
theorem infBlock_comp {α β : Type*} (e : α → β) (f : ℕ → α) (s l : ℕ) :
    infBlock (e ∘ f) s l = (infBlock f s l).map e := by
  unfold infBlock; simp +decide [ List.map_map, Function.comp_def ] ;

/-
Infinite abelian-square-freeness is preserved under composition with
an injection.
-/
theorem inf_asf_comp_inj {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : ℕ → α) (e : α → β) (he : Function.Injective e)
    (hf : InfAbelianSquareFree f) : InfAbelianSquareFree (e ∘ f) := by
  intro i l hl; specialize hf i l hl; simp_all +decide [ InfAbelianSquareFree, List.map_eq_map_iff ] ;
  contrapose! hf;
  rw [ ← List.map_perm_map_iff he ];
  unfold infBlock at *; aesop;

/-
No infinite word over `Fin 3` is abelian-square-free.
Proof: by `max_asf_3letters`, every length-8 prefix has an abelian square.
-/
theorem no_inf_asf_three (f : ℕ → Fin 3) : ¬InfAbelianSquareFree f := by
  intro hf
  have h8 : FinAbelianSquareFree (infBlock f 0 8) := by
    -- For any i, l, if the two blocks of length l starting at i and i+l are permutations, then they are also permutations of the infinite word.
    intro i l hl h
    have := hf i l hl
    contrapose! this
    simp_all +decide [ infBlock ];
    convert this using 1;
    · refine' List.ext_get _ _ <;> simp +arith +decide [ List.get ];
      omega;
    · refine' List.ext_get _ _ <;> simp +arith +decide;
      omega;
  convert isFinASF3_complete _ h8 using 1;
  simp only [false_iff, Bool.not_eq_true];
  exact max_asf_3letters _ _ _ _ _ _ _ _

/-
For `d ≤ 3`, every infinite word over `Fin d` has a Parikh AP.
-/
theorem hasParikhAP_of_le_three {d : ℕ} (hd : d ≤ 3) (f : ℕ → Fin d) :
    hasParikhAP f := by
  -- Let `e := Fin.castLE hd : Fin d → Fin 3`. This is injective (Fin.castLE_injective).
  set e : Fin d → Fin 3 := fun x => Fin.castLE hd x
  have he_inj : Function.Injective e := by
    exact Fin.castLE_injective hd;
  -- If `InfAbelianSquareFree f`, then by `inf_asf_comp_inj`, `InfAbelianSquareFree (e ∘ f)`.
  by_cases h_inf_asf : InfAbelianSquareFree f;
  · exact False.elim <| no_inf_asf_three ( e ∘ f ) <| inf_asf_comp_inj f e he_inj h_inf_asf;
  · exact Classical.not_not.1 fun h => h_inf_asf <| by simpa [ h ] using infAbelianSquareFree_iff_parikhAPFree f |>.2 h;

end Erdos192
