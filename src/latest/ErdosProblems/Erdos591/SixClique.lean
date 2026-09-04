import ErdosProblems.Erdos591.InterlacingGraph

namespace Erdos591.Negative

def fin4To5 (i : Fin 4) : Fin 5 := ⟨i, by omega⟩
def fin5To6 (i : Fin 5) : Fin 6 := ⟨i, by omega⟩
def fin4To6 (i : Fin 4) : Fin 6 := fin5To6 (fin4To5 i)

/-- The first numerical coordinate, with an irrelevant value on the empty
sequence.  Every endpoint of an interlacing edge is nonempty. -/
def firstValue : List TaggedCoord → ℕ
  | [] => 0
  | a :: _ => a.value

theorem InterlacingWitness.firstValue_lt
    {x y : List TaggedCoord} (w : InterlacingWitness x y) :
    firstValue x < firstValue y := by
  cases hx : w.X.p0 with
  | nil => exact (w.X.ne0 hx).elim
  | cons a as =>
      cases hy : w.Y.p0 with
      | nil => exact (w.Y.ne0 hy).elim
      | cons b bs =>
          have hab : a.value < b.value :=
            w.x0_y0.mem (by simp [hx]) (by simp [hy])
          simpa [firstValue, w.X.eq_append, w.Y.eq_append, hx, hy] using hab

@[simp] theorem fin4To5_val (i : Fin 4) : (fin4To5 i).val = i.val := rfl
@[simp] theorem fin5To6_val (i : Fin 5) : (fin5To6 i).val = i.val := rfl
@[simp] theorem fin4To6_val (i : Fin 4) : (fin4To6 i).val = i.val := rfl

theorem fin4To6_lt {i j : Fin 4} (h : i < j) : fin4To6 i < fin4To6 j := by
  change i.val < j.val
  exact h

theorem fin4To6_lt_four (i : Fin 4) : fin4To6 i < (4 : Fin 6) := by
  change i.val < 4
  exact i.isLt

theorem fin4To6_lt_five (i : Fin 4) : fin4To6 i < (5 : Fin 6) := by
  exact (fin4To6_lt_four i).trans (by decide)

theorem fin5To6_lt_five (i : Fin 5) : fin5To6 i < (5 : Fin 6) := by
  change i.val < 5
  exact i.isLt

inductive FourOrder where
  | o0123 | o0132 | o0213 | o0231 | o0312 | o0321
  | o1023 | o1032 | o1203 | o1230 | o1302 | o1320
  | o2013 | o2031 | o2103 | o2130 | o2301 | o2310
  | o3012 | o3021 | o3102 | o3120 | o3201 | o3210

def FourOrder.Holds (o : FourOrder) (q₀ q₁ q₂ q₃ : ℕ) : Prop :=
  match o with
  | .o0123 => q₀ < q₁ ∧ q₁ < q₂ ∧ q₂ < q₃
  | .o0132 => q₀ < q₁ ∧ q₁ < q₃ ∧ q₃ < q₂
  | .o0213 => q₀ < q₂ ∧ q₂ < q₁ ∧ q₁ < q₃
  | .o0231 => q₀ < q₂ ∧ q₂ < q₃ ∧ q₃ < q₁
  | .o0312 => q₀ < q₃ ∧ q₃ < q₁ ∧ q₁ < q₂
  | .o0321 => q₀ < q₃ ∧ q₃ < q₂ ∧ q₂ < q₁
  | .o1023 => q₁ < q₀ ∧ q₀ < q₂ ∧ q₂ < q₃
  | .o1032 => q₁ < q₀ ∧ q₀ < q₃ ∧ q₃ < q₂
  | .o1203 => q₁ < q₂ ∧ q₂ < q₀ ∧ q₀ < q₃
  | .o1230 => q₁ < q₂ ∧ q₂ < q₃ ∧ q₃ < q₀
  | .o1302 => q₁ < q₃ ∧ q₃ < q₀ ∧ q₀ < q₂
  | .o1320 => q₁ < q₃ ∧ q₃ < q₂ ∧ q₂ < q₀
  | .o2013 => q₂ < q₀ ∧ q₀ < q₁ ∧ q₁ < q₃
  | .o2031 => q₂ < q₀ ∧ q₀ < q₃ ∧ q₃ < q₁
  | .o2103 => q₂ < q₁ ∧ q₁ < q₀ ∧ q₀ < q₃
  | .o2130 => q₂ < q₁ ∧ q₁ < q₃ ∧ q₃ < q₀
  | .o2301 => q₂ < q₃ ∧ q₃ < q₀ ∧ q₀ < q₁
  | .o2310 => q₂ < q₃ ∧ q₃ < q₁ ∧ q₁ < q₀
  | .o3012 => q₃ < q₀ ∧ q₀ < q₁ ∧ q₁ < q₂
  | .o3021 => q₃ < q₀ ∧ q₀ < q₂ ∧ q₂ < q₁
  | .o3102 => q₃ < q₁ ∧ q₁ < q₀ ∧ q₀ < q₂
  | .o3120 => q₃ < q₁ ∧ q₁ < q₂ ∧ q₂ < q₀
  | .o3201 => q₃ < q₂ ∧ q₂ < q₀ ∧ q₀ < q₁
  | .o3210 => q₃ < q₂ ∧ q₂ < q₁ ∧ q₁ < q₀

theorem four_order_exists (q₀ q₁ q₂ q₃ : ℕ)
    (h₀₁ : q₀ ≠ q₁) (h₀₂ : q₀ ≠ q₂) (h₀₃ : q₀ ≠ q₃)
    (h₁₂ : q₁ ≠ q₂) (h₁₃ : q₁ ≠ q₃) (h₂₃ : q₂ ≠ q₃) :
    ∃ o, FourOrder.Holds o q₀ q₁ q₂ q₃ := by
  rcases lt_or_gt_of_ne h₀₁ with h₀₁ | h₁₀ <;>
    rcases lt_or_gt_of_ne h₀₂ with h₀₂ | h₂₀ <;>
    rcases lt_or_gt_of_ne h₀₃ with h₀₃ | h₃₀ <;>
    rcases lt_or_gt_of_ne h₁₂ with h₁₂ | h₂₁ <;>
    rcases lt_or_gt_of_ne h₁₃ with h₁₃ | h₃₁ <;>
    rcases lt_or_gt_of_ne h₂₃ with h₂₃ | h₃₂
  all_goals first
    | omega
    | exact ⟨.o0123, h₀₁, h₁₂, h₂₃⟩
    | exact ⟨.o0132, h₀₁, h₁₃, h₃₂⟩
    | exact ⟨.o0213, h₀₂, h₂₁, h₁₃⟩
    | exact ⟨.o0231, h₀₂, h₂₃, h₃₁⟩
    | exact ⟨.o0312, h₀₃, h₃₁, h₁₂⟩
    | exact ⟨.o0321, h₀₃, h₃₂, h₂₁⟩
    | exact ⟨.o1023, h₁₀, h₀₂, h₂₃⟩
    | exact ⟨.o1032, h₁₀, h₀₃, h₃₂⟩
    | exact ⟨.o1203, h₁₂, h₂₀, h₀₃⟩
    | exact ⟨.o1230, h₁₂, h₂₃, h₃₀⟩
    | exact ⟨.o1302, h₁₃, h₃₀, h₀₂⟩
    | exact ⟨.o1320, h₁₃, h₃₂, h₂₀⟩
    | exact ⟨.o2013, h₂₀, h₀₁, h₁₃⟩
    | exact ⟨.o2031, h₂₀, h₀₃, h₃₁⟩
    | exact ⟨.o2103, h₂₁, h₁₀, h₀₃⟩
    | exact ⟨.o2130, h₂₁, h₁₃, h₃₀⟩
    | exact ⟨.o2301, h₂₃, h₃₀, h₀₁⟩
    | exact ⟨.o2310, h₂₃, h₃₁, h₁₀⟩
    | exact ⟨.o3012, h₃₀, h₀₁, h₁₂⟩
    | exact ⟨.o3021, h₃₀, h₀₂, h₂₁⟩
    | exact ⟨.o3102, h₃₁, h₁₀, h₀₂⟩
    | exact ⟨.o3120, h₃₁, h₁₂, h₂₀⟩
    | exact ⟨.o3201, h₃₂, h₂₀, h₀₁⟩
    | exact ⟨.o3210, h₃₂, h₂₁, h₁₀⟩

/-- The final finite argument in Hajnal--Larson's proof.  Four box
coordinates from the first four vertices are assumed in increasing order.
Claims B and C, followed by one of the two nine-block capacity lemmas,
give a contradiction. -/
theorem ordered_four_contradiction
    (v : Fin 6 → List TaggedCoord)
    (w : ∀ {i j : Fin 6}, i < j → InterlacingWitness (v i) (v j))
    (q : Fin 5 → TaggedCoord)
    (hqbox : ∀ i, IsBoxCoord (v (fin5To6 i)) (q i))
    (hqinside : ∀ i, Inside (v 5) (q i))
    {a b c d : Fin 4}
    (hab : (q (fin4To5 a)).value < (q (fin4To5 b)).value)
    (hbc : (q (fin4To5 b)).value < (q (fin4To5 c)).value)
    (hcd : (q (fin4To5 c)).value < (q (fin4To5 d)).value) : False := by
  let wef : InterlacingWitness (v 4) (v 5) := w (by omega)
  have hinsideE (i : Fin 4) : Inside (v 4) (q (fin4To5 i)) := by
    exact wef.inside_first_of_inside_second (hqinside (fin4To5 i))
  have betweenE (i j : Fin 4) (hne : i ≠ j) :
      ∃ r ∈ v 4,
        ((q (fin4To5 i)).value < r.value ∧
          r.value < (q (fin4To5 j)).value) ∨
        ((q (fin4To5 j)).value < r.value ∧
          r.value < (q (fin4To5 i)).value) := by
    rcases lt_or_gt_of_ne hne with hij | hji
    · exact triangle_exists_coord_between
        (w (fin4To6_lt hij))
        (w (fin4To6_lt_four i))
        (w (fin4To6_lt_four j))
        (hqbox (fin4To5 i)) (hqbox (fin4To5 j))
        (hinsideE i) (hinsideE j)
    · simpa [or_comm] using triangle_exists_coord_between
        (w (fin4To6_lt hji))
        (w (fin4To6_lt_four j))
        (w (fin4To6_lt_four i))
        (hqbox (fin4To5 j)) (hqbox (fin4To5 i))
        (hinsideE j) (hinsideE i)
  have betweenF (i j : Fin 4) (hne : i ≠ j) :
      ∃ r ∈ v 5,
        ((q (fin4To5 i)).value < r.value ∧
          r.value < (q (fin4To5 j)).value) ∨
        ((q (fin4To5 j)).value < r.value ∧
          r.value < (q (fin4To5 i)).value) := by
    rcases lt_or_gt_of_ne hne with hij | hji
    · exact triangle_exists_coord_between
        (w (fin4To6_lt hij))
        (w (fin4To6_lt_five i))
        (w (fin4To6_lt_five j))
        (hqbox (fin4To5 i)) (hqbox (fin4To5 j))
        (hqinside (fin4To5 i)) (hqinside (fin4To5 j))
    · simpa [or_comm] using triangle_exists_coord_between
        (w (fin4To6_lt hji))
        (w (fin4To6_lt_five j))
        (w (fin4To6_lt_five i))
        (hqbox (fin4To5 j)) (hqbox (fin4To5 i))
        (hqinside (fin4To5 j)) (hqinside (fin4To5 i))
  have betweenLast (i : Fin 4) :
      ∃ r ∈ v 5,
        ((q (fin4To5 i)).value < r.value ∧ r.value < (q 4).value) ∨
        ((q 4).value < r.value ∧ r.value < (q (fin4To5 i)).value) := by
    exact triangle_exists_coord_between
      (w (fin4To6_lt_four i))
      (w (fin4To6_lt_five i)) wef
      (hqbox (fin4To5 i)) (hqbox 4)
      (hqinside (fin4To5 i)) (hqinside 4)
  have notLastBetween (i j : Fin 4) (hne : i ≠ j) :
      ¬ ((q (fin4To5 i)).value < (q 4).value ∧
          (q 4).value < (q (fin4To5 j)).value) ∧
      ¬ ((q (fin4To5 j)).value < (q 4).value ∧
          (q 4).value < (q (fin4To5 i)).value) := by
    rcases lt_or_gt_of_ne hne with hij | hji
    · exact triangle_box_not_between
        (w (fin4To6_lt hij))
        (w (fin4To6_lt_four i))
        (w (fin4To6_lt_four j))
        (hqbox (fin4To5 i)) (hqbox (fin4To5 j)) (hqbox 4)
        (hinsideE i) (hinsideE j)
    · simpa [and_comm] using triangle_box_not_between
        (w (fin4To6_lt hji))
        (w (fin4To6_lt_four j))
        (w (fin4To6_lt_four i))
        (hqbox (fin4To5 j)) (hqbox (fin4To5 i)) (hqbox 4)
        (hinsideE j) (hinsideE i)
  have habne : a ≠ b := by intro h; cases h; exact (Nat.lt_irrefl _ hab)
  have hbcne : b ≠ c := by intro h; cases h; exact (Nat.lt_irrefl _ hbc)
  have hcdne : c ≠ d := by intro h; cases h; exact (Nat.lt_irrefl _ hcd)
  have hadne : a ≠ d := by intro h; cases h; omega
  obtain ⟨eab, heabmem, heab⟩ := betweenE a b habne
  obtain ⟨fbc, hfbcmem, hfbc⟩ := betweenF b c hbcne
  obtain ⟨ecd, hecdmem, hecd⟩ := betweenE c d hcdne
  have heab' : (q (fin4To5 a)).value < eab.value ∧
      eab.value < (q (fin4To5 b)).value := by rcases heab with h | h <;> omega
  have hfbc' : (q (fin4To5 b)).value < fbc.value ∧
      fbc.value < (q (fin4To5 c)).value := by rcases hfbc with h | h <;> omega
  have hecd' : (q (fin4To5 c)).value < ecd.value ∧
      ecd.value < (q (fin4To5 d)).value := by rcases hecd with h | h <;> omega
  obtain ⟨rA, hrAmem, hcompA⟩ := betweenLast a
  obtain ⟨rD, hrDmem, hcompD⟩ := betweenLast d
  have hsides : (q 4).value < (q (fin4To5 a)).value ∨
      (q (fin4To5 d)).value < (q 4).value := by
    have hnot := notLastBetween a d hadne
    rcases hcompA with hcompA | hcompA <;>
      rcases hcompD with hcompD | hcompD <;> omega
  have he4mid : q 4 ∈ wef.X.p2 :=
    wef.box_mem_middle_of_inside (hqbox 4) (hqinside 4)
  rcases hsides with hleft | hright
  · obtain ⟨fextra, hfextramem, hfextra⟩ := betweenLast a
    have hfextra' : (q 4).value < fextra.value ∧
        fextra.value < (q (fin4To5 a)).value := by
      rcases hfextra with h | h <;> omega
    let wdf : InterlacingWitness (v (fin4To6 d)) (v 5) :=
      w (fin4To6_lt_five d)
    obtain ⟨delta, hdeltapiece, hdeltabox⟩ := wdf.box_y3
    have hqdmid : q (fin4To5 d) ∈ wdf.X.p2 :=
      wdf.box_mem_middle_of_inside (hqbox (fin4To5 d))
        (hqinside (fin4To5 d))
    have hqddelta : (q (fin4To5 d)).value < delta.value :=
      wdf.x_head_before_y3 (Or.inr (Or.inr (Or.inl hqdmid))) hdeltapiece
    have hdeltamem : delta ∈ v 5 := wdf.Y.mem3 hdeltapiece
    have hdeltalast : delta ∈ wef.Y.p3 :=
      wef.box_second_mem_last_of_middle_lt he4mid
        ⟨hdeltamem, hdeltabox⟩ (by omega)
    exact wef.no_forward_three_alternations he4mid heabmem hecdmem
      hfextramem hfbcmem hdeltalast (by omega) (by omega) (by omega)
      (by omega) (by omega)
  · obtain ⟨fextra, hfextramem, hfextra⟩ := betweenLast d
    have hfextra' : (q (fin4To5 d)).value < fextra.value ∧
        fextra.value < (q 4).value := by
      rcases hfextra with h | h <;> omega
    let waf : InterlacingWitness (v (fin4To6 a)) (v 5) :=
      w (fin4To6_lt_five a)
    obtain ⟨delta, hdeltapiece, hdeltabox⟩ := waf.box_y0
    have hqamid : q (fin4To5 a) ∈ waf.X.p2 :=
      waf.box_mem_middle_of_inside (hqbox (fin4To5 a))
        (hqinside (fin4To5 a))
    have hdeltaqa : delta.value < (q (fin4To5 a)).value :=
      waf.y0_before_x_tail hdeltapiece (Or.inr (Or.inl hqamid))
    have hdeltamem : delta ∈ v 5 := waf.Y.mem0 hdeltapiece
    have hdeltafirst : delta ∈ wef.Y.p0 :=
      wef.box_second_mem_first_of_lt_middle he4mid
        ⟨hdeltamem, hdeltabox⟩ (by omega)
    exact wef.no_backward_three_alternations hdeltafirst hfbcmem
      hfextramem heabmem hecdmem he4mid (by omega) (by omega) (by omega)
      (by omega) (by omega)

/-- The oriented nine-block relation has no six-element complete set. -/
theorem no_oriented_six
    (v : Fin 6 → List TaggedCoord)
    (w : ∀ {i j : Fin 6}, i < j → InterlacingWitness (v i) (v j)) : False := by
  have hmiddle (i : Fin 5) :
      ∃ q, IsBoxCoord (v (fin5To6 i)) q ∧ Inside (v 5) q := by
    exact (w (fin5To6_lt_five i)).middle_box_inside
  choose q hqbox hqinside using hmiddle
  have qne (i j : Fin 4) (hne : i ≠ j) :
      (q (fin4To5 i)).value ≠ (q (fin4To5 j)).value := by
    rcases lt_or_gt_of_ne hne with hij | hji
    · obtain ⟨r, -, hr⟩ := triangle_exists_coord_between
        (w (fin4To6_lt hij))
        (w (fin4To6_lt_five i))
        (w (fin4To6_lt_five j))
        (hqbox (fin4To5 i)) (hqbox (fin4To5 j))
        (hqinside (fin4To5 i)) (hqinside (fin4To5 j))
      rcases hr with hr | hr <;> omega
    · obtain ⟨r, -, hr⟩ := triangle_exists_coord_between
        (w (fin4To6_lt hji))
        (w (fin4To6_lt_five j))
        (w (fin4To6_lt_five i))
        (hqbox (fin4To5 j)) (hqbox (fin4To5 i))
        (hqinside (fin4To5 j)) (hqinside (fin4To5 i))
      rcases hr with hr | hr <;> omega
  obtain ⟨o, ho⟩ := four_order_exists
    (q (fin4To5 0)).value (q (fin4To5 1)).value
    (q (fin4To5 2)).value (q (fin4To5 3)).value
    (qne 0 1 (by decide)) (qne 0 2 (by decide)) (qne 0 3 (by decide))
    (qne 1 2 (by decide)) (qne 1 3 (by decide)) (qne 2 3 (by decide))
  cases o <;> simp only [FourOrder.Holds] at ho
  · exact ordered_four_contradiction v w q hqbox hqinside
      (a := 0) (b := 1) (c := 2) (d := 3) ho.1 ho.2.1 ho.2.2
  · exact ordered_four_contradiction v w q hqbox hqinside
      (a := 0) (b := 1) (c := 3) (d := 2) ho.1 ho.2.1 ho.2.2
  · exact ordered_four_contradiction v w q hqbox hqinside
      (a := 0) (b := 2) (c := 1) (d := 3) ho.1 ho.2.1 ho.2.2
  · exact ordered_four_contradiction v w q hqbox hqinside
      (a := 0) (b := 2) (c := 3) (d := 1) ho.1 ho.2.1 ho.2.2
  · exact ordered_four_contradiction v w q hqbox hqinside
      (a := 0) (b := 3) (c := 1) (d := 2) ho.1 ho.2.1 ho.2.2
  · exact ordered_four_contradiction v w q hqbox hqinside
      (a := 0) (b := 3) (c := 2) (d := 1) ho.1 ho.2.1 ho.2.2
  · exact ordered_four_contradiction v w q hqbox hqinside
      (a := 1) (b := 0) (c := 2) (d := 3) ho.1 ho.2.1 ho.2.2
  · exact ordered_four_contradiction v w q hqbox hqinside
      (a := 1) (b := 0) (c := 3) (d := 2) ho.1 ho.2.1 ho.2.2
  · exact ordered_four_contradiction v w q hqbox hqinside
      (a := 1) (b := 2) (c := 0) (d := 3) ho.1 ho.2.1 ho.2.2
  · exact ordered_four_contradiction v w q hqbox hqinside
      (a := 1) (b := 2) (c := 3) (d := 0) ho.1 ho.2.1 ho.2.2
  · exact ordered_four_contradiction v w q hqbox hqinside
      (a := 1) (b := 3) (c := 0) (d := 2) ho.1 ho.2.1 ho.2.2
  · exact ordered_four_contradiction v w q hqbox hqinside
      (a := 1) (b := 3) (c := 2) (d := 0) ho.1 ho.2.1 ho.2.2
  · exact ordered_four_contradiction v w q hqbox hqinside
      (a := 2) (b := 0) (c := 1) (d := 3) ho.1 ho.2.1 ho.2.2
  · exact ordered_four_contradiction v w q hqbox hqinside
      (a := 2) (b := 0) (c := 3) (d := 1) ho.1 ho.2.1 ho.2.2
  · exact ordered_four_contradiction v w q hqbox hqinside
      (a := 2) (b := 1) (c := 0) (d := 3) ho.1 ho.2.1 ho.2.2
  · exact ordered_four_contradiction v w q hqbox hqinside
      (a := 2) (b := 1) (c := 3) (d := 0) ho.1 ho.2.1 ho.2.2
  · exact ordered_four_contradiction v w q hqbox hqinside
      (a := 2) (b := 3) (c := 0) (d := 1) ho.1 ho.2.1 ho.2.2
  · exact ordered_four_contradiction v w q hqbox hqinside
      (a := 2) (b := 3) (c := 1) (d := 0) ho.1 ho.2.1 ho.2.2
  · exact ordered_four_contradiction v w q hqbox hqinside
      (a := 3) (b := 0) (c := 1) (d := 2) ho.1 ho.2.1 ho.2.2
  · exact ordered_four_contradiction v w q hqbox hqinside
      (a := 3) (b := 0) (c := 2) (d := 1) ho.1 ho.2.1 ho.2.2
  · exact ordered_four_contradiction v w q hqbox hqinside
      (a := 3) (b := 1) (c := 0) (d := 2) ho.1 ho.2.1 ho.2.2
  · exact ordered_four_contradiction v w q hqbox hqinside
      (a := 3) (b := 1) (c := 2) (d := 0) ho.1 ho.2.1 ho.2.2
  · exact ordered_four_contradiction v w q hqbox hqinside
      (a := 3) (b := 2) (c := 0) (d := 1) ho.1 ho.2.1 ho.2.2
  · exact ordered_four_contradiction v w q hqbox hqinside
      (a := 3) (b := 2) (c := 1) (d := 0) ho.1 ho.2.1 ho.2.2

/-- The symmetrized Hajnal--Larson graph has no six-vertex clique. -/
theorem interlacingGraph_no_six_clique {V : Type*}
    (seq : V → List TaggedCoord) :
    ¬ ∃ S : Set V, (interlacingGraph seq).IsClique S ∧ Cardinal.mk S = 6 := by
  rintro ⟨S, hclique, hcard⟩
  obtain ⟨e⟩ := Cardinal.mk_eq_nat_iff.mp hcard
  let : Fintype S := Fintype.ofEquiv (Fin 6) e.symm
  have hcardS : Fintype.card S = 6 := by
    simpa using Fintype.card_congr e
  have hkey_injective :
      Function.Injective (fun z : S ↦ firstValue (seq z.1)) := by
    intro x y hxy
    apply Subtype.ext
    by_contra hne
    have hadj := hclique x.2 y.2 hne
    rcases (interlacingGraph_adj seq x.1 y.1).mp hadj with ⟨-, hdir⟩
    change Nonempty (InterlacingWitness (seq x.1) (seq y.1)) ∨
      Nonempty (InterlacingWitness (seq y.1) (seq x.1)) at hdir
    rcases hdir with hdir | hdir
    · obtain ⟨wxy⟩ := hdir
      exact (Nat.ne_of_lt wxy.firstValue_lt) hxy
    · obtain ⟨wyx⟩ := hdir
      exact (Nat.ne_of_gt wyx.firstValue_lt) hxy
  let : LinearOrder S :=
    LinearOrder.lift' (fun z : S ↦ firstValue (seq z.1)) hkey_injective
  let o : Fin 6 ≃o S := Fintype.orderIsoFinOfCardEq S hcardS
  let v : Fin 6 → List TaggedCoord := fun i ↦ seq (o i).1
  have hw : ∀ {i j : Fin 6}, i < j → InterlacingWitness (v i) (v j) := by
    intro i j hij
    have hoij : o i < o j := o.lt_iff_lt.mpr hij
    have hkey : firstValue (seq (o i).1) < firstValue (seq (o j).1) := hoij
    have hvalne : (o i).1 ≠ (o j).1 := by
      intro h
      exact (Nat.ne_of_lt hkey) (congrArg (fun z ↦ firstValue (seq z)) h)
    have hadj := hclique (o i).2 (o j).2 hvalne
    rcases (interlacingGraph_adj seq (o i).1 (o j).1).mp hadj with ⟨-, hdir⟩
    change Nonempty (InterlacingWitness (v i) (v j)) ∨
      Nonempty (InterlacingWitness (v j) (v i)) at hdir
    have hinterlaces : Interlaces (v i) (v j) := by
      rcases hdir with hfwd | hrev
      · exact hfwd
      · obtain ⟨wji⟩ := hrev
        exact (Nat.not_lt_of_ge hkey.le wji.firstValue_lt).elim
    exact Classical.choice hinterlaces
  exact no_oriented_six v hw

end Erdos591.Negative
