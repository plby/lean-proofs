import ErdosProblems.Erdos733.ST.EndpointUnitDiskAlternatingVertexList

open Classical
noncomputable section

-- [TABLET NODE: EndpointUnitDiskAlternatingVertexListEdgeRoles]
lemma EndpointUnitDiskAlternatingVertexListEdgeRoles
    {β : Type*}
    (A B : EuclideanSpace ℝ (Fin 2))
    (items : List β)
    (block : β → List (EuclideanSpace ℝ (Fin 2)))
    (hblock : ∀ x ∈ items, 0 < (block x).length)
    {m : ℕ}
    (hm : m + 1 < (EndpointUnitDiskAlternatingVertexList A B (items.map block)).length)
    {p : EuclideanSpace ℝ (Fin 2)}
    (hp : p ∈
      segment ℝ
        (EndpointUnitDiskAlternatingVertexList A B (items.map block))[m]
        (EndpointUnitDiskAlternatingVertexList A B (items.map block))[m + 1]) :
    (items = [] ∧ p ∈ segment ℝ A B) ∨
      (∃ x xs X,
        items = x :: xs ∧
          (block x).head? = some X ∧
            p ∈ segment ℝ A X) ∨
      (∃ pre x post k,
        ∃ hk : k + 1 < (block x).length,
          items = pre ++ x :: post ∧
            p ∈ segment ℝ (block x)[k] (block x)[k + 1]) ∨
      (∃ pre x y post X Y,
        items = pre ++ x :: y :: post ∧
          (block x).getLast? = some X ∧
            (block y).head? = some Y ∧
              p ∈ segment ℝ X Y) ∨
      (∃ pre x X,
        items = pre ++ [x] ∧
          (block x).getLast? = some X ∧
            p ∈ segment ℝ X B) := by
-- BODY
  classical
  have htail :
      ∀ (items : List β),
        (∀ x ∈ items, 0 < (block x).length) →
        ∀ {n : ℕ},
          (hn : n + 1 < ((items.map block).flatten ++ [B]).length) →
          ∀ {p : EuclideanSpace ℝ (Fin 2)},
            p ∈ segment ℝ
                (((items.map block).flatten ++ [B])[n]'
                  (Nat.lt_trans (Nat.lt_succ_self n) hn))
                (((items.map block).flatten ++ [B])[n + 1]'hn) →
            (∃ pre x post k,
              ∃ hk : k + 1 < (block x).length,
                items = pre ++ x :: post ∧
                  p ∈ segment ℝ (block x)[k] (block x)[k + 1]) ∨
              (∃ pre x y post X Y,
                items = pre ++ x :: y :: post ∧
                  (block x).getLast? = some X ∧
                    (block y).head? = some Y ∧
                      p ∈ segment ℝ X Y) ∨
              (∃ pre x X,
                items = pre ++ [x] ∧
                  (block x).getLast? = some X ∧
                    p ∈ segment ℝ X B) := by
    intro items
    induction items with
    | nil =>
        intro _ n hn _ _
        simp at hn
    | cons x xs ih =>
        intro hblock_cons n hn p hp
        have hxlen : 0 < (block x).length := hblock_cons x (by simp)
        by_cases hinside : n + 1 < (block x).length
        · left
          refine ⟨[], x, xs, n, hinside, by simp, ?_⟩
          have hn_left : n < (block x).length := Nat.lt_trans (Nat.lt_succ_self n) hinside
          simpa [List.flatten_cons, List.append_assoc, List.getElem_append_left hn_left,
            List.getElem_append_left hinside] using hp
        · by_cases hn_left : n < (block x).length
          · have hn_succ_eq : n + 1 = (block x).length := by omega
            have hn_eq_last : n = (block x).length - 1 := by omega
            cases xs with
            | nil =>
                right
                right
                have hlast :
                    (block x).getLast? = some ((block x)[n]) := by
                  rw [List.getLast?_eq_getElem?]
                  have hlast_index : (block x).length - 1 < (block x).length := by omega
                  rw [List.getElem?_eq_getElem hlast_index]
                  congr
                  exact hn_eq_last.symm
                refine ⟨[], x, (block x)[n], by simp, hlast, ?_⟩
                simpa [List.flatten_cons, List.append_assoc, hn_succ_eq,
                  List.getElem_append_left hn_left] using hp
            | cons y ys =>
                right
                left
                have hylen : 0 < (block y).length := hblock_cons y (by simp)
                have hlast :
                    (block x).getLast? = some ((block x)[n]) := by
                  rw [List.getLast?_eq_getElem?]
                  have hlast_index : (block x).length - 1 < (block x).length := by omega
                  rw [List.getElem?_eq_getElem hlast_index]
                  congr
                  exact hn_eq_last.symm
                have hhead :
                    (block y).head? = some ((block y)[0]) := by
                  have hyne : block y ≠ [] := List.ne_nil_of_length_pos hylen
                  rw [List.head?_eq_some_head hyne, List.head_eq_getElem hyne]
                refine ⟨[], x, y, ys, (block x)[n], (block y)[0], by simp,
                  hlast, hhead, ?_⟩
                have happ_len :
                    n + 1 <
                      (block x ++ (block y ++ ((ys.map block).flatten ++ [B]))).length := by
                  simpa [List.flatten_cons, List.append_assoc] using hn
                have hn_app :
                    n <
                      (block x ++ (block y ++ ((ys.map block).flatten ++ [B]))).length :=
                  Nat.lt_trans (Nat.lt_succ_self n) happ_len
                have hright :
                    (block x ++ (block y ++ ((ys.map block).flatten ++ [B])))[n + 1]'happ_len =
                      (block y)[0] := by
                  rw [List.getElem_append_right (by omega : (block x).length ≤ n + 1)]
                  have hsub : n + 1 - (block x).length = 0 := by omega
                  simp [hsub, List.getElem_append_left hylen]
                have hleft :
                    (block x ++ (block y ++ ((ys.map block).flatten ++ [B])))[n]'hn_app =
                      (block x)[n] := by
                  exact List.getElem_append_left hn_left
                simpa [List.flatten_cons, List.append_assoc, hleft, hright] using hp
          · have hle : (block x).length ≤ n := Nat.le_of_not_gt hn_left
            have hblock_xs : ∀ y ∈ xs, 0 < (block y).length := by
              intro y hy
              exact hblock_cons y (by simp [hy])
            have hn' :
                (n - (block x).length) + 1 <
                  ((xs.map block).flatten ++ [B]).length := by
              have hn_len :
                  n + 1 <
                    (block x ++ ((xs.map block).flatten ++ [B])).length := by
                simpa [List.flatten_cons, List.append_assoc] using hn
              simp at hn_len ⊢
              omega
            have hp' :
                p ∈ segment ℝ
                    (((xs.map block).flatten ++ [B])[n - (block x).length]'
                      (Nat.lt_trans (Nat.lt_succ_self _) hn'))
                    (((xs.map block).flatten ++ [B])[n - (block x).length + 1]'hn') := by
              have hright_index :
                  n + 1 - (block x).length = n - (block x).length + 1 := by
                omega
              simpa [List.flatten_cons, List.append_assoc,
                List.getElem_append_right hle,
                List.getElem_append_right (by omega : (block x).length ≤ n + 1),
                hright_index] using hp
            rcases ih hblock_xs hn' hp' with hlocal | hbridge | hterminal
            · left
              rcases hlocal with ⟨pre, y, post, k, hk, hxs, hpseg⟩
              refine ⟨x :: pre, y, post, k, hk, ?_, hpseg⟩
              simp [hxs]
            · right
              left
              rcases hbridge with ⟨pre, y, z, post, X, Y, hxs, hlast, hhead, hpseg⟩
              refine ⟨x :: pre, y, z, post, X, Y, ?_, hlast, hhead, hpseg⟩
              simp [hxs]
            · right
              right
              rcases hterminal with ⟨pre, y, X, hxs, hlast, hpseg⟩
              refine ⟨x :: pre, y, X, ?_, hlast, hpseg⟩
              simp [hxs]
  cases items with
  | nil =>
      left
      have hm0 : m = 0 := by
        simpa [EndpointUnitDiskAlternatingVertexList] using hm
      subst m
      simpa [EndpointUnitDiskAlternatingVertexList] using hp
  | cons x xs =>
      right
      cases m with
      | zero =>
          left
          have hxlen : 0 < (block x).length := hblock x (by simp)
          have hhead :
              (block x).head? = some ((block x)[0]) := by
            have hxne : block x ≠ [] := List.ne_nil_of_length_pos hxlen
            rw [List.head?_eq_some_head hxne, List.head_eq_getElem hxne]
          refine ⟨x, xs, (block x)[0], rfl, hhead, ?_⟩
          simpa [EndpointUnitDiskAlternatingVertexList, List.flatten_cons, List.append_assoc,
            List.getElem_append_left hxlen] using hp
      | succ n =>
          right
          have hn_tail :
              n + 1 < (((x :: xs).map block).flatten ++ [B]).length := by
            simpa [EndpointUnitDiskAlternatingVertexList] using hm
          have hp_tail :
              p ∈ segment ℝ
                  ((((x :: xs).map block).flatten ++ [B])[n]'
                    (Nat.lt_trans (Nat.lt_succ_self n) hn_tail))
                  ((((x :: xs).map block).flatten ++ [B])[n + 1]'hn_tail) := by
            simpa [EndpointUnitDiskAlternatingVertexList] using hp
          rcases htail (x :: xs) hblock hn_tail hp_tail with hlocal | hbridge | hterminal
          · left
            exact hlocal
          · right
            left
            exact hbridge
          · right
            right
            exact hterminal
