import ErdosProblems.Erdos556.Basic

/-!
# The sharp four-clique construction

The two Boolean coordinates index four cliques, each of order `n - 1`.
Colour zero separates the first coordinate, colour one separates the second
coordinate within a fixed first coordinate, and colour two stays in a clique.
-/

namespace Erdos556

open SimpleGraph
open scoped SimpleGraph

/-- The vertex set of the sharpness construction. -/
abbrev SharpVertex (n : ℕ) := Bool × Bool × Fin (n - 1)

/-- The explicit colouring on four cliques of order `n - 1`. -/
def sharpColouring (n : ℕ) : ThreeColouring (SharpVertex n) where
  colour x y := if x.1 ≠ y.1 then 0 else if x.2.1 ≠ y.2.1 then 1 else 2
  symm x y := by simp only [ne_comm]

theorem sharpColouring_zero {n : ℕ} {x y : SharpVertex n}
    (h : ((sharpColouring n).graph 0).Adj x y) : x.1 ≠ y.1 := by
  have hc := h.2
  change (if x.1 ≠ y.1 then (0 : Fin 3) else
    if x.2.1 ≠ y.2.1 then 1 else 2) = 0 at hc
  split_ifs at hc <;> simp_all

theorem sharpColouring_one {n : ℕ} {x y : SharpVertex n}
    (h : ((sharpColouring n).graph 1).Adj x y) : x.2.1 ≠ y.2.1 := by
  have hc := h.2
  change (if x.1 ≠ y.1 then (0 : Fin 3) else
    if x.2.1 ≠ y.2.1 then 1 else 2) = 1 at hc
  split_ifs at hc <;> simp_all

theorem sharpColouring_two {n : ℕ} {x y : SharpVertex n}
    (h : ((sharpColouring n).graph 2).Adj x y) :
    (x.1, x.2.1) = (y.1, y.2.1) := by
  have hc := h.2
  change (if x.1 ≠ y.1 then (0 : Fin 3) else
    if x.2.1 ≠ y.2.1 then 1 else 2) = 2 at hc
  split_ifs at hc <;> simp_all

/-- A Boolean proper colouring rules out every odd cycle. -/
theorem not_cycle_of_bicolouring {V : Type*} {G : SimpleGraph V}
    (b : G.Coloring Bool) {n : ℕ} (hn : 2 < n) (ho : Odd n) :
    ¬ cycleGraph n ⊑ G := by
  intro h
  obtain ⟨v, p, _, hp⟩ := (cycleGraph_isContained_iff hn).mp h
  have he : Even p.length := (b.even_length_iff_congr p).mpr Iff.rfl
  rw [hp] at he
  exact (Nat.not_even_iff_odd.mpr ho) he

/-- An edgewise constant label is constant along a walk. -/
theorem label_eq_of_walk {V W : Type*} {G : SimpleGraph V}
    (label : V → W) (hlabel : ∀ {u v}, G.Adj u v → label u = label v)
    {u v : V} (p : G.Walk u v) : label u = label v := by
  induction p with
  | nil => rfl
  | cons h p ih => exact (hlabel h).trans ih

theorem sharpColouring_no_cycle (n : ℕ) (hn : 2 < n) (ho : Odd n)
    (i : Fin 3) : ¬ cycleGraph n ⊑ (sharpColouring n).graph i := by
  fin_cases i
  · let b : ((sharpColouring n).graph 0).Coloring Bool :=
      { toFun := fun x => x.1
        map_rel' := by
          intro x y h
          exact sharpColouring_zero h }
    exact not_cycle_of_bicolouring b hn ho
  · let b : ((sharpColouring n).graph 1).Coloring Bool :=
      { toFun := fun x => x.2.1
        map_rel' := by
          intro x y h
          exact sharpColouring_one h }
    exact not_cycle_of_bicolouring b hn ho
  · rintro ⟨f⟩
    have hlabel (u v : Fin n) :
        ((f u).1, (f u).2.1) = ((f v).1, (f v).2.1) := by
      obtain ⟨p⟩ := cycleGraph_preconnected u v
      exact label_eq_of_walk (fun x : SharpVertex n => (x.1, x.2.1))
        (fun h => sharpColouring_two h) (p.map f.toHom)
    have hinj : Function.Injective (fun u : Fin n => (f u).2.2) := by
      intro u v huv
      apply f.injective
      have h := hlabel u v
      apply Prod.ext
      · exact congrArg (fun z : Bool × Bool => z.1) h
      · exact Prod.ext (congrArg (fun z : Bool × Bool => z.2) h) huv
    have hc := Fintype.card_le_of_injective _ hinj
    simp only [Fintype.card_fin] at hc
    omega

theorem card_sharpVertex (n : ℕ) :
    Fintype.card (SharpVertex n) = 4 * n - 4 := by
  simp only [SharpVertex, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]
  omega

/-- The explicit construction shows that `4*n - 4` is not a Ramsey order. -/
theorem not_isRamseyOrder_four_mul_sub_four (n : ℕ) (hn : 2 < n) (ho : Odd n) :
    ¬ IsRamseyOrder n (4 * n - 4) := by
  intro h
  let e : Fin (4 * n - 4) ≃ SharpVertex n :=
    Fintype.equivOfCardEq (by simp only [Fintype.card_fin, card_sharpVertex])
  obtain ⟨i, hi⟩ := h.of_equiv e (sharpColouring n)
  exact sharpColouring_no_cycle n hn ho i hi

#print axioms sharpColouring_no_cycle
#print axioms not_isRamseyOrder_four_mul_sub_four

end Erdos556
