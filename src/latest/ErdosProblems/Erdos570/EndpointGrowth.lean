/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos570.EndpointPath

/-!
# Growing endpoint-preserving paths

Starting from an edge, paths with the same ordered endpoints can be grown one
vertex at a time.  Before a prescribed length is reached, either the next
length exists or the current path is endpoint-unextendable.  We also record
the elementary fact that a large enough clique contains every graph of the
corresponding order.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos570

/-- Every graph whose vertex type has cardinality at most a clique embeds in
the ambient graph containing that clique. -/
theorem isContained_of_isClique_card
    {W V : Type*} [Fintype W] [Fintype V] [DecidableEq V]
    {H : SimpleGraph W} {G : SimpleGraph V} {U : Finset V}
    (hU : G.IsClique (U : Set V)) (hcard : Fintype.card W ≤ U.card) :
    H ⊑ G := by
  classical
  obtain ⟨T, hTU, hTcard⟩ := Finset.exists_subset_card_eq hcard
  let e : W ≃ T := Fintype.equivOfCardEq (by simp [hTcard])
  let f : W → V := fun w ↦ (e w).1
  have hfinj : Function.Injective f := by
    intro x y hxy
    apply e.injective
    apply Subtype.ext
    exact hxy
  let hom : H →g G :=
    { toFun := f
      map_rel' := by
        intro x y hxy
        apply hU (hTU (e x).2) (hTU (e y).2)
        intro heq
        exact hxy.ne (hfinj heq) }
  exact ⟨hom.toCopy hfinj⟩

/-- An edge, represented as a two-entry endpoint path. -/
def edgeEndpointPath {V : Type*} (a b : V) : Fin 2 → V :=
  Fin.cons a (Fin.cons b Fin.elim0)

@[simp] theorem edgeEndpointPath_zero {V : Type*} (a b : V) :
    edgeEndpointPath a b 0 = a := by
  simp [edgeEndpointPath]

@[simp] theorem edgeEndpointPath_last {V : Type*} (a b : V) :
    edgeEndpointPath a b (Fin.last 1) = b := by
  simp [edgeEndpointPath]

theorem edgeEndpointPath_isEndpointPath
    {V : Type*} {G : SimpleGraph V} {a b : V} (hab : G.Adj a b) :
    IsEndpointPath G (edgeEndpointPath a b) := by
  constructor
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [edgeEndpointPath]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [edgeEndpointPath]

/-- Grow an endpoint path to a prescribed number `t` of internal vertices,
or stop at an endpoint-unextendable path with fewer than `t` internal
vertices. -/
theorem exists_endpointPath_or_unextendable
    {V : Type*} {G : SimpleGraph V} {a b : V} (hab : G.Adj a b) (t : ℕ) :
    (∃ p : Fin (t + 2) → V, IsEndpointPath G p ∧
        p 0 = a ∧ p (Fin.last (t + 1)) = b) ∨
      ∃ n < t, ∃ p : Fin (n + 2) → V, IsEndpointPath G p ∧
        p 0 = a ∧ p (Fin.last (n + 1)) = b ∧ EndpointUnextendable G p := by
  induction t with
  | zero =>
      left
      exact ⟨edgeEndpointPath a b, edgeEndpointPath_isEndpointPath hab,
        edgeEndpointPath_zero a b, edgeEndpointPath_last a b⟩
  | succ t ih =>
      rcases ih with hexact | hstop
      · obtain ⟨p, hp, hp0, hplast⟩ := hexact
        by_cases hmax : EndpointUnextendable G p
        · right
          exact ⟨t, by omega, p, hp, hp0, hplast, hmax⟩
        · have hext : ∃ q : Fin (t + 3) → V, IsEndpointPath G q ∧
              q 0 = p 0 ∧ q (Fin.last (t + 2)) = p (Fin.last (t + 1)) := by
            by_contra h
            exact hmax h
          obtain ⟨q, hq, hq0, hqlast⟩ := hext
          left
          exact ⟨q, hq, hq0.trans hp0, hqlast.trans hplast⟩
      · obtain ⟨n, hnt, p, hp, hp0, hplast, hmax⟩ := hstop
        right
        exact ⟨n, by omega, p, hp, hp0, hplast, hmax⟩

/-- Grow an already available endpoint path by at most `d` further internal
vertices.  If the final length is not reached, the first obstruction occurs
at an internal-vertex count between `ℓ` and `ℓ+d-1`. -/
theorem exists_endpointPath_extension_or_unextendable
    {V : Type*} {G : SimpleGraph V} {a b : V} {ℓ : ℕ}
    (base : Fin (ℓ + 2) → V) (hbase : IsEndpointPath G base)
    (hbase0 : base 0 = a) (hbaseLast : base (Fin.last (ℓ + 1)) = b)
    (d : ℕ) :
    (∃ p : Fin (ℓ + d + 2) → V, IsEndpointPath G p ∧
        p 0 = a ∧ p (Fin.last (ℓ + d + 1)) = b) ∨
      ∃ n, ℓ ≤ n ∧ n < ℓ + d ∧
        ∃ p : Fin (n + 2) → V, IsEndpointPath G p ∧
          p 0 = a ∧ p (Fin.last (n + 1)) = b ∧
            EndpointUnextendable G p := by
  induction d with
  | zero =>
      left
      simpa using ⟨base, hbase, hbase0, hbaseLast⟩
  | succ d ih =>
      rcases ih with hexact | hstop
      · obtain ⟨p, hp, hp0, hplast⟩ := hexact
        by_cases hmax : EndpointUnextendable G p
        · right
          exact ⟨ℓ + d, by omega, by omega, p, hp, hp0, hplast, hmax⟩
        · have hext : ∃ q : Fin (ℓ + d + 3) → V, IsEndpointPath G q ∧
              q 0 = p 0 ∧
                q (Fin.last (ℓ + d + 2)) = p (Fin.last (ℓ + d + 1)) := by
            by_contra h
            exact hmax h
          obtain ⟨q, hq, hq0, hqlast⟩ := hext
          left
          exact ⟨q, hq, hq0.trans hp0, hqlast.trans hplast⟩
      · obtain ⟨n, hℓn, hn, p, hp, hp0, hplast, hmax⟩ := hstop
        right
        exact ⟨n, hℓn, by omega, p, hp, hp0, hplast, hmax⟩

end Erdos570
