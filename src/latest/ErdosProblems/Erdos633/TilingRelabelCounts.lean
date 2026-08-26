import ErdosProblems.Erdos633.ReferenceRelabelling

/-!
# Transport of actual corner counts through relabelling

The chosen isometry depends only on its image-of-carrier predicate. Equality
of those predicates proves equality of the choices; it is not assumed. Thus
reference relabelling permutes the actual corner counts, while outer
relabelling preserves their total over the three outer vertices.
-/

namespace Erdos633

open scoped BigOperators

theorem exists_choose_eq_of_predicate_eq {α : Type*} {p q : α → Prop}
    (h : p = q) (hp : ∃ a, p a) (hq : ∃ a, q a) :
    Classical.choose hp = Classical.choose hq := by
  cases h
  rfl

theorem CongruentTiling.tileIsometry_of_reference_carrier_eq
    {P R S : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (h : S.carrier = R.carrier) (i : Fin N) :
    (T.of_reference_carrier_eq h).tileIsometry i = T.tileIsometry i := by
  unfold CongruentTiling.tileIsometry
  apply exists_choose_eq_of_predicate_eq
  funext e
  rw [h]
  rfl

theorem CongruentTiling.labelled_vertex_of_reference_relabel
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (e : Equiv.Perm (Fin 3)) (i : Fin N) (k : Fin 3) :
    ((T.of_reference_carrier_eq (R.relabel_carrier e)).labelledTile i).vertex k =
      (T.labelledTile i).vertex (e k) := by
  unfold CongruentTiling.labelledTile
  rw [Triangle.vertex_mapIsometry, Triangle.vertex_mapIsometry,
    T.tileIsometry_of_reference_carrier_eq, R.vertex_relabel]

theorem CongruentTiling.cornerCount_of_reference_relabel
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (e : Equiv.Perm (Fin 3)) (z : ℂ) (k : Fin 3) :
    (T.of_reference_carrier_eq (R.relabel_carrier e)).cornerCount z k =
      T.cornerCount z (e k) := by
  classical
  simp only [CongruentTiling.cornerCount, T.labelled_vertex_of_reference_relabel]

theorem CongruentTiling.outerCornerCount_of_reference_relabel
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (e : Equiv.Perm (Fin 3)) (k : Fin 3) :
    (T.of_reference_carrier_eq (R.relabel_carrier e)).outerCornerCount k =
      T.outerCornerCount (e k) := by
  simp only [CongruentTiling.outerCornerCount, T.cornerCount_of_reference_relabel]

theorem CongruentTiling.cornerCount_of_carrier_eq
    {P Q R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (h : P.carrier = Q.carrier) (z : ℂ) (k : Fin 3) :
    (T.of_carrier_eq h).cornerCount z k = T.cornerCount z k := rfl

theorem CongruentTiling.outerCornerCount_of_outer_relabel
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (e : Equiv.Perm (Fin 3)) (k : Fin 3) :
    (T.of_carrier_eq (P.relabel_carrier e).symm).outerCornerCount k = T.outerCornerCount k := by
  simp only [CongruentTiling.outerCornerCount, T.cornerCount_of_carrier_eq, P.vertex_relabel]
  exact Equiv.sum_comp e (fun z => T.cornerCount (P.vertex z) k)

end Erdos633
