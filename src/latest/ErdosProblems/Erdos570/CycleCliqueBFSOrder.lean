/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos570.CycleCliqueBFSTree

/-!
# Lexicographic order on a finite BFS tree

An ancestral address is encoded in base `|V|+1`.  At a fixed level this is
the recursive EFRS order: vertices are grouped by their parents, and the
children within each group are ordered by an arbitrary injective vertex
rank.  Numeric encoding makes the prefix/interval facts elementary.
-/

noncomputable section

namespace Erdos570

namespace BFSTree

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {root : V}

/-- An arbitrary injective rank of the finite vertex type. -/
def vertexRank (v : V) : ℕ := (Fintype.equivFin V v).val

theorem vertexRank_lt (v : V) : vertexRank v < Fintype.card V :=
  (Fintype.equivFin V v).isLt

theorem vertexRank_injective : Function.Injective (vertexRank (V := V)) := by
  intro u v huv
  apply (Fintype.equivFin V).injective
  apply Fin.ext
  exact huv

/-- Base-`|V|+1` ancestral address of depth `d`. -/
def orderKey (T : BFSTree G root) : ℕ → V → ℕ
  | 0, v => vertexRank v
  | d + 1, v =>
      orderKey T d (T.parent v) * (Fintype.card V + 1) + vertexRank v

@[simp] theorem orderKey_zero (T : BFSTree G root) (v : V) :
    T.orderKey 0 v = vertexRank v := rfl

@[simp] theorem orderKey_succ (T : BFSTree G root) (d : ℕ) (v : V) :
    T.orderKey (d + 1) v =
      T.orderKey d (T.parent v) * (Fintype.card V + 1) + vertexRank v :=
  rfl

theorem orderKey_mod (T : BFSTree G root) (d : ℕ) (v : V) :
    T.orderKey d v % (Fintype.card V + 1) = vertexRank v := by
  cases d with
  | zero =>
      exact Nat.mod_eq_of_lt
        ((vertexRank_lt v).trans (Nat.lt_succ_self _))
  | succ d =>
      rw [orderKey_succ, Nat.add_mod, Nat.mul_mod]
      have hr := (vertexRank_lt v).trans (Nat.lt_succ_self _)
      simp [Nat.mod_eq_of_lt hr]

theorem orderKey_injective (T : BFSTree G root) (d : ℕ) :
    Function.Injective (T.orderKey d) := by
  intro u v huv
  have hmod := congrArg (fun z ↦ z % (Fintype.card V + 1)) huv
  rw [T.orderKey_mod d u, T.orderKey_mod d v] at hmod
  exact vertexRank_injective hmod

/-- Comparing addresses compares their parent prefixes weakly. -/
theorem orderKey_parent_le_of_lt
    (T : BFSTree G root) (d : ℕ) {u v : V}
    (h : T.orderKey (d + 1) u < T.orderKey (d + 1) v) :
    T.orderKey d (T.parent u) ≤ T.orderKey d (T.parent v) := by
  let q := Fintype.card V + 1
  let A := T.orderKey d (T.parent u)
  let B := T.orderKey d (T.parent v)
  let r := vertexRank u
  let s := vertexRank v
  have hq : 0 < q := by simp [q]
  have hr : r < q := by
    exact (vertexRank_lt u).trans (by simp [q])
  have hs : s < q := by
    exact (vertexRank_lt v).trans (by simp [q])
  change A * q + r < B * q + s at h
  by_contra hnot
  have hBA : B + 1 ≤ A := by omega
  have hmul : (B + 1) * q ≤ A * q :=
    Nat.mul_le_mul_right q hBA
  have hsq : B * q + s < (B + 1) * q := by
    rw [Nat.add_mul, one_mul]
    exact Nat.add_lt_add_left hs (B * q)
  omega

/-- Repeated prefix comparison: order at level `i` induces weak order on
every pair of `r`th ancestors. -/
theorem orderKey_ancestor_le_of_lt
    (T : BFSTree G root) {i r : ℕ} (hri : r ≤ i) {u v : V}
    (h : T.orderKey i u < T.orderKey i v) :
    T.orderKey (i - r) (T.ancestor r u) ≤
      T.orderKey (i - r) (T.ancestor r v) := by
  induction r generalizing i u v with
  | zero => simpa using h.le
  | succ r ih =>
      have hi : 1 ≤ i := by omega
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      have hp := T.orderKey_parent_le_of_lt j h
      have hrj : r ≤ j := by omega
      by_cases heq : T.orderKey j (T.parent u) = T.orderKey j (T.parent v)
      · have huv : T.parent u = T.parent v := T.orderKey_injective j heq
        rw [T.ancestor_succ_parent, T.ancestor_succ_parent, huv]
      · have hplt : T.orderKey j (T.parent u) < T.orderKey j (T.parent v) :=
          lt_of_le_of_ne hp heq
        have hih := ih hrj hplt
        simpa [T.ancestor_succ_parent, T.parent_ancestor,
          Nat.add_sub_cancel] using hih

/-- An interval in the address order remains an interval after taking any
fixed number of ancestors. -/
theorem ancestor_eq_of_orderKey_between
    (T : BFSTree G root) {i r : ℕ} (hri : r ≤ i)
    {u w v : V}
    (huw : T.orderKey i u < T.orderKey i w)
    (hwv : T.orderKey i w < T.orderKey i v)
    (huv : T.ancestor r u = T.ancestor r v) :
    T.ancestor r w = T.ancestor r u := by
  have hleft := T.orderKey_ancestor_le_of_lt hri huw
  have hright := T.orderKey_ancestor_le_of_lt hri hwv
  have hend : T.orderKey (i - r) (T.ancestor r u) =
      T.orderKey (i - r) (T.ancestor r v) := by rw [huv]
  have hkey : T.orderKey (i - r) (T.ancestor r w) =
      T.orderKey (i - r) (T.ancestor r u) := by omega
  exact T.orderKey_injective (i - r) hkey

/-- Closed-interval version of `ancestor_eq_of_orderKey_between`.  Equality
at either end is handled using injectivity of the address. -/
theorem ancestor_eq_of_orderKey_closed_between
    (T : BFSTree G root) {i r : ℕ} (hri : r ≤ i)
    {u w v : V}
    (huw : T.orderKey i u ≤ T.orderKey i w)
    (hwv : T.orderKey i w ≤ T.orderKey i v)
    (huv : T.ancestor r u = T.ancestor r v) :
    T.ancestor r w = T.ancestor r u := by
  rcases huw.eq_or_lt with heq | hlt
  · have huw' : u = w := T.orderKey_injective i heq
    subst w
    rfl
  · rcases hwv.eq_or_lt with heq | hlt'
    · have hwv' : w = v := T.orderKey_injective i heq
      subst w
      exact huv.symm
    · exact T.ancestor_eq_of_orderKey_between hri hlt hlt' huv

end BFSTree

end Erdos570
