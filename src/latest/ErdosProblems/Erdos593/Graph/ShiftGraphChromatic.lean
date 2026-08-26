import ErdosProblems.Erdos593.Graph.ShiftGraph
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Order.Fin.Basic
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.Tactic

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Chromatic growth of finite shift graphs

This file proves the standard Erdős--Rado coloring descent for finite shift
graphs.  A coloring of the shift graph on `(r + 1)`-tuples induces a coloring
of the graph on `r`-tuples whose colors are sets of old colors.  Iterating the
construction reduces to the complete graph on increasing one-tuples.
-/

namespace Erdos593

open scoped Cardinal

universe u v

namespace ShiftGraph

variable {κ : Type u} [LinearOrder κ]

/-- Delete the last entry of an increasing tuple. -/
def init {r : ℕ} (z : Tuple κ (r + 1)) : Tuple κ r :=
  ⟨fun i ↦ z.1 i.castSucc, z.2.comp Fin.strictMono_castSucc⟩

/-- Delete the first entry of an increasing tuple. -/
def tail {r : ℕ} (z : Tuple κ (r + 1)) : Tuple κ r :=
  ⟨fun i ↦ z.1 i.succ, z.2.comp Fin.strictMono_succ⟩

@[simp]
theorem init_apply {r : ℕ} (z : Tuple κ (r + 1)) (i : Fin r) :
    (init z).1 i = z.1 i.castSucc := rfl

@[simp]
theorem tail_apply {r : ℕ} (z : Tuple κ (r + 1)) (i : Fin r) :
    (tail z).1 i = z.1 i.succ := rfl

theorem shift_iff_exists_init_tail {r : ℕ} {x y : Tuple κ r} :
    Shift κ x y ↔ ∃ z : Tuple κ (r + 1), init z = x ∧ tail z = y := by
  constructor
  · rintro ⟨z, hx, hy⟩
    refine ⟨z, Subtype.ext ?_, Subtype.ext ?_⟩
    · funext i
      exact (hx i).symm
    · funext i
      exact (hy i).symm
  · rintro ⟨z, rfl, rfl⟩
    exact ⟨z, fun _ ↦ rfl, fun _ ↦ rfl⟩

/-- Glue two overlapping nonempty windows into one longer tuple. -/
def glue {r : ℕ} (hr : 0 < r) (z w : Tuple κ (r + 1))
    (h : tail z = init w) : Tuple κ (r + 2) :=
  ⟨Fin.cons (z.1 0) w.1, by
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · have hz := (Fin.strictMono_iff_lt_succ.mp z.2) (⟨0, hr⟩ : Fin r)
      have hover := congrArg (fun q : Tuple κ r ↦ q.1 (⟨0, hr⟩ : Fin r)) h
      simpa [tail, init] using! hz.trans_eq hover
    · simpa using! (Fin.strictMono_iff_lt_succ.mp w.2) j⟩

@[simp]
theorem init_glue {r : ℕ} (hr : 0 < r) (z w : Tuple κ (r + 1))
    (h : tail z = init w) : init (glue hr z w h) = z := by
  apply Subtype.ext
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · rfl
  · have hover := congrArg (fun q : Tuple κ r ↦ q.1 j) h
    simpa [glue, tail, init] using! hover.symm

@[simp]
theorem tail_glue {r : ℕ} (hr : 0 < r) (z w : Tuple κ (r + 1))
    (h : tail z = init w) : tail (glue hr z w h) = w := by
  apply Subtype.ext
  funext i
  rfl

theorem shift_of_tail_eq_init {r : ℕ} (hr : 0 < r) {z w : Tuple κ (r + 1)}
    (h : tail z = init w) : Shift κ z w := by
  exact (shift_iff_exists_init_tail).2 ⟨glue hr z w h, init_glue hr z w h, tail_glue hr z w h⟩

/-- The colors occurring among one-step right extensions of a tuple. -/
def extensionColors {C : Type v} {r : ℕ}
    (c : (graph κ (r + 1)).Coloring C) (x : Tuple κ r) : Set C :=
  {a | ∃ z : Tuple κ (r + 1), init z = x ∧ c z = a}

theorem extensionColors_ne_of_shift {C : Type v} {r : ℕ} (hr : 0 < r)
    (c : (graph κ (r + 1)).Coloring C) {x y : Tuple κ r} (hxy : Shift κ x y) :
    extensionColors c x ≠ extensionColors c y := by
  obtain ⟨z, hz_init, hz_tail⟩ := (shift_iff_exists_init_tail).1 hxy
  intro heq
  have hz_mem : c z ∈ extensionColors c x := ⟨z, hz_init, rfl⟩
  rw [heq] at hz_mem
  obtain ⟨w, hw_init, hcw⟩ := hz_mem
  have hzw : Shift κ z w := shift_of_tail_eq_init hr (hz_tail.trans hw_init.symm)
  exact c.valid (adj_of_shift κ (Nat.succ_pos r) hzw) hcw.symm

/-- A coloring of the `(r+1)`-shift graph induces a coloring of the `r`-shift
graph by sets of colors. -/
noncomputable def lowerColoring {C : Type v} {r : ℕ} (hr : 0 < r)
    (c : (graph κ (r + 1)).Coloring C) : (graph κ r).Coloring (Set C) :=
  SimpleGraph.Coloring.mk (extensionColors c) fun {x y} hxy ↦ by
    rw [adj_iff_shift_or_shift κ hr] at hxy
    rcases hxy with hxy | hyx
    · exact extensionColors_ne_of_shift hr c hxy
    · exact (extensionColors_ne_of_shift hr c hyx).symm

/-- A coloring of the one-dimensional shift graph is injective, since that
shift graph is complete. -/
theorem coloring_one_injective {C : Type v}
    (c : (graph κ 1).Coloring C) : Function.Injective c := by
  intro x y hxy
  by_contra hne
  exact c.valid (by rw [graph_one_eq_completeGraph]; simpa) hxy

/-- The type obtained by iterating the powerset operation `n` times. -/
def IteratedSet (C : Type v) : ℕ → Type v
  | 0 => C
  | n + 1 => IteratedSet (Set C) n

/-- Iterating coloring descent reaches the complete one-dimensional shift
graph, with an iterated powerset as color type. -/
noncomputable def lowerToOne {C : Type v} :
    ∀ n : ℕ, (graph κ (n + 1)).Coloring C →
      (graph κ 1).Coloring (IteratedSet C n)
  | 0, c => c
  | n + 1, c => lowerToOne n (lowerColoring (Nat.succ_pos n) c)

/-- Moving one successor outside the iterated-powerset definition. -/
theorem iteratedSet_succ (C : Type v) (n : ℕ) :
    IteratedSet C (n + 1) = Set (IteratedSet C n) := by
  induction n generalizing C with
  | zero => rfl
  | succ n ih => simpa only [IteratedSet] using! ih (Set C)

/-- The cardinality of the `n`-fold powerset of `ℕ` is `ℶ_n`. -/
theorem mk_iteratedSet_nat (n : ℕ) :
    #(IteratedSet ℕ n) = ℶ_ (n : Ordinal) := by
  induction n with
  | zero => simp [IteratedSet, Cardinal.beth_zero]
  | succ n ih =>
    rw [iteratedSet_succ, Cardinal.mk_set, ih, ← Cardinal.beth_succ]
    change ℶ_ ((n : Ordinal) + 1) = ℶ_ (((n + 1 : ℕ) : Ordinal))
    rw [Nat.cast_add_one]

/-- Increasing one-tuples are canonically equivalent to their entries. -/
def tupleOneEquiv : Tuple κ 1 ≃ κ where
  toFun x := x.1 0
  invFun x := ⟨fun _ => x, by simp [StrictMono]⟩
  left_inv x := by ext i; fin_cases i; rfl
  right_inv _ := rfl

/-- If `κ` is larger than `ℶ_(r-1)`, the `r`th shift graph admits no coloring
by natural numbers. -/
theorem not_nonempty_coloring_nat_of_beth_lt {r : ℕ} (hr : 0 < r)
    (hκ : ℶ_ ((r - 1 : ℕ) : Ordinal) < #κ) :
    ¬ Nonempty ((graph κ r).Coloring ℕ) := by
  rintro ⟨c⟩
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  have hinj : Function.Injective (lowerToOne n c) := coloring_one_injective _
  have hle0 := Cardinal.lift_mk_le_lift_mk_of_injective hinj
  have hle : #κ ≤ ℶ_ (n : Ordinal) := by
    rw [mk_iteratedSet_nat, Cardinal.lift_beth, Ordinal.lift_natCast] at hle0
    simpa only [Cardinal.lift_uzero, Cardinal.mk_congr tupleOneEquiv] using! hle0
  rw [Nat.succ_sub_one] at hκ
  exact (not_lt_of_ge hle) hκ

end ShiftGraph

end Erdos593
