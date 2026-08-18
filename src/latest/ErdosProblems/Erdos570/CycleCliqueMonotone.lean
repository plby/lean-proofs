/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos570.CycleCliqueBFSOrder

/-!
# Increasing paths in an ordered BFS level

The EFRS level argument colors each vertex by the maximum length of a path
whose ancestral addresses increase at every step.  An edge always joins two
different color classes unless such a path has the forbidden maximum length.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos570

namespace BFSTree

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {root : V}

/-- A path with `s` edges, starting at `v`, along which the fixed-level
ancestral address is strictly increasing. -/
def MonotonePathFrom (T : BFSTree G root) (i s : ℕ) (v : V) : Prop :=
  ∃ f : Fin (s + 1) → V,
    f 0 = v ∧
    (∀ j, G.dist root (f j) = i) ∧
    StrictMono (fun j ↦ T.orderKey i (f j)) ∧
    ∀ j : Fin s, G.Adj (f j.castSucc) (f j.succ)

theorem monotonePathFrom_zero (T : BFSTree G root) (i : ℕ) (v : V)
    (hv : G.dist root v = i) :
    T.MonotonePathFrom i 0 v := by
  refine ⟨fun _ ↦ v, rfl, fun _ ↦ hv, ?_, ?_⟩
  · rw [Fin.strictMono_iff_lt_succ]
    exact fun j ↦ Fin.elim0 j
  · exact fun j ↦ Fin.elim0 j

/-- A smaller adjacent vertex can be prepended to an increasing path. -/
theorem MonotonePathFrom.prepend
    (T : BFSTree G root) {i s : ℕ} {u v : V}
    (huv : G.Adj u v)
    (hu : G.dist root u = i)
    (hkey : T.orderKey i u < T.orderKey i v)
    (hpath : T.MonotonePathFrom i s v) :
    T.MonotonePathFrom i (s + 1) u := by
  obtain ⟨f, hf0, hflevel, hfmono, hfadj⟩ := hpath
  let g : Fin (s + 2) → V := Fin.cons u f
  refine ⟨g, by simp [g], ?_, ?_, ?_⟩
  · intro j
    induction j using Fin.cases with
    | zero => simpa [g] using hu
    | succ j => simpa [g] using hflevel j
  · rw [Fin.strictMono_iff_lt_succ]
    intro j
    induction j using Fin.cases with
    | zero => simpa [g, hf0] using hkey
    | succ j =>
        have h := (Fin.strictMono_iff_lt_succ.mp hfmono) j
        simpa [g] using h
  · intro j
    induction j using Fin.cases with
    | zero => simpa [g, hf0] using huv
    | succ j => simpa [g] using hfadj j

theorem MonotonePathFrom.injective
    (T : BFSTree G root) {i s : ℕ} {v : V}
    (hpath : T.MonotonePathFrom i s v) :
    ∃ f : Fin (s + 1) → V,
      f 0 = v ∧ (∀ j, G.dist root (f j) = i) ∧ Function.Injective f ∧
        StrictMono (fun j ↦ T.orderKey i (f j)) ∧
        ∀ j : Fin s, G.Adj (f j.castSucc) (f j.succ) := by
  obtain ⟨f, hf0, hflevel, hfmono, hfadj⟩ := hpath
  refine ⟨f, hf0, hflevel, ?_, hfmono, hfadj⟩
  exact Function.Injective.of_comp hfmono.injective

/-- An initial segment of an increasing path is again an increasing path. -/
theorem MonotonePathFrom.prefix
    (T : BFSTree G root) {i r s : ℕ} {v : V}
    (hrs : r ≤ s) (hpath : T.MonotonePathFrom i s v) :
    T.MonotonePathFrom i r v := by
  obtain ⟨f, hf0, hflevel, hfmono, hfadj⟩ := hpath
  let e : Fin (r + 1) → Fin (s + 1) :=
    Fin.castLE (Nat.add_le_add_right hrs 1)
  let g : Fin (r + 1) → V := fun j ↦ f (e j)
  refine ⟨g, ?_, ?_, ?_, ?_⟩
  · simpa [g, e] using hf0
  · intro j
    exact hflevel (e j)
  · exact hfmono.comp (Fin.strictMono_castLE _)
  · intro j
    have h := hfadj (Fin.castLE hrs j)
    simpa [g, e] using h

/-- Maximum number of edges in an increasing path from `v`. -/
def monotoneHeight (T : BFSTree G root) (i : ℕ) (v : V) : ℕ :=
  @Nat.findGreatest (fun s ↦ T.MonotonePathFrom i s v)
    (Classical.decPred _) (Fintype.card V)

theorem monotoneHeight_spec (T : BFSTree G root) (i : ℕ) (v : V)
    (hv : G.dist root v = i) :
    T.MonotonePathFrom i (T.monotoneHeight i v) v := by
  classical
  simpa only [monotoneHeight] using
    (Nat.findGreatest_spec (P := fun s ↦ T.MonotonePathFrom i s v)
      (n := Fintype.card V) (Nat.zero_le _)
      (T.monotonePathFrom_zero i v hv))

theorem monotoneHeight_le_card (T : BFSTree G root) (i : ℕ) (v : V) :
    T.monotoneHeight i v ≤ Fintype.card V :=
  by
    classical
    simpa only [monotoneHeight] using
      (Nat.findGreatest_le (P := fun s ↦ T.MonotonePathFrom i s v)
        (Fintype.card V))

/-- Orienting an edge in the address order raises the maximum path height
by at least one in the reverse direction. -/
theorem monotoneHeight_succ_le
    (T : BFSTree G root) {i : ℕ} {u v : V}
    (huv : G.Adj u v)
    (hu : G.dist root u = i) (hv : G.dist root v = i)
    (hkey : T.orderKey i u < T.orderKey i v) :
    T.monotoneHeight i v + 1 ≤ T.monotoneHeight i u := by
  have hp := MonotonePathFrom.prepend T huv hu hkey
    (T.monotoneHeight_spec i v hv)
  obtain ⟨f, -, -, hfinj, -, -⟩ := hp.injective
  have hcard : T.monotoneHeight i v + 1 ≤ Fintype.card V := by
    have hstrong := Fintype.card_le_of_injective f hfinj
    simp only [Fintype.card_fin] at hstrong
    omega
  classical
  simpa only [monotoneHeight] using
    (Nat.le_findGreatest (P := fun s ↦ T.MonotonePathFrom i s u)
      (n := Fintype.card V) hcard hp)

/-- If no increasing path has `s` edges, every maximum height is below `s`. -/
theorem monotoneHeight_lt_of_not_path
    (T : BFSTree G root) {i s : ℕ} {v : V}
    (hs : s ≤ Fintype.card V)
    (hv : G.dist root v = i)
    (hno : ¬ T.MonotonePathFrom i s v) :
    T.monotoneHeight i v < s := by
  by_contra hnot
  have hle : s ≤ T.monotoneHeight i v := Nat.le_of_not_gt hnot
  exact hno ((T.monotoneHeight_spec i v hv).prefix T hle)

end BFSTree

end Erdos570
