import ErdosProblems.Erdos593.Graph.OddClosedWalk
import ErdosProblems.Erdos593.Graph.ShiftGraph

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Odd girth of finite shift graphs

The shift graph on increasing `r`-tuples has no odd cycle shorter than
`2 * r + 1`.  The proof rotates a cycle to a tuple whose first coordinate is
minimal.  Both incident edges then point away from that tuple.  After deleting
those two edges, projection to the first `r - 1` coordinates gives an odd
closed walk two edges shorter in the lower-dimensional shift graph.
-/

namespace Erdos593

universe u

namespace ShiftGraph

variable (κ : Type u) [LinearOrder κ]

/-- Delete the last coordinate of a nonempty increasing tuple. -/
def initTuple {r : ℕ} (x : Tuple κ (r + 1)) : Tuple κ r :=
  ⟨fun i => x.1 i.castSucc, fun _ _ hij => x.2 (Fin.castSucc_lt_castSucc_iff.mpr hij)⟩

/-- A shift of nonempty tuples strictly increases the first coordinate. -/
theorem first_lt_first_of_shift {r : ℕ} {x y : Tuple κ (r + 1)}
    (h : Shift κ x y) : x.1 0 < y.1 0 := by
  obtain ⟨z, hx, hy⟩ := h
  rw [hx 0, hy 0]
  exact z.2 (by simp)

/-- Prefix projection respects a directed shift, provided the projected tuple
is still nonempty. -/
theorem shift_prefix {r : ℕ} (_hr : 0 < r) {x y : Tuple κ (r + 1)}
    (h : Shift κ x y) : Shift κ (initTuple κ x) (initTuple κ y) := by
  obtain ⟨z, hx, hy⟩ := h
  refine ⟨x, ?_, ?_⟩
  · intro i
    rfl
  · intro i
    change y.1 i.castSucc = x.1 i.succ
    rw [hy i.castSucc, hx i.succ]
    rfl

/-- Prefix projection is a graph homomorphism between consecutive positive
shift graphs. -/
def prefixHom {r : ℕ} (hr : 0 < r) : graph κ (r + 1) →g graph κ r where
  toFun := initTuple κ
  map_rel' := by
    intro x y hxy
    rw [adj_iff_shift_or_shift κ (Nat.succ_pos r)] at hxy
    rw [adj_iff_shift_or_shift κ hr]
    exact hxy.imp (shift_prefix κ hr) (shift_prefix κ hr)

/-- Two outward shifts from the same tuple have the same prefix. -/
theorem prefix_eq_of_shift_of_shift {r : ℕ} {x y z : Tuple κ (r + 1)}
    (hxy : Shift κ x y) (hxz : Shift κ x z) : initTuple κ y = initTuple κ z := by
  obtain ⟨w, hxw, hyw⟩ := hxy
  obtain ⟨w', hxw', hzw'⟩ := hxz
  ext i
  change y.1 i.castSucc = z.1 i.castSucc
  rw [hyw i.castSucc, hzw' i.castSucc]
  have hi : i.castSucc.succ = i.succ.castSucc := Fin.ext rfl
  rw [hi, ← hxw i.succ, ← hxw' i.succ]

/-- Every odd simple cycle in the shift graph on increasing `r`-tuples has
length at least `2 * r + 1`. -/
theorem odd_cycle_length_ge :
    ∀ (r : ℕ) {v : Tuple κ r} (c : (graph κ r).Walk v v),
      c.IsCycle → Odd c.length → 2 * r + 1 ≤ c.length := by
  intro r
  induction r with
  | zero =>
      intro v c hc _
      exact Nat.le_trans (by omega) hc.three_le_length
  | succ r ih =>
      intro v c hc hodd
      by_cases hr : r = 0
      · subst r
        exact hc.three_le_length
      · have hrpos : 0 < r := Nat.pos_of_ne_zero hr
        by_contra hbound
        have hclt : c.length < 2 * (r + 1) + 1 := by omega
        classical
        obtain ⟨x, hxc, hxmin⟩ :=
          Finset.exists_min_image c.support.toFinset (fun t => t.1 0)
            (by simp)
        have hxsupp : x ∈ c.support := by simpa using! hxc
        let d := c.rotate x hxsupp
        have hdcycle : d.IsCycle := hc.rotate hxsupp
        have hdlen : d.length = c.length := c.length_rotate x hxsupp
        have hmin : ∀ y ∈ d.support, x.1 0 ≤ y.1 0 := by
          intro y hy
          apply hxmin y
          simpa [d, c.mem_support_rotate_iff x hxsupp] using! hy
        have hdnotnil : ¬ d.Nil := hdcycle.not_nil
        let y := d.snd
        let p := d.tail
        have hpnotnil : ¬ p.Nil := by
          intro hp
          have hpzero : p.length = 0 :=
            SimpleGraph.Walk.length_eq_zero_iff.mpr hp
          have htail := d.length_tail_add_one hdnotnil
          have hthree := hdcycle.three_le_length
          simp only [p] at hpzero
          omega
        have hadj : (graph κ (r + 1)).Adj x y := by
          simpa [y, d] using! d.adj_snd hdnotnil
        have hxy : Shift κ x y := by
          rw [adj_iff_shift_or_shift κ (Nat.succ_pos r)] at hadj
          rcases hadj with hxy | hyx
          · exact hxy
          · have hylt := first_lt_first_of_shift κ hyx
            have hy_mem : y ∈ d.support := by
              exact List.mem_of_mem_tail (by simpa [y, p] using! d.snd_mem_tail_support hdnotnil)
            have hymin : x.1 0 ≤ y.1 0 := hmin y hy_mem
            exact (not_lt_of_ge hymin hylt).elim
        have hxp : Shift κ x p.penultimate := by
          have hadj' := p.adj_penultimate hpnotnil
          rw [adj_iff_shift_or_shift κ (Nat.succ_pos r)] at hadj'
          rcases hadj' with hpx | hxp
          · have hplt := first_lt_first_of_shift κ hpx
            have hp_mem_p : p.penultimate ∈ p.support :=
              List.mem_of_mem_dropLast (p.penultimate_mem_dropLast_support hpnotnil)
            have hp_mem_d : p.penultimate ∈ d.support := by
              apply List.mem_of_mem_tail
              rw [← d.support_tail_of_not_nil hdnotnil]
              simpa [p] using! hp_mem_p
            have hpmin : x.1 0 ≤ p.penultimate.1 0 := hmin _ hp_mem_d
            exact (not_lt_of_ge hpmin hplt).elim
          · exact hxp
        have hpref : initTuple κ y = initTuple κ p.penultimate :=
          prefix_eq_of_shift_of_shift κ hxy hxp
        let q : (graph κ r).Walk (initTuple κ y) (initTuple κ y) :=
          (p.dropLast.map (prefixHom κ hrpos)).copy rfl hpref.symm
        have hqlen : q.length = c.length - 2 := by
          have htail := d.length_tail_add_one hdnotnil
          simp only [q, SimpleGraph.Walk.length_map, SimpleGraph.Walk.length_copy,
            SimpleGraph.Walk.length_dropLast]
          simp only [p] at htail ⊢
          omega
        have hqodd : Odd q.length := by
          obtain ⟨k, hk⟩ := hodd
          refine ⟨k - 1, ?_⟩
          rw [hqlen]
          have := hc.three_le_length
          omega
        exact (Erdos593.SimpleGraph.no_odd_closedWalk_up_to_of_no_odd_cycle_up_to
          (graph κ r) (2 * r)
          (fun {_} e he hle heodd => by
            have := ih e he heodd
            omega)
          q (by rw [hqlen]; omega)) hqodd

/-- Bounded formulation of the odd-girth estimate. -/
theorem no_odd_cycle_up_to {r m : ℕ} (hm : m < 2 * r + 1) :
    ∀ ⦃v : Tuple κ r⦄ (c : (graph κ r).Walk v v),
      c.IsCycle → c.length ≤ m → ¬ Odd c.length := by
  intro v c hc hcm hodd
  have := odd_cycle_length_ge κ r c hc hodd
  omega

/-- Consequently, no odd closed walk has length below the odd-girth bound. -/
theorem no_odd_closedWalk_up_to {r m : ℕ} (hm : m < 2 * r + 1) :
    ∀ ⦃v : Tuple κ r⦄ (w : (graph κ r).Walk v v),
      w.length ≤ m → ¬ Odd w.length :=
  Erdos593.SimpleGraph.no_odd_closedWalk_up_to_of_no_odd_cycle_up_to
    (graph κ r) m (no_odd_cycle_up_to κ hm)

end ShiftGraph

end Erdos593
