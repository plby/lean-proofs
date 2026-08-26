import ErdosProblems.Erdos556.Basic

/-!
# Path operations for connecting gadgets

We record first-entry paths and concatenation under a precise support
intersection hypothesis. These lemmas make vertex avoidance explicit.
-/

namespace Erdos556

open SimpleGraph

theorem exists_path_first_meeting_set {V : Type*} {G : SimpleGraph V}
    {u v : V} (p : G.Walk u v) (hp : p.IsPath) (S : Set V) (hv : v ∈ S) :
    ∃ w ∈ S, ∃ q : G.Walk u w, q.IsPath ∧ q.length ≤ p.length ∧
      q.support ⊆ p.support ∧ ∀ x ∈ q.support, x ∈ S → x = w := by
  classical
  let P (m : ℕ) : Prop := ∃ w ∈ S, ∃ q : G.Walk u w,
    q.IsPath ∧ q.support ⊆ p.support ∧ q.length = m
  have hex : ∃ m, P m := ⟨p.length, v, hv, p, hp, List.Subset.refl _, rfl⟩
  obtain ⟨w, hw, q, hq, hsub, hlen⟩ := Nat.find_spec hex
  have hmin {z : V} (hz : z ∈ S) (r : G.Walk u z) (hr : r.IsPath)
      (hrs : r.support ⊆ p.support) : q.length ≤ r.length := by
    rw [hlen]
    exact Nat.find_min' hex ⟨z, hz, r, hr, hrs, rfl⟩
  refine ⟨w, hw, q, hq, hmin hv p hp (List.Subset.refl _), hsub, ?_⟩
  intro x hx hxS
  by_contra hxw
  have hlt := q.length_takeUntil_lt_length hx hxw
  have hle := hmin hxS (q.takeUntil x hx) (hq.takeUntil hx)
    (fun _ hz => hsub (q.support_takeUntil_subset_support hx hz))
  omega

/-- Two paths concatenate to a path when their only possible common vertex
is the endpoint at which they are joined. -/
theorem isPath_append_of_support_inter {V : Type*} {G : SimpleGraph V}
    {u v w : V} (p : G.Walk u v) (q : G.Walk v w)
    (hp : p.IsPath) (hq : q.IsPath)
    (hinter : ∀ x ∈ p.support, x ∈ q.support → x = v) :
    (p.append q).IsPath := by
  induction p with
  | nil => simpa using hq
  | @cons u z v huz p ih =>
      have hp' := hp.of_cons
      have hu : u ∉ p.support := (Walk.cons_isPath_iff huz p).mp hp |>.2
      have huv : u ≠ v := fun h => hu (h ▸ p.end_mem_support)
      have huq : u ∉ q.support := fun h => huv (hinter u (by simp) h)
      have hi : ∀ x ∈ p.support, x ∈ q.support → x = v :=
        fun x hx hxq => hinter x (by simp [hx]) hxq
      exact (ih q hp' hq hi).cons (by
        intro hx
        rcases (Walk.mem_support_append_iff _ _).mp hx with hx | hx
        · exact hu hx
        · exact huq hx)

#print axioms exists_path_first_meeting_set
#print axioms isPath_append_of_support_inter

end Erdos556
