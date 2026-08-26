import ErdosProblems.Erdos593.TripleSystem.SequenceLiftBaseFiberSupportBranchGeometry
import ErdosProblems.Erdos593.TripleSystem.SequenceLiftBaseFiberSupportIncidenceGraph

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Acyclicity of base-fibre support incidence graphs

The incidence graph has one vertex for each active canonical base fibre and
one for each point in the selected support.  In a linear restriction, a cycle
would propagate one initial base letter all the way around its fibre-side
vertices.  The two boundary support points would consequently arise from the
same base-fibre edge, contradicting simplicity of the cycle.
-/

namespace Erdos593

universe u

namespace SequenceLift

variable {V : Type u} {G : _root_.SimpleGraph V}

private theorem incidence_cycle_exists_node_support
    {S : Set (Edge G)}
    {v : activeBaseNodeIndex S ⊕ activeBaseFiberSupportPointIndex S}
    (c : (baseFiberSupportIncidenceGraph S).Walk v v)
    (hc : c.IsCycle) :
    ∃ q : activeBaseNodeIndex S, (.inl q :
      activeBaseNodeIndex S ⊕ activeBaseFiberSupportPointIndex S) ∈ c.support := by
  cases v with
  | inl q =>
      refine ⟨q, ?_⟩
      simpa only [c.getVert_zero] using! c.getVert_mem_support 0
  | inr p =>
      have hsnd := c.adj_snd hc.not_nil
      have hlen : 1 ≤ c.length := by
        have hthree := hc.three_le_length
        omega
      cases hs : c.snd with
      | inl q =>
          refine ⟨q, ?_⟩
          apply (c.mem_support_iff_exists_getVert).mpr
          refine ⟨1, ?_, hlen⟩
          simp [hs]
      | inr p' =>
          rw [hs] at hsnd
          exact (not_baseFiberSupportIncidenceGraph_adj_inr_inr hsnd).elim

/-- Rotate a cycle at a fibre-side vertex and expose its two endpoint
fibre--point--fibre segments. -/
private theorem rotated_incidence_cycle_boundary
    {S : Set (Edge G)}
    {v : activeBaseNodeIndex S ⊕ activeBaseFiberSupportPointIndex S}
    {q : activeBaseNodeIndex S}
    (c : (baseFiberSupportIncidenceGraph S).Walk v v)
    (hc : c.IsCycle)
    (hq : (.inl q : activeBaseNodeIndex S ⊕ activeBaseFiberSupportPointIndex S) ∈
      c.support) :
    ∃ r : (baseFiberSupportIncidenceGraph S).Walk (.inl q) (.inl q),
      r.IsCycle ∧
      (∀ x : activeBaseNodeIndex S ⊕ activeBaseFiberSupportPointIndex S,
        x ∈ r.support ↔ x ∈ c.support) ∧
      ∃ pL pR : activeBaseFiberSupportPointIndex S,
      ∃ uL uR : activeBaseNodeIndex S,
        r.snd = .inr pL ∧
        r.getVert 2 = .inl uL ∧
        r.getVert (r.length - 2) = .inl uR ∧
        r.penultimate = .inr pR ∧
        (baseFiberSupportIncidenceGraph S).Adj (.inl q) (.inr pL) ∧
        (baseFiberSupportIncidenceGraph S).Adj (.inr pL) (.inl uL) ∧
        (baseFiberSupportIncidenceGraph S).Adj (.inl uR) (.inr pR) ∧
        (baseFiberSupportIncidenceGraph S).Adj (.inr pR) (.inl q) ∧
        pL ≠ pR ∧ uL ≠ q ∧ uR ≠ q := by
  classical
  let r := c.rotate (.inl q) hq
  have hr : r.IsCycle := hc.rotate hq
  have hlen : 3 ≤ r.length := hr.three_le_length
  have hsnd : (baseFiberSupportIncidenceGraph S).Adj (.inl q) r.snd :=
    r.adj_snd hr.not_nil
  have hpen : (baseFiberSupportIncidenceGraph S).Adj r.penultimate (.inl q) :=
    r.adj_penultimate hr.not_nil
  cases hs : r.snd with
  | inl q' =>
      rw [hs] at hsnd
      exact (not_baseFiberSupportIncidenceGraph_adj_inl_inl hsnd).elim
  | inr pL =>
      cases hp : r.penultimate with
      | inl q' =>
          rw [hp] at hpen
          exact (not_baseFiberSupportIncidenceGraph_adj_inl_inl hpen).elim
      | inr pR =>
          have hLadj : (baseFiberSupportIncidenceGraph S).Adj (.inr pL)
              (r.getVert 2) := by
            rw [← hs]
            exact r.adj_getVert_succ (i := 1) (by omega)
          have hRadj : (baseFiberSupportIncidenceGraph S).Adj
              (r.getVert (r.length - 2)) (.inr pR) := by
            rw [← hp]
            have hindex : r.length - 2 + 1 = r.length - 1 := by omega
            change (baseFiberSupportIncidenceGraph S).Adj
              (r.getVert (r.length - 2)) (r.getVert (r.length - 1))
            rw [← hindex]
            exact r.adj_getVert_succ (i := r.length - 2) (by omega)
          cases hL : r.getVert 2 with
          | inr p =>
              rw [hL] at hLadj
              exact (not_baseFiberSupportIncidenceGraph_adj_inr_inr hLadj).elim
          | inl uL =>
              cases hR : r.getVert (r.length - 2) with
              | inr p =>
                  rw [hR] at hRadj
                  exact (not_baseFiberSupportIncidenceGraph_adj_inr_inr hRadj).elim
              | inl uR =>
                  refine ⟨r, hr, ?_, pL, pR, uL, uR, hs, hL, hR, hp,
                    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                  · intro x
                    dsimp [r]
                    exact c.mem_support_rotate_iff (.inl q) hq
                  · simpa [hs] using! hsnd
                  · simpa [hL] using! hLadj
                  · simpa [hR] using! hRadj
                  · simpa [hp] using! hpen
                  · intro hpLR
                    apply hr.snd_ne_penultimate
                    calc
                      r.snd = .inr pL := hs
                      _ = .inr pR := congrArg Sum.inr hpLR
                      _ = r.penultimate := hp.symm
                  · intro huL
                    have hEq : r.getVert 2 = (.inl q :
                        activeBaseNodeIndex S ⊕ activeBaseFiberSupportPointIndex S) := by
                      calc
                        r.getVert 2 = .inl uL := hL
                        _ = .inl q := congrArg Sum.inl huL
                    have hEnds := (hr.getVert_endpoint_iff (i := 2) (by omega)).mp hEq
                    omega
                  · intro huR
                    have hEq : r.getVert (r.length - 2) = (.inl q :
                        activeBaseNodeIndex S ⊕ activeBaseFiberSupportPointIndex S) := by
                      calc
                        r.getVert (r.length - 2) = .inl uR := hR
                        _ = .inl q := congrArg Sum.inl huR
                    have hEnds :=
                      (hr.getVert_endpoint_iff (i := r.length - 2) (by omega)).mp hEq
                    omega

private theorem incidence_getVert_even_is_node
    {S : Set (Edge G)} {q : activeBaseNodeIndex S}
    (r : (baseFiberSupportIncidenceGraph S).Walk (.inl q) (.inl q)) :
    ∀ k : ℕ, 2 * k ≤ r.length →
      ∃ u : activeBaseNodeIndex S, r.getVert (2 * k) = .inl u := by
  intro k
  induction k with
  | zero =>
      intro _
      exact ⟨q, by simp⟩
  | succ k ih =>
      intro hk
      have hbound : 2 * k + 2 ≤ r.length := by
        convert! hk using 1
        all_goals omega
      rcases ih (by omega) with ⟨u, hu⟩
      have hmid : (baseFiberSupportIncidenceGraph S).Adj
          (.inl u) (r.getVert (2 * k + 1)) := by
        have hadj := r.adj_getVert_succ (i := 2 * k) (by omega)
        simpa [hu] using! hadj
      cases hm : r.getVert (2 * k + 1) with
      | inl w =>
          rw [hm] at hmid
          exact (not_baseFiberSupportIncidenceGraph_adj_inl_inl hmid).elim
      | inr p =>
          have hnext : (baseFiberSupportIncidenceGraph S).Adj
              (.inr p) (r.getVert (2 * (k + 1))) := by
            rw [← hm]
            have hsuc : 2 * k + 1 < r.length := by omega
            have hadj := r.adj_getVert_succ (i := 2 * k + 1) hsuc
            have hindex : 2 * k + 1 + 1 = 2 * (k + 1) := by omega
            rw [hindex] at hadj
            exact hadj
          cases hn : r.getVert (2 * (k + 1)) with
          | inl w => exact ⟨w, rfl⟩
          | inr p' =>
              rw [hn] at hnext
              exact (not_baseFiberSupportIncidenceGraph_adj_inr_inr hnext).elim

private theorem incidence_cycle_length_even
    {S : Set (Edge G)} {q : activeBaseNodeIndex S}
    (r : (baseFiberSupportIncidenceGraph S).Walk (.inl q) (.inl q)) :
    ∃ n : ℕ, r.length = 2 * n := by
  rcases Nat.even_or_odd' r.length with ⟨n, hn | hn⟩
  · exact ⟨n, hn⟩
  · have hle : 2 * n ≤ r.length := by omega
    rcases incidence_getVert_even_is_node r n hle with ⟨u, hu⟩
    have hadj := r.adj_getVert_succ (i := 2 * n) (by omega)
    have hend : r.getVert (2 * n + 1) = (.inl q :
        activeBaseNodeIndex S ⊕ activeBaseFiberSupportPointIndex S) := by
      rw [← hn]
      exact r.getVert_length
    rw [hu, hend] at hadj
    exact (not_baseFiberSupportIncidenceGraph_adj_inl_inl hadj).elim

private theorem incidence_cycle_node_ne_start
    {S : Set (Edge G)} {q : activeBaseNodeIndex S}
    (r : (baseFiberSupportIncidenceGraph S).Walk (.inl q) (.inl q))
    (hr : r.IsCycle) {i : ℕ} {u : activeBaseNodeIndex S}
    (hi : 0 < i) (hil : i < r.length)
    (hu : r.getVert i = .inl u) :
    q ≠ u := by
  intro hqu
  have hEq : r.getVert i = (.inl q :
      activeBaseNodeIndex S ⊕ activeBaseFiberSupportPointIndex S) := by
    calc
      r.getVert i = .inl u := hu
      _ = .inl q := congrArg Sum.inl hqu.symm
  have hEnds := (hr.getVert_endpoint_iff (i := i) (by omega)).mp hEq
  omega

/-- Propagate a fixed initial `ExtendsBy` branch along the fibre-side vertices
of an oriented incidence cycle. -/
private theorem extendsBy_along_incidence_cycle
    {S : Set (Edge G)} {q : activeBaseNodeIndex S}
    (r : (baseFiberSupportIncidenceGraph S).Walk (.inl q) (.inl q))
    (hr : r.IsCycle) {n : ℕ} (hlen : r.length = 2 * n)
    (hmin : ∀ u : activeBaseNodeIndex S,
      (.inl u : activeBaseNodeIndex S ⊕ activeBaseFiberSupportPointIndex S) ∈
        r.support → q.1.length ≤ u.1.length)
    {a : Alphabet G} {u1 : activeBaseNodeIndex S}
    (hu1 : r.getVert 2 = .inl u1)
    (hqu1 : q.1.ExtendsBy a u1.1) :
    ∀ k : ℕ, ∀ u : activeBaseNodeIndex S,
      1 ≤ k → k < n → r.getVert (2 * k) = .inl u → q.1.ExtendsBy a u.1 := by
  intro k
  induction k with
  | zero =>
      intro u hk
      omega
  | succ k ih =>
      intro u hk hkn hu
      cases k with
      | zero =>
          have htwo : 2 * Nat.succ 0 = 2 := by omega
          have hu' : r.getVert 2 = (.inl u :
              activeBaseNodeIndex S ⊕ activeBaseFiberSupportPointIndex S) := by
            rw [← htwo]
            exact hu
          have hEq : u = u1 := Sum.inl.inj (hu'.symm.trans hu1)
          subst u
          exact hqu1
      | succ k =>
          have hprev_le : 2 * Nat.succ k ≤ r.length := by
            rw [hlen]
            omega
          rcases incidence_getVert_even_is_node r (Nat.succ k) hprev_le with
            ⟨w, hw⟩
          have hprev : q.1.ExtendsBy a w.1 :=
            ih w (by omega) (by omega) hw
          have hmid_raw := r.adj_getVert_succ (i := 2 * Nat.succ k) (by
            rw [hlen]
            omega)
          cases hm : r.getVert (2 * Nat.succ k + 1) with
          | inl z =>
              rw [hw, hm] at hmid_raw
              exact (not_baseFiberSupportIncidenceGraph_adj_inl_inl hmid_raw).elim
          | inr p =>
              have hmid : (baseFiberSupportIncidenceGraph S).Adj (.inl w) (.inr p) := by
                simpa [hw, hm] using! hmid_raw
              have hnext_raw := r.adj_getVert_succ (i := 2 * Nat.succ k + 1) (by
                rw [hlen]
                omega)
              have hindex : 2 * Nat.succ k + 1 + 1 =
                  2 * Nat.succ (Nat.succ k) := by omega
              rw [hindex, hm, hu] at hnext_raw
              have hnext : (baseFiberSupportIncidenceGraph S).Adj (.inr p) (.inl u) :=
                hnext_raw
              apply Node.extendsBy_of_common_support_of_le hprev
              · apply hmin u
                rw [← hu]
                exact r.getVert_mem_support _
              · intro hqu
                have hne : q ≠ u := incidence_cycle_node_ne_start r hr
                  (i := 2 * Nat.succ (Nat.succ k)) (u := u)
                  (by omega) (by rw [hlen]; omega) hu
                exact hne (Subtype.ext hqu)
              · exact baseFiberSupportIncidenceGraph_adj_inl_inr_iff.mp hmid
              · exact baseFiberSupportIncidenceGraph_adj_inr_inl_iff.mp hnext

/-- In a finite linear selected family, the bipartite incidence graph of
active canonical base fibres and their supported points has no simple cycle. -/
theorem baseFiberSupportIncidenceGraph_isAcyclic_of_finite_linear
    {S : Set (Edge G)} (_hS : S.Finite)
    (hlinear : ((system G).edgeRestriction S).Linear) :
    (baseFiberSupportIncidenceGraph S).IsAcyclic := by
  classical
  intro v c hc
  rcases incidence_cycle_exists_node_support c hc with ⟨q0, hq0⟩
  let Q : Set (activeBaseNodeIndex S) :=
    {q | (.inl q : activeBaseNodeIndex S ⊕ activeBaseFiberSupportPointIndex S) ∈
      c.support}
  have hQ : Q.Nonempty := by
    refine ⟨q0, ?_⟩
    simpa only [Q, Set.mem_setOf_eq] using! hq0
  let q : activeBaseNodeIndex S :=
    Function.argminOn (fun q : activeBaseNodeIndex S => q.1.length) Q hQ
  have hq : (.inl q : activeBaseNodeIndex S ⊕ activeBaseFiberSupportPointIndex S) ∈
      c.support := by
    change q ∈ Q
    exact Function.argminOn_mem _ Q hQ
  have hmin : ∀ u : activeBaseNodeIndex S,
      (.inl u : activeBaseNodeIndex S ⊕ activeBaseFiberSupportPointIndex S) ∈
        c.support → q.1.length ≤ u.1.length := by
    intro u hu
    dsimp only [q]
    exact Function.argminOn_le
      (fun q : activeBaseNodeIndex S => q.1.length) Q hu
  rcases rotated_incidence_cycle_boundary c hc hq with
    ⟨r, hr, hrsupp, pL, pR, uL, uR, hs, hL, hR, hp,
      hqL, hpLuL, huRpR, hpRq, hpLR, huLq, huRq⟩
  have hminR : ∀ u : activeBaseNodeIndex S,
      (.inl u : activeBaseNodeIndex S ⊕ activeBaseFiberSupportPointIndex S) ∈
        r.support → q.1.length ≤ u.1.length := by
    intro u hu
    exact hmin u ((hrsupp _).mp hu)
  have hpLq : pL.1 ∈ (system G).edgeSupportSet (baseFiber S q.1) :=
    baseFiberSupportIncidenceGraph_adj_inl_inr_iff.mp hqL
  have hpLuL : pL.1 ∈ (system G).edgeSupportSet (baseFiber S uL.1) :=
    baseFiberSupportIncidenceGraph_adj_inr_inl_iff.mp hpLuL
  have huLmem : (.inl uL : activeBaseNodeIndex S ⊕ activeBaseFiberSupportPointIndex S) ∈
      r.support := by
    rw [← hL]
    exact r.getVert_mem_support 2
  have hqlt : q.1.length < uL.1.length := by
    rcases (hminR uL huLmem).eq_or_lt with hEq | hlt
    · exfalso
      apply huLq
      apply Subtype.ext
      exact (eq_of_common_support_of_length_eq hEq hpLq hpLuL).symm
    · exact hlt
  rcases exists_baseFiber_edge_of_common_support_of_lt hqlt hpLq hpLuL with
    ⟨eL, heL, hpL, hquL⟩
  rcases incidence_cycle_length_even r with ⟨n, hlen⟩
  have hn2 : 2 ≤ n := by
    have hthree := hr.three_le_length
    rw [hlen] at hthree
    omega
  have hbranch := extendsBy_along_incidence_cycle r hr hlen hminR hL hquL
  have hquR : q.1.ExtendsBy (baseLetter eL) uR.1 := by
    apply hbranch (n - 1) uR
    · omega
    · omega
    · have hindex : 2 * (n - 1) = r.length - 2 := by
        rw [hlen]
        omega
      calc
        r.getVert (2 * (n - 1)) = r.getVert (r.length - 2) := by
          rw [hindex]
        _ = .inl uR := hR
  have hpRq' : pR.1 ∈ (system G).edgeSupportSet (baseFiber S q.1) :=
    baseFiberSupportIncidenceGraph_adj_inr_inl_iff.mp hpRq
  have hpRuR : pR.1 ∈ (system G).edgeSupportSet (baseFiber S uR.1) :=
    baseFiberSupportIncidenceGraph_adj_inl_inr_iff.mp huRpR
  rcases exists_baseFiber_edge_of_common_support_of_lt hquR.choose hpRq' hpRuR with
    ⟨eR, heR, hpR, hquR'⟩
  have hletter : baseLetter eL = baseLetter eR :=
    Node.letter_eq_of_extendsBy_same_target hquR hquR'
  have heq : eL = eR :=
    baseLetter_injOn_baseFiber_of_linear q.1 hlinear heL heR hletter
  apply hpLR
  apply Subtype.ext
  calc
    pL.1 = baseApex eL := hpL
    _ = baseApex eR := congrArg baseApex heq
    _ = pR.1 := hpR.symm

end SequenceLift

end Erdos593
