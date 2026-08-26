import ErdosProblems.Erdos118.PentagramTriangles

/-! The finite five-clique contradiction for Larson's sharper graph. -/

namespace Erdos118.Pentagram

open Negative

/-- Three separated earlier cores force an impossible box in the fourth word. -/
theorem three_cores_contradiction {u v w d e : List TaggedCoord}
    (ud : Witness u d) (wd : Witness w d)
    (ue : Witness u e) (ve : Witness v e) (we : Witness w e)
    (de : Witness d e)
    (huv : ∃ r ∈ d, (∀ p ∈ Core u d, p.value < r.value) ∧
      (∀ q ∈ Core v d, r.value < q.value))
    (hvw : ∃ s ∈ d, (∀ q ∈ Core v d, q.value < s.value) ∧
      (∀ p ∈ Core w d, s.value < p.value))
    (hhigh : ud.highBoxes = wd.highBoxes) : False := by
  obtain ⟨r, hr, hur, hrv⟩ := huv
  obtain ⟨s, hs, hvs, hsw⟩ := hvw
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil ue.Y.p2 ue.Y.ne2
  obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil ve.Y.p2 ve.Y.ne2
  obtain ⟨z, hz⟩ := List.exists_mem_of_ne_nil we.Y.p2 we.Y.ne2
  obtain ⟨ul, hul, ur, hurCore, hulx, hxur⟩ := ue.mid_between_core_boxes hx
  obtain ⟨vl, hvl, vr, hvr, hvly, hyvr⟩ := ve.mid_between_core_boxes hy
  obtain ⟨wl, hwl, wr, hwr, hwlz, hzwr⟩ := we.mid_between_core_boxes hz
  have hxr := hxur.trans (hur ur (core_subset de hurCore))
  have hry := (hrv vl (core_subset de hvl)).trans hvly
  have hys := hyvr.trans (hvs vr (core_subset de hvr))
  have hsz := (hsw wl (core_subset de hwl)).trans hwlz
  obtain ⟨f, hf, hxf, hfz⟩ := de.alternating_box
    (ue.Y.mem2 hx) hr (ve.Y.mem2 hy) hs (we.Y.mem2 hz) hxr hry hys hsz
  rcases ud.box_right_parts hf with hlow | hhi
  · have hulD := core_subset de hul
    have hfx := (ud.low_before_inside hlow hulD.1.1 hulD.2).trans hulx
    exact hxf.not_gt hfx
  · have hfHigh : f ∈ wd.highBoxes := hhigh ▸ (show f ∈ ud.highBoxes from ⟨hhi, hf.2⟩)
    have hwrD := core_subset de hwr
    have hzf := hzwr.trans (wd.inside_before_high hwrD.1.1 hwrD.2 hfHigh.1)
    exact hfz.not_gt hzf

private theorem three_order_cases (a b c : ℕ)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (a < b ∧ b < c) ∨ (a < c ∧ c < b) ∨
    (b < a ∧ a < c) ∨ (b < c ∧ c < a) ∨
    (c < a ∧ a < b) ∨ (c < b ∧ b < a) := by
  omega

/-- No five words have forward witnesses for all their ordered pairs. -/
theorem no_oriented_five (v : Fin 5 → List TaggedCoord)
    (w : ∀ {i j : Fin 5}, i < j → Witness (v i) (v j)) : False := by
  let f (i : Fin 3) : Fin 5 := ⟨i.val, by omega⟩
  have hfd (i : Fin 3) : f i < (3 : Fin 5) := i.isLt
  have hfe (i : Fin 3) : f i < (4 : Fin 5) := (hfd i).trans (by decide)
  have hflt {i j : Fin 3} (h : i < j) : f i < f j := h
  let wd (i : Fin 3) := w (hfd i)
  let we (i : Fin 3) := w (hfe i)
  choose q hq using fun i : Fin 3 ↦ (wd i).core_nonempty
  have separated (i j : Fin 3) (hne : i ≠ j) :
      (∃ r ∈ v 3, (∀ p ∈ Core (v (f i)) (v 3), p.value < r.value) ∧
        (∀ p ∈ Core (v (f j)) (v 3), r.value < p.value)) ∨
      (∃ r ∈ v 3, (∀ p ∈ Core (v (f j)) (v 3), p.value < r.value) ∧
        (∀ p ∈ Core (v (f i)) (v 3), r.value < p.value)) := by
    rcases lt_or_gt_of_ne hne with hij | hji
    · exact (w (hflt hij)).core_separator (wd i) (wd j)
    · exact ((w (hflt hji)).core_separator (wd j) (wd i)).symm
  have qne (i j : Fin 3) (hne : i ≠ j) : (q i).value ≠ (q j).value := by
    rcases separated i j hne with ⟨r, _, hl, hr⟩ | ⟨r, _, hl, hr⟩
    · exact ((hl _ (hq i)).trans (hr _ (hq j))).ne
    · exact ((hl _ (hq j)).trans (hr _ (hq i))).ne'
  have between (i j : Fin 3) (hij : (q i).value < (q j).value) :
      ∃ r ∈ v 3, (∀ p ∈ Core (v (f i)) (v 3), p.value < r.value) ∧
        (∀ p ∈ Core (v (f j)) (v 3), r.value < p.value) := by
    have hne : i ≠ j := by intro h; subst j; exact (Nat.lt_irrefl _ hij)
    rcases separated i j hne with h | ⟨r, _, hl, hr⟩
    · exact h
    · exact (hij.not_gt ((hl _ (hq j)).trans (hr _ (hq i)))).elim
  have cuts (i j : Fin 3) : (wd i).highBoxes = (wd j).highBoxes := by
    rcases lt_trichotomy i j with hij | he | hji
    · exact ((w (hflt hij)).common_box_cuts (wd i) (wd j)).2
    · subst j; rfl
    · exact ((w (hflt hji)).common_box_cuts (wd j) (wd i)).2.symm
  have contradiction (i j k : Fin 3)
      (hij : (q i).value < (q j).value) (hjk : (q j).value < (q k).value) : False :=
    three_cores_contradiction (wd i) (wd k) (we i) (we j) (we k)
      (w (show (3 : Fin 5) < 4 by decide)) (between i j hij) (between j k hjk) (cuts i k)
  rcases three_order_cases (q 0).value (q 1).value (q 2).value
      (qne 0 1 (by decide)) (qne 0 2 (by decide)) (qne 1 2 (by decide)) with
    h | h | h | h | h | h
  · exact contradiction 0 1 2 h.1 h.2
  · exact contradiction 0 2 1 h.1 h.2
  · exact contradiction 1 0 2 h.1 h.2
  · exact contradiction 1 2 0 h.1 h.2
  · exact contradiction 2 0 1 h.1 h.2
  · exact contradiction 2 1 0 h.1 h.2

/-- The symmetrized eleven-segment graph has no five-vertex clique. -/
theorem graphOf_no_five_clique {V : Type*} (seq : V → List TaggedCoord) :
    ¬ ∃ S : Set V, (graphOf seq).IsClique S ∧ Cardinal.mk S = 5 := by
  rintro ⟨S, hclique, hcard⟩
  obtain ⟨e⟩ := Cardinal.mk_eq_nat_iff.mp hcard
  let : Fintype S := Fintype.ofEquiv (Fin 5) e.symm
  have hcardS : Fintype.card S = 5 := by simpa using Fintype.card_congr e
  have hkey_injective : Function.Injective (fun z : S ↦ firstValue (seq z.1)) := by
    intro x y hxy
    apply Subtype.ext
    by_contra hne
    have hadj := hclique x.2 y.2 hne
    rcases (graphOf_adj seq x.1 y.1).mp hadj with ⟨_, hdir⟩
    change Nonempty (Witness (seq x.1) (seq y.1)) ∨
      Nonempty (Witness (seq y.1) (seq x.1)) at hdir
    rcases hdir with hfwd | hrev
    · obtain ⟨wxy⟩ := hfwd
      exact (Nat.ne_of_lt wxy.firstValue_lt) hxy
    · obtain ⟨wyx⟩ := hrev
      exact (Nat.ne_of_gt wyx.firstValue_lt) hxy
  let : LinearOrder S :=
    LinearOrder.lift' (fun z : S ↦ firstValue (seq z.1)) hkey_injective
  let o : Fin 5 ≃o S := Fintype.orderIsoFinOfCardEq S hcardS
  let v : Fin 5 → List TaggedCoord := fun i ↦ seq (o i).1
  have hw : ∀ {i j : Fin 5}, i < j → Witness (v i) (v j) := by
    intro i j hij
    have hoij : o i < o j := o.lt_iff_lt.mpr hij
    have hkey : firstValue (seq (o i).1) < firstValue (seq (o j).1) := hoij
    have hvalne : (o i).1 ≠ (o j).1 := by
      intro h
      exact (Nat.ne_of_lt hkey) (congrArg (fun z ↦ firstValue (seq z)) h)
    have hadj := hclique (o i).2 (o j).2 hvalne
    rcases (graphOf_adj seq (o i).1 (o j).1).mp hadj with ⟨_, hdir⟩
    change Nonempty (Witness (v i) (v j)) ∨ Nonempty (Witness (v j) (v i)) at hdir
    have hforward : Nonempty (Witness (v i) (v j)) := by
      rcases hdir with hfwd | hrev
      · exact hfwd
      · obtain ⟨wji⟩ := hrev
        exact (Nat.not_lt_of_ge hkey.le wji.firstValue_lt).elim
    exact Classical.choice hforward
  exact no_oriented_five v hw

theorem graph_no_five :
    ¬ ∃ S : Set Negative.Exact.G, graph.IsClique S ∧ Cardinal.mk S = 5 :=
  graphOf_no_five_clique Negative.Exact.sequence

end Erdos118.Pentagram
