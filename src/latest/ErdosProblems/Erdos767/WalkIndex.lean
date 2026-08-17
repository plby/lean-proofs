import Mathlib

/-!
Small, division-free indexing lemmas for paths and cycles.  These are intended
for the path-rotation/lollipop part of the proof of Erdős 767.
-/

open Finset
open scoped SimpleGraph

namespace E767WalkIndex

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {a b : V}

/-! ### Index sets and elementary path indexing -/

/-- The natural-number indices of all vertices of a walk. -/
def vertexIndices (p : G.Walk a b) : Finset ℕ := Finset.range (p.length + 1)

/-- The indices on a path at which the indexed vertex is adjacent to `x`. -/
def neighborIndices (p : G.Walk a b) (x : V) : Finset ℕ :=
  (vertexIndices p).filter fun i ↦ G.Adj x (p.getVert i)

/-- The indices on a path at which the indexed vertex is in `S`. -/
def indicesIn (p : G.Walk a b) (S : Finset V) : Finset ℕ :=
  (vertexIndices p).filter fun i ↦ p.getVert i ∈ S

@[simp] theorem mem_vertexIndices {p : G.Walk a b} {i : ℕ} :
    i ∈ vertexIndices p ↔ i ≤ p.length := by
  simp [vertexIndices]

@[simp] theorem mem_neighborIndices {p : G.Walk a b} {x : V} {i : ℕ} :
    i ∈ neighborIndices p x ↔ i ≤ p.length ∧ G.Adj x (p.getVert i) := by
  simp [neighborIndices]

@[simp] theorem mem_indicesIn {p : G.Walk a b} {S : Finset V} {i : ℕ} :
    i ∈ indicesIn p S ↔ i ≤ p.length ∧ p.getVert i ∈ S := by
  simp [indicesIn]

theorem path_getVert_injOn_vertexIndices {p : G.Walk a b} (hp : p.IsPath) :
    Set.InjOn p.getVert (vertexIndices p : Set ℕ) := by
  intro i hi j hj hij
  exact hp.getVert_injOn (mem_vertexIndices.mp hi) (mem_vertexIndices.mp hj) hij

theorem path_getVert_eq_iff {p : G.Walk a b} (hp : p.IsPath)
    {i j : ℕ} (hi : i ≤ p.length) (hj : j ≤ p.length) :
    p.getVert i = p.getVert j ↔ i = j := by
  exact ⟨hp.getVert_injOn hi hj, congrArg p.getVert⟩

theorem path_mem_support_iff_exists_index {p : G.Walk a b} (hp : p.IsPath) {x : V} :
    x ∈ p.support ↔ ∃! i, i ≤ p.length ∧ p.getVert i = x := by
  constructor
  · intro hx
    obtain ⟨i, hix, hi⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hx
    refine ⟨i, ⟨hi, hix⟩, ?_⟩
    rintro j ⟨hj, hjx⟩
    exact hp.getVert_injOn hj hi (hjx.trans hix.symm)
  · rintro ⟨i, ⟨hi, hix⟩, -⟩
    exact SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr ⟨i, hix, hi⟩

theorem path_support_toFinset_eq_image_vertexIndices {p : G.Walk a b} (hp : p.IsPath) :
    p.support.toFinset = (vertexIndices p).image p.getVert := by
  ext x
  simp only [List.mem_toFinset, Finset.mem_image]
  constructor
  · intro hx
    obtain ⟨i, hix, hi⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hx
    exact ⟨i, mem_vertexIndices.mpr hi, hix⟩
  · rintro ⟨i, hi, rfl⟩
    exact p.getVert_mem_support i

theorem path_support_toFinset_card {p : G.Walk a b} (hp : p.IsPath) :
    p.support.toFinset.card = p.length + 1 := by
  rw [List.toFinset_card_of_nodup hp.support_nodup, p.length_support]

theorem path_idxOf_getVert {p : G.Walk a b} (hp : p.IsPath)
    {i : ℕ} (hi : i ≤ p.length) :
    p.support.idxOf (p.getVert i) = i := by
  let fi : Fin p.support.length :=
    ⟨i, p.length_support ▸ Nat.lt_add_one_of_le hi⟩
  have h := List.get_idxOf hp.support_nodup fi
  have hget : p.support.get fi = p.getVert i := by
    exact (p.getVert_eq_support_getElem hi).symm
  rw [hget] at h
  simpa [fi] using h

/-! ### Exact cardinal transport along a path -/

theorem image_indicesIn {p : G.Walk a b} (hp : p.IsPath) (S : Finset V) :
    (indicesIn p S).image p.getVert = p.support.toFinset ∩ S := by
  ext x
  simp only [Finset.mem_image, mem_indicesIn, Finset.mem_inter,
    List.mem_toFinset]
  constructor
  · rintro ⟨i, ⟨hi, hiS⟩, rfl⟩
    exact ⟨p.getVert_mem_support i, hiS⟩
  · rintro ⟨hxp, hxS⟩
    obtain ⟨i, hix, hi⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hxp
    exact ⟨i, ⟨hi, hix ▸ hxS⟩, hix⟩

theorem card_indicesIn {p : G.Walk a b} (hp : p.IsPath) (S : Finset V) :
    (indicesIn p S).card = (p.support.toFinset ∩ S).card := by
  rw [← image_indicesIn hp S, Finset.card_image_iff.mpr]
  exact hp.getVert_injOn.mono fun i hi ↦ (mem_indicesIn.mp hi).1

theorem image_neighborIndices {p : G.Walk a b} (hp : p.IsPath) (x : V) :
    (neighborIndices p x).image p.getVert =
      G.neighborFinset x ∩ p.support.toFinset := by
  ext y
  simp only [Finset.mem_image, mem_neighborIndices, Finset.mem_inter,
    G.mem_neighborFinset, List.mem_toFinset]
  constructor
  · rintro ⟨i, ⟨hi, hxy⟩, rfl⟩
    exact ⟨hxy, p.getVert_mem_support i⟩
  · rintro ⟨hxy, hyp⟩
    obtain ⟨i, hiy, hi⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hyp
    exact ⟨i, ⟨hi, hiy ▸ hxy⟩, hiy⟩

theorem card_neighborIndices {p : G.Walk a b} (hp : p.IsPath) (x : V) :
    (neighborIndices p x).card =
      (G.neighborFinset x ∩ p.support.toFinset).card := by
  rw [← image_neighborIndices hp x, Finset.card_image_iff.mpr]
  exact hp.getVert_injOn.mono fun i hi ↦ (mem_neighborIndices.mp hi).1

theorem card_neighborIndices_eq_degree {p : G.Walk a b} (hp : p.IsPath) (x : V)
    (hN : G.neighborFinset x ⊆ p.support.toFinset) :
    (neighborIndices p x).card = G.degree x := by
  rw [card_neighborIndices hp x, Finset.inter_eq_left.mpr hN,
    G.card_neighborFinset_eq_degree]

/-! ### The terminal-neighbour index set -/

/-- The positions on `p` adjacent to its terminal endpoint. -/
def endNeighborIndices (p : G.Walk a b) : Finset ℕ := neighborIndices p b

@[simp] theorem mem_endNeighborIndices {p : G.Walk a b} {i : ℕ} :
    i ∈ endNeighborIndices p ↔ i ≤ p.length ∧ G.Adj b (p.getVert i) := by
  simp [endNeighborIndices]

theorem mem_endNeighborIndices_iff_lt {p : G.Walk a b} (hp : p.IsPath) {i : ℕ} :
    i ∈ endNeighborIndices p ↔ i < p.length ∧ G.Adj b (p.getVert i) := by
  rw [mem_endNeighborIndices]
  constructor
  · rintro ⟨hi, hadj⟩
    exact ⟨by
      rcases hi.eq_or_lt with rfl | hlt
      · simpa using hadj
      · exact hlt, hadj⟩
  · rintro ⟨hi, hadj⟩
    exact ⟨hi.le, hadj⟩

theorem endNeighborIndices_eq_filter_range {p : G.Walk a b} (hp : p.IsPath) :
    endNeighborIndices p =
      (Finset.range p.length).filter fun i ↦ G.Adj b (p.getVert i) := by
  ext i
  simp [mem_endNeighborIndices_iff_lt hp]

theorem card_endNeighborIndices {p : G.Walk a b} (hp : p.IsPath) :
    (endNeighborIndices p).card =
      (G.neighborFinset b ∩ p.support.toFinset).card := by
  exact card_neighborIndices hp b

theorem card_endNeighborIndices_eq_degree {p : G.Walk a b} (hp : p.IsPath)
    (hN : G.neighborFinset b ⊆ p.support.toFinset) :
    (endNeighborIndices p).card = G.degree b := by
  exact card_neighborIndices_eq_degree hp b hN

/-! ### `take`, `drop`, `takeUntil`, and `dropUntil` carriers -/

theorem take_support_toFinset_card {p : G.Walk a b} (hp : p.IsPath) (i : ℕ) :
    (p.take i).support.toFinset.card = min i p.length + 1 := by
  simpa using path_support_toFinset_card (hp.take i)

theorem drop_support_toFinset_card {p : G.Walk a b} (hp : p.IsPath) (i : ℕ) :
    (p.drop i).support.toFinset.card = p.length - i + 1 := by
  simpa using path_support_toFinset_card (hp.drop i)

theorem getVert_mem_take_support_iff {p : G.Walk a b} (hp : p.IsPath)
    {i j : ℕ} (hj : j ≤ p.length) :
    p.getVert j ∈ (p.take i).support ↔ j ≤ min i p.length := by
  constructor
  · intro hjmem
    obtain ⟨k, hkvert, hk⟩ :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hjmem
    rw [SimpleGraph.Walk.take_length] at hk
    have hki : k ≤ i := hk.trans (min_le_left _ _)
    have hkp : k ≤ p.length := hk.trans (min_le_right _ _)
    have hget : p.getVert k = p.getVert j := by
      simpa [SimpleGraph.Walk.take_getVert, min_eq_right hki] using hkvert
    have : k = j := hp.getVert_injOn hkp hj hget
    omega
  · intro hjmin
    apply SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr
    refine ⟨j, ?_, ?_⟩
    · simp [SimpleGraph.Walk.take_getVert, min_eq_right (hjmin.trans (min_le_left _ _))]
    · simpa using hjmin

theorem getVert_mem_drop_support_iff {p : G.Walk a b} (hp : p.IsPath)
    {i j : ℕ} (hi : i ≤ p.length) (hj : j ≤ p.length) :
    p.getVert j ∈ (p.drop i).support ↔ i ≤ j := by
  constructor
  · intro hjmem
    obtain ⟨k, hkvert, hk⟩ :=
      SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hjmem
    rw [SimpleGraph.Walk.drop_length] at hk
    have hik : i + k ≤ p.length := by omega
    have hget : p.getVert (i + k) = p.getVert j := by
      simpa [SimpleGraph.Walk.drop_getVert] using hkvert
    have : i + k = j := hp.getVert_injOn hik hj hget
    omega
  · intro hij
    apply SimpleGraph.Walk.mem_support_iff_exists_getVert.mpr
    refine ⟨j - i, ?_, ?_⟩
    · simp [SimpleGraph.Walk.drop_getVert, Nat.add_sub_of_le hij]
    · rw [SimpleGraph.Walk.drop_length]
      omega

theorem takeUntil_getVert_support_card {p : G.Walk a b} (hp : p.IsPath)
    {i : ℕ} (hi : i ≤ p.length) :
    (p.takeUntil (p.getVert i) (p.getVert_mem_support i)).support.toFinset.card = i + 1 := by
  rw [path_support_toFinset_card (hp.takeUntil _),
    SimpleGraph.Walk.length_takeUntil, path_idxOf_getVert hp hi]

theorem dropUntil_getVert_support_card {p : G.Walk a b} (hp : p.IsPath)
    {i : ℕ} (hi : i ≤ p.length) :
    (p.dropUntil (p.getVert i) (p.getVert_mem_support i)).support.toFinset.card =
      p.length - i + 1 := by
  rw [path_support_toFinset_card (hp.dropUntil _),
    SimpleGraph.Walk.length_dropUntil, path_idxOf_getVert hp hi]

/-! ### Cycles indexed without repeating their initial vertex -/

/-- The indices `0, ..., c.length - 1` of the distinct vertices of a cycle. -/
def cycleIndices {v : V} (c : G.Walk v v) : Finset ℕ := Finset.range c.length

/-- The vertex carrier of a cycle, with the repeated terminal vertex removed. -/
def cycleVertexFinset {v : V} (c : G.Walk v v) : Finset V :=
  c.support.dropLast.toFinset

@[simp] theorem mem_cycleIndices {v : V} {c : G.Walk v v} {i : ℕ} :
    i ∈ cycleIndices c ↔ i < c.length := by
  simp [cycleIndices]

theorem cycle_getVert_injOn_cycleIndices {v : V} {c : G.Walk v v}
    (hc : c.IsCycle) :
    Set.InjOn c.getVert (cycleIndices c : Set ℕ) := by
  intro i hi j hj hij
  apply hc.getVert_injOn' (show i ≤ c.length - 1 by
      have := mem_cycleIndices.mp hi
      omega)
    (show j ≤ c.length - 1 by
      have := mem_cycleIndices.mp hj
      omega)
  exact hij

theorem cycle_support_dropLast_card {v : V} {c : G.Walk v v} (hc : c.IsCycle) :
    (cycleVertexFinset c).card = c.length := by
  rw [cycleVertexFinset, List.toFinset_card_of_nodup hc.nodup_dropLast_support,
    List.length_dropLast, c.length_support]
  omega

theorem cycle_support_toFinset_eq_cycleVertexFinset {v : V} {c : G.Walk v v}
    (hc : c.IsCycle) :
    c.support.toFinset = cycleVertexFinset c := by
  apply Finset.Subset.antisymm
  · intro x hx
    have hdecomp : c.support.dropLast ++ [v] = c.support := by
      simpa [c.getLast_support] using List.dropLast_append_getLast c.support_ne_nil
    rw [← hdecomp, List.mem_toFinset] at hx
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | hx
    · exact List.mem_toFinset.mpr hx
    · subst x
      exact List.mem_toFinset.mpr (by
        apply (List.mem_dropLast_iff_idxOf_lt c.start_mem_support).mpr
        have hidx : c.support.idxOf v = 0 :=
          (List.idxOf_eq_zero_iff_head_eq c.support_ne_nil).mpr c.head_support
        rw [hidx, c.length_support]
        have := hc.three_le_length
        omega)
  · exact fun x hx ↦ List.mem_toFinset.mpr
      (List.mem_of_mem_dropLast (List.mem_toFinset.mp hx))

theorem cycleVertexFinset_eq_image_cycleIndices {v : V} {c : G.Walk v v}
    (hc : c.IsCycle) :
    cycleVertexFinset c = (cycleIndices c).image c.getVert := by
  ext x
  simp only [cycleVertexFinset, List.mem_toFinset, Finset.mem_image]
  constructor
  · intro hx
    have hxfull : x ∈ c.support := List.mem_of_mem_dropLast hx
    let i := c.support.idxOf x
    have hi : i < c.length := by
      have := List.mem_dropLast_iff_idxOf_lt hxfull
      rw [this] at hx
      simpa [i, c.length_support] using hx
    refine ⟨i, mem_cycleIndices.mpr hi, ?_⟩
    exact c.getVert_support_idxOf hxfull
  · rintro ⟨i, hi, rfl⟩
    have hil : i < c.length := mem_cycleIndices.mp hi
    have himem : c.getVert i ∈ c.support := c.getVert_mem_support i
    apply (List.mem_dropLast_iff_idxOf_lt himem).mpr
    have hidx : c.support.idxOf (c.getVert i) = i := by
      let fi : Fin c.support.dropLast.length :=
        ⟨i, by simpa [c.length_support] using hil⟩
      have h := List.get_idxOf hc.nodup_dropLast_support fi
      have hget : c.support.dropLast.get fi = c.getVert i := by
        rw [c.getVert_eq_support_getElem hil.le]
        exact List.getElem_dropLast fi.isLt
      rw [hget] at h
      have himemdrop : c.getVert i ∈ c.support.dropLast := by
        rw [← hget]
        exact List.getElem_mem _
      have hprefix : c.support.dropLast <+: c.support := by
        exact ⟨[v], c.dropLast_support_concat⟩
      calc
        c.support.idxOf (c.getVert i) =
            c.support.dropLast.idxOf (c.getVert i) :=
          (hprefix.idxOf_eq_of_mem himemdrop).symm
        _ = i := by simpa [fi] using h
    rw [hidx, c.length_support]
    omega

end E767WalkIndex

