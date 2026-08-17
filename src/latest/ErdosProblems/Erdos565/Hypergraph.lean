/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Real.Basic

/-!
# Elementary finite hypergraphs

This file supplies the set-system language used in the proof of the exponential
upper bound for induced Ramsey numbers.  A hypergraph is a `Finset` of `Finset`s;
in particular, parallel edges are deliberately excluded.  The definitions here
are finite and computable.  No choice of an ambient vertex set is stored: when a
finite universe is needed, it is supplied by a `Fintype` instance.
-/

open scoped BigOperators

@[expose] public section

namespace Erdos565

/-- A finite simple hypergraph on `V`. -/
abbrev Hypergraph (V : Type*) := Finset (Finset V)

namespace Hypergraph

variable {V W U : Type*}

section Basic

variable [DecidableEq V]

/-- The hypergraph obtained by retaining only edges contained in `X`. -/
def restrict (H : Hypergraph V) (X : Finset V) : Hypergraph V :=
  H.filter fun e => e ⊆ X

@[simp] theorem mem_restrict {H : Hypergraph V} {X e : Finset V} :
    e ∈ H.restrict X ↔ e ∈ H ∧ e ⊆ X := by
  simp [restrict]

theorem restrict_subset (H : Hypergraph V) (X : Finset V) : H.restrict X ⊆ H := by
  intro e he
  exact (mem_restrict.mp he).1

theorem restrict_mono_right (H : Hypergraph V) {X Y : Finset V} (hXY : X ⊆ Y) :
    H.restrict X ⊆ H.restrict Y := by
  intro e he
  exact mem_restrict.mpr ⟨(mem_restrict.mp he).1, (mem_restrict.mp he).2.trans hXY⟩

theorem restrict_mono_left {H K : Hypergraph V} (hHK : H ⊆ K) (X : Finset V) :
    H.restrict X ⊆ K.restrict X := by
  intro e he
  exact mem_restrict.mpr ⟨hHK (mem_restrict.mp he).1, (mem_restrict.mp he).2⟩

@[simp] theorem restrict_empty (H : Hypergraph V) :
    H.restrict ∅ = H.filter (fun e => e = ∅) := by
  ext e
  simp [Finset.subset_empty]

@[simp] theorem restrict_univ [Fintype V] (H : Hypergraph V) :
    H.restrict Finset.univ = H := by
  ext e
  simp

@[simp] theorem restrict_restrict (H : Hypergraph V) (X Y : Finset V) :
    (H.restrict X).restrict Y = H.restrict (X ∩ Y) := by
  ext e
  simp only [mem_restrict]
  constructor
  · rintro ⟨⟨he, heX⟩, heY⟩
    exact ⟨he, Finset.subset_inter heX heY⟩
  · rintro ⟨he, heXY⟩
    exact ⟨⟨he, heXY.trans Finset.inter_subset_left⟩,
      heXY.trans Finset.inter_subset_right⟩

/-- The traces `e ∩ X` of all edges on `X`. -/
def trace (H : Hypergraph V) (X : Finset V) : Hypergraph V :=
  H.image fun e => e ∩ X

@[simp] theorem mem_trace {H : Hypergraph V} {X t : Finset V} :
    t ∈ H.trace X ↔ ∃ e ∈ H, e ∩ X = t := by
  simp [trace]

theorem trace_edge_subset {H : Hypergraph V} {X t : Finset V} (ht : t ∈ H.trace X) :
    t ⊆ X := by
  obtain ⟨e, he, rfl⟩ := mem_trace.mp ht
  exact Finset.inter_subset_right

@[simp] theorem trace_empty (H : Hypergraph V) : H.trace ∅ = {∅} ↔ H.Nonempty := by
  constructor
  · intro h
    by_contra hH
    have : H = ∅ := Finset.not_nonempty_iff_eq_empty.mp hH
    simp [this, trace] at h
  · intro hH
    ext e
    simp only [mem_trace, Finset.inter_empty, exists_eq_right, Finset.mem_singleton]
    constructor
    · rintro ⟨_, _, rfl⟩
      rfl
    · rintro rfl
      obtain ⟨e, he⟩ := hH
      exact ⟨e, he, rfl⟩

/-- Delete all vertices of `X` from every edge. -/
def deleteVertices (H : Hypergraph V) (X : Finset V) : Hypergraph V :=
  H.image fun e => e \ X

@[simp] theorem mem_deleteVertices {H : Hypergraph V} {X t : Finset V} :
    t ∈ H.deleteVertices X ↔ ∃ e ∈ H, e \ X = t := by
  simp [deleteVertices]

/-- The `k`-uniform layer of a hypergraph. -/
def layer (H : Hypergraph V) (k : ℕ) : Hypergraph V :=
  H.filter fun e => e.card = k

@[simp] theorem mem_layer {H : Hypergraph V} {k : ℕ} {e : Finset V} :
    e ∈ H.layer k ↔ e ∈ H ∧ e.card = k := by
  simp [layer]

theorem layer_subset (H : Hypergraph V) (k : ℕ) : H.layer k ⊆ H := by
  intro e he
  exact (mem_layer.mp he).1

/-- Every edge has exactly `k` vertices. -/
def IsUniform (H : Hypergraph V) (k : ℕ) : Prop :=
  ∀ e ∈ H, e.card = k

theorem isUniform_iff_layer_eq (H : Hypergraph V) (k : ℕ) :
    H.IsUniform k ↔ H.layer k = H := by
  constructor
  · intro h
    apply Finset.Subset.antisymm (layer_subset H k)
    intro e he
    exact mem_layer.mpr ⟨he, h e he⟩
  · intro h e he
    have : e ∈ H.layer k := h.symm ▸ he
    exact (mem_layer.mp this).2

theorem IsUniform.card_eq {H : Hypergraph V} {k : ℕ} (hH : H.IsUniform k)
    {e : Finset V} (he : e ∈ H) : e.card = k :=
  hH e he

theorem IsUniform.subset_card_eq {H : Hypergraph V} {k : ℕ} (hH : H.IsUniform k)
    {e f : Finset V} (he : e ∈ H) (hf : f ∈ H) (hef : e ⊆ f) : e = f := by
  exact Finset.eq_of_subset_of_card_le hef (by simp [hH e he, hH f hf])

/-- Every edge has at most `k` vertices. -/
def IsBounded (H : Hypergraph V) (k : ℕ) : Prop :=
  ∀ e ∈ H, e.card ≤ k

theorem IsUniform.isBounded {H : Hypergraph V} {k : ℕ} (hH : H.IsUniform k) :
    H.IsBounded k := by
  intro e he
  exact (hH e he).le

/-- The set of vertices occurring in at least one edge. -/
def vertices (H : Hypergraph V) : Finset V :=
  H.biUnion id

@[simp] theorem mem_vertices {H : Hypergraph V} {v : V} :
    v ∈ H.vertices ↔ ∃ e ∈ H, v ∈ e := by
  simp [vertices]

theorem edge_subset_vertices {H : Hypergraph V} {e : Finset V} (he : e ∈ H) :
    e ⊆ H.vertices := by
  intro v hv
  exact mem_vertices.mpr ⟨e, he, hv⟩

theorem vertices_mono {H K : Hypergraph V} (hHK : H ⊆ K) : H.vertices ⊆ K.vertices := by
  intro v hv
  obtain ⟨e, he, hve⟩ := mem_vertices.mp hv
  exact mem_vertices.mpr ⟨e, hHK he, hve⟩

@[simp] theorem vertices_empty : (Hypergraph.vertices (∅ : Hypergraph V)) = ∅ := by
  ext v
  simp

/-- Number of edges containing `S`. -/
def degree (H : Hypergraph V) (S : Finset V) : ℕ :=
  (H.filter fun e => S ⊆ e).card

@[simp] theorem degree_empty (H : Hypergraph V) : H.degree ∅ = H.card := by
  simp [degree]

theorem degree_mono_left {H K : Hypergraph V} (hHK : H ⊆ K) (S : Finset V) :
    H.degree S ≤ K.degree S := by
  apply Finset.card_le_card
  intro e he
  obtain ⟨heH, hSe⟩ := Finset.mem_filter.mp he
  exact Finset.mem_filter.mpr ⟨hHK heH, hSe⟩

theorem degree_anti_right (H : Hypergraph V) {S T : Finset V} (hST : S ⊆ T) :
    H.degree T ≤ H.degree S := by
  apply Finset.card_le_card
  intro e he
  obtain ⟨heH, hTe⟩ := Finset.mem_filter.mp he
  exact Finset.mem_filter.mpr ⟨heH, hST.trans hTe⟩

theorem degree_le_card (H : Hypergraph V) (S : Finset V) : H.degree S ≤ H.card := by
  exact Finset.card_filter_le _ _

end Basic

section Links

variable [DecidableEq V]

/-- The (non-strict) link at `S`: remove `S` from every edge containing it. -/
def link (H : Hypergraph V) (S : Finset V) : Hypergraph V :=
  (H.filter fun e => S ⊆ e).image fun e => e \ S

@[simp] theorem mem_link {H : Hypergraph V} {S t : Finset V} :
    t ∈ H.link S ↔ ∃ e ∈ H, S ⊆ e ∧ e \ S = t := by
  simp [link, and_assoc]

/-- The strict link omits the empty remainder, equivalently edges equal to `S`. -/
def strictLink (H : Hypergraph V) (S : Finset V) : Hypergraph V :=
  (H.link S).erase ∅

@[simp] theorem mem_strictLink {H : Hypergraph V} {S t : Finset V} :
    t ∈ H.strictLink S ↔ t ≠ ∅ ∧ ∃ e ∈ H, S ⊆ e ∧ e \ S = t := by
  simp [strictLink, and_left_comm, and_assoc]

theorem strictLink_subset_link (H : Hypergraph V) (S : Finset V) :
    H.strictLink S ⊆ H.link S := by
  exact Finset.erase_subset _ _

@[simp] theorem link_empty (H : Hypergraph V) : H.link ∅ = H := by
  ext t
  simp

theorem link_mono_left {H K : Hypergraph V} (hHK : H ⊆ K) (S : Finset V) :
    H.link S ⊆ K.link S := by
  intro t ht
  obtain ⟨e, he, hSe, rfl⟩ := mem_link.mp ht
  exact mem_link.mpr ⟨e, hHK he, hSe, rfl⟩

theorem strictLink_mono_left {H K : Hypergraph V} (hHK : H ⊆ K) (S : Finset V) :
    H.strictLink S ⊆ K.strictLink S := by
  intro t ht
  rw [mem_strictLink] at ht ⊢
  obtain ⟨e, he, hSe, het⟩ := ht.2
  exact ⟨ht.1, e, hHK he, hSe, het⟩

theorem link_edge_disjoint {H : Hypergraph V} {S t : Finset V} (ht : t ∈ H.link S) :
    Disjoint t S := by
  obtain ⟨e, he, hSe, rfl⟩ := mem_link.mp ht
  exact Finset.disjoint_sdiff.symm

theorem link_card_le_degree (H : Hypergraph V) (S : Finset V) :
    (H.link S).card ≤ H.degree S := by
  exact Finset.card_image_le

theorem mem_link_iff_union_mem_of_disjoint {H : Hypergraph V} {S t : Finset V}
    (hdis : Disjoint t S) : t ∈ H.link S ↔ S ∪ t ∈ H := by
  constructor
  · intro ht
    obtain ⟨e, he, hSe, het⟩ := mem_link.mp ht
    have hdecomp : S ∪ (e \ S) = e := Finset.union_sdiff_of_subset hSe
    have heq : S ∪ t = e := by simpa [het] using hdecomp
    rwa [heq]
  · intro h
    refine mem_link.mpr ⟨S ∪ t, h, Finset.subset_union_left, ?_⟩
    rw [Finset.union_sdiff_left]
    exact Finset.sdiff_eq_self_of_disjoint hdis

end Links

section Closures

variable [Fintype V] [DecidableEq V]

/-- All vertex sets which contain an edge of `H`. -/
def upClosure (H : Hypergraph V) : Hypergraph V :=
  Finset.univ.powerset.filter fun S => ∃ e ∈ H, e ⊆ S

@[simp] theorem mem_upClosure {H : Hypergraph V} {S : Finset V} :
    S ∈ H.upClosure ↔ ∃ e ∈ H, e ⊆ S := by
  simp [upClosure]

/-- All vertex sets which strictly contain an edge of `H`. -/
def strictUpClosure (H : Hypergraph V) : Hypergraph V :=
  Finset.univ.powerset.filter fun S => ∃ e ∈ H, e ⊂ S

@[simp] theorem mem_strictUpClosure {H : Hypergraph V} {S : Finset V} :
    S ∈ H.strictUpClosure ↔ ∃ e ∈ H, e ⊂ S := by
  simp [strictUpClosure]

theorem subset_upClosure (H : Hypergraph V) : H ⊆ H.upClosure := by
  intro e he
  exact mem_upClosure.mpr ⟨e, he, Finset.Subset.rfl⟩

theorem strictUpClosure_subset_upClosure (H : Hypergraph V) :
    H.strictUpClosure ⊆ H.upClosure := by
  intro S hS
  obtain ⟨e, he, hes⟩ := mem_strictUpClosure.mp hS
  exact mem_upClosure.mpr ⟨e, he, hes.1⟩

theorem upClosure_mono {H K : Hypergraph V} (hHK : H ⊆ K) :
    H.upClosure ⊆ K.upClosure := by
  intro S hS
  obtain ⟨e, he, heS⟩ := mem_upClosure.mp hS
  exact mem_upClosure.mpr ⟨e, hHK he, heS⟩

theorem upClosure_upward {H : Hypergraph V} {S T : Finset V}
    (hS : S ∈ H.upClosure) (hST : S ⊆ T) : T ∈ H.upClosure := by
  obtain ⟨e, he, heS⟩ := mem_upClosure.mp hS
  exact mem_upClosure.mpr ⟨e, he, heS.trans hST⟩

@[simp] theorem upClosure_upClosure (H : Hypergraph V) :
    H.upClosure.upClosure = H.upClosure := by
  apply Finset.Subset.antisymm
  · intro S hS
    obtain ⟨T, hT, hTS⟩ := mem_upClosure.mp hS
    exact upClosure_upward hT hTS
  · exact subset_upClosure H.upClosure

@[simp] theorem upClosure_empty : (∅ : Hypergraph V).upClosure = ∅ := by
  ext S
  simp

end Closures

section CoverAndIndependence

variable [DecidableEq V]

/-- `C` covers `H` if every edge of `H` contains some member of `C`. -/
def Covers (C H : Hypergraph V) : Prop :=
  ∀ e ∈ H, ∃ c ∈ C, c ⊆ e

theorem covers_iff_subset_upClosure [Fintype V] {C H : Hypergraph V} :
    C.Covers H ↔ H ⊆ C.upClosure := by
  constructor
  · intro h e he
    exact mem_upClosure.mpr (h e he)
  · intro h e he
    exact mem_upClosure.mp (h he)

theorem Covers.refl (H : Hypergraph V) : H.Covers H := by
  intro e he
  exact ⟨e, he, Finset.Subset.rfl⟩

theorem Covers.trans {A B C : Hypergraph V} (hAB : A.Covers B) (hBC : B.Covers C) :
    A.Covers C := by
  intro e he
  obtain ⟨b, hb, hbe⟩ := hBC e he
  obtain ⟨a, ha, hab⟩ := hAB b hb
  exact ⟨a, ha, hab.trans hbe⟩

theorem Covers.mono_left {C D H : Hypergraph V} (hCD : C ⊆ D) (h : C.Covers H) :
    D.Covers H := by
  intro e he
  obtain ⟨c, hc, hce⟩ := h e he
  exact ⟨c, hCD hc, hce⟩

theorem Covers.mono_right {C H K : Hypergraph V} (hHK : H ⊆ K) (h : C.Covers K) :
    C.Covers H := by
  intro e he
  exact h e (hHK he)

/-- A set is independent when it contains no edge. -/
def IsIndependent (H : Hypergraph V) (A : Finset V) : Prop :=
  ∀ e ∈ H, ¬ e ⊆ A

theorem not_isIndependent_iff {H : Hypergraph V} {A : Finset V} :
    ¬ H.IsIndependent A ↔ ∃ e ∈ H, e ⊆ A := by
  simp [IsIndependent]

theorem isIndependent_iff_not_mem_upClosure [Fintype V]
    {H : Hypergraph V} {A : Finset V} :
    H.IsIndependent A ↔ A ∉ H.upClosure := by
  simp [IsIndependent]

theorem IsIndependent.mono {H : Hypergraph V} {A B : Finset V}
    (hA : H.IsIndependent A) (hBA : B ⊆ A) : H.IsIndependent B := by
  intro e he heB
  exact hA e he (heB.trans hBA)

theorem IsIndependent.anti_hypergraph {H K : Hypergraph V} {A : Finset V}
    (hK : K.IsIndependent A) (hHK : H ⊆ K) : H.IsIndependent A := by
  intro e he
  exact hK e (hHK he)

theorem Covers.independent_of {C H : Hypergraph V} (hCH : C.Covers H)
    {A : Finset V} (hA : C.IsIndependent A) : H.IsIndependent A := by
  intro e he heA
  obtain ⟨c, hc, hce⟩ := hCH e he
  exact hA c hc (hce.trans heA)

end CoverAndIndependence

section Maps

variable [DecidableEq V] [DecidableEq W] [DecidableEq U]

/-- Push every edge forward along a map. -/
def map (f : V → W) (H : Hypergraph V) : Hypergraph W :=
  H.image fun e => e.image f

@[simp] theorem mem_map {f : V → W} {H : Hypergraph V} {t : Finset W} :
    t ∈ H.map f ↔ ∃ e ∈ H, e.image f = t := by
  simp [map]

theorem map_mono {f : V → W} {H K : Hypergraph V} (hHK : H ⊆ K) :
    H.map f ⊆ K.map f := by
  intro t ht
  obtain ⟨e, he, rfl⟩ := mem_map.mp ht
  exact mem_map.mpr ⟨e, hHK he, rfl⟩

@[simp] theorem map_id (H : Hypergraph V) : H.map id = H := by
  ext e
  simp

theorem map_comp (g : W → U) (f : V → W) (H : Hypergraph V) :
    (H.map f).map g = H.map (g ∘ f) := by
  ext t
  simp only [mem_map]
  constructor
  · rintro ⟨s, ⟨e, he, rfl⟩, rfl⟩
    exact ⟨e, he, by rw [Finset.image_image]⟩
  · rintro ⟨e, he, rfl⟩
    exact ⟨e.image f, ⟨e, he, rfl⟩, by rw [Finset.image_image]⟩

theorem card_map_le (f : V → W) (H : Hypergraph V) :
    (H.map f).card ≤ H.card := by
  exact Finset.card_image_le

theorem edge_card_map_le {f : V → W} {H : Hypergraph V} {t : Finset W}
    (ht : t ∈ H.map f) : ∃ e ∈ H, t.card ≤ e.card := by
  obtain ⟨e, he, rfl⟩ := mem_map.mp ht
  exact ⟨e, he, Finset.card_image_le⟩

theorem edge_card_map_eq_of_injective {f : V → W} (hf : Function.Injective f)
    {H : Hypergraph V} {t : Finset W} (ht : t ∈ H.map f) :
    ∃ e ∈ H, t.card = e.card := by
  obtain ⟨e, he, rfl⟩ := mem_map.mp ht
  exact ⟨e, he, Finset.card_image_of_injective e hf⟩

/-- Pull a hypergraph back along `f`, considering every subset of the finite domain. -/
def comap [Fintype V] (f : V → W) (K : Hypergraph W) : Hypergraph V :=
  Finset.univ.powerset.filter fun e => e.image f ∈ K

@[simp] theorem mem_comap [Fintype V] {f : V → W} {K : Hypergraph W}
    {e : Finset V} : e ∈ K.comap f ↔ e.image f ∈ K := by
  simp [comap]

theorem map_comap_subset [Fintype V] (f : V → W) (K : Hypergraph W) :
    (K.comap f).map f ⊆ K := by
  intro t ht
  obtain ⟨e, he, rfl⟩ := mem_map.mp ht
  exact mem_comap.mp he

theorem subset_comap_map [Fintype V] (f : V → W) (H : Hypergraph V) :
    H ⊆ (H.map f).comap f := by
  intro e he
  exact mem_comap.mpr (mem_map.mpr ⟨e, he, rfl⟩)

end Maps

section Weights

variable [DecidableEq V]

/-- Sum an arbitrary edge weight over a hypergraph. -/
def weight {R : Type*} [AddCommMonoid R] (H : Hypergraph V) (w : Finset V → R) : R :=
  ∑ e ∈ H, w e

@[simp] theorem weight_empty {R : Type*} [AddCommMonoid R] (w : Finset V → R) :
    weight (∅ : Hypergraph V) w = 0 := by
  simp [weight]

@[simp] theorem weight_zero {R : Type*} [AddCommMonoid R] (H : Hypergraph V) :
    H.weight (fun _ => (0 : R)) = 0 := by
  simp [weight]

theorem weight_congr {R : Type*} [AddCommMonoid R] {H K : Hypergraph V}
    {w z : Finset V → R} (hHK : H = K) (
      hw : ∀ e ∈ K, w e = z e) : H.weight w = K.weight z := by
  subst H
  exact Finset.sum_congr rfl hw

theorem weight_union {R : Type*} [AddCommMonoid R] {H K : Hypergraph V}
    (hdis : Disjoint H K) (w : Finset V → R) :
    (H ∪ K).weight w = H.weight w + K.weight w := by
  simp [weight, Finset.sum_union hdis]

theorem weight_sdiff_add_weight_inter {R : Type*} [AddCommMonoid R]
    (H K : Hypergraph V) (w : Finset V → R) :
    (H \ K).weight w + (H ∩ K).weight w = H.weight w := by
  rw [← weight_union]
  · congr
    exact Finset.sdiff_union_inter H K
  · exact Finset.disjoint_sdiff_inter H K

theorem weight_nonneg (H : Hypergraph V) {w : Finset V → ℝ}
    (hw : ∀ e ∈ H, 0 ≤ w e) : 0 ≤ H.weight w := by
  exact Finset.sum_nonneg hw

theorem weight_mono {H K : Hypergraph V} (hHK : H ⊆ K) {w : Finset V → ℝ}
    (hw : ∀ e ∈ K, 0 ≤ w e) : H.weight w ≤ K.weight w := by
  exact Finset.sum_le_sum_of_subset_of_nonneg hHK (fun e heK _ => hw e heK)

/-- The standard `p`-weight `∑ₑ p ^ |e|`. -/
def pWeight (H : Hypergraph V) (p : ℝ) : ℝ :=
  H.weight fun e => p ^ e.card

@[simp] theorem pWeight_empty (p : ℝ) : pWeight (∅ : Hypergraph V) p = 0 := by
  simp [pWeight]

theorem pWeight_nonneg (H : Hypergraph V) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ H.pWeight p := by
  exact H.weight_nonneg fun e _ => pow_nonneg hp _

theorem pWeight_mono {H K : Hypergraph V} (hHK : H ⊆ K) {p : ℝ} (hp : 0 ≤ p) :
    H.pWeight p ≤ K.pWeight p := by
  exact weight_mono hHK (fun e _ => pow_nonneg hp e.card)

theorem pWeight_layer (H : Hypergraph V) (p : ℝ) (k : ℕ) :
    (H.layer k).pWeight p = (H.layer k).card * p ^ k := by
  rw [pWeight, weight]
  calc
    ∑ e ∈ H.layer k, p ^ e.card = ∑ _e ∈ H.layer k, p ^ k := by
      apply Finset.sum_congr rfl
      intro e he
      rw [(mem_layer.mp he).2]
    _ = (H.layer k).card * p ^ k := by simp

end Weights

end Hypergraph

end Erdos565
