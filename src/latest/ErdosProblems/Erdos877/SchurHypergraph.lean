/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos877.Core
import ErdosProblems.Erdos877.EnumerationSupersaturation
import ErdosProblems.Erdos565.Hypergraph

/-!
# The finite Schur hypergraph

The vertex `v : Fin n` represents the positive integer `v + 1`.  The edges of
`schurHypergraph n` are the three-element sets `{x,y,z}` with distinct
summands and `x+y=z`.  This is the uniform part of the Schur equation; a
genuinely sum-free set is therefore an independent set in this hypergraph.
-/

open Finset

namespace Erdos877
namespace Enumeration

open Erdos565

/-- The positive integer represented by a vertex of the Schur hypergraph. -/
def vertexNat {n : ℕ} (v : Fin n) : ℕ := v.1 + 1

@[simp] theorem vertexNat_pos {n : ℕ} (v : Fin n) : 0 < vertexNat v := by
  simp [vertexNat]

theorem vertexNat_le {n : ℕ} (v : Fin n) : vertexNat v ≤ n := by
  simp only [vertexNat]
  omega

theorem vertexNat_injective {n : ℕ} : Function.Injective (@vertexNat n) := by
  intro v w h
  apply Fin.ext
  simp only [vertexNat] at h
  omega

/-- Encode the members of `A ∩ {1,...,n}` as vertices. -/
def verticesOf (n : ℕ) (A : Finset ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun v ↦ vertexNat v ∈ A

@[simp] theorem mem_verticesOf {n : ℕ} {A : Finset ℕ} {v : Fin n} :
    v ∈ verticesOf n A ↔ vertexNat v ∈ A := by
  simp [verticesOf]

/-- Decode a set of vertices as positive integers. -/
def naturalsOf {n : ℕ} (I : Finset (Fin n)) : Finset ℕ :=
  I.image vertexNat

@[simp] theorem mem_naturalsOf {n : ℕ} {I : Finset (Fin n)} {x : ℕ} :
    x ∈ naturalsOf I ↔ ∃ v ∈ I, vertexNat v = x := by
  simp [naturalsOf]

theorem naturalsOf_subset_interval {n : ℕ} (I : Finset (Fin n)) :
    naturalsOf I ⊆ interval n := by
  intro x hx
  obtain ⟨v, hv, rfl⟩ := mem_naturalsOf.mp hx
  exact mem_interval.mpr ⟨vertexNat_pos v, vertexNat_le v⟩

@[simp] theorem verticesOf_naturalsOf {n : ℕ} (I : Finset (Fin n)) :
    verticesOf n (naturalsOf I) = I := by
  ext v
  simp only [mem_verticesOf, mem_naturalsOf]
  constructor
  · rintro ⟨w, hw, h⟩
    exact vertexNat_injective h ▸ hw
  · intro hv
    exact ⟨v, hv, rfl⟩

theorem naturalsOf_verticesOf {n : ℕ} {A : Finset ℕ}
    (hA : A ⊆ interval n) :
    naturalsOf (verticesOf n A) = A := by
  ext x
  constructor
  · rintro hx
    obtain ⟨v, hv, rfl⟩ := mem_naturalsOf.mp hx
    exact mem_verticesOf.mp hv
  · intro hx
    have hxi := mem_interval.mp (hA hx)
    let v : Fin n := ⟨x - 1, by omega⟩
    have hvx : vertexNat v = x := by
      simp only [vertexNat, v]
      omega
    exact mem_naturalsOf.mpr ⟨v, mem_verticesOf.mpr (hvx ▸ hx), hvx⟩

theorem verticesOf_injective_on_interval (n : ℕ) :
    Set.InjOn (verticesOf n) {A : Finset ℕ | A ⊆ interval n} := by
  intro A hA B hB h
  rw [← naturalsOf_verticesOf hA, ← naturalsOf_verticesOf hB, h]

/-- Three distinct represented integers satisfying the Schur equation. -/
def IsSchurEdge {n : ℕ} (e : Finset (Fin n)) : Prop :=
  ∃ x ∈ e, ∃ y ∈ e, ∃ z ∈ e,
    x ≠ y ∧ vertexNat x + vertexNat y = vertexNat z

noncomputable instance {n : ℕ} (e : Finset (Fin n)) : Decidable (IsSchurEdge e) :=
  Classical.propDecidable _

/-- The `3`-uniform hypergraph of distinct-summand Schur triples in
`{1,...,n}`. -/
noncomputable def schurHypergraph (n : ℕ) : Erdos565.Hypergraph (Fin n) :=
  (Finset.univ.powersetCard 3).filter IsSchurEdge

@[simp] theorem mem_schurHypergraph {n : ℕ} {e : Finset (Fin n)} :
    e ∈ schurHypergraph n ↔ e.card = 3 ∧ IsSchurEdge e := by
  classical
  simp [schurHypergraph]

theorem schurHypergraph_isUniform (n : ℕ) :
    (schurHypergraph n).IsUniform 3 := by
  intro e he
  exact (mem_schurHypergraph.mp he).1

/-- The three witnesses of a Schur edge exhaust it. -/
theorem schurEdge_eq_triple {n : ℕ} {e : Finset (Fin n)} {x y z : Fin n}
    (hecard : e.card = 3) (hx : x ∈ e) (hy : y ∈ e) (hz : z ∈ e)
    (hxy : x ≠ y) (heq : vertexNat x + vertexNat y = vertexNat z) :
    e = {x, y, z} := by
  have hxz : x ≠ z := by
    intro h
    subst z
    have := vertexNat_pos y
    omega
  have hyz : y ≠ z := by
    intro h
    subst z
    have := vertexNat_pos x
    omega
  have hsub : ({x, y, z} : Finset (Fin n)) ⊆ e := by
    simp [Finset.insert_subset_iff, hx, hy, hz]
  exact (Finset.eq_of_subset_of_card_le hsub (by simp [hecard, hxy, hxz, hyz])).symm

/-- The edge canonically determined by an ordered integer pair. -/
def pairEdge (n : ℕ) (p : ℕ × ℕ) : Finset (Fin n) :=
  verticesOf n {p.1, p.2, p.1 + p.2}

theorem pairEdge_mem_restrict {n : ℕ} {I : Finset (Fin n)} {p : ℕ × ℕ}
    (hp : p ∈ schurPairs (naturalsOf I)) :
    pairEdge n p ∈ (schurHypergraph n).restrict I := by
  classical
  have hp' := mem_schurPairs.mp hp
  rcases hp' with ⟨hp1I, hp2I, hp12, hpSumI⟩
  obtain ⟨x, hxI, hx⟩ := mem_naturalsOf.mp hp1I
  obtain ⟨y, hyI, hy⟩ := mem_naturalsOf.mp hp2I
  obtain ⟨z, hzI, hz⟩ := mem_naturalsOf.mp hpSumI
  have hxyz : vertexNat x + vertexNat y = vertexNat z := by
    omega
  have hxy : x ≠ y := by
    intro h
    subst y
    rw [← hx, ← hy] at hp12
    omega
  have hxmem : x ∈ pairEdge n p := by
    rw [pairEdge, mem_verticesOf, hx]
    simp
  have hymem : y ∈ pairEdge n p := by
    rw [pairEdge, mem_verticesOf, hy]
    simp
  have hzmem : z ∈ pairEdge n p := by
    rw [pairEdge, mem_verticesOf, hz]
    simp
  have hxz : x ≠ z := by
    intro h
    have hv := congrArg vertexNat h
    have := vertexNat_pos y
    omega
  have hyz : y ≠ z := by
    intro h
    have hv := congrArg vertexNat h
    have := vertexNat_pos x
    omega
  have hcard : (pairEdge n p).card = 3 := by
    have heqset : pairEdge n p = {x, y, z} := by
      ext w
      simp only [pairEdge, mem_verticesOf, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro hw
        rcases hw with hw | hw | hw
        · left
          exact vertexNat_injective (hw.trans hx.symm)
        · right; left
          exact vertexNat_injective (hw.trans hy.symm)
        · right; right
          exact vertexNat_injective (hw.trans hz.symm)
      · intro hw
        rcases hw with hw | hw | hw
        · exact hw ▸ Or.inl hx
        · exact hw ▸ Or.inr (Or.inl hy)
        · exact hw ▸ Or.inr (Or.inr hz)
    rw [heqset]
    simp [hxy, hxz, hyz]
  apply Erdos565.Hypergraph.mem_restrict.mpr
  refine ⟨mem_schurHypergraph.mpr ⟨hcard, ?_⟩, ?_⟩
  · exact ⟨x, hxmem, y, hymem, z, hzmem, hxy, hxyz⟩
  · intro w hw
    rw [pairEdge, mem_verticesOf] at hw
    have hw' : vertexNat w = p.1 ∨ vertexNat w = p.2 ∨
        vertexNat w = p.1 + p.2 := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hw
    rcases hw' with hw | hw | hw
    · have hwx : w = x := vertexNat_injective (hw.trans hx.symm)
      exact hwx ▸ hxI
    · have hwy : w = y := vertexNat_injective (hw.trans hy.symm)
      exact hwy ▸ hyI
    · have hwz : w = z := vertexNat_injective (hw.trans hz.symm)
      exact hwz ▸ hzI

theorem pairEdge_surjOn_restrict (n : ℕ) (I : Finset (Fin n)) :
    Set.SurjOn (pairEdge n) (schurPairs (naturalsOf I))
      ((schurHypergraph n).restrict I) := by
  intro e he
  have heH := (Erdos565.Hypergraph.mem_restrict.mp he).1
  obtain ⟨x, hx, y, hy, z, hz, hxy, heq⟩ := (mem_schurHypergraph.mp heH).2
  have hecard := (mem_schurHypergraph.mp heH).1
  have heqtriple := schurEdge_eq_triple hecard hx hy hz hxy heq
  have heI := (Erdos565.Hypergraph.mem_restrict.mp he).2
  have hxI : x ∈ I := heI hx
  have hyI : y ∈ I := heI hy
  have hzI : z ∈ I := heI hz
  by_cases hlt : vertexNat x < vertexNat y
  · refine ⟨(vertexNat x, vertexNat y), ?_, ?_⟩
    · exact mem_schurPairs.mpr
        ⟨mem_naturalsOf.mpr ⟨x, hxI, rfl⟩,
          mem_naturalsOf.mpr ⟨y, hyI, rfl⟩, hlt,
          heq ▸ mem_naturalsOf.mpr ⟨z, hzI, rfl⟩⟩
    · rw [pairEdge, heq]
      calc
        verticesOf n {vertexNat x, vertexNat y, vertexNat z} =
            verticesOf n (naturalsOf ({x, y, z} : Finset (Fin n))) := by
              congr 1
              ext a
              simp [naturalsOf]
        _ = {x, y, z} := verticesOf_naturalsOf _
        _ = e := heqtriple.symm
  · have hgt : vertexNat y < vertexNat x := by
      have hne : vertexNat x ≠ vertexNat y := fun h ↦ hxy (vertexNat_injective h)
      omega
    refine ⟨(vertexNat y, vertexNat x), ?_, ?_⟩
    · exact mem_schurPairs.mpr
        ⟨mem_naturalsOf.mpr ⟨y, hyI, rfl⟩,
          mem_naturalsOf.mpr ⟨x, hxI, rfl⟩, hgt,
          (by rw [Nat.add_comm, heq]; exact mem_naturalsOf.mpr ⟨z, hzI, rfl⟩)⟩
    · rw [pairEdge, Nat.add_comm, heq]
      calc
        verticesOf n {vertexNat y, vertexNat x, vertexNat z} =
            verticesOf n (naturalsOf ({x, y, z} : Finset (Fin n))) := by
              congr 1
              ext a
              simp [naturalsOf, or_left_comm]
        _ = {x, y, z} := verticesOf_naturalsOf _
        _ = e := heqtriple.symm

/-- Distinct-summand Schur pairs cover all edges in a restriction. -/
theorem card_schurHypergraph_restrict_le_card_schurPairs
    (n : ℕ) (I : Finset (Fin n)) :
    ((schurHypergraph n).restrict I).card ≤
      (schurPairs (naturalsOf I)).card := by
  classical
  exact Finset.card_le_card_of_surjOn (pairEdge n)
    (pairEdge_surjOn_restrict n I)

theorem pairEdge_injOn_schurPairs (n : ℕ) (I : Finset (Fin n)) :
    Set.InjOn (pairEdge n) (schurPairs (naturalsOf I)) := by
  intro p hp q hq hpq
  have hp' := mem_schurPairs.mp hp
  have hq' := mem_schurPairs.mp hq
  have hp1pos : 0 < p.1 :=
    (mem_interval.mp (naturalsOf_subset_interval I hp'.1)).1
  have hp2pos : 0 < p.2 :=
    (mem_interval.mp (naturalsOf_subset_interval I hp'.2.1)).1
  have hq1pos : 0 < q.1 :=
    (mem_interval.mp (naturalsOf_subset_interval I hq'.1)).1
  have hq2pos : 0 < q.2 :=
    (mem_interval.mp (naturalsOf_subset_interval I hq'.2.1)).1
  have hpSub : ({p.1, p.2, p.1 + p.2} : Finset ℕ) ⊆ interval n := by
    intro a ha
    have ha' : a = p.1 ∨ a = p.2 ∨ a = p.1 + p.2 := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using ha
    rcases ha' with rfl | rfl | rfl
    · exact naturalsOf_subset_interval I hp'.1
    · exact naturalsOf_subset_interval I hp'.2.1
    · exact naturalsOf_subset_interval I hp'.2.2.2
  have hqSub : ({q.1, q.2, q.1 + q.2} : Finset ℕ) ⊆ interval n := by
    intro a ha
    have ha' : a = q.1 ∨ a = q.2 ∨ a = q.1 + q.2 := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using ha
    rcases ha' with rfl | rfl | rfl
    · exact naturalsOf_subset_interval I hq'.1
    · exact naturalsOf_subset_interval I hq'.2.1
    · exact naturalsOf_subset_interval I hq'.2.2.2
  have hsets : ({p.1, p.2, p.1 + p.2} : Finset ℕ) =
      {q.1, q.2, q.1 + q.2} := by
    calc
      _ = naturalsOf (pairEdge n p) := (naturalsOf_verticesOf hpSub).symm
      _ = naturalsOf (pairEdge n q) := congrArg naturalsOf hpq
      _ = _ := naturalsOf_verticesOf hqSub
  have hpSumMem : p.1 + p.2 = q.1 ∨ p.1 + p.2 = q.2 ∨
      p.1 + p.2 = q.1 + q.2 := by
    have : p.1 + p.2 ∈ ({q.1, q.2, q.1 + q.2} : Finset ℕ) := by
      rw [← hsets]
      simp
    simpa only [Finset.mem_insert, Finset.mem_singleton] using this
  have hqSumMem : q.1 + q.2 = p.1 ∨ q.1 + q.2 = p.2 ∨
      q.1 + q.2 = p.1 + p.2 := by
    have : q.1 + q.2 ∈ ({p.1, p.2, p.1 + p.2} : Finset ℕ) := by
      rw [hsets]
      simp
    simpa only [Finset.mem_insert, Finset.mem_singleton] using this
  have hsum : p.1 + p.2 = q.1 + q.2 := by
    rcases hpSumMem with h | h | h <;>
      rcases hqSumMem with h' | h' | h' <;> omega
  have hp1Mem : p.1 = q.1 ∨ p.1 = q.2 ∨ p.1 = q.1 + q.2 := by
    have : p.1 ∈ ({q.1, q.2, q.1 + q.2} : Finset ℕ) := by
      rw [← hsets]
      simp
    simpa only [Finset.mem_insert, Finset.mem_singleton] using this
  have hp2Mem : p.2 = q.1 ∨ p.2 = q.2 ∨ p.2 = q.1 + q.2 := by
    have : p.2 ∈ ({q.1, q.2, q.1 + q.2} : Finset ℕ) := by
      rw [← hsets]
      simp
    simpa only [Finset.mem_insert, Finset.mem_singleton] using this
  have hfirst : p.1 = q.1 := by
    rcases hp1Mem with h | h | h <;>
      rcases hp2Mem with h' | h' | h' <;> omega
  apply Prod.ext
  · exact hfirst
  · omega

/-- The oriented pair parametrization is in fact a bijection. -/
theorem card_schurPairs_eq_card_schurHypergraph_restrict
    (n : ℕ) (I : Finset (Fin n)) :
    (schurPairs (naturalsOf I)).card =
      ((schurHypergraph n).restrict I).card := by
  apply Nat.le_antisymm
  · exact Finset.card_le_card_of_injOn (pairEdge n)
      (fun _ hp ↦ pairEdge_mem_restrict hp) (pairEdge_injOn_schurPairs n I)
  · exact card_schurHypergraph_restrict_le_card_schurPairs n I

/-- The at most three arithmetic values which can complete a prescribed pair
of vertices to a Schur triple. -/
def completionCandidates {n : ℕ} (a b : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun w ↦
    vertexNat w ∈
      ({vertexNat a + vertexNat b, vertexNat a - vertexNat b,
        vertexNat b - vertexNat a} : Finset ℕ)

@[simp] theorem mem_completionCandidates {n : ℕ} {a b w : Fin n} :
    w ∈ completionCandidates a b ↔
      vertexNat w = vertexNat a + vertexNat b ∨
      vertexNat w = vertexNat a - vertexNat b ∨
      vertexNat w = vertexNat b - vertexNat a := by
  simp [completionCandidates]

theorem card_completionCandidates_le_three {n : ℕ} (a b : Fin n) :
    (completionCandidates a b).card ≤ 3 := by
  classical
  have himage : (completionCandidates a b).image vertexNat ⊆
      ({vertexNat a + vertexNat b, vertexNat a - vertexNat b,
        vertexNat b - vertexNat a} : Finset ℕ) := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨w, hw, rfl⟩ := hx
    exact (Finset.mem_filter.mp hw).2
  calc
    (completionCandidates a b).card =
        ((completionCandidates a b).image vertexNat).card :=
      (Finset.card_image_iff.mpr vertexNat_injective.injOn).symm
    _ ≤ ({vertexNat a + vertexNat b, vertexNat a - vertexNat b,
          vertexNat b - vertexNat a} : Finset ℕ).card :=
      Finset.card_le_card himage
    _ ≤ 3 := by
      have h₁ := Finset.card_insert_le (vertexNat a + vertexNat b)
        ({vertexNat a - vertexNat b, vertexNat b - vertexNat a} : Finset ℕ)
      have h₂ := Finset.card_insert_le (vertexNat a - vertexNat b)
        ({vertexNat b - vertexNat a} : Finset ℕ)
      simp only [Finset.card_singleton] at h₁ h₂
      omega

theorem schurHypergraph_degree_pair_le_three {n : ℕ} {a b : Fin n}
    (hab : a ≠ b) :
    (schurHypergraph n).degree {a, b} ≤ 3 := by
  classical
  have hedgeSubset :
      (schurHypergraph n).filter (fun e ↦ ({a, b} : Finset (Fin n)) ⊆ e) ⊆
        (completionCandidates a b).image (fun w ↦ insert w {a, b}) := by
    intro e he
    have heH := (Finset.mem_filter.mp he).1
    have habE := (Finset.mem_filter.mp he).2
    have hecard := (mem_schurHypergraph.mp heH).1
    have hdiff : (e \ {a, b}).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      have hesub : e ⊆ {a, b} := Finset.sdiff_eq_empty_iff_subset.mp hempty
      have := Finset.card_le_card hesub
      simp [hecard, hab] at this
    obtain ⟨w, hw⟩ := hdiff
    have hwE : w ∈ e := (Finset.mem_sdiff.mp hw).1
    have hwab : w ∉ ({a, b} : Finset (Fin n)) := (Finset.mem_sdiff.mp hw).2
    have hwneA : w ≠ a := by
      intro h
      apply hwab
      simp [h]
    have hwneB : w ≠ b := by
      intro h
      apply hwab
      simp [h]
    have hinsertSub : insert w {a, b} ⊆ e := by
      simpa [Finset.insert_subset_iff, hwE] using habE
    have hinsertCard : ({w, a, b} : Finset (Fin n)).card = 3 := by
      simp [hab, hwneA, hwneB]
    have hcardle : e.card ≤ ({w, a, b} : Finset (Fin n)).card := by
      rw [hecard, hinsertCard]
    have heq : e = insert w {a, b} :=
      (Finset.eq_of_subset_of_card_le hinsertSub hcardle).symm
    obtain ⟨x, hx, y, hy, z, hz, hxy, hsum⟩ := (mem_schurHypergraph.mp heH).2
    have hx' : x ∈ insert w {a, b} := heq ▸ hx
    have hy' : y ∈ insert w {a, b} := heq ▸ hy
    have hz' : z ∈ insert w {a, b} := heq ▸ hz
    have hxv : vertexNat x = vertexNat w ∨ vertexNat x = vertexNat a ∨
        vertexNat x = vertexNat b := by
      have h : x = w ∨ x = a ∨ x = b := by
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hx'
      rcases h with h | h | h
      · exact Or.inl (congrArg vertexNat h)
      · exact Or.inr (Or.inl (congrArg vertexNat h))
      · exact Or.inr (Or.inr (congrArg vertexNat h))
    have hyv : vertexNat y = vertexNat w ∨ vertexNat y = vertexNat a ∨
        vertexNat y = vertexNat b := by
      have h : y = w ∨ y = a ∨ y = b := by
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hy'
      rcases h with h | h | h
      · exact Or.inl (congrArg vertexNat h)
      · exact Or.inr (Or.inl (congrArg vertexNat h))
      · exact Or.inr (Or.inr (congrArg vertexNat h))
    have hzv : vertexNat z = vertexNat w ∨ vertexNat z = vertexNat a ∨
        vertexNat z = vertexNat b := by
      have h : z = w ∨ z = a ∨ z = b := by
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hz'
      rcases h with h | h | h
      · exact Or.inl (congrArg vertexNat h)
      · exact Or.inr (Or.inl (congrArg vertexNat h))
      · exact Or.inr (Or.inr (congrArg vertexNat h))
    have hxyv : vertexNat x ≠ vertexNat y := by
      intro h
      exact hxy (vertexNat_injective h)
    have hwpos := vertexNat_pos w
    have hap := vertexNat_pos a
    have hbp := vertexNat_pos b
    have hwcand : w ∈ completionCandidates a b := by
      rw [mem_completionCandidates]
      rcases hxv with h | h | h <;>
        rcases hyv with h' | h' | h' <;>
          rcases hzv with h'' | h'' | h'' <;> omega
    exact Finset.mem_image.mpr ⟨w, hwcand, heq.symm⟩
  rw [Erdos565.Hypergraph.degree]
  calc
    _ ≤ ((completionCandidates a b).image (fun w ↦ insert w {a, b})).card :=
      Finset.card_le_card hedgeSubset
    _ ≤ (completionCandidates a b).card := Finset.card_image_le
    _ ≤ 3 := card_completionCandidates_le_three a b

/-- Every set of at least two vertices has uniformly bounded codegree.  The
constant `6` is the convenient bound consumed by the container estimate (the
proof actually gives `3`). -/
theorem schurHypergraph_degree_le_six (n : ℕ) (c : Finset (Fin n))
    (hc : 2 ≤ c.card) :
    (schurHypergraph n).degree c ≤ 6 := by
  have hc' : 1 < c.card := by omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hc'
  calc
    (schurHypergraph n).degree c ≤ (schurHypergraph n).degree {a, b} :=
      Erdos565.Hypergraph.degree_anti_right (schurHypergraph n) (by
        intro x hx
        have hx' : x = a ∨ x = b := by
          simpa only [Finset.mem_insert, Finset.mem_singleton] using hx
        rcases hx' with rfl | rfl
        · exact ha
        · exact hb)
    _ ≤ 3 := schurHypergraph_degree_pair_le_three hab
    _ ≤ 6 := by omega

/-- A sum-free subset of the interval encodes to an independent vertex set. -/
theorem sumFree_independent_verticesOf {n : ℕ} {A : Finset ℕ}
    (hA : SumFree A) :
    (schurHypergraph n).IsIndependent (verticesOf n A) := by
  intro e he heA
  obtain ⟨x, hx, y, hy, z, hz, hxy, heq⟩ := (mem_schurHypergraph.mp he).2
  have hxA : vertexNat x ∈ A := mem_verticesOf.mp (heA hx)
  have hyA : vertexNat y ∈ A := mem_verticesOf.mp (heA hy)
  have hzA : vertexNat z ∈ A := mem_verticesOf.mp (heA hz)
  exact hA hxA hyA (heq ▸ hzA)

/-- All independent vertex sets in the finite Schur hypergraph. -/
noncomputable def independentVertexSets (n : ℕ) : Finset (Finset (Fin n)) :=
  by
    classical
    exact Finset.univ.filter (schurHypergraph n).IsIndependent

@[simp] theorem mem_independentVertexSets {n : ℕ} {I : Finset (Fin n)} :
    I ∈ independentVertexSets n ↔ (schurHypergraph n).IsIndependent I := by
  classical
  simp [independentVertexSets]

/-- Counting genuinely sum-free sets is bounded by counting independent sets
of the distinct-summand Schur hypergraph. -/
theorem sumFreeCount_le_independentVertexSets (n : ℕ) :
    sumFreeCount n ≤ (independentVertexSets n).card := by
  classical
  rw [sumFreeCount]
  apply Finset.card_le_card_of_injOn (verticesOf n)
  · intro A hA
    have hA' := (mem_sumFreeSets (n := n) (A := A)).mp hA
    exact mem_independentVertexSets.mpr (sumFree_independent_verticesOf hA'.2)
  · intro A hA B hB hAB
    apply verticesOf_injective_on_interval n
    · exact ((mem_sumFreeSets (n := n) (A := A)).mp hA).1
    · exact ((mem_sumFreeSets (n := n) (A := B)).mp hB).1
    · exact hAB

end Enumeration
end Erdos877
