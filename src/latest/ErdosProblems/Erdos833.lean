/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Mathlib

/-!
# Erdős Problem 833

Erdős and Lovász proved that an `r`-uniform hypergraph which is not
two-colourable has a vertex of degree at least `2^(r-1)/(4*r)`.  The proof
below formalizes their finite symmetric-local-lemma argument and then gives
the explicit absolute constant `c = 1/9` for the original question.

The detailed mathematical reconstruction is in `tex/833.tex`.
-/

namespace Erdos833

open scoped BigOperators

section FiniteLocalLemma

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype ι] [DecidableEq ι]

/-- The outcomes avoiding every event indexed by `S`. -/
def avoid (A : ι → Finset Ω) (S : Finset ι) : Finset Ω :=
  Finset.univ.filter fun ω ↦ ∀ i ∈ S, ω ∉ A i

@[simp] lemma mem_avoid {A : ι → Finset Ω} {S : Finset ι} {ω : Ω} :
    ω ∈ avoid A S ↔ ∀ i ∈ S, ω ∉ A i := by
  simp [avoid]

@[simp] lemma avoid_empty (A : ι → Finset Ω) : avoid A ∅ = Finset.univ := by
  ext
  simp [avoid]

lemma avoid_insert (A : ι → Finset Ω) (i : ι) (S : Finset ι) :
    avoid A (insert i S) = avoid A S \ A i := by
  ext ω
  simp [avoid, and_comm]

lemma avoid_anti (A : ι → Finset Ω) {S T : Finset ι} (hST : S ⊆ T) :
    avoid A T ⊆ avoid A S := by
  intro ω hω
  rw [mem_avoid] at hω ⊢
  exact fun i hi ↦ hω i (hST hi)

/--
A cardinal form of the finite symmetric local lemma.  The `hfar` hypothesis
is the conditional `1/(4d)` bound after avoiding any collection of
non-neighbouring events.  It follows from ordinary independence, and is the
form that is most convenient for the finite coloring space used below.
-/
theorem finite_symmetric_local_lemma
    [Nonempty Ω] (A : ι → Finset Ω) (N : ι → Finset ι) (d : ℕ)
    (hd : 0 < d)
    (hN : ∀ i, (N i).card ≤ d)
    (hfar : ∀ (i : ι) (S : Finset ι), i ∉ S →
      (∀ j ∈ S, j ∉ N i) →
      4 * d * (A i ∩ avoid A S).card ≤ (avoid A S).card) :
    (avoid A Finset.univ).Nonempty := by
  classical
  let Good : Finset ι → Prop := fun S ↦
    (avoid A S).Nonempty ∧
      ∀ i, i ∉ S → 2 * d * (A i ∩ avoid A S).card ≤ (avoid A S).card
  have main : ∀ n : ℕ, ∀ S : Finset ι, S.card = n → Good S := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro S hScard
        have hnonempty : (avoid A S).Nonempty := by
          by_cases hS : S = ∅
          · subst S
            simp [avoid]
          · obtain ⟨j, hjS⟩ := S.nonempty_iff_ne_empty.mpr hS
            let T := S.erase j
            have hTcard : T.card < n := by
              rw [← hScard]
              exact Finset.card_erase_lt_of_mem hjS
            have hgoodT : Good T := ih T.card hTcard T rfl
            have hjT : j ∉ T := Finset.notMem_erase _ _
            have hjbound := hgoodT.2 j hjT
            have htwo : 2 * (A j ∩ avoid A T).card ≤ (avoid A T).card := by
              calc
                2 * (A j ∩ avoid A T).card
                    ≤ (2 * d) * (A j ∩ avoid A T).card := by
                      gcongr
                      omega
                _ = 2 * d * (A j ∩ avoid A T).card := by ring
                _ ≤ (avoid A T).card := hjbound
            have hbadlt : (A j ∩ avoid A T).card < (avoid A T).card := by
              have hpos : 0 < (avoid A T).card := Finset.card_pos.mpr hgoodT.1
              omega
            have hST : S = insert j T := by
              simp [T, hjS]
            rw [hST, avoid_insert]
            apply Finset.card_pos.mp
            rw [Finset.card_sdiff]
            simpa [Finset.inter_comm] using Nat.sub_pos_of_lt hbadlt
        refine ⟨hnonempty, ?_⟩
        intro i hiS
        let U := S.filter fun j ↦ j ∈ N i
        let T := S.filter fun j ↦ j ∉ N i
        by_cases hU : U = ∅
        · have hfarS : 4 * d * (A i ∩ avoid A S).card ≤ (avoid A S).card := by
            apply hfar i S hiS
            intro j hjS hjN
            have : j ∈ U := by simp [U, hjS, hjN]
            simpa [hU] using this
          calc
            2 * d * (A i ∩ avoid A S).card
                ≤ 4 * d * (A i ∩ avoid A S).card := by
                  gcongr
                  omega
            _ ≤ (avoid A S).card := hfarS
        · have hU_nonempty : U.Nonempty := Finset.nonempty_iff_ne_empty.mpr hU
          have hTsub : T ⊆ S := Finset.filter_subset _ _
          have hTltS : T.card < S.card := by
            apply Finset.card_lt_card
            refine Finset.ssubset_iff_subset_ne.mpr ⟨hTsub, ?_⟩
            intro hTS
            obtain ⟨j, hjU⟩ := hU_nonempty
            have hjS : j ∈ S := (Finset.mem_filter.mp hjU).1
            have hjN : j ∈ N i := (Finset.mem_filter.mp hjU).2
            have hjT : j ∉ T := by simp [T, hjN]
            exact hjT (hTS ▸ hjS)
          have hgoodT : Good T := ih T.card (hTltS.trans_eq hScard) T rfl
          have hST : S = T ∪ U := by
            ext j
            by_cases hjN : j ∈ N i <;> simp [T, U, hjN]
          have hBSBT : avoid A S ⊆ avoid A T :=
            avoid_anti A (hST ▸ Finset.subset_union_left)
          let lost := avoid A T \ avoid A S
          have hlost_subset :
              lost ⊆ U.biUnion fun j ↦ A j ∩ avoid A T := by
            intro ω hω
            have hωT : ω ∈ avoid A T := (Finset.mem_sdiff.mp hω).1
            have hωS : ω ∉ avoid A S := (Finset.mem_sdiff.mp hω).2
            rw [mem_avoid] at hωT
            rw [mem_avoid] at hωS
            simp only [not_forall] at hωS
            obtain ⟨j, hjS, hωAj⟩ := hωS
            have hjN : j ∈ N i := by
              by_contra hjN
              exact hωAj (hωT j (by simp [T, hjS, hjN]))
            rw [Finset.mem_biUnion]
            exact ⟨j, by simp [U, hjS, hjN], Finset.mem_inter.mpr ⟨by simpa using hωAj, by simpa using
              (show ω ∈ avoid A T from (Finset.mem_sdiff.mp hω).1)⟩⟩
          have hlost_card :
              lost.card ≤ ∑ j ∈ U, (A j ∩ avoid A T).card := by
            calc
              lost.card ≤ (U.biUnion fun j ↦ A j ∩ avoid A T).card :=
                Finset.card_le_card hlost_subset
              _ ≤ ∑ j ∈ U, (A j ∩ avoid A T).card := Finset.card_biUnion_le
          have hsum :
              2 * d * (∑ j ∈ U, (A j ∩ avoid A T).card) ≤
                U.card * (avoid A T).card := by
            calc
              2 * d * (∑ j ∈ U, (A j ∩ avoid A T).card)
                  = ∑ j ∈ U, 2 * d * (A j ∩ avoid A T).card := by
                    simp [Finset.mul_sum]
              _ ≤ ∑ _j ∈ U, (avoid A T).card := by
                    apply Finset.sum_le_sum
                    intro j hjU
                    apply hgoodT.2 j
                    simp [T, (Finset.mem_filter.mp hjU).2]
              _ = U.card * (avoid A T).card := by simp
          have hUcard : U.card ≤ d := by
            exact (Finset.card_le_card (show U ⊆ N i by
              intro j hj
              exact (Finset.mem_filter.mp hj).2)).trans (hN i)
          have hlost_scaled :
              2 * d * lost.card ≤ d * (avoid A T).card := by
            calc
              2 * d * lost.card
                  ≤ 2 * d * (∑ j ∈ U, (A j ∩ avoid A T).card) := by gcongr
              _ ≤ U.card * (avoid A T).card := hsum
              _ ≤ d * (avoid A T).card := Nat.mul_le_mul_right _ hUcard
          have hlost_twice : 2 * lost.card ≤ (avoid A T).card := by
            exact Nat.le_of_mul_le_mul_left
              (by simpa [mul_assoc, mul_left_comm, mul_comm] using hlost_scaled) hd
          have hlost_add : lost.card + (avoid A S).card = (avoid A T).card := by
            simpa [lost] using Finset.card_sdiff_add_card_eq_card hBSBT
          have hT_le_twoS : (avoid A T).card ≤ 2 * (avoid A S).card := by omega
          have hiT : i ∉ T := by
            simp [T, hiS]
          have hfarT : 4 * d * (A i ∩ avoid A T).card ≤ (avoid A T).card := by
            apply hfar i T hiT
            intro j hjT
            exact (Finset.mem_filter.mp hjT).2
          have hinter : (A i ∩ avoid A S).card ≤ (A i ∩ avoid A T).card := by
            apply Finset.card_le_card
            exact Finset.inter_subset_inter (by rfl) hBSBT
          have hfour :
              4 * d * (A i ∩ avoid A S).card ≤ 2 * (avoid A S).card := by
            calc
              4 * d * (A i ∩ avoid A S).card
                  ≤ 4 * d * (A i ∩ avoid A T).card := by gcongr
              _ ≤ (avoid A T).card := hfarT
              _ ≤ 2 * (avoid A S).card := hT_le_twoS
          have hcancel :
              2 * (2 * d * (A i ∩ avoid A S).card) ≤
                2 * (avoid A S).card := by
            simpa [mul_assoc, mul_left_comm, mul_comm] using hfour
          exact Nat.le_of_mul_le_mul_left hcancel (by omega)
  exact (main Finset.univ.card Finset.univ rfl).1

end FiniteLocalLemma

section Hypergraphs

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- A finite simple set-valued hypergraph. -/
abbrev Hypergraph (V : Type u) [Fintype V] [DecidableEq V] := Finset (Finset V)

/-- Every edge has exactly `r` vertices. -/
def IsUniform (H : Hypergraph V) (r : ℕ) : Prop :=
  ∀ e ∈ H, e.card = r

/-- An edge is monochromatic under `c`. -/
def Monochromatic {κ : Type*} (c : V → κ) (e : Finset V) : Prop :=
  ∀ x ∈ e, ∀ y ∈ e, c x = c y

/-- A vertex coloring is proper when no edge is monochromatic. -/
def IsProper {κ : Type*} (H : Hypergraph V) (c : V → κ) : Prop :=
  ∀ e ∈ H, ¬ Monochromatic c e

/-- Proper colorability by a palette of size `k`. -/
def Colorable (H : Hypergraph V) (k : ℕ) : Prop :=
  ∃ c : V → Fin k, IsProper H c

/-- The literal least-palette definition of chromatic number `k`. -/
def HasChromaticNumber (H : Hypergraph V) (k : ℕ) : Prop :=
  Colorable H k ∧ ∀ q < k, ¬ Colorable H q

/-- The number of edges containing `v`. -/
def degree (H : Hypergraph V) (v : V) : ℕ :=
  (H.filter fun e ↦ v ∈ e).card

/-- Other edges of `H` which meet `e`. -/
def edgeNeighbors (H : Hypergraph V) (e : Finset V) : Finset (Finset V) :=
  (H.erase e).filter fun f ↦ ¬Disjoint e f

lemma edgeNeighbors_card_le_sum_degree (H : Hypergraph V) (e : Finset V) :
    (edgeNeighbors H e).card ≤ ∑ v ∈ e, degree H v := by
  classical
  have hsub : edgeNeighbors H e ⊆ e.biUnion fun v ↦ H.filter fun f ↦ v ∈ f := by
    intro f hf
    have hf' := Finset.mem_filter.mp hf
    have hmeet : (e ∩ f).Nonempty := Finset.not_disjoint_iff_nonempty_inter.mp hf'.2
    obtain ⟨v, hv⟩ := hmeet
    have hve : v ∈ e := (Finset.mem_inter.mp hv).1
    have hvf : v ∈ f := (Finset.mem_inter.mp hv).2
    rw [Finset.mem_biUnion]
    exact ⟨v, hve, Finset.mem_filter.mpr ⟨Finset.mem_of_mem_erase hf'.1, hvf⟩⟩
  calc
    (edgeNeighbors H e).card
        ≤ (e.biUnion fun v ↦ H.filter fun f ↦ v ∈ f).card := Finset.card_le_card hsub
    _ ≤ ∑ v ∈ e, (H.filter fun f ↦ v ∈ f).card := Finset.card_biUnion_le
    _ = ∑ v ∈ e, degree H v := by rfl

lemma edgeNeighbors_card_le_mul (H : Hypergraph V) (e : Finset V) (D : ℕ)
    (hdeg : ∀ v, degree H v ≤ D) :
    (edgeNeighbors H e).card ≤ e.card * D := by
  calc
    (edgeNeighbors H e).card ≤ ∑ v ∈ e, degree H v :=
      edgeNeighbors_card_le_sum_degree H e
    _ ≤ ∑ _v ∈ e, D := Finset.sum_le_sum fun v _ ↦ hdeg v
    _ = e.card * D := by simp

/-- The finite event of two-colorings monochromatic on `e`. -/
noncomputable def monoEvent (e : Finset V) : Finset (V → Fin 2) :=
  by
    classical
    exact Finset.univ.filter fun c ↦ Monochromatic c e

@[simp] lemma mem_monoEvent {e : Finset V} {c : V → Fin 2} :
    c ∈ monoEvent e ↔ Monochromatic c e := by
  classical
  simp [monoEvent]

/-- Replace the colors on `e` by the pattern `p`. -/
def recolor (e : Finset V) (p : e → Fin 2) (c : V → Fin 2) : V → Fin 2 :=
  fun v ↦ if hv : v ∈ e then p ⟨v, hv⟩ else c v

@[simp] lemma recolor_of_mem (e : Finset V) (p : e → Fin 2) (c : V → Fin 2)
    {v : V} (hv : v ∈ e) : recolor e p c v = p ⟨v, hv⟩ := by
  simp [recolor, hv]

@[simp] lemma recolor_of_notMem (e : Finset V) (p : e → Fin 2) (c : V → Fin 2)
    {v : V} (hv : v ∉ e) : recolor e p c v = c v := by
  simp [recolor, hv]

lemma monochromatic_recolor_iff_of_disjoint (e f : Finset V) (hdisj : Disjoint e f)
    (p : e → Fin 2) (c : V → Fin 2) :
    Monochromatic (recolor e p c) f ↔ Monochromatic c f := by
  have hout : ∀ x ∈ f, x ∉ e := by
    intro x hxf hxe
    exact Finset.disjoint_left.mp hdisj hxe hxf
  simp only [Monochromatic]
  constructor <;> intro h x hx y hy
  · simpa [recolor_of_notMem e p c (hout x hx), recolor_of_notMem e p c (hout y hy)]
      using h x hx y hy
  · simpa [recolor_of_notMem e p c (hout x hx), recolor_of_notMem e p c (hout y hy)]
      using h x hx y hy

/-- Recoloring `e` preserves avoidance of events supported on edges disjoint from `e`. -/
lemma recolor_mem_avoid_of_disjoint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (edge : ι → Finset V) (e : Finset V) (S : Finset ι)
    (hdisj : ∀ j ∈ S, Disjoint e (edge j))
    (p : e → Fin 2) {c : V → Fin 2}
    (hc : c ∈ avoid (fun j ↦ monoEvent (edge j)) S) :
    recolor e p c ∈ avoid (fun j ↦ monoEvent (edge j)) S := by
  rw [mem_avoid] at hc ⊢
  intro j hjS
  intro hbad
  apply hc j hjS
  rw [mem_monoEvent] at hbad ⊢
  exact (monochromatic_recolor_iff_of_disjoint e (edge j) (hdisj j hjS) p c).mp hbad

/--
The conditional monochromatic-event estimate used to instantiate the local
lemma.  It is proved by an explicit injection: recolor `e` by one of
`4*d` tagged patterns while remembering the old constant color.
-/
lemma monoEvent_inter_avoid_card_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (edge : ι → Finset V) (i : ι) (S : Finset ι) (r d : ℕ)
    (hr : 0 < r) (hcard : (edge i).card = r)
    (hdisj : ∀ j ∈ S, Disjoint (edge i) (edge j))
    (hnum : 4 * d ≤ 2 ^ (r - 1)) :
    4 * d * (monoEvent (edge i) ∩ avoid (fun j ↦ monoEvent (edge j)) S).card ≤
      (avoid (fun j ↦ monoEvent (edge j)) S).card := by
  classical
  let e := edge i
  have hecard : e.card = r := hcard
  have he : e.Nonempty := by
    apply Finset.card_pos.mp
    rw [hcard]
    omega
  let x₀ : e := ⟨he.choose, he.choose_spec⟩
  have hpatterns : 8 * d ≤ 2 ^ r := by
    calc
      8 * d = 2 * (4 * d) := by ring
      _ ≤ 2 * 2 ^ (r - 1) := Nat.mul_le_mul_left 2 hnum
      _ = 2 ^ r := by
        conv_rhs => rw [← Nat.succ_pred_eq_of_pos hr]
        rw [pow_succ]
        simp [Nat.pred_eq_sub_one, mul_comm]
  have hcardLE : Fintype.card (Fin (4 * d) × Fin 2) ≤ Fintype.card (e → Fin 2) := by
    simpa [Fintype.card_fun, hecard, mul_comm, mul_left_comm, mul_assoc] using hpatterns
  let pat : Fin (4 * d) × Fin 2 ↪ (e → Fin 2) :=
    Classical.choice (Function.Embedding.nonempty_iff_card_le.mpr hcardLE)
  let B := avoid (fun j ↦ monoEvent (edge j)) S
  let C := monoEvent e ∩ B
  let F : Fin (4 * d) × C → B := fun z ↦
    ⟨recolor e (pat (z.1, z.2.1 x₀)) z.2.1,
      recolor_mem_avoid_of_disjoint edge e S hdisj
        (pat (z.1, z.2.1 x₀)) (Finset.mem_inter.mp z.2.2).2⟩
  have hFinj : Function.Injective F := by
    intro z w hzw
    have hfun :
        recolor e (pat (z.1, z.2.1 x₀)) z.2.1 =
          recolor e (pat (w.1, w.2.1 x₀)) w.2.1 :=
      congr_arg Subtype.val hzw
    have hpat : pat (z.1, z.2.1 x₀) = pat (w.1, w.2.1 x₀) := by
      funext x
      have := congr_fun hfun x
      simpa [recolor_of_mem e (pat (z.1, z.2.1 x₀)) z.2.1 x.property,
        recolor_of_mem e (pat (w.1, w.2.1 x₀)) w.2.1 x.property] using this
    have htag : (z.1, z.2.1 x₀) = (w.1, w.2.1 x₀) := pat.injective hpat
    have hc : z.2.1 = w.2.1 := by
      funext v
      by_cases hv : v ∈ e
      · have hzmono : Monochromatic z.2.1 e :=
          mem_monoEvent.mp (Finset.mem_inter.mp z.2.2).1
        have hwmono : Monochromatic w.2.1 e :=
          mem_monoEvent.mp (Finset.mem_inter.mp w.2.2).1
        calc
          z.2.1 v = z.2.1 x₀ := hzmono v hv x₀ x₀.property
          _ = w.2.1 x₀ := congr_arg Prod.snd htag
          _ = w.2.1 v := (hwmono v hv x₀ x₀.property).symm
      · have := congr_fun hfun v
        simpa [recolor_of_notMem e (pat (z.1, z.2.1 x₀)) z.2.1 hv,
          recolor_of_notMem e (pat (w.1, w.2.1 x₀)) w.2.1 hv] using this
    apply Prod.ext
    · exact congr_arg (fun q : Fin (4 * d) × Fin 2 ↦ q.1) htag
    · exact Subtype.ext hc
  have hle := Fintype.card_le_of_injective F hFinj
  have hle' : 4 * d * C.card ≤ B.card := by
    simpa only [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe] using hle
  exact hle'

/-- The dependency neighborhood on the subtype of edges of `H`. -/
def dependencyNeighbors (H : Hypergraph V) (e : {f // f ∈ H}) :
    Finset {f // f ∈ H} :=
  Finset.univ.filter fun f ↦ f ≠ e ∧ ¬Disjoint e.1 f.1

lemma dependencyNeighbors_card (H : Hypergraph V) (e : {f // f ∈ H}) :
    (dependencyNeighbors H e).card = (edgeNeighbors H e.1).card := by
  classical
  apply Finset.card_bij (fun f _ ↦ f.1)
  · intro f hf
    have hf' := Finset.mem_filter.mp hf
    rw [edgeNeighbors, Finset.mem_filter, Finset.mem_erase]
    exact ⟨⟨fun h ↦ hf'.2.1 (Subtype.ext h), f.2⟩, hf'.2.2⟩
  · intro f _ g _ hfg
    exact Subtype.ext hfg
  · intro f hf
    have hf' := Finset.mem_filter.mp hf
    have hferase := Finset.mem_erase.mp hf'.1
    have hfH : f ∈ H := hferase.2
    let g : {f // f ∈ H} := ⟨f, hfH⟩
    refine ⟨g, ?_, rfl⟩
    rw [dependencyNeighbors, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, hf'.2⟩
    intro hge
    exact hferase.1 (congr_arg Subtype.val hge)

lemma dependencyNeighbors_card_le (H : Hypergraph V) (e : {f // f ∈ H})
    (r D : ℕ) (hunif : IsUniform H r) (hdeg : ∀ v, degree H v ≤ D) :
    (dependencyNeighbors H e).card ≤ r * D := by
  rw [dependencyNeighbors_card]
  calc
    (edgeNeighbors H e.1).card ≤ e.1.card * D :=
      edgeNeighbors_card_le_mul H e.1 D hdeg
    _ = r * D := by rw [hunif e.1 e.2]

lemma colorable_of_empty (H : Hypergraph V) (hH : H = ∅) : Colorable H 2 := by
  subst H
  exact ⟨fun _ ↦ 0, by simp [IsProper]⟩

/--
The exact Erdős--Lovász degree bound, in division-free natural-number form.
The assumption is stronger than three-chromaticity: failure of a proper
two-coloring is enough.
-/
theorem erdos_lovasz_degree_bound
    (H : Hypergraph V) (r : ℕ) (hr : 2 ≤ r)
    (hunif : IsUniform H r) (hnot2 : ¬Colorable H 2) :
    ∃ v : V, 2 ^ (r - 1) ≤ 4 * r * degree H v := by
  classical
  have hH : H.Nonempty := by
    by_contra h
    exact hnot2 (colorable_of_empty H (Finset.not_nonempty_iff_eq_empty.mp h))
  obtain ⟨e₀, he₀H⟩ := hH
  have he₀card : e₀.card = r := hunif e₀ he₀H
  have he₀ : e₀.Nonempty := by
    apply Finset.card_pos.mp
    rw [he₀card]
    omega
  let v₀ : V := he₀.choose
  letI : Nonempty V := ⟨v₀⟩
  obtain ⟨vmax, _hvmax, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset V) (degree H) Finset.univ_nonempty
  let D := degree H vmax
  have hdeg : ∀ v, degree H v ≤ D := fun v ↦ hmax v (Finset.mem_univ v)
  have hDpos : 0 < D := by
    have he₀mem : e₀ ∈ H.filter fun e ↦ v₀ ∈ e := by
      rw [Finset.mem_filter]
      exact ⟨he₀H, he₀.choose_spec⟩
    have hv₀pos : 0 < degree H v₀ := by
      rw [degree]
      exact Finset.card_pos.mpr ⟨e₀, he₀mem⟩
    exact lt_of_lt_of_le hv₀pos (hdeg v₀)
  by_contra hbound
  push_neg at hbound
  have hDsmall : 4 * r * D < 2 ^ (r - 1) := hbound vmax
  let E := {e // e ∈ H}
  let A : E → Finset (V → Fin 2) := fun e ↦ monoEvent e.1
  let N : E → Finset E := fun e ↦ dependencyNeighbors H e
  let d := r * D
  have hd : 0 < d := Nat.mul_pos (by omega) hDpos
  have hN : ∀ e : E, (N e).card ≤ d := by
    intro e
    exact dependencyNeighbors_card_le H e r D hunif hdeg
  have hnum : 4 * d ≤ 2 ^ (r - 1) := by
    exact (show 4 * (r * D) ≤ 2 ^ (r - 1) by
      rw [← mul_assoc]
      exact hDsmall.le)
  have hfar : ∀ (i : E) (S : Finset E), i ∉ S →
      (∀ j ∈ S, j ∉ N i) →
      4 * d * (A i ∩ avoid A S).card ≤ (avoid A S).card := by
    intro i S hiS hnonneighbor
    apply monoEvent_inter_avoid_card_bound (edge := fun e : E ↦ e.1)
        (i := i) (S := S) (r := r) (d := d) (by omega) (hunif i.1 i.2)
    · intro j hjS
      have hjne : j ≠ i := fun h ↦ hiS (h ▸ hjS)
      have hjnot := hnonneighbor j hjS
      change j ∉ dependencyNeighbors H i at hjnot
      simp only [dependencyNeighbors, Finset.mem_filter, Finset.mem_univ,
        true_and, not_and, not_not] at hjnot
      exact hjnot hjne
    · exact hnum
  have havoid : (avoid A Finset.univ).Nonempty :=
    finite_symmetric_local_lemma A N d hd hN hfar
  obtain ⟨c, hc⟩ := havoid
  apply hnot2
  refine ⟨c, ?_⟩
  intro e heH hmono
  let i : E := ⟨e, heH⟩
  have hcavoid := (mem_avoid.mp hc) i (Finset.mem_univ i)
  exact hcavoid (mem_monoEvent.mpr hmono)

/-- The established rational/real formulation of the degree bound. -/
theorem erdos_lovasz_degree_bound_real
    (H : Hypergraph V) (r : ℕ) (hr : 2 ≤ r)
    (hunif : IsUniform H r) (hnot2 : ¬Colorable H 2) :
    ∃ v : V, (2 : ℝ) ^ (r - 1) / (4 * r) ≤ degree H v := by
  obtain ⟨v, hv⟩ := erdos_lovasz_degree_bound H r hr hunif hnot2
  refine ⟨v, ?_⟩
  have hden : (0 : ℝ) < 4 * r := by positivity
  rw [div_le_iff₀ hden]
  rw [mul_comm]
  exact_mod_cast hv

/-- Problem 833's degree conclusion for a hypergraph of chromatic number three. -/
theorem erdos_833_degree_bound
    (H : Hypergraph V) (r : ℕ) (hr : 2 ≤ r)
    (hunif : IsUniform H r) (hχ : HasChromaticNumber H 3) :
    ∃ v : V, (2 : ℝ) ^ (r - 1) / (4 * r) ≤ degree H v := by
  apply erdos_lovasz_degree_bound_real H r hr hunif
  exact hχ.2 2 (by omega)

lemma two_le_degree_of_two_edges (H : Hypergraph V) {e f : Finset V} {v : V}
    (he : e ∈ H) (hf : f ∈ H) (hef : e ≠ f) (hve : v ∈ e) (hvf : v ∈ f) :
    2 ≤ degree H v := by
  rw [degree]
  have hsub : {e, f} ⊆ H.filter fun g ↦ v ∈ g := by
    intro g hg
    simp only [Finset.mem_insert, Finset.mem_singleton] at hg
    rcases hg with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨he, hve⟩
    · exact Finset.mem_filter.mpr ⟨hf, hvf⟩
  have hcard := Finset.card_le_card hsub
  simpa [hef] using hcard

/-- Even before the exponential estimate becomes nontrivial, non-two-colorability
forces a vertex to lie in two different edges. -/
theorem exists_degree_two_of_not_colorable
    (H : Hypergraph V) (r : ℕ) (hr : 2 ≤ r)
    (hunif : IsUniform H r) (hnot2 : ¬Colorable H 2) :
    ∃ v : V, 2 ≤ degree H v := by
  classical
  by_contra hdegree
  push Not at hdegree
  have hdeg_one : ∀ v, degree H v ≤ 1 := by
    intro v
    have := hdegree v
    omega
  have hH : H.Nonempty := by
    by_contra h
    exact hnot2 (colorable_of_empty H (Finset.not_nonempty_iff_eq_empty.mp h))
  let E := {e // e ∈ H}
  have hedge : ∀ e : E, e.1.Nonempty := by
    intro e
    apply Finset.card_pos.mp
    rw [hunif e.1 e.2]
    omega
  let pick : E → V := fun e ↦ (hedge e).choose
  have hpick : ∀ e : E, pick e ∈ e.1 := fun e ↦ (hedge e).choose_spec
  let c : V → Fin 2 := fun v ↦ if ∃ e : E, pick e = v then 1 else 0
  apply hnot2
  refine ⟨c, ?_⟩
  intro e heH hmono
  let ie : E := ⟨e, heH⟩
  let x : V := pick ie
  have hxe : x ∈ e := hpick ie
  have herase : (e.erase x).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem hxe, hunif e heH]
    omega
  let y : V := herase.choose
  have hyerase : y ∈ e.erase x := herase.choose_spec
  have hye : y ∈ e := Finset.mem_of_mem_erase hyerase
  have hyx : y ≠ x := Finset.ne_of_mem_erase hyerase
  have hcx : c x = 1 := by
    simp [c, x]
  have hcy : c y = 0 := by
    by_cases hex : ∃ je : E, pick je = y
    · exfalso
      obtain ⟨je, hpy⟩ := hex
      by_cases hji : je = ie
      · subst je
        exact hyx hpy.symm
      · have htwo : 2 ≤ degree H y :=
          two_le_degree_of_two_edges H je.2 ie.2
            (fun h ↦ hji (Subtype.ext h)) (hpy ▸ hpick je) hye
        have hless := hdegree y
        omega
    · simp [c, hex]
  have hxy := hmono x hxe y hye
  rw [hcx, hcy] at hxy
  exact Fin.zero_ne_one hxy.symm

lemma ten_ninth_pow_le_two {r : ℕ} (hr : r ≤ 6) :
    ((10 : ℝ) / 9) ^ r ≤ 2 := by
  interval_cases r <;> norm_num

lemma erdos_bound_ratio_step (n : ℕ) (hn : 7 ≤ n) :
    ((2 : ℝ) ^ (n - 1) / (4 * (n : ℝ))) * ((10 : ℝ) / 9) ≤
      (2 : ℝ) ^ n / (4 * ((n + 1 : ℕ) : ℝ)) := by
  have hpow : (2 : ℝ) ^ n = 2 * (2 : ℝ) ^ (n - 1) := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega]
    rw [pow_succ]
    ring
  rw [hpow]
  have hnR : (7 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : (0 : ℝ) < 2 ^ (n - 1) := by positivity
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hn10 : (n : ℝ) + 1 ≠ 0 := by positivity
  rw [Nat.cast_add, Nat.cast_one]
  field_simp
  nlinarith

lemma ten_ninth_pow_le_erdos_bound {r : ℕ} (hr : 7 ≤ r) :
    ((10 : ℝ) / 9) ^ r ≤ (2 : ℝ) ^ (r - 1) / (4 * r) := by
  induction r, hr using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      rw [pow_succ]
      calc
        ((10 : ℝ) / 9) ^ n * ((10 : ℝ) / 9)
            ≤ ((2 : ℝ) ^ (n - 1) / (4 * n)) * ((10 : ℝ) / 9) := by
              exact mul_le_mul_of_nonneg_right ih (by norm_num)
        _ ≤ (2 : ℝ) ^ n / (4 * ((n + 1 : ℕ) : ℝ)) := erdos_bound_ratio_step n hn
        _ = (2 : ℝ) ^ (n + 1 - 1) / (4 * ((n + 1 : ℕ) : ℝ)) := by norm_num

/--
**Erdős Problem 833.**  The answer is positive.  The same absolute constant
`c = 1/9` works for every finite vertex type, every `r ≥ 2`, and every
`r`-uniform hypergraph of chromatic number three.
-/
theorem erdos_833 :
    ∃ c : ℝ, 0 < c ∧
      ∀ (W : Type u) [Fintype W] [DecidableEq W]
        (r : ℕ), 2 ≤ r → ∀ H : Hypergraph W,
          IsUniform H r → HasChromaticNumber H 3 →
            ∃ v : W, (1 + c) ^ r ≤ degree H v := by
  refine ⟨(1 : ℝ) / 9, by norm_num, ?_⟩
  intro W _ _ r hr H hunif hχ
  have hnot2 : ¬Colorable H 2 := hχ.2 2 (by omega)
  by_cases hsmall : r ≤ 6
  · obtain ⟨v, hv⟩ := exists_degree_two_of_not_colorable H r hr hunif hnot2
    refine ⟨v, ?_⟩
    calc
      (1 + (1 : ℝ) / 9) ^ r = ((10 : ℝ) / 9) ^ r := by congr 1 <;> norm_num
      _ ≤ 2 := ten_ninth_pow_le_two hsmall
      _ ≤ degree H v := by exact_mod_cast hv
  · have hlarge : 7 ≤ r := by omega
    obtain ⟨v, hv⟩ := erdos_lovasz_degree_bound_real H r hr hunif hnot2
    refine ⟨v, ?_⟩
    calc
      (1 + (1 : ℝ) / 9) ^ r = ((10 : ℝ) / 9) ^ r := by congr 1 <;> norm_num
      _ ≤ (2 : ℝ) ^ (r - 1) / (4 * r) := ten_ninth_pow_le_erdos_bound hlarge
      _ ≤ degree H v := hv

#print axioms erdos_833_degree_bound
#print axioms erdos_833

end Hypergraphs

end Erdos833
