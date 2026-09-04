-- Modified for this repository: Lean 4.33.0 port and Erdos1177 namespace.
import ErdosProblems.Erdos1177.External
import ErdosProblems.Erdos1177.E3Facts

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# E3 (Erdős–Galvin–Hajnal): property `P` for a Specker-type graph

This file discharges the literature input `E3_EGH_P`: for every infinite
cardinal `ρ`, there is a graph `S` on `ρ` vertices with an edge labelling by a
set of size `ρ` satisfying the simultaneous common-colour property `P` at
`δ(ρ) = min{δ : ρ^δ > ρ}`.

Instead of the literal generalized Specker graph `GS₂(ρ)` (which is engineered
to be triangle-free), we build the *universal level graph* of Erdős–Galvin–Hajnal
Theorem 8.1, which is what actually delivers property `P`.  Because we only need
`P` (not the stronger `P*`, and not triangle-freeness), no set-mapping free-set
theorem (Máté's lemma) is needed: the construction realizes *every* small
labelled down-neighbourhood, and the proof of `P` is a direct counting argument.

## Construction

Levels are indexed by `Lv = (δ.ord).ToType` (order type `δ.ord`, cardinality
`δ`).  Vertices are `Vx = Lv × ρ.out` (cardinality `δ·ρ = ρ`), with `lvl = fst`.
A *type at level `ξ`* is a labelled down-neighbourhood: a map
`t : Vx → Option ρ.out` supported strictly below `ξ` with support of size `< δ`.
There are at most `ρ` types at each level, so each level (size `ρ`) can realize
every type `ρ` times.  We fix such a realization `typeOf`, and set
`Adj u w ↔ (typeOf u w).isSome ∨ (typeOf w u).isSome` with the label read off the
higher endpoint.
-/

open Cardinal Ordinal Classical

namespace Erdos1177
namespace E3

noncomputable section

variable (ρ : Cardinal.{u})

/-- Levels, of order type `δ(ρ).ord` and cardinality `δ(ρ)`. -/
abbrev Lv : Type u := (deltaRho ρ).ord.ToType

/-- Vertices: a level together with a `ρ`-indexed copy. -/
abbrev Vx : Type u := Lv ρ × ρ.out

/-- The level of a vertex. -/
def lvl : Vx ρ → Lv ρ := Prod.fst

/-- `t` is a *type at level `ξ`*: a labelled down-neighbourhood supported strictly
below `ξ`, with support of cardinality `< δ(ρ)`. -/
def IsTypeAt (ξ : Lv ρ) (t : Vx ρ → Option ρ.out) : Prop :=
  (∀ w, (t w).isSome → lvl ρ w < ξ) ∧ #({w | (t w).isSome}) < deltaRho ρ

/-- The type of valid labelled down-neighbourhoods at level `ξ`. -/
def Types (ξ : Lv ρ) : Type u := {t : Vx ρ → Option ρ.out // IsTypeAt ρ ξ t}

/-! ### Basic cardinalities -/

theorem mk_Lv : #(Lv ρ) = deltaRho ρ := by
  rw [Lv, Cardinal.mk_toType, Cardinal.card_ord]

theorem mk_level (ξ : Lv ρ) : #({x : Vx ρ // lvl ρ x = ξ}) = ρ := by
  have e : {x : Vx ρ // lvl ρ x = ξ} ≃ ρ.out := by
    refine ⟨fun x => x.1.2, fun r => ⟨(ξ, r), rfl⟩, ?_, ?_⟩
    · rintro ⟨⟨a, b⟩, h⟩; simp only [lvl] at h; subst h; rfl
    · intro r; rfl
  rw [Cardinal.mk_congr e, Cardinal.mk_out]

theorem mk_Vx (hρ : ℵ₀ ≤ ρ) : #(Vx ρ) = ρ := by
  rw [Vx, Cardinal.mk_prod, Cardinal.mk_out, Cardinal.lift_id, Cardinal.lift_id, mk_Lv]
  exact Cardinal.mul_eq_right hρ (deltaRho_le hρ)
    ((lt_of_lt_of_le Cardinal.aleph0_pos (aleph0_le_deltaRho hρ)).ne')

theorem mk_below_le (hρ : ℵ₀ ≤ ρ) (ξ : Lv ρ) :
    #({w : Vx ρ // lvl ρ w < ξ}) ≤ ρ :=
  le_trans (Cardinal.mk_subtype_le _) (le_of_eq (mk_Vx ρ hρ))

/-- The number of subsets of a set of size `≤ ρ` that have cardinality `< δ(ρ)`
is at most `ρ`. -/
theorem mk_small_subsets_le (hρ : ℵ₀ ≤ ρ) {α : Type u} (hα : #α ≤ ρ) :
    #({S : Set α | #S < deltaRho ρ}) ≤ ρ := by
  have hwo : IsWellOrder (deltaRho ρ).ord.ToType (· < ·) := inferInstance
  set δ := deltaRho ρ with hδ
  set f : δ.ord.ToType → Set (Set α) :=
    fun o => {S : Set α | #S ≤ ((Ordinal.typein (r := (· < ·)) ).toRelEmbedding o).card} with hf
  have hcover : {S : Set α | #S < δ} ⊆ ⋃ (o : δ.ord.ToType), f o := by
    intro S hS
    simp only [Set.mem_setOf_eq] at hS
    rw [Set.mem_iUnion]
    have hlt' : (#S).ord < Ordinal.type (α := δ.ord.ToType) (· < ·) := by
      rw [Ordinal.type_toType]; exact (Cardinal.ord_lt_ord).mpr hS
    refine ⟨Ordinal.enum (· < ·) ⟨(#S).ord, hlt'⟩, ?_⟩
    rw [hf]; simp only [Set.mem_setOf_eq]
    rw [Ordinal.typein_enum, Cardinal.card_ord]
  have hterm : ∀ o : δ.ord.ToType, #(f o) ≤ ρ := by
    intro o
    have hc : ((Ordinal.typein (r := (· < ·)) ).toRelEmbedding o).card < δ :=
      Cardinal.lt_ord.mp (Ordinal.typein_lt_self (o := δ.ord) o)
    calc #(f o) ≤ max #α ℵ₀ ^ ((Ordinal.typein (r := (· < ·)) ).toRelEmbedding o).card :=
          Cardinal.mk_bounded_set_le α _
      _ ≤ ρ ^ ((Ordinal.typein (r := (· < ·)) ).toRelEmbedding o).card :=
          Cardinal.power_le_power_right (max_le hα hρ)
      _ ≤ ρ := deltaRho_pow_le hc
  calc #({S : Set α | #S < δ}) ≤ #(⋃ (o : δ.ord.ToType), f o) :=
        Cardinal.mk_le_mk_of_subset hcover
    _ ≤ Cardinal.sum (fun o => #(f o)) := Cardinal.mk_iUnion_le_sum_mk
    _ ≤ Cardinal.sum (fun _ : δ.ord.ToType => ρ) := Cardinal.sum_le_sum _ _ hterm
    _ = #(δ.ord.ToType) * ρ := by rw [Cardinal.sum_const, Cardinal.lift_id, Cardinal.lift_id]
    _ = δ * ρ := by rw [Cardinal.mk_toType, Cardinal.card_ord]
    _ = ρ := Cardinal.mul_eq_right hρ (deltaRho_le hρ)
              ((lt_of_lt_of_le Cardinal.aleph0_pos (aleph0_le_deltaRho hρ)).ne')

theorem types_card_le (hρ : ℵ₀ ≤ ρ) (ξ : Lv ρ) : #(Types ρ ξ) ≤ ρ := by
  classical
  set δ := deltaRho ρ with hδ
  set W : Set (Vx ρ) := {w | lvl ρ w < ξ} with hW
  set Idx := {S : Set (Vx ρ) // #S < δ ∧ S ⊆ W} with hIdx
  have hsurj : Function.Surjective
      (fun p : (Σ S : Idx, (↥S.1 → ρ.out)) =>
        (⟨fun w => if h : w ∈ p.1.1 then some (p.2 ⟨w, h⟩) else none, by
            refine ⟨?_, ?_⟩
            · intro w hw
              by_cases h : w ∈ p.1.1
              · exact p.1.2.2 h
              · simp [h] at hw
            · apply lt_of_le_of_lt _ p.1.2.1
              apply Cardinal.mk_le_mk_of_subset
              intro w hw
              by_cases h : w ∈ p.1.1
              · exact h
              · simp [h] at hw⟩ : Types ρ ξ)) := by
    intro t
    refine ⟨⟨⟨{w | (t.1 w).isSome}, ⟨t.2.2, fun w hw => t.2.1 w hw⟩⟩,
      fun w => (t.1 w.1).get w.2⟩, ?_⟩
    apply Subtype.ext
    funext w
    by_cases h : (t.1 w).isSome
    · simp only [Set.mem_setOf_eq, h, dif_pos]
      exact Option.some_get h
    · simp only [Set.mem_setOf_eq, h]
      exact (Option.not_isSome_iff_eq_none.mp h).symm
  calc #(Types ρ ξ) ≤ #(Σ S : Idx, (↥S.1 → ρ.out)) := Cardinal.mk_le_of_surjective hsurj
    _ = Cardinal.sum (fun S : Idx => #(↥S.1 → ρ.out)) := Cardinal.mk_sigma _
    _ ≤ Cardinal.sum (fun _ : Idx => ρ) := by
        apply Cardinal.sum_le_sum
        intro S
        rw [Cardinal.mk_arrow, Cardinal.mk_out, Cardinal.lift_id, Cardinal.lift_id]
        exact deltaRho_pow_le S.2.1
    _ = #Idx * ρ := by rw [Cardinal.sum_const, Cardinal.lift_id, Cardinal.lift_id]
    _ ≤ ρ * ρ := by
        gcongr
        refine le_trans (Cardinal.mk_subtype_mono (fun S (h : #S < δ ∧ S ⊆ W) => h.1)) ?_
        exact mk_small_subsets_le ρ hρ (le_of_eq (mk_Vx ρ hρ))
    _ = ρ := Cardinal.mul_eq_self hρ

theorem types_nonempty (hρ : ℵ₀ ≤ ρ) (ξ : Lv ρ) : Nonempty (Types ρ ξ) :=
  ⟨⟨fun _ => none, by
    refine ⟨?_, ?_⟩
    · intro w h; simp at h
    · have : ({w | (Option.none : Option ρ.out).isSome}) = (∅ : Set (Vx ρ)) := by
        ext w; simp
      rw [this]
      simpa using! lt_of_lt_of_le Cardinal.aleph0_pos (aleph0_le_deltaRho hρ)⟩⟩

/-- Nonemptiness of `ρ.out` for infinite `ρ`. -/
theorem out_nonempty (hρ : ℵ₀ ≤ ρ) : Nonempty ρ.out := by
  rw [← Cardinal.mk_ne_zero_iff, Cardinal.mk_out]
  exact (lt_of_lt_of_le Cardinal.aleph0_pos hρ).ne'

/-! ### A fibered surjection: partition `ρ` into `#B` classes each of size `ρ`. -/

theorem fiber_partition {B : Type u} (hB1 : Nonempty B) (hB : #B ≤ ρ) (hρ : ℵ₀ ≤ ρ) :
    ∃ s : ρ.out → B, ∀ b : B, #({a : ρ.out // s a = b}) = ρ := by
  have hBne : #B ≠ 0 := by rw [Cardinal.mk_ne_zero_iff]; exact hB1
  have hmul : #(B × ρ.out) = ρ := by
    rw [Cardinal.mk_prod, Cardinal.mk_out, Cardinal.lift_id, Cardinal.lift_id]
    exact Cardinal.mul_eq_right hρ hB hBne
  obtain ⟨e⟩ : Nonempty (ρ.out ≃ B × ρ.out) := by
    rw [← Cardinal.eq, Cardinal.mk_out, hmul]
  refine ⟨fun a => (e a).1, fun b => ?_⟩
  have e2 : {a : ρ.out // (e a).1 = b} ≃ {p : B × ρ.out // p.1 = b} :=
    Equiv.subtypeEquiv e (fun a => Iff.rfl)
  rw [Cardinal.mk_congr e2]
  have e3 : {p : B × ρ.out // p.1 = b} ≃ ρ.out := by
    refine ⟨fun p => p.1.2, fun r => ⟨(b, r), rfl⟩, ?_, ?_⟩
    · rintro ⟨⟨x, y⟩, h⟩; simp only at h; subst h; rfl
    · intro r; rfl
  rw [Cardinal.mk_congr e3, Cardinal.mk_out]

/-! ### The realization function -/

/-- For each level, a fixed surjection from the level's copies onto the types,
with every fiber of size `ρ`. -/
def chosenSurj (hρ : ℵ₀ ≤ ρ) (ξ : Lv ρ) : ρ.out → Types ρ ξ :=
  Classical.choose (fiber_partition ρ (types_nonempty ρ hρ ξ) (types_card_le ρ hρ ξ) hρ)

theorem chosenSurj_fiber (hρ : ℵ₀ ≤ ρ) (ξ : Lv ρ) (t : Types ρ ξ) :
    #({r : ρ.out // chosenSurj ρ hρ ξ r = t}) = ρ :=
  Classical.choose_spec (fiber_partition ρ (types_nonempty ρ hρ ξ) (types_card_le ρ hρ ξ) hρ) t

/-- Each vertex's labelled down-neighbourhood. -/
def typeOf (hρ : ℵ₀ ≤ ρ) (v : Vx ρ) : Vx ρ → Option ρ.out :=
  (chosenSurj ρ hρ (lvl ρ v) v.2).1

theorem typeOf_supp (hρ : ℵ₀ ≤ ρ) (v w : Vx ρ) (h : (typeOf ρ hρ v w).isSome) :
    lvl ρ w < lvl ρ v :=
  (chosenSurj ρ hρ (lvl ρ v) v.2).2.1 w h

theorem not_both_some (hρ : ℵ₀ ≤ ρ) (u w : Vx ρ) :
    ¬ ((typeOf ρ hρ u w).isSome ∧ (typeOf ρ hρ w u).isSome) := by
  rintro ⟨h1, h2⟩
  exact absurd (typeOf_supp ρ hρ u w h1) (not_lt.mpr (le_of_lt (typeOf_supp ρ hρ w u h2)))

/-- Realization: every type at level `ξ` is realized by exactly `ρ` vertices. -/
theorem realize (hρ : ℵ₀ ≤ ρ) (ξ : Lv ρ) (t : Types ρ ξ) :
    #({x : Vx ρ // lvl ρ x = ξ ∧ ∀ w, typeOf ρ hρ x w = t.1 w}) = ρ := by
  refine Eq.trans (Cardinal.mk_congr ?_) (chosenSurj_fiber ρ hρ ξ t)
  refine ⟨fun x => ⟨x.1.2, ?_⟩, fun r => ⟨(ξ, r.1), rfl, ?_⟩, ?_, ?_⟩
  · obtain ⟨⟨a, b⟩, hlv, hfun⟩ := x
    simp only [lvl] at hlv; subst hlv
    apply Subtype.ext; funext w; exact hfun w
  · obtain ⟨b, hb⟩ := r
    intro w
    show typeOf ρ hρ (ξ, b) w = t.1 w
    have h1 : typeOf ρ hρ (ξ, b) = (chosenSurj ρ hρ ξ b).1 := rfl
    rw [h1, hb]
  · rintro ⟨⟨a, b⟩, hlv, hfun⟩
    simp only [lvl] at hlv; subst hlv; rfl
  · rintro ⟨b, hb⟩; rfl

/-! ### The graph and edge labelling -/

/-- Adjacency: an edge from `u` down to `w`, or from `w` down to `u`. -/
def Grel (hρ : ℵ₀ ≤ ρ) (u w : Vx ρ) : Prop :=
  (typeOf ρ hρ u w).isSome ∨ (typeOf ρ hρ w u).isSome

theorem Grel_symm (hρ : ℵ₀ ≤ ρ) : Symmetric (Grel ρ hρ) := by
  intro u w h; exact h.symm

theorem Grel_irrefl (hρ : ℵ₀ ≤ ρ) : ∀ v, ¬ Grel ρ hρ v v := by
  intro v h
  rcases h with h | h <;> exact (lt_irrefl _ (typeOf_supp ρ hρ v v h))

/-- The universal level graph. -/
def G (hρ : ℵ₀ ≤ ρ) : SimpleGraph (Vx ρ) :=
  { Adj := Grel ρ hρ, symm := ⟨Grel_symm ρ hρ⟩, loopless := ⟨Grel_irrefl ρ hρ⟩ }

/-- The label of an ordered pair: read off the higher endpoint. -/
def labPair (hρ : ℵ₀ ≤ ρ) (u w : Vx ρ) : ρ.out :=
  haveI : Nonempty ρ.out := out_nonempty ρ hρ
  (typeOf ρ hρ u w).getD ((typeOf ρ hρ w u).getD (Classical.arbitrary ρ.out))

theorem labPair_symm (hρ : ℵ₀ ≤ ρ) (u w : Vx ρ) :
    labPair ρ hρ u w = labPair ρ hρ w u := by
  have hnb := not_both_some ρ hρ u w
  unfold labPair
  cases hu : typeOf ρ hρ u w <;> cases hw : typeOf ρ hρ w u <;>
    simp_all [Option.isSome]

/-- The edge labelling `E(G) → ρ.out`. -/
def edgeLabel (hρ : ℵ₀ ≤ ρ) : (G ρ hρ).edgeSet → ρ.out :=
  fun e => Sym2.lift ⟨labPair ρ hρ, labPair_symm ρ hρ⟩ e.1

theorem edgeLabel_eq (hρ : ℵ₀ ≤ ρ) (x y : Vx ρ) (h : (G ρ hρ).Adj x y) :
    edgeLabel ρ hρ ⟨s(x, y), h⟩ = labPair ρ hρ x y := by
  simp [edgeLabel, Sym2.lift_mk]

theorem labPair_of_some (hρ : ℵ₀ ≤ ρ) (x y : Vx ρ) (l : ρ.out)
    (h : typeOf ρ hρ x y = some l) : labPair ρ hρ x y = l := by
  simp [labPair, h]

/-! ### Cardinal helpers used in the main proof -/

/-- A subset of `Lv ρ` of cardinality `< δ(ρ)` has a strict upper bound. -/
theorem exists_ub_Lv (hρ : ℵ₀ ≤ ρ) (S : Set (Lv ρ)) (hS : #S < deltaRho ρ) :
    ∃ ξ : Lv ρ, ∀ b ∈ S, b < ξ := by
  have hcof : (Ordinal.type (α := Lv ρ) (· < ·)).cof = deltaRho ρ := by
    rw [show (Ordinal.type (α := Lv ρ) (· < ·)) = (deltaRho ρ).ord from Ordinal.type_toType _]
    exact deltaRho_regular hρ
  by_contra! h
  have hc : deltaRho ρ ≤ #S := by
    rw [← hcof, Ordinal.cof_type]
    exact Order.cof_le h
  exact (not_le_of_gt hS) hc


/-- Union of `< cf(ρ)` sets each of cardinality `< ρ` has cardinality `< ρ`. -/
theorem small_union_lt_rho {ι α : Type u} (hρ : ℵ₀ ≤ ρ) (hι : #ι < (ρ.ord).cof)
    (t : ι → Set α) (ht : ∀ i, #(t i) < ρ) : #(⋃ i, t i) < ρ := by
  have hsup : ⨆ i, #(t i) < ρ := Ordinal.iSup_lt hι ht
  have hιρ : #ι < ρ := lt_of_lt_of_le hι (Ordinal.cof_ord_le ρ)
  calc #(⋃ i, t i) ≤ Cardinal.sum (fun i => #(t i)) := Cardinal.mk_iUnion_le_sum_mk
    _ ≤ #ι * ⨆ i, #(t i) := Cardinal.sum_le_mk_mul_iSup _
    _ < ρ := Cardinal.mul_lt_of_lt hρ hιρ hsup

/-! ### Property `P` -/

/-- The universal level graph has the Erdős–Galvin–Hajnal property `P` at `δ(ρ)`. -/
theorem propertyP (hρ : ℵ₀ ≤ ρ) :
    SimpleGraph.PropertyP (G ρ hρ) (edgeLabel ρ hρ) (deltaRho ρ) := by
  classical
  intro θ hθ c
  by_contra hcon
  push_neg at hcon
  choose q hq using hcon
  have hLvne : Nonempty (Lv ρ) := by
    have hpos : (0:Cardinal) < deltaRho ρ :=
      lt_of_lt_of_le Cardinal.aleph0_pos (aleph0_le_deltaRho hρ)
    exact Ordinal.toType_nonempty_iff_ne_zero.mpr (fun hh => hpos.ne' (Cardinal.ord_eq_zero.mp hh))
  have hρne : Nonempty ρ.out := out_nonempty ρ hρ
  set full : θ.out → Lv ρ → Prop :=
    fun a ξ => ρ ≤ #{x : Vx ρ // lvl ρ x = ξ ∧ c x = a} with hfulldef
  set isM : θ.out → Prop := fun a => #({ξ : Lv ρ | full a ξ}) < deltaRho ρ with hisMdef
  have hθδ : #(θ.out) < deltaRho ρ := by rw [Cardinal.mk_out]; exact hθ
  have hθcof : #(θ.out) < (ρ.ord).cof := lt_of_lt_of_le hθδ (deltaRho_le_cof hρ)
  have hyy : ∀ a : θ.out, ¬ isM a → ∃ w : Vx ρ, c w = a ∧ full a (lvl ρ w) := by
    intro a ha
    rw [hisMdef] at ha; simp only [not_lt] at ha
    have hFne : Nonempty {ξ : Lv ρ // ξ ∈ {ξ | full a ξ}} := by
      rw [← Cardinal.mk_ne_zero_iff]
      have h0 : (0:Cardinal) < deltaRho ρ :=
        lt_of_lt_of_le Cardinal.aleph0_pos (aleph0_le_deltaRho hρ)
      exact (lt_of_lt_of_le h0 ha).ne'
    obtain ⟨⟨ξ, hξ⟩⟩ := hFne
    simp only [Set.mem_setOf_eq] at hξ
    rw [hfulldef] at hξ
    have hxne : Nonempty {x : Vx ρ // lvl ρ x = ξ ∧ c x = a} := by
      rw [← Cardinal.mk_ne_zero_iff]
      have h0 : (0:Cardinal) < ρ := lt_of_lt_of_le Cardinal.aleph0_pos hρ
      exact (lt_of_lt_of_le h0 hξ).ne'
    obtain ⟨⟨x, hx1, hx2⟩⟩ := hxne
    exact ⟨x, hx2, by rw [hfulldef, hx1]; exact hξ⟩
  set yy : θ.out → Vx ρ := fun a =>
    if h : ¬ isM a then (hyy a h).choose else Classical.arbitrary _ with hyydef
  have hyy_spec : ∀ a, ¬ isM a → c (yy a) = a ∧ full a (lvl ρ (yy a)) := by
    intro a ha
    have he : yy a = (hyy a ha).choose := by rw [hyydef]; simp [ha]
    rw [he]; exact (hyy a ha).choose_spec
  set t : Vx ρ → Option ρ.out :=
    fun w => if (¬ isM (c w) ∧ yy (c w) = w) then some (q (c w)) else none with htdef
  have ht_some_iff : ∀ w, (t w).isSome ↔ (¬ isM (c w) ∧ yy (c w) = w) := by
    intro w; rw [htdef]; by_cases h : (¬ isM (c w) ∧ yy (c w) = w) <;> simp [h]
  have hsupp_inj : #({w : Vx ρ | (t w).isSome}) < deltaRho ρ := by
    apply lt_of_le_of_lt _ hθδ
    apply Cardinal.mk_le_of_injective (f := fun w : {w : Vx ρ // (t w).isSome} => c w.1)
    rintro ⟨w, hw⟩ ⟨w', hw'⟩ hcc
    simp only at hcc
    rw [ht_some_iff] at hw hw'
    have hww : w = w' := by rw [← hw.2, ← hw'.2, hcc]
    exact Subtype.ext hww
  set Bad : Set (Lv ρ) :=
    {ξ | (∃ a, ¬ isM a ∧ lvl ρ (yy a) = ξ) ∨ (∃ a, isM a ∧ full a ξ)} with hBaddef
  have hBadlt : #Bad < deltaRho ρ := by
    have hP1 : #({ξ : Lv ρ | ∃ a, ¬ isM a ∧ lvl ρ (yy a) = ξ}) < deltaRho ρ := by
      have hsub : {ξ : Lv ρ | ∃ a, ¬ isM a ∧ lvl ρ (yy a) = ξ} ⊆
          Set.range (fun a : θ.out => lvl ρ (yy a)) := by
        rintro ξ ⟨a, _, heq⟩; exact ⟨a, heq⟩
      exact lt_of_le_of_lt (le_trans (Cardinal.mk_le_mk_of_subset hsub)
        (le_trans Cardinal.mk_range_le (le_of_eq (Cardinal.mk_out θ)))) hθ
    have hP2 : #({ξ : Lv ρ | ∃ a, isM a ∧ full a ξ}) < deltaRho ρ := by
      have hEq : {ξ : Lv ρ | ∃ a, isM a ∧ full a ξ}
          = ⋃ (a : {a : θ.out // isM a}), {ξ | full a.1 ξ} := by
        ext ξ; simp only [Set.mem_setOf_eq, Set.mem_iUnion]
        constructor
        · rintro ⟨a, hM, hf⟩; exact ⟨⟨a, hM⟩, hf⟩
        · rintro ⟨⟨a, hM⟩, hf⟩; exact ⟨a, hM, hf⟩
      rw [hEq, card_iUnion_lt_iff_forall_of_isRegular (deltaRho_isRegular hρ)
        (lt_of_le_of_lt (Cardinal.mk_subtype_le _) hθδ)]
      rintro ⟨a, hM⟩; exact hM
    have hsub : Bad ⊆ {ξ : Lv ρ | ∃ a, ¬ isM a ∧ lvl ρ (yy a) = ξ} ∪
        {ξ : Lv ρ | ∃ a, isM a ∧ full a ξ} := by
      rw [hBaddef]; intro ξ h; rcases h with h | h
      · exact Or.inl h
      · exact Or.inr h
    exact lt_of_le_of_lt (le_trans (Cardinal.mk_le_mk_of_subset hsub) (Cardinal.mk_union_le _ _))
      (Cardinal.add_lt_of_lt (aleph0_le_deltaRho hρ) hP1 hP2)
  obtain ⟨ξstar, hξstar⟩ := exists_ub_Lv ρ hρ Bad hBadlt
  have hsupp_below : ∀ w, (t w).isSome → lvl ρ w < ξstar := by
    intro w hw
    rw [ht_some_iff] at hw
    obtain ⟨hnM, hyw⟩ := hw
    have hin : lvl ρ (yy (c w)) ∈ Bad := by rw [hBaddef]; left; exact ⟨c w, hnM, rfl⟩
    have := hξstar _ hin
    rwa [hyw] at this
  have htype : IsTypeAt ρ ξstar t := ⟨hsupp_below, hsupp_inj⟩
  have hD : #({x : Vx ρ // lvl ρ x = ξstar ∧ ∀ w, typeOf ρ hρ x w = t w}) = ρ :=
    realize ρ hρ ξstar ⟨t, htype⟩
  have hDcard : #({x : Vx ρ | lvl ρ x = ξstar ∧ ∀ w, typeOf ρ hρ x w = t w}) = ρ := hD
  have hMpart :
      #({x : Vx ρ | (lvl ρ x = ξstar ∧ ∀ w, typeOf ρ hρ x w = t w) ∧ isM (c x)}) < ρ := by
    apply lt_of_le_of_lt (Cardinal.mk_le_mk_of_subset
      (t := ⋃ (a : {a : θ.out // isM a}), {x : Vx ρ | lvl ρ x = ξstar ∧ c x = a.1}) ?_)
      (small_union_lt_rho ρ hρ ?_ _ ?_)
    · rintro x ⟨⟨hlv, _⟩, hM⟩
      rw [Set.mem_iUnion]; exact ⟨⟨c x, hM⟩, hlv, rfl⟩
    · exact lt_of_le_of_lt (Cardinal.mk_subtype_le _) hθcof
    · rintro ⟨a, hM⟩
      have hnfull : ¬ full a ξstar := by
        intro hf
        exact absurd (hξstar ξstar (by rw [hBaddef]; right; exact ⟨a, hM, hf⟩)) (lt_irrefl _)
      rw [hfulldef] at hnfull; simp only [not_le] at hnfull
      exact hnfull
  have hexists : ∃ x, (lvl ρ x = ξstar ∧ ∀ w, typeOf ρ hρ x w = t w) ∧ ¬ isM (c x) := by
    by_contra hall
    push_neg at hall
    have hsub : {x : Vx ρ | lvl ρ x = ξstar ∧ ∀ w, typeOf ρ hρ x w = t w} ⊆
        {x : Vx ρ | (lvl ρ x = ξstar ∧ ∀ w, typeOf ρ hρ x w = t w) ∧ isM (c x)} :=
      fun x hx => ⟨hx, hall x hx⟩
    have hle := Cardinal.mk_le_mk_of_subset hsub
    rw [hDcard] at hle
    exact absurd (lt_of_le_of_lt hle hMpart) (lt_irrefl _)
  obtain ⟨x, ⟨hxlv, hxtype⟩, hxnM⟩ := hexists
  have hyya' := hyy_spec (c x) hxnM
  have htval : t (yy (c x)) = some (q (c x)) := by
    have h1 : c (yy (c x)) = c x := hyya'.1
    have hbeta : t (yy (c x))
        = if (¬ isM (c (yy (c x))) ∧ yy (c (yy (c x))) = yy (c x))
          then some (q (c (yy (c x)))) else none := rfl
    rw [hbeta, if_pos ⟨by rw [h1]; exact hxnM, by rw [h1]⟩, h1]
  have htypeof : typeOf ρ hρ x (yy (c x)) = some (q (c x)) := by rw [hxtype, htval]
  have hadj : (G ρ hρ).Adj x (yy (c x)) := by
    show Grel ρ hρ x (yy (c x)); left; rw [htypeof]; rfl
  have hlabel : edgeLabel ρ hρ ⟨s(x, yy (c x)), hadj⟩ = q (c x) := by
    rw [edgeLabel_eq]; exact labPair_of_some ρ hρ x (yy (c x)) (q (c x)) htypeof
  exact hq (c x) x (yy (c x)) hadj hlabel rfl hyya'.1

end

end E3

/-- **E3** (`thm:EGH-P`) discharged: property `P` at `δ(ρ)` for a graph on `ρ`
vertices with a labelling by `ρ` labels. -/
theorem e3_EGH_P : E3_EGH_P.{u} := by
  intro ρ hρ
  refine ⟨E3.Vx ρ, E3.G ρ hρ, ρ.out, ?_, Cardinal.mk_out ρ, E3.edgeLabel ρ hρ, ?_⟩
  · exact E3.mk_Vx ρ hρ
  · exact E3.propertyP ρ hρ

end Erdos1177
