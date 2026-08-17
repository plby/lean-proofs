/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos110.GraphLemmas

/-!
# The Lambie--Hanson graph

Vertices are natural-valued histories indexed by the stationary height set.
For each upper vertex and label there is at most one chosen lower restriction.
Eligibility records all finite Specker block conditions through the label.
-/

noncomputable section

open Cardinal Set

namespace Erdos110
namespace Construction

open Height Blocks

variable (C : (a : Height.S) → Ordinal.Club a.1)
variable (q : ℕ → ℕ)

/-- A tagged natural-valued history. -/
structure Vertex : Type 1 where
  height : Height.S
  value : (a : Height.S) → a.1 < height.1 → ℕ

@[ext] theorem Vertex.ext {x y : Vertex}
    (hh : x.height = y.height)
    (hv : ∀ a ha hb, x.value a ha = y.value a hb) : x = y := by
  cases x with
  | mk xh xv =>
    cases y with
    | mk yh yv =>
      dsimp at hh
      subst yh
      congr
      funext a ha
      exact hv a ha ha

/-- Restriction of a history to a smaller stationary height. -/
def restrict (v : Vertex) (a : Height.S) (ha : a.1 < v.height.1) :
    Vertex where
  height := a
  value b hb := v.value b (hb.trans ha)

@[simp] theorem restrict_height (v : Vertex) (a : Height.S)
    (ha : a.1 < v.height.1) : (restrict v a ha).height = a := rfl

/-- An eligible lower height for one labeled edge entering `v`. -/
structure Candidate (v : Vertex) (k : ℕ) : Type 1 where
  lower : Height.S
  lower_lt : lower.1 < v.height.1
  label_eq : v.value lower lower_lt = k
  compatible : CompatibleThrough C q lower v.height k

/-- The uniquely selected incoming lower vertex for label `k`, if one exists. -/
def chosen (v : Vertex) (k : ℕ) : Option Vertex := by
  classical
  exact if h : Nonempty (Candidate C q v k) then
    some (restrict v h.some.lower h.some.lower_lt)
  else none

theorem chosen_spec {v x : Vertex} {k : ℕ}
    (h : chosen C q v k = some x) :
    ∃ e : Candidate C q v k,
      x = restrict v e.lower e.lower_lt := by
  rw [chosen] at h
  split at h
  next he =>
    refine ⟨he.some, ?_⟩
    exact Option.some.inj h |>.symm
  next he => simp at h

theorem chosen_exists (v : Vertex) (k : ℕ)
    (e : Candidate C q v k) :
    ∃ x : Vertex, chosen C q v k = some x := by
  rw [chosen, dif_pos ⟨e⟩]
  exact ⟨_, rfl⟩

theorem chosen_lower {v x : Vertex} {k : ℕ}
    (h : chosen C q v k = some x) : x.height.1 < v.height.1 := by
  obtain ⟨e, rfl⟩ := chosen_spec C q h
  exact e.lower_lt

theorem chosen_compatible {v x : Vertex} {k : ℕ}
    (h : chosen C q v k = some x) :
    CompatibleThrough C q x.height v.height k := by
  obtain ⟨e, rfl⟩ := chosen_spec C q h
  exact e.compatible

theorem chosen_label {v x : Vertex} {k : ℕ}
    (h : chosen C q v k = some x) :
    v.value x.height (chosen_lower C q h) = k := by
  obtain ⟨e, rfl⟩ := chosen_spec C q h
  exact e.label_eq

/-- An oriented label-`k` edge, from the selected lower restriction to its
upper history. -/
def Directed (k : ℕ) (x y : Vertex) : Prop :=
  chosen C q y k = some x

/-- The Lambie--Hanson graph. -/
def graph : SimpleGraph Vertex :=
  SimpleGraph.fromRel fun x y ↦ ∃ k, Directed C q k x y

theorem adj_iff {x y : Vertex} :
    (graph C q).Adj x y ↔
      x ≠ y ∧ ∃ k, Directed C q k x y ∨ Directed C q k y x := by
  rw [graph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, h | h⟩
    · obtain ⟨k, hk⟩ := h
      exact ⟨hne, k, Or.inl hk⟩
    · obtain ⟨k, hk⟩ := h
      exact ⟨hne, k, Or.inr hk⟩
  · rintro ⟨hne, k, hk | hk⟩
    · exact ⟨hne, Or.inl ⟨k, hk⟩⟩
    · exact ⟨hne, Or.inr ⟨k, hk⟩⟩

theorem adj_has_label {x y : Vertex} (h : (graph C q).Adj x y) :
    ∃ k, Directed C q k x y ∨ Directed C q k y x :=
  (adj_iff C q).1 h |>.2

private theorem vertexHeight_wf :
    WellFounded (fun x y : Vertex ↦ x.height.1 < y.height.1) := by
  exact Ordinal.lt_wf.onFun

private def layerStep (k : ℕ) (v : Vertex)
    (rec : ∀ w : Vertex, w.height.1 < v.height.1 → Bool) : Bool := by
  classical
  exact if h : ∃ w, chosen C q v k = some w then
    !(rec h.choose (chosen_lower C q h.choose_spec))
  else false

/-- The canonical two-coloring of one label layer, defined recursively by
toggling the color of its unique selected parent. -/
def layerColor (k : ℕ) : Vertex → Bool :=
  vertexHeight_wf.fix (fun v rec ↦ layerStep C q k v rec)

theorem layerColor_eq (k : ℕ) (v : Vertex) :
    layerColor C q k v =
      layerStep C q k v (fun w _ ↦ layerColor C q k w) := by
  rw [layerColor, WellFounded.fix_eq]

theorem layerColor_ne {k : ℕ} {x y : Vertex}
    (h : Directed C q k x y) : layerColor C q k x ≠ layerColor C q k y := by
  have h' : chosen C q y k = some x := h
  let hex : ∃ w, chosen C q y k = some w := ⟨x, h'⟩
  rw [layerColor_eq C q k y, layerStep, dif_pos hex]
  have hchoose : hex.choose = x := by
    exact Option.some.inj (hex.choose_spec.symm.trans h')
  change layerColor C q k x ≠ !layerColor C q k hex.choose
  rw [hchoose]
  simp

private theorem succ_lt_omegaOne (o : Ordinal.{0})
    (ho : o < Ordinal.omega.{0} 1) :
    Order.succ o < Ordinal.omega.{0} 1 := by
  rw [Cardinal.lt_omega_iff_card_lt]
  change (o + 1).card < Cardinal.aleph 1
  rw [Ordinal.card_add_one]
  have hocard : o.card ≤ Cardinal.aleph 0 := by
    simpa only [Cardinal.aleph_zero] using
      Cardinal.lt_aleph_one_iff.mp (Cardinal.lt_omega_iff_card_lt.mp ho)
  exact lt_of_le_of_lt
    (Cardinal.add_le_aleph0.2 ⟨by simpa only [Cardinal.aleph_zero] using hocard, by simp⟩)
    Cardinal.aleph0_lt_aleph_one

private theorem countableSuccSup_lt_omegaOne
    (f : ℕ → Set.Iio (Ordinal.omega.{0} 1)) :
    (⨆ k, Order.succ (f k).1) < Ordinal.omega.{0} 1 := by
  apply Ordinal.iSup_lt_ord_lift'
    (ι := ℕ) (f := fun k ↦ Order.succ (f k).1)
  · rw [Cardinal.mk_nat]
    rw [← Cardinal.ord_aleph, Cardinal.isRegular_aleph_one.cof_ord]
    simpa only [Cardinal.lift_id] using
      Cardinal.aleph0_lt_aleph_one
  · exact fun k ↦ succ_lt_omegaOne (f k).1 (f k).2

private def freshColor (f : ℕ → Set.Iio (Ordinal.omega.{0} 1)) :
    Set.Iio (Ordinal.omega.{0} 1) :=
  ⟨⨆ k, Order.succ (f k).1, countableSuccSup_lt_omegaOne f⟩

private theorem lt_freshColor
    (f : ℕ → Set.Iio (Ordinal.omega.{0} 1)) (k : ℕ) :
    (f k).1 < (freshColor f).1 := by
  have hb : BddAbove (Set.range fun k ↦ Order.succ (f k).1) :=
    ⟨Ordinal.omega 1, by
      rintro _ ⟨k, rfl⟩
      exact (succ_lt_omegaOne (f k).1 (f k).2).le⟩
  exact (Order.lt_succ _).trans_le
    (le_ciSup (f := fun k ↦ Order.succ (f k).1) hb k)

private def omegaStep (v : Vertex)
    (rec : ∀ w : Vertex, w.height.1 < v.height.1 →
      Set.Iio (Ordinal.omega.{0} 1)) : Set.Iio (Ordinal.omega.{0} 1) := by
  classical
  let lowerColor : ℕ → Set.Iio (Ordinal.omega.{0} 1) := fun k ↦
    if h : ∃ w, chosen C q v k = some w then
      rec h.choose (chosen_lower C q h.choose_spec)
    else ⟨0, Ordinal.omega_pos 1⟩
  exact freshColor lowerColor

/-- A proper `ω₁`-coloring, obtained by avoiding the countably many selected
lower-neighbor colors at every height. -/
def omegaColor : Vertex → Set.Iio (Ordinal.omega.{0} 1) :=
  vertexHeight_wf.fix (fun v rec ↦ omegaStep C q v rec)

theorem omegaColor_eq (v : Vertex) :
    omegaColor C q v = omegaStep C q v (fun w _ ↦ omegaColor C q w) := by
  rw [omegaColor, WellFounded.fix_eq]

theorem omegaColor_lt_of_directed {k : ℕ} {x y : Vertex}
    (h : Directed C q k x y) :
    (omegaColor C q x).1 < (omegaColor C q y).1 := by
  classical
  have h' : chosen C q y k = some x := h
  let hex : ∃ w, chosen C q y k = some w := ⟨x, h'⟩
  have hchoose : hex.choose = x :=
    Option.some.inj (hex.choose_spec.symm.trans h')
  rw [omegaColor_eq C q y]
  change (omegaColor C q x).1 <
    (freshColor (fun j ↦ if hj : ∃ w, chosen C q y j = some w then
      omegaColor C q hj.choose else ⟨0, Ordinal.omega_pos 1⟩)).1
  have hlt := lt_freshColor
    (fun j ↦ if hj : ∃ w, chosen C q y j = some w then
      omegaColor C q hj.choose else ⟨0, Ordinal.omega_pos 1⟩) k
  simp only [dif_pos hex] at hlt
  simpa only [hchoose] using hlt

theorem has_omegaOne_coloring :
    Nonempty ((graph C q).Coloring (Set.Iio (Ordinal.omega.{0} 1))) := by
  refine ⟨SimpleGraph.Coloring.mk (fun v ↦ omegaColor C q v) ?_⟩
  intro x y hxy
  obtain ⟨k, hk | hk⟩ := adj_has_label C q hxy
  · intro heq
    exact (omegaColor_lt_of_directed C q hk).ne
      (congrArg Subtype.val heq)
  · intro heq
    exact (omegaColor_lt_of_directed C q hk).ne
      (congrArg Subtype.val heq.symm)

private theorem heightS_wf :
    WellFounded (fun a b : Height.S ↦ a.1 < b.1) := by
  exact Ordinal.lt_wf.onFun

private def historyVertex (a : Height.S)
    (rec : ∀ b : Height.S, b.1 < a.1 → ℕ) : Vertex where
  height := a
  value := rec

/-- The diagonal history induced by a hypothetical countable coloring. -/
def diagonal (c : (graph C q).Coloring ℕ) : Height.S → ℕ :=
  heightS_wf.fix fun a rec ↦ c (historyVertex a rec)

theorem diagonal_eq (c : (graph C q).Coloring ℕ) (a : Height.S) :
    diagonal C q c a = c (historyVertex a
      (fun b _ ↦ diagonal C q c b)) := by
  rw [diagonal, WellFounded.fix_eq]

/-- The fully assembled history at height `a` for a diagonal function. -/
def diagonalVertex (c : (graph C q).Coloring ℕ) (a : Height.S) :
    Vertex := historyVertex a (fun b _ ↦ diagonal C q c b)

@[simp] theorem diagonalVertex_height
    (c : (graph C q).Coloring ℕ) (a : Height.S) :
    (diagonalVertex C q c a).height = a := rfl

theorem diagonal_color (c : (graph C q).Coloring ℕ) (a : Height.S) :
    c (diagonalVertex C q c a) = diagonal C q c a := by
  exact (diagonal_eq C q c a).symm

theorem restrict_diagonalVertex (c : (graph C q).Coloring ℕ)
    {a b : Height.S} (hab : a.1 < b.1) :
    restrict (diagonalVertex C q c b) a hab = diagonalVertex C q c a := by
  apply Vertex.ext rfl
  intro d hd₁ hd₂
  rfl

/-- Club guessing and simultaneous block realization contradict every
countable proper coloring of the construction. -/
theorem no_nat_coloring
    (hC : Ordinal.IsClubGuessing C Height.lambda.ord) :
    IsEmpty ((graph C q).Coloring ℕ) := by
  refine ⟨fun c ↦ ?_⟩
  obtain ⟨k, hk⟩ := Height.exists_guessing_color C hC (diagonal C q c)
  let P : Height.S → Prop := fun a ↦ diagonal C q c a = k
  have hguess : ∀ D : Ordinal.Club Height.lambda.ord,
      ∃ a : Height.S, P a ∧ (C a).carrier ⊆ D.carrier := by
    intro D
    obtain ⟨a, ha, hsub⟩ := hk D
    exact ⟨a, ha, hsub⟩
  obtain ⟨a, b, hPa, hPb, hab, hcompat⟩ :=
    Blocks.realizeBlocks C q P hguess k
  let y := diagonalVertex C q c b
  let e : Candidate C q y k :=
    ⟨a, hab, (show diagonal C q c a = k from hPa), hcompat⟩
  obtain ⟨x, hx⟩ := chosen_exists C q y k e
  have hadj : (graph C q).Adj x y := by
    rw [adj_iff C q]
    refine ⟨?_, k, Or.inl hx⟩
    intro hxy
    exact (chosen_lower C q hx).ne (congrArg (fun v : Vertex ↦ v.height.1) hxy)
  have hxform := chosen_spec C q hx
  obtain ⟨e', rfl⟩ := hxform
  have hrestrict : restrict y e'.lower e'.lower_lt =
      diagonalVertex C q c e'.lower := by
    exact restrict_diagonalVertex C q c e'.lower_lt
  have heP : diagonal C q c e'.lower = k := by
    simpa [y, diagonalVertex, historyVertex] using e'.label_eq
  have hcx : c (restrict y e'.lower e'.lower_lt) = k := by
    rw [hrestrict, diagonal_color C q c, heP]
  have hcy : c y = k := by
    simpa [y] using (diagonal_color C q c b).trans hPb
  exact c.valid hadj (hcx.trans hcy.symm)

end Construction
end Erdos110
