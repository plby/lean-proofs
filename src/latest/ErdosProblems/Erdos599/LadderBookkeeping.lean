/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DirectedPath
import ErdosProblems.Erdos599.Stationary

/-!
# Set-theoretic bookkeeping for Erdős Problem 599 ladders

This file gives the one-record-per-stage construction for the concrete
finite-path-or-ray families of `Core.lean`.
It proves the part of the ladder argument which is independent of roofs,
quotients, and arrow extensions:

* persistence of paths which were recorded at an earlier stage;
* existence and cardinal control of the first-emergence fibers;
* nonstationarity of hanging stages by pressing down;
* the stationary obstruction characterization used in Lemma 7.27; and
* the order-theoretic conclusion of the corrected closure Lemma 7.28.

The genuinely graph-theoretic inputs to Lemmas 7.27 and 7.28 occur as
premises of the corresponding theorems.  They say respectively that a
nonexceptional obstruction has regressive emergence, and that a path which
misses the limiting frontier is inessential at the successor-normalized
limit stage.  No graph-theoretic conclusion is postulated globally.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace LadderBookkeeping

universe u

open DirectedPath

/-- Stages of a ladder of cardinal length `κ`. -/
abbrev Stage (κ : Cardinal.{u}) := Stationary.Below κ

/-- The part of a concrete web needed by the bookkeeping layer.  Its path
type is definitionally the `DirectedPath.Path` used by `Core.DWeb`. -/
structure PathSystem (V : Type u) where
  graph : Digraph V
  source : Set V

namespace PathSystem

abbrev DPath (Γ : PathSystem V) := DirectedPath.Path Γ.graph

end PathSystem

/-- The Section 7 bookkeeping, instantiated with the actual concrete paths
of a directed path system.  `inessentialNext α` is successor-normalized: it
means the inessential paths of `Y_(α+1)`. -/
structure ConcreteBookkeeping (κ : Cardinal.{u}) {V : Type u}
    (Γ : PathSystem V) where
  /-- Paths inessential in the current warp `Y_α`. -/
  inessentialCurrent : Stage κ → Set Γ.DPath
  /-- Paths inessential in the successor warp `Y_(α+1)`. -/
  inessentialNext : Stage κ → Set Γ.DPath
  isRay : Γ.DPath → Prop
  chosen : Stage κ → Option Γ.DPath

variable {κ : Cardinal.{u}} {V : Type u} {Γ : PathSystem V}

namespace ConcreteBookkeeping

/-! ## The one-record-per-stage rule -/

/-- Paths selected at strictly earlier stages. -/
def recordedBefore (B : ConcreteBookkeeping κ Γ) (α : Stage κ) : Set Γ.DPath :=
  {p | ∃ β : Stage κ, β < α ∧ B.chosen β = some p}

/-- Previously unrecorded inessential paths available at `α`. -/
def available (B : ConcreteBookkeeping κ Γ) (α : Stage κ) : Set Γ.DPath :=
  B.inessentialNext α \ B.recordedBefore α

/-- Obstruction stages. -/
def phi (B : ConcreteBookkeeping κ Γ) : Set (Stage κ) :=
  {α | (B.available α).Nonempty}

/-- The choice rule: choose precisely at obstruction stages, from the
available set.  The graph construction may add its ray-priority condition
separately; none of the bookkeeping results below needs that priority. -/
def IsValid (B : ConcreteBookkeeping κ Γ) : Prop :=
  ∀ α,
    ((B.available α).Nonempty →
      ∃ p, B.chosen α = some p ∧ p ∈ B.available α) ∧
    ∀ p, B.chosen α = some p → p ∈ B.available α

@[simp]
theorem mem_recordedBefore {B : ConcreteBookkeeping κ Γ}
    {α : Stage κ} {p : Γ.DPath} :
    p ∈ B.recordedBefore α ↔
      ∃ β : Stage κ, β < α ∧ B.chosen β = some p :=
  Iff.rfl

@[simp]
theorem mem_available {B : ConcreteBookkeeping κ Γ}
    {α : Stage κ} {p : Γ.DPath} :
    p ∈ B.available α ↔
      p ∈ B.inessentialNext α ∧ p ∉ B.recordedBefore α :=
  Iff.rfl

@[simp]
theorem mem_phi {B : ConcreteBookkeeping κ Γ} {α : Stage κ} :
    α ∈ B.phi ↔ (B.available α).Nonempty :=
  Iff.rfl

theorem chosen_mem_available (B : ConcreteBookkeeping κ Γ) (hB : B.IsValid)
    {α : Stage κ} {p : Γ.DPath} (hp : B.chosen α = some p) :
    p ∈ B.available α :=
  (hB α).2 p hp

theorem chosen_not_mem_recordedBefore (B : ConcreteBookkeeping κ Γ)
    (hB : B.IsValid) {α : Stage κ} {p : Γ.DPath}
    (hp : B.chosen α = some p) : p ∉ B.recordedBefore α :=
  (B.chosen_mem_available hB hp).2

theorem mem_phi_iff_exists_chosen (B : ConcreteBookkeeping κ Γ)
    (hB : B.IsValid) {α : Stage κ} :
    α ∈ B.phi ↔ ∃ p, B.chosen α = some p := by
  constructor
  · intro hα
    obtain ⟨p, hp, -⟩ := (hB α).1 hα
    exact ⟨p, hp⟩
  · rintro ⟨p, hp⟩
    exact ⟨p, B.chosen_mem_available hB hp⟩

theorem chosen_stage_unique (B : ConcreteBookkeeping κ Γ) (hB : B.IsValid)
    {α β : Stage κ} {p : Γ.DPath}
    (hp : B.chosen α = some p) (hq : B.chosen β = some p) : α = β := by
  rcases lt_trichotomy α β with hlt | heq | hgt
  · exact False.elim <| B.chosen_not_mem_recordedBefore hB hq ⟨α, hlt, hp⟩
  · exact heq
  · exact False.elim <| B.chosen_not_mem_recordedBefore hB hp ⟨β, hgt, hq⟩

/-- The graph-theoretic persistence statement supplied by the arrow/liminf
construction. -/
def IsPersistent (B : ConcreteBookkeeping κ Γ) : Prop :=
  ∀ α p, B.chosen α = some p →
    ∀ β, α < β → p ∈ B.inessentialCurrent β

/-! ## Recorded paths and persistence -/

/-- A concrete path which was recorded at `α` belongs to the current
inessential family at every strictly later stage.  This is the bookkeeping
conclusion of source Lemma 7.4; the arrow/liminf proof supplies `hpers`. -/
theorem recorded_path_persists (B : ConcreteBookkeeping κ Γ)
    (hpers : B.IsPersistent) {α β : Stage κ} {p : Γ.DPath}
    (hp : B.chosen α = some p) (hαβ : α < β) :
    p ∈ B.inessentialCurrent β :=
  hpers α p hp β hαβ

/-- Every path recorded strictly before `β` is inessential at `β`. -/
theorem recordedBefore_subset (B : ConcreteBookkeeping κ Γ)
    (hpers : B.IsPersistent) (β : Stage κ) :
    B.recordedBefore β ⊆ B.inessentialCurrent β :=
  by
    rintro p ⟨α, hαβ, hp⟩
    exact hpers α p hp β hαβ

/-! ## The selected path and its first-emergence stage -/

/-- The path selected at an obstruction stage. -/
noncomputable def selectedPath (B : ConcreteBookkeeping κ Γ)
    (hB : B.IsValid) (α : B.phi) : Γ.DPath :=
  Classical.choose ((B.mem_phi_iff_exists_chosen hB).mp α.2)

@[simp]
theorem chosen_selectedPath (B : ConcreteBookkeeping κ Γ)
    (hB : B.IsValid) (α : B.phi) :
    B.chosen α.1 = some (B.selectedPath hB α) :=
  Classical.choose_spec ((B.mem_phi_iff_exists_chosen hB).mp α.2)

theorem selectedPath_mem_available (B : ConcreteBookkeeping κ Γ)
    (hB : B.IsValid) (α : B.phi) :
    B.selectedPath hB α ∈ B.available α :=
  B.chosen_mem_available hB (B.chosen_selectedPath hB α)

theorem selectedPath_mem_inessentialNext (B : ConcreteBookkeeping κ Γ)
    (hB : B.IsValid) (α : B.phi) :
    B.selectedPath hB α ∈ B.inessentialNext α :=
  (B.selectedPath_mem_available hB α).1

/-- Distinct obstruction stages select distinct paths. -/
theorem selectedPath_injective (B : ConcreteBookkeeping κ Γ)
    (hB : B.IsValid) : Function.Injective (B.selectedPath hB) := by
  intro α β hp
  apply Subtype.ext
  exact B.chosen_stage_unique hB (B.chosen_selectedPath hB α)
    (hp ▸ B.chosen_selectedPath hB β)

/-- The set of stages at which the path selected at `α` is already
inessential.  It is nonempty because it contains `α`. -/
def emergenceSet (B : ConcreteBookkeeping κ Γ) (hB : B.IsValid)
    (α : B.phi) : Set (Stage κ) :=
  {β | B.selectedPath hB α ∈ B.inessentialNext β}

theorem emergenceSet_nonempty (B : ConcreteBookkeeping κ Γ)
    (hB : B.IsValid) (α : B.phi) :
    (B.emergenceSet hB α).Nonempty :=
  ⟨α, B.selectedPath_mem_inessentialNext hB α⟩

/-- The least stage at which the selected path is inessential.  Off the
obstruction set the value is set equal to the argument; this makes a total
function suitable for Fodor's lemma without choosing a dummy path. -/
noncomputable def emergenceIndex (B : ConcreteBookkeeping κ Γ)
    (hB : B.IsValid) (α : Stage κ) : Stage κ := by
  classical
  exact if hα : α ∈ B.phi then
      wellFounded_lt.min (B.emergenceSet hB ⟨α, hα⟩)
        (B.emergenceSet_nonempty hB ⟨α, hα⟩)
    else α

theorem emergenceIndex_eq_min (B : ConcreteBookkeeping κ Γ)
    (hB : B.IsValid) {α : Stage κ} (hα : α ∈ B.phi) :
    B.emergenceIndex hB α =
      wellFounded_lt.min (B.emergenceSet hB ⟨α, hα⟩)
        (B.emergenceSet_nonempty hB ⟨α, hα⟩) := by
  simp [emergenceIndex, hα]

/-- The selected path is inessential at its emergence stage. -/
theorem selectedPath_mem_emergenceIndex (B : ConcreteBookkeeping κ Γ)
    (hB : B.IsValid) {α : Stage κ} (hα : α ∈ B.phi) :
    B.selectedPath hB ⟨α, hα⟩ ∈
      B.inessentialNext (B.emergenceIndex hB α) := by
  rw [B.emergenceIndex_eq_min hB hα]
  exact wellFounded_lt.min_mem
    (B.emergenceSet hB ⟨α, hα⟩)
    (B.emergenceSet_nonempty hB ⟨α, hα⟩)

/-- Emergence occurs no later than the stage at which the path is selected. -/
theorem emergenceIndex_le (B : ConcreteBookkeeping κ Γ)
    (hB : B.IsValid) {α : Stage κ} (hα : α ∈ B.phi) :
    B.emergenceIndex hB α ≤ α := by
  rw [B.emergenceIndex_eq_min hB hα]
  by_contra h
  exact wellFounded_lt.not_lt_min
    (B.emergenceSet hB ⟨α, hα⟩)
    (B.selectedPath_mem_inessentialNext hB ⟨α, hα⟩)
    (lt_of_not_ge h)

/-- No earlier stage contains the selected path in its inessential part. -/
theorem not_mem_inessentialNext_of_lt_emergenceIndex
    (B : ConcreteBookkeeping κ Γ) (hB : B.IsValid)
    {α β : Stage κ} (hα : α ∈ B.phi)
    (hβ : β < B.emergenceIndex hB α) :
    B.selectedPath hB ⟨α, hα⟩ ∉ B.inessentialNext β := by
  intro hp
  rw [B.emergenceIndex_eq_min hB hα] at hβ
  exact wellFounded_lt.not_lt_min (B.emergenceSet hB ⟨α, hα⟩) hp hβ

/-- The stages whose selected paths first become inessential at `i`. -/
def emergenceFiber (B : ConcreteBookkeeping κ Γ) (hB : B.IsValid)
    (i : Stage κ) : Set (Stage κ) :=
  B.phi ∩ {α | B.emergenceIndex hB α = i}

@[simp]
theorem mem_emergenceFiber (B : ConcreteBookkeeping κ Γ)
    (hB : B.IsValid) {i α : Stage κ} :
    α ∈ B.emergenceFiber hB i ↔
      α ∈ B.phi ∧ B.emergenceIndex hB α = i :=
  Iff.rfl

/-- Send a stage in the `i`-th emergence fiber to the concrete path selected
at that stage, regarded as a member of `IE(Y_(i+1))`. -/
noncomputable def emergenceFiberPath (B : ConcreteBookkeeping κ Γ)
    (hB : B.IsValid) (i : Stage κ) :
    B.emergenceFiber hB i → B.inessentialNext i :=
  fun α ↦
    ⟨B.selectedPath hB ⟨α.1, α.2.1⟩, by
      have hp := B.selectedPath_mem_emergenceIndex hB α.2.1
      rw [α.2.2] at hp
      exact hp⟩

theorem emergenceFiberPath_injective (B : ConcreteBookkeeping κ Γ)
    (hB : B.IsValid) (i : Stage κ) :
    Function.Injective (B.emergenceFiberPath hB i) := by
  intro α β hp
  have hp' := congrArg Subtype.val hp
  change B.selectedPath hB ⟨α.1, α.2.1⟩ =
    B.selectedPath hB ⟨β.1, β.2.1⟩ at hp'
  have hstage : (⟨α.1, α.2.1⟩ : B.phi) = ⟨β.1, β.2.1⟩ :=
    B.selectedPath_injective hB hp'
  exact Subtype.ext (congrArg (fun z : B.phi ↦ z.1) hstage)

/-- Each emergence fiber has cardinality at most the corresponding
inessential path family.  The lift is forced by `Stage κ`, which lives one
universe above the web's vertex and path types. -/
theorem mk_emergenceFiber_le (B : ConcreteBookkeeping κ Γ)
    (hB : B.IsValid) (i : Stage κ) :
    #(B.emergenceFiber hB i) ≤
      Cardinal.lift.{u + 1, u} #(B.inessentialNext i) := by
  simpa only [← Cardinal.lift_umax, Cardinal.lift_id] using
    Cardinal.lift_mk_le_lift_mk_of_injective
    (B.emergenceFiberPath_injective hB i)

/-- If the inessential family at `i` has size below `κ`, then its emergence
fiber is nonstationary. -/
theorem emergenceFiber_not_stationary (B : ConcreteBookkeeping κ Γ)
    (hB : B.IsValid) (hκ : κ.IsRegular) (i : Stage κ)
    (hsmall : #(B.inessentialNext i) < κ) :
    ¬ Stationary.IsStationaryBelow κ (B.emergenceFiber hB i) := by
  apply Stationary.not_isStationaryBelow_of_mk_lt hκ
  exact (B.mk_emergenceFiber_le hB i).trans_lt (Cardinal.lift_lt.mpr hsmall)

/-! ## Hanging stages -/

/-- Grounded obstruction stages for a concrete web. -/
def groundedStages (B : ConcreteBookkeeping κ Γ) : Set (Stage κ) :=
  {α | ∃ p, B.chosen α = some p ∧ p.initial ∈ Γ.source}

/-- Hanging obstruction stages for a concrete web. -/
def hangingStages (B : ConcreteBookkeeping κ Γ) : Set (Stage κ) :=
  B.phi \ B.groundedStages

theorem phi_eq_grounded_union_hanging (B : ConcreteBookkeeping κ Γ)
    (hB : B.IsValid) :
    B.phi = B.groundedStages ∪ B.hangingStages := by
  ext α
  constructor
  · intro hα
    by_cases hg : α ∈ B.groundedStages
    · exact Or.inl hg
    · exact Or.inr ⟨hα, hg⟩
  · rintro (hg | hh)
    · obtain ⟨p, hp, -⟩ := hg
      exact (B.mem_phi_iff_exists_chosen hB).2 ⟨p, hp⟩
    · exact hh.1

/-- The hanging stages are nonstationary when their marker origins form an
injective regressive map.  This is source Lemma 7.15 in its exact
set-theoretic form. -/
theorem hangingStages_not_stationary
    (hκ : κ.IsRegular) (hκu : ℵ₀ < κ)
    (B : ConcreteBookkeeping κ Γ) (origin : Stage κ → Stage κ)
    (hreg : Stationary.IsRegressiveOn B.hangingStages origin)
    (hinj : Set.InjOn origin B.hangingStages) :
    ¬ Stationary.IsStationaryBelow κ B.hangingStages :=
  Stationary.not_isStationaryBelow_of_injOn_regressive hκu hκ hreg hinj

/-- If all obstruction stages are stationary but hanging stages are not,
then grounded obstruction stages are stationary (source Lemma 7.22). -/
theorem groundedStages_isStationary
    (hκ : κ.IsRegular) (hκu : ℵ₀ < κ)
    (B : ConcreteBookkeeping κ Γ) (hB : B.IsValid)
    (hphi : Stationary.IsStationaryBelow κ B.phi)
    (hhang : ¬ Stationary.IsStationaryBelow κ B.hangingStages) :
    Stationary.IsStationaryBelow κ B.groundedStages :=
  by
    have hcof : Order.cof (Stage κ) ≠ ℵ₀ := by
      rw [Stationary.cof_below_eq_lift hκ]
      rw [← Cardinal.lift_aleph0.{u + 1, u}]
      exact (Cardinal.lift_lt.mpr hκu).ne'
    have hu : Stationary.IsStationaryBelow κ
        (B.groundedStages ∪ B.hangingStages) := by
      rw [← B.phi_eq_grounded_union_hanging hB]
      exact hphi
    exact (isStationary_union_iff hcof).mp hu |>.resolve_right hhang

/-! ## The stationary obstruction characterization -/

/-- Stages at which at least `κ` paths are already inessential. -/
def largeInessentialStages (B : ConcreteBookkeeping κ Γ) : Set (Stage κ) :=
  {i | κ ≤ #(B.inessentialNext i)}

/-- Outside an exceptional set, regressive emergence cannot be stationary
when every inessential family has size below `κ`.  Fodor makes the
emergence index constant on a stationary set, while the fiber injection
above makes that fiber nonstationary. -/
theorem regularEmergence_not_stationary
    (hκ : κ.IsRegular) (hκu : ℵ₀ < κ)
    (B : ConcreteBookkeeping κ Γ) (hB : B.IsValid)
    (exceptional : Set (Stage κ))
    (hlarge : ¬ (B.largeInessentialStages).Nonempty)
    (hreg : Stationary.IsRegressiveOn (B.phi \ exceptional)
      (B.emergenceIndex hB)) :
    ¬ Stationary.IsStationaryBelow κ (B.phi \ exceptional) := by
  intro hstat
  obtain ⟨i, hi⟩ := Stationary.pressingDown hκu hκ hstat hreg
  have hsmall : #(B.inessentialNext i) < κ := by
    exact lt_of_not_ge fun hiLarge ↦ hlarge ⟨i, hiLarge⟩
  have hfiber : Stationary.IsStationaryBelow κ (B.emergenceFiber hB i) := by
    apply hi.mono
    rintro α ⟨hα, heq⟩
    exact ⟨hα.1, heq⟩
  exact B.emergenceFiber_not_stationary hB hκ i hsmall hfiber

/-- Pure bookkeeping form of source Lemma 7.27.

`exceptional` is instantiated by `Φ_h ∪ Φ_h^∞`.  The three local premises
are precisely the graph-specific facts used by the set-theoretic proof:
exceptional stages are obstructions, a nonexceptional obstruction has
strictly earlier emergence, and one large inessential family forces the
entire later tail to consist of obstructions. -/
theorem obstruction_characterization
    (hκ : κ.IsRegular) (hκu : ℵ₀ < κ)
    (B : ConcreteBookkeeping κ Γ) (hB : B.IsValid)
    (exceptional : Set (Stage κ))
    (hexceptional : exceptional ⊆ B.phi)
    (hreg : Stationary.IsRegressiveOn (B.phi \ exceptional)
      (B.emergenceIndex hB))
    (htail : ∀ i ∈ B.largeInessentialStages, Set.Ici i ⊆ B.phi) :
    Stationary.IsStationaryBelow κ B.phi ↔
      Stationary.IsStationaryBelow κ exceptional ∨
        (B.largeInessentialStages).Nonempty := by
  have hcof : Order.cof (Stage κ) ≠ ℵ₀ := by
    rw [Stationary.cof_below_eq_lift hκ]
    rw [← Cardinal.lift_aleph0.{u + 1, u}]
    exact (Cardinal.lift_lt.mpr hκu).ne'
  constructor
  · intro hphi
    by_cases hlarge : (B.largeInessentialStages).Nonempty
    · exact Or.inr hlarge
    · left
      have hregular : ¬ Stationary.IsStationaryBelow κ
          (B.phi \ exceptional) :=
        regularEmergence_not_stationary hκ hκu B hB exceptional hlarge hreg
      have hdecomp : B.phi = exceptional ∪ (B.phi \ exceptional) := by
        ext α
        constructor
        · intro hα
          by_cases he : α ∈ exceptional
          · exact Or.inl he
          · exact Or.inr ⟨hα, he⟩
        · rintro (he | hr)
          · exact hexceptional he
          · exact hr.1
      have hstatUnion : Stationary.IsStationaryBelow κ
          (exceptional ∪ (B.phi \ exceptional)) := hdecomp ▸ hphi
      exact ((isStationary_union_iff hcof).mp hstatUnion).resolve_right hregular
  · rintro (he | ⟨i, hi⟩)
    · exact he.mono hexceptional
    · letI : Nonempty (Stage κ) := ⟨i⟩
      have htailStat : Stationary.IsStationaryBelow κ (Set.Ici i) :=
        (Stationary.isClub_Ici i).isStationary hcof
      exact htailStat.mono (htail i hi)

/-! ## Corrected closure lemma -/

/-- A stage at which the frontier meets the support of `p`.  Keeping the
support on the path side avoids the type error `Σ(p) ∩ T_β` in the printed
proof of Lemma 7.28. -/
def Hits (frontier : Stage κ → Set V) (p : Γ.DPath) (α : Stage κ) : Prop :=
  (frontier α ∩ p.support).Nonempty

/-- The hit stages of `p` which lie in the prescribed closed set `Σ`. -/
def hitStages (frontier : Stage κ → Set V) (sigma : Set (Stage κ))
    (p : Γ.DPath) : Set (Stage κ) :=
  sigma ∩ {α | Hits frontier p α}

@[simp]
theorem mem_hitStages {frontier : Stage κ → Set V} {sigma : Set (Stage κ)}
    {p : Γ.DPath} {α : Stage κ} :
    α ∈ hitStages frontier sigma p ↔ α ∈ sigma ∧ Hits frontier p α :=
  Iff.rfl

/-- A path which meets a frontier at a stage is not inessential there.
This is a graph premise of Lemma 7.28, separated out because its proof uses
essential prefixes and warp disjointness. -/
def HitExcludesInessential (B : ConcreteBookkeeping κ Γ)
    (frontier : Stage κ → Set V) (p : Γ.DPath) : Prop :=
  ∀ α, Hits frontier p α → p ∉ B.inessentialCurrent α

/-- Corrected order-theoretic form of source Lemma 7.28.

The premise `hlimitIE` packages only the roof/frontier part of the graph
argument: at a supremum of earlier hit stages, if `p` misses the limiting
frontier, then `p` belongs to the successor-normalized inessential family.
The theorem itself proves that `p` was not recorded earlier, using
`hpers`, `hhitEssential`, and the cofinality encoded by `IsLUB`.  Hence the
missed limit would be an obstruction in `Φ`, contradicting `Σ ∩ Φ = ∅`. -/
theorem hitStages_dirSupClosed
    (B : ConcreteBookkeeping κ Γ) (hpers : B.IsPersistent)
    (frontier : Stage κ → Set V) (sigma : Set (Stage κ))
    (hsigma : DirSupClosed sigma) (hsigmaPhi : Disjoint sigma B.phi)
    (p : Γ.DPath) (hhitEssential : HitExcludesInessential B frontier p)
    (hlimitIE : ∀ (d : Set (Stage κ)) (β : Stage κ),
      d ⊆ hitStages frontier sigma p → d.Nonempty →
      DirectedOn (· ≤ ·) d → IsLUB d β →
      β ∈ sigma → ¬ Hits frontier p β → p ∈ B.inessentialNext β) :
    DirSupClosed (hitStages frontier sigma p) := by
  intro d hd hdn hdd β hβ
  have hdSigma : d ⊆ sigma := fun α hα ↦ (hd hα).1
  have hβSigma : β ∈ sigma := hsigma hdSigma hdn hdd hβ
  by_contra hβhitStages
  have hβmiss : ¬ Hits frontier p β := by
    intro hhit
    exact hβhitStages ⟨hβSigma, hhit⟩
  have hpIE : p ∈ B.inessentialNext β :=
    hlimitIE d β hd hdn hdd hβ hβSigma hβmiss
  have hpNotRecorded : p ∉ B.recordedBefore β := by
    rintro ⟨γ, hγβ, hγp⟩
    have hex : ∃ ψ ∈ d, γ < ψ := by
      by_contra hn
      push Not at hn
      have hγub : ∀ ψ ∈ d, ψ ≤ γ := by
        intro ψ hψ
        exact hn ψ hψ
      exact (not_le_of_gt hγβ) (hβ.2 hγub)
    obtain ⟨ψ, hψd, hγψ⟩ := hex
    have hpIEψ : p ∈ B.inessentialCurrent ψ :=
      B.recorded_path_persists hpers hγp hγψ
    exact hhitEssential ψ (hd hψd).2 hpIEψ
  have hβphi : β ∈ B.phi :=
    ⟨p, hpIE, hpNotRecorded⟩
  exact Set.disjoint_left.1 hsigmaPhi hβSigma hβphi

end ConcreteBookkeeping
end LadderBookkeeping
end Erdos599
