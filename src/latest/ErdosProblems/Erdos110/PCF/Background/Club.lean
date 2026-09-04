import ErdosProblems.Erdos110.PCF.Background.Cofinality
import ErdosProblems.Erdos110.PCF.Background.Topology

/-!
Adapted from Y. Paz, `PCF-Theory` (Apache 2.0), and ported to Mathlib v4.33.0.
-/

/-!
# Club and stationary sets

This file sets up the basic theory of clubs (closed and unbounded sets) and stationary sets.

## Main definitions

* `Ordinal.IsClosed`: A set of ordinals `S` is closed in `o` if `S ⊆ Iio o`
  and `S` contains every `x < o` such that `x.IsAcc S`.
* `Ordinal.IsClub`: A set of ordinals `S` is a club in `o` if
  it is closed in `o` and unbounded in `o`.

## Main results

* `isClub_sInter`: The intersection of fewer than `o.cof` clubs in `o` is a club in `o`.
-/

noncomputable section
open Classical

open Cardinal Set Order Filter

universe u v

namespace Ordinal

-- Match the order projections used by the legacy ordinal-topology API.
local instance clubOrdinalLT : LT Ordinal := Ordinal.partialOrder.toLT
local instance clubOrdinalLE : LE Ordinal := Ordinal.partialOrder.toLE

/-- A set of ordinals is a club below an ordinal if it is closed and unbounded in it. -/
def IsClub (C : Set Ordinal) (o : Ordinal) : Prop :=
  IsClosedBelow C o ∧ IsAcc o C

structure Club (α : Ordinal) where
  carrier : Set Ordinal
  isClub : IsClub carrier α

instance {α : Ordinal} : SetLike (Club α) Ordinal where
  coe := Club.carrier
  coe_injective s t h := by cases s; cases t; congr

instance {α : Ordinal} : HasSubset (Club α) where
  Subset := fun C D ↦ C.carrier ⊆ D.carrier

instance {α : Ordinal} : HasSSubset (Club α) where
  SSubset := fun C D ↦ C.carrier ⊂ D.carrier

instance {α : Ordinal} : IsNonstrictStrictOrder (Club α) (· ⊆ ·) (· ⊂ ·) where
  right_iff_left_not_left _ _ := Iff.rfl

instance {α : Ordinal} : IsAntisymm (Club α) (· ⊆ ·) where
  antisymm _ _ h h' := SetLike.coe_injective (Subset.antisymm h h')

section ClubBasics

theorem IsClub.isClosedBelow {C : Set Ordinal} {o : Ordinal} (h : IsClub C o) :
    IsClosedBelow C o := h.1

theorem IsClub.isAcc {C : Set Ordinal} {o : Ordinal} (h : IsClub C o) : IsAcc o C := h.2

theorem isClub_iff {C : Set Ordinal} {o : Ordinal} : IsClub C o
    ↔ ((∀ p < o, IsAcc p C → p ∈ C) ∧ (o ≠ 0 ∧ ∀ p < o, (C ∩ Ioo p o).Nonempty)) :=
  and_congr isClosedBelow_iff (isAcc_iff _ _)

theorem IsClub.pos {C : Set Ordinal} {o : Ordinal} (h : IsClub C o) : 0 < o :=
  h.isAcc.pos

theorem IsClub.ne_zero {C : Set Ordinal} {o : Ordinal} {h : IsClub C o} : o ≠ 0 :=
  h.pos.ne.symm

theorem IsClub.mem_of_isAcc {C : Set Ordinal} {o p : Ordinal} (h : IsClub C o) (hp : p < o) :
    IsAcc p C → p ∈ C := (isClub_iff.mp h).1 _ hp

theorem IsClub.forall_lt {o : Ordinal} {S : Set Ordinal} (h : o.IsClub S) :
    ∀ p < o, (S ∩ Ioo p o).Nonempty := ((isAcc_iff _ _).mp h.isAcc).2

theorem IsClub.inter_Iio {C : Set Ordinal} {o : Ordinal} (h : IsClub C o) :
    IsClub (C ∩ Iio o) o := by
  apply isClub_iff.mpr
  constructor
  · exact fun p hpo hp ↦ ⟨h.mem_of_isAcc hpo (hp.mono inter_subset_left), hpo⟩
  · refine ⟨h.pos.ne.symm, fun p hpo ↦ ?_⟩
    convert h.isAcc.inter_Ioo_nonempty hpo using 1
    ext; simp_all

theorem isClub_univ {α : Ordinal} (h : IsSuccLimit α) : IsClub Set.univ α := by
  refine isClub_iff.mpr ⟨?_, ?_, ?_⟩
  · exact fun _ _ _ ↦ mem_univ _
  · exact h.pos.ne.symm
  · exact fun p plt ↦ ⟨succ p, ⟨mem_univ _, ⟨lt_succ _, h.succ_lt plt⟩⟩⟩

def univ_club {α : Ordinal} (h : IsSuccLimit α) : Club α := ⟨Set.univ, isClub_univ h⟩

theorem IsClub.isClub_of_isAcc {α β : Ordinal} {C : Set Ordinal} (h : β < α) (hC : IsClub C α)
    (hacc : IsAcc β C) : IsClub C β := by
  refine isClub_iff.mpr ⟨?_, ?_, ?_⟩
  · exact fun p plt hp ↦ hC.mem_of_isAcc (plt.trans h) hp
  · exact hacc.isSuccLimit.pos.ne.symm
  · exact fun p hp ↦ hacc.forall_lt p hp

end ClubBasics

section ClubIntersection

variable {o : Ordinal.{u}} {S : Set (Set Ordinal)}
variable {ι : Type u} {f : ι → Set Ordinal}

/-- Given less than `o.cof` unbounded sets in `o` and some `q < o`, there is a `q < p < o`
  such that `Ioo q p` contains an element of every unbounded set. -/
theorem exists_above_of_lt_cof {p : Ordinal} (h : p < o) (hSemp : Nonempty S)
    (hSacc : ∀ U ∈ S, o.IsAcc U) (hScard : #S < Cardinal.lift.{u + 1, u} o.cof) :
    ∃ q < o, p < q ∧ ∀ U ∈ S, (U ∩ Ioo p q).Nonempty := by
  rw [lift_cof] at hScard
  have oLim : IsSuccLimit o := hSemp.casesOn fun ⟨T, hT⟩ ↦ (hSacc T hT).isSuccLimit
  let f : ↑S → Ordinal := fun U ↦ lift.{u + 1, u} (sInf (U ∩ (Ioo p o)))
  have infMem : ∀ U : S, sInf (↑U ∩ Ioo p o) ∈ ↑U ∩ Ioo p o := fun U ↦
    csInf_mem ((hSacc U.1 U.2).inter_Ioo_nonempty h : (↑U ∩ Ioo p o).Nonempty)
  have flto : ∀ U : S, f U < lift.{u + 1, u} o := fun U ↦ by
    simp_all only [mem_inter_iff, mem_Ioo, lift_lt, f]
  set q := (iSup f) + 1 with qdef
  have qlto : q < lift.{u + 1, u} o :=
    ((isSuccLimit_lift.{u + 1, u}).mpr oLim).succ_lt (iSup_lt_ord hScard flto)
  rcases mem_range_lift_of_le qlto.le with ⟨q', hq'⟩
  use q', lift_lt.mp (hq' ▸ qlto)
  have fltq : ∀ U, f U < q := fun U ↦ by
    convert lt_of_le_of_lt (le_ciSup (by apply bddAbove_of_small) U) (qdef ▸ lt_add_one (iSup f))
  constructor <;> try constructor
  · rcases hSemp with ⟨U, hU⟩
    have pltf : lift.{u + 1, u} p < f ⟨U, hU⟩ :=
      lift_lt.mpr (mem_of_mem_inter_right (infMem ⟨U, hU⟩)).1
    have := lt_of_lt_of_le pltf (fltq ⟨U, hU⟩).le
    rwa [← hq', lift_lt] at this
  intro U hU
  specialize infMem ⟨U, hU⟩
  specialize fltq ⟨U, hU⟩
  have : f ⟨U, hU⟩ ∈ Ioo (lift.{u + 1, u} p) q := ⟨lift_lt.mpr infMem.2.1, fltq⟩
  rw [← hq'] at fltq
  rcases mem_range_lift_of_le fltq.le with ⟨fUdown, fUlift⟩
  use fUdown
  constructor
  · simp_all only [lift_inj, mem_inter_iff, f]
  · exact ⟨lift_lt.mp <| fUlift ▸ (this.1), lift_lt.mp (hq'.symm ▸ (fUlift ▸ this).2)⟩

/--
Given a limit ordinal `o` and a property on pairs of ordinals `P`, such that
for any `p < o` there is a `q < o` above `p` so that `P p q`, we can construct
an increasing `ω`-sequence below `o` that satisfies `P` between every 2 consecutive elements.
Additionaly, the sequence can begin arbitrarily high in `o`. That is, above any `r < o`.
-/
theorem exists_omega0_seq_succ_prop (opos : 0 < o) {P : Ordinal → Ordinal → Prop}
    (hP : ∀ p : Iio o, ∃ q, (p < q ∧ P p q)) (r : Iio o) : ∃ f : (Iio ω) → Iio o,
    (∀ i, P (f i) (f (succ i))) ∧ (∀ i j, (i < j) → f i < f j)
    ∧ r < f ⟨0, omega0_pos⟩ := by
  let step : Iio o → Iio o := fun p ↦ choose (hP p)
  let g : ℕ → Iio o := fun n ↦ Nat.rec (step r) (fun _ p ↦ step p) n
  have g_zero : g 0 = step r := rfl
  have g_succ (n : ℕ) : g (n + 1) = step (g n) := by
    simp [g]
  let f : Iio ω → Iio o := fun i ↦ g (relIso_nat_omega0.symm i)
  have symm_succ (i : Iio ω) :
      relIso_nat_omega0.symm (succ i) = Nat.succ (relIso_nat_omega0.symm i) := by
    have hmap := relIso_nat_omega0.map_succ (relIso_nat_omega0.symm i)
    rw [relIso_nat_omega0.apply_symm_apply] at hmap
    have h := congrArg relIso_nat_omega0.symm hmap
    simpa only [relIso_nat_omega0.symm_apply_apply, Order.succ_eq_add_one,
      Nat.succ_eq_add_one] using h.symm
  have f_succ (i : Iio ω) : f (succ i) = step (f i) := by
    change g (relIso_nat_omega0.symm (succ i)) = step (g (relIso_nat_omega0.symm i))
    rw [symm_succ, Nat.succ_eq_add_one, g_succ]
  use f
  constructor <;> try constructor
  · intro i
    rw [f_succ]
    exact (choose_spec (hP (f i))).2
  · have aux : ∀ i, f i < f (succ i) := fun i ↦ by
      rw [f_succ]
      exact (choose_spec (hP (f i))).1
    exact strictMono_of_succ_lt_omega0 f aux
  have symm_zero : relIso_nat_omega0.symm (⟨0, omega0_pos⟩ : Iio ω) = 0 := by
    apply relIso_nat_omega0.injective
    rw [relIso_nat_omega0.apply_symm_apply]
    rfl
  change r < g (relIso_nat_omega0.symm (⟨0, omega0_pos⟩ : Iio ω))
  rw [symm_zero, g_zero]
  exact (choose_spec (hP r)).1

theorem exists_omega0_seq_succ_prop_pos (onelto : 1 < o) {P : Ordinal → Ordinal → Prop}
    (hP : ∀ p : Iio o, 0 < p.1 → ∃ q : Iio o, (p < q ∧ P p q)) (r : Iio o) :
    ∃ f : (Iio ω : Set Ordinal.{0}) → (Iio o), (∀ i, P (f i) (f (succ i)))
    ∧ (∀ i j, (i < j) → f i < f j) ∧ r < f ⟨0, omega0_pos⟩ := by
  let P' : Ordinal → Ordinal → Prop := fun p q ↦ p = 0 ∨ P p q
  have hP' : ∀ p : Iio o, ∃ q : Iio o, (p < q ∧ P' p q) := fun p ↦ by
    by_cases h : p.1 = 0
    · use ⟨1, onelto⟩
      use (by change p.1 < 1; exact h ▸ zero_lt_one)
      exact Or.inl h
    convert hP p (pos_iff_ne_zero.mpr h) using 1
    simp_all only [false_or, P']
  rcases exists_omega0_seq_succ_prop (zero_lt_one.trans onelto) hP' r with ⟨f, hf⟩
  use f
  refine ⟨fun i ↦ ?_, hf.2⟩
  have := hf.1 i
  have rltf0 := hf.2.2
  by_cases hi' : i.1 = 0
  · refine this.resolve_left ?_
    have hi : i = (⟨0, omega0_pos⟩ : Iio ω) := Subtype.ext hi'
    have hpos : (0 : Ordinal) < (f i).1 := by
      rw [hi]
      exact bot_lt_of_lt rltf0
    exact hpos.ne'
  · refine this.resolve_left ?_
    have h0i : (⟨0, omega0_pos⟩ : Iio ω) < i := by
      change (0 : Ordinal) < i.1
      exact pos_iff_ne_zero.mpr hi'
    have hpos : (0 : Ordinal) < (f i).1 := bot_lt_of_lt (hf.2.1 _ _ h0i)
    exact hpos.ne'

/-- If between every 2 consecutive elements of a weakly increasing `δ`-sequence
  there is an element of `C`, and `δ` is a limit ordinal,
  then the supremum of the sequence is an accumulation point of `C`. -/
theorem isAcc_iSup_of_between {δ : Ordinal.{u}} (C : Set Ordinal) (δLim : IsSuccLimit δ)
    (s : Iio δ → Ordinal.{max u v}) (sInc : ∀ o, s o < s (succ o))
    (h : ∀ o, (C ∩ (Icc (s o) (s (succ o)))).Nonempty) :
    IsAcc (iSup s) C := by
  rw [isAcc_iff]
  constructor
  · rw [← pos_iff_ne_zero, Ordinal.lt_iSup_iff]
    have h1 : (1 : Ordinal) < δ := by
      simpa only [← Ordinal.add_one_eq_succ, zero_add] using δLim.succ_lt δLim.pos
    let z : Iio δ := ⟨0, δLim.pos⟩
    let one : Iio δ := ⟨1, h1⟩
    have hz : succ z = one := by
      apply Subtype.ext
      rw [coe_succ_Iio δLim.isSuccPrelimit]
      exact succ_zero
    use one
    refine lt_of_le_of_lt (bot_le : (0 : Ordinal) ≤ s z) ?_
    simpa only [hz] using sInc z
  intro p hp
  rw [Ordinal.lt_iSup_iff] at hp
  obtain ⟨r, hr⟩ := hp
  obtain ⟨q, hq⟩ := h r
  use q
  refine ⟨hq.1, ⟨hr.trans_le hq.2.1, ?_⟩⟩
  rw [Ordinal.lt_iSup_iff]
  exact ⟨succ (succ r), hq.2.2.trans_lt (sInc (succ r))⟩

/--
The intersection of less than `o.cof` clubs in `o` is a club in `o`.
-/
theorem IsClub.sInter (hCof : ℵ₀ < o.cof) (hS : ∀ C ∈ S, IsClub C o) (hSemp : S.Nonempty)
    (Scard : #S < Cardinal.lift.{u + 1, u} o.cof) : IsClub (⋂₀ S) o := by
  refine ⟨IsClosedBelow.sInter (fun C CmemS ↦ (hS C CmemS).1), (isAcc_iff _ _).mpr ?_⟩
  have nonemptyS : Nonempty S := hSemp.to_subtype
  have oLim : IsSuccLimit o := aleph0_le_cof.mp hCof.le
  use oLim.pos.ne.symm
  intro p plto
  let P : Ordinal → Ordinal → Prop := fun p q ↦ ∀ C ∈ S, (C ∩ Ioo p q).Nonempty
  have auxP : ∀ p : Iio o, ∃ q, p < q ∧ P p q := fun p ↦ by
    rcases exists_above_of_lt_cof p.2 nonemptyS (fun U hU ↦ (hS U hU).2) Scard with ⟨q, hq⟩
    use ⟨q, hq.1⟩, hq.2.1, hq.2.2
  rcases exists_omega0_seq_succ_prop.{u, u} oLim.pos auxP ⟨p, plto⟩ with ⟨f, hf⟩
  let sup := iSup (fun n ↦ (f n).1)
  use sup
  have suplt : sup < o := by
    apply iSup_Iio_lt_ord (fun n ↦ (f n).2)
    rwa [Cardinal.lift_id, Cardinal.lift_id, card_omega0]
  constructor
  · intro s hs
    apply (hS s hs).1.forall_lt sup suplt
    apply isAcc_iSup_of_between
    · exact isSuccLimit_omega0
    · intro n
      rw [@Subtype.coe_lt_coe]
      convert hf.2.1 n (succ n) ?_
      · apply Subtype.coe_lt_coe.mp
        rw [coe_succ_of_mem]
        · exact lt_succ n.1
        exact isSuccLimit_omega0.succ_lt n.2
    · intro n
      apply (hf.1 n s hs).mono
      exact inter_subset_inter_right _ Ioo_subset_Icc_self
  · constructor
    · rw [Ordinal.lt_iSup_iff]
      exact ⟨⟨0, omega0_pos⟩, hf.2.2⟩
    · exact suplt

theorem IsClub.iInter_lift {ι : Type v} {f : ι → Set Ordinal.{u}} [Nonempty ι] (hCof : ℵ₀ < o.cof)
    (hf : ∀ i, IsClub (f i) o) (ιCard : Cardinal.lift.{u} #ι < Cardinal.lift.{v} o.cof) :
    IsClub (⋂ i, f i) o := by
  refine IsClub.sInter (S := range f) hCof (fun y ⟨x, hx⟩ ↦ hx ▸ hf x) (range_nonempty f) ?_
  have := mk_range_le_lift (f := f)
  rw [← Cardinal.lift_lt.{_, max v (u + 1)}]
  have aux : Cardinal.lift.{max v (u + 1), u + 1} #↑(range f) =
      Cardinal.lift.{max v, u + 1} #↑(range f) := by
    simpa only [max_comm] using
      congrFun (@Cardinal.lift_umax.{u + 1, v}) #(range f)
  rw [aux]
  apply this.trans_lt
  convert lift_strictMono.{max u v, max (u + 1) v} ιCard
  · rw [Cardinal.lift_lift, Cardinal.lift_umax.{v, u + 1}]
  · rw [Cardinal.lift_lift, Cardinal.lift_lift]

theorem IsClub.iInter [Nonempty ι] (hCof : ℵ₀ < o.cof) (hf : ∀ i, IsClub (f i) o)
    (ιCard : #ι < o.cof) : IsClub (⋂ i, f i) o :=
  IsClub.iInter_lift hCof hf (Cardinal.lift_lt.mpr ιCard)

theorem IsClub.inter {Ϟ : Ordinal.{u}} (hCof : ℵ₀ < Ϟ.cof) {C D : Set Ordinal}
    (hC : IsClub C Ϟ) (hD : IsClub D Ϟ) : IsClub (C ∩ D) Ϟ := by
  rw [← sInter_pair C D]
  refine IsClub.sInter hCof ?_ ⟨C, mem_insert C _⟩ ?_
  · simp_all
  · exact (Set.finite_singleton D).insert C |>.lt_aleph0 |>.trans
      (by simpa using Cardinal.lift_lt.2 hCof)

theorem IsClub.iInter_Iio {Ϟ o : Ordinal.{u}} {p : Iio o} {f : Iio p → Set Ordinal} (hϞ : ℵ₀ < Ϟ.cof)
    (h : p.1.card < Ϟ.cof) (hf : ∀ x, IsClub (f x) Ϟ) : IsClub (⋂ α, f α) Ϟ := by
  by_cases h : 0 < p.1
  · have : Nonempty (Iio p) := ⟨⟨0, h.trans p.2⟩, h⟩
    apply IsClub.iInter_lift hϞ hf
    · rwa [mk_Iio_subtype, mk_Iio_ordinal, Cardinal.lift_lift, Cardinal.lift_lt]
  · have : IsEmpty (Iio p) := isEmpty_iff.mpr fun ⟨x, h'⟩ ↦
      have hp0 : p.1 = 0 := (eq_zero_or_pos p.1).resolve_right h
      have hx : x.1 < (0 : Ordinal) := by
        change x.1 < p.1 at h'
        simpa only [hp0] using h'
      (not_lt_of_ge (bot_le : (0 : Ordinal) ≤ x.1)) hx
    rw [iInter_of_empty]
    convert isClub_univ <| aleph0_le_cof.mp hϞ.le

end ClubIntersection

/- Accumulation points of a club form a club. -/
theorem IsClub.derivedSet {α : Ordinal.{u}} {C : Set Ordinal} (hcof : ℵ₀ < α.cof) (h : IsClub C α) :
    IsClub (derivedSet C) α := by
  rw [isClub_iff]
  refine ⟨?_, h.ne_zero, ?_⟩
  · intro p pltα pacc
    change IsAcc _ _
    rw [isAcc_iff]
    refine ⟨pacc.pos.ne.symm, ?_⟩
    intro q qltp
    obtain ⟨x, hx⟩ := pacc.forall_lt q qltp
    exact ⟨x, ⟨h.mem_of_isAcc (hx.2.2.trans pltα) hx.1, hx.2⟩⟩
  · intro p pltα
    obtain ⟨f, hf⟩ := exists_omega0_seq_succ_prop.{_, 0} (bot_lt_of_lt pltα) (P := fun _ x ↦ x ∈ C)
      (fun p ↦ by
        obtain ⟨x, hx⟩ := h.forall_lt p p.2
        exact ⟨⟨x, hx.2.2⟩, ⟨hx.2.1, hx.1⟩⟩)
      ⟨p, pltα⟩
    use iSup (fun x ↦ f x)
    constructor
    · apply isAcc_iSup (o := ω) (α := ⟨0, omega0_pos⟩) isSuccLimit_omega0
      · exact hf.2.1
      · intro n h
        convert hf.1 ⟨pred n, (pred_le_self n.1).trans_lt n.2⟩
        rw [succ_Iio isSuccLimit_omega0.isSuccPrelimit]
        apply SetCoe.ext
        exact (succ_pred_of_finite (bot_lt_of_lt h) n.2).symm
    · constructor
      · exact (lt_ciSup_iff bddAbove_of_small).mpr ⟨⟨0, omega0_pos⟩, hf.2.2⟩
      · apply iSup_Iio_lt_ord (fun i ↦ (f i).2)
        rwa [card_omega0, lift_aleph0, Cardinal.lift_id']

def diagInter {o : Ordinal} (c : Iio o → Set Ordinal) : Set Ordinal :=
  {p | ∀ r : Iio o, r < p → p ∈ c r}

prefix:110 "Δ " => diagInter

theorem mem_diagInter {o x : Ordinal} {c : Iio o → Set Ordinal} :
    x ∈ Δ c ↔ ∀ r : Iio o, r < x → x ∈ c r := Iff.rfl

theorem diagInter_Ioi_subset {o : Ordinal} (r : Iio o) (c : Iio o → Set Ordinal) :
    Δ c ∩ Ioi r.1 ⊆ c r :=
  fun _ h ↦ h.1 r h.2

section DiagonalIntersection

theorem isClosedBelow_diagInter {o : Ordinal} {c : Iio o → Set Ordinal}
    (h : ∀ r, IsClosedBelow (c r) o) : IsClosedBelow (Δ c) o := by
  rw [isClosedBelow_iff]
  intro p plt hp r rlt
  apply (h r).forall_lt p plt
  apply IsAcc.mono (diagInter_Ioi_subset r c)
  exact hp.inter_Ioi rlt

theorem isAcc_diagInter {κ : Cardinal.{u}} (hκ : ℵ₀ < κ) (hreg : κ.IsRegular)
    {c : Iio κ.ord → Set Ordinal} (hc : ∀ r, IsClub (c r) κ.ord) : IsAcc κ.ord (Δ c) := by
  rw [isAcc_iff]
  refine ⟨(ord_zero ▸ ord_strictMono (aleph0_pos.trans hκ)).ne.symm, ?_⟩
  let P : Ordinal.{u} → Ordinal → Prop := fun p q ↦ ∀ r : Iio κ.ord, r.1 < p → q ∈ c r
  have auxP : ∀ r : Iio κ.ord, 0 < r.1 → ∃ s, (r < s ∧ P r s) := by
    intro r hr
    have : ↑(Iio r.1).Nonempty := ⟨0, hr⟩
    let C : Set Ordinal := ⋂ s : Iio r.1, c ⟨s.1, have : s.1 < r.1 := s.2
      this.trans (r.2 : r.1 < κ.ord)⟩
    have : IsClub C κ.ord := by
      refine @IsClub.iInter_lift κ.ord (Iio r.1)
        (fun s ↦ c ⟨s.1, have : s.1 < r.1 := s.2; this.trans (r.2 : r.1 < κ.ord)⟩) this.to_subtype
        (hreg.cof_eq.symm ▸ hκ)
        (fun s ↦ hc ⟨s.1, (LT.lt.trans s.2 r.2 : s.1 < κ.ord)⟩)
        ?_
      · rw [mk_Iio_ordinal, Cardinal.lift_lift, Cardinal.lift_lt, hreg.cof_eq, ← lt_ord]
        exact r.2
    obtain ⟨x, hx⟩ := this.2.inter_Ioo_nonempty r.2
    use ⟨x, hx.2.2⟩
    constructor
    · exact hx.2.1
    · exact fun s slt ↦ mem_iInter.mp hx.1 ⟨s.1, slt⟩
  intro p plt
  obtain ⟨f, hf⟩ := exists_omega0_seq_succ_prop_pos (one_lt_omega0.trans (lt_ord.mpr hκ))
    auxP ⟨p, plt⟩
  use ⨆ i, f i
  have ltκ : ⨆ i, (f i).1 < κ.ord := by
    refine iSup_lt_ord_lift' ?_ fun i ↦ (f i).2
    have aux : Cardinal.lift.{max 1 u, 0} ℵ₀ = Cardinal.lift.{max 1 u, u} (Cardinal.lift.{u} ℵ₀) := by
      rw [Cardinal.lift_id, lift_aleph0, lift_aleph0]
    rwa [mk_Iio_ordinal, card_omega0, Cardinal.lift_lift, aux, Cardinal.lift_umax.{u, 1},
      Cardinal.lift_lt, lift_aleph0, hreg.cof_eq]
  constructor
  · intro r hr
    rw [Ordinal.lt_iSup_iff] at hr
    obtain ⟨n, hn⟩ := hr
    apply (hc r).1.forall_lt _ ltκ
    have aux := hf.1
    have : ∀ m, n < m → (f (succ m)).val ∈ c r := by
      intro m hm
      apply aux m r
      have := hf.2.1 n m hm
      exact hn.trans this
    have : ∀ m, succ n < m → (f m).1 ∈ c r := by
      intro m hm
      have := this ⟨pred m.1, (pred_le_self m.1).trans_lt m.2⟩ ?_
      · convert this
        apply Subtype.val_inj.mp
        rw [coe_succ_Iio isSuccLimit_omega0.isSuccPrelimit]
        symm
        change succ (pred m.1) = m.1
        rw [Ordinal.succ_pred_eq_iff_not_isSuccPrelimit]
        intro hpre
        have hmpos : (0 : Ordinal) < m.1 :=
          bot_lt_of_lt <| Subtype.coe_lt_coe.mpr hm
        have hnotmin : ¬ IsMin m.1 := fun hmin ↦
          hmpos.ne (isMin_iff_eq_bot.mp hmin).symm
        exact (not_lt_of_ge (omega0_le_of_isSuccLimit ⟨hnotmin, hpre⟩)) m.2
      rw [← Subtype.coe_lt_coe]
      apply Ordinal.lt_pred_iff_succ_lt.mpr
      rwa [← coe_succ_Iio isSuccLimit_omega0.isSuccPrelimit]
    exact isAcc_iSup isSuccLimit_omega0 (fun x ↦ (f x).1) hf.2.1 this
  · constructor
    · rw [Ordinal.lt_iSup_iff]
      exact ⟨⟨0, omega0_pos⟩, hf.2.2⟩
    · exact ltκ

theorem IsClub.diagInter {κ : Cardinal.{u}} (hκ : ℵ₀ < κ) (hreg : κ.IsRegular)
    {c : Iio κ.ord → Set Ordinal} (hc : ∀ r, IsClub (c r) κ.ord) : IsClub (Δ c) κ.ord :=
  ⟨isClosedBelow_diagInter (fun x ↦ (hc x).1), isAcc_diagInter hκ hreg hc⟩

end DiagonalIntersection

theorem exists_unbounded_Iio_cof {α : Ordinal} (hlim : IsSuccLimit α) : ∃ S, S ⊆ Iio α ∧ IsAcc α S
    ∧ #S = Cardinal.lift.{u + 1, u} α.cof := by
  obtain ⟨S, hUnb, hCard⟩ := Order.cof_eq (α := Iio α)
  use S
  constructor <;> try constructor
  · exact Subtype.coe_image_subset (Iio α) S
  · rw [isAcc_iff]
    refine ⟨hlim.pos.ne.symm, ?_⟩
    intro β βltα
    obtain ⟨x, hx⟩ := hUnb ⟨succ β, hlim.succ_lt βltα⟩
    exact ⟨x, ⟨⟨x, ⟨hx.1, rfl⟩⟩, ⟨succ_le_iff.mp hx.2, x.2⟩⟩⟩
  · rw [Cardinal.mk_image_eq Subtype.val_injective, hCard, Ordinal.cof_Iio]
    exact (lift_cof α).symm

theorem exists_club_card {o : Ordinal.{u}} (h : IsSuccLimit o) :
    ∃ C : Club o, #C = Cardinal.lift.{u + 1, u} o.cof := by
  obtain ⟨S, hS⟩ := exists_unbounded_Iio_cof h
  let C := S ∪ (derivedSet S)
  use ⟨C, ⟨isClosedBelow_derivedSet o, hS.2.1.mono subset_union_left⟩⟩
  apply (hS.2.2 ▸ mk_le_mk_of_subset subset_union_left).antisymm'
  calc
    #C ≤ #S + #(derivedSet S) := mk_union_le _ _
    _ ≤ #S + #S := by
      simpa [add_comm] using add_le_add_left (mk_derivedSet_le S) #S
    _ = max #S #S := add_eq_max <| by
      rw [hS.2.2, ← lift_aleph0.{u + 1, u}, Cardinal.lift_le]
      exact aleph0_le_cof.mpr h
    _ = #S := max_self _
    _ = Cardinal.lift.{u + 1, u} o.cof := hS.2.2

/-- A set of ordinals is stationary below an ordinal if it intersects every club of it. -/
def IsStationary (S : Set Ordinal) (o : Ordinal) : Prop :=
  ∀ C, IsClub C o → (S ∩ C).Nonempty

theorem IsStationary.inter_Iio {o : Ordinal} {S : Set Ordinal} (hS : IsStationary S o) :
    IsStationary (S ∩ Iio o) o := by
  intro C hC
  convert hS _ hC.inter_Iio using 1
  rw [inter_comm C, inter_assoc]

theorem IsStationary.inter_isClub {o : Ordinal} {S C : Set Ordinal} (hS : IsStationary S o)
    (hC : IsClub C o) : (S ∩ C ∩ (Iio o)).Nonempty := by
  have := hS.inter_Iio C hC
  rwa [inter_assoc, inter_comm C, ← inter_assoc]
