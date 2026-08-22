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

import ErdosProblems.Erdos1165.PreStoppingSpatialLaw
import ErdosProblems.Erdos1165.Upper

/-!
# Lazy/external decomposition for all six HLOZ domino tilings

The four checkerboard tilings support the constant-direction deletion used in
`LazyDecomposition`.  The two column tilings do not: the direction from a site
to its mate depends on the first-coordinate parity of that site.  This file
therefore gives the uniform, state-dependent formulation.  Every lattice site
has a canonical domino base and a unique mate, and a two-step excursion is
removed when it goes to that mate and immediately returns.

The construction is entirely pathwise.  It proves exact clock and local-time
identities for both possible temporal phases, identifies membership in the
external visited set from positive external local time, and turns HLOZ's
`fourPointsSeparated` predicate (together with the already-required
distinctness of the four points) into pairwise distinct domino bases.

There is deliberately no claimed global symmetry from the column tilings to a
checkerboard tiling.  Such a nearest-neighbor lattice symmetry does not exist:
graph automorphisms preserve the checkerboard bipartition, whereas the left
bases of a column tiling occupy both checkerboard classes.
-/

open scoped BigOperators

namespace Erdos1165.TilingLazyDecomposition

open LazyDecomposition

abbrev DominoTiling := Tilings.Tiling

/-- The checkerboard-east tiling used by the original constant-direction
decomposition. -/
def canonicalEastTiling : DominoTiling := .checker 0

/-- Subtraction by a displacement, written in the coordinate convention used
by `Tilings.shift`. -/
def unshift (x d : Point) : Point := (x.1 - d.1, x.2 - d.2)

/-- The displacement from the canonical base to its mate. -/
def tilingDisplacement : DominoTiling → Point
  | .checker d => Tilings.directionVector d
  | .evenColumns | .oddColumns => (1, 0)

/-- Predicate selecting the canonical base endpoint. -/
def IsTilingBase : DominoTiling → Point → Prop
  | .checker _, x => Tilings.checkerEven x = true
  | .evenColumns, x => Tilings.columnEven x = true
  | .oddColumns, x => Tilings.columnEven x = false

instance (t : DominoTiling) (x : Point) : Decidable (IsTilingBase t x) := by
  cases t <;> unfold IsTilingBase <;> infer_instance

/-- The canonical representative of the domino containing `x`.  For a checker
tiling it is the checkerboard-even endpoint; for a column tiling it is the left
endpoint of the selected column parity. -/
def tilingBase (t : DominoTiling) (x : Point) : Point :=
  if IsTilingBase t x then x else unshift x (tilingDisplacement t)

/-- The other endpoint of the unique domino containing `x`. -/
def tilingPartner (t : DominoTiling) (x : Point) : Point :=
  if IsTilingBase t x then Tilings.shift x (tilingDisplacement t)
  else unshift x (tilingDisplacement t)

private lemma checkerEven_unshift_direction_eq_true (x : Point)
    (d : Tilings.CheckerDirection) (hx : Tilings.checkerEven x = false) :
    Tilings.checkerEven (unshift x (Tilings.directionVector d)) = true := by
  rcases x with ⟨x₁, x₂⟩
  fin_cases d <;>
    simp only [Tilings.checkerEven, unshift, Tilings.directionVector,
      beq_eq_false_iff_ne, beq_iff_eq] at hx ⊢ <;>
    omega

private lemma columnEven_unshift_east_eq_false (x : Point)
    (hx : Tilings.columnEven x = true) :
    Tilings.columnEven (unshift x (1, 0)) = false := by
  rcases x with ⟨x₁, x₂⟩
  simp only [Tilings.columnEven, beq_iff_eq] at hx
  simp only [Tilings.columnEven, unshift, beq_eq_false_iff_ne]
  omega

private lemma columnEven_unshift_east_eq_true (x : Point)
    (hx : Tilings.columnEven x = false) :
    Tilings.columnEven (unshift x (1, 0)) = true := by
  rcases x with ⟨x₁, x₂⟩
  simp only [Tilings.columnEven, beq_eq_false_iff_ne] at hx
  simp only [Tilings.columnEven, unshift, beq_iff_eq]
  omega

private lemma columnEven_shift_east_eq_false (x : Point)
    (hx : Tilings.columnEven x = true) :
    Tilings.columnEven (Tilings.shift x (1, 0)) = false := by
  rcases x with ⟨x₁, x₂⟩
  simp only [Tilings.columnEven, beq_iff_eq] at hx
  simp only [Tilings.columnEven, Tilings.shift, beq_eq_false_iff_ne]
  omega

private lemma columnEven_shift_east_eq_true (x : Point)
    (hx : Tilings.columnEven x = false) :
    Tilings.columnEven (Tilings.shift x (1, 0)) = true := by
  rcases x with ⟨x₁, x₂⟩
  simp only [Tilings.columnEven, beq_eq_false_iff_ne] at hx
  simp only [Tilings.columnEven, Tilings.shift, beq_iff_eq]
  omega

private theorem isTilingBase_shift {t : DominoTiling} {x : Point}
    (hx : IsTilingBase t x) :
    ¬IsTilingBase t (Tilings.shift x (tilingDisplacement t)) := by
  cases t with
  | checker d =>
      intro h
      change Tilings.checkerEven (Tilings.shift x (Tilings.directionVector d)) = true at h
      rw [Tilings.checkerEven_shift_direction_eq_false x d hx] at h
      contradiction
  | evenColumns =>
      intro h
      change Tilings.columnEven (Tilings.shift x (1, 0)) = true at h
      rw [columnEven_shift_east_eq_false x hx] at h
      contradiction
  | oddColumns =>
      intro h
      change Tilings.columnEven (Tilings.shift x (1, 0)) = false at h
      rw [columnEven_shift_east_eq_true x hx] at h
      contradiction

private theorem isTilingBase_unshift {t : DominoTiling} {x : Point}
    (hx : ¬IsTilingBase t x) :
    IsTilingBase t (unshift x (tilingDisplacement t)) := by
  cases t with
  | checker d =>
      apply checkerEven_unshift_direction_eq_true x d
      exact Bool.eq_false_of_not_eq_true hx
  | evenColumns =>
      apply columnEven_unshift_east_eq_true x
      exact Bool.eq_false_of_not_eq_true hx
  | oddColumns =>
      apply columnEven_unshift_east_eq_false x
      exact Bool.eq_true_of_not_eq_false hx

@[simp] private theorem shift_unshift (x d : Point) :
    Tilings.shift (unshift x d) d = x := by
  rcases x with ⟨x₁, x₂⟩
  rcases d with ⟨d₁, d₂⟩
  simp [Tilings.shift, unshift]

@[simp] private theorem unshift_shift (x d : Point) :
    unshift (Tilings.shift x d) d = x := by
  rcases x with ⟨x₁, x₂⟩
  rcases d with ⟨d₁, d₂⟩
  simp [Tilings.shift, unshift]

theorem tilingBase_partner (t : DominoTiling) (x : Point) :
    tilingBase t (tilingPartner t x) = tilingBase t x := by
  by_cases hx : IsTilingBase t x
  · have hm := isTilingBase_shift hx
    simp [tilingBase, tilingPartner, hx, hm]
  · have hm := isTilingBase_unshift hx
    simp [tilingBase, tilingPartner, hx, hm]

theorem tilingPartner_partner (t : DominoTiling) (x : Point) :
    tilingPartner t (tilingPartner t x) = x := by
  by_cases hx : IsTilingBase t x
  · have hm := isTilingBase_shift hx
    simp [tilingPartner, hx, hm]
  · have hm := isTilingBase_unshift hx
    simp [tilingPartner, hx, hm]

theorem tilingPartner_ne (t : DominoTiling) (x : Point) : tilingPartner t x ≠ x := by
  intro h
  by_cases hx : IsTilingBase t x
  · have hn : ¬IsTilingBase t (tilingPartner t x) := by
      simpa [tilingPartner, hx] using isTilingBase_shift hx
    exact (h ▸ hn) hx
  · have hp : IsTilingBase t (tilingPartner t x) := by
      simpa [tilingPartner, hx] using isTilingBase_unshift hx
    exact hx (h ▸ hp)

private theorem sameDomino_iff_base_oriented (t : DominoTiling) (x y : Point) :
    Tilings.sameDomino t x y ↔
      (IsTilingBase t x ∧ y = Tilings.shift x (tilingDisplacement t)) ∨
      (IsTilingBase t y ∧ x = Tilings.shift y (tilingDisplacement t)) := by
  cases t <;> rfl

theorem sameDomino_iff_partner_eq (t : DominoTiling) (x y : Point) :
    Tilings.sameDomino t x y ↔ tilingPartner t x = y := by
  rw [sameDomino_iff_base_oriented]
  by_cases hx : IsTilingBase t x
  · simp only [tilingPartner, if_pos hx]
    constructor
    · rintro (⟨_, rfl⟩ | ⟨hy, hxy⟩)
      · rfl
      · have hnot := isTilingBase_shift hy
        exact (hnot (hxy ▸ hx)).elim
    · intro h
      exact Or.inl ⟨hx, h.symm⟩
  · have hb := isTilingBase_unshift hx
    simp only [tilingPartner, if_neg hx]
    constructor
    · rintro (⟨hxb, _⟩ | ⟨hy, hxy⟩)
      · exact (hx hxb).elim
      · rw [hxy, unshift_shift]
    · intro h
      right
      refine ⟨h ▸ hb, ?_⟩
      rw [← h, shift_unshift]

theorem point_eq_tilingBase_or_partner_base (t : DominoTiling) (x : Point) :
    x = tilingBase t x ∨ x = tilingPartner t (tilingBase t x) := by
  by_cases hx : IsTilingBase t x
  · left
    simp [tilingBase, hx]
  · right
    have hb := isTilingBase_unshift hx
    simp [tilingBase, tilingPartner, hx, hb]

theorem tilingBase_eq_iff (t : DominoTiling) (x y : Point) :
    tilingBase t x = tilingBase t y ↔ x = y ∨ Tilings.sameDomino t x y := by
  constructor
  · intro hbase
    rcases point_eq_tilingBase_or_partner_base t x with hx | hx <;>
      rcases point_eq_tilingBase_or_partner_base t y with hy | hy
    · left; rw [hx, hy, hbase]
    · right
      rw [sameDomino_iff_partner_eq, hx, hy, hbase]
    · right
      rw [sameDomino_iff_partner_eq, hx, hy, hbase, tilingPartner_partner]
    · left; rw [hx, hy, hbase]
  · rintro (rfl | hdom)
    · rfl
    · rw [sameDomino_iff_partner_eq] at hdom
      rw [← hdom, tilingBase_partner]

theorem tilingBase_ne_of_ne_of_not_sameDomino {t : DominoTiling} {x y : Point}
    (hxy : x ≠ y) (hdom : ¬Tilings.sameDomino t x y) :
    tilingBase t x ≠ tilingBase t y := by
  simpa [tilingBase_eq_iff] using not_or_intro hxy hdom

/-! ## Compatibility with the nearest-neighbor increment law -/

/-- Reversal of a cardinal direction. -/
def oppositeDirection : Direction → Direction
  | 0 => 1
  | 1 => 0
  | 2 => 3
  | 3 => 2

/-- The unique direction from a site to its mate.  It is state-dependent for
the two column tilings. -/
def tilingPartnerDirection : DominoTiling → Point → Direction
  | .checker d, x => if IsTilingBase (.checker d) x then d else oppositeDirection d
  | .evenColumns, x => if IsTilingBase .evenColumns x then 0 else 1
  | .oddColumns, x => if IsTilingBase .oddColumns x then 0 else 1

theorem tilingPartner_eq_add_directionVector (t : DominoTiling) (x : Point) :
    tilingPartner t x = x + directionVector (tilingPartnerDirection t x) := by
  cases t with
  | checker d =>
      by_cases hx : IsTilingBase (.checker d) x
      · simp only [tilingPartner, tilingPartnerDirection, hx, if_pos,
          tilingDisplacement]
        rcases x with ⟨x₁, x₂⟩
        fin_cases d <;> simp [Tilings.shift, Tilings.directionVector, directionVector]
      · simp only [tilingPartner, tilingPartnerDirection, hx,
          tilingDisplacement]
        rcases x with ⟨x₁, x₂⟩
        fin_cases d <;>
          simp [unshift, Tilings.directionVector, oppositeDirection, directionVector,
            sub_eq_add_neg]
  | evenColumns =>
      by_cases hx : IsTilingBase .evenColumns x <;>
        rcases x with ⟨x₁, x₂⟩ <;>
        simp [tilingPartner, tilingPartnerDirection, tilingDisplacement, hx,
          Tilings.shift, unshift, directionVector, sub_eq_add_neg]
  | oddColumns =>
      by_cases hx : IsTilingBase .oddColumns x <;>
        rcases x with ⟨x₁, x₂⟩ <;>
        simp [tilingPartner, tilingPartnerDirection, tilingDisplacement, hx,
          Tilings.shift, unshift, directionVector, sub_eq_add_neg]

/-- Thus every state-dependent mate is reached by exactly one of the four
equiprobable increments of `fairStep`. -/
theorem existsUnique_direction_to_tilingPartner (t : DominoTiling) (x : Point) :
    ∃! d : Direction, tilingPartner t x = x + directionVector d := by
  refine ⟨tilingPartnerDirection t x, tilingPartner_eq_add_directionVector t x, ?_⟩
  intro d hd
  apply directionVector_injective
  apply add_left_cancel (a := x)
  rw [← hd, tilingPartner_eq_add_directionVector]

/-! ## Uniform state-dependent deletion -/

/-- A removable two-step return along the domino containing its initial site. -/
def TilingRemovable (t : DominoTiling) (a b c : Point) : Prop :=
  b = tilingPartner t a ∧ c = a

instance (t : DominoTiling) (a b c : Point) : Decidable (TilingRemovable t a b c) :=
  by unfold TilingRemovable; infer_instance

theorem TilingRemovable.sameDomino {t : DominoTiling} {a b c : Point}
    (h : TilingRemovable t a b c) : Tilings.sameDomino t a b := by
  rw [sameDomino_iff_partner_eq]
  exact h.1.symm

theorem TilingRemovable.base_eq {t : DominoTiling} {a b c : Point}
    (h : TilingRemovable t a b c) : tilingBase t a = tilingBase t b := by
  rw [h.1, tilingBase_partner]

def tilingCompressTail (t : DominoTiling) (a : Point) : List Point → List Point
  | [] => []
  | [b] => [b]
  | b :: c :: rest =>
      if TilingRemovable t a b c then tilingCompressTail t c rest
      else b :: c :: tilingCompressTail t c rest

def tilingRemovedTail (t : DominoTiling) (a : Point) : List Point → List Point
  | [] => []
  | [_] => []
  | b :: c :: rest =>
      if TilingRemovable t a b c then b :: c :: tilingRemovedTail t c rest
      else tilingRemovedTail t c rest

def tilingExternalPath (t : DominoTiling) : List Point → List Point
  | [] => []
  | a :: rest => a :: tilingCompressTail t a rest

def tilingLazyPoints (t : DominoTiling) : List Point → List Point
  | [] => []
  | a :: rest => tilingRemovedTail t a rest

def tilingRemovedExcursionsTail (t : DominoTiling) (a : Point) : List Point → ℕ
  | [] => 0
  | [_] => 0
  | b :: c :: rest =>
      if TilingRemovable t a b c then 1 + tilingRemovedExcursionsTail t c rest
      else tilingRemovedExcursionsTail t c rest

def tilingRemovedExcursions (t : DominoTiling) : List Point → ℕ
  | [] => 0
  | a :: rest => tilingRemovedExcursionsTail t a rest

lemma tilingCompressTail_length_add_removedTail_length (t : DominoTiling) (a : Point) :
    ∀ rest : List Point,
      (tilingCompressTail t a rest).length + (tilingRemovedTail t a rest).length =
        rest.length := by
  intro rest
  induction rest using List.twoStepInduction generalizing a with
  | nil => simp [tilingCompressTail, tilingRemovedTail]
  | singleton b => simp [tilingCompressTail, tilingRemovedTail]
  | cons_cons b c rest ih _ =>
      simp only [tilingCompressTail, tilingRemovedTail]
      split_ifs <;> simp only [List.length_cons] <;> specialize ih c <;> omega

lemma tilingRemovedTail_length (t : DominoTiling) (a : Point) :
    ∀ rest : List Point,
      (tilingRemovedTail t a rest).length =
        2 * tilingRemovedExcursionsTail t a rest := by
  intro rest
  induction rest using List.twoStepInduction generalizing a with
  | nil => simp [tilingRemovedTail, tilingRemovedExcursionsTail]
  | singleton b => simp [tilingRemovedTail, tilingRemovedExcursionsTail]
  | cons_cons b c rest ih _ =>
      simp only [tilingRemovedTail, tilingRemovedExcursionsTail]
      split_ifs
      · specialize ih c
        simp only [List.length_cons]
        omega
      · exact ih c

theorem tilingExternalPath_length_add_lazyPoints_length (t : DominoTiling)
    (p : List Point) :
    (tilingExternalPath t p).length + (tilingLazyPoints t p).length = p.length := by
  cases p with
  | nil => simp [tilingExternalPath, tilingLazyPoints]
  | cons a rest =>
      have h := tilingCompressTail_length_add_removedTail_length t a rest
      simp only [tilingExternalPath, tilingLazyPoints, List.length_cons]
      omega

theorem tilingLazyPoints_length (t : DominoTiling) (p : List Point) :
    (tilingLazyPoints t p).length = 2 * tilingRemovedExcursions t p := by
  cases p with
  | nil => simp [tilingLazyPoints, tilingRemovedExcursions]
  | cons a rest =>
      simpa [tilingLazyPoints, tilingRemovedExcursions] using
        tilingRemovedTail_length t a rest

def tilingExternalClock (t : DominoTiling) (p : List Point) : ℕ :=
  (tilingExternalPath t p).length - 1

lemma tilingExternalPath_nonempty (t : DominoTiling) {p : List Point} (hp : p ≠ []) :
    tilingExternalPath t p ≠ [] := by
  cases p with
  | nil => contradiction
  | cons a rest => simp [tilingExternalPath]

theorem tilingExternalClock_eq (t : DominoTiling) {p : List Point} (hp : p ≠ []) :
    tilingExternalClock t p + 2 * tilingRemovedExcursions t p = p.length - 1 := by
  have hext : 0 < (tilingExternalPath t p).length :=
    Nat.pos_of_ne_zero (by simpa using tilingExternalPath_nonempty t hp)
  have hlen := tilingExternalPath_length_add_lazyPoints_length t p
  have hlazy := tilingLazyPoints_length t p
  unfold tilingExternalClock
  omega

lemma count_tilingCompressTail_add_count_tilingRemovedTail
    (t : DominoTiling) (a x : Point) : ∀ rest : List Point,
    rest.count x = (tilingCompressTail t a rest).count x +
      (tilingRemovedTail t a rest).count x := by
  intro rest
  induction rest using List.twoStepInduction generalizing a with
  | nil => simp [tilingCompressTail, tilingRemovedTail]
  | singleton b => simp [tilingCompressTail, tilingRemovedTail]
  | cons_cons b c rest ih _ =>
      simp only [tilingCompressTail, tilingRemovedTail]
      split_ifs <;> simp only [List.count_cons] <;> specialize ih c <;> omega

/-- Exact local-time splitting for every one of HLOZ's six tilings. -/
theorem tilingListLocalTime_split (t : DominoTiling) (p : List Point) (x : Point) :
    listLocalTime p x = listLocalTime (tilingExternalPath t p) x +
      listLocalTime (tilingLazyPoints t p) x := by
  cases p with
  | nil => simp [listLocalTime, tilingExternalPath, tilingLazyPoints]
  | cons a rest =>
      have h := count_tilingCompressTail_add_count_tilingRemovedTail t a x rest
      simp only [listLocalTime, tilingExternalPath, tilingLazyPoints, List.count_cons]
      omega

/-! ## Both temporal phases and path prefixes -/

/-- Input list for the selected two-step temporal phase. -/
def phasedInput (o : Orientation) : List Point → List Point
  | [] => []
  | a :: rest => match o with
    | .even => a :: rest
    | .shifted => rest

/-- The time-zero contribution omitted by the shifted input. -/
def phasedBoundaryLocalTime (o : Orientation) (p : List Point) (x : Point) : ℕ :=
  match o, p with
  | .even, _ => 0
  | .shifted, [] => 0
  | .shifted, a :: _ => if a = x then 1 else 0

def phasedExternalLocalTime (t : DominoTiling) (o : Orientation)
    (p : List Point) (x : Point) : ℕ :=
  listLocalTime (tilingExternalPath t (phasedInput o p)) x

def phasedLazyLocalTime (t : DominoTiling) (o : Orientation)
    (p : List Point) (x : Point) : ℕ :=
  listLocalTime (tilingLazyPoints t (phasedInput o p)) x

def phasedExternalVisitedSites (t : DominoTiling) (o : Orientation)
    (p : List Point) : Finset Point :=
  (tilingExternalPath t (phasedInput o p)).toFinset

/-- Unified exact boundary/external/lazy identity. -/
theorem listLocalTime_eq_phasedBoundary_add_external_add_lazy
    (t : DominoTiling) (o : Orientation) (p : List Point) (x : Point) :
    listLocalTime p x = phasedBoundaryLocalTime o p x +
      phasedExternalLocalTime t o p x + phasedLazyLocalTime t o p x := by
  cases o with
  | even =>
      cases p with
      | nil => simpa [phasedInput, phasedBoundaryLocalTime, phasedExternalLocalTime,
          phasedLazyLocalTime] using tilingListLocalTime_split t [] x
      | cons a rest =>
          simpa [phasedInput, phasedBoundaryLocalTime, phasedExternalLocalTime,
            phasedLazyLocalTime] using tilingListLocalTime_split t (a :: rest) x
  | shifted =>
      cases p with
      | nil => simp [listLocalTime, phasedInput, phasedBoundaryLocalTime,
          phasedExternalLocalTime, phasedLazyLocalTime, tilingExternalPath,
          tilingLazyPoints]
      | cons a rest =>
          have h := tilingListLocalTime_split t rest x
          unfold listLocalTime at h
          simp only [listLocalTime, List.count_cons, phasedInput,
            phasedBoundaryLocalTime, phasedExternalLocalTime, phasedLazyLocalTime]
          split_ifs <;> simp_all <;> omega

theorem mem_phasedExternalVisitedSites_of_pos
    {t : DominoTiling} {o : Orientation} {p : List Point} {x : Point}
    (hx : 0 < phasedExternalLocalTime t o p x) :
    x ∈ phasedExternalVisitedSites t o p := by
  rw [phasedExternalVisitedSites, List.mem_toFinset, ← List.count_pos_iff]
  exact hx

def pathPhasedBoundaryLocalTime (o : Orientation) (s : WalkPath) (n : ℕ)
    (x : Point) : ℕ :=
  phasedBoundaryLocalTime o (finitePathList (pathPrefix s n)) x

def pathPhasedExternalLocalTime (t : DominoTiling) (o : Orientation)
    (s : WalkPath) (n : ℕ) (x : Point) : ℕ :=
  phasedExternalLocalTime t o (finitePathList (pathPrefix s n)) x

def pathPhasedLazyLocalTime (t : DominoTiling) (o : Orientation)
    (s : WalkPath) (n : ℕ) (x : Point) : ℕ :=
  phasedLazyLocalTime t o (finitePathList (pathPrefix s n)) x

def pathPhasedExternalVisitedSites (t : DominoTiling) (o : Orientation)
    (s : WalkPath) (n : ℕ) : Finset Point :=
  phasedExternalVisitedSites t o (finitePathList (pathPrefix s n))

theorem localTime_eq_phasedBoundary_add_external_add_lazy
    (t : DominoTiling) (o : Orientation) (s : WalkPath) (n : ℕ) (x : Point) :
    localTime s n x = pathPhasedBoundaryLocalTime o s n x +
      pathPhasedExternalLocalTime t o s n x +
      pathPhasedLazyLocalTime t o s n x := by
  rw [localTime, localTimePrefix, finiteLocalTime_eq_listLocalTime]
  exact listLocalTime_eq_phasedBoundary_add_external_add_lazy t o _ x

theorem mem_pathPhasedExternalVisitedSites_of_pos
    {t : DominoTiling} {o : Orientation} {s : WalkPath} {n : ℕ} {x : Point}
    (hx : 0 < pathPhasedExternalLocalTime t o s n x) :
    x ∈ pathPhasedExternalVisitedSites t o s n :=
  mem_phasedExternalVisitedSites_of_pos hx

/-- The arithmetic step used by a thick-point screen: after bounding the
boundary and lazy contributions, a large actual local time forces a large
external local time.  The cutoff `n` may itself later be specialized to any
path-dependent stopping clock. -/
theorem pathPhasedExternalLocalTime_lower_bound_of_boundary_lazy_cap
    {t : DominoTiling} {o : Orientation} {s : WalkPath} {n : ℕ}
    {site : Point} {cap externalThreshold : ℕ}
    (hcap : pathPhasedBoundaryLocalTime o s n site +
      pathPhasedLazyLocalTime t o s n site ≤ cap)
    (hlarge : cap + externalThreshold ≤ localTime s n site) :
    externalThreshold ≤ pathPhasedExternalLocalTime t o s n site := by
  have hsplit := localTime_eq_phasedBoundary_add_external_add_lazy t o s n site
  omega

theorem mem_pathPhasedExternalVisitedSites_of_lazy_cap
    {t : DominoTiling} {o : Orientation} {s : WalkPath} {n : ℕ}
    {site : Point} {cap externalThreshold : ℕ}
    (hthreshold : 0 < externalThreshold)
    (hcap : pathPhasedBoundaryLocalTime o s n site +
      pathPhasedLazyLocalTime t o s n site ≤ cap)
    (hlarge : cap + externalThreshold ≤ localTime s n site) :
    site ∈ pathPhasedExternalVisitedSites t o s n := by
  apply mem_pathPhasedExternalVisitedSites_of_pos
  exact hthreshold.trans_le
    (pathPhasedExternalLocalTime_lower_bound_of_boundary_lazy_cap hcap hlarge)

/-! ## Separation of distinguished favorite dominoes -/

/-- The canonical domino bases of the favorite sites at a fixed time. -/
noncomputable def favoriteTilingBases (t : DominoTiling) (s : WalkPath) (n : ℕ) :
    Finset Point := (favoriteSites s n).image (tilingBase t)

theorem mem_favoriteTilingBases {t : DominoTiling} {s : WalkPath} {n : ℕ}
    {x : Point} (hx : x ∈ favoriteSites s n) :
    tilingBase t x ∈ favoriteTilingBases t s n := by
  exact Finset.mem_image.mpr ⟨x, hx, rfl⟩

/-- A site separated from every current favorite lies outside every current
favorite domino. -/
theorem tilingBase_not_mem_favoriteTilingBases
    {t : DominoTiling} {s : WalkPath} {n : ℕ} {x : Point}
    (hsep : ∀ y ∈ favoriteSites s n, x ≠ y ∧ ¬Tilings.sameDomino t x y) :
    tilingBase t x ∉ favoriteTilingBases t s n := by
  intro hx
  rw [favoriteTilingBases, Finset.mem_image] at hx
  obtain ⟨y, hyfav, hy⟩ := hx
  exact tilingBase_ne_of_ne_of_not_sameDomino (hsep y hyfav).1
    (hsep y hyfav).2 hy.symm

theorem fourPointsSeparated_tilingBases
    {t : DominoTiling} {a b c d : Point}
    (hsep : fourPointsSeparated t a b c d)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    tilingBase t a ≠ tilingBase t b ∧ tilingBase t a ≠ tilingBase t c ∧
      tilingBase t a ≠ tilingBase t d ∧ tilingBase t b ≠ tilingBase t c ∧
      tilingBase t b ≠ tilingBase t d ∧ tilingBase t c ≠ tilingBase t d := by
  rcases hsep with ⟨habd, hacd, hadd, hbcd, hbdd, hcdd⟩
  exact ⟨tilingBase_ne_of_ne_of_not_sameDomino hab habd,
    tilingBase_ne_of_ne_of_not_sameDomino hac hacd,
    tilingBase_ne_of_ne_of_not_sameDomino had hadd,
    tilingBase_ne_of_ne_of_not_sameDomino hbc hbcd,
    tilingBase_ne_of_ne_of_not_sameDomino hbd hbdd,
    tilingBase_ne_of_ne_of_not_sameDomino hcd hcdd⟩

/-! ## Compatibility with the original canonical-east implementation -/

theorem isTilingBase_canonicalEast_iff_evenPoint (x : Point) :
    IsTilingBase canonicalEastTiling x ↔ EvenPoint x := by
  rcases x with ⟨x₁, x₂⟩
  simp only [IsTilingBase, canonicalEastTiling, EvenPoint, pointParity,
    ← Int.cast_add]
  change ((x₁ + x₂) % 2 == 0) = true ↔
    ((x₁ + x₂ : ℤ) : ZMod 2) = 0
  rw [beq_iff_eq, ZMod.intCast_zmod_eq_zero_iff_dvd, Int.dvd_iff_emod_eq_zero]
  norm_num

private theorem evenPoint_not_oddPoint {x : Point} (hx : EvenPoint x) : ¬OddPoint x := by
  intro hodd
  rw [OddPoint, hx] at hodd
  exact zero_ne_one hodd

private theorem oddPoint_not_evenPoint {x : Point} (hx : OddPoint x) : ¬EvenPoint x := by
  intro heven
  rw [EvenPoint, hx] at heven
  exact one_ne_zero heven

theorem even_dominoBase_eq_tilingBase (x : Point) :
    PreStoppingSpatialLaw.dominoBase .even x = tilingBase canonicalEastTiling x := by
  by_cases hx : EvenPoint x
  · have hb : IsTilingBase canonicalEastTiling x :=
      (isTilingBase_canonicalEast_iff_evenPoint x).2 hx
    simp [PreStoppingSpatialLaw.dominoBase, tilingBase, hx, hb]
  · have hb : ¬IsTilingBase canonicalEastTiling x :=
      mt (isTilingBase_canonicalEast_iff_evenPoint x).1 hx
    rcases x with ⟨x₁, x₂⟩
    simp only [canonicalEastTiling] at hb
    simp [PreStoppingSpatialLaw.dominoBase, tilingBase, canonicalEastTiling,
      tilingDisplacement, Tilings.directionVector, hx, hb, e₁, unshift]

theorem shifted_dominoBase_eq_shift_tilingBase (x : Point) :
    PreStoppingSpatialLaw.dominoBase .shifted x =
      Tilings.shift (tilingBase canonicalEastTiling x) (1, 0) := by
  rcases PreStoppingSpatialLaw.evenPoint_or_oddPoint x with hx | hx
  · have hnotOdd := evenPoint_not_oddPoint hx
    have hb : IsTilingBase canonicalEastTiling x :=
      (isTilingBase_canonicalEast_iff_evenPoint x).2 hx
    rcases x with ⟨x₁, x₂⟩
    simp only [canonicalEastTiling] at hb
    simp [PreStoppingSpatialLaw.dominoBase, tilingBase, hnotOdd, hb,
      canonicalEastTiling, Tilings.shift, e₁]
  · have hnotEven := oddPoint_not_evenPoint hx
    have hb : ¬IsTilingBase canonicalEastTiling x :=
      mt (isTilingBase_canonicalEast_iff_evenPoint x).1 hnotEven
    rcases x with ⟨x₁, x₂⟩
    simp only [canonicalEastTiling] at hb
    simp [PreStoppingSpatialLaw.dominoBase, tilingBase, canonicalEastTiling,
      tilingDisplacement, Tilings.directionVector, hx, hb, Tilings.shift, unshift]

private theorem shift_right_injective (d : Point) :
    Function.Injective (fun x ↦ Tilings.shift x d) := by
  rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ h
  simp only [Tilings.shift, Prod.mk.injEq] at h ⊢
  omega

/-- Corrected canonical-east consumer lemma.  Distinctness is necessary:
`sameDomino t x x` is false, while the two bases are of course equal. -/
theorem dominoBase_ne_of_not_sameDomino_canonicalEast
    (o : Orientation) {x y : Point} (hxy : x ≠ y)
    (hdom : ¬Tilings.sameDomino canonicalEastTiling x y) :
    PreStoppingSpatialLaw.dominoBase o x ≠
      PreStoppingSpatialLaw.dominoBase o y := by
  have hbase := tilingBase_ne_of_ne_of_not_sameDomino hxy hdom
  cases o with
  | even => simpa [even_dominoBase_eq_tilingBase] using hbase
  | shifted =>
      rw [shifted_dominoBase_eq_shift_tilingBase,
        shifted_dominoBase_eq_shift_tilingBase]
      exact fun h ↦ hbase (shift_right_injective (1, 0) h)

end Erdos1165.TilingLazyDecomposition
