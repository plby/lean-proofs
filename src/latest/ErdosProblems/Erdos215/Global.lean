import ErdosProblems.Erdos215.RationalLattice
import ErdosProblems.Erdos215.PoolGeometry
import ErdosProblems.Erdos215.Selector
import ErdosProblems.Erdos215.CircleWrapper
import ErdosProblems.Erdos215.Davies

/-!
# The terminal and global recursions for Erdős Problem 215

This file contains the order-theoretic part of the Jackson--Mauldin
construction.  In particular, `globalOfStageExtension` is the genuine
well-founded union argument: it does not assume that initial segments of the
continuum are countable.

The geometric work at one countable terminal layer is isolated by the exact
predicates below.  They deliberately mention the selected sets, the rational
translate hitting property, and every old--new distance condition.  Thus the
outer recursion cannot manufacture either hitting or separation from a
weaker or vacuous hypothesis.
-/

namespace Erdos215

open Set

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

namespace Global

/-- A set meets every rational translate of the integer lattice in the frame
`L`. -/
def HitsRationalTranslates (S : Set Point) (L : OrientedFrame) : Prop :=
  ∀ q : RatPoint, (S ∩ L.rationalTranslate q).Nonempty

/-- A set meets the lattice of every frame rationally equivalent to `L`.
This is the form consumed by the outer Davies recursion. -/
def HitsRationalClass (S : Set Point) (L : OrientedFrame) : Prop :=
  ∀ K : OrientedFrame, K.RationallyEquivalent L →
    ∃ p : Point, p ∈ S ∧ K.IsLatticePoint p

/-- A rich pool in the coordinates of `L`.  The formulation is the literal
rank-two residue condition (4.1): every residue sublattice in every rational
translate contributes infinitely many ambient points. -/
def FrameRich (L : OrientedFrame) (P : Set Point) : Prop :=
  ∀ (d : ℕ), d ≠ 0 → ∀ (i j : Fin d) (a b : ℤ),
    Set.Infinite {x : Point | ∃ k l : ℤ,
      x = L.fromCoords
        (ratPoint (fun r ↦ if r = 0 then (i : ℕ) / d + k else (j : ℕ) / d + l)) ∧
      a ≡ k [ZMOD d] ∧ b ≡ l [ZMOD d] ∧ x ∈ P}

/-- The exact rich-selector theorem required from the arithmetic component.
The optional distinguished point is the `w` of Section 4.  When it is
present it must be selected; partiality then separates it from all other
selected points. -/
def RichSelectorTheorem : Prop :=
  ∀ (L : OrientedFrame) (P : Set Point), FrameRich L P →
    (∀ x ∈ P, L.IsRational x) →
    ∀ w : Option Point, (∀ x, w = some x → x ∈ P) →
      ∃ T : Set Point,
        T ⊆ P ∧
        IsPartialSteinhaus T ∧
        HitsRationalTranslates T L ∧
        ∀ x, w = some x → x ∈ T

/-- The exact three-circle finiteness alternative.  This is intentionally
the component theorem itself, rather than the later finite-forbidden-lines
conclusion.  `target` is a labelled triangle and `center` the labelled circle
centres. -/
def ThreeCircleFinitenessTheorem : Prop :=
  ∀ (center target : Fin 3 → Point) (radiusSq : Fin 3 → ℝ),
    Function.Injective center →
    Function.Injective target →
    (∀ i, 0 < radiusSq i) →
    (Set.Finite {z : Fin 3 → Point |
      (∀ i, distSq (center i) (z i) = radiusSq i) ∧
      ∀ i j, distSq (z i) (z j) = distSq (target i) (target j)}) ∨
      (∀ i j, radiusSq i = radiusSq j) ∧
        ∀ i j, distSq (center i) (center j) = distSq (target i) (target j)

theorem threeCircleFiniteness : ThreeCircleFinitenessTheorem := by
  simpa only [ThreeCircleFinitenessTheorem] using Erdos215.threeCircleFiniteness

/-! ## The coded Skolem universe used by the Davies decomposition -/

/-- The finite data that are baked into one three-circle Skolem operation.
The operation's only run-time parameters are the three centres. -/
structure CircleDatum where
  radiusSq : Fin 3 → ℚ
  targetSq : Fin 3 → Fin 3 → ℤ
  deriving Nonempty, Countable

/-- The labelled configurations associated to a datum and three centres. -/
def circleConfigurations (d : CircleDatum) (center : Fin 3 → Point) :
    Set (Fin 3 → Point) :=
  {z | (∀ i, distSq (center i) (z i) = (d.radiusSq i : ℝ)) ∧
    ∀ i j, distSq (z i) (z j) = (d.targetSq i j : ℝ)}

/-- A one-sorted universe containing exactly the sorts on which the global
argument invokes Skolem closure. -/
inductive Code where
  | point : Point → Code
  | frame : OrientedFrame → Code
  | latticeClass : OrientedFrame.RationalClass → Code
  | configurations : Finset (Fin 3 → Point) → Code
  | default : Code

namespace Code

def standardFrame : OrientedFrame where
  origin := 0
  c := 1
  s := 0
  unit := by norm_num

/-- The class uniquely recovered from two common rational points, totalized
by the standard class when no witness exists. -/
noncomputable def recoveredClass (x y : Point) : OrientedFrame.RationalClass :=
  by
    classical
    exact if h : ∃ L : OrientedFrame,
      x ≠ y ∧ L.IsRational x ∧ L.IsRational y then
      OrientedFrame.classOf (Classical.choose h)
    else OrientedFrame.classOf standardFrame

theorem recoveredClass_eq {L : OrientedFrame} {x y : Point} (hxy : x ≠ y)
    (hx : L.IsRational x) (hy : L.IsRational y) :
    recoveredClass x y = OrientedFrame.classOf L := by
  have h : ∃ K : OrientedFrame,
      x ≠ y ∧ K.IsRational x ∧ K.IsRational y := ⟨L, hxy, hx, hy⟩
  rw [recoveredClass, dif_pos h]
  let K := Classical.choose h
  have hK := Classical.choose_spec h
  exact OrientedFrame.class_eq_of_two_common hxy hK.2.1 hx hK.2.2 hy

/-- Turn a finite set into a `Finset`, with a total default in the infinite
case. -/
noncomputable def finiteCode {X : Type} [DecidableEq X] (s : Set X) : Finset X :=
  by
    classical
    exact if h : s.Finite then h.toFinset else ∅

theorem mem_finiteCode_iff {X : Type} [DecidableEq X] {s : Set X}
    (hs : s.Finite) (x : X) : x ∈ finiteCode s ↔ x ∈ s := by
  simp [finiteCode, hs]

/-- A canonical (choice-dependent) enumeration of a nonempty position in a
finset.  The natural index is exactly the parameter-free integer baked into
the second D6 application in Claim 2.7. -/
noncomputable def nthConfiguration (F : Finset (Fin 3 → Point)) (k : ℕ) :
    Fin 3 → Point :=
  if hk : k < F.card then
    ((Fintype.equivFin {z // z ∈ F}).symm
      ⟨k, by simpa only [Fintype.card_coe] using hk⟩).1
  else fun _ ↦ 0

theorem nthConfiguration_mem (F : Finset (Fin 3 → Point)) (k : ℕ)
    (hk : k < F.card) : nthConfiguration F k ∈ F := by
  simp only [nthConfiguration, dif_pos hk]
  exact ((Fintype.equivFin {z // z ∈ F}).symm
    ⟨k, by simpa only [Fintype.card_coe] using hk⟩).2

theorem exists_nthConfiguration_eq (F : Finset (Fin 3 → Point))
    {z : Fin 3 → Point} (hz : z ∈ F) :
    ∃ k < F.card, nthConfiguration F k = z := by
  let e := Fintype.equivFin {w // w ∈ F}
  let j := e ⟨z, hz⟩
  have hj : (j : ℕ) < F.card := by
    simpa only [Fintype.card_coe] using j.2
  refine ⟨j, hj, ?_⟩
  rw [nthConfiguration, dif_pos hj]
  exact congrArg Subtype.val (e.symm_apply_apply ⟨z, hz⟩)

/-- A parameter-free enumeration of rational coordinate pairs. -/
noncomputable def ratEnumeration : ℕ → RatPoint :=
  Classical.choose (exists_surjective_nat RatPoint)

theorem ratEnumeration_surjective : Function.Surjective ratEnumeration :=
  Classical.choose_spec (exists_surjective_nat RatPoint)

/-- All baked three-circle numeric data form a countable type. -/
noncomputable def circleDataEnumeration : ℕ → CircleDatum :=
  Classical.choose (exists_surjective_nat CircleDatum)

theorem circleDataEnumeration_surjective :
    Function.Surjective circleDataEnumeration :=
  Classical.choose_spec (exists_surjective_nat CircleDatum)

/-- The countable family of named Skolem operations used by the global
argument.  Odd indices `2*n+3` form finite three-circle solution codes;
even indices `2*k+4` recover a lattice class from the first two entries of
the `k`-th coded configuration. -/
noncomputable def skolem : SkolemFamily Code :=
  fun n xs ↦
    match n, xs with
    | 0, [latticeClass C] => frame (OrientedFrame.representative C)
    | 1, [frame L] => latticeClass (OrientedFrame.classOf L)
    | 2, [point x, point y] => latticeClass (recoveredClass x y)
    | n + 3, [latticeClass C] =>
        point ((OrientedFrame.representative C).fromCoords
          (ratPoint (ratEnumeration n)))
    | n + 3, [point c₀, point c₁, point c₂] =>
        if Odd (n + 3) then
          let d := circleDataEnumeration (n / 2)
          configurations (finiteCode (circleConfigurations d ![c₀, c₁, c₂]))
        else default
    | n + 4, [configurations F] =>
        if Even (n + 4) then
          let z := nthConfiguration F (n / 2)
          latticeClass (recoveredClass (z 0) (z 1))
        else default
    | _, _ => default

@[simp]
theorem skolem_representative (C : OrientedFrame.RationalClass) :
    skolem 0 [latticeClass C] = frame (OrientedFrame.representative C) := rfl

@[simp]
theorem skolem_classOf (L : OrientedFrame) :
    skolem 1 [frame L] = latticeClass (OrientedFrame.classOf L) := rfl

@[simp]
theorem skolem_recover (x y : Point) :
    skolem 2 [point x, point y] = latticeClass (recoveredClass x y) := rfl

@[simp]
theorem skolem_rationalPoint (n : ℕ)
    (C : OrientedFrame.RationalClass) :
    skolem (n + 3) [latticeClass C] =
      point ((OrientedFrame.representative C).fromCoords
        (ratPoint (ratEnumeration n))) := rfl

@[simp]
theorem skolem_circleCode (r : ℕ) (c₀ c₁ c₂ : Point) :
    skolem (2 * r + 3) [point c₀, point c₁, point c₂] =
      configurations (finiteCode (circleConfigurations
        (circleDataEnumeration r) ![c₀, c₁, c₂])) := by
  have hodd : Odd (2 * r + 3) := ⟨r + 1, by omega⟩
  simp [skolem, hodd]

@[simp]
theorem skolem_classFromConfiguration (k : ℕ)
    (F : Finset (Fin 3 → Point)) :
    skolem (2 * k + 4) [configurations F] =
      latticeClass (recoveredClass
        ((nthConfiguration F k) 0) ((nthConfiguration F k) 1)) := by
  have heven : Even (2 * k + 4) := ⟨k + 2, by omega⟩
  simp [skolem, heven]

end Code

/-- The exact circle alternative implies finiteness for a baked rational /
integer datum whenever the exceptional congruence would violate partiality of
the three old centres. -/
theorem circleConfigurations_finite
    (circle : ThreeCircleFinitenessTheorem)
    (d : CircleDatum) (center target : Fin 3 → Point)
    (hcenter : Function.Injective center) (htarget : Function.Injective target)
    (hpositive : ∀ i, 0 < (d.radiusSq i : ℝ))
    (htargetSq : ∀ i j,
      distSq (target i) (target j) = (d.targetSq i j : ℝ))
    {S : Set Point} (hS : IsPartialSteinhaus S)
    (hcenterS : ∀ i, center i ∈ S) :
    (circleConfigurations d center).Finite := by
  rcases circle center target (fun i ↦ (d.radiusSq i : ℝ))
      hcenter htarget hpositive with hfinite | hexception
  · let Q : Set (Fin 3 → Point) :=
      {z | (∀ i, distSq (center i) (z i) = (d.radiusSq i : ℝ)) ∧
        ∀ i j, distSq (z i) (z j) = distSq (target i) (target j)}
    have hset : Q = circleConfigurations d center := by
      ext z
      constructor
      · rintro ⟨hc, ht⟩
        exact ⟨hc, fun i j ↦ (ht i j).trans (htargetSq i j)⟩
      · rintro ⟨hc, ht⟩
        exact ⟨hc, fun i j ↦ (ht i j).trans (htargetSq i j).symm⟩
    rw [← hset]
    exact hfinite
  · exfalso
    have hne : center 0 ≠ center 1 := by
      intro h
      have h01 : (0 : Fin 3) = 1 := hcenter h
      norm_num at h01
    exact hS (hcenterS 0) (hcenterS 1) hne (d.targetSq 0 1)
      ((hexception.2 0 1).trans (htargetSq 0 1))

namespace CodedDavies

variable (D : DaviesDecomposition Code.skolem)

/-- The chosen Davies decomposition of the concrete coded universe. -/
noncomputable def decomposition : DaviesDecomposition Code.skolem :=
  daviesDecomposition Code.skolem

/-- Rational-equivalence classes whose class tags occur in one terminal
layer. -/
def classes (i : D.Index) : Set OrientedFrame.RationalClass :=
  {C | Code.latticeClass C ∈ D.layer i}

theorem classes_countable (i : D.Index) : (classes D i).Countable := by
  apply (D.layer_countable i).preimage
  intro C K h
  injection h

theorem not_mem_before_of_mem_layer {i : D.Index} {a : Code}
    (ha : a ∈ D.layer i) : a ∉ D.before i := by
  intro hb
  rcases hb with ⟨j, hji, hj⟩
  letI : IsWellOrder D.Index D.lt := D.isWellOrder
  have hne : j ≠ i := by
    intro h
    subst j
    exact (irrefl_of D.lt i hji)
  exact Set.disjoint_left.1 (D.layer_disjoint hne) hj ha

/-- If two distinct points in one predecessor guard are rational in `L`, the
class code of `L` is already in the predecessor cut.  This is the first D6
application used both in pool localization and in the one-cross argument. -/
theorem class_mem_before_of_two_points_in_guard
    {i : D.Index} {g : Set Code} (hg : g ∈ D.guards i)
    {L : OrientedFrame} {x y : Point} (hxy : x ≠ y)
    (hxg : Code.point x ∈ g) (hyg : Code.point y ∈ g)
    (hxL : L.IsRational x) (hyL : L.IsRational y) :
    Code.latticeClass (OrientedFrame.classOf L) ∈ D.before i := by
  have hs := D.skolem_mem_before hg 2 [Code.point x, Code.point y] (by
    intro a ha
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
    rcases ha with rfl | rfl
    · exact hxg
    · exact hyg)
  simpa only [Code.skolem_recover, Code.recoveredClass_eq hxy hxL hyL] using hs

/-- First D6 application in the finite-forbidden-lines contradiction: three
centres in one guard put their finite configuration code below the current
layer. -/
theorem circleCode_mem_before
    {i : D.Index} {g : Set Code} (hg : g ∈ D.guards i)
    (d : CircleDatum) (c₀ c₁ c₂ : Point)
    (hc₀ : Code.point c₀ ∈ g) (hc₁ : Code.point c₁ ∈ g)
    (hc₂ : Code.point c₂ ∈ g) :
    Code.configurations (Code.finiteCode
      (circleConfigurations d ![c₀, c₁, c₂])) ∈ D.before i := by
  obtain ⟨r, hr⟩ := Code.circleDataEnumeration_surjective d
  have hs := D.skolem_mem_before hg (2 * r + 3)
    [Code.point c₀, Code.point c₁, Code.point c₂] (by
      intro a ha
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
      rcases ha with rfl | rfl | rfl
      · exact hc₀
      · exact hc₁
      · exact hc₂)
  rw [Code.skolem_circleCode, hr] at hs
  exact hs

/-- Second D6 application, using the single finite-set code as its only
parameter.  Any coded triple whose first two points are common rational points
recovers the corresponding current lattice class below the layer. -/
theorem class_mem_before_of_configurationCode
    {i : D.Index} (F : Finset (Fin 3 → Point))
    (hF : Code.configurations F ∈ D.before i)
    {z : Fin 3 → Point} (hzF : z ∈ F)
    {L : OrientedFrame} (hz : z 0 ≠ z 1)
    (hz₀ : L.IsRational (z 0)) (hz₁ : L.IsRational (z 1)) :
    Code.latticeClass (OrientedFrame.classOf L) ∈ D.before i := by
  obtain ⟨g, hg, hFg⟩ := D.exists_guard_of_mem_before hF
  obtain ⟨k, hk, hkz⟩ := Code.exists_nthConfiguration_eq F hzF
  have hs := D.skolem_mem_before hg (2 * k + 4) [Code.configurations F] (by
    intro a ha
    have : a = Code.configurations F := by
      simpa only [List.mem_singleton] using ha
    simpa only [this] using hFg)
  rw [Code.skolem_classFromConfiguration] at hs
  rw [hkz, Code.recoveredClass_eq hz hz₀ hz₁] at hs
  exact hs

/-- A predecessor guard contains at most one point rational in the current
lattice class. -/
theorem rational_points_in_guard_subsingleton
    {i : D.Index} {g : Set Code} (hg : g ∈ D.guards i)
    {L : OrientedFrame}
    (hclass : Code.latticeClass (OrientedFrame.classOf L) ∈ D.layer i) :
    {x : Point | Code.point x ∈ g ∧ L.IsRational x}.Subsingleton := by
  intro x hx y hy
  by_contra hxy
  exact (not_mem_before_of_mem_layer D hclass)
    (class_mem_before_of_two_points_in_guard D hg hxy hx.1 hy.1 hx.2 hy.2)

/-- Only finitely many `L`-rational points have point codes below the current
Davies layer.  There is at most one such point in each of finitely many
guards. -/
theorem finite_rational_points_before
    {i : D.Index} {L : OrientedFrame}
    (hclass : Code.latticeClass (OrientedFrame.classOf L) ∈ D.layer i) :
    Set.Finite {x : Point | Code.point x ∈ D.before i ∧ L.IsRational x} := by
  let R : {g // g ∈ D.guards i} → Set Point := fun g ↦
    {x | Code.point x ∈ g.1 ∧ L.IsRational x}
  have hR : ∀ g, (R g).Finite := by
    intro g
    exact (rational_points_in_guard_subsingleton D g.2 hclass).finite
  have hU : Set.Finite (⋃ g, R g) := Set.finite_iUnion hR
  apply hU.subset
  intro x hx
  obtain ⟨g, hg, hxg⟩ := D.exists_guard_of_mem_before hx.1
  exact mem_iUnion.2 ⟨⟨g, hg⟩, hxg, hx.2⟩

/-- Every rational point of a class in the current layer is itself coded
either before that layer or in it.  The rational coordinate is compiled into
the natural-number index of the Skolem operation. -/
theorem rational_point_mem_before_or_layer
    {i : D.Index} {L : OrientedFrame}
    (hclass : Code.latticeClass (OrientedFrame.classOf L) ∈ D.layer i)
    {x : Point} (hx : L.IsRational x) :
    Code.point x ∈ D.before i ∪ D.layer i := by
  let C := OrientedFrame.classOf L
  let K := OrientedFrame.representative C
  have hKL : K.RationallyEquivalent L := by
    apply (OrientedFrame.classOf_eq_iff K L).1
    exact (OrientedFrame.classOf_representative C).trans rfl
  obtain ⟨q, hq⟩ := (hKL x).2 hx
  obtain ⟨n, hn⟩ := Code.ratEnumeration_surjective q
  have hs := D.skolem_mem_before_or_layer i (n + 3)
    [Code.latticeClass C] (by
      intro a ha
      have ha' : a = Code.latticeClass C := by
        simpa only [List.mem_singleton] using ha
      simpa only [ha'] using hclass)
  rw [Code.skolem_rationalPoint] at hs
  simpa only [C, K, hn, ← hq] using hs

/-- Pool localization in its strongest useful form: among all rational
points of a current class, only finitely many fail to lie in the current
terminal layer.  Every residue sublattice used by richness is a subset of
this rational plane, so the paper's localization lemma follows immediately. -/
theorem finite_rational_points_outside_layer
    {i : D.Index} {L : OrientedFrame}
    (hclass : Code.latticeClass (OrientedFrame.classOf L) ∈ D.layer i) :
    Set.Finite {x : Point | L.IsRational x ∧ Code.point x ∉ D.layer i} := by
  apply (finite_rational_points_before D hclass).subset
  intro x hx
  refine ⟨?_, hx.1⟩
  rcases rational_point_mem_before_or_layer D hclass hx.1 with hb | hl
  · exact hb
  · exact (hx.2 hl).elim

theorem exists_layer_of_class (C : OrientedFrame.RationalClass) :
    ∃ i : D.Index, C ∈ classes D i := by
  have h : Code.latticeClass C ∈ ⋃ i, D.layer i := by
    rw [D.layer_cover]
    trivial
  rcases mem_iUnion.1 h with ⟨i, hi⟩
  exact ⟨i, hi⟩

end CodedDavies

/-- Nonintegral squared distance, packaged as a symmetric binary relation. -/
def Separated (x y : Point) : Prop :=
  x ≠ y → ∀ z : ℤ, distSq x y ≠ (z : ℝ)

lemma separated_comm {x y : Point} : Separated x y ↔ Separated y x := by
  simp only [Separated, ne_eq]
  constructor
  · intro h hyx z hz
    exact h (Ne.symm hyx) z (by simpa only [distSq_comm] using hz)
  · intro h hxy z hz
    exact h (Ne.symm hxy) z (by simpa only [distSq_comm] using hz)

lemma partial_union {A B : Set Point} (hA : IsPartialSteinhaus A)
    (hB : IsPartialSteinhaus B)
    (hcross : ∀ x ∈ A, ∀ y ∈ B, Separated x y) :
    IsPartialSteinhaus (A ∪ B) := by
  intro x hx y hy hxy z
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact hA hx hy hxy z
  · exact hcross x hx y hy hxy z
  · exact (separated_comm.mp (hcross y hy x hx)) hxy z
  · exact hB hx hy hxy z

/-- Data produced by the forbidden-line and candidate-pool construction for
one member of a countable terminal layer.  `old` includes the set inherited
from earlier terminal layers and all blocks already chosen in this layer.
The only old point not covered by `old_safe` is `distinguished`; requiring it to be
selected makes the block's own partiality handle that pair.

The proof that such data exist is the geometric Claim 2.7 part of the
construction; it must be derived from `ThreeCircleFinitenessTheorem` and the
guard closure of a `DaviesDecomposition`, not postulated globally.
-/
structure CandidatePool (old : Set Point) (L : OrientedFrame) where
  pool : Set Point
  distinguished : Option Point
  rich : FrameRich L pool
  rational : ∀ x ∈ pool, L.IsRational x
  distinguished_mem : ∀ x, distinguished = some x → x ∈ old ∩ pool
  old_safe : ∀ x ∈ old, ∀ y ∈ pool,
    distinguished ≠ some x → Separated x y

/-- One exact selector application extends a partial old set by a block
meeting all rational translates of `L`. -/
theorem extendByCandidatePool
    (selector : RichSelectorTheorem) {old : Set Point} (hOld : IsPartialSteinhaus old)
    (L : OrientedFrame) (C : CandidatePool old L) :
    ∃ T : Set Point,
      T ⊆ C.pool ∧
      IsPartialSteinhaus (old ∪ T) ∧
      HitsRationalTranslates T L := by
  obtain ⟨T, hTP, hTpartial, hThits, hdistinguished⟩ :=
    selector L C.pool C.rich C.rational C.distinguished
      (fun x hx ↦ (C.distinguished_mem x hx).2)
  refine ⟨T, hTP, ?_, hThits⟩
  apply partial_union hOld hTpartial
  intro x hx y hy
  by_cases hdx : C.distinguished = some x
  · have hxT : x ∈ T := hdistinguished x hdx
    intro hxy z hz
    exact hTpartial hxT hy hxy z hz
  · exact C.old_safe x hx y (hTP hy) hdx

/-- Frames in a countable terminal layer.  The set `active` is used instead
of an arbitrary countable type so the inner recursion is the ordinary
natural-number recursion used in the paper. -/
structure TerminalLayer where
  active : Set ℕ
  frame : ℕ → OrientedFrame

namespace TerminalLayer

variable (A : TerminalLayer)

/-- A set has hit every rational-equivalence class listed in the terminal
layer. -/
def Hits (S : Set Point) : Prop :=
  ∀ n ∈ A.active, HitsRationalClass S (A.frame n)

end TerminalLayer

/-! ## A countable schedule of all residue requirements -/

/-- One rank-two congruence class occurring in the definition of richness. -/
structure ResidueRequirement where
  d : ℕ
  hd : d ≠ 0
  i : Fin d
  j : Fin d
  a : ℤ
  b : ℤ
  deriving Countable

namespace ResidueRequirement

/-- The rational translate containing the whole residue requirement. -/
def translate (R : ResidueRequirement) : RatPoint := fun r ↦
  if r = 0 then (R.i : ℕ) / R.d else (R.j : ℕ) / R.d

theorem mem_rationalTranslate {L : OrientedFrame} {R : ResidueRequirement}
    {x : Point} (hx : x ∈ FramedResidueSet L R.d R.i R.j R.a R.b) :
    x ∈ L.rationalTranslate R.translate := by
  rcases hx with ⟨k, l, rfl, -, -⟩
  let z : IntPoint := fun r ↦ if r = 0 then k else l
  refine ⟨z, ?_⟩
  apply congrArg L.fromCoords
  ext r
  fin_cases r <;> simp [translate, z, ratPoint, intPoint]

end ResidueRequirement

/-- A residue requirement attached to an active frame of a terminal layer. -/
structure ScheduledRequirement (A : TerminalLayer) where
  index : ℕ
  active : index ∈ A.active
  residue : ResidueRequirement
  deriving Countable

namespace ScheduledRequirement

variable {A : TerminalLayer}

noncomputable def encodable : Encodable (ScheduledRequirement A) :=
  Encodable.ofCountable _

/-- Cantor pairing makes every requirement occur infinitely often: the
second paired coordinate is deliberately ignored. -/
noncomputable def scheduled (default : ScheduledRequirement A) (r : ℕ) :
    ScheduledRequirement A :=
  ( @Encodable.decode (ScheduledRequirement A) encodable (Nat.unpair r).1
    ).getD default

theorem scheduled_pair (default req : ScheduledRequirement A) (k : ℕ) :
    scheduled default
      (Nat.pair (@Encodable.encode (ScheduledRequirement A) encodable req) k) = req := by
  simp [scheduled, Nat.unpair_pair,
    @Encodable.encodek (ScheduledRequirement A) encodable]

end ScheduledRequirement

/-- A harmless totalization used when a previous point is already rational
in the frame currently being scheduled. -/
def defaultFramedLine (L : OrientedFrame) : FramedLine L where
  point := 0
  direction := WithLp.toLp 2 fun r ↦ if r = 0 then 1 else 0
  direction_ne := by
    intro h
    have h0 := congrArg (fun p : Point ↦ p 0) h
    norm_num at h0

/-- The line containing every rational point at rational squared distance
from `x`, totalized in the rational case. -/
noncomputable def rationalDistanceLine (L : OrientedFrame) (x : Point) :
    FramedLine L := by
  classical
  exact if hx : L.IsRational x then defaultFramedLine L
    else Classical.choose (framed_rational_sqDist_line hx)

theorem mem_rationalDistanceLine {L : OrientedFrame} {x y : Point}
    (hx : ¬L.IsRational x) (hy : L.IsRational y)
    (hxy : HasRationalSqDist x y) :
    y ∈ (rationalDistanceLine L x).carrier := by
  rw [rationalDistanceLine, dif_neg hx]
  exact Classical.choose_spec (framed_rational_sqDist_line hx) y hy hxy

/-- Well-founded recursive choice from a set depending on all earlier
values.  Keeping this small utility explicit makes the later candidate
sequence a genuine natural-number recursion. -/
noncomputable def recursiveChoice {X : Type}
    (available : (n : ℕ) → (Fin n → X) → Set X)
    (havailable : ∀ n previous, (available n previous).Nonempty)
    (n : ℕ) : X :=
  Classical.choose (havailable n fun k ↦
    recursiveChoice available havailable k.1)
termination_by n

theorem recursiveChoice_spec {X : Type}
    (available : (n : ℕ) → (Fin n → X) → Set X)
    (havailable : ∀ n previous, (available n previous).Nonempty)
    (n : ℕ) :
    recursiveChoice available havailable n ∈
      available n (fun k ↦ recursiveChoice available havailable k.1) := by
  rw [recursiveChoice]
  exact Classical.choose_spec (havailable n fun k ↦
    recursiveChoice available havailable k.1)

namespace CodedDavies

variable (D : DaviesDecomposition Code.skolem)

noncomputable def classEncodable (i : D.Index) :
    Encodable {C // C ∈ classes D i} :=
  (classes_countable D i).toEncodable

noncomputable def encodedClass (i : D.Index) (n : ℕ) :
    Option OrientedFrame.RationalClass :=
  Option.map Subtype.val
    (@Encodable.decode {C // C ∈ classes D i} (classEncodable D i) n)

/-- The no-repetition natural-number enumeration of the class tags in one
countable Davies layer. -/
noncomputable def terminalLayer (i : D.Index) : TerminalLayer where
  active := Set.range
    (@Encodable.encode {C // C ∈ classes D i} (classEncodable D i))
  frame := fun n ↦
    match encodedClass D i n with
    | some C => OrientedFrame.representative C
    | none => Code.standardFrame

theorem active_frame_class_mem_layer {i : D.Index} {n : ℕ}
    (hn : n ∈ (terminalLayer D i).active) :
    Code.latticeClass
      (OrientedFrame.classOf ((terminalLayer D i).frame n)) ∈ D.layer i := by
  rcases hn with ⟨C, rfl⟩
  have hdecode : @Encodable.decode {C // C ∈ classes D i} (classEncodable D i)
      (@Encodable.encode {C // C ∈ classes D i} (classEncodable D i) C) = some C :=
    @Encodable.encodek {C // C ∈ classes D i} (classEncodable D i) C
  simp only [terminalLayer, encodedClass, hdecode, Option.map_some]
  rw [OrientedFrame.classOf_representative]
  change Code.latticeClass (C : OrientedFrame.RationalClass) ∈ D.layer i
  have hC := C.property
  change Code.latticeClass (C : OrientedFrame.RationalClass) ∈ D.layer i at hC
  exact hC

theorem class_appears_in_terminalLayer {i : D.Index}
    {C : OrientedFrame.RationalClass} (hC : C ∈ classes D i) :
    ∃ n ∈ (terminalLayer D i).active,
      OrientedFrame.classOf ((terminalLayer D i).frame n) = C := by
  let c : {K // K ∈ classes D i} := ⟨C, hC⟩
  let n := @Encodable.encode {K // K ∈ classes D i} (classEncodable D i) c
  refine ⟨n, ⟨c, rfl⟩, ?_⟩
  have hdecode : @Encodable.decode {K // K ∈ classes D i} (classEncodable D i) n = some c :=
    @Encodable.encodek {K // K ∈ classes D i} (classEncodable D i) c
  simp only [terminalLayer, encodedClass, hdecode, Option.map_some]
  exact OrientedFrame.classOf_representative C

theorem terminalLayer_class_injOn (i : D.Index) :
    Set.InjOn (fun n ↦ OrientedFrame.classOf ((terminalLayer D i).frame n))
      (terminalLayer D i).active := by
  intro n hn m hm hnm
  rcases hn with ⟨C, rfl⟩
  rcases hm with ⟨K, rfl⟩
  have hdecodeC :
      @Encodable.decode {J // J ∈ classes D i} (classEncodable D i)
        (@Encodable.encode {J // J ∈ classes D i} (classEncodable D i) C) = some C :=
    @Encodable.encodek {J // J ∈ classes D i} (classEncodable D i) C
  have hdecodeK :
      @Encodable.decode {J // J ∈ classes D i} (classEncodable D i)
        (@Encodable.encode {J // J ∈ classes D i} (classEncodable D i) K) = some K :=
    @Encodable.encodek {J // J ∈ classes D i} (classEncodable D i) K
  simp only [terminalLayer, encodedClass, hdecodeC, hdecodeK, Option.map_some,
    OrientedFrame.classOf_representative] at hnm
  apply congrArg
    (@Encodable.encode {J // J ∈ classes D i} (classEncodable D i))
  exact Subtype.ext hnm

theorem every_class_appears (C : OrientedFrame.RationalClass) :
    ∃ (i : D.Index) (n : ℕ), n ∈ (terminalLayer D i).active ∧
      OrientedFrame.classOf ((terminalLayer D i).frame n) = C := by
  obtain ⟨i, hi⟩ := exists_layer_of_class D C
  obtain ⟨n, hn, hclass⟩ := class_appears_in_terminalLayer D hi
  exact ⟨i, n, hn, hclass⟩

/-- The current Davies layer is already rich in every rank-two residue
sublattice of every class it contains.  This is the constructive content of
the pool-localization lemma before forbidden lines are removed. -/
theorem layerPool_rich {i : D.Index} {L : OrientedFrame}
    (hclass : Code.latticeClass (OrientedFrame.classOf L) ∈ D.layer i) :
    FrameRich L {x | Code.point x ∈ D.layer i} := by
  intro d hd ri rj a b
  let q : ℤ → RatPoint := fun t r ↦
    if r = 0 then (ri : ℕ) / d + (a + d * t : ℤ)
    else (rj : ℕ) / d + (b : ℤ)
  let f : ℤ → Point := fun t ↦ L.fromCoords (ratPoint (q t))
  have hf : Function.Injective f := by
    intro t u htu
    have hrat : ratPoint (q t) = ratPoint (q u) :=
      L.fromCoords_injective htu
    have hq : q t = q u := ratPoint_injective hrat
    have hzero := congrFun hq 0
    have hdpos : (0 : ℚ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd
    simp only [q, if_pos rfl] at hzero
    push_cast at hzero
    have hmul : (d : ℚ) * (t : ℚ) = (d : ℚ) * (u : ℚ) := by
      linarith
    have htuq : (t : ℚ) = (u : ℚ) :=
      mul_left_cancel₀ (ne_of_gt hdpos) hmul
    exact_mod_cast htuq
  have hfinf : Set.Infinite (Set.range f) := Set.infinite_range_of_injective hf
  let bad : Set Point :=
    {x | L.IsRational x ∧ Code.point x ∉ D.layer i}
  have hbad : bad.Finite := finite_rational_points_outside_layer D hclass
  have hremain : Set.Infinite (Set.range f \ bad) := hfinf.sdiff hbad
  apply hremain.mono
  intro x hx
  rcases hx.1 with ⟨t, rfl⟩
  have hrat : L.IsRational (f t) := ⟨q t, rfl⟩
  have hlayer : Code.point (f t) ∈ D.layer i := by
    by_contra hout
    exact hx.2 ⟨hrat, hout⟩
  refine ⟨a + d * t, b, ?_, ?_, ?_, hlayer⟩
  · simp [f, q]
  · exact Int.modEq_iff_dvd.2 ⟨t, by ring⟩
  · exact Int.ModEq.rfl

/-- The robust localized pool remains rich after deleting finitely many
framed affine lines. -/
theorem layerAvoidPool_rich {i : D.Index} {L : OrientedFrame}
    (hclass : Code.latticeClass (OrientedFrame.classOf L) ∈ D.layer i)
    (G : Finset (FramedLine L)) :
    FrameRich L {x | Code.point x ∈ D.layer i ∧
      ∀ line ∈ G, x ∉ line.carrier} := by
  intro d hd ri rj a b
  let bad : Set Point :=
    {x | L.IsRational x ∧ Code.point x ∉ D.layer i}
  have hbad : bad.Finite := finite_rational_points_outside_layer D hclass
  have hinf := framedResidueSet_infinite_avoid hd ri rj a b G hbad
  apply hinf.mono
  intro x hx
  rcases hx with ⟨⟨k, l, heq, hka, hlb⟩, hxbad, hxlines⟩
  have hrat : L.IsRational x := by
    refine ⟨fun r ↦ if r = 0 then (ri : ℕ) / d + k else (rj : ℕ) / d + l, ?_⟩
    exact heq
  have hlayer : Code.point x ∈ D.layer i := by
    by_contra hout
    exact hxbad ⟨hrat, hout⟩
  exact ⟨k, l, heq, hka, hlb, hlayer, hxlines⟩

/-- For a fixed predecessor guard and a fixed rational translate, all
`L`-rational candidates having rational squared distance from an
`L`-irrational old point lie on finitely many framed lines.  This is the
three-centre/D6 core of Claim 2.7. -/
theorem finite_forbiddenLines_in_guard
    (circle : ThreeCircleFinitenessTheorem)
    {i : D.Index} {L : OrientedFrame} {old : Set Point}
    {g : Set Code} (hg : g ∈ D.guards i)
    (hOld : IsPartialSteinhaus old)
    (hclass : Code.latticeClass (OrientedFrame.classOf L) ∈ D.layer i)
    (q : RatPoint) :
    ∃ G : Finset (FramedLine L),
      ∀ x ∈ old, Code.point x ∈ g → ¬L.IsRational x →
        ∀ y ∈ L.rationalTranslate q, HasRationalSqDist x y →
          ∃ line ∈ G, y ∈ line.carrier := by
  classical
  by_contra hcover
  have hstep (G : Finset (FramedLine L)) :
      ∃ x ∈ old, Code.point x ∈ g ∧ ¬L.IsRational x ∧
        ∃ y ∈ L.rationalTranslate q, HasRationalSqDist x y ∧
          ∀ line ∈ G, y ∉ line.carrier := by
    have hn := not_exists.mp hcover G
    push Not at hn
    exact hn
  obtain ⟨c₀, hc₀old, hc₀g, hc₀irr, t₀, ht₀q, hd₀, -⟩ :=
    hstep ∅
  obtain ⟨line₀, hline₀⟩ := framed_rational_sqDist_line hc₀irr
  have ht₀rat : L.IsRational t₀ := isRational_of_mem_rationalTranslate ht₀q
  have ht₀line : t₀ ∈ line₀.carrier := hline₀ t₀ ht₀rat hd₀
  obtain ⟨c₁, hc₁old, hc₁g, hc₁irr, t₁, ht₁q, hd₁, ht₁avoid⟩ :=
    hstep {line₀}
  obtain ⟨line₁, hline₁⟩ := framed_rational_sqDist_line hc₁irr
  have ht₁rat : L.IsRational t₁ := isRational_of_mem_rationalTranslate ht₁q
  have ht₁line : t₁ ∈ line₁.carrier := hline₁ t₁ ht₁rat hd₁
  have ht₁not₀ : t₁ ∉ line₀.carrier := ht₁avoid line₀ (by simp)
  obtain ⟨c₂, hc₂old, hc₂g, hc₂irr, t₂, ht₂q, hd₂, ht₂avoid⟩ :=
    hstep {line₀, line₁}
  have ht₂rat : L.IsRational t₂ := isRational_of_mem_rationalTranslate ht₂q
  have ht₂not₀ : t₂ ∉ line₀.carrier := ht₂avoid line₀ (by simp)
  have ht₂not₁ : t₂ ∉ line₁.carrier := ht₂avoid line₁ (by simp)
  have hc₀₁ : c₀ ≠ c₁ := by
    intro h
    apply ht₁not₀
    exact hline₀ t₁ ht₁rat (by simpa only [h] using hd₁)
  have hc₀₂ : c₀ ≠ c₂ := by
    intro h
    apply ht₂not₀
    exact hline₀ t₂ ht₂rat (by simpa only [h] using hd₂)
  have hc₁₂ : c₁ ≠ c₂ := by
    intro h
    apply ht₂not₁
    exact hline₁ t₂ ht₂rat (by simpa only [h] using hd₂)
  have ht₀₁ : t₀ ≠ t₁ := by
    intro h
    exact ht₁not₀ (h ▸ ht₀line)
  have ht₀₂ : t₀ ≠ t₂ := by
    intro h
    exact ht₂not₀ (h ▸ ht₀line)
  have ht₁₂ : t₁ ≠ t₂ := by
    intro h
    exact ht₂not₁ (h ▸ ht₁line)
  let center : Fin 3 → Point := ![c₀, c₁, c₂]
  let target : Fin 3 → Point := ![t₀, t₁, t₂]
  have hcenter : Function.Injective center := by
    intro a b hab
    fin_cases a <;> fin_cases b
    · rfl
    · exact (hc₀₁ (by simpa [center] using hab)).elim
    · exact (hc₀₂ (by simpa [center] using hab)).elim
    · exact (hc₀₁ (by simpa [center] using hab.symm)).elim
    · rfl
    · exact (hc₁₂ (by simpa [center] using hab)).elim
    · exact (hc₀₂ (by simpa [center] using hab.symm)).elim
    · exact (hc₁₂ (by simpa [center] using hab.symm)).elim
    · rfl
  have htarget : Function.Injective target := by
    intro a b hab
    fin_cases a <;> fin_cases b
    · rfl
    · exact (ht₀₁ (by simpa [target] using hab)).elim
    · exact (ht₀₂ (by simpa [target] using hab)).elim
    · exact (ht₀₁ (by simpa [target] using hab.symm)).elim
    · rfl
    · exact (ht₁₂ (by simpa [target] using hab)).elim
    · exact (ht₀₂ (by simpa [target] using hab.symm)).elim
    · exact (ht₁₂ (by simpa [target] using hab.symm)).elim
    · rfl
  rcases hd₀ with ⟨r₀, hr₀⟩
  rcases hd₁ with ⟨r₁, hr₁⟩
  rcases hd₂ with ⟨r₂, hr₂⟩
  let radius : Fin 3 → ℚ := ![r₀, r₁, r₂]
  have hc₀t₀ : c₀ ≠ t₀ := by
    intro h
    exact hc₀irr (h ▸ ht₀rat)
  have hc₁t₁ : c₁ ≠ t₁ := by
    intro h
    exact hc₁irr (h ▸ ht₁rat)
  have hc₂t₂ : c₂ ≠ t₂ := by
    intro h
    exact hc₂irr (h ▸ ht₂rat)
  have hr₀pos : 0 < (r₀ : ℝ) := by
    rw [← hr₀, distSq_eq_dist_sq]
    exact sq_pos_of_pos (dist_pos.mpr hc₀t₀)
  have hr₁pos : 0 < (r₁ : ℝ) := by
    rw [← hr₁, distSq_eq_dist_sq]
    exact sq_pos_of_pos (dist_pos.mpr hc₁t₁)
  have hr₂pos : 0 < (r₂ : ℝ) := by
    rw [← hr₂, distSq_eq_dist_sq]
    exact sq_pos_of_pos (dist_pos.mpr hc₂t₂)
  have htargetInt : ∀ a b, ∃ z : ℤ,
      distSq (target a) (target b) = (z : ℝ) := by
    intro a b
    apply exists_int_distSq_of_mem_rationalTranslate
    · fin_cases a
      · simpa [target] using ht₀q
      · simpa [target] using ht₁q
      · simpa [target] using ht₂q
    · fin_cases b
      · simpa [target] using ht₀q
      · simpa [target] using ht₁q
      · simpa [target] using ht₂q
  let targetSq : Fin 3 → Fin 3 → ℤ :=
    fun a b ↦ Classical.choose (htargetInt a b)
  have htargetSq : ∀ a b,
      distSq (target a) (target b) = (targetSq a b : ℝ) :=
    fun a b ↦ Classical.choose_spec (htargetInt a b)
  let d : CircleDatum := ⟨radius, targetSq⟩
  have hpositive : ∀ a, 0 < (d.radiusSq a : ℝ) := by
    intro a
    fin_cases a <;> assumption
  have hcenterOld : ∀ a, center a ∈ old := by
    intro a
    fin_cases a <;> assumption
  have hfinite : (circleConfigurations d center).Finite :=
    circleConfigurations_finite circle d center target hcenter htarget
      hpositive htargetSq hOld hcenterOld
  have htargetConfig : target ∈ circleConfigurations d center := by
    constructor
    · intro a
      fin_cases a
      · simpa [d, radius, center, target] using hr₀
      · simpa [d, radius, center, target] using hr₁
      · simpa [d, radius, center, target] using hr₂
    · exact htargetSq
  have htargetCode : target ∈
      Code.finiteCode (circleConfigurations d center) :=
    (Code.mem_finiteCode_iff hfinite target).2 htargetConfig
  have hcodeBefore : Code.configurations
      (Code.finiteCode (circleConfigurations d center)) ∈ D.before i := by
    simpa only [center] using
      circleCode_mem_before D hg d c₀ c₁ c₂ hc₀g hc₁g hc₂g
  have hclassBefore := class_mem_before_of_configurationCode D
    (Code.finiteCode (circleConfigurations d center)) hcodeBefore htargetCode
    (by simpa [target] using ht₀₁)
    (by simpa [target] using ht₀rat)
    (by simpa [target] using ht₁rat)
  exact (not_mem_before_of_mem_layer D hclass) hclassBefore

/-- The finite family of predecessor guards upgrades the preceding
guardwise conclusion to all old points coded below the current Davies
layer. -/
theorem finite_forbiddenLines
    (circle : ThreeCircleFinitenessTheorem)
    {i : D.Index} {L : OrientedFrame} {old : Set Point}
    (hOld : IsPartialSteinhaus old)
    (hbefore : ∀ x ∈ old, Code.point x ∈ D.before i)
    (hclass : Code.latticeClass (OrientedFrame.classOf L) ∈ D.layer i)
    (q : RatPoint) :
    ∃ G : Finset (FramedLine L),
      ∀ x ∈ old, ¬L.IsRational x →
        ∀ y ∈ L.rationalTranslate q, HasRationalSqDist x y →
          ∃ line ∈ G, y ∈ line.carrier := by
  classical
  let cover : (g : {g // g ∈ D.guards i}) → Finset (FramedLine L) :=
    fun g ↦ Classical.choose
      (finite_forbiddenLines_in_guard D circle g.2 hOld hclass q)
  have cover_spec (g : {g // g ∈ D.guards i}) :
      ∀ x ∈ old, Code.point x ∈ g.1 → ¬L.IsRational x →
        ∀ y ∈ L.rationalTranslate q, HasRationalSqDist x y →
          ∃ line ∈ cover g, y ∈ line.carrier :=
    Classical.choose_spec
      (finite_forbiddenLines_in_guard D circle g.2 hOld hclass q)
  let G : Finset (FramedLine L) := (D.guards i).attach.biUnion cover
  refine ⟨G, ?_⟩
  intro x hxold hxirr y hyq hxy
  obtain ⟨g, hg, hxg⟩ := D.exists_guard_of_mem_before (hbefore x hxold)
  obtain ⟨line, hline, hyline⟩ :=
    cover_spec ⟨g, hg⟩ x hxold hxg hxirr y hyq hxy
  refine ⟨line, ?_, hyline⟩
  apply Finset.mem_biUnion.2
  exact ⟨⟨g, hg⟩, by simp, hline⟩

/-! ### The globally scheduled candidate sequence inside one terminal layer -/

/-- The finite outer-old obstruction attached to one scheduled residue
requirement. -/
noncomputable def outerForbiddenLines
    (circle : ThreeCircleFinitenessTheorem)
    {i : D.Index} {A : TerminalLayer} {old : Set Point}
    (hOld : IsPartialSteinhaus old)
    (hbefore : ∀ x ∈ old, Code.point x ∈ D.before i)
    (hclass : ∀ n ∈ A.active,
      Code.latticeClass (OrientedFrame.classOf (A.frame n)) ∈ D.layer i)
    (req : ScheduledRequirement A) :
    Finset (FramedLine (A.frame req.index)) :=
  Classical.choose (finite_forbiddenLines D circle hOld hbefore
    (hclass req.index req.active) req.residue.translate)

theorem outerForbiddenLines_spec
    (circle : ThreeCircleFinitenessTheorem)
    {i : D.Index} {A : TerminalLayer} {old : Set Point}
    (hOld : IsPartialSteinhaus old)
    (hbefore : ∀ x ∈ old, Code.point x ∈ D.before i)
    (hclass : ∀ n ∈ A.active,
      Code.latticeClass (OrientedFrame.classOf (A.frame n)) ∈ D.layer i)
    (req : ScheduledRequirement A) :
    ∀ x ∈ old, ¬(A.frame req.index).IsRational x →
      ∀ y ∈ (A.frame req.index).rationalTranslate req.residue.translate,
        HasRationalSqDist x y →
        ∃ line ∈ outerForbiddenLines D circle hOld hbefore hclass req,
          y ∈ line.carrier :=
  Classical.choose_spec (finite_forbiddenLines D circle hOld hbefore
    (hclass req.index req.active) req.residue.translate)

/-- At rank `r`, delete both the outer-old obstruction and the one rational
distance line contributed by each earlier candidate. -/
noncomputable def candidateLines {A : TerminalLayer}
    (default : ScheduledRequirement A)
    (outer : (req : ScheduledRequirement A) →
      Finset (FramedLine (A.frame req.index)))
    (r : ℕ) (previous : Fin r → Point) :
    Finset (FramedLine (A.frame (ScheduledRequirement.scheduled default r).index)) := by
  classical
  let req := ScheduledRequirement.scheduled default r
  exact outer req ∪ Finset.univ.image
    (fun k ↦ rationalDistanceLine (A.frame req.index) (previous k))

/-- The finitely many possible common rational points with earlier active
frame classes.  Removing them resolves the reverse-rank case in the
diagonal candidate construction. -/
def earlierCross (A : TerminalLayer) (req : ScheduledRequirement A) : Set Point :=
  {x | ∃ m < req.index, m ∈ A.active ∧
    (A.frame req.index).IsRational x ∧ (A.frame m).IsRational x}

theorem rational_intersection_subsingleton {A : TerminalLayer}
    (hclassInj : Set.InjOn
      (fun n ↦ OrientedFrame.classOf (A.frame n)) A.active)
    {m n : ℕ} (hm : m ∈ A.active) (hn : n ∈ A.active) (hmn : m ≠ n) :
    {x | (A.frame n).IsRational x ∧
      (A.frame m).IsRational x}.Subsingleton := by
  intro x hx y hy
  by_contra hxy
  have heq := OrientedFrame.class_eq_of_two_common hxy
    hx.1 hx.2 hy.1 hy.2
  exact hmn (hclassInj hm hn heq.symm)

theorem earlierCross_finite {A : TerminalLayer}
    (hclassInj : Set.InjOn
      (fun n ↦ OrientedFrame.classOf (A.frame n)) A.active)
    (req : ScheduledRequirement A) : (earlierCross A req).Finite := by
  classical
  let cross : Fin req.index → Set Point := fun m ↦
    if hm : (m : ℕ) ∈ A.active then
      {x | (A.frame req.index).IsRational x ∧
        (A.frame m).IsRational x}
    else ∅
  have hcross : ∀ m, (cross m).Finite := by
    intro m
    by_cases hm : (m : ℕ) ∈ A.active
    · rw [show cross m = {x | (A.frame req.index).IsRational x ∧
          (A.frame m).IsRational x} by simp [cross, hm]]
      exact (rational_intersection_subsingleton hclassInj hm req.active
        (Nat.ne_of_lt m.2)).finite
    · simp [cross, hm]
  apply (Set.finite_iUnion hcross).subset
  intro x hx
  rcases hx with ⟨m, hmn, hm, hxn, hxm⟩
  apply mem_iUnion.2
  exact ⟨⟨m, hmn⟩, by simp [cross, hm, hxn, hxm]⟩

/-- The infinite set from which rank `r` is chosen. -/
def candidateAvailable {A : TerminalLayer}
    (default : ScheduledRequirement A)
    (outer : (req : ScheduledRequirement A) →
      Finset (FramedLine (A.frame req.index)))
    (i : D.Index) (r : ℕ) (previous : Fin r → Point) : Set Point :=
  let req := ScheduledRequirement.scheduled default r
  {x | x ∈ FramedResidueSet (A.frame req.index)
      req.residue.d req.residue.i req.residue.j
      req.residue.a req.residue.b ∧
    Code.point x ∈ D.layer i ∧
    (∀ line ∈ candidateLines default outer r previous,
      x ∉ line.carrier) ∧
    x ∉ earlierCross A req ∧
    ∀ k, x ≠ previous k}

theorem candidateAvailable_nonempty {A : TerminalLayer}
    (default : ScheduledRequirement A)
    (outer : (req : ScheduledRequirement A) →
      Finset (FramedLine (A.frame req.index)))
    {i : D.Index}
    (hclass : ∀ n ∈ A.active,
      Code.latticeClass (OrientedFrame.classOf (A.frame n)) ∈ D.layer i)
    (hclassInj : Set.InjOn
      (fun n ↦ OrientedFrame.classOf (A.frame n)) A.active)
    (r : ℕ) (previous : Fin r → Point) :
    (candidateAvailable D default outer i r previous).Nonempty := by
  classical
  let req := ScheduledRequirement.scheduled default r
  let G := candidateLines default outer r previous
  have hinfinite := layerAvoidPool_rich D
    (hclass req.index req.active) G
      req.residue.d req.residue.hd req.residue.i req.residue.j
      req.residue.a req.residue.b
  let previousSet : Set Point := ↑(Finset.univ.image previous)
  have hpreviousSet : previousSet.Finite := Finset.finite_toSet _
  have hremove : (earlierCross A req ∪ previousSet).Finite :=
    (earlierCross_finite hclassInj req).union hpreviousSet
  obtain ⟨x, hx, hxremove⟩ := hinfinite.exists_notMem_finite hremove
  refine ⟨x, ?_⟩
  change x ∈ FramedResidueSet (A.frame req.index)
      req.residue.d req.residue.i req.residue.j
      req.residue.a req.residue.b ∧
    Code.point x ∈ D.layer i ∧
    (∀ line ∈ G, x ∉ line.carrier) ∧
    x ∉ earlierCross A req ∧ ∀ k, x ≠ previous k
  rcases hx with ⟨k, l, heq, hka, hlb, hlayer, hlines⟩
  refine ⟨⟨k, l, heq, hka, hlb⟩, hlayer, hlines, ?_, ?_⟩
  · exact fun hx ↦ hxremove (Or.inl hx)
  intro k hk
  apply hxremove
  apply Or.inr
  apply Finset.mem_image.2
  exact ⟨k, by simp, hk.symm⟩

/-- The precomputed candidate sequence.  Each rank avoids every earlier
point and, when that point is irrational in the current frame, its entire
rational-distance line. -/
noncomputable def candidatePoint {A : TerminalLayer}
    (default : ScheduledRequirement A)
    (outer : (req : ScheduledRequirement A) →
      Finset (FramedLine (A.frame req.index)))
    {i : D.Index}
    (hclass : ∀ n ∈ A.active,
      Code.latticeClass (OrientedFrame.classOf (A.frame n)) ∈ D.layer i)
    (hclassInj : Set.InjOn
      (fun n ↦ OrientedFrame.classOf (A.frame n)) A.active)
    (r : ℕ) : Point :=
  recursiveChoice (candidateAvailable D default outer i)
    (candidateAvailable_nonempty D default outer hclass hclassInj) r

theorem candidatePoint_spec {A : TerminalLayer}
    (default : ScheduledRequirement A)
    (outer : (req : ScheduledRequirement A) →
      Finset (FramedLine (A.frame req.index)))
    {i : D.Index}
    (hclass : ∀ n ∈ A.active,
      Code.latticeClass (OrientedFrame.classOf (A.frame n)) ∈ D.layer i)
    (hclassInj : Set.InjOn
      (fun n ↦ OrientedFrame.classOf (A.frame n)) A.active)
    (r : ℕ) :
    candidatePoint D default outer hclass hclassInj r ∈
      candidateAvailable D default outer i r
        (fun k ↦ candidatePoint D default outer hclass hclassInj k.1) := by
  exact recursiveChoice_spec (candidateAvailable D default outer i)
    (candidateAvailable_nonempty D default outer hclass hclassInj) r

theorem candidatePoint_properties {A : TerminalLayer}
    (default : ScheduledRequirement A)
    (outer : (req : ScheduledRequirement A) →
      Finset (FramedLine (A.frame req.index)))
    {i : D.Index}
    (hclass : ∀ n ∈ A.active,
      Code.latticeClass (OrientedFrame.classOf (A.frame n)) ∈ D.layer i)
    (hclassInj : Set.InjOn
      (fun n ↦ OrientedFrame.classOf (A.frame n)) A.active)
    (r : ℕ) :
    let req := ScheduledRequirement.scheduled default r
    let p := candidatePoint D default outer hclass hclassInj r
    p ∈ FramedResidueSet (A.frame req.index)
        req.residue.d req.residue.i req.residue.j
        req.residue.a req.residue.b ∧
      Code.point p ∈ D.layer i ∧
      (∀ line ∈ candidateLines default outer r
        (fun k ↦ candidatePoint D default outer hclass hclassInj k.1),
        p ∉ line.carrier) ∧
      p ∉ earlierCross A req ∧
      ∀ k : Fin r, p ≠ candidatePoint D default outer hclass hclassInj k.1 := by
  simpa only [candidateAvailable, Set.mem_setOf_eq] using
    candidatePoint_spec D default outer hclass hclassInj r

theorem candidatePoint_ne_of_lt {A : TerminalLayer}
    (default : ScheduledRequirement A)
    (outer : (req : ScheduledRequirement A) →
      Finset (FramedLine (A.frame req.index)))
    {i : D.Index}
    (hclass : ∀ n ∈ A.active,
      Code.latticeClass (OrientedFrame.classOf (A.frame n)) ∈ D.layer i)
    (hclassInj : Set.InjOn
      (fun n ↦ OrientedFrame.classOf (A.frame n)) A.active)
    {r s : ℕ} (hrs : r < s) :
    candidatePoint D default outer hclass hclassInj s ≠
      candidatePoint D default outer hclass hclassInj r :=
  (candidatePoint_properties D default outer hclass hclassInj s).2.2.2.2
    ⟨r, hrs⟩

theorem candidatePoint_injective {A : TerminalLayer}
    (default : ScheduledRequirement A)
    (outer : (req : ScheduledRequirement A) →
      Finset (FramedLine (A.frame req.index)))
    {i : D.Index}
    (hclass : ∀ n ∈ A.active,
      Code.latticeClass (OrientedFrame.classOf (A.frame n)) ∈ D.layer i)
    (hclassInj : Set.InjOn
      (fun n ↦ OrientedFrame.classOf (A.frame n)) A.active) :
    Function.Injective (candidatePoint D default outer hclass hclassInj) := by
  intro r s hrs
  rcases lt_trichotomy r s with hlt | heq | hgt
  · exact (candidatePoint_ne_of_lt D default outer hclass hclassInj hlt
      hrs.symm).elim
  · exact heq
  · exact (candidatePoint_ne_of_lt D default outer hclass hclassInj hgt
      hrs).elim

/-- Candidates born for the active frame `n`. -/
def candidateSource {A : TerminalLayer}
    (default : ScheduledRequirement A)
    (outer : (req : ScheduledRequirement A) →
      Finset (FramedLine (A.frame req.index)))
    {i : D.Index}
    (hclass : ∀ n ∈ A.active,
      Code.latticeClass (OrientedFrame.classOf (A.frame n)) ∈ D.layer i)
    (hclassInj : Set.InjOn
      (fun n ↦ OrientedFrame.classOf (A.frame n)) A.active)
    (n : ℕ) : Set Point :=
  {x | ∃ r, (ScheduledRequirement.scheduled default r).index = n ∧
    candidatePoint D default outer hclass hclassInj r = x}

theorem candidateSource_located {A : TerminalLayer}
    (default : ScheduledRequirement A)
    (outer : (req : ScheduledRequirement A) →
      Finset (FramedLine (A.frame req.index)))
    {i : D.Index}
    (hclass : ∀ n ∈ A.active,
      Code.latticeClass (OrientedFrame.classOf (A.frame n)) ∈ D.layer i)
    (hclassInj : Set.InjOn
      (fun n ↦ OrientedFrame.classOf (A.frame n)) A.active)
    {n : ℕ} {x : Point}
    (hx : x ∈ candidateSource D default outer hclass hclassInj n) :
    Code.point x ∈ D.layer i := by
  rcases hx with ⟨r, -, rfl⟩
  exact (candidatePoint_properties D default outer hclass hclassInj r).2.1

theorem candidateSource_rational {A : TerminalLayer}
    (default : ScheduledRequirement A)
    (outer : (req : ScheduledRequirement A) →
      Finset (FramedLine (A.frame req.index)))
    {i : D.Index}
    (hclass : ∀ n ∈ A.active,
      Code.latticeClass (OrientedFrame.classOf (A.frame n)) ∈ D.layer i)
    (hclassInj : Set.InjOn
      (fun n ↦ OrientedFrame.classOf (A.frame n)) A.active)
    {n : ℕ} {x : Point}
    (hx : x ∈ candidateSource D default outer hclass hclassInj n) :
    (A.frame n).IsRational x := by
  rcases hx with ⟨r, hrn, rfl⟩
  let req := ScheduledRequirement.scheduled default r
  have hres := (candidatePoint_properties D default outer hclass hclassInj r).1
  have hq := ResidueRequirement.mem_rationalTranslate hres
  have hrat := isRational_of_mem_rationalTranslate hq
  simpa only [req, hrn] using hrat

theorem candidateSource_rich {A : TerminalLayer}
    (default : ScheduledRequirement A)
    (outer : (req : ScheduledRequirement A) →
      Finset (FramedLine (A.frame req.index)))
    {i : D.Index}
    (hclass : ∀ n ∈ A.active,
      Code.latticeClass (OrientedFrame.classOf (A.frame n)) ∈ D.layer i)
    (hclassInj : Set.InjOn
      (fun n ↦ OrientedFrame.classOf (A.frame n)) A.active)
    {n : ℕ} (hn : n ∈ A.active) :
    FrameRich (A.frame n)
      (candidateSource D default outer hclass hclassInj n) := by
  intro d hd ri rj a b
  let residue : ResidueRequirement := ⟨d, hd, ri, rj, a, b⟩
  let req : ScheduledRequirement A := ⟨n, hn, residue⟩
  let code := @Encodable.encode (ScheduledRequirement A)
    ScheduledRequirement.encodable req
  let rank : ℕ → ℕ := fun k ↦ Nat.pair code k
  let f : ℕ → Point := fun k ↦
    candidatePoint D default outer hclass hclassInj (rank k)
  have hrank : Function.Injective rank := by
    intro k l hkl
    have h := congrArg (fun z ↦ (Nat.unpair z).2) hkl
    simpa only [rank, Nat.unpair_pair] using h
  have hf : Function.Injective f :=
    (candidatePoint_injective D default outer hclass hclassInj).comp hrank
  apply (Set.infinite_range_of_injective hf).mono
  intro x hx
  rcases hx with ⟨k, rfl⟩
  have hschedule : ScheduledRequirement.scheduled default (rank k) = req := by
    exact ScheduledRequirement.scheduled_pair default req k
  have hp := (candidatePoint_properties D default outer hclass hclassInj (rank k)).1
  rw [hschedule] at hp
  rcases hp with ⟨u, v, heq, hua, hvb⟩
  refine ⟨u, v, ?_, hua, hvb, ?_⟩
  · simpa only [req, residue] using heq
  · refine ⟨rank k, ?_, rfl⟩
    simpa only [hschedule, req]

theorem candidatePoint_rational {A : TerminalLayer}
    (default : ScheduledRequirement A)
    (outer : (req : ScheduledRequirement A) →
      Finset (FramedLine (A.frame req.index)))
    {i : D.Index}
    (hclass : ∀ n ∈ A.active,
      Code.latticeClass (OrientedFrame.classOf (A.frame n)) ∈ D.layer i)
    (hclassInj : Set.InjOn
      (fun n ↦ OrientedFrame.classOf (A.frame n)) A.active)
    (r : ℕ) :
    let req := ScheduledRequirement.scheduled default r
    (A.frame req.index).IsRational
      (candidatePoint D default outer hclass hclassInj r) := by
  let req := ScheduledRequirement.scheduled default r
  have hres := (candidatePoint_properties D default outer hclass hclassInj r).1
  exact isRational_of_mem_rationalTranslate
    (ResidueRequirement.mem_rationalTranslate hres)

/-- Forward-rank half of the diagonal construction: rational squared
distance from an earlier candidate forces that earlier point to be rational
in the later candidate's scheduled frame. -/
theorem earlierCandidate_rational_of_rationalSqDist {A : TerminalLayer}
    (default : ScheduledRequirement A)
    (outer : (req : ScheduledRequirement A) →
      Finset (FramedLine (A.frame req.index)))
    {i : D.Index}
    (hclass : ∀ n ∈ A.active,
      Code.latticeClass (OrientedFrame.classOf (A.frame n)) ∈ D.layer i)
    (hclassInj : Set.InjOn
      (fun n ↦ OrientedFrame.classOf (A.frame n)) A.active)
    {r s : ℕ} (hrs : r < s)
    (hdist : HasRationalSqDist
      (candidatePoint D default outer hclass hclassInj r)
      (candidatePoint D default outer hclass hclassInj s)) :
    let req := ScheduledRequirement.scheduled default s
    (A.frame req.index).IsRational
      (candidatePoint D default outer hclass hclassInj r) := by
  classical
  let req := ScheduledRequirement.scheduled default s
  let pr := candidatePoint D default outer hclass hclassInj r
  let ps := candidatePoint D default outer hclass hclassInj s
  by_contra hpr
  have hps : (A.frame req.index).IsRational ps :=
    candidatePoint_rational D default outer hclass hclassInj s
  have hline : ps ∈ (rationalDistanceLine (A.frame req.index) pr).carrier :=
    mem_rationalDistanceLine hpr hps hdist
  have havoid :=
    (candidatePoint_properties D default outer hclass hclassInj s).2.2.1
  apply havoid (rationalDistanceLine (A.frame req.index) pr)
  · apply Finset.mem_union_right
    apply Finset.mem_image.2
    exact ⟨⟨r, hrs⟩, by simp [req, pr]⟩
  · exact hline

/-- If `m < n`, rational squared distance between the two scheduled source
sets forces the older-source point to be rational in frame `n`.  In the
reverse rank order, the later-source point was explicitly removed by
`earlierCross`. -/
theorem sourcePoint_rational_of_rationalSqDist {A : TerminalLayer}
    (default : ScheduledRequirement A)
    (outer : (req : ScheduledRequirement A) →
      Finset (FramedLine (A.frame req.index)))
    {i : D.Index}
    (hclass : ∀ n ∈ A.active,
      Code.latticeClass (OrientedFrame.classOf (A.frame n)) ∈ D.layer i)
    (hclassInj : Set.InjOn
      (fun n ↦ OrientedFrame.classOf (A.frame n)) A.active)
    {m n : ℕ} (hmn : m < n) {x y : Point}
    (hx : x ∈ candidateSource D default outer hclass hclassInj m)
    (hy : y ∈ candidateSource D default outer hclass hclassInj n)
    (hdist : HasRationalSqDist x y) :
    (A.frame n).IsRational x := by
  rcases hx with ⟨r, hrm, rfl⟩
  rcases hy with ⟨s, hsn, rfl⟩
  rcases lt_trichotomy r s with hrs | hrs | hsr
  · have h := earlierCandidate_rational_of_rationalSqDist D default outer
      hclass hclassInj hrs hdist
    simpa only [hsn] using h
  · subst s
    exact (Nat.ne_of_lt hmn (hrm.symm.trans hsn)).elim
  · exfalso
    have hyratM := earlierCandidate_rational_of_rationalSqDist D default outer
      hclass hclassInj hsr (by
        simpa only [HasRationalSqDist, distSq_comm] using hdist)
    have hyratN := candidatePoint_rational D default outer hclass hclassInj s
    have hnot :=
      (candidatePoint_properties D default outer hclass hclassInj s).2.2.2.1
    apply hnot
    refine ⟨(ScheduledRequirement.scheduled default r).index, ?_,
      (ScheduledRequirement.scheduled default r).active, hyratN, hyratM⟩
    simpa only [hrm, hsn] using hmn

/-- The outer forbidden-line theorem supplies the other half of (I5): a
candidate at source `n` can have rational squared distance from an outer-old
point only when that old point is itself rational in frame `n`. -/
theorem oldPoint_rational_of_rationalSqDist
    (circle : ThreeCircleFinitenessTheorem)
    {i : D.Index} {A : TerminalLayer} {old : Set Point}
    (hOld : IsPartialSteinhaus old)
    (hbefore : ∀ x ∈ old, Code.point x ∈ D.before i)
    (hclass : ∀ n ∈ A.active,
      Code.latticeClass (OrientedFrame.classOf (A.frame n)) ∈ D.layer i)
    (hclassInj : Set.InjOn
      (fun n ↦ OrientedFrame.classOf (A.frame n)) A.active)
    (default : ScheduledRequirement A)
    {n : ℕ} {x y : Point} (hx : x ∈ old)
    (hy : y ∈ candidateSource D default
      (outerForbiddenLines D circle hOld hbefore hclass)
      hclass hclassInj n)
    (hdist : HasRationalSqDist x y) :
    (A.frame n).IsRational x := by
  classical
  rcases hy with ⟨r, hrn, rfl⟩
  let req := ScheduledRequirement.scheduled default r
  by_contra hxirr
  have hxirr' : ¬(A.frame req.index).IsRational x := by
    simpa only [req, hrn] using hxirr
  have hp := candidatePoint_properties D default
    (outerForbiddenLines D circle hOld hbefore hclass)
    hclass hclassInj r
  have hyq := ResidueRequirement.mem_rationalTranslate hp.1
  obtain ⟨line, hlineOuter, hyline⟩ :=
    outerForbiddenLines_spec D circle hOld hbefore hclass req
      x hx hxirr'
      (candidatePoint D default
        (outerForbiddenLines D circle hOld hbefore hclass)
        hclass hclassInj r) hyq hdist
  have hlineAll : line ∈ candidateLines default
      (outerForbiddenLines D circle hOld hbefore hclass) r
      (fun k ↦ candidatePoint D default
        (outerForbiddenLines D circle hOld hbefore hclass)
        hclass hclassInj k.1) := by
    apply Finset.mem_union_left
    exact hlineOuter
  exact hp.2.2.1 line hlineAll hyline

end CodedDavies

/-- Rational-rotation transfer, exactly in the form needed after applying a
rich selector in one representative frame. -/
def RationalRotationTransferTheorem : Prop :=
  ∀ (S : Set Point) (L : OrientedFrame),
    IsPartialSteinhaus S → HitsRationalTranslates S L → HitsRationalClass S L

theorem rationalRotationTransfer : RationalRotationTransferTheorem := by
  intro S L hpartial hhits
  exact Erdos215.RationalRotationTransferTheorem S L hpartial hhits

lemma hitsRationalClass_mono {S T : Set Point} (hST : S ⊆ T)
    {L : OrientedFrame} (hS : HitsRationalClass S L) : HitsRationalClass T L := by
  intro K hKL
  obtain ⟨p, hpS, hpK⟩ := hS K hKL
  exact ⟨p, hST hpS, hpK⟩

/-- A rational squared distance.  This is the antecedent of invariant (I5),
not the stronger integral-distance conflict used by partiality. -/
def RationalSqDist (x y : Point) : Prop :=
  ∃ q : ℚ, distSq x y = (q : ℝ)

/-- The explanation demanded by (I5): both endpoints have rational
coordinates in a class processed at the current terminal layer. -/
def TerminalLayer.Explains (A : TerminalLayer) (x y : Point) : Prop :=
  ∃ n ∈ A.active, (A.frame n).IsRational x ∧ (A.frame n).IsRational y

/-- The finite inner state after processing the indices `< n` of one
terminal layer.  Unlike an arbitrary partial set, this state remembers (I3)
and (I5), so the known finite nonextendible examples cannot instantiate it. -/
structure TerminalState (A : TerminalLayer) (old : Set Point)
    (Located : Point → Prop) (Source : ℕ → Set Point) (n : ℕ) where
  selected : Set Point
  old_subset : old ⊆ selected
  isPartial : IsPartialSteinhaus selected
  hits_before : ∀ k < n, k ∈ A.active → HitsRationalClass selected (A.frame k)
  located_new : ∀ x ∈ selected, x ∉ old → Located x
  new_source : ∀ x ∈ selected, x ∉ old →
    ∃ k < n, k ∈ A.active ∧ x ∈ Source k
  explains_old_new : ∀ x ∈ old, ∀ y ∈ selected, y ∉ old →
    RationalSqDist x y → A.Explains x y

/-- A candidate pool with exactly the two additional conclusions obtained
from the Davies localization and forbidden-line arguments. -/
structure LocalizedCandidatePool (A : TerminalLayer) (old current : Set Point)
    (Located : Point → Prop) (Source : ℕ → Set Point) (n : ℕ)
    extends CandidatePool current (A.frame n) where
  located_fresh : ∀ y ∈ pool, y ∉ current → Located y
  fresh_source : ∀ y ∈ pool, y ∉ current → y ∈ Source n
  explains_fresh : ∀ x ∈ old, ∀ y ∈ pool, y ∉ current →
    RationalSqDist x y → A.Explains x y

namespace TerminalState

variable {A : TerminalLayer} {old : Set Point} {Located : Point → Prop}
    {Source : ℕ → Set Point}

def initial (hOld : IsPartialSteinhaus old) : TerminalState A old Located Source 0 where
  selected := old
  old_subset := Subset.rfl
  isPartial := hOld
  hits_before := by simp
  located_new := by
    intro x hx hnx
    exact (hnx hx).elim
  new_source := by
    intro x hx hnx
    exact (hnx hx).elim
  explains_old_new := by
    intro x hx y hy hny
    exact (hny hy).elim

/-- One active step of the terminal recursion.  The only imported arithmetic
fact is the rich-selector theorem; all old--new safety is visible in `C`. -/
noncomputable def activeStep (selector : RichSelectorTheorem)
    (transfer : RationalRotationTransferTheorem) (n : ℕ)
    (s : TerminalState A old Located Source n)
    (hn : n ∈ A.active)
    (C : LocalizedCandidatePool A old s.selected Located Source n) :
    TerminalState A old Located Source (n + 1) := by
  let witness := extendByCandidatePool selector s.isPartial (A.frame n) C.toCandidatePool
  let T : Set Point := Classical.choose witness
  have hT := Classical.choose_spec witness
  refine
    { selected := s.selected ∪ T
      old_subset := s.old_subset.trans subset_union_left
      isPartial := hT.2.1
      hits_before := ?_
      located_new := ?_
      new_source := ?_
      explains_old_new := ?_ }
  · intro k hk hkactive
    rcases Nat.lt_succ_iff_lt_or_eq.mp (by simpa using hk) with hkn | hkn
    · exact hitsRationalClass_mono subset_union_left
        (s.hits_before k hkn hkactive)
    · subst k
      exact hitsRationalClass_mono subset_union_right
        (transfer T (A.frame n)
          (fun x hx y hy hxy z ↦ hT.2.1 (Or.inr hx) (Or.inr hy) hxy z)
          hT.2.2)
  · intro x hx hxold
    rcases hx with hx | hx
    · exact s.located_new x hx hxold
    · by_cases hcurrent : x ∈ s.selected
      · exact s.located_new x hcurrent hxold
      · exact C.located_fresh x (hT.1 hx) hcurrent
  · intro x hx hxold
    rcases hx with hx | hx
    · obtain ⟨k, hk, hka, hsrc⟩ := s.new_source x hx hxold
      exact ⟨k, hk.trans (Nat.lt_succ_self n), hka, hsrc⟩
    · by_cases hcurrent : x ∈ s.selected
      · obtain ⟨k, hk, hka, hsrc⟩ := s.new_source x hcurrent hxold
        exact ⟨k, hk.trans (Nat.lt_succ_self n), hka, hsrc⟩
      · exact ⟨n, Nat.lt_succ_self n, hn, C.fresh_source x (hT.1 hx) hcurrent⟩
  · intro x hxold y hy hyold hr
    rcases hy with hy | hy
    · exact s.explains_old_new x hxold y hy hyold hr
    · by_cases hcurrent : y ∈ s.selected
      · exact s.explains_old_new x hxold y hcurrent hyold hr
      · exact C.explains_fresh x hxold y (hT.1 hy) hcurrent hr

def inactiveStep (n : ℕ) (s : TerminalState A old Located Source n)
    (hn : n ∉ A.active) :
    TerminalState A old Located Source (n + 1) where
  selected := s.selected
  old_subset := s.old_subset
  isPartial := s.isPartial
  hits_before := by
    intro k hk hkactive
    have hkn : k < n := by
      have hle : k ≤ n := Nat.le_of_lt_succ (by simpa using hk)
      exact hle.lt_of_ne (fun h ↦ by subst k; exact hn hkactive)
    exact s.hits_before k hkn hkactive
  located_new := s.located_new
  new_source := fun x hx hxold ↦ by
    obtain ⟨k, hk, hka, hsrc⟩ := s.new_source x hx hxold
    exact ⟨k, hk.trans (Nat.lt_succ_self n), hka, hsrc⟩
  explains_old_new := s.explains_old_new

/-- The exact pool-building obligation at an inner stage.  Its domain is a
state carrying the construction invariants, rather than an arbitrary partial
set.  The finite-forbidden-line proof supplies this obligation from the
three-circle theorem and Davies guards. -/
def PoolStepAvailable (A : TerminalLayer) (old : Set Point)
    (Located : Point → Prop) (Source : ℕ → Set Point) : Prop :=
  ∀ (n : ℕ) (s : TerminalState A old Located Source n), n ∈ A.active →
    Nonempty (LocalizedCandidatePool A old s.selected Located Source n)

/-- The actual natural-number recursion through a countable terminal layer. -/
noncomputable def run (selector : RichSelectorTheorem)
    (transfer : RationalRotationTransferTheorem)
    (hOld : IsPartialSteinhaus old)
    (pools : PoolStepAvailable A old Located Source) :
    (n : ℕ) → TerminalState A old Located Source n := by
  classical
  intro n
  induction n with
  | zero => exact initial hOld
  | succ n s =>
      by_cases hn : n ∈ A.active
      · exact activeStep selector transfer n s hn
          (Classical.choice (pools n s hn))
      · exact inactiveStep n s hn

theorem run_selected_mono_succ (selector : RichSelectorTheorem)
    (transfer : RationalRotationTransferTheorem)
    (hOld : IsPartialSteinhaus old)
    (pools : PoolStepAvailable A old Located Source) (n : ℕ) :
    (run selector transfer hOld pools n).selected ⊆
      (run selector transfer hOld pools (n + 1)).selected := by
  by_cases hn : n ∈ A.active
  · intro x hx
    simp only [run, dif_pos hn, activeStep]
    exact Or.inl hx
  · intro x hx
    simpa only [run, dif_neg hn, inactiveStep] using hx

theorem run_selected_mono (selector : RichSelectorTheorem)
    (transfer : RationalRotationTransferTheorem)
    (hOld : IsPartialSteinhaus old)
    (pools : PoolStepAvailable A old Located Source) {n m : ℕ} (hnm : n ≤ m) :
    (run selector transfer hOld pools n).selected ⊆
      (run selector transfer hOld pools m).selected := by
  induction m, hnm using Nat.le_induction with
  | base => exact Subset.rfl
  | succ m hnm ih =>
      exact ih.trans (run_selected_mono_succ selector transfer hOld pools m)

/-- The union of all finite inner states. -/
def runResult (selector : RichSelectorTheorem)
    (transfer : RationalRotationTransferTheorem)
    (hOld : IsPartialSteinhaus old)
    (pools : PoolStepAvailable A old Located Source) : Set Point :=
  ⋃ n, (run selector transfer hOld pools n).selected

theorem runResult_partial (selector : RichSelectorTheorem)
    (transfer : RationalRotationTransferTheorem)
    (hOld : IsPartialSteinhaus old)
    (pools : PoolStepAvailable A old Located Source) :
    IsPartialSteinhaus (runResult selector transfer hOld pools) := by
  intro x hx y hy hxy z
  rcases mem_iUnion.1 hx with ⟨n, hxn⟩
  rcases mem_iUnion.1 hy with ⟨m, hym⟩
  let k := max n m
  exact (run selector transfer hOld pools k).isPartial
    (run_selected_mono selector transfer hOld pools (Nat.le_max_left n m) hxn)
    (run_selected_mono selector transfer hOld pools (Nat.le_max_right n m) hym)
    hxy z

theorem runResult_old_subset (selector : RichSelectorTheorem)
    (transfer : RationalRotationTransferTheorem)
    (hOld : IsPartialSteinhaus old)
    (pools : PoolStepAvailable A old Located Source) :
    old ⊆ runResult selector transfer hOld pools := by
  intro x hx
  exact mem_iUnion.2 ⟨0, (run selector transfer hOld pools 0).old_subset hx⟩

theorem runResult_hits (selector : RichSelectorTheorem)
    (transfer : RationalRotationTransferTheorem)
    (hOld : IsPartialSteinhaus old)
    (pools : PoolStepAvailable A old Located Source) :
    A.Hits (runResult selector transfer hOld pools) := by
  intro n hn K hK
  have hh := (run selector transfer hOld pools (n + 1)).hits_before
    n (Nat.lt_succ_self n) hn K hK
  obtain ⟨p, hp, hpK⟩ := hh
  exact ⟨p, mem_iUnion.2 ⟨n + 1, hp⟩, hpK⟩

theorem runResult_located_new (selector : RichSelectorTheorem)
    (transfer : RationalRotationTransferTheorem)
    (hOld : IsPartialSteinhaus old)
    (pools : PoolStepAvailable A old Located Source) :
    ∀ x ∈ runResult selector transfer hOld pools, x ∉ old → Located x := by
  intro x hx hxold
  rcases mem_iUnion.1 hx with ⟨n, hxn⟩
  exact (run selector transfer hOld pools n).located_new x hxn hxold

theorem runResult_new_source (selector : RichSelectorTheorem)
    (transfer : RationalRotationTransferTheorem)
    (hOld : IsPartialSteinhaus old)
    (pools : PoolStepAvailable A old Located Source) :
    ∀ x ∈ runResult selector transfer hOld pools, x ∉ old →
      ∃ k, k ∈ A.active ∧ x ∈ Source k := by
  intro x hx hxold
  rcases mem_iUnion.1 hx with ⟨n, hxn⟩
  obtain ⟨k, -, hka, hsrc⟩ :=
    (run selector transfer hOld pools n).new_source x hxn hxold
  exact ⟨k, hka, hsrc⟩

theorem runResult_explains_old_new (selector : RichSelectorTheorem)
    (transfer : RationalRotationTransferTheorem)
    (hOld : IsPartialSteinhaus old)
    (pools : PoolStepAvailable A old Located Source) :
    ∀ x ∈ old, ∀ y ∈ runResult selector transfer hOld pools, y ∉ old →
      RationalSqDist x y → A.Explains x y := by
  intro x hx y hy hyold hr
  rcases mem_iUnion.1 hy with ⟨n, hyn⟩
  exact (run selector transfer hOld pools n).explains_old_new x hx y hyn hyold hr

end TerminalState

/-! ### Concrete terminal pool availability -/

/-- The precise one-cross invariant consumed by the terminal pool
constructor.  `GlobalOneCross.lean` derives it from the outer birth-block
invariants and Davies closure. -/
def TerminalLayer.OneCross (A : TerminalLayer) (old : Set Point)
    (Source : ℕ → Set Point) : Prop :=
  ∀ n ∈ A.active,
    {x | (x ∈ old ∨ ∃ m < n, m ∈ A.active ∧ x ∈ Source m) ∧
      (A.frame n).IsRational x}.Subsingleton

/-- Output of one complete countable terminal-layer recursion. -/
structure TerminalStageCertificate (A : TerminalLayer) (old : Set Point)
    (Located : Point → Prop) (Source : ℕ → Set Point) where
  selected : Set Point
  old_subset : old ⊆ selected
  isPartial : IsPartialSteinhaus selected
  hits : A.Hits selected
  located_new : ∀ x ∈ selected, x ∉ old → Located x
  new_source : ∀ x ∈ selected, x ∉ old →
    ∃ n ∈ A.active, x ∈ Source n
  explains_old_new : ∀ x ∈ old, ∀ y ∈ selected, y ∉ old →
    RationalSqDist x y → A.Explains x y

/-- Choose the unique point of a subsingleton set when it is inhabited. -/
noncomputable def optionalPoint (R : Set Point) : Option Point :=
  by
    classical
    exact if hR : R.Nonempty then some (Classical.choose hR) else none

theorem optionalPoint_mem {R : Set Point} {x : Point}
    (hx : optionalPoint R = some x) : x ∈ R := by
  classical
  rw [optionalPoint] at hx
  split at hx
  next hR =>
    injection hx with h
    simpa only [← h] using Classical.choose_spec hR
  next => simp at hx

theorem optionalPoint_eq_some {R : Set Point} (hR : R.Subsingleton)
    {x : Point} (hx : x ∈ R) : optionalPoint R = some x := by
  classical
  rw [optionalPoint, dif_pos ⟨x, hx⟩]
  congr
  exact hR (Classical.choose_spec ⟨x, hx⟩) hx

namespace CodedDavies

variable (D : DaviesDecomposition Code.skolem)

/-- The concrete forbidden-line/candidate-sequence construction discharges
the entire inner `PoolStepAvailable` obligation once the exact outer
one-cross invariant is supplied. -/
theorem poolStepAvailable
    (circle : ThreeCircleFinitenessTheorem)
    {i : D.Index} {A : TerminalLayer} {old : Set Point}
    (hOld : IsPartialSteinhaus old)
    (hbefore : ∀ x ∈ old, Code.point x ∈ D.before i)
    (hclass : ∀ n ∈ A.active,
      Code.latticeClass (OrientedFrame.classOf (A.frame n)) ∈ D.layer i)
    (hclassInj : Set.InjOn
      (fun n ↦ OrientedFrame.classOf (A.frame n)) A.active)
    (default : ScheduledRequirement A)
    (hone : A.OneCross old
      (candidateSource D default
        (outerForbiddenLines D circle hOld hbefore hclass)
        hclass hclassInj)) :
    TerminalState.PoolStepAvailable A old
      (fun x ↦ Code.point x ∈ D.layer i)
      (candidateSource D default
        (outerForbiddenLines D circle hOld hbefore hclass)
        hclass hclassInj) := by
  classical
  let outer := outerForbiddenLines D circle hOld hbefore hclass
  let Source := candidateSource D default outer hclass hclassInj
  intro n s hn
  let R : Set Point :=
    {x | x ∈ s.selected ∧ (A.frame n).IsRational x}
  have hR : R.Subsingleton := by
    intro x hx y hy
    apply hone n hn
    · refine ⟨?_, hx.2⟩
      by_cases hxold : x ∈ old
      · exact Or.inl hxold
      · obtain ⟨m, hmn, hm, hxm⟩ := s.new_source x hx.1 hxold
        exact Or.inr ⟨m, hmn, hm, hxm⟩
    · refine ⟨?_, hy.2⟩
      by_cases hyold : y ∈ old
      · exact Or.inl hyold
      · obtain ⟨m, hmn, hm, hym⟩ := s.new_source y hy.1 hyold
        exact Or.inr ⟨m, hmn, hm, hym⟩
  let w := optionalPoint R
  let P : Set Point := Source n ∪ {x | w = some x}
  refine ⟨{
    pool := P
    distinguished := w
    rich := ?_
    rational := ?_
    distinguished_mem := ?_
    old_safe := ?_
    located_fresh := ?_
    fresh_source := ?_
    explains_fresh := ?_ }⟩
  · intro d hd ri rj a b
    apply (candidateSource_rich D default outer hclass hclassInj hn
      d hd ri rj a b).mono
    intro x hx
    rcases hx with ⟨k, l, heq, hka, hlb, hsource⟩
    exact ⟨k, l, heq, hka, hlb, Or.inl hsource⟩
  · intro x hx
    rcases hx with hx | hx
    · exact candidateSource_rational D default outer hclass hclassInj hx
    · exact (optionalPoint_mem hx).2
  · intro x hx
    have hxR := optionalPoint_mem hx
    exact ⟨hxR.1, Or.inr hx⟩
  · intro x hx y hy hnot hxy z hdist
    have hratdist : HasRationalSqDist x y := by
      refine ⟨(z : ℚ), ?_⟩
      exact_mod_cast hdist
    rcases hy with hysource | hyv
    · have hxrat : (A.frame n).IsRational x := by
        by_cases hxold : x ∈ old
        · exact oldPoint_rational_of_rationalSqDist D circle hOld hbefore
            hclass hclassInj default hxold hysource hratdist
        · obtain ⟨m, hmn, hm, hxm⟩ := s.new_source x hx hxold
          exact sourcePoint_rational_of_rationalSqDist D default outer
            hclass hclassInj hmn hxm hysource hratdist
      exact hnot (optionalPoint_eq_some hR ⟨hx, hxrat⟩)
    · have hyR := optionalPoint_mem hyv
      exact s.isPartial hx hyR.1 hxy z hdist
  · intro y hy hycurrent
    rcases hy with hysource | hyv
    · exact candidateSource_located D default outer hclass hclassInj hysource
    · exact (hycurrent (optionalPoint_mem hyv).1).elim
  · intro y hy hycurrent
    rcases hy with hysource | hyv
    · exact hysource
    · exact (hycurrent (optionalPoint_mem hyv).1).elim
  · intro x hxold y hy hycurrent hdist
    rcases hy with hysource | hyv
    · refine ⟨n, hn, ?_, ?_⟩
      · apply oldPoint_rational_of_rationalSqDist D circle hOld hbefore
          hclass hclassInj default hxold hysource
        simpa only [RationalSqDist, HasRationalSqDist] using hdist
      · exact candidateSource_rational D default outer hclass hclassInj hysource
    · exact (hycurrent (optionalPoint_mem hyv).1).elim

/-- Running the verified inner recursion produces all terminal-stage
invariants needed by the outer birth-block recursion. -/
noncomputable def terminalStage
    (selector : RichSelectorTheorem)
    (circle : ThreeCircleFinitenessTheorem)
    {i : D.Index} {A : TerminalLayer} {old : Set Point}
    (hOld : IsPartialSteinhaus old)
    (hbefore : ∀ x ∈ old, Code.point x ∈ D.before i)
    (hclass : ∀ n ∈ A.active,
      Code.latticeClass (OrientedFrame.classOf (A.frame n)) ∈ D.layer i)
    (hclassInj : Set.InjOn
      (fun n ↦ OrientedFrame.classOf (A.frame n)) A.active)
    (default : ScheduledRequirement A)
    (hone : A.OneCross old
      (candidateSource D default
        (outerForbiddenLines D circle hOld hbefore hclass)
        hclass hclassInj)) :
    TerminalStageCertificate A old
      (fun x ↦ Code.point x ∈ D.layer i)
      (candidateSource D default
        (outerForbiddenLines D circle hOld hbefore hclass)
        hclass hclassInj) := by
  let Source := candidateSource D default
    (outerForbiddenLines D circle hOld hbefore hclass) hclass hclassInj
  let pools := poolStepAvailable D circle hOld hbefore hclass hclassInj default hone
  let S := TerminalState.runResult selector rationalRotationTransfer hOld pools
  exact {
    selected := S
    old_subset := TerminalState.runResult_old_subset
      selector rationalRotationTransfer hOld pools
    isPartial := TerminalState.runResult_partial
      selector rationalRotationTransfer hOld pools
    hits := TerminalState.runResult_hits
      selector rationalRotationTransfer hOld pools
    located_new := TerminalState.runResult_located_new
      selector rationalRotationTransfer hOld pools
    new_source := TerminalState.runResult_new_source
      selector rationalRotationTransfer hOld pools
    explains_old_new := TerminalState.runResult_explains_old_new
      selector rationalRotationTransfer hOld pools }

end CodedDavies

/-- A verified family of newly-added blocks indexed by terminal stages.
These are precisely the global invariants (I2)--(I5), expressed using birth
blocks rather than nested cumulative sets. -/
structure BlockFamily (I : Type) (lt : I → I → Prop)
    (layer : I → TerminalLayer) where
  block : I → Set Point
  block_partial : ∀ i, IsPartialSteinhaus (block i)
  earlier_separated : ∀ i j, lt i j →
    ∀ x ∈ block i, ∀ y ∈ block j, Separated x y
  hits_up_to : ∀ i, (layer i).Hits
    ({x | ∃ j, lt j i ∧ x ∈ block j} ∪ block i)
  located : I → Point → Prop
  first_added_located : ∀ i x, x ∈ block i → located i x
  old_new_explained : ∀ i j, lt i j →
    ∀ x ∈ block i, ∀ y ∈ block j,
      RationalSqDist x y → (layer j).Explains x y

namespace BlockFamily

variable {I : Type} {r : I → I → Prop} {layer : I → TerminalLayer}
    (B : BlockFamily I r layer)

def result : Set Point := ⋃ i, B.block i

/-- The global partial-Steinhaus conclusion.  Only total comparability of the
terminal well-order is used here; no countability assumption on its initial
segments occurs. -/
theorem result_partial (hTotal : ∀ i j, i = j ∨ r i j ∨ r j i) :
    IsPartialSteinhaus B.result := by
  intro x hx y hy hxy z
  rcases mem_iUnion.1 hx with ⟨i, hxi⟩
  rcases mem_iUnion.1 hy with ⟨j, hyj⟩
  rcases hTotal i j with rfl | hij | hji
  · exact B.block_partial i hxi hyj hxy z
  · exact B.earlier_separated i j hij x hxi y hyj hxy z
  · exact (separated_comm.mp
      (B.earlier_separated j i hji y hyj x hxi)) hxy z

theorem result_hits (i : I) : (layer i).Hits B.result := by
  intro n hn K hK
  obtain ⟨p, hp, hpK⟩ := B.hits_up_to i n hn K hK
  rcases hp with ⟨j, -, hpj⟩ | hpi
  · exact ⟨p, mem_iUnion.2 ⟨j, hpj⟩, hpK⟩
  · exact ⟨p, mem_iUnion.2 ⟨i, hpi⟩, hpK⟩

end BlockFamily

/-- Every oriented integer lattice is met. -/
def HitsAllFrames (S : Set Point) : Prop :=
  ∀ L : OrientedFrame, ∃ p : Point, p ∈ S ∧ L.IsLatticePoint p

lemma inverseMotion_eq_framePoint (t : Point) (c s : ℝ)
    (hcs : c ^ 2 + s ^ 2 = 1) (z : IntPoint) :
    let L : OrientedFrame :=
      { origin := inverseMotion t c s 0
        c := c
        s := -s
        unit := by nlinarith }
    inverseMotion t c s (intPoint z) = L.fromCoords (intPoint z) := by
  dsimp [OrientedFrame.fromCoords, inverseMotion]
  rw [rotate_sub]
  simp only [sub_zero, zero_sub, rotate_neg, rotate_zero]
  module

/-- Hitting every concrete oriented frame implies the public
`HitsEveryLattice` normal form. -/
theorem hitsEveryLattice_of_hitsAllFrames {S : Set Point}
    (hS : HitsAllFrames S) : HitsEveryLattice S := by
  intro t c s hcs
  let L : OrientedFrame :=
    { origin := inverseMotion t c s 0
      c := c
      s := -s
      unit := by nlinarith }
  obtain ⟨p, hpS, z, hpz⟩ := hS L
  refine ⟨z, ?_⟩
  rw [inverseMotion_eq_framePoint t c s hcs z, ← hpz]
  exact hpS

namespace CodedDavies

variable (D : DaviesDecomposition Code.skolem)

theorem blockFamily_hitsAllFrames
    (B : BlockFamily D.Index D.lt (terminalLayer D)) :
    HitsAllFrames B.result := by
  intro K
  obtain ⟨i, n, hn, hclass⟩ := every_class_appears D (OrientedFrame.classOf K)
  have hKL : K.RationallyEquivalent ((terminalLayer D i).frame n) := by
    apply (OrientedFrame.classOf_eq_iff K ((terminalLayer D i).frame n)).1
    exact hclass.symm
  exact (B.result_hits i) n hn K hKL

/-- The exact final outer-union conclusion from verified birth blocks. -/
theorem blockFamily_strong
    (B : BlockFamily D.Index D.lt (terminalLayer D)) :
    ∃ S : Set Point, IsPartialSteinhaus S ∧ HitsEveryLattice S := by
  letI : IsWellOrder D.Index D.lt := D.isWellOrder
  refine ⟨B.result, ?_, hitsEveryLattice_of_hitsAllFrames (blockFamily_hitsAllFrames D B)⟩
  apply B.result_partial
  intro i j
  rcases trichotomous_of D.lt i j with hij | hij | hij
  · exact Or.inr (Or.inl hij)
  · exact Or.inl hij
  · exact Or.inr (Or.inr hij)

end CodedDavies

end Global

end

end Erdos215
