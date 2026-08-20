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

import ErdosProblems.Erdos735.RedSectorGeometry
import ErdosProblems.Erdos735.RedChordSector
import ErdosProblems.Erdos735.SignVectorDoubleRestrictionCount
import ErdosProblems.Erdos735.ConcretePolarOrientedAcross
import ErdosProblems.Erdos735.RedChordPolarBoundary
import ErdosProblems.Erdos735.RedBlueDualIncidence
import ErdosProblems.Erdos735.PolarRedChordExtraction

open Classical
open scoped Matrix
open Matrix

namespace Erdos735.SignVector.LocalReceiver

/-!
# Exact receiver count at a multiplicity-two blue vertex

A red projective line through a crossing of exactly two blue lines enters
exactly two of the four oriented blue sectors.  This file proves that local
fact directly with homogeneous sign vectors, transports weak sectors to the
concrete polar boundary, and packages the cardinality statement in the form
required by `ABKPR.Data.badVertex_receiverCount`.
-/

open RedChordSector
open Erdos735.RedBlueDualIncidence

variable {I : Type*} [Fintype I]

noncomputable def localReceiverFaces (n : I → Vec3) (r y : Vec3) :
    Finset (StrictFace n) :=
  Finset.univ.filter fun f ↦ WeaklyRealizes n f.1 y ∧
    RestrictedRealizable n r f.1

omit [Fintype I] in
lemma sign_eq_of_weak_of_dot_ne_zero
    {n : I → Vec3} {s t : I → Bool} {y : Vec3} {i : I}
    (hs : WeaklyRealizes n s y) (ht : WeaklyRealizes n t y)
    (hi : dotProduct (n i) y ≠ 0) : s i = t i := by
  rcases lt_or_gt_of_ne hi with hneg | hpos
  · have hsfalse : s i = false := by
      cases hsi : s i
      · rfl
      · have := hs i
        simp [signed, hsi] at this
        linarith
    have htfalse : t i = false := by
      cases hti : t i
      · rfl
      · have := ht i
        simp [signed, hti] at this
        linarith
    rw [hsfalse, htfalse]
  · have hstrue : s i = true := by
      cases hsi : s i
      · have := hs i
        simp [signed, hsi] at this
        linarith
      · rfl
    have httrue : t i = true := by
      cases hti : t i
      · have := ht i
        simp [signed, hti] at this
        linarith
      · rfl
    rw [hstrue, httrue]

lemma bool_eq_not_of_ne {a b : Bool} (h : a ≠ b) : a = !b := by
  cases a <;> cases b <;> simp_all

lemma bool_eq_of_ne_ne {a b c : Bool} (hab : a ≠ b) (hcb : c ≠ b) : c = a := by
  cases a <;> cases b <;> cases c <;> simp_all

/-- A red plane through a crossing with exactly two active blue normals
meets exactly two of the strict blue sectors incident with the chosen
oriented crossing. -/
theorem localReceiverFaces_card_eq_two
    (n : I → Vec3) (r y z : Vec3) (i j : I)
    (hy0 : y ≠ 0) (hr0 : r ≠ 0)
    (hry : dotProduct r y = 0) (hrz : dotProduct r z = 0)
    (hzeros : ∀ k, dotProduct (n k) y = 0 ↔ k = i ∨ k = j)
    (hz : ∀ k, dotProduct (n k) y = 0 → dotProduct (n k) z ≠ 0) :
    (localReceiverFaces n r y).card = 2 := by
  let K := {k : I // dotProduct (n k) y ≠ 0}
  let nK : K → Vec3 := fun k ↦ n k.1
  let sK : K → Bool := strictSignAt nK y
  have hyK : Realizes nK sK y :=
    (realizes_strictSignAt_iff nK y).2 (fun k ↦ k.2)
  obtain ⟨c, hc, hpK, hmK⟩ := exists_small_perturbation nK sK hyK z
  let p : Vec3 := y + c • z
  let m : Vec3 := y - c • z
  have hpK' : Realizes nK sK p := hpK
  have hmK' : Realizes nK sK m := hmK
  have hpne : ∀ k, dotProduct (n k) p ≠ 0 := by
    intro k
    by_cases hk : dotProduct (n k) y = 0
    · have hkz := hz k hk
      simp only [p, dotProduct_add, dotProduct_smul, smul_eq_mul, hk, zero_add]
      exact mul_ne_zero hc.ne' hkz
    · have hkpos := hpK' ⟨k, hk⟩
      intro hzero
      rw [hzero] at hkpos
      cases h : sK ⟨k, hk⟩ <;> simp [signed, h] at hkpos
  have hmne : ∀ k, dotProduct (n k) m ≠ 0 := by
    intro k
    by_cases hk : dotProduct (n k) y = 0
    · have hkz := hz k hk
      simp only [m, dotProduct_sub, dotProduct_smul, smul_eq_mul, hk, zero_sub]
      exact neg_ne_zero.mpr (mul_ne_zero hc.ne' hkz)
    · have hkpos := hmK' ⟨k, hk⟩
      intro hzero
      rw [hzero] at hkpos
      cases h : sK ⟨k, hk⟩ <;> simp [signed, h] at hkpos
  let sp : I → Bool := strictSignAt n p
  let sm : I → Bool := strictSignAt n m
  have hpreal : Realizes n sp p := (realizes_strictSignAt_iff n p).2 hpne
  have hmreal : Realizes n sm m := (realizes_strictSignAt_iff n m).2 hmne
  let fp : StrictFace n := ⟨sp, ⟨p, hpreal⟩⟩
  let fm : StrictFace n := ⟨sm, ⟨m, hmreal⟩⟩
  have hspK : ∀ k : K, sp k.1 = sK k := by
    intro k
    have h := congrFun (eq_strictSignAt_of_realizes nK p sK hpK') k
    exact h.symm
  have hsmK : ∀ k : K, sm k.1 = sK k := by
    intro k
    have h := congrFun (eq_strictSignAt_of_realizes nK m sK hmK') k
    exact h.symm
  have hspweak : WeaklyRealizes n sp y := by
    intro k
    by_cases hk : dotProduct (n k) y = 0
    · rw [hk]
      cases sp k <;> simp [signed]
    · rw [hspK ⟨k, hk⟩]
      exact (hyK ⟨k, hk⟩).le
  have hsmweak : WeaklyRealizes n sm y := by
    intro k
    by_cases hk : dotProduct (n k) y = 0
    · rw [hk]
      cases sm k <;> simp [signed]
    · rw [hsmK ⟨k, hk⟩]
      exact (hyK ⟨k, hk⟩).le
  have hpres : RestrictedRealizable n r sp := by
    refine ⟨p, hpreal, ?_⟩
    simp [p, dotProduct_add, dotProduct_smul, smul_eq_mul, hry, hrz]
  have hmres : RestrictedRealizable n r sm := by
    refine ⟨m, hmreal, ?_⟩
    simp [m, dotProduct_sub, dotProduct_smul, smul_eq_mul, hry, hrz]
  have hspi : sp i ≠ sm i := by
    have hiy := (hzeros i).2 (Or.inl rfl)
    have hiz := hz i hiy
    have hpv := hpreal i
    have hmv := hmreal i
    simp only [p, m, dotProduct_add, dotProduct_sub, dotProduct_smul,
      smul_eq_mul, hiy, zero_add, zero_sub] at hpv hmv
    intro heq
    rw [heq] at hpv
    cases h : sm i <;> simp [signed, h] at hpv hmv <;> nlinarith
  have hspj : sp j ≠ sm j := by
    have hjy := (hzeros j).2 (Or.inr rfl)
    have hjz := hz j hjy
    have hpv := hpreal j
    have hmv := hmreal j
    simp only [p, m, dotProduct_add, dotProduct_sub, dotProduct_smul,
      smul_eq_mul, hjy, zero_add, zero_sub] at hpv hmv
    intro heq
    rw [heq] at hpv
    cases h : sm j <;> simp [signed, h] at hpv hmv <;> nlinarith
  have hfpne : fp ≠ fm := by
    intro h
    exact hspi (congrArg (fun f : StrictFace n ↦ f.1 i) h)
  have hset : localReceiverFaces n r y = {fp, fm} := by
    ext f
    simp only [localReceiverFaces, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hfweak, hfres⟩
      have hfi : f.1 i = sp i ∨ f.1 i = sm i := by
        by_cases h : f.1 i = sp i
        · exact Or.inl h
        · exact Or.inr (bool_eq_of_ne_ne hspi.symm h)
      rcases hfi with hfi | hfi
      · left
        apply Subtype.ext
        funext k
        by_cases hky : dotProduct (n k) y = 0
        · rcases (hzeros k).1 hky with hki | hkj
          · subst k
            exact hfi
          · subst k
            by_contra hfj
            exact not_restrictedRealizable_of_flip_right n r y i j sp f.1
              hy0 hr0 ((hzeros i).2 (Or.inl rfl))
              ((hzeros j).2 (Or.inr rfl)) hry hfi
              (bool_eq_not_of_ne hfj) hpres hfres
        · exact sign_eq_of_weak_of_dot_ne_zero hfweak hspweak hky
      · right
        apply Subtype.ext
        funext k
        by_cases hky : dotProduct (n k) y = 0
        · rcases (hzeros k).1 hky with hki | hkj
          · subst k
            exact hfi
          · subst k
            by_contra hfj
            exact not_restrictedRealizable_of_flip_right n r y i j sm f.1
              hy0 hr0 ((hzeros i).2 (Or.inl rfl))
              ((hzeros j).2 (Or.inr rfl)) hry hfi
              (bool_eq_not_of_ne hfj) hmres hfres
        · exact sign_eq_of_weak_of_dot_ne_zero hfweak hsmweak hky
    · rintro (rfl | rfl)
      · exact ⟨hspweak, hpres⟩
      · exact ⟨hsmweak, hmres⟩
  rw [hset, Finset.card_pair]
  exact hfpne

/-- At three distinct projective lines through one point, the tangent in
the red plane perpendicular to one blue normal is transverse to the other
blue normal as well. -/
lemma dot_kernelPerturbation_ne_zero_of_common_point
    {r u v y : Vec3}
    (hy0 : y ≠ 0) (hr0 : r ≠ 0)
    (hru : r ⨯₃ u ≠ 0) (hrv : r ⨯₃ v ≠ 0)
    (hry : dotProduct r y = 0)
    (huy : dotProduct u y = 0) (hvy : dotProduct v y = 0) :
    dotProduct v (kernelPerturbation r u) ≠ 0 := by
  let z := kernelPerturbation r u
  let q := kernelPerturbation r v
  have huz : 0 < dotProduct u z := dot_kernelPerturbation_right_pos hru
  have hvq : 0 < dotProduct v q := dot_kernelPerturbation_right_pos hrv
  have hrz : dotProduct r z = 0 := dot_kernelPerturbation_left r u
  have hrq : dotProduct r q = 0 := dot_kernelPerturbation_left r v
  have hratio : dotProduct u z * dotProduct v q =
      dotProduct v z * dotProduct u q := by
    have h := incident_dot_crossRatio
      (u := ProjectiveDuality.fromCoordinates u)
      (v := ProjectiveDuality.fromCoordinates v)
      (r := ProjectiveDuality.fromCoordinates r)
      (x := ProjectiveDuality.fromCoordinates y)
      (y := ProjectiveDuality.fromCoordinates z)
      (z := ProjectiveDuality.fromCoordinates q)
      (by
        rw [← ProjectiveDuality.toCoordinates_ne_zero_iff]
        simpa using hy0)
      (by
        rw [← ProjectiveDuality.toCoordinates_ne_zero_iff]
        simpa using hr0)
      (by simpa [dot_fromCoordinates_fromCoordinates] using huy)
      (by simpa [dot_fromCoordinates_fromCoordinates] using hvy)
      (by simpa [dot_fromCoordinates_fromCoordinates] using hry)
      (by simpa [dot_fromCoordinates_fromCoordinates] using hrz)
      (by simpa [dot_fromCoordinates_fromCoordinates] using hrq)
    simpa [dot_fromCoordinates_fromCoordinates] using h
  intro hvz
  rw [hvz, zero_mul] at hratio
  nlinarith

end Erdos735.SignVector.LocalReceiver

namespace Erdos735.ConcreteBadReceiver

open ProjectiveArrangement ProjectiveBoundaryExtraction ChartOrder
open SignVector SignVector.LocalReceiver SignVector.RedChordSector
open SignVector.PolarFace SignVector.PolarBoundaryOrder SignVector.PolarBoundaryAcross
open ConcretePolarOrientedVertex

variable {P : Finset Point}

/-- An oriented projective arrangement vertex occurs on the concrete polar
boundary of a face exactly when its canonical representative weakly realizes
that face. -/
theorem exists_boundaryOrientedVertex_eq_iff_weaklyRealizes
    {B : Finset Point} [Nonempty (ProjectiveBoundaryExtraction.Line B)]
    (hspan : Submodule.span ℝ (Set.range (normals B)) = ⊤)
    (f : StrictFace (normals B)) (v : OrientedVertex B) :
    (∃ i : BoundaryIndex (normals B) f,
      boundaryOrientedVertex hspan f i = v) ↔
      WeaklyRealizes (normals B) f.1 (orientedRep v) := by
  constructor
  · rintro ⟨i, rfl⟩
    exact orientedRep_boundaryOrientedVertex_weaklyRealizes hspan f i
  · intro hvweak
    let y := orientedRep v
    have hy0 : y ≠ 0 := orientedRep_ne_zero v
    have hyvertex : Projectivization.mk ℝ y hy0 ∈ projectiveVertices B := by
      rw [orientedRep_projectivization v]
      exact v.1.2
    obtain ⟨t, ht⟩ :=
      RedChordPolarBoundary.weak_projectiveVertex_eq_boundaryProjectiveVertex
        (faceWitness_realizes (normals B) f) hspan hy0 hvweak hyvertex
    let i : BoundaryIndex (normals B) f := finRotate _ t
    have hproj : boundaryVertex (normals B) normal_cross hspan f i = v.1.1 := by
      change boundaryProjectiveVertex f (faceWitness_realizes (normals B) f)
        normal_cross hspan ((finRotate _).symm i) = v.1.1
      rw [show (finRotate _).symm i = t by
        exact (finRotate _).symm_apply_apply t]
      exact ht.symm.trans (orientedRep_projectivization v)
    refine ⟨i, ?_⟩
    let q := boundaryCornerVector hspan f i
    have hq0 : q ≠ 0 := boundaryCornerVector_ne_zero hspan f i
    have hqweak : WeaklyRealizes (normals B) f.1 q :=
      cornerVector_weaklyRealizes f (faceWitness_realizes (normals B) f)
        normal_cross hspan ((finRotate _).symm i)
    have hqpos : 0 < dotProduct (orientedSum (normals B) f.1) q :=
      orientedSum_dot_pos_of_weak_of_span
        (faceWitness_realizes (normals B) f) hspan hq0 hqweak
    have hypos : 0 < dotProduct (orientedSum (normals B) f.1) y :=
      orientedSum_dot_pos_of_weak_of_span
        (faceWitness_realizes (normals B) f) hspan hy0 hvweak
    have hmk : Projectivization.mk ℝ q hq0 =
        Projectivization.mk ℝ y hy0 := by
      rw [boundaryCorner_projectivization hspan f i,
        orientedRep_projectivization v]
      exact hproj
    obtain ⟨a, ha⟩ :=
      (Projectivization.mk_eq_mk_iff' ℝ q y hq0 hy0).mp hmk
    have hdot := congrArg (fun u : Vec3 ↦
      dotProduct (orientedSum (normals B) f.1) u) ha
    simp only [dotProduct_smul, smul_eq_mul] at hdot
    have ha_pos : 0 < a := by nlinarith
    have hchart := congrArg (chartF B) ha
    simp only [map_smul, smul_eq_mul] at hchart
    apply Prod.ext
    · apply Subtype.ext
      exact hproj
    · change decide (0 < chartF B q) = v.2
      rw [← orientedRep_sheet v]
      apply Bool.decide_congr
      rw [← hchart]
      exact mul_pos_iff_of_pos_left ha_pos

/-- Concrete reduced-magic specialization of the exact local two-sector
count.  The red point is disjoint from the blue set, so its dual line is
transverse to both blue lines at the multiplicity-two crossing. -/
theorem localReceiverFaces_card_eq_two_at_badVertex
    [Nonempty (ProjectiveBoundaryExtraction.Line (nonordinaryPoints P))]
    (v : OrientedVertex (nonordinaryPoints P))
    (hmult : lineMultiplicity (OnLine (nonordinaryPoints P)) v.1 = 2)
    {a : Point} (ha : a ∈ ordinaryPoints P)
    (hainc : Incident v.1.1 a) :
    (localReceiverFaces (normals (nonordinaryPoints P)) (normalVec a)
      (orientedRep v)).card = 2 := by
  let B := nonordinaryPoints P
  let n := normals B
  let y := orientedRep v
  have hy0 : y ≠ 0 := orientedRep_ne_zero v
  have hS : (Finset.univ.filter fun l : ProjectiveBoundaryExtraction.Line B ↦
      OnLine B v.1 l).card = 2 :=
    hmult
  obtain ⟨i, j, -, hpair⟩ := Finset.card_eq_two.mp hS
  have hii : OnLine B v.1 i := by
    have : i ∈ (Finset.univ.filter fun l : ProjectiveBoundaryExtraction.Line B ↦
        OnLine B v.1 l) := by
      rw [hpair]
      simp
    simpa using (Finset.mem_filter.mp this).2
  have hjj : OnLine B v.1 j := by
    have : j ∈ (Finset.univ.filter fun l : ProjectiveBoundaryExtraction.Line B ↦
        OnLine B v.1 l) := by
      rw [hpair]
      simp
    simpa using (Finset.mem_filter.mp this).2
  have hzeros : ∀ k, dotProduct (n k) y = 0 ↔ k = i ∨ k = j := by
    intro k
    have hinc : dotProduct (n k) y = 0 ↔ OnLine B v.1 k := by
      change dotProduct (normalVec k.1) y = 0 ↔ Incident v.1.1 k.1
      rw [← orientedRep_projectivization v]
      exact (onProjectiveLine_mk_iff (normalVec k.1) y hy0).symm
    rw [hinc]
    constructor
    · intro hk
      have hmem : k ∈ (Finset.univ.filter
          fun l : ProjectiveBoundaryExtraction.Line B ↦ OnLine B v.1 l) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩
      rw [hpair] at hmem
      simpa using hmem
    · rintro (rfl | rfl)
      · exact hii
      · exact hjj
  have hai : a ≠ i.1 := by
    intro hai
    have hiB : i.1 ∈ nonordinaryPoints P := i.2
    exact (Finset.disjoint_left.mp
      (disjoint_ordinaryPoints_nonordinaryPoints P)) ha (hai ▸ hiB)
  have haj : a ≠ j.1 := by
    intro haj
    have hjB : j.1 ∈ nonordinaryPoints P := j.2
    exact (Finset.disjoint_left.mp
      (disjoint_ordinaryPoints_nonordinaryPoints P)) ha (haj ▸ hjB)
  have hru : normalVec a ⨯₃ n i ≠ 0 := normalVec_cross_ne_zero hai
  have hrv : normalVec a ⨯₃ n j ≠ 0 := normalVec_cross_ne_zero haj
  have hry : dotProduct (normalVec a) y = 0 := by
    apply (onProjectiveLine_mk_iff (normalVec a) y hy0).mp
    rw [orientedRep_projectivization v]
    exact hainc
  let z := kernelPerturbation (normalVec a) (n i)
  have hrz : dotProduct (normalVec a) z = 0 :=
    dot_kernelPerturbation_left (normalVec a) (n i)
  have hz : ∀ k, dotProduct (n k) y = 0 → dotProduct (n k) z ≠ 0 := by
    intro k hk
    rcases (hzeros k).1 hk with hki | hkj
    · subst k
      exact (dot_kernelPerturbation_right_pos hru).ne'
    · subst k
      exact dot_kernelPerturbation_ne_zero_of_common_point hy0
        (normalVec_ne_zero a) hru hrv hry
        ((hzeros i).2 (Or.inl rfl)) ((hzeros j).2 (Or.inr rfl))
  exact localReceiverFaces_card_eq_two n (normalVec a) y z i j hy0
    (normalVec_ne_zero a) hry hrz hzeros hz

/-- Boundary-index form of the local count: exactly two concrete polar
faces have `v` as a boundary corner and are feasible on the incident red
line. -/
theorem boundaryReceiverFaces_card_eq_two_at_badVertex
    [Nonempty (ProjectiveBoundaryExtraction.Line (nonordinaryPoints P))]
    (hspan : Submodule.span ℝ
      (Set.range (normals (nonordinaryPoints P))) = ⊤)
    (v : OrientedVertex (nonordinaryPoints P))
    (hmult : lineMultiplicity (OnLine (nonordinaryPoints P)) v.1 = 2)
    {a : Point} (ha : a ∈ ordinaryPoints P)
    (hainc : Incident v.1.1 a) :
    (Finset.univ.filter fun f : StrictFace (normals (nonordinaryPoints P)) ↦
      ∃ i : BoundaryIndex (normals (nonordinaryPoints P)) f,
        boundaryOrientedVertex hspan f i = v ∧
          RestrictedRealizable (normals (nonordinaryPoints P))
            (normalVec a) f.1).card = 2 := by
  have hset :
      (Finset.univ.filter fun f : StrictFace (normals (nonordinaryPoints P)) ↦
        ∃ i : BoundaryIndex (normals (nonordinaryPoints P)) f,
          boundaryOrientedVertex hspan f i = v ∧
            RestrictedRealizable (normals (nonordinaryPoints P))
              (normalVec a) f.1) =
        localReceiverFaces (normals (nonordinaryPoints P)) (normalVec a)
          (orientedRep v) := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, localReceiverFaces]
    constructor
    · rintro ⟨i, hiv, hrest⟩
      exact ⟨(exists_boundaryOrientedVertex_eq_iff_weaklyRealizes
        hspan f v).1 ⟨i, hiv⟩, hrest⟩
    · rintro ⟨hweak, hrest⟩
      obtain ⟨i, hiv⟩ :=
        (exists_boundaryOrientedVertex_eq_iff_weaklyRealizes hspan f v).2 hweak
      exact ⟨i, hiv, hrest⟩
  rw [hset]
  exact localReceiverFaces_card_eq_two_at_badVertex v hmult ha hainc

/-- Stage-1 corners on the literal, unreindexed polar boundary. -/
noncomputable def polarStage1Corners
    [Nonempty (ProjectiveBoundaryExtraction.Line (nonordinaryPoints P))]
    {w : Point → ℝ} {c : ℝ} (hred : IsReducedMagic P w c)
    (hspan : Submodule.span ℝ
      (Set.range (normals (nonordinaryPoints P))) = ⊤)
    (f : StrictFace (normals (nonordinaryPoints P))) :
    Finset (BoundaryIndex (normals (nonordinaryPoints P)) f) :=
  (PolarRedChordExtraction.redEndpoints hred hspan f).filter fun i ↦
    lineMultiplicity (OnLine (nonordinaryPoints P))
      (boundaryOrientedVertex hspan f i).1 = 2

/-- A literal polar corner is a red endpoint exactly when some feasible
ordinary dual line is incident with its projective vertex. -/
theorem mem_polarRedEndpoints_iff_exists_feasible_incident
    [Nonempty (ProjectiveBoundaryExtraction.Line (nonordinaryPoints P))]
    {w : Point → ℝ} {c : ℝ} (hred : IsReducedMagic P w c)
    (hspan : Submodule.span ℝ
      (Set.range (normals (nonordinaryPoints P))) = ⊤)
    (f : StrictFace (normals (nonordinaryPoints P)))
    (i : BoundaryIndex (normals (nonordinaryPoints P)) f) :
    i ∈ PolarRedChordExtraction.redEndpoints hred hspan f ↔
      ∃ a ∈ ordinaryPoints P,
        RestrictedRealizable (normals (nonordinaryPoints P))
            (normalVec a) f.1 ∧
          Incident (boundaryOrientedVertex hspan f i).1.1 a := by
  constructor
  · intro hi
    obtain ⟨p, hp, hip⟩ :=
      (PolarRedChordExtraction.mem_redEndpoints_iff hred hspan f i).1 hi
    obtain ⟨a, rfl⟩ :=
      (PolarRedChordExtraction.mem_redChords_iff hred hspan f p).1 hp
    have hspec := PolarRedChordExtraction.chordPair_spec hred hspan f a
    have himem : i ∈ PolarRedChordExtraction.endpointIndices hspan f a.1 := by
      rw [hspec.2]
      simpa using hip
    refine ⟨a.1.1, a.1.2, a.2, ?_⟩
    have hinc := (Finset.mem_filter.mp himem).2
    exact hinc
  · rintro ⟨a, ha, hrest, hinc⟩
    let aa : PolarRedChordExtraction.ChordLine (P := P) f :=
      ⟨⟨a, ha⟩, hrest⟩
    have himem : i ∈ PolarRedChordExtraction.endpointIndices hspan f aa.1 := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hinc⟩
    have hspec := PolarRedChordExtraction.chordPair_spec hred hspan f aa
    rw [hspec.2] at himem
    apply (PolarRedChordExtraction.mem_redEndpoints_iff hred hspan f i).2
    refine ⟨PolarRedChordExtraction.chordPair hred hspan f aa, ?_, ?_⟩
    · apply (PolarRedChordExtraction.mem_redChords_iff hred hspan f _).2
      exact ⟨aa, rfl⟩
    · simpa using himem

@[simp] theorem mem_polarStage1Corners
    [Nonempty (ProjectiveBoundaryExtraction.Line (nonordinaryPoints P))]
    {w : Point → ℝ} {c : ℝ} (hred : IsReducedMagic P w c)
    (hspan : Submodule.span ℝ
      (Set.range (normals (nonordinaryPoints P))) = ⊤)
    (f : StrictFace (normals (nonordinaryPoints P)))
    (i : BoundaryIndex (normals (nonordinaryPoints P)) f) :
    i ∈ polarStage1Corners hred hspan f ↔
      lineMultiplicity (OnLine (nonordinaryPoints P))
          (boundaryOrientedVertex hspan f i).1 = 2 ∧
        ∃ a ∈ ordinaryPoints P,
          RestrictedRealizable (normals (nonordinaryPoints P))
              (normalVec a) f.1 ∧
            Incident (boundaryOrientedVertex hspan f i).1.1 a := by
  rw [polarStage1Corners, Finset.mem_filter,
    mem_polarRedEndpoints_iff_exists_feasible_incident hred hspan f i]
  tauto

/-- Direct adapter to the shape of `ABKPR.Data.badVertex_receiverCount`.
The hypothesis is the geometry-expanded form of `stage1Corner_iff`: a
selected corner is multiplicity two and lies on a feasible ordinary red
line.  Reduced magic makes that red line unique at the fixed bad vertex. -/
theorem badVertex_receiverCount_of_stage1Corner_iff
    [Nonempty (ProjectiveBoundaryExtraction.Line (nonordinaryPoints P))]
    {w : Point → ℝ} {c : ℝ} (hred : IsReducedMagic P w c)
    (hspan : Submodule.span ℝ
      (Set.range (normals (nonordinaryPoints P))) = ⊤)
    (stage1Corners : ∀ f : StrictFace (normals (nonordinaryPoints P)),
      Finset (BoundaryIndex (normals (nonordinaryPoints P)) f))
    (hstage : ∀ f i, i ∈ stage1Corners f ↔
      lineMultiplicity (OnLine (nonordinaryPoints P))
          (boundaryOrientedVertex hspan f i).1 = 2 ∧
        ∃ a ∈ ordinaryPoints P,
          RestrictedRealizable (normals (nonordinaryPoints P))
              (normalVec a) f.1 ∧
            Incident (boundaryOrientedVertex hspan f i).1.1 a)
    (v : OrientedVertex (nonordinaryPoints P))
    (hmult : lineMultiplicity (OnLine (nonordinaryPoints P)) v.1 = 2) :
    (Finset.univ.filter fun f : StrictFace (normals (nonordinaryPoints P)) ↦
      ∃ i ∈ stage1Corners f,
        boundaryOrientedVertex hspan f i = v).card = 2 := by
  obtain ⟨a, ha, haincHom⟩ :=
    RedBlueDualIncidence.exists_ordinary_incident_of_lineMultiplicity_eq_two
      hred v.1 hmult
  have incidence_iff (p : Point) : Incident v.1.1 p ↔
      RedBlueDualIncidence.vertexHomogeneous v.1 ∈
        ProjectiveDuality.dualLine p := by
    change dotProduct (normalVec p) v.1.1.rep = 0 ↔ _
    simpa [RedBlueDualIncidence.vertexHomogeneous] using
      (dotProduct_normalVec_toCoordinates_iff p
        (RedBlueDualIncidence.vertexHomogeneous v.1))
  have hainc : Incident v.1.1 a := (incidence_iff a).2 haincHom
  have hredcard :=
    RedBlueDualIncidence.redIncidentPoints_card_eq_one_of_lineMultiplicity_eq_two
      hred v.1 hmult
  obtain ⟨a₀, hredset⟩ := Finset.card_eq_one.mp hredcard
  have haMem : a ∈ RedBlueDualIncidence.redIncidentPoints P
      (RedBlueDualIncidence.vertexHomogeneous v.1) :=
    Finset.mem_filter.mpr ⟨ha, haincHom⟩
  have haeq : a = a₀ := by
    rw [hredset] at haMem
    simpa using haMem
  have hset :
      (Finset.univ.filter fun f : StrictFace (normals (nonordinaryPoints P)) ↦
        ∃ i ∈ stage1Corners f,
          boundaryOrientedVertex hspan f i = v) =
      (Finset.univ.filter fun f : StrictFace (normals (nonordinaryPoints P)) ↦
        ∃ i : BoundaryIndex (normals (nonordinaryPoints P)) f,
          boundaryOrientedVertex hspan f i = v ∧
            RestrictedRealizable (normals (nonordinaryPoints P))
              (normalVec a) f.1) := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, histage, hiv⟩
      obtain ⟨-, a', ha', ha'rest, ha'inc⟩ := (hstage f i).1 histage
      have ha'incv : Incident v.1.1 a' := by
        rw [← hiv]
        exact ha'inc
      have ha'Hom : RedBlueDualIncidence.vertexHomogeneous v.1 ∈
          ProjectiveDuality.dualLine a' := (incidence_iff a').1 ha'incv
      have ha'Mem : a' ∈ RedBlueDualIncidence.redIncidentPoints P
          (RedBlueDualIncidence.vertexHomogeneous v.1) :=
        Finset.mem_filter.mpr ⟨ha', ha'Hom⟩
      have ha'eq : a' = a₀ := by
        rw [hredset] at ha'Mem
        simpa using ha'Mem
      have haa' : a' = a := ha'eq.trans haeq.symm
      exact ⟨i, hiv, haa' ▸ ha'rest⟩
    · rintro ⟨i, hiv, hirest⟩
      refine ⟨i, (hstage f i).2 ⟨?_, a, ha, hirest, ?_⟩, hiv⟩
      · rw [hiv]
        exact hmult
      · rw [hiv]
        exact hainc
  rw [hset]
  exact boundaryReceiverFaces_card_eq_two_at_badVertex hspan v hmult ha hainc

/-- Fully concrete literal-polar form of the ABKPR bad-vertex receiver
count.  No residual local-sector hypothesis remains. -/
theorem polarStage1Corners_receiverCount
    [Nonempty (ProjectiveBoundaryExtraction.Line (nonordinaryPoints P))]
    {w : Point → ℝ} {c : ℝ} (hred : IsReducedMagic P w c)
    (hspan : Submodule.span ℝ
      (Set.range (normals (nonordinaryPoints P))) = ⊤)
    (v : OrientedVertex (nonordinaryPoints P))
    (hmult : lineMultiplicity (OnLine (nonordinaryPoints P)) v.1 = 2) :
    (Finset.univ.filter fun f : StrictFace (normals (nonordinaryPoints P)) ↦
      ∃ i ∈ polarStage1Corners hred hspan f,
        boundaryOrientedVertex hspan f i = v).card = 2 := by
  apply badVertex_receiverCount_of_stage1Corner_iff hred hspan
    (polarStage1Corners hred hspan)
  · intro f i
    exact mem_polarStage1Corners hred hspan f i
  · exact hmult

end Erdos735.ConcreteBadReceiver
