/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos847.Pictures
import ErdosProblems.Erdos847.Encoding
import ErdosProblems.Erdos847.FiniteArch

/-!
# Extracting a finite integer block from a final RRS picture

This file contains the last, elementary step of the finite RRS construction.
A finite picture which is Ramsey for `r` colours and which projects to a base
three-graph having the natural `1/3` fractional property gives a finite set of
natural numbers with the two properties needed by the separated-block
assembly.
-/

namespace Erdos847PictureOutput

open Function Set
open Erdos847Pictures Erdos847Encoding Erdos847FiniteArch

set_option autoImplicit false

noncomputable def EncodedBlock {V P : Type*} [DecidableEq V]
    (G : ThreeGraph V) {m : ℕ} [Fintype P] [DecidableEq P]
    (picture : Picture G P (Fin m)) : Finset ℕ :=
  Finset.univ.image fun p => encode m (picture.embed p)

/-- Reindex an arbitrary finite coordinate type by its canonical finite
ordinal.  This is only a change of names; all picture structure is preserved. -/
noncomputable def reindexFin {V P C : Type*} [DecidableEq V] [Fintype C]
    {G : ThreeGraph V} (picture : Picture G P C) :
    Picture G P (Fin (Fintype.card C)) where
  embed p i := picture.embed p ((Fintype.equivFin C).symm i)
  embed_injective := by
    intro p q hpq
    apply picture.embed_injective
    funext c
    have hi := congrFun hpq (Fintype.equivFin C c)
    simpa using hi
  proj := picture.proj
  quasiline_is_line := by
    intro l hl
    have hold : IsQuasiline picture.embed l := by
      refine ⟨hl.1, ?_⟩
      intro c
      simpa using hl.2 (Fintype.equivFin C c)
    rcases picture.quasiline_is_line l hold with ⟨hinj, σ, hσ⟩
    refine ⟨hinj, σ, ?_⟩
    intro i
    simpa using hσ ((Fintype.equivFin C).symm i)
  quasiline_maps_edge := by
    intro l hl
    apply picture.quasiline_maps_edge l
    refine ⟨hl.1, ?_⟩
    intro c
    simpa using hl.2 (Fintype.equivFin C c)

/-- A selected combinatorial line stays selected after finite-coordinate
reindexing. -/
theorem isCombinatorialLine_reindexFin {V P C : Type*} [DecidableEq V]
    [Fintype C] {G : ThreeGraph V} (picture : Picture G P C)
    {l : Alphabet → P} (hl : IsCombinatorialLine picture.embed l) :
    IsCombinatorialLine (reindexFin picture).embed l := by
  rcases hl with ⟨hinj, σ, hσ⟩
  refine ⟨hinj, σ, ?_⟩
  intro i
  simpa [reindexFin] using hσ ((Fintype.equivFin C).symm i)

/-- Coordinatewise midpoints are preserved by the base-six encoding. -/
theorem encode_preserves_midpoint {m : ℕ} (u v w : Word m)
    (h : IsWeakQuasiLine u v w) :
    encode m u + encode m w = 2 * encode m v := by
  unfold encode
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  calc
    (u i).val * 6 ^ (i : ℕ) + (w i).val * 6 ^ (i : ℕ) =
        ((u i).val + (w i).val) * 6 ^ (i : ℕ) := (Nat.add_mul ..).symm
    _ = (2 * (v i).val) * 6 ^ (i : ℕ) := by rw [h i]
    _ = 2 * ((v i).val * 6 ^ (i : ℕ)) := by simp [Nat.mul_assoc]

/-- Reindexing a custom combinatorial line by its global alphabet permutation
puts its three encoded points in arithmetic-progression order. -/
theorem custom_line_encodes_AP {V P : Type*} [DecidableEq V]
    {G : ThreeGraph V} {m : ℕ} (picture : Picture G P (Fin m))
    (l : Alphabet → P) (hl : IsCombinatorialLine picture.embed l) :
    ∃ q : Alphabet → P,
      (∀ a, q a ∈ Set.range l) ∧
      encode m (picture.embed (q 0)) + encode m (picture.embed (q 2)) =
        2 * encode m (picture.embed (q 1)) ∧
      encode m (picture.embed (q 0)) ≠ encode m (picture.embed (q 2)) := by
  rcases hl with ⟨hlinj, σ, hσ⟩
  let q : Alphabet → P := fun a => l (σ.symm a)
  refine ⟨q, ?_, ?_, ?_⟩
  · intro a
    exact ⟨σ.symm a, rfl⟩
  · apply encode_preserves_midpoint
    intro c
    rcases hσ c with ⟨x, hx⟩ | hmove
    · simp only [q, hx]
      simp [two_mul]
    · simp only [q, hmove, Equiv.apply_symm_apply]
      decide
  · apply (encode_injective m).ne
    apply picture.embed_injective.ne
    apply hlinj.ne
    intro h
    have := congrArg σ h
    simp at this

/-- A word midpoint with distinct endpoints gives an injective custom
quasiline enumeration. -/
theorem isQuasiline_of_weak_of_ne {m : ℕ} (u v w : Word m)
    (hmid : IsWeakQuasiLine u v w) (huw : u ≠ w) :
    IsQuasiline id ![u, v, w] := by
  have huv : u ≠ v := by
    intro huv
    apply huw
    funext i
    have hi := hmid i
    have huvi := congrFun huv i
    apply Fin.ext
    rw [huvi] at hi
    omega
  have hvw : v ≠ w := by
    intro hvw
    apply huw
    funext i
    have hi := hmid i
    have hvwi := congrFun hvw i
    apply Fin.ext
    rw [hvwi] at hi
    omega
  constructor
  · intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  · intro i
    rw [isWeakQuasiLine_iff] at hmid
    rcases hmid i with hconst | hforward | hreverse
    · left
      exact ⟨u i, by intro a; fin_cases a <;> simp_all⟩
    · right
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all
    · right
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all

/-- If all points of a picture project into an independent set of the base
three-graph, their words contain no nonconstant quasiline. -/
theorem quasiLineFree_image_of_independent
    {V P : Type*} [Fintype V] [DecidableEq V] [Fintype P] [DecidableEq P]
    {G : ThreeGraph V} {m : ℕ} (picture : Picture G P (Fin m))
    {I : Finset V} (hI : Erdos847FiniteArch.Independent G.edges I)
    {D : Finset P} (hproj : ∀ p ∈ D, picture.proj p ∈ I) :
    QuasiLineFree ((D.image picture.embed : Finset (Word m)) : Set (Word m)) := by
  intro u hu v hv w hw hmid
  obtain ⟨pu, hpuD, hpu⟩ := Finset.mem_image.mp hu
  obtain ⟨pv, hpvD, hpv⟩ := Finset.mem_image.mp hv
  obtain ⟨pw, hpwD, hpw⟩ := Finset.mem_image.mp hw
  subst u
  subst v
  subst w
  by_contra huw
  let l : Alphabet → P := ![pu, pv, pw]
  have hwords : IsQuasiline id ![picture.embed pu, picture.embed pv, picture.embed pw] :=
    isQuasiline_of_weak_of_ne _ _ _ hmid huw
  have hl : IsQuasiline picture.embed l := by
    constructor
    · intro a b hab
      apply hwords.1
      fin_cases a <;> fin_cases b <;> simp_all [l]
    · intro c
      rcases hwords.2 c with ⟨d, hd⟩ | hinj
      · left
        refine ⟨d, ?_⟩
        intro a
        fin_cases a
        · simpa [l] using hd 0
        · simpa [l] using hd 1
        · simpa [l] using hd 2
      · right
        intro a b hab
        apply hinj
        fin_cases a <;> fin_cases b <;> simp_all [l]
  obtain ⟨e, he⟩ := picture.quasiline_maps_edge l hl
  apply hI e.1 e.2
  intro x hx
  have hxrange : x ∈ Set.range (fun a => picture.proj (l a)) := by
    rw [he]
    exact hx
  obtain ⟨a, rfl⟩ := hxrange
  fin_cases a
  · exact hproj pu hpuD
  · exact hproj pv hpvD
  · exact hproj pw hpwD

/-- The finite output theorem.  Its assumptions are precisely the two facts
provided by the final stage of the picture construction: Ramsey focusing and
the natural fractional-third property of the base graph. -/
theorem exists_encoded_block
    {V P : Type*} [Fintype V] [DecidableEq V] [Fintype P] [DecidableEq P]
    {G : ThreeGraph V} {m r : ℕ} (picture : Picture G P (Fin m))
    (hr : 0 < r)
    (hRamsey : ∀ color : P → Fin r,
      ∃ l : Alphabet → P, IsCombinatorialLine picture.embed l ∧
        ∃ k : Fin r, ∀ a, color (l a) = k)
    (hFractional : NatFractionalThird G.edges) :
    ∃ X : Finset ℕ,
      X.Nonempty ∧
      (∀ color : ℕ → Fin r,
        ∃ a ∈ X, ∃ b ∈ X, ∃ c ∈ X,
          a + c = b + b ∧ a ≠ c ∧
          color a = color b ∧ color b = color c) ∧
      (∀ Y : Finset ℕ, Y ⊆ X →
        ∃ Z : Finset ℕ, Z ⊆ Y ∧ Y.card ≤ 3 * Z.card ∧
          ThreeAPFree (Z : Set ℕ)) := by
  let f : P → ℕ := fun p => encode m (picture.embed p)
  let X : Finset ℕ := Finset.univ.image f
  have hf : Function.Injective f :=
    (encode_injective m).comp picture.embed_injective
  have hXne : X.Nonempty := by
    let color : P → Fin r := fun _ => ⟨0, hr⟩
    obtain ⟨l, hl, k, hk⟩ := hRamsey color
    exact ⟨f (l 0), Finset.mem_image.mpr ⟨l 0, Finset.mem_univ _, rfl⟩⟩
  refine ⟨X, hXne, ?_, ?_⟩
  · intro color
    obtain ⟨l, hl, k, hk⟩ := hRamsey (fun p => color (f p))
    obtain ⟨q, hqrange, hAP, hne⟩ := custom_line_encodes_AP picture l hl
    refine ⟨f (q 0), ?_, f (q 1), ?_, f (q 2), ?_, ?_, hne, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨q 0, Finset.mem_univ _, rfl⟩
    · exact Finset.mem_image.mpr ⟨q 1, Finset.mem_univ _, rfl⟩
    · exact Finset.mem_image.mpr ⟨q 2, Finset.mem_univ _, rfl⟩
    · simpa [two_mul] using hAP
    · obtain ⟨a, ha⟩ := hqrange 0
      obtain ⟨b, hb⟩ := hqrange 1
      calc
        color (f (q 0)) = color (f (l a)) := congrArg (fun p => color (f p)) ha.symm
        _ = k := hk a
        _ = color (f (l b)) := (hk b).symm
        _ = color (f (q 1)) := congrArg (fun p => color (f p)) hb
    · obtain ⟨a, ha⟩ := hqrange 1
      obtain ⟨b, hb⟩ := hqrange 2
      calc
        color (f (q 1)) = color (f (l a)) := congrArg (fun p => color (f p)) ha.symm
        _ = k := hk a
        _ = color (f (l b)) := (hk b).symm
        _ = color (f (q 2)) := congrArg (fun p => color (f p)) hb
  · intro Y hYX
    let D : Finset P := Finset.univ.filter fun p => f p ∈ Y
    let pointWeight : P → ℕ := fun p => if p ∈ D then 1 else 0
    let W : V → ℕ := fun y => ∑ p with picture.proj p = y, pointWeight p
    obtain ⟨I, hI, hweight⟩ := hFractional W
    let E : Finset P := D.filter fun p => picture.proj p ∈ I
    let Z : Finset ℕ := E.image f
    have hDimage : D.image f = Y := by
      ext y
      constructor
      · intro hy
        obtain ⟨p, hpD, rfl⟩ := Finset.mem_image.mp hy
        exact (Finset.mem_filter.mp hpD).2
      · intro hy
        have hyX := hYX hy
        obtain ⟨p, hp, hpy⟩ := Finset.mem_image.mp hyX
        refine Finset.mem_image.mpr ⟨p, ?_, hpy⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpy ▸ hy⟩
    have hZsubset : Z ⊆ Y := by
      intro y hy
      obtain ⟨p, hpE, rfl⟩ := Finset.mem_image.mp hy
      have hpD := (Finset.mem_filter.mp hpE).1
      rw [← hDimage]
      exact Finset.mem_image.mpr ⟨p, hpD, rfl⟩
    have htotal : (∑ y, W y) = D.card := by
      have hfiber : (∑ y, W y) = ∑ p, pointWeight p := by
        simp only [W]
        simpa using Finset.sum_fiberwise (Finset.univ : Finset P)
          picture.proj pointWeight
      rw [hfiber]
      simp [pointWeight]
    have hselected : (∑ y ∈ I, W y) = E.card := by
      have hfiber : (∑ y ∈ I, W y) =
          ∑ p ∈ Finset.univ.filter (fun p => picture.proj p ∈ I), pointWeight p := by
        simp only [W]
        simpa using Finset.sum_fiberwise_eq_sum_filter
          (Finset.univ : Finset P) I picture.proj pointWeight
      rw [hfiber]
      simp [pointWeight, E, D, Finset.filter_filter, and_comm]
    have hcard : Y.card ≤ 3 * Z.card := by
      rw [← hDimage, Finset.card_image_of_injective _ hf]
      rw [show Z.card = E.card by simp [Z, Finset.card_image_of_injective _ hf]]
      rw [← htotal, ← hselected]
      exact hweight
    have hfreeWords :
        QuasiLineFree ((E.image picture.embed : Finset (Word m)) : Set (Word m)) := by
      apply quasiLineFree_image_of_independent picture hI
      intro p hpE
      exact (Finset.mem_filter.mp hpE).2
    have hfree : ThreeAPFree (Z : Set ℕ) := by
      have := threeAPFree_finset_image_encode hfreeWords
      simpa [Z, f, Finset.image_image] using this
    exact ⟨Z, hZsubset, hcard, hfree⟩

/-- Real-valued form of `exists_encoded_block`, ready to instantiate the
`mu = 1/3` density field in the separated-block assembly. -/
theorem exists_encoded_block_one_third
    {V P : Type*} [Fintype V] [DecidableEq V] [Fintype P] [DecidableEq P]
    {G : ThreeGraph V} {m r : ℕ} (picture : Picture G P (Fin m))
    (hr : 0 < r)
    (hRamsey : ∀ color : P → Fin r,
      ∃ l : Alphabet → P, IsCombinatorialLine picture.embed l ∧
        ∃ k : Fin r, ∀ a, color (l a) = k)
    (hFractional : NatFractionalThird G.edges) :
    ∃ X : Finset ℕ,
      X.Nonempty ∧
      (∀ color : ℕ → Fin r,
        ∃ a ∈ X, ∃ b ∈ X, ∃ c ∈ X,
          a + c = b + b ∧ a ≠ c ∧
          color a = color b ∧ color b = color c) ∧
      (∀ Y : Finset ℕ, Y ⊆ X →
        ∃ Z : Finset ℕ, Z ⊆ Y ∧
          (Z.card : ℝ) ≥ (1 / 3 : ℝ) * Y.card ∧
          ThreeAPFree (Z : Set ℕ)) := by
  obtain ⟨X, hXne, hXRamsey, hXdense⟩ :=
    exists_encoded_block picture hr hRamsey hFractional
  refine ⟨X, hXne, hXRamsey, ?_⟩
  intro Y hYX
  obtain ⟨Z, hZY, hcard, hfree⟩ := hXdense Y hYX
  refine ⟨Z, hZY, ?_, hfree⟩
  have hcast : (Y.card : ℝ) ≤ 3 * (Z.card : ℝ) := by
    exact_mod_cast hcard
  norm_num at ⊢ hcast
  linarith

/-- Coordinate-type-independent output theorem.  In particular, it consumes
the `Coord` type produced existentially by the finite picture iteration
without asking that construction to choose a literal `Fin m`. -/
theorem exists_encoded_block_one_third_of_finite_coords
    {V P C : Type*} [Fintype V] [DecidableEq V]
    [Fintype P] [DecidableEq P] [Fintype C]
    {G : ThreeGraph V} {r : ℕ} (picture : Picture G P C)
    (hr : 0 < r)
    (hRamsey : ∀ color : P → Fin r,
      ∃ l : Alphabet → P, IsCombinatorialLine picture.embed l ∧
        ∃ k : Fin r, ∀ a, color (l a) = k)
    (hFractional : NatFractionalThird G.edges) :
    ∃ X : Finset ℕ,
      X.Nonempty ∧
      (∀ color : ℕ → Fin r,
        ∃ a ∈ X, ∃ b ∈ X, ∃ c ∈ X,
          a + c = b + b ∧ a ≠ c ∧
          color a = color b ∧ color b = color c) ∧
      (∀ Y : Finset ℕ, Y ⊆ X →
        ∃ Z : Finset ℕ, Z ⊆ Y ∧
          (Z.card : ℝ) ≥ (1 / 3 : ℝ) * Y.card ∧
          ThreeAPFree (Z : Set ℕ)) := by
  apply exists_encoded_block_one_third (reindexFin picture) hr
  · intro color
    obtain ⟨l, hl, k, hk⟩ := hRamsey color
    exact ⟨l, isCombinatorialLine_reindexFin picture hl, k, hk⟩
  · exact hFractional

end Erdos847PictureOutput
