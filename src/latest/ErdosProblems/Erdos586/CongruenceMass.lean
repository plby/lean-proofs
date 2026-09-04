/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos586.FiniteProbability

/-!
# Congruence classes in a fixed finite cyclic group

This file contains the finite cyclic-group bookkeeping used in the moment
part of the distortion sieve for Erdős Problem 586.  A congruence class
modulo `m ∣ Q` is represented as a fibre of the canonical map
`ZMod Q → ZMod m`.  This representation makes changes of modulus and the
counting of fibres independent of integer representatives.
-/

open scoped BigOperators

namespace Erdos586

noncomputable section

/-- The congruence class `b (mod m)` inside the fixed cyclic group `ZMod Q`.
The proof `hm` records that reduction modulo `m` is well-defined. -/
def congruenceClass (Q m : ℕ) (hm : m ∣ Q) (b : ℤ) : Set (ZMod Q) :=
  {x | ZMod.castHom hm (ZMod m) x = (b : ZMod m)}

@[simp]
lemma mem_congruenceClass {Q m : ℕ} (hm : m ∣ Q) (b : ℤ) (x : ZMod Q) :
    x ∈ congruenceClass Q m hm b ↔
      ZMod.castHom hm (ZMod m) x = (b : ZMod m) :=
  Iff.rfl

lemma intCast_mem_congruenceClass {Q m : ℕ} (hm : m ∣ Q) (a b : ℤ) :
    (a : ZMod Q) ∈ congruenceClass Q m hm b ↔ a ≡ b [ZMOD m] := by
  rw [mem_congruenceClass, ZMod.castHom_apply, ZMod.cast_intCast hm]
  exact ZMod.intCast_eq_intCast_iff a b m

lemma congruenceClass_nonempty {Q m : ℕ} (hm : m ∣ Q) (b : ℤ) :
    (congruenceClass Q m hm b).Nonempty := by
  obtain ⟨x, hx⟩ := ZMod.castHom_surjective hm (b : ZMod m)
  exact ⟨x, hx⟩

/-- Translation identifies any two fibres of a surjective additive
homomorphism. -/
def castFiberEquiv {Q m : ℕ} (hm : m ∣ Q) (a b : ZMod m) :
    {x : ZMod Q // ZMod.castHom hm (ZMod m) x = a} ≃
      {x : ZMod Q // ZMod.castHom hm (ZMod m) x = b} := by
  let f := ZMod.castHom hm (ZMod m)
  let z := Classical.choose (ZMod.castHom_surjective hm (b - a))
  have hz : ZMod.castHom hm (ZMod m) z = b - a :=
    Classical.choose_spec (ZMod.castHom_surjective hm (b - a))
  exact
    { toFun := fun x => ⟨x.1 + z, by
          change f (x.1 + z) = b
          rw [map_add, x.2, hz]
          abel⟩
      invFun := fun x => ⟨x.1 - z, by
          change f (x.1 - z) = a
          rw [map_sub, x.2, hz]
          abel⟩
      left_inv := by
        intro x
        apply Subtype.ext
        simp
      right_inv := by
        intro x
        apply Subtype.ext
        simp }

lemma card_castFiber_eq {Q m : ℕ} [NeZero Q] (hm : m ∣ Q) (a b : ZMod m) :
    Fintype.card {x : ZMod Q // ZMod.castHom hm (ZMod m) x = a} =
      Fintype.card {x : ZMod Q // ZMod.castHom hm (ZMod m) x = b} :=
  Fintype.card_congr (castFiberEquiv hm a b)

/-- Every residue class modulo `m` has exactly `Q / m` representatives
modulo `Q`. -/
theorem card_congruenceClass {Q m : ℕ} [NeZero Q] (hm : m ∣ Q)
    (hm0 : 0 < m) (b : ℤ) :
    (congruenceClass Q m hm b).ncard = Q / m := by
  let : NeZero m := ⟨hm0.ne'⟩
  let f : ZMod Q → ZMod m := ZMod.castHom hm (ZMod m)
  let c := Fintype.card {x : ZMod Q // f x = (b : ZMod m)}
  have htotal :
      (∑ y : ZMod m, Fintype.card {x : ZMod Q // f x = y}) = Q := by
    calc
      (∑ y : ZMod m, Fintype.card {x : ZMod Q // f x = y}) =
          Fintype.card ((y : ZMod m) × {x : ZMod Q // f x = y}) := by
            rw [Fintype.card_sigma]
      _ = Fintype.card (ZMod Q) := Fintype.card_congr (Equiv.sigmaFiberEquiv f)
      _ = Q := ZMod.card Q
  have heach (y : ZMod m) :
      Fintype.card {x : ZMod Q // f x = y} = c := by
    exact Fintype.card_congr (castFiberEquiv hm y (b : ZMod m))
  have hmul : m * c = Q := by
    simpa [heach, ZMod.card, c, nsmul_eq_mul] using htotal
  have hc : c = Q / m := by
    exact Nat.eq_div_of_mul_eq_left hm0.ne' (by simpa [Nat.mul_comm] using hmul)
  change Nat.card {x : ZMod Q //
    ZMod.castHom hm (ZMod m) x = (b : ZMod m)} = Q / m
  rw [Nat.card_eq_fintype_card]
  simpa [congruenceClass, f, c] using hc

/-- In a nonzero ambient cyclic group, membership in the cast-hom fibre is
the usual congruence of the canonical integer representative. -/
lemma mem_congruenceClass_iff_modEq_val {Q m : ℕ} [NeZero Q]
    (hm : m ∣ Q) (b : ℤ) (x : ZMod Q) :
    x ∈ congruenceClass Q m hm b ↔ (x.val : ℤ) ≡ b [ZMOD m] := by
  rw [mem_congruenceClass]
  have hcast : ZMod.castHom hm (ZMod m) x = (x.val : ZMod m) := by
    rw [← ZMod.natCast_zmod_val x]
    simp
  rw [hcast]
  simpa using ZMod.intCast_eq_intCast_iff (x.val : ℤ) b m

/-- Two compatible congruence classes intersect in exactly one congruence
class modulo the least common multiple.  The representative `x₀` packages
the compatibility hypothesis and avoids making an arbitrary CRT choice. -/
theorem congruenceClass_inter_eq_lcm_of_mem {Q m n : ℕ} [NeZero Q]
    (hm : m ∣ Q) (hn : n ∣ Q) (b c : ℤ) (x₀ : ZMod Q)
    (hx₀ : x₀ ∈ congruenceClass Q m hm b ∩ congruenceClass Q n hn c) :
    congruenceClass Q m hm b ∩ congruenceClass Q n hn c =
      congruenceClass Q (Nat.lcm m n) (Nat.lcm_dvd hm hn) x₀.val := by
  ext x
  rw [Set.mem_inter_iff]
  rw [mem_congruenceClass_iff_modEq_val,
    mem_congruenceClass_iff_modEq_val,
    mem_congruenceClass_iff_modEq_val]
  have hx₀m : (x₀.val : ℤ) ≡ b [ZMOD m] :=
    (mem_congruenceClass_iff_modEq_val hm b x₀).mp hx₀.1
  have hx₀n : (x₀.val : ℤ) ≡ c [ZMOD n] :=
    (mem_congruenceClass_iff_modEq_val hn c x₀).mp hx₀.2
  constructor
  · rintro ⟨hxm, hxn⟩
    exact Int.modEq_and_modEq_iff_modEq_lcm.mp
      ⟨hxm.trans hx₀m.symm, hxn.trans hx₀n.symm⟩
  · intro hxl
    have hpair :
        (x.val : ℤ) ≡ (x₀.val : ℤ) [ZMOD m] ∧
          (x.val : ℤ) ≡ (x₀.val : ℤ) [ZMOD n] := by
      have hmL : (m : ℤ) ∣ (Nat.lcm m n : ℕ) := by
        exact_mod_cast Nat.dvd_lcm_left m n
      have hnL : (n : ℤ) ∣ (Nat.lcm m n : ℕ) := by
        exact_mod_cast Nat.dvd_lcm_right m n
      exact ⟨hxl.of_dvd hmL, hxl.of_dvd hnL⟩
    exact ⟨hpair.1.trans hx₀m, hpair.2.trans hx₀n⟩

/-- The intersection of two congruence classes is either empty or a single
class modulo their least common multiple. -/
theorem congruenceClass_inter_eq_empty_or_lcm {Q m n : ℕ} [NeZero Q]
    (hm : m ∣ Q) (hn : n ∣ Q) (b c : ℤ) :
    congruenceClass Q m hm b ∩ congruenceClass Q n hn c = ∅ ∨
      ∃ a : ℤ,
        congruenceClass Q m hm b ∩ congruenceClass Q n hn c =
          congruenceClass Q (Nat.lcm m n) (Nat.lcm_dvd hm hn) a := by
  classical
  by_cases h : (congruenceClass Q m hm b ∩ congruenceClass Q n hn c).Nonempty
  · rcases h with ⟨x₀, hx₀⟩
    exact Or.inr ⟨x₀.val, congruenceClass_inter_eq_lcm_of_mem hm hn b c x₀ hx₀⟩
  · left
    exact Set.not_nonempty_iff_eq_empty.mp h

/-! ## Finite weights and periodic lifting -/

/-- The total weight of a decidable event in a finite type.  No normalization
or nonnegativity is needed for the algebraic fibre identities below. -/
def finiteWeightMass {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (S : Set Ω) : ℝ := by
  classical
  exact ∑ x, if x ∈ S then w x else 0

/-- The sum of a weight over one fibre of a map of finite types. -/
def finiteFiberWeight {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq Y] (f : X → Y) (w : X → ℝ) (y : Y) : ℝ :=
  ∑ x ∈ (Finset.univ : Finset X) with f x = y, w x

/-- Grouping a finite sum by fibres: if the sum on every fibre of `f` is
`v y`, then the weight of a pullback event is its `v`-weight downstairs. -/
theorem finiteWeightMass_preimage_eq_of_fiberWeight_eq
    {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    (f : X → Y) (u : X → ℝ) (v : Y → ℝ)
    (hfiber : ∀ y, finiteFiberWeight f u y = v y) (S : Set Y) :
    finiteWeightMass u (f ⁻¹' S) = finiteWeightMass v S := by
  classical
  unfold finiteWeightMass
  rw [← Finset.sum_fiberwise (Finset.univ : Finset X) f
    (fun x => if x ∈ f ⁻¹' S then u x else 0)]
  apply Finset.sum_congr rfl
  intro y hy
  by_cases hS : y ∈ S
  · rw [if_pos hS, ← hfiber]
    unfold finiteFiberWeight
    apply Finset.sum_congr rfl
    intro x hx
    have hxy : f x = y := (Finset.mem_filter.mp hx).2
    simp [hxy, hS]
  · rw [if_neg hS]
    apply Finset.sum_eq_zero
    intro x hx
    have hxy : f x = y := (Finset.mem_filter.mp hx).2
    simp [hxy, hS]

/-- Fibre sums determine the mass of every event pulled back from the base. -/
theorem finiteWeightMass_preimage_eq_of_fiberWeight_eq'
    {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    (f : X → Y) (u₁ u₂ : X → ℝ)
    (hfiber : ∀ y, finiteFiberWeight f u₁ y = finiteFiberWeight f u₂ y)
    (S : Set Y) :
    finiteWeightMass u₁ (f ⁻¹' S) = finiteWeightMass u₂ (f ⁻¹' S) := by
  calc
    finiteWeightMass u₁ (f ⁻¹' S) =
        finiteWeightMass (finiteFiberWeight f u₁) S :=
      finiteWeightMass_preimage_eq_of_fiberWeight_eq f u₁ _ (fun _ => rfl) S
    _ = finiteWeightMass (finiteFiberWeight f u₂) S := by
      apply congrArg (fun w => finiteWeightMass w S)
      funext y
      exact hfiber y
    _ = finiteWeightMass u₂ (f ⁻¹' S) :=
      (finiteWeightMass_preimage_eq_of_fiberWeight_eq f u₂ _ (fun _ => rfl) S).symm

/-- Congruence classes whose modulus divides `q` are pullbacks along the
canonical reduction `ZMod Q → ZMod q`. -/
theorem congruenceClass_eq_preimage {Q q m : ℕ} (hqQ : q ∣ Q) (hmq : m ∣ q)
    (b : ℤ) :
    congruenceClass Q m (dvd_trans hmq hqQ) b =
      (ZMod.castHom hqQ (ZMod q)) ⁻¹' congruenceClass q m hmq b := by
  ext x
  change ZMod.castHom (dvd_trans hmq hqQ) (ZMod m) x = (b : ZMod m) ↔
    ZMod.castHom hmq (ZMod m) (ZMod.castHom hqQ (ZMod q) x) = (b : ZMod m)
  have hcomp := congrArg (fun f : ZMod Q →+* ZMod m => f x)
    (ZMod.castHom_comp hmq hqQ)
  rw [← hcomp]
  rfl

/-- Extend a finite weight on `ZMod q` periodically and uniformly to
`ZMod Q`.  Each of the `Q / q` representatives of a residue downstairs gets
the same share of its weight. -/
def periodicLiftWeight {Q q : ℕ} (hqQ : q ∣ Q) (w : ZMod q → ℝ)
    (x : ZMod Q) : ℝ :=
  w (ZMod.castHom hqQ (ZMod q) x) / (Q / q : ℕ)

/-- The periodic lift has exactly the prescribed sum on every reduction
fibre. -/
theorem finiteFiberWeight_periodicLift {Q q : ℕ} [NeZero Q] [NeZero q]
    (hqQ : q ∣ Q) (hq0 : 0 < q) (w : ZMod q → ℝ) (y : ZMod q) :
    finiteFiberWeight (ZMod.castHom hqQ (ZMod q))
      (periodicLiftWeight hqQ w) y = w y := by
  have hqQpos : q ≤ Q := Nat.le_of_dvd (NeZero.pos Q) hqQ
  have hkpos : 0 < Q / q := Nat.div_pos hqQpos hq0
  have hcard :
      ((Finset.univ : Finset (ZMod Q)).filter
        (fun x => ZMod.castHom hqQ (ZMod q) x = y)).card = Q / q := by
    have hy : (y.val : ZMod q) = y := ZMod.natCast_zmod_val y
    have hyInt : ((y.val : ℤ) : ZMod q) = y := by simpa using hy
    have hc := card_congruenceClass hqQ hq0 (y.val : ℤ)
    let F := (Finset.univ : Finset (ZMod Q)).filter
      (fun x => ZMod.castHom hqQ (ZMod q) x = y)
    calc
      F.card = (↑F : Set (ZMod Q)).ncard := by simp
      _ = (congruenceClass Q q hqQ (y.val : ℤ)).ncard := by
        congr 1
        ext x
        simp only [F, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
          true_and, mem_congruenceClass, hyInt]
      _ = Q / q := hc
  unfold finiteFiberWeight periodicLiftWeight
  have hconst :
      ∑ x with ZMod.castHom hqQ (ZMod q) x = y,
          w (ZMod.castHom hqQ (ZMod q) x) / (Q / q : ℕ) =
        ∑ _x with ZMod.castHom hqQ (ZMod q) _x = y,
          w y / (Q / q : ℕ) := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [(Finset.mem_filter.mp hx).2]
  rw [hconst, Finset.sum_const, nsmul_eq_mul, hcard]
  field_simp [show ((Q / q : ℕ) : ℝ) ≠ 0 by positivity]

/-- Exact class-mass formula for a periodic lift.  In particular, any later
uniform coordinate extension preserves the mass of every old-coordinate
congruence event. -/
theorem finiteWeightMass_periodicLift_congruenceClass {Q q m : ℕ}
    [NeZero Q] [NeZero q]
    (hqQ : q ∣ Q) (hq0 : 0 < q) (hmq : m ∣ q) (w : ZMod q → ℝ) (b : ℤ) :
    finiteWeightMass (periodicLiftWeight hqQ w)
        (congruenceClass Q m (dvd_trans hmq hqQ) b) =
      finiteWeightMass w (congruenceClass q m hmq b) := by
  rw [congruenceClass_eq_preimage (Q := Q) (q := q) (m := m) hqQ hmq b]
  exact finiteWeightMass_preimage_eq_of_fiberWeight_eq
    (ZMod.castHom hqQ (ZMod q)) (periodicLiftWeight hqQ w) w
    (finiteFiberWeight_periodicLift hqQ hq0 w) (congruenceClass q m hmq b)

/-- A product-coordinate version of the `1/ℓ` factor in the `p ∤ m`
branch of the class-mass induction. -/
theorem finiteWeightMass_product_class {q g ℓ : ℕ} [NeZero q] [NeZero ℓ]
    (hgq : g ∣ q) (w : ZMod q → ℝ) (b : ℤ) :
    finiteWeightMass (fun z : ZMod q × ZMod ℓ => w z.1 / (ℓ : ℝ))
        {z | z.1 ∈ congruenceClass q g hgq b ∧ z.2 = (b : ZMod ℓ)} =
      finiteWeightMass w (congruenceClass q g hgq b) / (ℓ : ℝ) := by
  classical
  unfold finiteWeightMass
  rw [Fintype.sum_prod_type]
  apply Eq.trans ?_ (Finset.sum_div (s := Finset.univ) (f := fun x : ZMod q =>
    if x ∈ congruenceClass q g hgq b then w x else 0) (ℓ : ℝ)).symm
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hclass : x ∈ congruenceClass q g hgq b
  · simp only [Set.mem_ofPred_eq, Prod.fst, Prod.snd, hclass, true_and, if_true]
    rw [Finset.sum_ite_eq' Finset.univ (b : ZMod ℓ)]
    simp
  · simp only [Set.mem_ofPred_eq, Prod.fst, Prod.snd, hclass, false_and,
      if_false, Finset.sum_const_zero, zero_div]

/-! ## The processed-prime class-mass step -/

/-- If a modulus does not use the newly exposed coordinate, its congruence
event is pulled back from the old coordinate and distortion preserves its
mass exactly.  This is the cancellation used in the `p ∤ m` branch of the
class-mass induction. -/
theorem finiteWeightMass_distort_old_congruenceClass
    {q m : ℕ} [NeZero q] {Y : Type*} [Fintype Y] [Nonempty Y]
    (μ : FiniteProbability (ZMod q)) (B : Set (ZMod q × Y))
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2)
    (hmq : m ∣ q) (b : ℤ) :
    finiteWeightMass (distortWeight μ B δ)
        {z | z.1 ∈ congruenceClass q m hmq b} =
      μ.mass (congruenceClass q m hmq b) := by
  classical
  unfold finiteWeightMass FiniteProbability.mass
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hclass : x ∈ congruenceClass q m hmq b
  · simp only [Set.mem_setOf_eq, hclass, if_true]
    exact distort_fiber_sum μ B hδ0 hδhalf x
  · simp only [Set.mem_ofPred_eq, Prod.fst, hclass, if_false,
      Finset.sum_const_zero]

/-- Every distorted point weight is at most the uniform-lift weight times
`(1-δ)⁻¹`. -/
theorem distortWeight_le_uniformLift_div
    {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty Y]
    (μ : FiniteProbability X) (B : Set (X × Y))
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2) (z : X × Y) :
    distortWeight μ B δ z ≤ uniformLiftWeight μ z / (1 - δ) := by
  calc
    distortWeight μ B δ z ≤ (1 / (1 - δ)) * uniformLiftWeight μ z :=
      distortWeight_le_uniform_div μ B hδ0 hδhalf z
    _ = uniformLiftWeight μ z / (1 - δ) := by ring

/-- The distorted mass of any event is bounded by `(1-δ)⁻¹` times its
uniform-lift mass. -/
theorem finiteWeightMass_distort_le_uniformLift
    {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty Y]
    (μ : FiniteProbability X) (B S : Set (X × Y))
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2) :
    finiteWeightMass (distortWeight μ B δ) S ≤
      finiteWeightMass (uniformLiftWeight μ) S / (1 - δ) := by
  classical
  unfold finiteWeightMass
  calc
    (∑ z, if z ∈ S then distortWeight μ B δ z else 0) ≤
        ∑ z, if z ∈ S then uniformLiftWeight μ z / (1 - δ) else 0 := by
      apply Finset.sum_le_sum
      intro z hz
      by_cases hS : z ∈ S
      · simp [hS, distortWeight_le_uniformLift_div μ B hδ0 hδhalf z]
      · simp [hS]
    _ = (∑ z, if z ∈ S then uniformLiftWeight μ z else 0) / (1 - δ) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro z hz
      by_cases hS : z ∈ S <;> simp [hS]

/-- Uniform extension across a prime-power coordinate contributes exactly
the reciprocal of the modulus imposed in that coordinate. -/
theorem finiteWeightMass_uniformLift_product_congruenceClass
    {q g P e : ℕ} [NeZero q] [NeZero P]
    (hgq : g ∣ q) (heP : e ∣ P) (he0 : 0 < e)
    (μ : FiniteProbability (ZMod q)) (a b : ℤ) :
    finiteWeightMass (uniformLiftWeight μ)
        {z : ZMod q × ZMod P |
          z.1 ∈ congruenceClass q g hgq a ∧
            z.2 ∈ congruenceClass P e heP b} =
      μ.mass (congruenceClass q g hgq a) / (e : ℝ) := by
  classical
  have hP0 : (0 : ℝ) < P := by exact_mod_cast NeZero.pos P
  have heReal : (e : ℝ) ≠ 0 := by positivity
  have hPe : ((P / e : ℕ) : ℝ) * (e : ℝ) = (P : ℝ) := by
    exact_mod_cast Nat.div_mul_cancel heP
  have hcard : (congruenceClass P e heP b).ncard = P / e :=
    card_congruenceClass heP he0 b
  unfold finiteWeightMass uniformLiftWeight FiniteProbability.mass
  rw [Fintype.sum_prod_type]
  simp only [Set.mem_ofPred_eq, Prod.fst, Prod.snd]
  calc
    (∑ x : ZMod q, ∑ y : ZMod P,
        if x ∈ congruenceClass q g hgq a ∧ y ∈ congruenceClass P e heP b then
          μ.weight x / (Fintype.card (ZMod P) : ℕ) else 0) =
        ∑ x : ZMod q,
          if x ∈ congruenceClass q g hgq a then μ.weight x / (e : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hxclass : x ∈ congruenceClass q g hgq a
      · simp only [hxclass, true_and, Finset.sum_ite_irrel, Finset.sum_const_zero]
        rw [← Finset.sum_filter]
        simp only [Finset.sum_const, nsmul_eq_mul, ZMod.card]
        rw [show ((Finset.univ : Finset (ZMod P)).filter
          (fun y => y ∈ congruenceClass P e heP b)).card = P / e by
            let F := (Finset.univ : Finset (ZMod P)).filter
              (fun y => y ∈ congruenceClass P e heP b)
            calc
              F.card = (↑F : Set (ZMod P)).ncard := by simp
              _ = (congruenceClass P e heP b).ncard := by
                congr 1
                ext y
                simp [F]
              _ = P / e := hcard]
        simp only [if_true]
        rw [show ((P / e : ℕ) : ℝ) * (μ.weight x / (P : ℝ)) =
            μ.weight x / (e : ℝ) by
          field_simp [heReal, ne_of_gt hP0]
          linear_combination (μ.weight x) * hPe]
      · simp [hxclass]
    _ = (∑ x : ZMod q,
        if x ∈ congruenceClass q g hgq a then μ.weight x else 0) / (e : ℝ) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro x hx
      by_cases h : x ∈ congruenceClass q g hgq a <;> simp [h]

/-- One processed-prime update for a class using `e` in the new coordinate.
It is the local estimate which contributes the factor
`1 / (e * (1-δ))`; the preceding preservation theorem is the `p ∤ m`
alternative. -/
theorem finiteWeightMass_distort_product_congruenceClass_le
    {q g P e : ℕ} [NeZero q] [NeZero P]
    (hgq : g ∣ q) (heP : e ∣ P) (he0 : 0 < e)
    (μ : FiniteProbability (ZMod q)) (B : Set (ZMod q × ZMod P))
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2) (a b : ℤ) :
    finiteWeightMass (distortWeight μ B δ)
        {z : ZMod q × ZMod P |
          z.1 ∈ congruenceClass q g hgq a ∧
            z.2 ∈ congruenceClass P e heP b} ≤
      μ.mass (congruenceClass q g hgq a) / (e : ℝ) / (1 - δ) := by
  calc
    finiteWeightMass (distortWeight μ B δ) _ ≤
        finiteWeightMass (uniformLiftWeight μ) _ / (1 - δ) :=
      finiteWeightMass_distort_le_uniformLift μ B _ hδ0 hδhalf
    _ = μ.mass (congruenceClass q g hgq a) / (e : ℝ) / (1 - δ) := by
      rw [finiteWeightMass_uniformLift_product_congruenceClass
        hgq heP he0 μ a b]

/-! ## Induction over the processed primes -/

/-- The product of the distortion factors contributed by the first `r`
prime stages which divide `m`.  The recursive form is convenient for the
class-mass induction and is definitionally finite. -/
def processedClassFactor (p : ℕ → ℕ) (δ : ℕ → ℝ) (m : ℕ) : ℕ → ℝ
  | 0 => 1
  | r + 1 =>
      processedClassFactor p δ m r *
        if p (r + 1) ∣ m then 1 / (1 - δ (r + 1)) else 1

@[simp]
lemma processedClassFactor_zero (p : ℕ → ℕ) (δ : ℕ → ℝ) (m : ℕ) :
    processedClassFactor p δ m 0 = 1 := rfl

@[simp]
lemma processedClassFactor_succ (p : ℕ → ℕ) (δ : ℕ → ℝ) (m r : ℕ) :
    processedClassFactor p δ m (r + 1) =
      processedClassFactor p δ m r *
        if p (r + 1) ∣ m then 1 / (1 - δ (r + 1)) else 1 := rfl

/-- The complete class-mass induction.  `hdiv` is the one-step pointwise
distortion bound at a prime which divides the modulus; `hnodiv` is exact
fibre-mass conservation when that prime does not divide the modulus.  The
result is the finite version of Lemma 3.3 in BBMST specialized to one
congruence class. -/
theorem classMass_le_processedClassFactor
    {Q m : ℕ} [NeZero Q] (hmQ : m ∣ Q) (hm0 : 0 < m)
    (p : ℕ → ℕ) (μ : ℕ → FiniteProbability (ZMod Q)) (δ : ℕ → ℝ)
    (hδ0 : ∀ s, 0 ≤ δ s) (hδhalf : ∀ s, δ s ≤ 1 / 2)
    (hbase : ∀ b : ℤ,
      (μ 0).mass (congruenceClass Q m hmQ b) ≤ 1 / (m : ℝ))
    (hdiv : ∀ (r : ℕ) (b : ℤ), p (r + 1) ∣ m →
      (μ (r + 1)).mass (congruenceClass Q m hmQ b) ≤
        (μ r).mass (congruenceClass Q m hmQ b) / (1 - δ (r + 1)))
    (hnodiv : ∀ (r : ℕ) (b : ℤ), ¬p (r + 1) ∣ m →
      (μ (r + 1)).mass (congruenceClass Q m hmQ b) =
        (μ r).mass (congruenceClass Q m hmQ b)) :
    ∀ (r : ℕ) (b : ℤ),
      (μ r).mass (congruenceClass Q m hmQ b) ≤
        (1 / (m : ℝ)) * processedClassFactor p δ m r := by
  intro r
  induction r with
  | zero =>
      intro b
      simpa using hbase b
  | succ r ih =>
      intro b
      by_cases hp : p (r + 1) ∣ m
      · have hden : 0 < 1 - δ (r + 1) := by
          have := hδhalf (r + 1)
          linarith
        calc
          (μ (r + 1)).mass (congruenceClass Q m hmQ b) ≤
              (μ r).mass (congruenceClass Q m hmQ b) /
                (1 - δ (r + 1)) := hdiv r b hp
          _ ≤ ((1 / (m : ℝ)) * processedClassFactor p δ m r) /
                (1 - δ (r + 1)) :=
            div_le_div_of_nonneg_right (ih b) hden.le
          _ = (1 / (m : ℝ)) * processedClassFactor p δ m (r + 1) := by
            simp [processedClassFactor, hp]
            ring
      · calc
          (μ (r + 1)).mass (congruenceClass Q m hmQ b) =
              (μ r).mass (congruenceClass Q m hmQ b) := hnodiv r b hp
          _ ≤ (1 / (m : ℝ)) * processedClassFactor p δ m r := ih b
          _ = (1 / (m : ℝ)) * processedClassFactor p δ m (r + 1) := by
            simp [processedClassFactor, hp]

end

end Erdos586
