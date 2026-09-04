/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ErdosProblems.Erdos90b.External.ErdosUnitDistance.IdealFamily
import ErdosProblems.Erdos90b.External.TauCeti.NumberTheory.EffectiveBounds.UnitSquares.Basic

/-!
# The norm fibre

Class-group and unit-square-class pigeonholes turn the ideal family
into a set `Z = {z ∈ 𝔟 : z·z∗ = μ}` of exponential size, all of one
archimedean modulus.
-/

open scoped Classical
open NumberField IsCMField

namespace Erdos

/-
The ideal norm is invariant under the CM complex conjugation.
-/
theorem absNorm_map_conj (g : ℕ) (A : Ideal (𝓞 (Kf g))) :
    Ideal.absNorm (Ideal.map (ringOfIntegersComplexConj (Kf g)) A) = Ideal.absNorm A := by
  have h_card : Nat.card (𝓞 (Kf g) ⧸ A) = Nat.card (𝓞 (Kf g) ⧸ Ideal.map (ringOfIntegersComplexConj (Kf g)) A) := by
    refine' Nat.card_congr _;
    refine' ( Quotient.congr _ _ );
    exact ( ringOfIntegersComplexConj ( Kf g ) ).toEquiv;
    simp +decide only [AlgEquiv.toEquiv_eq_coe, EquivLike.coe_coe];
    intro a₁ a₂; rw [ ← map_sub ] ; rw [ Ideal.mem_map_iff_of_surjective ] ;
    · exact ⟨ fun h => ⟨ _, h, rfl ⟩, by rintro ⟨ x, hx, hx' ⟩ ; exact ( ringOfIntegersComplexConj ( Kf g ) ).injective hx' ▸ hx ⟩;
    · exact AlgEquiv.surjective _;
  convert! h_card.symm using 1

/-
At every infinite place, `z · conj z` has value `w(z)^2`.
-/
theorem place_mul_conj (g : ℕ) (z : 𝓞 (Kf g)) (w : InfinitePlace (Kf g)) :
    w (algebraMap (𝓞 (Kf g)) (Kf g) (z * ringOfIntegersComplexConj (Kf g) z))
      = (w (algebraMap (𝓞 (Kf g)) (Kf g) z)) ^ 2 := by
  rw [map_mul, map_mul, sq]
  congr 1
  have h : algebraMap (𝓞 (Kf g)) (Kf g) (ringOfIntegersComplexConj (Kf g) z)
      = complexConj (Kf g) (algebraMap (𝓞 (Kf g)) (Kf g) z) :=
    coe_ringOfIntegersComplexConj (Kf g) z
  rw [h, infinitePlace_complexConj]

/-
The absolute norm of `(n)` for a natural number `n` in `𝓞 (Kf g)` is `n^(2^(g+1))`.
-/
theorem absNorm_span_natCast (g : ℕ) (n : ℕ) :
    Ideal.absNorm (Ideal.span {((n : ℕ) : 𝓞 (Kf g))}) = n ^ 2 ^ (g + 1) := by
  -- By definition of algebra norm, we know that the norm of `n` in `Kf g` is `n^{[Kf g : ℚ]}`.
  have h_norm : Algebra.norm ℤ (n : (𝓞 (Kf g))) = n ^ (Module.finrank ℚ (Kf g)) := by
    erw [ Algebra.norm_apply ];
    erw [ show ( Algebra.lmul ℤ ( 𝓞 ( Kf g ) ) ) n = ( n : ℤ ) • LinearMap.id from ?_ ];
    · erw [ LinearMap.det_smul ] ; norm_num;
      rw [ ← NumberField.RingOfIntegers.rank ];
    · ext; simp [Algebra.lmul];
  convert congr_arg Int.natAbs h_norm using 1;
  · rw [ Ideal.absNorm_span_singleton ];
  · norm_num [ Kf_finrank ]

/-
If `A · conj A = (m)` then `absNorm A = m^(2^g)`.
-/
theorem absNorm_of_mul_conj (g : ℕ) (A : Ideal (𝓞 (Kf g))) (n : ℕ)
    (h : A * Ideal.map (ringOfIntegersComplexConj (Kf g)) A = Ideal.span {((n : ℕ) : 𝓞 (Kf g))}) :
    Ideal.absNorm A = n ^ 2 ^ g := by
  apply_fun Ideal.absNorm at h;
  rw [ Ideal.absNorm.map_mul ] at h;
  rw [ absNorm_map_conj, absNorm_span_natCast ] at h;
  rw [ ← sq_eq_sq₀ ] <;> first | positivity | ring_nf at * ; aesop;

/-- The product of `w(y · conj y)` over all infinite places equals `absNorm (y)`. -/
theorem prod_place_mul_conj (g : ℕ) (y : 𝓞 (Kf g)) :
    ∏ w : InfinitePlace (Kf g),
        w (algebraMap (𝓞 (Kf g)) (Kf g) (y * ringOfIntegersComplexConj (Kf g) y))
      = (Ideal.absNorm (Ideal.span {y}) : ℝ) := by
  have htc := Kf_isTotallyComplex g
  convert NumberField.InfinitePlace.prod_eq_abs_norm (algebraMap (𝓞 (Kf g)) (Kf g) y) using 1
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [place_mul_conj g y w, IsTotallyComplex.mult_eq w]
  · rw [Ideal.absNorm_span_singleton, ← Algebra.coe_norm_int]
    push_cast [Int.abs_eq_natAbs]
    exact_mod_cast Nat.cast_natAbs (Algebra.norm ℤ y)

/-
Pigeonhole: some fiber of `f` has size at least `s.card / card β`.
-/
theorem exists_fiber_card_ge {α β : Type*} [Fintype β] [DecidableEq β] [Nonempty β]
    (s : Finset α) (f : α → β) :
    ∃ y : β, s.card ≤ {x ∈ s | f x = y}.card * Fintype.card β := by
  obtain ⟨y₀, -, hy₀⟩ := Finset.exists_max_image (Finset.univ : Finset β)
    (fun y => {x ∈ s | f x = y}.card) Finset.univ_nonempty
  refine ⟨y₀, ?_⟩
  calc s.card = ∑ y : β, {x ∈ s | f x = y}.card := by
              rw [← Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ (f x))]
    _ ≤ ∑ _y : β, {x ∈ s | f x = y₀}.card :=
              Finset.sum_le_sum (fun y _ => hy₀ y (Finset.mem_univ y))
    _ = {x ∈ s | f x = y₀}.card * Fintype.card β := by
              rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]

/-
The maximal totally real subfield of `K_g` has degree `2^g` over `ℚ`.
-/
theorem Kf_maximalReal_finrank (g : ℕ) :
    Module.finrank ℚ (maximalRealSubfield (Kf g)) = 2 ^ g := by
  have h1 : Module.finrank ℚ (Kf g) = 2 ^ (g + 1) := Kf_finrank g
  have h2 : Module.finrank (maximalRealSubfield (Kf g)) (Kf g) = 2 :=
    Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have h3 := Module.finrank_mul_finrank ℚ (maximalRealSubfield (Kf g)) (Kf g)
  rw [h1, h2, pow_succ] at h3
  omega

/-
The quotient of the unit group by squares is finite.
-/
theorem units_sq_quot_finite (F : Type) [Field F] [NumberField F] :
    Finite ((𝓞 F)ˣ ⧸ (MonoidHom.range (powMonoidHom 2 : (𝓞 F)ˣ →* (𝓞 F)ˣ))) := by
  have h_fg : AddGroup.FG (Additive ((𝓞 F)ˣ ⧸ (powMonoidHom 2 : (𝓞 F)ˣ →* (𝓞 F)ˣ).range)) := by
    have h_finite_gen : Monoid.FG ((𝓞 F)ˣ) := by
      grind +suggestions;
    convert AddGroup.fg_iff_addMonoid_fg.mpr _;
    obtain ⟨ S, hS ⟩ := h_finite_gen;
    refine' ⟨ S.image ( fun x => QuotientGroup.mk x ), _ ⟩;
    simp_all +decide [ SetLike.ext_iff, AddSubmonoid.mem_closure ];
    intro a S_1 hS_1; obtain ⟨ x, rfl ⟩ := QuotientGroup.mk_surjective a; simp_all +decide [ Set.subset_def, Submonoid.mem_closure ] ;
    specialize hS x ( Submonoid.comap ( QuotientGroup.mk' ( powMonoidHom 2 |> MonoidHom.range ) ) ( AddSubmonoid.toSubmonoid S_1 ) )
    exact hS fun s hs => hS_1 _ (Finset.mem_image.mpr ⟨s, hs, rfl⟩)
  have h_add_group : ∀ (G : Type) [AddCommGroup G] [AddGroup.FG G], (∀ g : G, 2 • g = 0) → Finite G := by
    intros G _ _ hG
    have h_vector_space : Module (ZMod 2) G := AddCommGroup.zmodModule hG
    have h_finite_dim : FiniteDimensional (ZMod 2) G := by
      have h_fg : Module.Finite (ZMod 2) G := by
        obtain ⟨ s, hs ⟩ := ‹AddGroup.FG G›;
        use s;
        simp_all +decide [ SetLike.ext_iff, AddSubgroup.mem_closure ];
        intro x; specialize hs x ( Submodule.toAddSubgroup ( Submodule.span ( ZMod 2 ) ( s : Set G ) ) ) ; simp_all +decide [ Set.subset_def, Submodule.mem_span ] ;
      lia;
    exact Finite.of_equiv _ ( ( Module.finBasis ( ZMod 2 ) G ).equivFun.symm.toEquiv );
  convert! h_add_group ( Additive ( ( 𝓞 F ) ˣ ⧸ ( powMonoidHom 2 : ( 𝓞 F ) ˣ →* ( 𝓞 F ) ˣ ).range ) ) _;
  rintro ⟨ a ⟩ ; exact QuotientGroup.eq.mpr ( by aesop ) ;

/-
Pigeonhole over square-classes of real units.
-/
theorem units_square_pigeonhole (g : ℕ) {α : Type*} (F₁ : Finset α)
    (ν : α → (𝓞 (maximalRealSubfield (Kf g)))ˣ) :
    ∃ F₂ : Finset α, F₂ ⊆ F₁ ∧ F₁.card ≤ F₂.card * 2 ^ 2 ^ g ∧
      ∀ A ∈ F₂, ∀ A' ∈ F₂, ∃ δ : (𝓞 (maximalRealSubfield (Kf g)))ˣ, ν A * (ν A')⁻¹ = δ ^ 2 := by
  obtain ⟨y, hy⟩ : ∃ y : (𝓞 (↥(maximalRealSubfield (Kf g))))ˣ ⧸ MonoidHom.range (powMonoidHom 2 : (𝓞 (↥(maximalRealSubfield (Kf g))))ˣ →* (𝓞 (↥(maximalRealSubfield (Kf g))))ˣ), F₁.card ≤ (Finset.filter (fun A => QuotientGroup.mk (ν A) = y) F₁).card * 2 ^ 2 ^ g := by
    have h_finite : Finite ((𝓞 (↥(maximalRealSubfield (Kf g))))ˣ ⧸ MonoidHom.range (powMonoidHom 2 : (𝓞 (↥(maximalRealSubfield (Kf g))))ˣ →* (𝓞 (↥(maximalRealSubfield (Kf g))))ˣ)) := by
      convert units_sq_quot_finite ( maximalRealSubfield ( Kf g ) );
    have h_finite : Fintype ((𝓞 (↥(maximalRealSubfield (Kf g))))ˣ ⧸ MonoidHom.range (powMonoidHom 2 : (𝓞 (↥(maximalRealSubfield (Kf g))))ˣ →* (𝓞 (↥(maximalRealSubfield (Kf g))))ˣ)) := by
      exact Fintype.ofFinite _;
    have h_finite : Fintype.card ((𝓞 (↥(maximalRealSubfield (Kf g))))ˣ ⧸ MonoidHom.range (powMonoidHom 2 : (𝓞 (↥(maximalRealSubfield (Kf g))))ˣ →* (𝓞 (↥(maximalRealSubfield (Kf g))))ˣ)) ≤ 2 ^ 2 ^ g := by
      have hsq : MonoidHom.range
            (powMonoidHom 2 : (𝓞 (↥(maximalRealSubfield (Kf g))))ˣ →* _)
          = Subgroup.square ((𝓞 (↥(maximalRealSubfield (Kf g))))ˣ) := by
        ext x
        rw [MonoidHom.mem_range, Subgroup.mem_square]
        constructor <;> rintro ⟨h, rfl⟩ <;> exact ⟨h, by rw [powMonoidHom_apply, sq]⟩
      rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card, hsq]
      exact (TauCeti.NumberField.units_sq_index_le (↥(maximalRealSubfield (Kf g)))).trans
        (pow_le_pow_right₀ (by decide) (Kf_maximalReal_finrank g).le)
    have := @exists_fiber_card_ge;
    exact Exists.elim ( this F₁ ( fun A => QuotientGroup.mk ( ν A ) ) ) fun y hy => ⟨ y, hy.trans ( Nat.mul_le_mul_left _ h_finite ) ⟩;
  refine' ⟨ _, _, hy, _ ⟩;
  · exact Finset.filter_subset _ _;
  · intro A hA A' hA'
    obtain ⟨δ, hδ⟩ : ∃ δ : (𝓞 (↥(maximalRealSubfield (Kf g))))ˣ, (ν A)⁻¹ * (ν A') = δ ^ 2 := by
      have h_eq : (ν A)⁻¹ * ν A' ∈ MonoidHom.range (powMonoidHom 2 : (𝓞 (↥(maximalRealSubfield (Kf g))))ˣ →* (𝓞 (↥(maximalRealSubfield (Kf g))))ˣ) := by
        rw [ ← QuotientGroup.eq_one_iff ] at * ; aesop;
      exact h_eq.imp fun x hx => by simpa [ sq ] using hx.symm;
    generalize_proofs at *; (
    exact ⟨ δ⁻¹, by simpa [ mul_comm ] using congr_arg Inv.inv hδ ⟩)

/-
Two associate conjugation-fixed integers differ by a unit coming from `K⁺`.
-/
theorem descent_unit (g : ℕ) (a b : 𝓞 (Kf g))
    (ha : ringOfIntegersComplexConj (Kf g) a = a)
    (hb : ringOfIntegersComplexConj (Kf g) b = b) (hb0 : b ≠ 0)
    (hab : Ideal.span {a} = Ideal.span {b}) :
    ∃ u : (𝓞 (maximalRealSubfield (Kf g)))ˣ,
      algebraMap (𝓞 (maximalRealSubfield (Kf g))) (𝓞 (Kf g)) (u : 𝓞 (maximalRealSubfield (Kf g))) * b = a := by
  obtain ⟨u, hu⟩ : ∃ u : (𝓞 (Kf g))ˣ, a = u * b := by
    have := Ideal.span_singleton_eq_span_singleton.mp hab;
    obtain ⟨ u, hu ⟩ := this.symm;
    exact ⟨ u, by rw [ ← hu, mul_comm ] ⟩;
  have h_fixed : (complexConj (Kf g)) (u : Kf g) = (u : Kf g) := by
    have h_conj_u : (ringOfIntegersComplexConj (Kf g)) (u : (𝓞 (Kf g))) = (u : (𝓞 (Kf g))) := by
      simp_all +decide [ ringOfIntegersComplexConj ];
    convert! congr_arg ( algebraMap ( 𝓞 ( Kf g ) ) ( Kf g ) ) h_conj_u using 1;
  have := @Units.complexConj_eq_self_iff ( Kf g );
  obtain ⟨ v, hv ⟩ := this u |>.1 h_fixed;
  use v;
  simp +decide [RingOfIntegers.ext_iff ];
  convert! congr_arg ( fun x : Kf g => x * b ) hv using 1;
  exact congr_arg ( algebraMap ( 𝓞 ( Kf g ) ) ( Kf g ) ) hu

/-- Conjugation is involutive on the ring of integers. -/
theorem ringConj_ringConj (g : ℕ) (x : 𝓞 (Kf g)) :
    ringOfIntegersComplexConj (Kf g) (ringOfIntegersComplexConj (Kf g) x) = x := by
  apply RingOfIntegers.ext
  rw [coe_ringOfIntegersComplexConj, coe_ringOfIntegersComplexConj, complexConj_apply_apply]

/-
After pigeonholing, a subfamily with a common `z · conj z = μ`.
-/
theorem norm_constant_subfamily (g : ℕ) {α : Type*} (F₁ : Finset α) (y : α → 𝓞 (Kf g))
    (hy0 : ∀ A ∈ F₁, y A ≠ 0)
    (hassoc : ∀ A ∈ F₁, ∀ A' ∈ F₁,
      Ideal.span {y A * ringOfIntegersComplexConj (Kf g) (y A)}
        = Ideal.span {y A' * ringOfIntegersComplexConj (Kf g) (y A')}) :
    ∃ (F₂ : Finset α) (μ : 𝓞 (Kf g)), F₂ ⊆ F₁ ∧ F₁.card ≤ F₂.card * 2 ^ 2 ^ g ∧
      ∀ A ∈ F₂, ∃ z : 𝓞 (Kf g), Ideal.span {z} = Ideal.span {y A} ∧
        z * ringOfIntegersComplexConj (Kf g) z = μ := by
  by_cases hF₁ : F₁.Nonempty;
  · obtain ⟨A₀, hA₀⟩ : ∃ A₀ ∈ F₁, True := by
      exact ⟨ hF₁.choose, hF₁.choose_spec, trivial ⟩;
    -- For each `A ∈ F₁`, define `U A : (𝓞 (maximalRealSubfield (Kf g)))ˣ` by `descent_unit` with `a := ν A`, `b := ν A₀`.
    have hU : ∀ A ∈ F₁, ∃ U : (𝓞 (maximalRealSubfield (Kf g)))ˣ, algebraMap (𝓞 (maximalRealSubfield (Kf g))) (𝓞 (Kf g)) (U : 𝓞 (maximalRealSubfield (Kf g))) * (y A₀ * ringOfIntegersComplexConj (Kf g) (y A₀)) = y A * ringOfIntegersComplexConj (Kf g) (y A) := by
      intro A hA
      apply descent_unit g (y A * ringOfIntegersComplexConj (Kf g) (y A)) (y A₀ * ringOfIntegersComplexConj (Kf g) (y A₀)) (by
      simp +decide only [map_mul];
      exact mul_comm _ _) (by
      grind +suggestions) (by
      simp_all +decide [ mul_eq_zero ]) (by
      exact hassoc A hA A₀ hA₀.1);
    choose! U hU using hU;
    obtain ⟨F₂, hF₂⟩ := units_square_pigeonhole g F₁ U;
    obtain ⟨A₁, hA₁⟩ : ∃ A₁ ∈ F₂, True := by
      exact Exists.elim ( Finset.card_pos.mp ( by nlinarith [ Finset.card_pos.mpr hF₁, Nat.one_le_pow ( 2 ^ g ) 2 zero_lt_two ] ) ) fun x hx => ⟨ x, hx, trivial ⟩;
    refine' ⟨ F₂, y A₁ * ( ringOfIntegersComplexConj ( Kf g ) ) ( y A₁ ), hF₂.1, hF₂.2.1, fun A hA => _ ⟩;
    obtain ⟨ δ, hδ ⟩ := hF₂.2.2 A hA A₁ hA₁.1;
    refine' ⟨ y A * ( Units.map ( algebraMap ( 𝓞 ( maximalRealSubfield ( Kf g ) ) ) ( 𝓞 ( Kf g ) ) |> RingHom.toMonoidHom ) δ⁻¹ ), _, _ ⟩;
    · refine' le_antisymm _ _ <;> simp +decide only [RingHom.toMonoidHom_eq_coe, map_inv, Units.coe_map_inv, MonoidHom.coe_coe,
    Submodule.span_singleton_le_iff_mem];
      exact Ideal.mem_span_singleton.mpr
        ⟨algebraMap _ _ ((δ : (𝓞 (maximalRealSubfield (Kf g)))ˣ) : 𝓞 (maximalRealSubfield (Kf g))),
         by rw [mul_assoc, ← map_mul, Units.inv_mul, map_one, mul_one]⟩;
    · have hδ_eq : algebraMap (𝓞 (maximalRealSubfield (Kf g))) (𝓞 (Kf g)) (U A) = (algebraMap (𝓞 (maximalRealSubfield (Kf g))) (𝓞 (Kf g)) δ) ^ 2 * algebraMap (𝓞 (maximalRealSubfield (Kf g))) (𝓞 (Kf g)) (U A₁) := by
        replace hδ := congr_arg ( fun x : ( 𝓞 ( maximalRealSubfield ( Kf g ) ) ) ˣ => ( algebraMap ( 𝓞 ( maximalRealSubfield ( Kf g ) ) ) ( 𝓞 ( Kf g ) ) ) x ) hδ ; simp_all +decide [ mul_assoc, pow_two ];
        simp_all +decide [ ← mul_assoc ];
        rw [ ← hδ, mul_assoc ];
        simp +decide [ ← map_mul ];
      simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ];
      simp_all +decide [ ← mul_assoc, ← hU A ( hF₂.1 hA ), ← hU A₁ ( hF₂.1 hA₁ ) ];
      simp +decide [ sq, mul_assoc ];
      simp +decide [ ← mul_assoc, ← map_mul ];
  · aesop

/-
Class-group pigeonhole: a subfamily lying in one class, an ideal `b` in the inverse
class, and principal generators `y A` of `A * b`.
-/
theorem stage1 (g : ℕ) (F : Finset (Ideal (𝓞 (Kf g)))) (hF : ∀ A ∈ F, A ≠ ⊥) :
    ∃ (b : Ideal (𝓞 (Kf g))) (F₁ : Finset (Ideal (𝓞 (Kf g)))) (y : Ideal (𝓞 (Kf g)) → 𝓞 (Kf g)),
      b ≠ ⊥ ∧ F₁ ⊆ F ∧ F.card ≤ F₁.card * NumberField.classNumber (Kf g) ∧
      ∀ A ∈ F₁, y A ≠ 0 ∧ Ideal.span {y A} = A * b := by
  -- Define `φ : Ideal (𝓞 (Kf g)) → ClassGroup (𝓞 (Kf g))` by `φ A := if h : A ≠ ⊥ then ClassGroup.mk0 ⟨A, mem_nonZeroDivisors_of_ne_zero h⟩ else 1`.
  set φ : Ideal (𝓞 (Kf g)) → ClassGroup (𝓞 (Kf g)) := fun A =>
    if h : A ≠ ⊥ then ClassGroup.mk0 ⟨A, mem_nonZeroDivisors_of_ne_zero h⟩ else 1;
  -- By `exists_fiber_card_ge F φ`, there is a class `c` with `F.card ≤ {A ∈ F | φ A = c}.card * Fintype.card (ClassGroup (𝓞 (Kf g)))`.
  obtain ⟨c, hc⟩ : ∃ c : ClassGroup (𝓞 (Kf g)), F.card ≤ (Finset.filter (fun A => φ A = c) F).card * Fintype.card (ClassGroup (𝓞 (Kf g))) := by
    convert exists_fiber_card_ge F φ;
  -- Choose `b' ∈ nonZeroDivisors (Ideal (𝓞 (Kf g)))` with `ClassGroup.mk0 b' = c⁻¹`;
  obtain ⟨b', hb'⟩ : ∃ b' : { x : Ideal (𝓞 (Kf g)) // x ∈ nonZeroDivisors (Ideal (𝓞 (Kf g)) ) }, ClassGroup.mk0 b' = c⁻¹ := by
    have := ClassGroup.mk0_surjective ( c⁻¹ );
    exact this;
  refine' ⟨ b', Finset.filter ( fun A => φ A = c ) F, _ ⟩;
  simp +zetaDelta only [ne_eq, Finset.filter_subset, Finset.mem_filter, and_imp, true_and, exists_and_left] at *;
  refine' ⟨ _, _, _ ⟩;
  · exact fun h => by simpa [ h ] using b'.2;
  · convert! hc using 1;
  · have h_principal : ∀ A ∈ F, (if h : A = ⊥ then 1 else ClassGroup.mk0 ⟨A, mem_nonZeroDivisors_of_ne_zero h⟩) = c → ∃ a : 𝓞 (Kf g), A * b' = Ideal.span {a} ∧ a ≠ 0 := by
      intro A hA hA'; split_ifs at hA' ; simp_all +decide  ;
      have h_principal : ClassGroup.mk0 (⟨A, mem_nonZeroDivisors_of_ne_zero ‹_›⟩ * b') = 1 := by
        convert congr_arg₂ ( · * · ) hA' hb' using 1;
        · convert map_mul ( ClassGroup.mk0 : nonZeroDivisors ( Ideal ( 𝓞 ( Kf g ) ) ) →* ClassGroup ( 𝓞 ( Kf g ) ) ) _ _ using 1;
        · rw [ mul_inv_cancel ];
      rw [ ClassGroup.mk0_eq_one_iff ] at h_principal;
      obtain ⟨ a, ha ⟩ := h_principal;
      refine' ⟨ a, _, _ ⟩ <;> simp_all +decide only [ne_eq] ;
      intro ha'; simp_all +decide  ;
      exact absurd ha ( by exact fun h => by have := b'.2; simp_all +decide [ nonZeroDivisors ] );
    choose! a ha₁ ha₂ using h_principal;
    exact ⟨ a, fun A hA hA' => ⟨ ha₂ A hA hA', ha₁ A hA hA' ▸ rfl ⟩ ⟩

/-- [medium-hard given `exists_ideal_family` and `units_sq_index_le`]
**The norm fibre `Z`.**  There exist a nonzero integral ideal `b`, a
nonzero `μ ∈ K_g` and a finite set `Z` of integers of `K_g`, all lying in
`b`, such that:
* every `z ∈ Z` satisfies `w(z)² = w(μ)` at every infinite place `w`
  (i.e. `z · z∗ = μ`, one archimedean modulus at every place);
* `∏_w w(μ) = (m t)^(2^g) · N(b)`;
* `#Z ≥ 2^(t·2^(g-1)) / (h_K · 2^(2^g))`.

Sketch: pigeonhole the family from `exists_ideal_family` into one ideal
class (`h_K` classes; use `ClassGroup.mk0`); pick an integral ideal `b`
in the inverse class (`ClassGroup.mk0_surjective`); each `𝔄·b = (y_𝔄)` is
principal with `y_𝔄 ∈ b`, and `y_𝔄 y_𝔄∗` generates `(m t)·b·b∗`, so the
ratios are totally positive units of `𝒪_{K⁺}` (totally positive since
`σ(y y∗) = |σ y|² > 0`); pigeonhole over the `≤ 2^(2^g)` square-classes of
units (`units_sq_index_le` for `K⁺`, of degree `2^g`), and set
`z_𝔄 = y_𝔄 ε_𝔄⁻¹`, `μ = z z∗` (common value).  Injectivity of `𝔄 ↦ z_𝔄`:
`(z_𝔄) = 𝔄 b` and Dedekind cancellation.  The norm identity:
`N_{K/ℚ}(μ) = N(m·b·b∗) = (m t)^(2^(g+1)) N(b)²` and
`∏_w w(μ) = √|N_{K/ℚ}(μ)|` (places squared), giving
`(m t)^(2^g) · N(b)`.  The place identity: `w(z)² = w(z) w(z∗) = w(z z∗)`
using `infinitePlace_complexConj`.
-/
theorem arithmetic_construction (g t : ℕ) (hg : 1 ≤ g) (ht : 1 ≤ t) :
    ∃ (b : Ideal (𝓞 (Kf g))) (μ : Kf g) (Z : Finset (𝓞 (Kf g))),
      b ≠ ⊥ ∧ μ ≠ 0 ∧
      (∀ z ∈ Z, z ∈ b) ∧
      (∀ z ∈ Z, ∀ w : InfinitePlace (Kf g),
        (w (algebraMap (𝓞 (Kf g)) (Kf g) z)) ^ 2 = w μ) ∧
      (∏ w : InfinitePlace (Kf g), w μ) = (m t : ℝ) ^ 2 ^ g * (Ideal.absNorm b : ℝ) ∧
      (2 : ℝ) ^ (t * 2 ^ (g - 1)) ≤
        (Z.card : ℝ) * (NumberField.classNumber (Kf g)) * 2 ^ 2 ^ g := by
  -- Let `conj := ringOfIntegersComplexConj (Kf g)` and `m := m t`.
  set conj := ringOfIntegersComplexConj (Kf g)
  set m := m t;
  -- From `exists_ideal_family g t hg` obtain `F` with `(2:ℝ)^(t*2^(g-1)) ≤ F.card` and `hFm : ∀ A ∈ F, A * Ideal.map conj A = Ideal.span {(m : 𝓞 (Kf g))}`.
  obtain ⟨F, hFcard, hF⟩ := exists_ideal_family g t hg;
  -- Apply `stage1 g F` to get `b, F₁, y` with `b ≠ ⊥`, `F₁ ⊆ F`, `F.card ≤ F₁.card * classNumber (Kf g)`, and `hy : ∀ A ∈ F₁, y A ≠ 0 ∧ Ideal.span {y A} = A * b`.
  obtain ⟨b, F₁, y, hb, hF₁, hF₁card, hy⟩ := stage1 g F (by
  intro A hA hA'; specialize hF A hA; simp_all +decide  ;
  rw [ eq_comm, Ideal.span_singleton_eq_bot ] at hF ; norm_cast at hF;
  exact absurd hF <| ne_of_gt <| Finset.prod_pos fun i hi => Nat.Prime.pos <| p1_spec i |>.1);
  -- Establish `hassoc : ∀ A ∈ F₁, ∀ A' ∈ F₁, Ideal.span {y A * conj (y A)} = Ideal.span {y A' * conj (y A')}` by showing each side equals `Ideal.span {(m : 𝓞 (Kf g))} * (b * Ideal.map conj b)`.
  have hassoc : ∀ A ∈ F₁, ∀ A' ∈ F₁, Ideal.span {y A * conj (y A)} = Ideal.span {y A' * conj (y A')} := by
    intros A hA A' hA'
    have h_eq : Ideal.span {y A * conj (y A)} = Ideal.span {(m : 𝓞 (Kf g))} * (b * Ideal.map conj b) := by
      have h_eq : Ideal.span {y A * conj (y A)} = Ideal.span {y A} * Ideal.map conj (Ideal.span {y A}) := by
        simp +decide [ Ideal.span_singleton_mul_span_singleton, Ideal.map_span ];
      rw [ h_eq, hy A hA |>.2 ];
      rw [ ← hF A ( hF₁ hA ) ];
      rw [ Ideal.map_mul ] ; ring
    have h_eq' : Ideal.span {y A' * conj (y A')} = Ideal.span {(m : 𝓞 (Kf g))} * (b * Ideal.map conj b) := by
      have h_eq' : Ideal.span {y A' * conj (y A')} = Ideal.span {y A'} * Ideal.map conj (Ideal.span {y A'}) := by
        simp +decide [ Ideal.map_span, Ideal.span_singleton_mul_span_singleton ];
      rw [ h_eq', hy A' hA' |>.2, Ideal.map_mul ];
      rw [ ← hF A' ( hF₁ hA' ) ] ; ring
    rw [h_eq, h_eq'];
  -- Apply `norm_constant_subfamily g F₁ y (fun A hA => (hy A hA).1) hassoc` to get `F₂ ⊆ F₁`, `μ₀`, `F₁.card ≤ F₂.card * 2^(2^g)`, and `hz : ∀ A ∈ F₂, ∃ z, Ideal.span {z} = Ideal.span {y A} ∧ z * conj z = μ₀`.
  obtain ⟨F₂, μ₀, hF₂, hF₂card, hz⟩ := norm_constant_subfamily g F₁ y (fun A hA => (hy A hA).1) hassoc;
  -- With `Classical.choose`, define `zf` so that for `A ∈ F₂`: `Ideal.span {zf A} = Ideal.span {y A}` and `zf A * conj (zf A) = μ₀`.
  obtain ⟨zf, hzf⟩ : ∃ zf : Ideal (𝓞 (Kf g)) → 𝓞 (Kf g), ∀ A ∈ F₂, Ideal.span {zf A} = Ideal.span {y A} ∧ zf A * conj (zf A) = μ₀ := by
    exact ⟨ fun A => if hA : A ∈ F₂ then Classical.choose ( hz A hA ) else 0, fun A hA => by simpa [ hA ] using Classical.choose_spec ( hz A hA ) ⟩;
  refine' ⟨ b, algebraMap (𝓞 (Kf g)) (Kf g) μ₀, F₂.image zf, hb, _, _, _, _ ⟩;
  · -- Since $μ₀$ is a product of non-zero elements, it cannot be zero.
    have hμ₀_nonzero : μ₀ ≠ 0 := by
      obtain ⟨A, hA⟩ : ∃ A ∈ F₂, True := by
        contrapose! hFcard;
        simp_all +decide [ Finset.eq_empty_of_forall_notMem hFcard ];
      intro hμ₀_zero
      have hzf_zero : zf A = 0 := by
        simp_all +decide ;
      have := hzf A hA.1; simp_all +decide  ;
      exact hy A ( hF₂ hA ) |>.1 ( by simpa using this.symm );
    intro h
    exact hμ₀_nonzero (IsFractionRing.injective (𝓞 (Kf g)) (Kf g) (by rw [map_zero]; exact h))
  · simp +zetaDelta only [Finset.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at *;
    intro A hA;
    have hzfA_in_b : Ideal.span {zf A} ≤ b := by
      rw [ hzf A hA |>.1, hy A ( hF₂ hA ) |>.2 ];
      exact Ideal.mul_le_right (I := A)
    exact hzfA_in_b <| Ideal.mem_span_singleton_self _;
  · simp +zetaDelta only [Finset.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at *;
    intro A hA w; rw [ ← hzf A hA |>.2 ] ; rw [ ← place_mul_conj ] ;
  · refine' ⟨ _, _ ⟩;
    · obtain ⟨A₀, hA₀⟩ : ∃ A₀ ∈ F₂, True := by
        contrapose! hFcard;
        simp_all +decide [ Finset.eq_empty_of_forall_notMem hFcard ];
      have h_norm : Ideal.absNorm (Ideal.span {zf A₀}) = m ^ 2 ^ g * Ideal.absNorm b := by
        have h_norm : Ideal.absNorm A₀ = m ^ 2 ^ g := by
          apply absNorm_of_mul_conj g A₀ m (hF A₀ (hF₁ (hF₂ hA₀.left)));
        grind;
      have h_norm : ∏ w : InfinitePlace (Kf g), w (algebraMap (𝓞 (Kf g)) (Kf g) (zf A₀ * conj (zf A₀))) = (Ideal.absNorm (Ideal.span {zf A₀}) : ℝ) := by
        convert prod_place_mul_conj g ( zf A₀ ) using 1;
      aesop;
    · rw [ Finset.card_image_of_injOn ];
      · norm_cast at *;
        nlinarith [ show 0 < classNumber ( Kf g ) from Nat.pos_of_ne_zero ( by aesop ) ];
      · intro A hA A' hA' h_eq;
        have := hzf A hA; have := hzf A' hA'; simp_all +decide  ;
        have := hy A ( hF₂ hA ) ; have := hy A' ( hF₂ hA' ) ; simp_all +decide  ;

end Erdos
