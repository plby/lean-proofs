/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ErdosProblems.Erdos90b.External.ErdosUnitDistance.NormFibre
import ErdosProblems.Erdos90b.External.ErdosUnitDistance.GeometricCore

/-!
# The planar point set

The Minkowski embedding of `𝔟` into `ℂ^(2^g)`, the separation estimate,
and the application of the geometric core: an `n`-point planar set with
the three counting estimates feeding the final assembly.
-/

open scoped Classical
open NumberField IsCMField

namespace Erdos

/-- The coordinatewise-embeddings map `𝒪_{K_g} → (places → ℂ)`, sending
`x` to `(w.embedding x)_w` — one choice of embedding per conjugate pair.
This is the "Minkowski map" whose image of the ideal `b` is the lattice `Λ`
fed to the geometric core. -/
noncomputable def mink (g : ℕ) :
    𝓞 (Kf g) →+* (NumberField.InfinitePlace (Kf g) → ℂ) :=
  Pi.ringHom fun w => w.embedding.comp (algebraMap (𝓞 (Kf g)) (Kf g))

/-- General degree bound: a field obtained by adjoining a finite set of elements, each
integral of degree at most `2`, has degree at most `2 ^ (number of generators)`. -/
theorem finrank_adjoin_finset_le (s : Finset ℂ)
    (h : ∀ a ∈ s, IsIntegral ℚ a ∧ (minpoly ℚ a).natDegree ≤ 2) :
    Module.finrank ℚ (IntermediateField.adjoin ℚ (s : Set ℂ)) ≤ 2 ^ s.card := by
  classical
  induction s using Finset.induction with
  | empty =>
      rw [Finset.coe_empty, IntermediateField.adjoin_empty, IntermediateField.finrank_bot]
      simp
  | @insert a s ha ih =>
      have hmem : ∀ x ∈ s, IsIntegral ℚ x ∧ (minpoly ℚ x).natDegree ≤ 2 :=
        fun x hx => h x (Finset.mem_insert_of_mem hx)
      have ha2 := h a (Finset.mem_insert_self a s)
      have hsplit : IntermediateField.adjoin ℚ ((insert a s : Finset ℂ) : Set ℂ)
          = IntermediateField.adjoin ℚ ({a} : Set ℂ) ⊔ IntermediateField.adjoin ℚ (s : Set ℂ) := by
        rw [Finset.coe_insert, Set.insert_eq, IntermediateField.adjoin_union]
      have hfa : Module.finrank ℚ (IntermediateField.adjoin ℚ ({a} : Set ℂ)) ≤ 2 :=
        (IntermediateField.adjoin.finrank ha2.1).trans_le ha2.2
      rw [hsplit]
      refine le_trans (IntermediateField.finrank_sup_le _ _) ?_
      calc Module.finrank ℚ (IntermediateField.adjoin ℚ ({a} : Set ℂ))
              * Module.finrank ℚ (IntermediateField.adjoin ℚ (s : Set ℂ))
          ≤ 2 * 2 ^ s.card := Nat.mul_le_mul hfa (ih hmem)
        _ = 2 ^ (insert a s).card := by
            rw [Finset.card_insert_of_notMem ha, pow_succ]; ring

/-- Upper bound on the degree of the multiquadratic field: it is generated over `ℚ`
by the `g+1` elements `i, √q3 0, …, √q3 (g-1)`, each of degree at most `2`. -/
theorem Kf_finrank_le (g : ℕ) : Module.finrank ℚ (Kf g) ≤ 2 ^ (g + 1) := by
  have h_deg : ∀ x ∈ ({Complex.I} ∪ ((fun j => ((Real.sqrt (q3 j):ℝ):ℂ)) '' (Finset.range g) : Set ℂ)), IsIntegral ℚ x ∧ (minpoly ℚ x).natDegree ≤ 2 := by
    intro x hx; cases' hx with hx hx <;> simp_all +decide [ IsIntegral ] ;
    · refine' ⟨ _, _ ⟩;
      · exact ⟨ Polynomial.X ^ 2 + 1, by exact Polynomial.monic_X_pow_add_C _ two_ne_zero, by norm_num ⟩;
      · refine' le_trans ( Polynomial.natDegree_le_of_dvd _ _ ) _;
        exacts [ Polynomial.X ^ 2 + 1, minpoly.dvd ℚ Complex.I <| by norm_num [ Complex.ext_iff, sq ], by exact ne_of_apply_ne ( Polynomial.eval 0 ) <| by norm_num, by erw [ Polynomial.natDegree_X_pow_add_C ] ];
    · obtain ⟨ j, hj, rfl ⟩ := hx;
      -- The minimal polynomial of $\sqrt{q3 j}$ over $\mathbb{Q}$ is $x^2 - q3 j$.
      have h_minpoly : minpoly ℚ (Real.sqrt (q3 j) : ℂ) ∣ Polynomial.X ^ 2 - Polynomial.C (q3 j : ℚ) := by
        refine' minpoly.dvd ℚ _ _;
        norm_num [ ← Complex.ofReal_pow, Real.sq_sqrt ( Nat.cast_nonneg _ ) ];
      refine' ⟨ _, _ ⟩;
      · refine' ⟨ Polynomial.X ^ 2 - Polynomial.C ( q3 j : ℚ ), _, _ ⟩;
        · erw [ Polynomial.Monic, Polynomial.leadingCoeff_X_pow_sub_C ] ; norm_num;
        · norm_num [ ← Complex.ofReal_pow ];
      · exact le_trans ( Polynomial.natDegree_le_of_dvd h_minpoly ( Polynomial.X_pow_sub_C_ne_zero ( by norm_num ) _ ) ) ( by erw [ Polynomial.natDegree_X_pow_sub_C ] );
  set F : Finset ℂ :=
    insert Complex.I ((Finset.range g).image fun j => ((Real.sqrt (q3 j) : ℝ) : ℂ)) with hF
  have hset : (F : Set ℂ)
      = insert Complex.I ((fun j => ((Real.sqrt (q3 j) : ℝ) : ℂ)) '' Set.Iio g) := by
    simp [hF]
  have hKf : Module.finrank ℚ (Kf g)
      = Module.finrank ℚ (IntermediateField.adjoin ℚ (F : Set ℂ)) := by
    rw [Kf, ← hset]
  have hcard : F.card ≤ g + 1 :=
    (Finset.card_insert_le _ _).trans
      (Nat.succ_le_succ (Finset.card_image_le.trans (by simp)))
  rw [hKf]
  refine (finrank_adjoin_finset_le F ?_).trans (Nat.pow_le_pow_right (by norm_num) hcard)
  intro a ha
  refine h_deg a ?_
  simp only [hF, Finset.mem_insert, Finset.mem_image, Finset.mem_range] at ha
  rcases ha with rfl | ⟨j, hj, rfl⟩
  · exact Set.mem_union_left _ rfl
  · exact Set.mem_union_right _ ⟨j, Finset.mem_coe.mpr (Finset.mem_range.mpr hj), rfl⟩

/-- Upper bound on the number of infinite places: `K_g` is totally complex, so the
number of places is `finrank/2 ≤ 2^g`. -/
theorem Kf_card_le (g : ℕ) :
    Fintype.card (NumberField.InfinitePlace (Kf g)) ≤ 2 ^ g := by
  have h_card : Fintype.card (InfinitePlace (Kf g)) * 2 ≤ Module.finrank ℚ (Kf g) := by
    convert! NumberField.IsTotallyComplex.finrank ( Kf g ) |> le_of_eq using 1;
    · have := NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces ( Kf g );
      convert! NumberField.IsTotallyComplex.finrank ( Kf g ) |> Eq.symm using 1;
      rw [ this, mul_comm, NumberField.IsTotallyComplex.nrRealPlaces_eq_zero ] ; norm_num;
    · convert! NumberField.IsTotallyComplex.finrank ( Kf g ) using 1;
  linarith [ Kf_finrank_le g, pow_succ' 2 g ]

/-- Coordinate formula for the Minkowski map. -/
theorem mink_apply (g : ℕ) (y : 𝓞 (Kf g)) (w : NumberField.InfinitePlace (Kf g)) :
    mink g y w = w.embedding (algebraMap (𝓞 (Kf g)) (Kf g) y) := rfl

/-- The modulus of a Minkowski coordinate is the value of the place. -/
theorem norm_mink_apply (g : ℕ) (y : 𝓞 (Kf g)) (w : NumberField.InfinitePlace (Kf g)) :
    ‖mink g y w‖ = w (algebraMap (𝓞 (Kf g)) (Kf g) y) := by
  rw [mink_apply]; exact NumberField.InfinitePlace.norm_embedding_eq w _

/-- The Minkowski map is injective. -/
theorem mink_injective (g : ℕ) : Function.Injective (mink g) := by
  intro a c h
  have hi : (Classical.arbitrary (NumberField.InfinitePlace (Kf g))).embedding
        (algebraMap (𝓞 (Kf g)) (Kf g) a)
      = (Classical.arbitrary (NumberField.InfinitePlace (Kf g))).embedding
        (algebraMap (𝓞 (Kf g)) (Kf g) c) := by
    have hc := congrFun h (Classical.arbitrary _)
    rwa [mink_apply, mink_apply] at hc
  exact RingOfIntegers.coe_injective
    ((Classical.arbitrary (NumberField.InfinitePlace (Kf g))).embedding.injective hi)

/-- The product of the squares of the place-values of a nonzero element of an ideal `b`
is at least `absNorm b` (since the principal ideal it generates is contained in `b`). -/
theorem absNorm_le_prod_places (g : ℕ) (b : Ideal (𝓞 (Kf g))) (y : 𝓞 (Kf g))
    (hy : y ∈ b) (hy0 : y ≠ 0) :
    (Ideal.absNorm b : ℝ) ≤
      ∏ w : NumberField.InfinitePlace (Kf g),
        (w (algebraMap (𝓞 (Kf g)) (Kf g) y)) ^ 2 := by
  -- Step 1: Rewrite the product as the absolute norm.
  have h1 : ∏ w : NumberField.InfinitePlace (Kf g), (w (algebraMap (𝓞 (Kf g)) (Kf g) y)) ^ 2 = (Ideal.absNorm (Ideal.span {y}) : ℝ) := by
    convert NumberField.InfinitePlace.prod_eq_abs_norm ( algebraMap ( 𝓞 ( Kf g ) ) ( Kf g ) y ) using 1;
    · refine' Finset.prod_congr rfl fun w hw => _;
      have h_complex : w.IsComplex := NumberField.IsTotallyComplex.isComplex w
      rw [ NumberField.InfinitePlace.mult ] ; aesop;
    · have := Algebra.coe_norm_int y; norm_cast at *; aesop;
  refine' h1 ▸ mod_cast Nat.le_of_dvd ( Nat.pos_of_ne_zero _ ) _;
  · simp +decide [ hy0 ];
  · exact Ideal.absNorm_dvd_absNorm_of_le ( Ideal.span_le.mpr ( Set.singleton_subset_iff.mpr hy ) )

/-- **Separation.**  A nonzero element of the ideal `b`, under the Minkowski map, cannot
have all of its coordinates small relative to `ρ √(w μ)` once
`ρ^(2·#places)·(m t)^(2^g) < 1`. -/
theorem mink_sep_aux (g t : ℕ) (b : Ideal (𝓞 (Kf g))) (μ : Kf g) (y : 𝓞 (Kf g))
    (hy : y ∈ b) (hy0 : y ≠ 0)
    (hprod : (∏ w : NumberField.InfinitePlace (Kf g), w μ)
        = (m t : ℝ) ^ 2 ^ g * (Ideal.absNorm b : ℝ))
    (ρ : ℝ)
    (hkey : ρ ^ (2 * Fintype.card (NumberField.InfinitePlace (Kf g)))
        * (m t : ℝ) ^ 2 ^ g < 1) :
    ∃ w : NumberField.InfinitePlace (Kf g),
      ρ * Real.sqrt (w μ) < ‖mink g y w‖ := by
  contrapose! hkey; simp_all +decide;
  -- By combining the results from the contrapositive assumption and the properties of the Minkowski map, we derive a contradiction.
  have h_contradiction : (Ideal.absNorm b : ℝ) ≤ ρ ^ (2 * Fintype.card (InfinitePlace (Kf g))) * (∏ w : InfinitePlace (Kf g), (w μ)) := by
    have h_contradiction : (∏ w : InfinitePlace (Kf g), (w (algebraMap (𝓞 (Kf g)) (Kf g) y)) ^ 2) ≤ (ρ ^ 2) ^ (Fintype.card (InfinitePlace (Kf g))) * (∏ w : InfinitePlace (Kf g), (w μ)) := by
      have h_prod_le : ∀ w : InfinitePlace (Kf g), (w (algebraMap (𝓞 (Kf g)) (Kf g) y)) ^ 2 ≤ (ρ * Real.sqrt (w μ)) ^ 2 := by
        exact fun w => by simpa only [ ← norm_mink_apply ] using pow_le_pow_left₀ ( by positivity ) ( hkey w ) 2;
      convert! Finset.prod_le_prod ( fun _ _ => sq_nonneg _ ) fun w _ => h_prod_le w using 1 ; norm_num [ mul_pow, Finset.prod_mul_distrib ];
    convert! le_trans ( absNorm_le_prod_places g b y hy hy0 ) h_contradiction using 1 ; ring;
  by_cases hb : Ideal.absNorm b = 0 <;> simp_all +decide;
  · rw [ Ideal.absNorm_eq_zero_iff ] at hb ; aesop;
  · nlinarith [ show 0 < ( Ideal.absNorm b : ℝ ) by positivity ]

/-- Real-analysis balancing identity (strict): the chosen radius factor makes the
separation product strictly less than one. -/
theorem rpow_balance_lt {B0 : ℝ} (hB0 : 1 ≤ B0) {d : ℕ} (hd : 1 ≤ d) :
    ((1 / 2 : ℝ) * B0 ^ (-(1 : ℝ) / (2 * (d : ℝ)))) ^ (2 * d) * B0 < 1 := by
  rw [ mul_pow ];
  rw [ ← Real.rpow_natCast _ ( 2 * d ), ← Real.rpow_natCast _ ( 2 * d ), ← Real.rpow_mul ( by positivity ), mul_comm ] ; ring_nf ; norm_num [ show d ≠ 0 by positivity ];
  norm_cast ; norm_num [ mul_comm, Real.rpow_mul ];
  rw [ ← mul_assoc, inv_mul_cancel₀ ( by positivity ), one_mul ] ; exact pow_lt_one₀ ( by positivity ) ( by norm_num ) ( by positivity )

/-- Real-analysis balancing identity (equality) for the box-count upper bound. -/
theorem rpow_balance_le {B0 : ℝ} (hB0 : 1 ≤ B0) {d : ℕ} (hd : 1 ≤ d) :
    (8 / ((1 / 2 : ℝ) * B0 ^ (-(1 : ℝ) / (2 * (d : ℝ))))) ^ (2 * d)
      = (256 : ℝ) ^ d * B0 := by
  ring_nf at *;
  norm_num [ pow_mul', ← Real.rpow_natCast, ← Real.rpow_mul ( by positivity : 0 ≤ B0 ), mul_assoc, mul_comm, mul_left_comm ];
  norm_num [ show d ≠ 0 by linarith ];
  norm_num [ Real.rpow_neg_one ]

/-- Box-count upper bound: with `d ≤ 2^g` places, `256^d · M^(2^g) ≤ (32 √M)^(2·2^g)`. -/
theorem box_count_bound {M : ℝ} (hM : 0 ≤ M) {d g : ℕ} (hd : d ≤ 2 ^ g) :
    (256 : ℝ) ^ d * M ^ 2 ^ g ≤ (32 * Real.sqrt M) ^ (2 * 2 ^ g) := by
  rw [ mul_pow, pow_mul ] ; norm_num [ Real.sq_sqrt hM ] ; ring_nf ;
  rw [ pow_mul', Real.sq_sqrt hM ];
  exact mul_le_mul_of_nonneg_left ( le_trans ( pow_le_pow_left₀ ( by norm_num ) ( by norm_num ) _ ) ( pow_le_pow_right₀ ( by norm_num ) hd ) ) ( by positivity )

/-- [medium given everything above; pure glue]  **Summary of the
construction.**  For all `g t ≥ 1` there is a planar set `Q` with `#Q = n`
points satisfying the three counting estimates that feed the assembly:
`n` is at least `#Z` (first line), at most `(32 √(m t))^(2·2^g)` (second),
and `Q` has at least `#Z · n / (2 · 64^(2^g))` unit-distance pairs (third,
folded with the first into the displayed form).

Sketch: instantiate the geometric core with `ι = InfinitePlace (K_g)`
(`#ι = 2^g` by `IsTotallyComplex.card_infinitePlace` and `Kf_finrank`),
`Λ = mink g '' b`, `r w = √(w μ)`, `ρ = 1/(4·√(m t))`, `i₀` arbitrary, and
`Z' = Z.image (mink g)`.  Hypotheses: `hr` from `μ ≠ 0`; `hinj` since a
field embedding is injective; `hZr` from the place identity and
`norm_embedding_eq`; `hsep`: for `0 ≠ x ∈ b`,
`∏_w w(x)² = |N_{K/ℚ}(x)| ≥ N(b)` (an element of `b` generates a
sub-ideal), while `∏_w (ρ √(w μ))² = ρ^(2^(g+1)) (m t)^(2^g) N(b) < N(b)`,
so not all coordinates can be `≤ ρ r w`. -/
theorem exists_good_pointset (g t : ℕ) (hg : 1 ≤ g) (ht : 1 ≤ t) :
    ∃ (n : ℕ) (Q : Finset (EuclideanSpace ℝ (Fin 2))),
      Q.card = n ∧
      (2 : ℝ) ^ (t * 2 ^ (g - 1)) ≤
        (n : ℝ) * (NumberField.classNumber (Kf g)) * 2 ^ 2 ^ g ∧
      (n : ℝ) ≤ (32 * Real.sqrt (m t)) ^ (2 * 2 ^ g) ∧
      (2 : ℝ) ^ (t * 2 ^ (g - 1)) * (n : ℝ) ≤
        (NumberField.classNumber (Kf g) : ℝ) * 2 ^ 2 ^ g *
          (2 * 64 ^ 2 ^ g) * unitDist Q := by
  classical
  obtain ⟨b, μ, Z, hb, hμ, hZb, hZplace, hprodμ, hZcard⟩ :=
    arithmetic_construction g t hg ht
  -- number of infinite places
  set d : ℕ := Fintype.card (NumberField.InfinitePlace (Kf g)) with hd_def
  have hd_le : d ≤ 2 ^ g := Kf_card_le g
  have hd_pos : 1 ≤ d := Fintype.card_pos
  -- `m t ≥ 1`
  have hM1 : (1 : ℝ) ≤ (m t : ℝ) := by
    have : 1 ≤ m t := Finset.one_le_prod' (fun i _ => (p1_spec i).1.pos)
    exact_mod_cast this
  have hM0 : (0 : ℝ) ≤ (m t : ℝ) := by linarith
  set B0 : ℝ := (m t : ℝ) ^ 2 ^ g with hB0_def
  have hB0 : (1 : ℝ) ≤ B0 := by rw [hB0_def]; exact one_le_pow₀ hM1
  have hB0pos : (0 : ℝ) < B0 := lt_of_lt_of_le one_pos hB0
  set ρ : ℝ := (1 / 2 : ℝ) * B0 ^ (-(1 : ℝ) / (2 * (d : ℝ))) with hρ_def
  have hρ0 : 0 < ρ := by rw [hρ_def]; positivity
  have hρ2 : ρ ≤ 2 := by
    rw [hρ_def]
    have hle1 : B0 ^ (-(1 : ℝ) / (2 * (d : ℝ))) ≤ 1 := by
      apply Real.rpow_le_one_of_one_le_of_nonpos hB0
      apply div_nonpos_of_nonpos_of_nonneg (by norm_num)
      positivity
    nlinarith [Real.rpow_pos_of_pos hB0pos (-(1 : ℝ) / (2 * (d : ℝ)))]
  -- radius vector and distinguished place
  set r : NumberField.InfinitePlace (Kf g) → ℝ := fun w => Real.sqrt (w μ) with hr_def
  have hr : ∀ w, 0 < r w := by
    intro w; rw [hr_def]
    exact Real.sqrt_pos.mpr (NumberField.InfinitePlace.pos_iff.mpr hμ)
  set i0 : NumberField.InfinitePlace (Kf g) := Classical.arbitrary _ with hi0_def
  -- the Minkowski lattice of `b`
  set Λ : AddSubgroup (NumberField.InfinitePlace (Kf g) → ℂ) :=
    AddSubgroup.map ((mink g).toAddMonoidHom) (b.toAddSubgroup) with hΛ_def
  have hΛ_mem : ∀ x, x ∈ Λ ↔ ∃ y ∈ b, mink g y = x := by
    intro x
    rw [hΛ_def, AddSubgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, rfl⟩
  set Z' : Finset (NumberField.InfinitePlace (Kf g) → ℂ) := Z.image (mink g) with hZ'_def
  have hZ'card : Z'.card = Z.card := by
    rw [hZ'_def]; exact Finset.card_image_of_injective Z (mink_injective g)
  -- separation hypothesis
  have hsep : ∀ x ∈ Λ, x ≠ 0 → ∃ i, ρ * r i < ‖x i‖ := by
    intro x hx hx0
    rw [hΛ_mem] at hx
    obtain ⟨y, hyb, rfl⟩ := hx
    have hy0 : y ≠ 0 := by rintro rfl; exact hx0 (by simp)
    have hkey : ρ ^ (2 * d) * (m t : ℝ) ^ 2 ^ g < 1 := by
      rw [hρ_def, ← hB0_def]; exact rpow_balance_lt hB0 hd_pos
    obtain ⟨w, hw⟩ := mink_sep_aux g t b μ y hyb hy0 hprodμ ρ hkey
    exact ⟨w, hw⟩
  -- injectivity at the distinguished place
  have hinj : ∀ x ∈ Λ, x i0 = 0 → x = 0 := by
    intro x hx hx0
    rw [hΛ_mem] at hx
    obtain ⟨y, hyb, rfl⟩ := hx
    rw [mink_apply] at hx0
    have hz : algebraMap (𝓞 (Kf g)) (Kf g) y = 0 :=
      i0.embedding.injective (by rw [hx0]; simp)
    have hy0 : y = 0 := RingOfIntegers.coe_injective (by rw [hz]; simp)
    rw [hy0]; simp
  -- `Z'` lies in `Λ` and is coordinate-exact
  have hZΛ : ∀ z ∈ Z', z ∈ Λ := by
    intro z hz
    rw [hZ'_def, Finset.mem_image] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    rw [hΛ_mem]; exact ⟨y, hZb y hy, rfl⟩
  have hZr : ∀ z ∈ Z', ∀ i, ‖z i‖ = r i := by
    intro z hz i
    rw [hZ'_def, Finset.mem_image] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    have h2 := hZplace y hy i
    have hnn : 0 ≤ i (algebraMap (𝓞 (Kf g)) (Kf g) y) := apply_nonneg i _
    rw [norm_mink_apply]
    show i (algebraMap (𝓞 (Kf g)) (Kf g) y) = Real.sqrt (i μ)
    rw [← h2, Real.sqrt_sq hnn]
  -- run the geometric core
  obtain ⟨n, Q, hQcard, hZn, hnbound, hpairs⟩ :=
    geometric_core i0 r hr Λ hρ0 hρ2 hsep hinj Z' hZΛ hZr
  have hZnR : (Z.card : ℝ) ≤ (n : ℝ) := by
    have h := hZn; rw [hZ'card] at h; exact_mod_cast h
  refine ⟨n, Q, hQcard, ?_, ?_, ?_⟩
  · -- first counting estimate
    calc (2 : ℝ) ^ (t * 2 ^ (g - 1))
          ≤ (Z.card : ℝ) * (NumberField.classNumber (Kf g)) * 2 ^ 2 ^ g := hZcard
      _ ≤ (n : ℝ) * (NumberField.classNumber (Kf g)) * 2 ^ 2 ^ g := by gcongr
  · -- box-count estimate
    have hbox : (8 / ρ) ^ (2 * d) = (256 : ℝ) ^ d * B0 := by
      rw [hρ_def]; exact rpow_balance_le hB0 hd_pos
    calc (n : ℝ) ≤ (8 / ρ) ^ (2 * d) := hnbound
      _ = (256 : ℝ) ^ d * B0 := hbox
      _ = (256 : ℝ) ^ d * (m t : ℝ) ^ 2 ^ g := by rw [hB0_def]
      _ ≤ (32 * Real.sqrt (m t)) ^ (2 * 2 ^ g) := box_count_bound hM0 hd_le
  · -- unit-distance estimate
    have hpairs' : (Z.card : ℝ) * n ≤ 2 * 64 ^ d * unitDist Q := by
      rw [← hZ'card]; exact hpairs
    calc (2 : ℝ) ^ (t * 2 ^ (g - 1)) * (n : ℝ)
          ≤ ((Z.card : ℝ) * (NumberField.classNumber (Kf g)) * 2 ^ 2 ^ g) * (n : ℝ) := by
            gcongr
      _ = (NumberField.classNumber (Kf g) : ℝ) * 2 ^ 2 ^ g * ((Z.card : ℝ) * (n : ℝ)) := by
            ring
      _ ≤ (NumberField.classNumber (Kf g) : ℝ) * 2 ^ 2 ^ g * (2 * 64 ^ d * unitDist Q) := by
            gcongr
      _ ≤ (NumberField.classNumber (Kf g) : ℝ) * 2 ^ 2 ^ g * (2 * 64 ^ 2 ^ g * unitDist Q) := by
            gcongr
            norm_num
      _ = (NumberField.classNumber (Kf g) : ℝ) * 2 ^ 2 ^ g * (2 * 64 ^ 2 ^ g) * unitDist Q := by
            ring

end Erdos
