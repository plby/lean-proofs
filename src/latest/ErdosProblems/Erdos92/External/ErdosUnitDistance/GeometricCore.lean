/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ErdosProblems.Erdos92.External.ErdosUnitDistance.Counting

/-!
# The geometric core

Grid-pigeonhole packing and doubling bounds for additive subgroups of
`ι → ℂ` in polydisc boxes, and the translation argument producing many
unit distances after projection to one coordinate.  No measure theory.
-/

open scoped Classical

namespace Erdos

/-! ## Geometric core

Everything in this section is about an additive subgroup `Λ ≤ (ι → ℂ)`
(`ι` finite: in the application, the set of infinite places, with
`Fintype.card ι = 2^g`), a "radius vector" `r : ι → ℝ`, and the polydisc
boxes `box r c`.  All bounds are by grid pigeonhole: each coordinate disc
`{‖w‖ ≤ 2 * r i}` is partitioned into at most `(4 * 2/ε)²` half-open square
cells of diameter at most `ε * r i`, so the polydisc splits into at most
`(8/ε)^(2·#ι)` cells, on each of which all pairwise coordinate differences
have modulus at most `ε * r i`. -/

section GeometricCore

variable {ι : Type} [Fintype ι]

/-- The closed polydisc box of polyradius `c • r` in `ι → ℂ`. -/
def box (r : ι → ℝ) (c : ℝ) : Set (ι → ℂ) :=
  {x | ∀ i, ‖x i‖ ≤ c * r i}

omit [Fintype ι] in
theorem box_mono {r : ι → ℝ} (hr : ∀ i, 0 ≤ r i) {c c' : ℝ} (h : c ≤ c') :
    box r c ⊆ box r c' :=
  fun x hx i => (hx i).trans (by have := hr i; nlinarith)

private lemma cell_index_mem {c ε : ℝ} (hε : 0 < ε) {ri : ℝ} (hri : 0 < ri)
    {t : ℝ} (ht : |t| ≤ c * ri) :
    ⌊(t + c * ri) / (ε * ri / Real.sqrt 2)⌋ ∈
      Finset.Icc (0 : ℤ) ((⌊2 * Real.sqrt 2 * c / ε⌋₊ : ℕ) : ℤ) := by
  refine' Finset.mem_Icc.mpr ⟨ Int.floor_nonneg.mpr _, Int.le_of_lt_add_one ( Int.floor_lt.mpr _ ) ⟩;
  · exact div_nonneg ( by linarith [ abs_le.mp ht ] ) ( by positivity );
  · rw [ div_lt_iff₀ ] <;> norm_num;
    · rw [ ← mul_div_assoc, lt_div_iff₀ ] <;> nlinarith [ Nat.lt_floor_add_one ( 2 * Real.sqrt 2 * c / ε ), Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two, mul_pos hε hri, mul_div_cancel₀ ( 2 * Real.sqrt 2 * c ) hε.ne', abs_le.mp ht ];
    · positivity

/-
Helper: two real coordinates with the same cell index differ by less than the
cell side `ε*ri/√2`.
-/
private lemma cell_index_diff {c ε : ℝ} (hε : 0 < ε) {ri : ℝ} (hri : 0 < ri)
    {a b : ℝ}
    (h : ⌊(a + c * ri) / (ε * ri / Real.sqrt 2)⌋
        = ⌊(b + c * ri) / (ε * ri / Real.sqrt 2)⌋) :
    |a - b| < ε * ri / Real.sqrt 2 := by
  rw [ Int.floor_eq_iff ] at h;
  rw [ abs_lt ] ; constructor <;> nlinarith [ Int.floor_le ( ( b + c * ri ) / ( ε * ri / Real.sqrt 2 ) ), Int.lt_floor_add_one ( ( b + c * ri ) / ( ε * ri / Real.sqrt 2 ) ), show 0 < ε * ri / Real.sqrt 2 by positivity, mul_div_cancel₀ ( a + c * ri ) ( show ε * ri / Real.sqrt 2 ≠ 0 by positivity ), mul_div_cancel₀ ( b + c * ri ) ( show ε * ri / Real.sqrt 2 ≠ 0 by positivity ) ] ;

/-
Helper: a complex number whose real and imaginary parts are each `< d` in
absolute value has norm `< d * √2`.
-/
private lemma norm_lt_of_re_im_bound {z : ℂ} {d : ℝ} (hd : 0 ≤ d)
    (hre : |z.re| < d) (him : |z.im| < d) : ‖z‖ < d * Real.sqrt 2 := by
  rw [ ← Real.sqrt_sq ( show 0 ≤ d by assumption ) ];
  rw [ ← Real.sqrt_mul <| by positivity ] ; refine' Real.sqrt_lt_sqrt _ _;
  · exact Complex.normSq_nonneg _;
  · nlinarith [ abs_lt.mp hre, abs_lt.mp him, Complex.normSq_apply z ]

/-
Helper: the per-axis cell count `⌊2√2 c/ε⌋₊ + 1` is at most `4c/ε`
(using `ε ≤ c`, i.e. `c/ε ≥ 1`).
-/
private lemma cellCount_le {c ε : ℝ} (hε : 0 < ε) (hεc : ε ≤ c) :
    ((⌊2 * Real.sqrt 2 * c / ε⌋₊ : ℕ) : ℝ) + 1 ≤ 4 * c / ε := by
  by_contra h_contra;
  exact h_contra <| by have := Nat.floor_le ( show 0 ≤ 2 * Real.sqrt 2 * c / ε by exact div_nonneg ( mul_nonneg ( mul_nonneg zero_le_two <| Real.sqrt_nonneg _ ) <| by linarith ) <| by linarith ) ; rw [ le_div_iff₀ <| by linarith ] at *; nlinarith [ Real.sqrt_nonneg 2, Real.sq_sqrt zero_le_two, mul_div_cancel₀ ( 2 * Real.sqrt 2 * c ) <| ne_of_gt hε ] ;

/-
[medium] **Grid pigeonhole.**  A subset of the polydisc `box r c` whose
distinct elements are `ε`-separated in some coordinate (relative to `r`)
is finite, of cardinality at most `(4 * c / ε) ^ (2 * #ι)`.
Sketch: partition each coordinate disc of radius `c * r i` into half-open
square cells of side `ε * r i / √2`; there are at most
`⌈2√2 * c/ε⌉² ≤ (4c/ε)²` cells per coordinate (using `ε ≤ c`).  Map each
point to its tuple of cell indices: two points with the same tuple differ
by at most `ε * r i` in every coordinate, contradicting separation; so the
map into `ι → (Fin M × Fin M)` is injective.
-/
/-- [medium] **Grid pigeonhole.**  A subset of the polydisc `box r c` whose
distinct elements are `ε`-separated in some coordinate (relative to `r`)
is finite, of cardinality at most `(4 * c / ε) ^ (2 * #ι)`.
Sketch: partition each coordinate disc of radius `c * r i` into half-open
square cells of side `ε * r i / √2`; there are at most
`⌈2√2 * c/ε⌉² ≤ (4c/ε)²` cells per coordinate (using `ε ≤ c`).  Map each
point to its tuple of cell indices: two points with the same tuple differ
by at most `ε * r i` in every coordinate, contradicting separation; so the
map into `ι → (Fin M × Fin M)` is injective. -/
theorem finite_and_card_le_of_separated (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    {c ε : ℝ} (hε : 0 < ε) (hεc : ε ≤ c)
    {S : Set (ι → ℂ)} (hS : S ⊆ box r c)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ∃ i, ε * r i < ‖x i - y i‖) :
    S.Finite ∧ (S.ncard : ℝ) ≤ (4 * c / ε) ^ (2 * Fintype.card ι) := by
  -- Let's define the cell map and the finite codomain.
  set δ : ι → ℝ := fun i => ε * r i / Real.sqrt 2
  set K : ℤ := (⌊2 * Real.sqrt 2 * c / ε⌋₊ : ℤ)
  set T : Finset (ι → ℤ × ℤ) := Fintype.piFinset (fun _ : ι => (Finset.Icc (0:ℤ) K) ×ˢ (Finset.Icc (0:ℤ) K));
  -- Define the cell map `g` and show that it maps `S` into `T`.
  set g : (ι → ℂ) → (ι → ℤ × ℤ) := fun x i => (⌊((x i).re + c * r i) / δ i⌋, ⌊((x i).im + c * r i) / δ i⌋)
  have hg : ∀ x ∈ S, g x ∈ T := by
    intro x hx;
    simp +zetaDelta at *;
    intro i; exact ⟨ ⟨ cell_index_mem hε ( hr i ) ( show |( x i |> Complex.re )| ≤ c * r i from by simpa using Complex.abs_re_le_norm ( x i ) |> le_trans <| hS hx i ) |> Finset.mem_Icc.mp |> And.left, cell_index_mem hε ( hr i ) ( show |( x i |> Complex.re )| ≤ c * r i from by simpa using Complex.abs_re_le_norm ( x i ) |> le_trans <| hS hx i ) |> Finset.mem_Icc.mp |> And.right ⟩, ⟨ cell_index_mem hε ( hr i ) ( show |( x i |> Complex.im )| ≤ c * r i from by simpa using Complex.abs_im_le_norm ( x i ) |> le_trans <| hS hx i ) |> Finset.mem_Icc.mp |> And.left, cell_index_mem hε ( hr i ) ( show |( x i |> Complex.im )| ≤ c * r i from by simpa using Complex.abs_im_le_norm ( x i ) |> le_trans <| hS hx i ) |> Finset.mem_Icc.mp |> And.right ⟩ ⟩ ;
  -- Show that `g` is injective on `S`.
  have hg_inj : Set.InjOn g S := by
    intros x hx y hy hxy
    by_contra hxy_ne
    obtain ⟨i, hi⟩ := hsep x hx y hy hxy_ne
    have h_diff : ‖x i - y i‖ < δ i * Real.sqrt 2 := by
      apply norm_lt_of_re_im_bound;
      · exact div_nonneg ( mul_nonneg hε.le ( le_of_lt ( hr i ) ) ) ( Real.sqrt_nonneg _ );
      · convert! cell_index_diff hε ( hr i ) _ using 1;
        exacts [ c, by simpa using! congr_arg Prod.fst ( congr_fun hxy i ) ];
      · convert! cell_index_diff hε ( hr i ) _ using 1;
        exacts [ c, by simpa using! congr_arg Prod.snd ( congr_fun hxy i ) ];
    rw [ div_mul_cancel₀ _ ( by positivity ) ] at h_diff ; linarith;
  -- Conclude that `S` is finite and its cardinality is bounded by `T.card`.
  have h_finite : S.Finite := by
    exact Set.Finite.of_finite_image ( Set.Finite.subset ( Finset.finite_toSet T ) ( Set.image_subset_iff.mpr hg ) ) hg_inj
  have h_card : (S.ncard : ℝ) ≤ T.card := by
    have := Set.InjOn.ncard_image hg_inj;
    exact_mod_cast this ▸ Set.ncard_le_ncard ( show g '' S ⊆ T from Set.image_subset_iff.mpr hg ) |> le_trans <| by simp +decide [ Set.ncard_eq_toFinset_card' ] ;
  refine ⟨ h_finite, h_card.trans ?_ ⟩;
  convert pow_le_pow_left₀ ( by positivity ) ( cellCount_le hε hεc ) ( 2 * Fintype.card ι ) using 1 ; norm_num [ Finset.card_univ, pow_mul ];
  erw [ Fintype.card_piFinset ] ; norm_num [ pow_mul ];
  norm_cast ; ring_nf!
  rw [ pow_mul' ] ; norm_cast ; ring_nf!

/-- [easy given `finite_and_card_le_of_separated`] **Lattice points in the
box.**  If every nonzero element of `Λ` escapes the small polydisc
`box r ρ`, then `Λ ∩ box r 2` is finite of cardinality at most
`(8/ρ)^(2·#ι)`.  Sketch: differences of distinct elements of `Λ ∩ box r 2`
are nonzero elements of `Λ`, so the separation hypothesis of the grid
pigeonhole holds with `c = 2`, `ε = ρ`. -/
theorem lattice_inter_box_finite_card (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (Λ : AddSubgroup (ι → ℂ)) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ2 : ρ ≤ 2)
    (hsep : ∀ x ∈ Λ, x ≠ 0 → ∃ i, ρ * r i < ‖x i‖) :
    ((Λ : Set (ι → ℂ)) ∩ box r 2).Finite ∧
      (((Λ : Set (ι → ℂ)) ∩ box r 2).ncard : ℝ) ≤
        (8 / ρ) ^ (2 * Fintype.card ι) := by
  convert finite_and_card_le_of_separated r hr ( show 0 < ρ by linarith ) ( show ρ ≤ 2 by linarith ) ( show ( Λ : Set ( ι → ℂ ) ) ∩ box r 2 ⊆ box r 2 by exact Set.inter_subset_right ) _ using 1;
  · norm_num;
  · exact fun x hx y hy hxy => hsep ( x - y ) ( Λ.sub_mem hx.1 hy.1 ) ( sub_ne_zero_of_ne hxy ) |> fun ⟨ i, hi ⟩ => ⟨ i, by simpa using hi ⟩

/-- [medium] **Doubling.**  Counting lattice points in the double box loses
at most `64^#ι` against the unit box.  Sketch: partition `box r 2` into at
most `(4·2/1)² = 64` cells per coordinate, of coordinatewise diameter at
most `1 * r i`.  If a cell meets `Λ ∩ box r 2`, fix one such point `x₀`;
every other lattice point `y` of the same cell has `y - x₀ ∈ Λ ∩ box r 1`,
so the cell contains at most `#(Λ ∩ box r 1)` lattice points.  Sum over
cells. -/
theorem ncard_box_two_le_doubling (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (Λ : AddSubgroup (ι → ℂ))
    (hfin : ((Λ : Set (ι → ℂ)) ∩ box r 2).Finite) :
    (((Λ : Set (ι → ℂ)) ∩ box r 2).ncard : ℝ) ≤
      64 ^ Fintype.card ι * ((Λ : Set (ι → ℂ)) ∩ box r 1).ncard := by
  -- Let `A := (Λ : Set _) ∩ box r 2` and `B := (Λ : Set _) ∩ box r 1`.
  set A : Set (ι → ℂ) := Λ ∩ box r 2
  set B : Set (ι → ℂ) := Λ ∩ box r 1;
  obtain ⟨sA, hsA⟩ : ∃ sA : Finset (ι → ℂ), A = sA := by
    exact ⟨ hfin.toFinset, hfin.coe_toFinset.symm ⟩
  obtain ⟨sB, hsB⟩ : ∃ sB : Finset (ι → ℂ), B = sB := by
    have hBfin : B.Finite := by
      exact hfin.subset fun x hx => ⟨ hx.1, fun i => le_trans ( hx.2 i ) ( mul_le_mul_of_nonneg_right ( by norm_num ) ( le_of_lt ( hr i ) ) ) ⟩
    exact ⟨hBfin.toFinset, by simp⟩
  simp_all +decide [ Set.ncard_eq_toFinset_card' ];
  -- Apply `Finset.card_le_mul_card_image sA f (B.ncard)` to get `sA.card ≤ B.ncard * (sA.image f).card`.
  have h_card_le_mul_card_image : sA.card ≤ sB.card * (sA.image (fun x => fun i => (⌊(x i).re / (2 * r i / 3)⌋, ⌊(x i).im / (2 * r i / 3)⌋))).card := by
    have h_card_le_mul_card_image : ∀ b ∈ sA.image (fun x => fun i => (⌊(x i).re / (2 * r i / 3)⌋, ⌊(x i).im / (2 * r i / 3)⌋)), (sA.filter (fun a => (fun x i => (⌊(x i).re / (2 * r i / 3)⌋, ⌊(x i).im / (2 * r i / 3)⌋)) a = b)).card ≤ sB.card := by
      intro b hb
      obtain ⟨x₀, hx₀⟩ : ∃ x₀ ∈ sA, (fun x i => (⌊(x i).re / (2 * r i / 3)⌋, ⌊(x i).im / (2 * r i / 3)⌋)) x₀ = b := by
        aesop
      have h_fiber : ∀ y ∈ sA, (fun x i => (⌊(x i).re / (2 * r i / 3)⌋, ⌊(x i).im / (2 * r i / 3)⌋)) y = b → y - x₀ ∈ sB := by
        intro y hy hyb
        have h_diff : ∀ i, ‖(y i - x₀ i)‖ ≤ r i := by
          intro i
          have h_diff_re : |(y i).re - (x₀ i).re| ≤ 2 * r i / 3 := by
            have h_diff_re : ⌊(y i).re / (2 * r i / 3)⌋ = ⌊(x₀ i).re / (2 * r i / 3)⌋ := by
              replace hyb := congr_fun hyb i; replace hx₀ := congr_fun hx₀.2 i; aesop;
            rw [ Int.floor_eq_iff ] at h_diff_re;
            rw [ abs_le ] ; constructor <;> nlinarith [ hr i, Int.floor_le ( ( x₀ i |> Complex.re ) / ( 2 * r i / 3 ) ), Int.lt_floor_add_one ( ( x₀ i |> Complex.re ) / ( 2 * r i / 3 ) ), mul_div_cancel₀ ( ( y i |> Complex.re ) ) ( by linarith [ hr i ] : ( 2 * r i / 3 ) ≠ 0 ), mul_div_cancel₀ ( ( x₀ i |> Complex.re ) ) ( by linarith [ hr i ] : ( 2 * r i / 3 ) ≠ 0 ) ] ;
          have h_diff_im : |(y i).im - (x₀ i).im| ≤ 2 * r i / 3 := by
            have h_diff_im : ⌊(y i).im / (2 * r i / 3)⌋ = ⌊(x₀ i).im / (2 * r i / 3)⌋ := by
              replace hyb := congr_fun hyb i; replace hx₀ := congr_fun hx₀.2 i; aesop;
            rw [ Int.floor_eq_iff ] at h_diff_im;
            rw [ abs_le ];
            constructor <;> nlinarith [ hr i, Int.floor_le ( ( x₀ i |> Complex.im ) / ( 2 * r i / 3 ) ), Int.lt_floor_add_one ( ( x₀ i |> Complex.im ) / ( 2 * r i / 3 ) ), mul_div_cancel₀ ( ( y i |> Complex.im ) ) ( by linarith [ hr i ] : ( 2 * r i / 3 ) ≠ 0 ), mul_div_cancel₀ ( ( x₀ i |> Complex.im ) ) ( by linarith [ hr i ] : ( 2 * r i / 3 ) ≠ 0 ) ];
          norm_num [ Complex.normSq, Complex.norm_def ] at *;
          exact Real.sqrt_le_iff.mpr ⟨ by linarith [ hr i ], by nlinarith [ abs_le.mp h_diff_re, abs_le.mp h_diff_im ] ⟩;
        exact hsB.subset ⟨ Λ.sub_mem ( hsA.symm.subset hy |>.1 ) ( hsA.symm.subset hx₀.1 |>.1 ), fun i => by simpa using h_diff i ⟩
      have h_fiber_card : (sA.filter (fun a => (fun x i => (⌊(x i).re / (2 * r i / 3)⌋, ⌊(x i).im / (2 * r i / 3)⌋)) a = b)).card ≤ (sB.image (fun y => y + x₀)).card := by
        exact Finset.card_le_card fun x hx => Finset.mem_image.mpr ⟨ x - x₀, h_fiber x ( Finset.mem_filter.mp hx |>.1 ) ( Finset.mem_filter.mp hx |>.2 ), by simp +decide ⟩ ;
      exact h_fiber_card.trans (Finset.card_image_le);
    exact Finset.card_le_mul_card_image sA sB.card h_card_le_mul_card_image
  -- The image of `sA` under `f` is a subset of `T := Fintype.piFinset (fun _ : ι => (Finset.Icc (-3:ℤ) 3) ×ˢ (Finset.Icc (-3:ℤ) 3))`.
  have h_image_subset_T : sA.image (fun x => fun i => (⌊(x i).re / (2 * r i / 3)⌋, ⌊(x i).im / (2 * r i / 3)⌋)) ⊆ Fintype.piFinset (fun _ : ι => (Finset.Icc (-3:ℤ) 3) ×ˢ (Finset.Icc (-3:ℤ) 3)) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    simp [Fintype.piFinset];
    refine' ⟨ fun i _ => ( ⌊ ( y i |> Complex.re ) / ( 2 * r i / 3 ) ⌋, ⌊ ( y i |> Complex.im ) / ( 2 * r i / 3 ) ⌋ ), _, by rfl ⟩;
    intro i
    have h_bound : |(y i).re| ≤ 2 * r i ∧ |(y i).im| ≤ 2 * r i := by
      exact ⟨ le_trans ( Complex.abs_re_le_norm _ ) ( hsA.symm.subset hy |>.2 i ), le_trans ( Complex.abs_im_le_norm _ ) ( hsA.symm.subset hy |>.2 i ) ⟩;
    exact ⟨ ⟨ Int.le_floor.2 <| by norm_num; nlinarith [ abs_le.mp h_bound.1, hr i, mul_div_cancel₀ ( ( y i |> Complex.re ) ) ( by linarith [ hr i ] : ( 2 * r i / 3 ) ≠ 0 ) ], Int.le_of_lt_add_one <| Int.floor_lt.2 <| by norm_num; nlinarith [ abs_le.mp h_bound.1, hr i, mul_div_cancel₀ ( ( y i |> Complex.re ) ) ( by linarith [ hr i ] : ( 2 * r i / 3 ) ≠ 0 ) ] ⟩, ⟨ Int.le_floor.2 <| by norm_num; nlinarith [ abs_le.mp h_bound.2, hr i, mul_div_cancel₀ ( ( y i |> Complex.im ) ) ( by linarith [ hr i ] : ( 2 * r i / 3 ) ≠ 0 ) ], Int.le_of_lt_add_one <| Int.floor_lt.2 <| by norm_num; nlinarith [ abs_le.mp h_bound.2, hr i, mul_div_cancel₀ ( ( y i |> Complex.im ) ) ( by linarith [ hr i ] : ( 2 * r i / 3 ) ≠ 0 ) ] ⟩ ⟩;
  -- The cardinality of `T` is `64 ^ Fintype.card ι`.
  have h_card_T : (Fintype.piFinset (fun _ : ι => (Finset.Icc (-3:ℤ) 3) ×ˢ (Finset.Icc (-3:ℤ) 3))).card ≤ 64 ^ Fintype.card ι := by
    simp +decide [ Fintype.piFinset ];
    gcongr ; norm_num;
  exact_mod_cast h_card_le_mul_card_image.trans ( Nat.mul_le_mul_left _ ( Finset.card_le_card h_image_subset_T |> le_trans <| h_card_T ) ) |> le_trans <| by ring_nf; norm_num;

variable (i₀ : ι)

/-- Projection of a polydisc point to the distinguished coordinate `i₀`,
rescaled so that the repeated distance becomes exactly `1`. -/
noncomputable def proj (r : ι → ℝ) (i₀ : ι) (x : ι → ℂ) : ℂ :=
  x i₀ / (r i₀ : ℂ)

/-- [medium] **Translation produces unit distances.**  Let `Z` be a finite
set of elements of `Λ` whose coordinates have modulus *exactly* `r i`.
Then the projection `P ⊆ ℂ` of `Λ ∩ box r 2` to the (rescaled) `i₀`-th
coordinate satisfies `#P = #(Λ ∩ box r 2)` and has at least
`#Z · #(Λ ∩ box r 1)` ordered unit-distance pairs.
Sketch: (1) `proj` is injective on `Λ` by `hinj` (two preimages differ by
an element of `Λ` vanishing at `i₀`), giving the cardinality statement.
(2) For `a ∈ Λ ∩ box r 1` and `z ∈ Z`, the translate `a + z` lies in
`Λ ∩ box r 2` (triangle inequality coordinatewise), and
`dist (proj a) (proj (a + z)) = ‖z i₀‖ / r i₀ = 1`.  The assignment
`(a, z) ↦ (proj a, proj (a + z))` is injective into ordered pairs (recover
`a` from the first component by injectivity, then `z i₀`, then `z`), and
each image pair is a distinct-points pair at distance one. -/
theorem le_unitPairsC_of_translates (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (Λ : AddSubgroup (ι → ℂ))
    (hinj : ∀ x ∈ Λ, x i₀ = 0 → x = 0)
    (hfin : ((Λ : Set (ι → ℂ)) ∩ box r 2).Finite)
    (Z : Finset (ι → ℂ)) (hZΛ : ∀ z ∈ Z, z ∈ Λ)
    (hZr : ∀ z ∈ Z, ∀ i, ‖z i‖ = r i) :
    (hfin.toFinset.image (proj r i₀)).card = ((Λ : Set (ι → ℂ)) ∩ box r 2).ncard ∧
      Z.card * ((Λ : Set (ι → ℂ)) ∩ box r 1).ncard ≤
        unitPairsC (hfin.toFinset.image (proj r i₀)) := by
  refine' ⟨ _, _ ⟩;
  · rw [ Finset.card_image_of_injOn, ← Set.ncard_coe_finset, hfin.coe_toFinset ];
    intro x hx y hy; specialize hinj ( x - y ) ; simp_all +decide [ sub_eq_zero ] ;
    simp_all +decide [ proj, div_eq_iff, ne_of_gt ( hr i₀ ) ];
    exact fun h => hinj ( Λ.sub_mem hx.1 hy.1 ) h;
  · refine' le_trans _ ( Finset.card_mono _ );
    rotate_left;
    exact Finset.image ( fun p : ( ι → ℂ ) × ( ι → ℂ ) => ( p.2 i₀ / r i₀, ( p.2 + p.1 ) i₀ / r i₀ ) ) ( Z ×ˢ ( hfin.toFinset.filter fun x => ∀ i, ‖x i‖ ≤ r i ) );
    · intro; simp +decide [ dist_eq_norm ] ;
      rintro x y hx hy hxy hy' rfl; simp_all +decide [ proj, box ] ;
      refine' ⟨ ⟨ ⟨ y, ⟨ hy, hxy ⟩, rfl ⟩, ⟨ y + x, ⟨ Λ.add_mem hy ( hZΛ x hx ), fun i => _ ⟩, _ ⟩, _ ⟩, _ ⟩ <;> simp_all +decide [ add_div, ne_of_gt ];
      · exact le_trans ( norm_add_le _ _ ) ( by linarith [ hy' i, hZr x hx i ] );
      · exact fun h => by have := hZr x hx i₀; norm_num [ h ] at this; linarith [ hr i₀ ] ;
      · rw [ abs_of_pos ( hr i₀ ), div_self ( ne_of_gt ( hr i₀ ) ) ];
    · rw [ Finset.card_image_of_injOn ];
      · simp +zetaDelta at *;
        gcongr;
        rw [ ← Set.ncard_coe_finset ];
        fapply Set.ncard_le_ncard;
        · simp +contextual [ Set.subset_def, box ];
          exact fun x hx hx' i => le_trans ( hx' i ) ( le_mul_of_one_le_left ( le_of_lt ( hr i ) ) ( by norm_num ) );
        · exact hfin.toFinset.finite_toSet.subset fun x hx => by aesop;
      · intro p hp q hq h; simp_all +decide [ div_eq_iff, ne_of_gt ( hr _ ) ] ;
        have h_eq : p.1 = q.1 := by
          specialize hinj ( p.1 - q.1 ) ; simp_all +decide [ sub_eq_iff_eq_add ] ;
          exact hinj ( by simpa using Λ.sub_mem ( hZΛ _ hp.1 ) ( hZΛ _ hq.1 ) ) ( by aesop );
        specialize hinj ( p.2 - q.2 ) ; simp_all +decide [ sub_eq_iff_eq_add ];
        exact Prod.ext h_eq ( hinj ( Λ.sub_mem hp.1.1 hq.2.1.1 ) )

/-- [medium, glue] **The geometric core, assembled.**  From a separated
lattice `Λ`, a coordinate-exact set `Z ⊆ Λ`, and an injective coordinate,
produce a planar point set `Q` with `#Q = n` points where
`#Z ≤ n ≤ (8/ρ)^(2·#ι)` and `#Z · n ≤ 2 · 64^#ι · unitDist Q`.
Sketch: combine `lattice_inter_box_finite_card` (finiteness and the upper
bound for `n`), `le_unitPairsC_of_translates`, and
`ncard_box_two_le_doubling`, then transport to the Euclidean plane with
`exists_euclidean_copy`.  For `#Z ≤ n` note `Z ⊆ Λ ∩ box r 2` since
`‖z i‖ = r i ≤ 2 r i`, and `Z` maps injectively into the box (it is inside
it). -/
theorem geometric_core (r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (Λ : AddSubgroup (ι → ℂ)) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ2 : ρ ≤ 2)
    (hsep : ∀ x ∈ Λ, x ≠ 0 → ∃ i, ρ * r i < ‖x i‖)
    (hinj : ∀ x ∈ Λ, x i₀ = 0 → x = 0)
    (Z : Finset (ι → ℂ)) (hZΛ : ∀ z ∈ Z, z ∈ Λ)
    (hZr : ∀ z ∈ Z, ∀ i, ‖z i‖ = r i) :
    ∃ (n : ℕ) (Q : Finset (EuclideanSpace ℝ (Fin 2))),
      Q.card = n ∧
      Z.card ≤ n ∧
      (n : ℝ) ≤ (8 / ρ) ^ (2 * Fintype.card ι) ∧
      (Z.card : ℝ) * n ≤ 2 * 64 ^ Fintype.card ι * unitDist Q := by
  obtain ⟨hfin, hupper⟩ := lattice_inter_box_finite_card r hr Λ hρ0 hρ2 hsep;
  obtain ⟨hcard, hpairs⟩ := le_unitPairsC_of_translates i₀ r hr Λ hinj hfin Z hZΛ hZr;
  obtain ⟨Q, hQcard, hQunit⟩ := exists_euclidean_copy (hfin.toFinset.image (proj r i₀));
  refine' ⟨ Q.card, Q, rfl, _, _, _ ⟩ <;> norm_cast at * <;> simp_all +decide [ mul_comm ];
  · refine' le_trans _ ( Set.ncard_le_ncard ( show ( ↑Z : Set ( ι → ℂ ) ) ⊆ ( Λ : Set ( ι → ℂ ) ) ∩ box r 2 from _ ) hfin );
    · rw [ Set.ncard_coe_finset ];
    · exact fun x hx => ⟨ hZΛ x hx, fun i => by simpa [ hZr x hx i ] using by nlinarith [ hr i ] ⟩;
  · have hdbl := ncard_box_two_le_doubling r hr Λ hfin; norm_cast at *; simp_all +decide ;
    nlinarith [ pow_pos ( by norm_num : ( 0 : ℕ ) < 64 ) ( Fintype.card ι ) ]

end GeometricCore

end Erdos
