/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.DenseBox

/-!
# CFP Corollary 2.17

This module assembles the reducedness-free dense-grid theorem, finite
lattice-quotient saturation, and the adapted-HNF sandwich.  It is separated
from `DenseBox` so the substantial dense-box development is compiled once
before the final source-facing certificate is elaborated.
-/

namespace Erdos186.CFP

open scoped BigOperators Pointwise
open Module LatticeBasis

noncomputable section

/-- CFP Corollary 2.17(1), with a single uniform constant chosen before the
box and the dense set.  No reducedness assumption is present: the missing
residue classes are supplied by the finite quotient of the generated
lattice by the rectangular lattice produced by the coordinate blocks. -/
theorem exists_corollary217Certificate
    (d : ℕ) (hd : 0 < d) (cNum cDen : ℕ)
    (hcNum : 0 < cNum) (hc : cNum ≤ cDen) :
    ∃ C widthThreshold : ℕ, 0 < C ∧
      ∀ (Q : AxisBox d) (B : Finset (BoxPoint d)),
        widthThreshold ≤ Q.minWidth →
        (0 : BoxPoint d) ∈ B →
        B ⊆ Q.carrier →
        cNum * Q.volume ≤ cDen * B.card →
        ∃ cert : Corollary217Certificate Q B, cert.constant = C := by
  classical
  have hcDen : 0 < cDen := lt_of_lt_of_le hcNum hc
  let V := 4 * cDen
  let R := V ^ d
  let Hmax := (1 + d * (d * V)) ^ d
  let M := Hmax * d * V
  let L := 16 * cDen * (M + R)
  let ellGrid := d * (V * L)
  let C := ellGrid + R + 2 * M + 1
  let widthThreshold := 24 * cDen * cDen
  have hVpos : 0 < V := by dsimp [V]; positivity
  have hRpos : 0 < R := by dsimp [R]; positivity
  have hHmaxpos : 0 < Hmax := by dsimp [Hmax]; positivity
  have hMpos : 0 < M := by dsimp [M]; positivity
  have hsumpos : 0 < M + R := Nat.add_pos_left hMpos _
  have hLpos : 0 < L := by
    dsimp [L]
    exact Nat.mul_pos (by positivity) hsumpos
  have hCpos : 0 < C := by dsimp [C]; omega
  refine ⟨C, widthThreshold, hCpos, ?_⟩
  intro Q B hwidthMin hzeroB hBQ hdensity
  have hzeroQ : (0 : BoxPoint d) ∈ Q.carrier := hBQ hzeroB
  have hwidth (i : Fin d) : 8 * cDen ≤ Q.widths i := by
    have hwide : widthThreshold ≤ Q.widths i :=
      hwidthMin.trans (Q.minWidth_le hd i)
    dsimp [widthThreshold] at hwide
    nlinarith
  have hLevLarge (i : Fin d) :
      2 * (((Q.widths i - 1) - 1 +
          (Q.widths i / (2 * cDen) - 2) - 1) /
        (Q.widths i / (2 * cDen) - 2)) ≤ L := by
    simpa [L] using corollary217_lev_large hcDen hsumpos Q
      (fun j ↦ by simpa [widthThreshold] using
        hwidthMin.trans (Q.minWidth_le hd j)) i
  let family : Fin ellGrid → Finset (BoxPoint d) := fun _ ↦ B
  obtain ⟨grid⟩ := exists_denseGridCertificate_of_numerics Q family
    cNum cDen hcNum hcDen (V := V) (L := L)
    (fun _ ↦ hBQ) (fun _ ↦ hdensity) rfl (by simp [ellGrid])
    hwidth (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hLpos)) hLevLarge
  have hgridSum : heterogeneousSumset family =
      iteratedSumset (fun _ ↦ B) ellGrid := by
    rw [heterogeneousSumset, List.sum_ofFn, iteratedSumset,
      ← Fin.sum_univ_eq_sum_range]
  have hgridSubset := grid.grid_subset
  rw [hgridSum] at hgridSubset
  have hlength (i : Fin d) : 1 ≤ grid.lengths i := by
    have hb4 : 4 ≤ Q.widths i / (2 * cDen) := by
      apply (Nat.le_div_iff_mul_le (by positivity : 0 < 2 * cDen)).2
      convert hwidth i using 1 <;> ring
    rw [grid.lengths_eq i]
    exact (Nat.one_le_iff_ne_zero).2
      (Nat.ne_of_gt (Nat.mul_pos hLpos (by omega)))
  let Gamma := generatedSublattice B
  have hrect : rectangularSubgroup grid.periods ≤ Gamma :=
    rectangularSubgroup_le_generated_of_grid_subset_iteratedSumset
      B ellGrid grid.periods grid.lengths hlength grid.translate
        hgridSubset
  let r := (rectangularSubgroup grid.periods).relIndex Gamma
  obtain ⟨hrprod, hres⟩ :=
    rectangularResidueCompleteOn_generated_iteratedSumset
      grid.periods grid.period_pos B hzeroB hrect
  have hprodR : (∏ i, grid.periods i) ≤ R := by
    calc
      (∏ i, grid.periods i) ≤ ∏ _i : Fin d, V :=
        Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _)
          (fun i _ ↦ grid.period_le i)
      _ = V ^ d := by simp
      _ = R := rfl
  have hrR : r ≤ R := hrprod.trans hprodR
  let w : Fin d → ℕ := fun i ↦ Q.widths i - 1
  obtain ⟨σ, b, H, hH, hreverse, hforward⟩ :=
    exists_basisProgression_sandwich_symmetricBox
      grid.periods w grid.period_pos Gamma hrect
  have hHle : H ≤ Hmax := by
    rw [hH]
    simpa [Hmax] using inverseCoefficientConstantNat_le_uniform
      grid.periods grid.period_le σ
  let radius : Fin d → ℕ := fun i ↦ H * w (σ i)
  let P : GAP d d := AdaptedHNF.centeredBasisGAP b radius
  have hHpos : 0 < H := by
    rw [hH]
    simp [AdaptedHNF.inverseCoefficientConstantNat]
  have hradiusLower (i : Fin d) : Q.minWidth - 1 ≤ radius i := by
    have hmin : Q.minWidth - 1 ≤ Q.widths (σ i) - 1 :=
      Nat.sub_le_sub_right (Q.minWidth_le hd (σ i)) 1
    calc
      Q.minWidth - 1 ≤ Q.widths (σ i) - 1 := hmin
      _ = 1 * (Q.widths (σ i) - 1) := by simp
      _ ≤ H * (Q.widths (σ i) - 1) :=
        Nat.mul_le_mul_right _ hHpos
      _ = radius i := rfl
  have hcarrier : P.carrier = basisProgression b radius :=
    centeredBasisGAP_carrier_eq_basisProgression b radius
  have hQsym : Q.carrier ⊆ (symmetricAxisBox w).carrier := by
    simpa [w] using carrier_subset_symmetricAxisBox_width_sub_one Q hzeroQ
  have hbox : ∀ x ∈ Q.carrier, x ∈ Gamma → x ∈ P.carrier := by
    intro x hxQ hxGamma
    rw [hcarrier]
    exact hreverse ⟨x, hxGamma⟩ (hQsym hxQ)
  have hPsim : P.carrier ⊆
      (symmetricAxisBox (fun i ↦ M * w i)).carrier := by
    rw [hcarrier]
    intro x hx
    have hx' := mem_symmetricAxisBox_iff.mp (hforward hx)
    rw [mem_symmetricAxisBox_iff]
    intro i
    apply (hx' i).trans
    exact_mod_cast Nat.mul_le_mul_right (w i)
      (Nat.mul_le_mul (Nat.mul_le_mul hHle (Nat.le_refl d))
        (grid.period_le i))
  have hBbound : ∀ j < r, ∀ x ∈ (fun _ : ℕ ↦ B) j, ∀ i,
      -((w i : ℕ) : ℤ) ≤ x i ∧ x i ≤ (w i : ℤ) := by
    intro _j _hj x hx i
    exact abs_le.mp ((mem_symmetricAxisBox_iff.mp (hQsym (hBQ hx))) i)
  have hRbound0 : CoordinateBound
      (iteratedSumset (fun _ ↦ B) r) (fun i ↦ r * w i) :=
    coordinateBound_iteratedSumset (fun _ ↦ B) w hBbound
  have hRbound : CoordinateBound
      (iteratedSumset (fun _ ↦ B) r) (fun i ↦ R * w i) := by
    exact hRbound0.mono (fun i ↦ Nat.mul_le_mul_right (w i) hrR)
  have hPbound : CoordinateBound P.carrier (fun i ↦ M * w i) := by
    intro x hx i
    exact abs_le.mp ((mem_symmetricAxisBox_iff.mp (hPsim hx)) i)
  have hmargin (i : Fin d) :
      (M + R) * w i ≤ grid.lengths i / 2 := by
    rw [grid.lengths_eq i]
    simpa [w, L] using corollary217_grid_margin hcDen Q hwidth i
  have hleft (i : Fin d) :
      M * w i + R * w i ≤
        grid.periods i * (grid.lengths i / 2) := by
    calc
      M * w i + R * w i = (M + R) * w i := by ring
      _ ≤ grid.lengths i / 2 := hmargin i
      _ ≤ grid.periods i * (grid.lengths i / 2) :=
        Nat.le_mul_of_pos_left _ (grid.period_pos i)
  have hright (i : Fin d) :
      grid.periods i * (grid.lengths i / 2) + M * w i + R * w i ≤
        grid.periods i * grid.lengths i := by
    have htail := hleft i
    calc
      grid.periods i * (grid.lengths i / 2) + M * w i + R * w i =
          grid.periods i * (grid.lengths i / 2) +
            (M * w i + R * w i) := by omega
      _ ≤ grid.periods i * (grid.lengths i / 2) +
          grid.periods i * (grid.lengths i / 2) := Nat.add_le_add_left htail _
      _ = grid.periods i * (2 * (grid.lengths i / 2)) := by ring
      _ ≤ grid.periods i * grid.lengths i :=
        Nat.mul_le_mul_left _ (by omega)
  have hPGamma : (P.carrier : Set (BoxPoint d)) ⊆ Gamma := by
    intro x hx
    rw [hcarrier] at hx
    obtain ⟨a, _ha, rfl⟩ := Finset.mem_image.mp hx
    exact (∑ i, a i • b i : Gamma).property
  obtain ⟨shift, hcovered0⟩ := grid_add_residues_contains_lattice_set
    Gamma grid.periods grid.lengths (fun i ↦ M * w i)
      (fun i ↦ R * w i) grid.period_pos hrect hleft hright
      grid.translate hgridSubset hres hRbound hPGamma hPbound
  have hcoveredShort : Elementary.translate shift P.carrier ⊆
      iteratedSumset (fun _ ↦ B) (ellGrid + r) := by
    rw [iteratedSumset_const_add, ← elementary_sumset_eq_pointwise_add]
    exact hcovered0
  have hshortC : ellGrid + r ≤ C := by dsimp [C]; omega
  have hcovered : Elementary.translate shift P.carrier ⊆
      iteratedSumset (fun _ ↦ B) C :=
    hcoveredShort.trans
      (iteratedSumset_const_mono_index B hzeroB hshortC)
  have h2MC : 2 * M ≤ C := by dsimp [C]; omega
  have hgeom : P.carrier ⊆
      Elementary.translate
        (fun i ↦ -((M * (Q.widths i - 1) : ℕ) : ℤ))
        (Q.dilate C).carrier := by
    exact hPsim.trans (by simpa [w] using
      symmetricAxisBox_subset_translate_dilate Q h2MC)
  have hcentered : P.Centered radius := ⟨rfl, rfl⟩
  have hproper : P.Proper := AdaptedHNF.centeredBasisGAP_proper b radius
  have hzeroP : (0 : BoxPoint d) ∈ P.carrier := hcentered.zero_mem_carrier
  have hBP : (B : Set (BoxPoint d)) ⊆ P.carrier := by
    intro x hx
    exact hbox x (hBQ hx) (subset_generatedSublattice B hx)
  have hgenerated : generatedSublattice P.carrier = Gamma := by
    apply le_antisymm
    · exact (AddSubgroup.closure_le Gamma).2 hPGamma
    · exact AddSubgroup.closure_mono hBP
  have hoffset : P.offset ∈ Gamma := by
    let y : Gamma := -∑ i, (radius i : ℤ) • b i
    have hy : ((y : Gamma) : BoxPoint d) = P.offset := by
      funext j
      simp [y, P, AdaptedHNF.centeredBasisGAP]
    rw [← hy]
    exact y.property
  have hsteps (i : Fin d) : P.steps i ∈ Gamma := by
    simpa [P, AdaptedHNF.centeredBasisGAP] using (b i).property
  refine ⟨{
    constant := C
    constant_pos := hCpos
    sigma := σ
    basis := b
    radius := radius
    radius_lower := hradiusLower
    progression := P
    progression_eq := rfl
    centered := hcentered
    proper := hproper
    zero_mem := hzeroP
    box_lattice_subset := hbox
    geometricTranslate :=
      fun i ↦ -((M * (Q.widths i - 1) : ℕ) : ℤ)
    geometric_bound := hgeom
    sumTranslate := shift
    sum_covered := hcovered
    generated_carrier_eq := hgenerated
    offset_mem_generated := hoffset
    steps_mem_generated := hsteps }, rfl⟩

end

end Erdos186.CFP
