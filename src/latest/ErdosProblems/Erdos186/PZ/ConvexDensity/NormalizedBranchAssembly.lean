/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.ConvexDensity.GraphBranchVolume
import ErdosProblems.Erdos186.PZ.ConvexDensity.GraphRadiusNumerics
import ErdosProblems.Erdos186.PZ.ConvexDensity.BranchAssembly
import ErdosProblems.Erdos186.PZ.ConvexDensity.RoundedBranchNumerics
import ErdosProblems.Erdos186.PZ.ConvexDensity.ShellNumerics

/-! # Quantitative assembly constants for the normalized graph branch -/

open Set MeasureTheory

namespace Erdos186.PZ.ConvexDensity

set_option autoImplicit false
noncomputable section

/-- A single dimension-dependent constant which dominates the thickening
costs in both graph-occupancy branches. -/
def normalizedGraphVolumeCoefficient (n : ℕ) (outer : ℝ) : ℝ :=
  2 * (3 : ℝ) ^ n * (2 : ℝ) ^ n * outer *
    (32 * ((n : ℝ) + 1) ^ (4 : ℕ) + 2 * (1 + 4 * (n : ℝ)))

theorem normalizedGraphVolumeCoefficient_pos {n : ℕ} (hn : 0 < n)
    {outer : ℝ} (houter : 0 < outer) :
    0 < normalizedGraphVolumeCoefficient n outer := by
  simp only [normalizedGraphVolumeCoefficient]
  positivity

def normalizedBranchInnerVolume (n : ℕ) : ℝ :=
  (((n + 1 + 1 : ℕ) : ℝ)⁻¹) ^ (n + 1)

theorem normalizedBranchInnerVolume_pos (n : ℕ) :
    0 < normalizedBranchInnerVolume n := by
  simp only [normalizedBranchInnerVolume]
  positivity

/-- The coefficient used by the branch closure includes the reciprocal
ambient-volume lower bound needed to turn absolute chart volume into relative
volume. -/
def normalizedBranchVolumeCoefficient (n : ℕ) (outer : ℝ) : ℝ :=
  normalizedGraphVolumeCoefficient n outer / normalizedBranchInnerVolume n

theorem normalizedBranchVolumeCoefficient_pos {n : ℕ} (hn : 0 < n)
    {outer : ℝ} (houter : 0 < outer) :
    0 < normalizedBranchVolumeCoefficient n outer :=
  div_pos (normalizedGraphVolumeCoefficient_pos hn houter)
    (normalizedBranchInnerVolume_pos n)

theorem etaLow_branch_mul_inner {n : ℕ} {outer q K s L : ℝ} :
    etaLow (n + 1) (normalizedBranchVolumeCoefficient n outer) q K s L *
        normalizedBranchInnerVolume n =
      etaLow (n + 1) (normalizedGraphVolumeCoefficient n outer) q K s L := by
  simp only [etaLow, normalizedBranchVolumeCoefficient]
  have hc : normalizedBranchInnerVolume n ≠ 0 :=
    (normalizedBranchInnerVolume_pos n).ne'
  field_simp

theorem etaHigh_branch_mul_inner {n : ℕ} {outer q s : ℝ} :
    etaHigh (n + 1) (normalizedBranchVolumeCoefficient n outer) q s *
        normalizedBranchInnerVolume n =
      etaHigh (n + 1) (normalizedGraphVolumeCoefficient n outer) q s := by
  simp only [etaHigh, normalizedBranchVolumeCoefficient]
  have hc : normalizedBranchInnerVolume n ≠ 0 :=
    (normalizedBranchInnerVolume_pos n).ne'
  field_simp

/-- The cap, first shell, and integral-to-real grid comparison retain this
fixed multiple of the model captured fraction. -/
def normalizedCaptureCoefficient (n : ℕ) (outer : ℝ) : ℝ :=
  capFractionCoefficient n outer / (4 * (2 : ℝ) ^ n)

theorem normalizedCaptureCoefficient_pos {n : ℕ} (hn : 0 < n)
    {outer : ℝ} (houter : 0 < outer) :
    0 < normalizedCaptureCoefficient n outer := by
  rw [normalizedCaptureCoefficient]
  exact div_pos (capFractionCoefficient_pos hn houter) (by positivity)

theorem boundaryDimension_succ (n : ℕ) :
    boundaryDimension (n + 1) = n := by
  simp [boundaryDimension]

theorem densityExponent_eq_alpha_add (d : ℕ) (epsilon : ℝ) :
    densityExponent d epsilon = alpha d + epsilon := by
  rfl

theorem half_le_relativeGraphOccupancy_mul
    {n m capCard Kabs L cells : ℕ}
    (hm : 0 < m) (hcap : 0 < capCard) (hK : 0 < Kabs)
    (hL : 0 < L) (hcells : cells ≤ m ^ n)
    (hmass : capCard ≤ 2 * L * Kabs * cells) :
    (1 / 2 : ℝ) ≤ relativeGraphOccupancy n m capCard Kabs * L := by
  have hmR : (0 : ℝ) < (m : ℝ) ^ n := by positivity
  have hcapR : (0 : ℝ) < capCard := by exact_mod_cast hcap
  have hmassR : (capCard : ℝ) ≤
      2 * (L : ℝ) * Kabs * cells := by exact_mod_cast hmass
  have hcellsR : (cells : ℝ) ≤ (m : ℝ) ^ n := by
    exact_mod_cast hcells
  have hmass' : capCard ≤ 2 * L * Kabs * m ^ n :=
    hmass.trans (Nat.mul_le_mul_left (2 * L * Kabs) hcells)
  rw [relativeGraphOccupancy]
  field_simp
  exact_mod_cast (by simpa [mul_assoc, mul_left_comm, mul_comm] using hmass')

/-- Rounding `s` up to an integral grid of size at most `2s` costs exactly
the displayed factor `2^n` in the captured fraction. -/
theorem capturedFraction_realScale_le_integral
    {n : ℕ} {outer q K s L m : ℝ}
    (hn : 0 < n) (houter : 0 < outer) (hq : 0 < q)
    (hK : 0 < K) (hs : 0 < s) (hL : 0 < L)
    (hm : 0 < m) (hmUpper : m ≤ 2 * s) :
    capturedFraction (n + 1) (normalizedCaptureCoefficient n outer)
        q K s L ≤
      (capFractionCoefficient n outer / 4) * q ^ n * K /
        (m ^ n * L) := by
  have hc : 0 < capFractionCoefficient n outer :=
    capFractionCoefficient_pos hn houter
  have hmPow : m ^ n ≤ (2 * s) ^ n :=
    pow_le_pow_left₀ hm.le hmUpper n
  rw [capturedFraction, boundaryDimension_succ,
    normalizedCaptureCoefficient]
  rw [Real.rpow_natCast, Real.rpow_natCast]
  rw [mul_pow] at hmPow
  have hmul := mul_le_mul_of_nonneg_left hmPow
    (show 0 ≤ capFractionCoefficient n outer * q ^ n * K * L by positivity)
  field_simp
  nlinarith

/-- The low graph slab in boundary dimension at least two has the uniform
thickness bound consumed by `graphThickeningCost_le_etaLow`. -/
theorem lowGraphEpsilon_le
    {n m capCard Kabs L cells : ℕ}
    (hn : 2 ≤ n) (hm : 0 < m) (hcap : 0 < capCard)
    (hK : 0 < Kabs) (hL : 0 < L) (hcells : 0 < cells)
    (hmass : capCard ≤ 2 * L * Kabs * cells) :
    4 * (((n : ℝ) + 1) ^ (4 : ℕ)) * (m : ℝ) ^ (n - 2) /
          ((1 / 2 : ℝ) * cells) ≤
      32 * (((n : ℝ) + 1) ^ (4 : ℕ)) *
        relativeGraphOccupancy n m capCard Kabs * L /
          (m : ℝ) ^ (2 : ℕ) := by
  have hinv := inv_cells_le_relativeGraphOccupancy (n := n)
    hm hcap hK hL hcells hmass
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hpowSplit : (m : ℝ) ^ n =
      (m : ℝ) ^ (n - 2) * (m : ℝ) ^ (2 : ℕ) := by
    rw [← pow_add]
    congr
    omega
  have hfactor : 0 ≤
      8 * (((n : ℝ) + 1) ^ (4 : ℕ)) * (m : ℝ) ^ (n - 2) := by
    positivity
  have hstep := mul_le_mul_of_nonneg_left hinv hfactor
  rw [hpowSplit] at hstep
  calc
    4 * (((n : ℝ) + 1) ^ (4 : ℕ)) * (m : ℝ) ^ (n - 2) /
          ((1 / 2 : ℝ) * cells) =
        (8 * (((n : ℝ) + 1) ^ (4 : ℕ)) *
          (m : ℝ) ^ (n - 2)) * (1 / (cells : ℝ)) := by ring
    _ ≤ (8 * (((n : ℝ) + 1) ^ (4 : ℕ)) *
          (m : ℝ) ^ (n - 2)) *
        (2 * (L : ℝ) * relativeGraphOccupancy n m capCard Kabs /
          ((m : ℝ) ^ (n - 2) * (m : ℝ) ^ (2 : ℕ))) := hstep
    _ = 16 * (((n : ℝ) + 1) ^ (4 : ℕ)) *
        relativeGraphOccupancy n m capCard Kabs * L /
          (m : ℝ) ^ (2 : ℕ) := by
      have hpowPos : 0 < (m : ℝ) ^ (n - 2) := pow_pos hmR _
      field_simp
      ring
    _ ≤ 32 * (((n : ℝ) + 1) ^ (4 : ℕ)) *
        relativeGraphOccupancy n m capCard Kabs * L /
          (m : ℝ) ^ (2 : ℕ) := by
      have hrel : 0 ≤ relativeGraphOccupancy n m capCard Kabs :=
        (relativeGraphOccupancy_pos hm hcap hK).le
      have hLR : (0 : ℝ) ≤ L := by positivity
      gcongr
      nlinarith

/-- Planar low-slab analogue of `lowGraphEpsilon_le`. -/
theorem lowGraphEpsilon_le_twoDimensional
    {m capCard Kabs L cells : ℕ}
    (hm : 0 < m) (hcap : 0 < capCard)
    (hK : 0 < Kabs) (hL : 0 < L) (hcells : 0 < cells)
    (hmass : capCard ≤ 2 * L * Kabs * cells) :
    2 / ((1 / 2 : ℝ) * (m : ℝ) * cells) ≤
      32 * (((1 : ℝ) + 1) ^ (4 : ℕ)) *
        relativeGraphOccupancy 1 m capCard Kabs * L /
          (m : ℝ) ^ (2 : ℕ) := by
  have hinv := inv_cells_le_relativeGraphOccupancy (n := 1)
    hm hcap hK hL hcells hmass
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hstep := mul_le_mul_of_nonneg_left hinv (show (0 : ℝ) ≤ 4 / m by positivity)
  calc
    2 / ((1 / 2 : ℝ) * (m : ℝ) * cells) =
        (4 / (m : ℝ)) * (1 / (cells : ℝ)) := by ring
    _ ≤ (4 / (m : ℝ)) *
        (2 * (L : ℝ) * relativeGraphOccupancy 1 m capCard Kabs /
          (m : ℝ)) := by simpa using hstep
    _ ≤ 32 * (((1 : ℝ) + 1) ^ (4 : ℕ)) *
        relativeGraphOccupancy 1 m capCard Kabs * L /
          (m : ℝ) ^ (2 : ℕ) := by
      rw [show ((1 : ℝ) + 1) ^ (4 : ℕ) = 16 by norm_num]
      have hrel : 0 < relativeGraphOccupancy 1 m capCard Kabs :=
        relativeGraphOccupancy_pos hm hcap hK
      field_simp
      nlinarith

theorem highGraphEpsilon_le {n : ℕ} {m : ℕ} {s : ℝ}
    (hm : 0 < m) (hs : 0 < s) (hsm : s ≤ (m : ℝ)) :
    (n : ℝ) / ((1 / 2 : ℝ) * (m : ℝ)) ≤ 2 * (n : ℝ) / s := by
  have hnR : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  calc
    (n : ℝ) / ((1 / 2 : ℝ) * (m : ℝ)) =
        2 * (n : ℝ) / (m : ℝ) := by field_simp
    _ ≤ 2 * (n : ℝ) / s :=
      div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hnR) hs hsm

/-- Final geometric constructor once a single normalized graph slab has
been selected.  It packages the centered Householder chart, its anisotropic
fibre-radius estimate, the exact Jacobian cancellation, and transport back
to the original convex hull. -/
theorem convexDensityOutput_of_normalizedGraphSlab
    {n : ℕ} {epsilon delta eta mesh rho q outer r : ℝ}
    {Omega : Set (EuclideanPoint (n + 1))}
    {X : Finset (EuclideanPoint (n + 1))}
    {J₀ : Finset (Fin (n + 1) → ℕ)}
    {S : Finset {k // k ∈ J₀}}
    {witness : {k // k ∈ J₀} → EuclideanPoint (n + 1)}
    {W : Set (EuclideanPoint n × ℝ)}
    (hn : 0 < n) (hq : 0 < q) (houter : 0 < outer)
    (center direction : EuclideanPoint (n + 1))
    (hEta : eta ∈ Set.Icc delta (delta ^ tau epsilon))
    (heta : 0 ≤ eta)
    (hOmega : IsConvexBody Omega)
    (hXOmega : (X : Set (EuclideanPoint (n + 1))) ⊆ Omega)
    (hinner : normalizedInnerCube (n + 1) ⊆ Omega)
    (hW : Convex ℝ W)
    (hwitness : ∀ i ∈ S,
      lastCoordinateCLE n
        (centeredGraphWindowAffineEquiv center direction q outer
          hq.ne' houter.ne' (witness i)) ∈ W)
    (hphysicalNear : ∀ i ∈ S, ∀ z ∈ gridAssignmentFiberFinset X mesh i.1,
      dist z (witness i) ≤ 4 * rho)
    (hradius : 4 * rho * ((2 * q)⁻¹ + outer⁻¹) ≤ r)
    (hnormalizedVolume :
      volume (minkowskiClosedBall W r) *
          ENNReal.ofReal ((2 * q) ^ n * outer) ≤
        ENNReal.ofReal eta * ENNReal.ofReal (normalizedBranchInnerVolume n))
    (hCard : eta ^ densityExponent (n + 1) epsilon * (X.card : ℝ) ≤
      (∑ i ∈ S, (gridAssignmentFiberFinset X mesh i.1).card : ℕ)) :
    ConvexDensityOutput epsilon (tau epsilon) delta Omega X := by
  let H := centeredHouseholderEquiv center direction
  let e := centeredGraphWindowAffineEquiv center direction q outer
    hq.ne' houter.ne'
  have hYX : ∀ i ∈ S, gridAssignmentFiberFinset X mesh i.1 ⊆ X := by
    intro i _hi
    exact gridAssignmentFiberFinset_subset X mesh i.1
  have hdisjoint : (S : Set {k // k ∈ J₀}).PairwiseDisjoint
      (fun i ↦ gridAssignmentFiberFinset X mesh i.1) := by
    intro i _hi j _hj hij
    apply Finset.disjoint_left.mpr
    intro z hzi hzj
    have heq : i.1 = j.1 :=
      (mem_gridAssignmentFiberFinset_iff.mp hzi).2.symm.trans
        (mem_gridAssignmentFiberFinset_iff.mp hzj).2
    exact hij (Subtype.ext heq)
  have hnear : ∀ i ∈ S, ∀ z ∈ gridAssignmentFiberFinset X mesh i.1,
      dist (e z) (e (witness i)) ≤ r := by
    intro i hi z hz
    have hgraph := dist_graphWindowAffineEquiv_le hq houter
      (H z) (H (witness i))
    have hiso : dist (H z) (H (witness i)) = dist z (witness i) := by
      exact dist_centeredHouseholderEquiv center direction z (witness i)
    have hlip : 0 ≤ (2 * q)⁻¹ + outer⁻¹ := by positivity
    calc
      dist (e z) (e (witness i)) ≤
          ((2 * q)⁻¹ + outer⁻¹) * dist (H z) (H (witness i)) := by
        simpa [e, H, centeredGraphWindowAffineEquiv] using hgraph
      _ = ((2 * q)⁻¹ + outer⁻¹) * dist z (witness i) := by rw [hiso]
      _ ≤ ((2 * q)⁻¹ + outer⁻¹) * (4 * rho) := by
        gcongr
        exact hphysicalNear i hi z hz
      _ = 4 * rho * ((2 * q)⁻¹ + outer⁻¹) := by ring
      _ ≤ r := hradius
  have hHvolume : volume (H '' Omega) = volume Omega :=
    volume_affineImage H Omega
  have hinnerVolume : ENNReal.ofReal (normalizedBranchInnerVolume n) ≤
      volume (H '' Omega) := by
    rw [hHvolume]
    simpa [normalizedBranchInnerVolume, ← add_assoc] using
      (normalizedInnerCube_volume_le hinner)
  have hvolume : volume (minkowskiClosedBall W r) ≤
      ENNReal.ofReal eta * volume (e '' Omega) := by
    have h := graphWindow_volume_le_chart_body hq houter
      heta (normalizedBranchInnerVolume_pos n).le
      hinnerVolume hnormalizedVolume
    simpa [e, H, centeredGraphWindowAffineEquiv, Set.image_image] using h
  exact convexDensityOutput_of_affineChart_disjointFibers e hEta hOmega
    hXOmega hYX hdisjoint hW hwitness hnear hvolume hCard

/-- Low-occupancy slabs have the volume scale used by `etaLow`.  The
hypotheses are stated after the two rounding comparisons, so this lemma is
pure ordered-field bookkeeping. -/
theorem graphThickeningCost_le_etaLow
    {n : ℕ} {q outer m s epsilon r slope K L : ℝ}
    (hn : 0 < n) (hq : 0 < q) (houter : 0 < outer)
    (hs : 0 < s) (hsm : s ≤ m)
    (hK : 0 < K) (hL : 0 < L) (hhalf : (1 / 2 : ℝ) ≤ K * L)
    (hepsilon : 0 ≤ epsilon)
    (hepsilonUpper : epsilon ≤
      32 * ((n : ℝ) + 1) ^ (4 : ℕ) * K * L / s ^ (2 : ℕ))
    (hr : 0 ≤ r) (hrUpper : r ≤ 1 / s ^ (2 : ℕ))
    (hslope : 0 ≤ slope) (hslopeUpper : slope ≤ 4) :
    graphThickeningCost n q outer m epsilon r slope ≤
      etaLow (n + 1) (normalizedGraphVolumeCoefficient n outer)
        q K s L := by
  have hm : 0 < m := hs.trans_le hsm
  let A : ℝ := 32 * ((n : ℝ) + 1) ^ (4 : ℕ)
  let B : ℝ := 2 * (1 + 4 * (n : ℝ))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hKL : 0 < K * L := mul_pos hK hL
  have hsSq : 0 < s ^ (2 : ℕ) := pow_pos hs _
  have hheight :
      epsilon + r * (1 + (n : ℝ) * slope) ≤
        (A + B) * K * L / s ^ (2 : ℕ) := by
    have hslopeTerm : 1 + (n : ℝ) * slope ≤
        1 + 4 * (n : ℝ) := by
      nlinarith [show (0 : ℝ) ≤ (n : ℝ) by positivity]
    have hslopeTermNonneg : 0 ≤ 1 + (n : ℝ) * slope := by positivity
    have hrterm : r * (1 + (n : ℝ) * slope) ≤
        (1 / s ^ (2 : ℕ)) * (1 + 4 * (n : ℝ)) :=
      (mul_le_mul hrUpper hslopeTerm hslopeTermNonneg
        (by positivity)).trans_eq (by rfl)
    have hBKL : 1 + 4 * (n : ℝ) ≤ B * K * L := by
      dsimp only [B]
      nlinarith [show (0 : ℝ) ≤ (n : ℝ) by positivity]
    have hrterm' : r * (1 + (n : ℝ) * slope) ≤
        B * K * L / s ^ (2 : ℕ) := by
      calc
        r * (1 + (n : ℝ) * slope) ≤
            (1 / s ^ (2 : ℕ)) * (1 + 4 * (n : ℝ)) := hrterm
        _ ≤ (1 / s ^ (2 : ℕ)) * (B * K * L) := by gcongr
        _ = B * K * L / s ^ (2 : ℕ) := by ring
    dsimp only [A] at hepsilonUpper ⊢
    calc
      epsilon + r * (1 + (n : ℝ) * slope) ≤
          A * K * L / s ^ (2 : ℕ) +
            B * K * L / s ^ (2 : ℕ) :=
        add_le_add hepsilonUpper hrterm'
      _ = (A + B) * K * L / s ^ (2 : ℕ) := by ring
  have hbase : (3 / m) ^ n ≤ (3 / s) ^ n := by
    apply pow_le_pow_left₀ (by positivity)
    exact div_le_div_of_nonneg_left (by norm_num) hs hsm
  have hqpow : 0 ≤ (2 * q) ^ n * outer := by positivity
  have hcost : graphThickeningCost n q outer m epsilon r slope ≤
      (3 / s) ^ n *
        (2 * ((A + B) * K * L / s ^ (2 : ℕ))) *
        ((2 * q) ^ n * outer) := by
    rw [graphThickeningCost]
    gcongr
  calc
    graphThickeningCost n q outer m epsilon r slope ≤
        (3 / s) ^ n *
          (2 * ((A + B) * K * L / s ^ (2 : ℕ))) *
          ((2 * q) ^ n * outer) := hcost
    _ = etaLow (n + 1) (normalizedGraphVolumeCoefficient n outer)
          q K s L := by
      rw [etaLow, boundaryDimension_succ]
      rw [show ((n + 1 : ℕ) : ℝ) + 1 = (n : ℝ) + 2 by
          push_cast
          ring,
        Real.rpow_add hs, Real.rpow_natCast, Real.rpow_two]
      have hsne : s ≠ 0 := hs.ne'
      simp only [normalizedGraphVolumeCoefficient]
      dsimp only [A, B]
      field_simp
      simp [Real.rpow_natCast]
      rw [div_pow, mul_pow]
      field_simp

/-- The constant-slab branch has the `etaHigh` volume scale. -/
theorem graphThickeningCost_le_etaHigh
    {n : ℕ} {q outer m s epsilon r : ℝ}
    (hn : 0 < n) (hq : 0 < q) (houter : 0 < outer)
    (hs : 0 < s) (hsOne : 1 ≤ s) (hsm : s ≤ m)
    (hepsilon : 0 ≤ epsilon)
    (hepsilonUpper : epsilon ≤ 2 * (n : ℝ) / s)
    (hr : 0 ≤ r) (hrUpper : r ≤ 1 / s ^ (2 : ℕ)) :
    graphThickeningCost n q outer m epsilon r 0 ≤
      etaHigh (n + 1) (normalizedGraphVolumeCoefficient n outer) q s := by
  have hm : 0 < m := hs.trans_le hsm
  have hns : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hrs : r ≤ 1 / s := by
    calc
      r ≤ 1 / s ^ (2 : ℕ) := hrUpper
      _ ≤ 1 / s := by
        rw [div_le_div_iff_of_pos_left zero_lt_one (pow_pos hs 2) hs]
        nlinarith
  have hheight : epsilon + r * (1 + (n : ℝ) * 0) ≤
      (2 * (n : ℝ) + 1) / s := by
    norm_num
    calc
      epsilon + r ≤ 2 * (n : ℝ) / s + 1 / s :=
        add_le_add hepsilonUpper hrs
      _ = (2 * (n : ℝ) + 1) / s := by ring
  have hbase : (3 / m) ^ n ≤ (3 / s) ^ n := by
    apply pow_le_pow_left₀ (by positivity)
    exact div_le_div_of_nonneg_left (by norm_num) hs hsm
  have hcost : graphThickeningCost n q outer m epsilon r 0 ≤
      (3 / s) ^ n * (2 * ((2 * (n : ℝ) + 1) / s)) *
        ((2 * q) ^ n * outer) := by
    rw [graphThickeningCost]
    gcongr
  have hcoeff : 2 * (n : ℝ) + 1 ≤
      32 * ((n : ℝ) + 1) ^ (4 : ℕ) +
        2 * (1 + 4 * (n : ℝ)) := by
    nlinarith [sq_nonneg ((n : ℝ) + 1),
      sq_nonneg (((n : ℝ) + 1) ^ (2 : ℕ))]
  calc
    graphThickeningCost n q outer m epsilon r 0 ≤
        (3 / s) ^ n * (2 * ((2 * (n : ℝ) + 1) / s)) *
          ((2 * q) ^ n * outer) := hcost
    _ ≤ (3 / s) ^ n *
          (2 * ((32 * ((n : ℝ) + 1) ^ (4 : ℕ) +
            2 * (1 + 4 * (n : ℝ))) / s)) *
          ((2 * q) ^ n * outer) := by gcongr
    _ = etaHigh (n + 1) (normalizedGraphVolumeCoefficient n outer) q s := by
      rw [etaHigh, boundaryDimension_succ]
      rw [show ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 by norm_num,
        Real.rpow_add hs, Real.rpow_natCast, Real.rpow_one]
      have hsne : s ≠ 0 := hs.ne'
      simp only [normalizedGraphVolumeCoefficient]
      field_simp
      simp [Real.rpow_natCast]
      rw [div_pow, mul_pow]
      field_simp

end
end Erdos186.PZ.ConvexDensity
