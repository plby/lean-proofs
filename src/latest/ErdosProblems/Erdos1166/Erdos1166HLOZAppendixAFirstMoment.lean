import ErdosProblems.Erdos1166.Erdos1166HLOZPropositionA7
import ErdosProblems.Erdos1166.Erdos1166HLOZTerminalNegBin

/-!
# The Appendix-A first-moment profile partition

This file formalizes the finite calculation in HLOZ Lemmas A.4 and A.6.
The coordinates of a path are the upcrossing counts
`(m₂, ..., mₙ)`.  Conditional on `m_ℓ = b`, the next coordinate has the
success-`1 / 2` negative-binomial mass `halfNegBinMass b b'`.  The different
transition used at the top scale is retained explicitly: its success
probability is `3 log n / (1 + 3 log n)`, and its number of failures is
restricted to the literal interval in the source.

Consequently the module contains no random-walk or Harnack assumption.  Its
last theorems consume the trajectory-sum conclusion of Proposition A.7 and
show exactly how it gives the first-moment profile mass.  To pass from that
finite Markov-chain calculation to annular simple-random-walk events one still
needs precisely the entry, exit, and embedded-chain comparison estimates in
HLOZ Lemma A.6.
-/

open scoped BigOperators

namespace Erdos1166.HLOZAppendixAFirstMoment

open Erdos1166.HLOZPropositionA7
open Filter

/-- The literal profile corridor `|m_ℓ - 2ℓ²| ≤ ℓ^(1+δ)` on a
finite interval of scales. -/
def ProfileCorridor (delta : ℝ) (start : ℕ) {N : ℕ} (q : NatPath N) : Prop :=
  ∀ i : Fin (N + 1),
    |centeredDeviation (start + (i : ℕ)) (q i)| ≤
      (Erdos1166.HLOZLemmaA8.corridorRadius delta (start + (i : ℕ)) : ℤ)

private theorem coordinate_le_of_profileCorridor {ell m R : ℕ}
    (h : |centeredDeviation ell m| ≤ (R : ℤ)) :
    m ≤ 2 * ell ^ 2 + R := by
  have h' : centeredDeviation ell m ≤ (R : ℤ) := (le_abs_self _).trans h
  unfold centeredDeviation at h'
  have hz : (m : ℤ) ≤ 2 * (ell : ℤ) ^ 2 + (R : ℤ) := by omega
  exact_mod_cast hz

/-- A finite box known to contain every corridor profile. -/
noncomputable def profileBox (delta : ℝ) (start N : ℕ) :
    Finset (NatPath N) :=
  Fintype.piFinset fun i ↦
    Finset.Icc 0
      (2 * (start + (i : ℕ)) ^ 2 +
        Erdos1166.HLOZLemmaA8.corridorRadius delta (start + (i : ℕ)))

/-- The finite family `M_n(δ)` of HLOZ profiles, with an arbitrary starting
scale and number of transitions. -/
noncomputable def corridorProfiles (delta : ℝ) (start N : ℕ) :
    Finset (NatPath N) := by
  classical
  exact (profileBox delta start N).filter (ProfileCorridor delta start)

@[simp] theorem mem_corridorProfiles {delta : ℝ} {start N : ℕ}
    {q : NatPath N} :
    q ∈ corridorProfiles delta start N ↔ ProfileCorridor delta start q := by
  classical
  constructor
  · rw [corridorProfiles, Finset.mem_filter]
    exact fun h ↦ h.2
  · intro h
    rw [corridorProfiles, Finset.mem_filter]
    refine ⟨?_, h⟩
    rw [profileBox, Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Icc]
    exact ⟨Nat.zero_le _, coordinate_le_of_profileCorridor (h i)⟩

/-- The natural-valued profile corridor is exactly the inverse image of the
integer centered corridor used in Lemma A.8 and Proposition A.7. -/
theorem mem_corridorProfiles_iff_centeredPath {delta : ℝ} {start N : ℕ}
    {q : NatPath N} :
    q ∈ corridorProfiles delta start N ↔
      centeredPath start q ∈ Erdos1166.HLOZLemmaA8.hlozCorridorPaths delta start N := by
  rw [mem_corridorProfiles]
  unfold Erdos1166.HLOZLemmaA8.hlozCorridorPaths
  rw [Erdos1166.HLOZLemmaA8.mem_corridorPaths]
  rfl

/-! ### Exact identification with the discrete Gaussian corridor sum -/

/-- Add the deterministic parabola back to an integer deviation path.  On a
source corridor this is nonnegative, so `Int.toNat` loses no information. -/
def uncenterPath (start : ℕ) {N : ℕ}
    (p : Erdos1166.HLOZLemmaA8.Path N) : NatPath N :=
  fun i ↦ Int.toNat (2 * (start + (i : ℕ) : ℤ) ^ 2 + p i)

lemma centeredPath_uncenterPath {start N : ℕ}
    {p : Erdos1166.HLOZLemmaA8.Path N}
    (hp : ∀ i : Fin (N + 1),
      -(2 * (start + (i : ℕ) : ℤ) ^ 2) ≤ p i) :
    centeredPath start (uncenterPath start p) = p := by
  funext i
  rw [centeredPath, centeredDeviation, uncenterPath]
  have hnonneg : 0 ≤ 2 * (start + (i : ℕ) : ℤ) ^ 2 + p i := by
    linarith [hp i]
  rw [Int.toNat_of_nonneg hnonneg]
  push_cast
  ring

/-- For `δ ≤ 1`, the HLOZ deviation window is below the parabola and hence
every centered integer path represents a genuine natural-valued profile. -/
lemma corridorRadius_le_two_sq {delta : ℝ} (hdelta : delta ≤ 1)
    {ell : ℕ} (hell : 1 ≤ ell) :
    Erdos1166.HLOZLemmaA8.corridorRadius delta ell ≤ 2 * ell ^ 2 := by
  have hpow : (ell : ℝ) ^ (1 + delta) ≤ (ell : ℝ) ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hell) (by linarith)
  have hfloor := corridorRadius_cast_le delta ell
  have hreal :
      (Erdos1166.HLOZLemmaA8.corridorRadius delta ell : ℝ) ≤
        (2 * ell ^ 2 : ℕ) := by
    norm_num [Real.rpow_two] at hpow ⊢
    exact hfloor.trans (hpow.trans (by nlinarith))
  exact_mod_cast hreal

lemma uncenterPath_mem_corridorProfiles {delta : ℝ} (hdelta : delta ≤ 1)
    {start N : ℕ} (hstart : 1 ≤ start)
    {p : Erdos1166.HLOZLemmaA8.Path N}
    (hp : p ∈ Erdos1166.HLOZLemmaA8.hlozCorridorPaths delta start N) :
    uncenterPath start p ∈ corridorProfiles delta start N := by
  rw [mem_corridorProfiles_iff_centeredPath]
  have hpbound := Erdos1166.HLOZLemmaA8.mem_corridorPaths.mp hp
  have hlower : ∀ i : Fin (N + 1),
      -(2 * (start + (i : ℕ) : ℤ) ^ 2) ≤ p i := by
    intro i
    have hr := corridorRadius_le_two_sq hdelta
      (show 1 ≤ start + (i : ℕ) by omega)
    have habs := hpbound i
    rw [abs_le] at habs
    have hrZ : (Erdos1166.HLOZLemmaA8.corridorRadius delta
        (start + (i : ℕ)) : ℤ) ≤ 2 * (start + (i : ℕ) : ℤ) ^ 2 := by
      exact_mod_cast hr
    linarith [habs.1]
  rw [centeredPath_uncenterPath hlower]
  exact hp

/-- The Gaussian sum over natural-valued parabolic profiles is exactly the
integer lattice sum of Lemma A.8.  This closes the previously implicit
surjectivity step: every admissible integer deviation has a nonnegative
uncentered profile when `δ ≤ 1`. -/
theorem centeredGaussianPathSum_corridorProfiles_eq_hlozPathSum
    {delta : ℝ} (hdelta : delta ≤ 1) {start N : ℕ} (hstart : 1 ≤ start) :
    centeredGaussianPathSum start N (corridorProfiles delta start N) =
      Erdos1166.HLOZLemmaA8.hlozPathSum delta start N := by
  unfold centeredGaussianPathSum Erdos1166.HLOZLemmaA8.hlozPathSum
    Erdos1166.HLOZLemmaA8.pathSum
  apply Finset.sum_bij (fun q _hq ↦ centeredPath start q)
  · intro q hq
    exact mem_corridorProfiles_iff_centeredPath.mp hq
  · intro q₁ hq₁ q₂ hq₂ heq
    funext i
    have hi := congrFun heq i
    simp [centeredPath, centeredDeviation] at hi
    exact_mod_cast hi
  · intro p hp
    refine ⟨uncenterPath start p,
      uncenterPath_mem_corridorProfiles hdelta hstart hp, ?_⟩
    apply centeredPath_uncenterPath
    intro i
    have hpbound := Erdos1166.HLOZLemmaA8.mem_corridorPaths.mp hp i
    rw [abs_le] at hpbound
    have hr := corridorRadius_le_two_sq hdelta
      (show 1 ≤ start + (i : ℕ) by omega)
    have hrZ : (Erdos1166.HLOZLemmaA8.corridorRadius delta
        (start + (i : ℕ)) : ℤ) ≤ 2 * (start + (i : ℕ) : ℤ) ^ 2 := by
      exact_mod_cast hr
    linarith [hpbound.1]
  · intro q hq
    rfl

/-- Direct composition of Lemma A.8 with Proposition A.7 on the same finite
power corridor.  The Gaussian premise is now the literal `hlozPathSum`
lower bound, rather than a separately assumed centered-profile sum. -/
theorem hlozPathSum_corridor_transfer
    {delta G : ℝ} (hdelta : delta ≤ 1) {start N : ℕ}
    (hstart : 0 < start)
    (hbudget : ParabolicRadiusBudget start N (hlozRadius delta start N))
    (hG : G ≤ Erdos1166.HLOZLemmaA8.hlozPathSum delta start N)
    (hG0 : 0 ≤ G) :
    Real.exp (-pathNormalizationCost start N (hlozRadius delta start N)) *
        Real.exp (-corridorComparisonCostBound start N
          (hlozRadius delta start N)) * G ≤
      halfNegBinPathSum (corridorProfiles delta start N) := by
  apply corridor_halfNegBinPathSum_lower
    (corridorProfiles delta start N) (hlozRadius delta start N)
    hstart hG0 hbudget
  · intro q hq
    exact mem_corridorProfiles.mp hq
  · rw [centeredGaussianPathSum_corridorProfiles_eq_hlozPathSum
      hdelta (show 1 ≤ start by omega)]
    exact hG

/-- Premise-free analytic specialization of the preceding transfer: the
many-path Gaussian lower bound is discharged by the variance-block proof in
Lemma A.8, leaving only its explicit finite-scale geometry hypotheses and
the already proved Proposition-A.7 radius budget. -/
theorem explicit_hlozCorridor_halfNegBinPathSum_lower
    {m N n : ℕ} {delta : ℝ}
    (hm : 0 < m) (hNpos : 0 < N) (hdelta0 : -1 ≤ delta)
    (hdelta1 : delta ≤ 1) (hupper : m + N ≤ n)
    (hpow : 2 ≤ (m : ℝ) ^ (1 + delta))
    (hratio : 2 ≤ Erdos1166.HLOZLemmaA8.varianceBlockRatio n
      ((m : ℝ) ^ (1 + delta) / 8))
    (hN : (N : ℝ) ≤ (m : ℝ) ^ (1 + delta) / 4)
    (hbudget : ParabolicRadiusBudget m N (hlozRadius delta m N)) :
    Real.exp (-pathNormalizationCost m N (hlozRadius delta m N)) *
        Real.exp (-corridorComparisonCostBound m N (hlozRadius delta m N)) *
        Real.exp (-(40960000 * (n : ℝ) ^ 3 /
          ((m : ℝ) ^ (1 + delta)) ^ 2 +
          (N : ℝ) * ((m : ℝ) ^ (1 + delta) / 2 + 3) /
            (m : ℝ) ^ 2 + 2)) ≤
      halfNegBinPathSum (corridorProfiles delta m N) := by
  apply hlozPathSum_corridor_transfer hdelta1 hm hbudget
  · exact Erdos1166.HLOZLemmaA8.exp_neg_power_radius_le_hlozPathSum
      hm hNpos hdelta0 hupper hpow hratio hN
  · positivity

lemma tendsto_rhoBlockStart_atTop {rho : ℝ} (hrho : 0 < rho) :
    Tendsto (Erdos1166.HLOZLemmaA8.rhoBlockStart rho) atTop atTop := by
  unfold Erdos1166.HLOZLemmaA8.rhoBlockStart
  exact tendsto_nat_floor_atTop.comp
    ((tendsto_rpow_atTop hrho).comp (tendsto_natCast_atTop_atTop (R := ℝ)))

/-- Source-scale composition of Lemma A.8 with Proposition A.7.  The
starting scale is the literal `floor (n^ρ)` and every Gaussian premise has
been discharged.  The two remaining exponential factors are precisely the
normalization and local-limit losses already isolated and bounded in
Proposition A.7. -/
theorem eventually_rho_floor_halfNegBinPathSum_lower
    {rho delta : ℝ} (hrho0 : 0 < rho) (hrho1 : rho < 1)
    (hd0 : -1 ≤ delta) (hd1 : delta ≤ 1 / 3)
    (hcritical : 1 < rho * (1 + delta)) :
    ∀ᶠ n : ℕ in atTop,
      let m := Erdos1166.HLOZLemmaA8.rhoBlockStart rho n
      let N := n - m
      Real.exp (-pathNormalizationCost m N (hlozRadius delta m N)) *
          Real.exp (-corridorComparisonCostBound m N (hlozRadius delta m N)) *
          Real.exp (-(655360100 *
            (n : ℝ) ^ max (3 - 2 * rho * (1 + delta)) (2 * delta))) ≤
        halfNegBinPathSum (corridorProfiles delta m N) := by
  have hA8 := Erdos1166.HLOZLemmaA8.eventually_exp_neg_rho_floor_le_hlozPathSum
    hrho0 hrho1 hd0 hd1 hcritical
  have hbudget0 := eventually_hlozRadiusBudget (show delta < 1 by linarith)
  rw [eventually_atTop] at hbudget0
  rcases hbudget0 with ⟨L, hL⟩
  have hstart := (tendsto_rhoBlockStart_atTop hrho0).eventually
    (eventually_ge_atTop (max L 1))
  filter_upwards [hA8, hstart] with n hA8n hstartn
  dsimp only
  apply hlozPathSum_corridor_transfer (show delta ≤ 1 by linarith)
    (show 0 < Erdos1166.HLOZLemmaA8.rhoBlockStart rho n by omega)
    (hL _ (le_trans (Nat.le_max_left _ _) hstartn)
      (n - Erdos1166.HLOZLemmaA8.rhoBlockStart rho n))
  · exact hA8n
  · positivity

/-- Source indexing: a path with `n - 2` transitions has coordinates
`(m₂, ..., mₙ)`. -/
noncomputable def sourceProfiles (delta : ℝ) (n : ℕ) :
    Finset (NatPath (n - 2)) :=
  corridorProfiles delta 2 (n - 2)

@[simp] theorem mem_sourceProfiles {delta : ℝ} {n : ℕ}
    {q : NatPath (n - 2)} :
    q ∈ sourceProfiles delta n ↔ ProfileCorridor delta 2 q := by
  exact mem_corridorProfiles

/-! ### Multiblock A.8 composition on the full source profile -/

/-- The exact A.12 multiblock estimate, transported from integer paths to
natural parabolic profiles.  No Gaussian or asymptotic premise remains: the
right side is the centered Gaussian sum over the literal corridor. -/
theorem multiBlock_centeredGaussianPathSum_lower
    {delta : ℝ} (hd0 : 0 < delta) (hd1 : delta ≤ 1)
    {m n : ℕ} (hm : 0 < m) (Ns : List ℕ) (hNs : Ns ≠ [])
    (hupper : m + Erdos1166.HLOZLemmaA8.separatedLength Ns ≤ n) :
    Real.exp (-((4 + 64 / (2 * delta)) * (n : ℝ) ^ (2 * delta) *
        (Erdos1166.HLOZLemmaA8.bridgeCount Ns : ℝ))) *
        Erdos1166.HLOZLemmaA8.separatedBlockProduct delta m Ns ≤
      centeredGaussianPathSum m
        (Erdos1166.HLOZLemmaA8.separatedLength Ns)
        (corridorProfiles delta m
          (Erdos1166.HLOZLemmaA8.separatedLength Ns)) := by
  rw [centeredGaussianPathSum_corridorProfiles_eq_hlozPathSum hd1
    (show 1 ≤ m by omega)]
  exact Erdos1166.HLOZLemmaA8.exp_multiBridgeCost_mul_separatedBlockProduct_le
    hd0 hd1 hm Ns hNs hupper

/-- Source-indexed form of the preceding theorem.  A list of blocks whose
separated lengths cover scales `2,…,n` now gives a checked lower bound for
the exact full-profile Gaussian sum consumed by Proposition A.7. -/
theorem multiBlock_sourceGaussianPathSum_lower
    {delta : ℝ} (hd0 : 0 < delta) (hd1 : delta ≤ 1)
    {n : ℕ} (hn : 2 ≤ n) (Ns : List ℕ) (hNs : Ns ≠ [])
    (hlen : Erdos1166.HLOZLemmaA8.separatedLength Ns = n - 2) :
    Real.exp (-((4 + 64 / (2 * delta)) * (n : ℝ) ^ (2 * delta) *
        (Erdos1166.HLOZLemmaA8.bridgeCount Ns : ℝ))) *
        Erdos1166.HLOZLemmaA8.separatedBlockProduct delta 2 Ns ≤
      centeredGaussianPathSum 2 (n - 2) (sourceProfiles delta n) := by
  unfold sourceProfiles
  rw [← hlen]
  apply multiBlock_centeredGaussianPathSum_lower hd0 hd1 (by norm_num) Ns hNs
  omega

/-! ### Exact finite-prefix concatenation for Proposition A.7 -/

/-- Concatenate two natural-valued profiles separated by one transition. -/
def joinNatPath {N₁ N₂ : ℕ} (p : NatPath N₁) (q : NatPath N₂) :
    NatPath (N₁ + 1 + N₂) :=
  fun i ↦ Fin.append p q (Fin.cast (by omega) i)

@[simp] lemma joinNatPath_left {N₁ N₂ : ℕ} (p : NatPath N₁) (q : NatPath N₂)
    (i : Fin (N₁ + 1)) :
    joinNatPath p q (Fin.castAdd (N₂ + 1) i) = p i := by
  unfold joinNatPath
  have hi : Fin.cast (by omega) (Fin.castAdd (N₂ + 1) i) =
      Fin.castAdd (N₂ + 1) i := by apply Fin.ext; rfl
  rw [hi]
  exact Fin.append_left p q i

@[simp] lemma joinNatPath_right {N₁ N₂ : ℕ} (p : NatPath N₁) (q : NatPath N₂)
    (i : Fin (N₂ + 1)) :
    joinNatPath p q (Fin.natAdd (N₁ + 1) i) = q i := by
  unfold joinNatPath
  have hi : Fin.cast (by omega) (Fin.natAdd (N₁ + 1) i) =
      Fin.natAdd (N₁ + 1) i := by apply Fin.ext; rfl
  rw [hi]
  exact Fin.append_right p q i

lemma joinNatPath_injective {N₁ N₂ : ℕ} :
    Function.Injective (fun pq : NatPath N₁ × NatPath N₂ ↦
      joinNatPath pq.1 pq.2) := by
  intro a b h
  apply Prod.ext
  · funext i
    have := congrFun h (Fin.castAdd (N₂ + 1) i)
    simpa using this
  · funext i
    have := congrFun h (Fin.natAdd (N₁ + 1) i)
    simpa using this

lemma joinNatPath_mem_corridorProfiles_iff {delta : ℝ} {m N₁ N₂ : ℕ}
    (p : NatPath N₁) (q : NatPath N₂) :
    joinNatPath p q ∈ corridorProfiles delta m (N₁ + 1 + N₂) ↔
      p ∈ corridorProfiles delta m N₁ ∧
      q ∈ corridorProfiles delta (m + N₁ + 1) N₂ := by
  simp only [mem_corridorProfiles, ProfileCorridor]
  constructor
  · intro h
    constructor
    · intro i
      have hi := h (Fin.castAdd (N₂ + 1) i)
      simpa [joinNatPath, Nat.add_assoc] using hi
    · intro i
      have hi := h (Fin.natAdd (N₁ + 1) i)
      simpa [joinNatPath, Nat.add_assoc, Nat.add_left_comm] using hi
  · rintro ⟨hp, hq⟩ i
    refine Fin.addCases (m := N₁ + 1) (n := N₂ + 1) ?_ ?_ i
    · intro j
      simpa [joinNatPath, Nat.add_assoc] using hp j
    · intro j
      simpa [joinNatPath, Nat.add_assoc, Nat.add_left_comm] using hq j

/-- Exact factorization of a concatenated negative-binomial trajectory. -/
lemma halfNegBinPathWeight_joinNatPath {N₁ N₂ : ℕ}
    (p : NatPath N₁) (q : NatPath N₂) :
    halfNegBinPathWeight (joinNatPath p q) =
      halfNegBinPathWeight p *
        Erdos1166.HLOZAppendixA.halfNegBinMass (p (Fin.last N₁)) (q 0) *
          halfNegBinPathWeight q := by
  unfold halfNegBinPathWeight
  rw [Fin.prod_univ_add]
  rw [Fin.prod_univ_castSucc]
  congr 1
  · congr 1
    · apply Finset.prod_congr rfl
      intro i hi
      have h₁ : (Fin.castAdd N₂ i.castSucc).castSucc =
          Fin.castAdd (N₂ + 1) i.castSucc := by apply Fin.ext; rfl
      have h₂ : (Fin.castAdd N₂ i.castSucc).succ =
          Fin.castAdd (N₂ + 1) i.succ := by apply Fin.ext; rfl
      rw [h₁, h₂, joinNatPath_left, joinNatPath_left]
    ·
      have h₁ : (Fin.castAdd N₂ (Fin.last N₁)).castSucc =
          Fin.castAdd (N₂ + 1) (Fin.last N₁) := by apply Fin.ext; rfl
      have h₂ : (Fin.castAdd N₂ (Fin.last N₁)).succ =
          Fin.natAdd (N₁ + 1) (0 : Fin (N₂ + 1)) := by apply Fin.ext; rfl
      rw [h₁, h₂, joinNatPath_left, joinNatPath_right]
  · apply Finset.prod_congr rfl
    intro i hi
    congr 1
    ·
      have h₁ : (Fin.natAdd (N₁ + 1) i).castSucc =
          Fin.natAdd (N₁ + 1) i.castSucc := by apply Fin.ext; rfl
      rw [h₁, joinNatPath_right]
    ·
      have h₂ : (Fin.natAdd (N₁ + 1) i).succ =
          Fin.natAdd (N₁ + 1) i.succ := by apply Fin.ext; rfl
      rw [h₂, joinNatPath_right]

private lemma halfNegBinPathWeight_nonneg_for_join {N : ℕ} (q : NatPath N) :
    0 ≤ halfNegBinPathWeight q := by
  unfold halfNegBinPathWeight
  exact Finset.prod_nonneg fun i hi ↦
    Erdos1166.HLOZAppendixA.halfNegBinMass_nonneg _ _

noncomputable def joinNatPathFamily {N₁ N₂ : ℕ}
    (P : Finset (NatPath N₁)) (Q : Finset (NatPath N₂)) :
    Finset (NatPath (N₁ + 1 + N₂)) := by
  classical
  exact (P ×ˢ Q).image (fun pq ↦ joinNatPath pq.1 pq.2)

lemma joinNatPathFamily_subset_corridorProfiles {delta : ℝ} {m N₁ N₂ : ℕ} :
    joinNatPathFamily (corridorProfiles delta m N₁)
        (corridorProfiles delta (m + N₁ + 1) N₂) ⊆
      corridorProfiles delta m (N₁ + 1 + N₂) := by
  classical
  intro r hr
  rw [joinNatPathFamily, Finset.mem_image] at hr
  rcases hr with ⟨pq, hpq, rfl⟩
  rw [joinNatPath_mem_corridorProfiles_iff]
  exact Finset.mem_product.mp hpq

lemma halfNegBinPathSum_joinNatPathFamily {N₁ N₂ : ℕ}
    (P : Finset (NatPath N₁)) (Q : Finset (NatPath N₂)) :
    halfNegBinPathSum (joinNatPathFamily P Q) =
      ∑ p ∈ P, ∑ q ∈ Q,
        halfNegBinPathWeight p *
          Erdos1166.HLOZAppendixA.halfNegBinMass (p (Fin.last N₁)) (q 0) *
            halfNegBinPathWeight q := by
  classical
  unfold halfNegBinPathSum joinNatPathFamily
  rw [Finset.sum_image (joinNatPath_injective.injOn)]
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  exact halfNegBinPathWeight_joinNatPath p q

/-- Exact finite-prefix bridge for Proposition A.7.  This lets the finitely
many scales before the sharp local-limit cutoff be retained as an explicit
positive factor, rather than imposing an invalid scale-2 radius budget. -/
theorem mul_halfNegBinPathSums_le_of_bridge
    {delta c : ℝ} {m N₁ N₂ : ℕ}
    (hbridge : ∀ p ∈ corridorProfiles delta m N₁,
      ∀ q ∈ corridorProfiles delta (m + N₁ + 1) N₂,
        c ≤ Erdos1166.HLOZAppendixA.halfNegBinMass (p (Fin.last N₁)) (q 0)) :
    c * halfNegBinPathSum (corridorProfiles delta m N₁) *
        halfNegBinPathSum (corridorProfiles delta (m + N₁ + 1) N₂) ≤
      halfNegBinPathSum (corridorProfiles delta m (N₁ + 1 + N₂)) := by
  let P := corridorProfiles delta m N₁
  let Q := corridorProfiles delta (m + N₁ + 1) N₂
  calc
    c * halfNegBinPathSum P * halfNegBinPathSum Q =
        ∑ p ∈ P, ∑ q ∈ Q,
          c * halfNegBinPathWeight p * halfNegBinPathWeight q := by
      unfold halfNegBinPathSum
      calc
        c * (∑ p ∈ P, halfNegBinPathWeight p) *
            ∑ q ∈ Q, halfNegBinPathWeight q =
          (∑ p ∈ P, halfNegBinPathWeight p) *
            (c * ∑ q ∈ Q, halfNegBinPathWeight q) := by ring
        _ = (∑ p ∈ P, halfNegBinPathWeight p) *
            (∑ q ∈ Q, c * halfNegBinPathWeight q) := by rw [Finset.mul_sum]
        _ = ∑ p ∈ P, ∑ q ∈ Q,
            c * halfNegBinPathWeight p * halfNegBinPathWeight q := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro p hp
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro q hq
          ring
    _ ≤ ∑ p ∈ P, ∑ q ∈ Q,
        halfNegBinPathWeight p *
          Erdos1166.HLOZAppendixA.halfNegBinMass (p (Fin.last N₁)) (q 0) *
            halfNegBinPathWeight q := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro q hq
      have h := mul_le_mul_of_nonneg_left
        (hbridge p (by simpa [P] using hp) q (by simpa [Q] using hq))
        (halfNegBinPathWeight_nonneg_for_join p)
      have h' := mul_le_mul_of_nonneg_right h (halfNegBinPathWeight_nonneg_for_join q)
      nlinarith
    _ = halfNegBinPathSum (joinNatPathFamily P Q) := by
      rw [halfNegBinPathSum_joinNatPathFamily]
    _ ≤ halfNegBinPathSum
        (corridorProfiles delta m (N₁ + 1 + N₂)) := by
      unfold halfNegBinPathSum
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (by simpa [P, Q] using
          (joinNatPathFamily_subset_corridorProfiles
            (delta := delta) (m := m) (N₁ := N₁) (N₂ := N₂)))
        (fun i hi hnot ↦ halfNegBinPathWeight_nonneg_for_join _)

/-! ### A concrete positive low-scale prefix -/

/-- The deterministic parabolic profile `m_ℓ = 2ℓ²`.  Its centered
deviation vanishes at every coordinate, so it belongs to every power
corridor, independently of the value of `delta`. -/
def parabolicProfile (start N : ℕ) : NatPath N :=
  fun i ↦ 2 * (start + (i : ℕ)) ^ 2

lemma parabolicProfile_mem_corridorProfiles (delta : ℝ) (start N : ℕ) :
    parabolicProfile start N ∈ corridorProfiles delta start N := by
  rw [mem_corridorProfiles]
  intro i
  simp [ProfileCorridor, parabolicProfile, centeredDeviation]

lemma halfNegBinPathWeight_parabolicProfile_pos {start N : ℕ}
    (hstart : 0 < start) :
    0 < halfNegBinPathWeight (parabolicProfile start N) := by
  unfold halfNegBinPathWeight
  apply Finset.prod_pos
  intro i hi
  apply Erdos1166.HLOZAppendixA.halfNegBinMass_pos
  simp [parabolicProfile]
  positivity

/-- The canonical low-scale parabolic prefix has an explicit cubic lower
bound.  This intentionally uses only `choose ≥ 1`: every transition is at
least its binary denominator, and all transition endpoints are bounded by
the final prefix scale.  Although very coarse, the resulting `exp (-4M³)`
loss is lower order once the recursive Appendix cutoff is an eighth-power
scale. -/
theorem exp_neg_four_mul_end_cube_le_halfNegBinPathWeight_parabolicProfile
    {start N : ℕ} (hstart : 1 ≤ start) :
    Real.exp (-4 * ((start + N : ℕ) : ℝ) ^ 3) ≤
      halfNegBinPathWeight (parabolicProfile start N) := by
  let M := start + N
  have hNM : N ≤ M := by dsimp [M]; omega
  have hpoint : ∀ i : Fin N,
      Real.exp (-4 * (M : ℝ) ^ 2) ≤
        Erdos1166.HLOZAppendixA.halfNegBinMass
          (parabolicProfile start N i.castSucc)
          (parabolicProfile start N i.succ) := by
    intro i
    let ell := start + (i : ℕ)
    let b := 2 * ell ^ 2
    let b' := 2 * (ell + 1) ^ 2
    have hellM : ell + 1 ≤ M := by
      dsimp [ell, M]
      omega
    have hsquare : (ell + 1) ^ 2 ≤ M ^ 2 :=
      Nat.pow_le_pow_left hellM 2
    have hellsquare : ell ^ 2 ≤ (ell + 1) ^ 2 :=
      Nat.pow_le_pow_left (by omega) 2
    have hB : b + b' ≤ 4 * M ^ 2 := by
      dsimp [b, b']
      omega
    have hBreal : ((b + b' : ℕ) : ℝ) ≤ 4 * (M : ℝ) ^ 2 := by
      exact_mod_cast hB
    have hpow : (2 : ℝ) ^ (b + b') ≤
        Real.exp (4 * (M : ℝ) ^ 2) := by
      calc
        (2 : ℝ) ^ (b + b') =
            Real.exp (Real.log ((2 : ℝ) ^ (b + b'))) :=
          (Real.exp_log (by positivity)).symm
        _ = Real.exp (((b + b' : ℕ) : ℝ) * Real.log 2) := by
          rw [Real.log_pow]
        _ ≤ Real.exp (4 * (M : ℝ) ^ 2) := by
          rw [Real.exp_le_exp]
          have hlog2 : Real.log 2 ≤ 1 :=
            Real.log_two_lt_d9.le.trans (by norm_num)
          nlinarith
    have hrecip : Real.exp (-4 * (M : ℝ) ^ 2) ≤
        1 / (2 : ℝ) ^ (b + b') := by
      rw [show -4 * (M : ℝ) ^ 2 = -(4 * (M : ℝ) ^ 2) by ring,
        Real.exp_neg]
      simpa only [one_div] using
        (one_div_le_one_div_of_le
          (by positivity : (0 : ℝ) < (2 : ℝ) ^ (b + b')) hpow)
    have hbpos : 0 < b := by dsimp [b, ell]; positivity
    have hchoose : (1 : ℝ) ≤ Nat.choose (b + b' - 1) b' := by
      exact_mod_cast Nat.succ_le_iff.mpr (Nat.choose_pos (by omega))
    simpa [Erdos1166.HLOZAppendixA.halfNegBinMass, parabolicProfile,
      ell, b, b', Fin.val_succ, Fin.val_castSucc, Nat.add_assoc] using
      hrecip.trans (div_le_div_of_nonneg_right hchoose (by positivity))
  unfold halfNegBinPathWeight
  calc
    Real.exp (-4 * (M : ℝ) ^ 3) ≤
        Real.exp (-4 * (M : ℝ) ^ 2) ^ N := by
      rw [← Real.exp_nat_mul, Real.exp_le_exp]
      have hNMreal : (N : ℝ) ≤ M := by exact_mod_cast hNM
      nlinarith [mul_nonneg (sq_nonneg (M : ℝ))
        (sub_nonneg.mpr hNMreal)]
    _ = ∏ _i : Fin N, Real.exp (-4 * (M : ℝ) ^ 2) := by
      rw [Fin.prod_const]
    _ ≤ ∏ i : Fin N,
        Erdos1166.HLOZAppendixA.halfNegBinMass
          (parabolicProfile start N i.castSucc)
          (parabolicProfile start N i.succ) := by
      exact Finset.prod_le_prod (fun _ _ ↦ (Real.exp_pos _).le)
        (fun i _ ↦ hpoint i)

/-- A completely explicit positive lower bound for a deleted bridge between
scales `ell` and `ell+1`.  The exponent is the sum of the two deterministic
upper endpoints of the corridor boxes. -/
noncomputable def finiteBridgeLower (delta : ℝ) (ell : ℕ) : ℝ :=
  1 / (2 : ℝ) ^
    ((2 * ell ^ 2 + Erdos1166.HLOZLemmaA8.corridorRadius delta ell) +
      (2 * (ell + 1) ^ 2 +
        Erdos1166.HLOZLemmaA8.corridorRadius delta (ell + 1)))

theorem finiteBridgeLower_pos (delta : ℝ) (ell : ℕ) :
    0 < finiteBridgeLower delta ell := by
  unfold finiteBridgeLower
  positivity

/-- The deliberately coarse finite bridge still has a quantitative
stretched-exponential lower bound.  For `delta ≤ 1` both corridor radii are
at most the corresponding square scale, so the binary-cylinder exponent is
at most `6 (ell+1)²`.  This is the bound needed when the recursively chosen
lowest Appendix scale is eventually below an eighth power of the outer
scale. -/
theorem exp_neg_six_mul_succ_sq_le_finiteBridgeLower
    {delta : ℝ} (hdelta : delta ≤ 1) {ell : ℕ} (hell : 1 ≤ ell) :
    Real.exp (-6 * ((ell + 1 : ℕ) : ℝ) ^ 2) ≤
      finiteBridgeLower delta ell := by
  let B : ℕ :=
    (2 * ell ^ 2 + Erdos1166.HLOZLemmaA8.corridorRadius delta ell) +
      (2 * (ell + 1) ^ 2 +
        Erdos1166.HLOZLemmaA8.corridorRadius delta (ell + 1))
  have hellR : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have hell1R : (1 : ℝ) ≤ (ell + 1 : ℕ) := by
    exact_mod_cast (show 1 ≤ ell + 1 by omega)
  have hrpow : (ell : ℝ) ^ (1 + delta) ≤ (ell : ℝ) ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hellR (by linarith)
  have hrpow1 : ((ell + 1 : ℕ) : ℝ) ^ (1 + delta) ≤
      ((ell + 1 : ℕ) : ℝ) ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hell1R (by linarith)
  have hr : Erdos1166.HLOZLemmaA8.corridorRadius delta ell ≤ ell ^ 2 := by
    exact_mod_cast
      (Erdos1166.HLOZLemmaA8.corridorRadius_cast_le_self delta ell |>.trans
        (hrpow.trans_eq (Real.rpow_two _)))
  have hr1 : Erdos1166.HLOZLemmaA8.corridorRadius delta (ell + 1) ≤
      (ell + 1) ^ 2 := by
    exact_mod_cast
      (Erdos1166.HLOZLemmaA8.corridorRadius_cast_le_self delta (ell + 1) |>.trans
        (hrpow1.trans_eq (Real.rpow_two _)))
  have hsquare : ell ^ 2 ≤ (ell + 1) ^ 2 := by
    exact Nat.pow_le_pow_left (by omega) 2
  have hBnat : B ≤ 6 * (ell + 1) ^ 2 := by
    dsimp [B]
    omega
  have hBreal : (B : ℝ) ≤ 6 * ((ell + 1 : ℕ) : ℝ) ^ 2 := by
    exact_mod_cast hBnat
  have hlog2 : Real.log 2 ≤ 1 :=
    Real.log_two_lt_d9.le.trans (by norm_num)
  have hpow : (2 : ℝ) ^ B ≤
      Real.exp (6 * ((ell + 1 : ℕ) : ℝ) ^ 2) := by
    calc
      (2 : ℝ) ^ B = Real.exp (Real.log ((2 : ℝ) ^ B)) :=
        (Real.exp_log (by positivity)).symm
      _ = Real.exp ((B : ℝ) * Real.log 2) := by rw [Real.log_pow]
      _ ≤ Real.exp (6 * ((ell + 1 : ℕ) : ℝ) ^ 2) := by
        rw [Real.exp_le_exp]
        nlinarith
  rw [show finiteBridgeLower delta ell = 1 / (2 : ℝ) ^ B by rfl]
  rw [show -6 * ((ell + 1 : ℕ) : ℝ) ^ 2 =
      -(6 * ((ell + 1 : ℕ) : ℝ) ^ 2) by ring, Real.exp_neg]
  simpa only [one_div] using
    (one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (2 : ℝ) ^ B) hpow)

/-- Combined quantitative lower bound for the complete finite source prefix:
the canonical parabolic path from scale `2`, followed by its deleted bridge
into the checked A.8 tail.  The uniform `exp (-10 m³)` loss is deliberately
coarse but already small enough at the checked eighth-power cutoff. -/
theorem exp_neg_ten_mul_cube_le_finitePrefixFactor
    {delta : ℝ} (hdelta : delta ≤ 1) {m : ℕ} (hm : 3 ≤ m) :
    Real.exp (-10 * (m : ℝ) ^ 3) ≤
      finiteBridgeLower delta (m - 1) *
        halfNegBinPathWeight (parabolicProfile 2 (m - 3)) := by
  have hb := exp_neg_six_mul_succ_sq_le_finiteBridgeLower
    hdelta (ell := m - 1) (by omega)
  have hp := exp_neg_four_mul_end_cube_le_halfNegBinPathWeight_parabolicProfile
    (start := 2) (N := m - 3) (by norm_num)
  calc
    Real.exp (-10 * (m : ℝ) ^ 3) ≤
        Real.exp (-6 * (m : ℝ) ^ 2 - 4 * ((m - 1 : ℕ) : ℝ) ^ 3) := by
      rw [Real.exp_le_exp]
      have hm1 : ((m - 1 : ℕ) : ℝ) ≤ m := by
        exact_mod_cast (Nat.sub_le m 1)
      have hm10 : (0 : ℝ) ≤ (m - 1 : ℕ) := by positivity
      have hcub : ((m - 1 : ℕ) : ℝ) ^ 3 ≤ (m : ℝ) ^ 3 := by gcongr
      have hmone : (1 : ℝ) ≤ m := by
        exact_mod_cast (show 1 ≤ m by omega)
      have hsqcube : (m : ℝ) ^ 2 ≤ (m : ℝ) ^ 3 := by
        nlinarith [mul_nonneg (sq_nonneg (m : ℝ)) (sub_nonneg.mpr hmone)]
      linarith
    _ = Real.exp (-6 * (m : ℝ) ^ 2) *
        Real.exp (-4 * ((m - 1 : ℕ) : ℝ) ^ 3) := by
      rw [← Real.exp_add]
      congr 1 <;> ring
    _ ≤ finiteBridgeLower delta (m - 1) *
        halfNegBinPathWeight (parabolicProfile 2 (m - 3)) := by
      have hsucc : m - 1 + 1 = m := by omega
      have hend : 2 + (m - 3) = m - 1 := by omega
      rw [hsucc] at hb
      rw [hend] at hp
      exact mul_le_mul hb hp (Real.exp_pos _).le
        (finiteBridgeLower_pos delta (m - 1)).le

theorem finiteBridgeLower_le_halfNegBinMass
    {delta : ℝ} {ell b b' : ℕ}
    (hb : b ≤ 2 * ell ^ 2 +
      Erdos1166.HLOZLemmaA8.corridorRadius delta ell)
    (hb' : b' ≤ 2 * (ell + 1) ^ 2 +
      Erdos1166.HLOZLemmaA8.corridorRadius delta (ell + 1))
    (hbpos : 0 < b) :
    finiteBridgeLower delta ell ≤
      Erdos1166.HLOZAppendixA.halfNegBinMass b b' := by
  let B := (2 * ell ^ 2 +
      Erdos1166.HLOZLemmaA8.corridorRadius delta ell) +
    (2 * (ell + 1) ^ 2 +
      Erdos1166.HLOZLemmaA8.corridorRadius delta (ell + 1))
  have hsum : b + b' ≤ B := by dsimp [B]; omega
  have hpow : (2 : ℝ) ^ (b + b') ≤ (2 : ℝ) ^ B := by
    exact pow_le_pow_right₀ (by norm_num) hsum
  have hrecip : 1 / (2 : ℝ) ^ B ≤ 1 / (2 : ℝ) ^ (b + b') := by
    exact one_div_le_one_div_of_le (by positivity) hpow
  have hchoose : (1 : ℝ) ≤ Nat.choose (b + b' - 1) b' := by
    exact_mod_cast Nat.succ_le_iff.mpr
      (Nat.choose_pos (by omega))
  unfold Erdos1166.HLOZAppendixA.halfNegBinMass
  rw [show finiteBridgeLower delta ell = 1 / (2 : ℝ) ^ B by
    rfl]
  exact hrecip.trans (div_le_div_of_nonneg_right hchoose (by positivity))

theorem finiteBridgeLower_uniform
    {delta : ℝ} (hdelta : delta ≤ 1) {m N₁ N₂ : ℕ} (hm : 0 < m) :
    ∀ p ∈ corridorProfiles delta m N₁,
      ∀ q ∈ corridorProfiles delta (m + N₁ + 1) N₂,
        finiteBridgeLower delta (m + N₁) ≤
          Erdos1166.HLOZAppendixA.halfNegBinMass
            (p (Fin.last N₁)) (q 0) := by
  intro p hp q hq
  apply finiteBridgeLower_le_halfNegBinMass
  · apply coordinate_le_of_profileCorridor
    simpa [ProfileCorridor] using
      (mem_corridorProfiles.mp hp (Fin.last N₁))
  · apply coordinate_le_of_profileCorridor
    simpa [ProfileCorridor, Nat.add_assoc] using
      (mem_corridorProfiles.mp hq (0 : Fin (N₂ + 1)))
  · have hpbound :
        |centeredDeviation (m + N₁) (p (Fin.last N₁))| ≤
          (Erdos1166.HLOZLemmaA8.corridorRadius delta (m + N₁) : ℤ) := by
      simpa using mem_corridorProfiles.mp hp (Fin.last N₁)
    have hpow : ((m + N₁ : ℕ) : ℝ) ^ (1 + delta) ≤
        ((m + N₁ : ℕ) : ℝ) ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le
        (by exact_mod_cast (show 1 ≤ m + N₁ by omega)) (by linarith)
    have hfloor := Erdos1166.HLOZPropositionA7.corridorRadius_cast_le
      delta (m + N₁)
    have hr : Erdos1166.HLOZLemmaA8.corridorRadius delta (m + N₁) ≤
        (m + N₁) ^ 2 := by
      have hrR : (Erdos1166.HLOZLemmaA8.corridorRadius delta
          (m + N₁) : ℝ) ≤ ((m + N₁) ^ 2 : ℕ) := by
        simpa [Real.rpow_two, Nat.cast_add, Nat.cast_pow] using
          hfloor.trans hpow
      exact_mod_cast hrR
    have habs := hpbound
    rw [abs_le] at habs
    have hrZ : (Erdos1166.HLOZLemmaA8.corridorRadius delta
        (m + N₁) : ℤ) ≤ ((m + N₁ : ℕ) : ℤ) ^ 2 := by
      exact_mod_cast hr
    unfold centeredDeviation at habs
    have : (0 : ℤ) < p (Fin.last N₁) := by
      have hmZ : (0 : ℤ) < ((m + N₁ : ℕ) : ℤ) := by
        exact_mod_cast (show 0 < m + N₁ by omega)
      have hsqZ : (0 : ℤ) < ((m + N₁ : ℕ) : ℤ) ^ 2 :=
        sq_pos_of_pos hmZ
      omega
    exact_mod_cast this

/-- Any checked tail lower bound beginning at scale `cut` extends to the
literal source profile, with no assumption at the finitely many small
scales.  The lost factor is explicit and strictly positive: one canonical
parabolic prefix and one uniform negative-binomial bridge atom. -/
theorem source_halfNegBinPathSum_lower_of_tail
    {delta A : ℝ} {n cut : ℕ} (hcut : 3 ≤ cut) (hcutn : cut ≤ n)
    (hdelta : delta ≤ 1)
    (hA0 : 0 ≤ A)
    (hA : A ≤ halfNegBinPathSum
      (corridorProfiles delta cut (n - cut))) :
    finiteBridgeLower delta (cut - 1) *
        halfNegBinPathWeight (parabolicProfile 2 (cut - 3)) * A ≤
      halfNegBinPathSum (sourceProfiles delta n) := by
  have hbridge := finiteBridgeLower_uniform
    (delta := delta) hdelta (m := 2) (N₁ := cut - 3)
      (N₂ := n - cut) (by norm_num)
  have hsum := mul_halfNegBinPathSums_le_of_bridge hbridge
  have hp_mem : parabolicProfile 2 (cut - 3) ∈
      corridorProfiles delta 2 (cut - 3) :=
    parabolicProfile_mem_corridorProfiles _ _ _
  have hp_le : halfNegBinPathWeight (parabolicProfile 2 (cut - 3)) ≤
      halfNegBinPathSum (corridorProfiles delta 2 (cut - 3)) := by
    unfold halfNegBinPathSum
    exact Finset.single_le_sum
      (fun q hq ↦ halfNegBinPathWeight_nonneg_for_join q) hp_mem
  have hsum' : finiteBridgeLower delta (cut - 1) *
        halfNegBinPathSum (corridorProfiles delta 2 (cut - 3)) *
        halfNegBinPathSum (corridorProfiles delta cut (n - cut)) ≤
      halfNegBinPathSum (corridorProfiles delta 2 (n - 2)) := by
    have h₁ : 2 + (cut - 3) = cut - 1 := by omega
    have h₂ : cut - 1 + 1 = cut := by omega
    have h₃ : cut - 3 + 1 + (n - cut) = n - 2 := by omega
    rw [h₃] at hsum
    simpa only [h₁, h₂] using hsum
  have hpSum0 : 0 ≤
      halfNegBinPathSum (corridorProfiles delta 2 (cut - 3)) := by
    unfold halfNegBinPathSum
    exact Finset.sum_nonneg fun q hq ↦ halfNegBinPathWeight_nonneg_for_join q
  unfold sourceProfiles
  calc
    finiteBridgeLower delta (cut - 1) *
          halfNegBinPathWeight (parabolicProfile 2 (cut - 3)) * A ≤
        finiteBridgeLower delta (cut - 1) *
          halfNegBinPathSum (corridorProfiles delta 2 (cut - 3)) *
            halfNegBinPathSum (corridorProfiles delta cut (n - cut)) := by
      have hprod := mul_le_mul hp_le hA hA0 hpSum0
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hprod
        (finiteBridgeLower_pos delta (cut - 1)).le
    _ ≤ halfNegBinPathSum (corridorProfiles delta 2 (n - 2)) := hsum'

/-! ### Premise-free finite-block Proposition-A.7 source factor -/

/-- The exact tail factor obtained by combining the recursively composed
Lemma-A.8 Gaussian bound with the two finite local-limit losses in
Proposition A.7. -/
noncomputable def iteratedTailA7
    (rho delta : ℝ) (k n : ℕ) : ℝ :=
  let m := Erdos1166.HLOZLemmaA8.iteratedRhoStart rho (k + 1) n
  let e := max (3 - 2 * rho * (1 + delta)) (2 * delta)
  let D := 655360100 + (4 + 64 / (2 * delta))
  Real.exp (-pathNormalizationCost m (n - m) (hlozRadius delta m (n - m))) *
    Real.exp (-corridorComparisonCostBound m (n - m)
      (hlozRadius delta m (n - m))) *
      Real.exp (-(((k + 1 : ℕ) : ℝ) * D * (n : ℝ) ^ e))

theorem iteratedTailA7_pos (rho delta : ℝ) (k n : ℕ) :
    0 < iteratedTailA7 rho delta k n := by
  unfold iteratedTailA7
  positivity

/-- Every premise in the tail half-negative-binomial bound is discharged:
the Gaussian estimate comes from the finite A.8/A.12 iteration and the
radius budget holds because its lowest endpoint tends to infinity. -/
theorem eventually_iteratedTailA7_lower
    {rho delta : ℝ} (hrho0 : 0 < rho) (hrho1 : rho < 1)
    (hd0 : 0 < delta) (hd1 : delta ≤ 1 / 3)
    (hcritical : 1 < rho * (1 + delta)) (k : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      let m := Erdos1166.HLOZLemmaA8.iteratedRhoStart rho (k + 1) n
      3 ≤ m ∧ m ≤ n ∧
        iteratedTailA7 rho delta k n ≤
          halfNegBinPathSum (corridorProfiles delta m (n - m)) := by
  have hgauss :=
    Erdos1166.HLOZLemmaA8.eventually_iteratedRhoStart_hlozPathSum_lower
      hrho0 hrho1 hd0 hd1 hcritical k
  have hmTop := Erdos1166.HLOZLemmaA8.tendsto_iteratedRhoStart_atTop
    hrho0 (k + 1)
  have hmthree := hmTop.eventually (eventually_ge_atTop (3 : ℕ))
  have hbudget0 := eventually_hlozRadiusBudget
    (show delta < 1 by linarith)
  have hbudget := hmTop.eventually hbudget0
  filter_upwards [hgauss, hmthree, hbudget] with n hg hm3 hbud
  let m := Erdos1166.HLOZLemmaA8.iteratedRhoStart rho (k + 1) n
  refine ⟨by simpa [m] using hm3, hg.2.1, ?_⟩
  unfold iteratedTailA7
  apply hlozPathSum_corridor_transfer
    (start := Erdos1166.HLOZLemmaA8.iteratedRhoStart rho (k + 1) n)
    (N := n - Erdos1166.HLOZLemmaA8.iteratedRhoStart rho (k + 1) n)
    (show delta ≤ 1 by linarith) hg.1
    (hbud (n - Erdos1166.HLOZLemmaA8.iteratedRhoStart rho (k + 1) n))
  · exact hg.2.2
  · positivity

/-- The full source A7 factor.  It retains the exact, strictly positive
finite prefix and bridge factors instead of silently applying the sharp
local limit at scale two. -/
noncomputable def iteratedSourceA7
    (rho delta : ℝ) (k n : ℕ) : ℝ :=
  let m := Erdos1166.HLOZLemmaA8.iteratedRhoStart rho (k + 1) n
  finiteBridgeLower delta (m - 1) *
    halfNegBinPathWeight (parabolicProfile 2 (m - 3)) *
      iteratedTailA7 rho delta k n

theorem iteratedSourceA7_pos (rho delta : ℝ) (k n : ℕ) :
    0 < iteratedSourceA7 rho delta k n := by
  unfold iteratedSourceA7
  exact mul_pos
    (mul_pos (finiteBridgeLower_pos _ _)
      (halfNegBinPathWeight_parabolicProfile_pos (by norm_num)))
    (iteratedTailA7_pos _ _ _ _)

/-- Premise-free source-facing form of Proposition A.7.  This theorem has
exactly the type required to populate `EuclideanDiskSourceEstimates.A7_lower`:
no Gaussian, bridge, low-scale, or radius-budget premise remains. -/
theorem eventually_iteratedSourceA7_lower
    {rho delta : ℝ} (hrho0 : 0 < rho) (hrho1 : rho < 1)
    (hd0 : 0 < delta) (hd1 : delta ≤ 1 / 3)
    (hcritical : 1 < rho * (1 + delta)) (k : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      iteratedSourceA7 rho delta k n ≤
        halfNegBinPathSum (sourceProfiles delta n) := by
  filter_upwards [eventually_iteratedTailA7_lower
    hrho0 hrho1 hd0 hd1 hcritical k] with n hn
  unfold iteratedSourceA7
  exact source_halfNegBinPathSum_lower_of_tail hn.1 hn.2.1
    (show delta ≤ 1 by linarith) (iteratedTailA7_pos _ _ _ _).le hn.2.2

/-! ### Numerical Appendix-A specialization -/

/-- The balanced HLOZ corridor exponent, `max(1-2δ,3δ)=3/5`. -/
noncomputable def appendixProfileDelta : ℝ := 1 / 5

/-- A rational block ratio close enough to one that the A.8 block exponent
fits under the repository's `3/5 + appendixEpsilon/3` budget. -/
noncomputable def appendixBlockRho : ℝ := 999 / 1000

/-- A conservative finite last index.  Besides putting the recursive start
below the `3/5` block threshold, this choice makes it at most an eighth-power
scale.  Consequently the deliberately crude finite prefix and bridge costs
are themselves lower-order than the final Appendix exponent. -/
def appendixBlockIndex : ℕ := 6992

theorem appendixBlockRho_pow_succ_index_lt :
    appendixBlockRho ^ (appendixBlockIndex + 1) < (3 : ℝ) / 5 := by
  have hbern : 1 + (6993 : ℝ) * (1 / 999) ≤
      (1 + (1 / 999 : ℝ)) ^ (6993 : ℕ) :=
    one_add_mul_le_pow (by norm_num) 6993
  have hnumeric : (5 : ℝ) / 3 < 1 + 6993 * (1 / 999) := by norm_num
  have hden : (5 : ℝ) / 3 <
      (1 + (1 / 999 : ℝ)) ^ (6993 : ℕ) := hnumeric.trans_le hbern
  have hinv := one_div_lt_one_div_of_lt
    (by norm_num : (0 : ℝ) < 5 / 3) hden
  unfold appendixBlockRho appendixBlockIndex
  norm_num only [Nat.reduceAdd]
  calc
    ((999 : ℝ) / 1000) ^ (6993 : ℕ) =
        1 / (1 + (1 / 999 : ℝ)) ^ (6993 : ℕ) := by
      rw [← one_div_pow]
      congr 1
      norm_num
    _ < 1 / ((5 : ℝ) / 3) := hinv
    _ = 3 / 5 := by norm_num

theorem appendixBlockRho_pow_succ_index_le_one_eighth :
    appendixBlockRho ^ (appendixBlockIndex + 1) ≤ (1 : ℝ) / 8 := by
  have hbern : 1 + (6993 : ℝ) * (1 / 999) ≤
      (1 + (1 / 999 : ℝ)) ^ (6993 : ℕ) :=
    one_add_mul_le_pow (by norm_num) 6993
  have hden : (8 : ℝ) ≤
      (1 + (1 / 999 : ℝ)) ^ (6993 : ℕ) := by
    calc
      (8 : ℝ) = 1 + 6993 * (1 / 999) := by norm_num
      _ ≤ (1 + (1 / 999 : ℝ)) ^ (6993 : ℕ) := hbern
  have hinv := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 8) hden
  unfold appendixBlockRho appendixBlockIndex
  norm_num only [Nat.reduceAdd]
  calc
    ((999 : ℝ) / 1000) ^ (6993 : ℕ) =
        1 / (1 + (1 / 999 : ℝ)) ^ (6993 : ℕ) := by
      rw [← one_div_pow]
      congr 1
      norm_num
    _ ≤ 1 / 8 := hinv

theorem appendix_block_exponent_eq :
    max (3 - 2 * appendixBlockRho * (1 + appendixProfileDelta))
      (2 * appendixProfileDelta) = (753 : ℝ) / 1250 := by
  norm_num [appendixBlockRho, appendixProfileDelta, max_eq_left]

theorem appendix_block_exponent_lt_target :
    (753 : ℝ) / 1250 < 3 / 5 + (1 / 100 : ℝ) / 3 := by
  norm_num

/-- The concrete, strictly positive A7 value used at the Appendix-A
parameters.  Its finite recursively cut blocks are the integer-safe
implementation of the literal endpoint list `q₀,…,qₖ,n`. -/
noncomputable def appendixSourceA7 (n : ℕ) : ℝ :=
  iteratedSourceA7 appendixBlockRho appendixProfileDelta
    appendixBlockIndex n

theorem appendixSourceA7_pos (n : ℕ) : 0 < appendixSourceA7 n := by
  exact iteratedSourceA7_pos _ _ _ _

/-- Final premise-free field value for
`EuclideanDiskSourceEstimates.A7_lower`. -/
theorem eventually_appendixSourceA7_lower :
    ∀ᶠ n : ℕ in atTop,
      appendixSourceA7 n ≤
        halfNegBinPathSum (sourceProfiles appendixProfileDelta n) := by
  exact eventually_iteratedSourceA7_lower
    (rho := appendixBlockRho) (delta := appendixProfileDelta)
    (by norm_num [appendixBlockRho])
    (by norm_num [appendixBlockRho])
    (by norm_num [appendixProfileDelta])
    (by norm_num [appendixProfileDelta])
    (by norm_num [appendixBlockRho, appendixProfileDelta])
    appendixBlockIndex

/-- Probability of returning downwards from the exceptional top state of the
auxiliary chain in HLOZ Lemma A.6. -/
noncomputable def topReturnProbability (n : ℕ) : ℝ :=
  (3 * Real.log (n : ℝ)) / (1 + 3 * Real.log (n : ℝ))

theorem topReturnProbability_pos {n : ℕ} (hn : 2 ≤ n) :
    0 < topReturnProbability n := by
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  unfold topReturnProbability
  positivity

theorem topReturnProbability_lt_one {n : ℕ} (hn : 2 ≤ n) :
    topReturnProbability n < 1 := by
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  unfold topReturnProbability
  rw [div_lt_one (by positivity)]
  linarith

theorem one_sub_topReturnProbability {n : ℕ} (hn : 2 ≤ n) :
    1 - topReturnProbability n =
      1 / (1 + 3 * Real.log (n : ℝ)) := by
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  unfold topReturnProbability
  field_simp
  ring

theorem topFailure_success_ratio {n : ℕ} (hn : 2 ≤ n) :
    (1 - topReturnProbability n) / topReturnProbability n =
      1 / (3 * Real.log (n : ℝ)) := by
  rw [one_sub_topReturnProbability hn]
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  unfold topReturnProbability
  field_simp

/-- The exact negative-binomial atom for the number `t` of top-state
upcrossings produced by `b` visits to level `n`. -/
noncomputable def topNegBinMass (n b t : ℕ) : ℝ :=
  (Nat.choose (b + t - 1) t : ℝ) * topReturnProbability n ^ b *
    (1 - topReturnProbability n) ^ t

theorem topNegBinMass_eq_nbMass (n b t : ℕ) :
    topNegBinMass n b t =
      Erdos1166.HLOZTerminalNegBin.nbMass (topReturnProbability n)
        (1 - topReturnProbability n) b t := by
  rfl

theorem topNegBinMass_nonneg {n b t : ℕ} (hn : 2 ≤ n) :
    0 ≤ topNegBinMass n b t := by
  unfold topNegBinMass
  have hp0 := (topReturnProbability_pos hn).le
  have hp1 := (topReturnProbability_lt_one hn).le
  positivity

theorem topNegBinMass_pos {n b t : ℕ} (hn : 2 ≤ n) (hb : 0 < b) :
    0 < topNegBinMass n b t := by
  unfold topNegBinMass
  have hc : 0 < Nat.choose (b + t - 1) t := Nat.choose_pos (by omega)
  have hp0 := topReturnProbability_pos hn
  have hp1 := topReturnProbability_lt_one hn
  positivity

/-- Literal terminal constraint in the definition of `H⁰_n(\bar m)` in
HLOZ Lemma A.6.  Writing it as a predicate on naturals avoids any rounding
convention: the comparison with the real lower endpoint is exact. -/
def TerminalAdmissible (n : ℕ) (delta : ℝ) (t : ℕ) : Prop :=
  (2 * (n : ℝ) ^ 2 - (n : ℝ) ^ (1 + delta)) /
      (3 * Real.log (n : ℝ)) ≤ (t : ℝ) ∧
    t ≤ n ^ 3

/-- The finite set of terminal upcrossing counts allowed by HLOZ. -/
noncomputable def terminalCounts (n : ℕ) (delta : ℝ) : Finset ℕ :=
  by
    classical
    exact (Finset.range (n ^ 3 + 1)).filter (TerminalAdmissible n delta)

@[simp] theorem mem_terminalCounts {n t : ℕ} {delta : ℝ} :
    t ∈ terminalCounts n delta ↔ TerminalAdmissible n delta t := by
  classical
  simp [terminalCounts, TerminalAdmissible]

/-- Total top-transition mass satisfying the terminal constraint. -/
noncomputable def terminalMass (n : ℕ) (delta : ℝ) (b : ℕ) : ℝ :=
  ∑ t ∈ terminalCounts n delta, topNegBinMass n b t

theorem terminalMass_nonneg {n b : ℕ} (delta : ℝ) (hn : 2 ≤ n) :
    0 ≤ terminalMass n delta b := by
  unfold terminalMass
  exact Finset.sum_nonneg fun t ht ↦ topNegBinMass_nonneg hn

theorem topNegBinMass_le_terminalMass {n b t : ℕ} {delta : ℝ}
    (hn : 2 ≤ n) (ht : TerminalAdmissible n delta t) :
    topNegBinMass n b t ≤ terminalMass n delta b := by
  unfold terminalMass
  exact Finset.single_le_sum
    (s := terminalCounts n delta) (f := fun j ↦ topNegBinMass n b j)
    (fun j hj ↦ topNegBinMass_nonneg hn) (mem_terminalCounts.mpr ht)

theorem terminalMass_pos_of_mem {n b t : ℕ} {delta : ℝ}
    (hn : 2 ≤ n) (hb : 0 < b) (ht : TerminalAdmissible n delta t) :
    0 < terminalMass n delta b := by
  exact lt_of_lt_of_le (topNegBinMass_pos hn hb)
    (topNegBinMass_le_terminalMass hn ht)

/-- Exact initial factor `P¹(u₂ = b)`.  The paper explicitly notes the
special value `P¹(u₂ = 1) = 1/4`; for an exact profile atom the argument
must be its first coordinate `m₂`. -/
noncomputable def initialUpcrossingMass (b : ℕ) : ℝ :=
  Erdos1166.HLOZAppendixA.halfNegBinMass 1 b

theorem initialUpcrossingMass_eq (b : ℕ) :
    initialUpcrossingMass b = 1 / (2 : ℝ) ^ (b + 1) := by
  simp [initialUpcrossingMass, Erdos1166.HLOZAppendixA.halfNegBinMass,
    add_comm]

@[simp] theorem initialUpcrossingMass_one : initialUpcrossingMass 1 = 1 / 4 := by
  rw [initialUpcrossingMass_eq]
  norm_num

/-- Explicit uniform initial factor on the source corridor.  Unlike the
paper's asymptotic notation, this records the dependence on the finitely many
allowed values of `m₂`. -/
noncomputable def sourceInitialLower (delta : ℝ) : ℝ :=
  1 / (2 : ℝ) ^
    ((8 + Erdos1166.HLOZLemmaA8.corridorRadius delta 2) + 1)

theorem sourceInitialLower_nonneg (delta : ℝ) : 0 ≤ sourceInitialLower delta := by
  unfold sourceInitialLower
  positivity

theorem sourceInitialLower_pos (delta : ℝ) : 0 < sourceInitialLower delta := by
  unfold sourceInitialLower
  positivity

theorem sourceInitialLower_le {delta : ℝ} {n : ℕ}
    {q : NatPath (n - 2)} (hq : q ∈ sourceProfiles delta n) :
    sourceInitialLower delta ≤ initialUpcrossingMass (q 0) := by
  have hcorr := (mem_sourceProfiles.mp hq) (0 : Fin ((n - 2) + 1))
  have hcap : q 0 ≤ 8 + Erdos1166.HLOZLemmaA8.corridorRadius delta 2 := by
    simpa using coordinate_le_of_profileCorridor hcorr
  rw [sourceInitialLower, initialUpcrossingMass_eq]
  exact one_div_le_one_div_of_le (by positivity)
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.add_le_add_right hcap 1))

theorem halfNegBinPathWeight_nonneg {N : ℕ} (q : NatPath N) :
    0 ≤ halfNegBinPathWeight q := by
  unfold halfNegBinPathWeight
  exact Finset.prod_nonneg fun i hi ↦
    Erdos1166.HLOZAppendixA.halfNegBinMass_nonneg _ _

/-- Exact mass assigned by the auxiliary killed birth-death chain to one
successful profile `(m₂, ..., mₙ)`, after summing the terminal coordinate. -/
noncomputable def successfulProfileWeight {N : ℕ} (n : ℕ) (delta : ℝ)
    (q : NatPath N) : ℝ :=
  initialUpcrossingMass (q 0) * halfNegBinPathWeight q *
    terminalMass n delta (q (Fin.last N))

/-- Sum of exact successful-profile masses over a finite profile family. -/
noncomputable def successfulProfilePartition {N : ℕ} (n : ℕ) (delta : ℝ)
    (Q : Finset (NatPath N)) : ℝ :=
  ∑ q ∈ Q, successfulProfileWeight n delta q

/-- The profile partition specialized to the source family
`M_n(δ) = {(m₂, ..., mₙ)}`. -/
noncomputable def sourceProfilePartition (n : ℕ) (delta : ℝ) : ℝ :=
  successfulProfilePartition n delta (sourceProfiles delta n)

theorem source_last_coordinate_is_scale_n {n : ℕ} (hn : 2 ≤ n) :
    2 + ((Fin.last (n - 2) : Fin ((n - 2) + 1)) : ℕ) = n := by
  simp
  omega

/-- A uniform lower bound for the exceptional top transition once its
incoming count lies in the numerical range supplied by the source corridor.
The proof uses exact negative-binomial factorial moments through order four,
the one-sided moment estimate in `HLOZTerminalNegBin`, and a first-moment
bound for the discarded tail above `n³`. -/
theorem top_terminalMass_lower_of_bounds {n b : ℕ} {delta : ℝ}
    (hn : 64 ≤ n)
    (hbn : n ^ 2 ≤ b) (hbupper : b ≤ 3 * n ^ 2)
    (hbsource : 2 * (n : ℝ) ^ 2 - (n : ℝ) ^ (1 + delta) ≤ b) :
    1 / 64 ≤ terminalMass n delta b := by
  have hn2 : 2 ≤ n := by omega
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hn64R : (64 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog0 : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn2)
  have hlog1 : 1 ≤ Real.log (n : ℝ) := by
    rw [Real.le_log_iff_exp_le hnR]
    exact Real.exp_one_lt_three.le.trans (by exact_mod_cast (show 3 ≤ n by omega))
  have hlogle : Real.log (n : ℝ) ≤ n := by
    exact (Real.log_le_sub_one_of_pos hnR).trans (by linarith)
  have hden : 0 < 3 * Real.log (n : ℝ) := by positivity
  have hp0 := topReturnProbability_pos hn2
  have hp1 := topReturnProbability_lt_one hn2
  have hq0 : 0 ≤ 1 - topReturnProbability n := sub_nonneg.mpr hp1.le
  have hq1 : 1 - topReturnProbability n < 1 := by linarith
  have hb1 : 1 ≤ b := le_trans (by nlinarith : 1 ≤ n ^ 2) hbn
  have hr1 :
      (1 - topReturnProbability n) / topReturnProbability n ≤ 1 := by
    rw [topFailure_success_ratio hn2]
    apply (div_le_one hden).2
    linarith
  have hbr :
      13 ≤ (b : ℝ) *
        ((1 - topReturnProbability n) / topReturnProbability n) := by
    rw [topFailure_success_ratio hn2]
    simp only [one_div, ← div_eq_mul_inv]
    apply (le_div_iff₀ hden).2
    have h39 : (39 : ℝ) * n ≤ (n : ℝ) ^ 2 := by nlinarith
    have hbnR : (n : ℝ) ^ 2 ≤ b := by exact_mod_cast hbn
    nlinarith
  have hL :
      (2 * (n : ℝ) ^ 2 - (n : ℝ) ^ (1 + delta)) /
          (3 * Real.log (n : ℝ)) ≤
        (b : ℝ) *
          ((1 - topReturnProbability n) / topReturnProbability n) := by
    rw [topFailure_success_ratio hn2]
    simp only [one_div, ← div_eq_mul_inv]
    exact (div_le_div_iff_of_pos_right hden).2 hbsource
  have hmu : (b : ℝ) / (3 * Real.log (n : ℝ)) ≤ (n : ℝ) ^ 2 := by
    apply (div_le_iff₀ hden).2
    have hbupperR : (b : ℝ) ≤ 3 * (n : ℝ) ^ 2 := by exact_mod_cast hbupper
    nlinarith
  have htail :
      ((b : ℝ) *
          ((1 - topReturnProbability n) / topReturnProbability n)) /
          (n ^ 3 : ℕ) ≤ 1 / 64 := by
    rw [topFailure_success_ratio hn2]
    calc
      ((b : ℝ) * (1 / (3 * Real.log (n : ℝ)))) / (n ^ 3 : ℕ) =
          ((b : ℝ) / (3 * Real.log (n : ℝ))) / (n : ℝ) ^ 3 := by
            push_cast
            ring
      _ ≤ (n : ℝ) ^ 2 / (n : ℝ) ^ 3 :=
        div_le_div_of_nonneg_right hmu (by positivity)
      _ = 1 / (n : ℝ) := by
        field_simp
      _ ≤ 1 / 64 := one_div_le_one_div_of_le (by norm_num) hn64R
  have hfinite := Erdos1166.HLOZTerminalNegBin.nb_interval_lower
    (p := topReturnProbability n) (q := 1 - topReturnProbability n)
    (b := b) (N := n ^ 3)
    (L := (2 * (n : ℝ) ^ 2 - (n : ℝ) ^ (1 + delta)) /
      (3 * Real.log (n : ℝ)))
    hb1 hp0 hq0 hq1 (by ring) hr1 hbr
      (one_le_pow₀ (by exact_mod_cast (show 1 ≤ n by omega))) hL htail
  calc
    1 / 64 ≤ ∑ t ∈ Finset.range (n ^ 3 + 1),
        if (2 * (n : ℝ) ^ 2 - (n : ℝ) ^ (1 + delta)) /
              (3 * Real.log (n : ℝ)) ≤ (t : ℝ) then
          Erdos1166.HLOZTerminalNegBin.nbMass (topReturnProbability n)
            (1 - topReturnProbability n) b t else 0 := hfinite
    _ = terminalMass n delta b := by
      rw [terminalMass, terminalCounts]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro t ht
      have htupper : t ≤ n ^ 3 := by simpa using (Finset.mem_range.mp ht)
      rw [topNegBinMass_eq_nbMass]
      simp only [TerminalAdmissible, htupper, and_true]

/-- The source corridor itself supplies all three numerical hypotheses of
`top_terminalMass_lower_of_bounds`.  This is the uniform endpoint estimate
used in HLOZ Lemma A.6, with explicit constant `1/64`. -/
theorem source_terminalMass_lower {n : ℕ} {delta : ℝ}
    (hn : 64 ≤ n) (hdelta : delta ≤ 1)
    (q : NatPath (n - 2)) (hq : q ∈ sourceProfiles delta n) :
    1 / 64 ≤ terminalMass n delta (q (Fin.last (n - 2))) := by
  let b := q (Fin.last (n - 2))
  let R := Erdos1166.HLOZLemmaA8.corridorRadius delta n
  have hn2 : 2 ≤ n := by omega
  have hscale := source_last_coordinate_is_scale_n hn2
  have hcorr := (mem_sourceProfiles.mp hq) (Fin.last (n - 2))
  have hcorrN : |centeredDeviation n b| ≤ (R : ℤ) := by
    simpa only [b, R, hscale] using hcorr
  rw [abs_le] at hcorrN
  unfold centeredDeviation at hcorrN
  have hlowR : -(R : ℝ) ≤ (b : ℝ) - 2 * (n : ℝ) ^ 2 := by
    exact_mod_cast hcorrN.1
  have huppR : (b : ℝ) - 2 * (n : ℝ) ^ 2 ≤ (R : ℝ) := by
    exact_mod_cast hcorrN.2
  have hRle : (R : ℝ) ≤ (n : ℝ) ^ (1 + delta) := by
    exact corridorRadius_cast_le delta n
  have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hrpowle : (n : ℝ) ^ (1 + delta) ≤ (n : ℝ) ^ 2 := by
    calc
      (n : ℝ) ^ (1 + delta) ≤ (n : ℝ) ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hn1R (by linarith)
      _ = (n : ℝ) ^ 2 := Real.rpow_two _
  have hbsource :
      2 * (n : ℝ) ^ 2 - (n : ℝ) ^ (1 + delta) ≤ (b : ℝ) := by
    linarith
  have hbnR : (n : ℝ) ^ 2 ≤ b := by linarith
  have hbupperR : (b : ℝ) ≤ 3 * (n : ℝ) ^ 2 := by linarith
  have hbn : n ^ 2 ≤ b := by exact_mod_cast hbnR
  have hbupper : b ≤ 3 * n ^ 2 := by exact_mod_cast hbupperR
  exact top_terminalMass_lower_of_bounds hn hbn hbupper hbsource

/-- Fully expanded formula for one source profile.  This displays every
ordinary transition and every admissible exceptional top transition. -/
theorem successfulProfileWeight_source_eq {n : ℕ} (delta : ℝ)
    (q : NatPath (n - 2)) :
    successfulProfileWeight n delta q =
      Erdos1166.HLOZAppendixA.halfNegBinMass 1 (q 0) *
        (∏ i : Fin (n - 2),
          Erdos1166.HLOZAppendixA.halfNegBinMass
            (q i.castSucc) (q i.succ)) *
        (∑ t ∈ terminalCounts n delta,
          topNegBinMass n (q (Fin.last (n - 2))) t) := by
  rw [successfulProfileWeight]
  rfl

/-- The same profile partition before summing out the terminal coordinate.
This is the literal finite product in the Markov-chain proof of Lemma A.6. -/
noncomputable def expandedProfilePartition {N : ℕ} (n : ℕ) (delta : ℝ)
    (Q : Finset (NatPath N)) : ℝ :=
  ∑ q ∈ Q, ∑ t ∈ terminalCounts n delta,
    initialUpcrossingMass (q 0) * halfNegBinPathWeight q *
      topNegBinMass n (q (Fin.last N)) t

/-- Summing the terminal negative-binomial atom gives exactly the compact
profile weight. -/
theorem expandedProfilePartition_eq {N n : ℕ} (delta : ℝ)
    (Q : Finset (NatPath N)) :
    expandedProfilePartition n delta Q = successfulProfilePartition n delta Q := by
  unfold expandedProfilePartition successfulProfilePartition successfulProfileWeight
  apply Finset.sum_congr rfl
  intro q hq
  unfold terminalMass
  rw [Finset.mul_sum]

theorem successfulProfilePartition_nonneg {N n : ℕ} (delta : ℝ)
    (hn : 2 ≤ n) (Q : Finset (NatPath N)) :
    0 ≤ successfulProfilePartition n delta Q := by
  unfold successfulProfilePartition successfulProfileWeight
  exact Finset.sum_nonneg fun q hq ↦ by
    exact mul_nonneg
      (mul_nonneg (by rw [initialUpcrossingMass_eq]; positivity)
        (halfNegBinPathWeight_nonneg q))
      (terminalMass_nonneg (b := q (Fin.last N)) delta hn)

/-- The purely finite content of the endpoint comparison in Lemma A.6:
uniform lower bounds on the initial and exceptional top transitions multiply
the ordinary half-negative-binomial path sum. -/
theorem profilePartition_lower_of_endpoints {N n : ℕ} (delta : ℝ)
    (Q : Finset (NatPath N)) {cInitial cTerminal : ℝ}
    (hcInitial : 0 ≤ cInitial) (hcTerminal : 0 ≤ cTerminal)
    (hinitial : ∀ q ∈ Q, cInitial ≤ initialUpcrossingMass (q 0))
    (hterminal : ∀ q ∈ Q,
      cTerminal ≤ terminalMass n delta (q (Fin.last N))) :
    (cInitial * cTerminal) * halfNegBinPathSum Q ≤
      successfulProfilePartition n delta Q := by
  unfold halfNegBinPathSum successfulProfilePartition
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q hq
  rw [successfulProfileWeight]
  have hw : 0 ≤ halfNegBinPathWeight q := halfNegBinPathWeight_nonneg q
  have hi : 0 ≤ initialUpcrossingMass (q 0) := by
    rw [initialUpcrossingMass_eq]
    positivity
  calc
    (cInitial * cTerminal) * halfNegBinPathWeight q =
        (cInitial * halfNegBinPathWeight q) * cTerminal := by ring
    _ ≤ (initialUpcrossingMass (q 0) * halfNegBinPathWeight q) * cTerminal :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hinitial q hq) hw) hcTerminal
    _ ≤ initialUpcrossingMass (q 0) * halfNegBinPathWeight q *
        terminalMass n delta (q (Fin.last N)) := by
      exact mul_le_mul_of_nonneg_left (hterminal q hq) (mul_nonneg hi hw)

/-- Direct consumer for any sharpened final form of Proposition A.7. -/
theorem profilePartition_lower_of_propositionA7 {N n : ℕ} (delta : ℝ)
    (Q : Finset (NatPath N)) {A cInitial cTerminal : ℝ}
    (hA : 0 ≤ A) (hcInitial : 0 ≤ cInitial) (hcTerminal : 0 ≤ cTerminal)
    (hinitial : ∀ q ∈ Q, cInitial ≤ initialUpcrossingMass (q 0))
    (hterminal : ∀ q ∈ Q,
      cTerminal ≤ terminalMass n delta (q (Fin.last N)))
    (hA7 : A ≤ halfNegBinPathSum Q) :
    (cInitial * cTerminal) * A ≤ successfulProfilePartition n delta Q := by
  exact (mul_le_mul_of_nonneg_left hA7 (by positivity)).trans
    (profilePartition_lower_of_endpoints delta Q hcInitial hcTerminal hinitial hterminal)

/-- Source-specialized Proposition-A.7 consumer.  The initial transition is
discharged by the proved finite `m₂` bound, so only the source's elementary
uniform estimate for the exceptional top transition remains. -/
theorem sourceProfilePartition_lower_of_propositionA7 {n : ℕ} (delta : ℝ)
    {A cTerminal : ℝ} (hA : 0 ≤ A) (hcTerminal : 0 ≤ cTerminal)
    (hterminal : ∀ q ∈ sourceProfiles delta n,
      cTerminal ≤ terminalMass n delta (q (Fin.last (n - 2))))
    (hA7 : A ≤ halfNegBinPathSum (sourceProfiles delta n)) :
    (sourceInitialLower delta * cTerminal) * A ≤ sourceProfilePartition n delta := by
  unfold sourceProfilePartition
  exact profilePartition_lower_of_propositionA7 delta (sourceProfiles delta n)
    hA (sourceInitialLower_nonneg delta) hcTerminal
    (fun q hq ↦ sourceInitialLower_le hq) hterminal hA7

/-- Proposition A.7 consumer with both endpoint factors discharged.  In
particular, no premise representing the source's terminal negative-binomial
estimate remains. -/
theorem sourceProfilePartition_lower_of_propositionA7_terminal
    {n : ℕ} (delta : ℝ) {A : ℝ}
    (hn : 64 ≤ n) (hdelta : delta ≤ 1) (hA : 0 ≤ A)
    (hA7 : A ≤ halfNegBinPathSum (sourceProfiles delta n)) :
    (sourceInitialLower delta * (1 / 64)) * A ≤
      sourceProfilePartition n delta := by
  exact sourceProfilePartition_lower_of_propositionA7 delta hA (by norm_num)
    (fun q hq ↦ source_terminalMass_lower hn hdelta q hq) hA7

/-- Consumer for the currently proved Gaussian-transfer interface in
`Erdos1166HLOZPropositionA7`. -/
theorem profilePartition_lower_of_gaussian {start N n : ℕ}
    (delta : ℝ) (Q : Finset (NatPath N)) {G R C cInitial cTerminal : ℝ}
    (hstart : 0 < start) (hG : 0 ≤ G) (hR : 0 ≤ R)
    (hcInitial : 0 ≤ cInitial) (hcTerminal : 0 ≤ cTerminal)
    (hb : ∀ q ∈ Q, ∀ i : Fin N, 2 ≤ q i.castSucc)
    (hd : ∀ q ∈ Q, ∀ i : Fin N,
      4 * Nat.dist (q i.castSucc) (q i.succ) ≤ q i.castSucc)
    (hRatio : ∀ q ∈ Q, R ≤ pathNormalizationRatio start N q)
    (hCost : ∀ q ∈ Q, pathComparisonCost start N q ≤ C)
    (hGaussian : G ≤ centeredGaussianPathSum start N Q)
    (hinitial : ∀ q ∈ Q, cInitial ≤ initialUpcrossingMass (q 0))
    (hterminal : ∀ q ∈ Q,
      cTerminal ≤ terminalMass n delta (q (Fin.last N))) :
    (cInitial * cTerminal) * (R * Real.exp (-C) * G) ≤
      successfulProfilePartition n delta Q := by
  apply profilePartition_lower_of_propositionA7 delta Q
  · positivity
  · exact hcInitial
  · exact hcTerminal
  · exact hinitial
  · exact hterminal
  · exact halfNegBinPathSum_lower_of_gaussian Q hstart hG hR hb hd hRatio hCost hGaussian

/-! ## The sole random-walk comparison interface in Lemma A.6 -/

open MeasureTheory Set

/-- Union of the mutually exclusive actual-walk events realizing the
profiles in `Q`. -/
def successfulProfileEvent {Omega : Type*} {N : ℕ} (Q : Finset (NatPath N))
    (A : NatPath N → Set Omega) : Set Omega :=
  ⋃ q ∈ Q, A q

/-- Once the annular entry/exit and embedded-chain Harnack comparison has
given a pointwise lower bound for every profile atom, finite additivity gives
the corresponding lower bound for their union.  Thus `hAnnulus` is exactly
the killed-walk/Harnack input left outside the finite profile calculation. -/
theorem annular_profile_union_lower
    {Omega : Type*} [MeasurableSpace Omega] {N n : ℕ}
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (delta : ℝ) (Q : Finset (NatPath N)) (A : NatPath N → Set Omega)
    {cAnnulus : ℝ} (hcAnnulus : 0 ≤ cAnnulus)
    (hA : ∀ q ∈ Q, MeasurableSet (A q))
    (hdisjoint : Set.PairwiseDisjoint (↑Q : Set (NatPath N)) A)
    (hAnnulus : ∀ q ∈ Q,
      cAnnulus * successfulProfileWeight n delta q ≤ mu.real (A q)) :
    cAnnulus * successfulProfilePartition n delta Q ≤
      mu.real (successfulProfileEvent Q A) := by
  rw [successfulProfilePartition, Finset.mul_sum]
  calc
    ∑ q ∈ Q, cAnnulus * successfulProfileWeight n delta q ≤
        ∑ q ∈ Q, mu.real (A q) := by
      exact Finset.sum_le_sum fun q hq ↦ hAnnulus q hq
    _ = mu.real (successfulProfileEvent Q A) := by
      rw [successfulProfileEvent,
        measureReal_biUnion_finset hdisjoint hA]

/-- Proposition A.7 plus the exact terminal factor and the annular comparison
give the one-site first-moment lower bound used in Lemma A.4. -/
theorem annular_firstMoment_lower_of_propositionA7
    {Omega : Type*} [MeasurableSpace Omega] {N n : ℕ}
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (delta : ℝ) (Q : Finset (NatPath N)) (Aevent : NatPath N → Set Omega)
    {A7 cInitial cTerminal cAnnulus : ℝ}
    (hA7nonneg : 0 ≤ A7) (hcInitial : 0 ≤ cInitial)
    (hcTerminal : 0 ≤ cTerminal)
    (hcAnnulus : 0 ≤ cAnnulus)
    (hinitial : ∀ q ∈ Q, cInitial ≤ initialUpcrossingMass (q 0))
    (hterminal : ∀ q ∈ Q,
      cTerminal ≤ terminalMass n delta (q (Fin.last N)))
    (hA7 : A7 ≤ halfNegBinPathSum Q)
    (hMeasurable : ∀ q ∈ Q, MeasurableSet (Aevent q))
    (hdisjoint : Set.PairwiseDisjoint (↑Q : Set (NatPath N)) Aevent)
    (hAnnulus : ∀ q ∈ Q,
      cAnnulus * successfulProfileWeight n delta q ≤ mu.real (Aevent q)) :
    cAnnulus * ((cInitial * cTerminal) * A7) ≤
      mu.real (successfulProfileEvent Q Aevent) := by
  exact (mul_le_mul_of_nonneg_left
      (profilePartition_lower_of_propositionA7 delta Q hA7nonneg hcInitial hcTerminal
        hinitial hterminal hA7) hcAnnulus).trans
    (annular_profile_union_lower mu delta Q Aevent hcAnnulus
      hMeasurable hdisjoint hAnnulus)

end Erdos1166.HLOZAppendixAFirstMoment
