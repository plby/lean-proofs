import ErdosProblems.Erdos722.Core
import ErdosProblems.Erdos722.CertificateAssembly
import ErdosProblems.Erdos722.SlowRotationBanks

namespace Erdos722

open Finset Filter
open Erdos722.RootedEmbedding
open Erdos722.ExchangePattern
open Erdos722.SpecialCliqueCandidates
open Erdos722.GeneratorAsymptotic
open Erdos722.Typicality

noncomputable section

/-- A single fixed exponent denominator large enough for all finite
patterns used in the Section 6 focusing certificate. -/
def sectionSixSampleDen {k r : ℕ} (hrk : r < k) : ℕ :=
  sectionSixPatternDen k r

/-- Fixed number of colour-coordinate roles used by the simultaneous
rotation construction, apart from the common rotation-bank factor. -/
def sectionSixColorLoadCoefficient {k r : ℕ} (hrk : r < k) : ℕ :=
  let E := ExchangeEmbedding.fullExchangeData hrk
  2 + 2 * (E.pattern.freeEdges.card +
    (CoverClique.coverPattern k r).freeEdges.card +
    (E.eliminationPattern
      (ExchangeEmbedding.fullExchangeRootEdge hrk)).freeEdges.card +
    (CoverClique.coverPattern k r).freeEdges.card) +
    (remainingBlocks E).card

lemma sectionSixSampleDen_bounds {k r : ℕ} (hr : 1 < r) (hrk : r < k) :
    let E := ExchangeEmbedding.fullExchangeData hrk
    let e₀ := ExchangeEmbedding.fullExchangeRootEdge hrk
    let d := sectionSixSampleDen hrk
    Nat.choose k r < d ∧
    E.pattern.freeEdges.card < d ∧
    2 * (CoverClique.coverPattern k r).freeEdges.card < d ∧
    (E.eliminationPattern e₀).freeEdges.card < d ∧
    (CoverClique.coverPattern k r).freeEdges.card < d ∧
    (3 * rhoDen k r) *
        (CoverClique.coverPattern k r).freeEdges.card < d ∧
    Nat.choose k r *
        (Nat.choose k r - 1 + (remainingBlocks E).card) < d := by
  simp only [sectionSixSampleDen, sectionSixPatternDen, dif_pos hrk]
  have hchoose : 0 < Nat.choose k r := Nat.choose_pos hrk.le
  have hrho : 0 < rhoDen k r := by
    simp [rhoDen, cliqueSize, hchoose]
  omega

lemma rhoDen_lt_sectionSixSampleDen {k r : ℕ} (hrk : r < k) :
    rhoDen k r < sectionSixSampleDen hrk := by
  simp only [sectionSixSampleDen, sectionSixPatternDen, dif_pos hrk]
  omega

lemma freeEdge_card (P : RootedPattern v r)
    (i : Fin P.freeEdges.card) :
    ((P.freeEdges.equivFin.symm i).1).card = r := by
  exact P.uniform _ (Finset.mem_filter.mp
    ((P.freeEdges.equivFin.symm i).2)).1

lemma freeEdge_inter_root_card_lt (P : RootedPattern v r)
    (i : Fin P.freeEdges.card) :
    (((P.freeEdges.equivFin.symm i).1 ∩ P.root).card < r) := by
  let e := (P.freeEdges.equivFin.symm i).1
  have he := (P.freeEdges.equivFin.symm i).2
  have hecard : e.card = r := P.uniform e (Finset.mem_filter.mp he).1
  have henot : ¬ e ⊆ P.root := (Finset.mem_filter.mp he).2
  have hinter : (e ∩ P.root).card ≤ r := by
    exact (Finset.card_le_card Finset.inter_subset_left).trans_eq hecard
  by_contra hnot
  change ¬ (e ∩ P.root).card < r at hnot
  have heq : (e ∩ P.root).card = r := by omega
  apply henot
  apply Finset.inter_eq_left.mp
  apply Finset.eq_of_subset_of_card_le Finset.inter_subset_left
  rw [hecard, heq]

lemma localDegree_rotateFamily (sigma : Equiv.Perm (Fin n))
    (K : Finset (Finset (Fin n))) (J : Finset (Fin n)) :
    localDegree (Erdos722.Rotations.rotateFamily sigma K) J =
      localDegree K (Erdos722.Rotations.rotateEdge sigma.symm J) := by
  simpa [localDegree, Generators.counterLoad] using
    (Erdos722.Rotations.counterLoad_rotateFamily sigma K
      (Erdos722.Rotations.rotateEdge sigma.symm J))

theorem eventually_const_mul_rotationBankCount_mul_generatorFaceCap_le
    (C b : ℕ) (hb : 0 < b) :
    ∀ᶠ n : ℕ in atTop,
      C * SlowRotationBanks.rotationBankCount (2 * b) n *
          generatorFaceCap (2 * b) n ≤
        Asymptotics.rationalPowerThreshold (3 * b - 1) (3 * b) n := by
  let a : ℝ := 1 / (10000 * (2 * b) : ℕ) +
    ((10 * (2 * b) - 7 : ℕ) : ℝ) / (10 * (2 * b) : ℕ)
  let target : ℝ := ((3 * b - 1 : ℕ) : ℝ) / (3 * b : ℕ)
  have hat : a < target := by
    dsimp [a, target]
    rw [Nat.cast_sub (by omega : 7 ≤ 10 * (2 * b)),
      Nat.cast_sub (by omega : 1 ≤ 3 * b)]
    push_cast
    field_simp
    nlinarith
  have hsmall := Asymptotics.eventually_const_mul_rpow_le_rpow
    (C := (2 * C : ℕ)) hat (by positivity : (0 : ℝ) ≤ (2 * C : ℕ))
  have htarget := Asymptotics.eventually_half_rpow_le_rationalPowerThreshold
    (E := 3 * b - 1) (d := 3 * b) (by omega) (by positivity)
  filter_upwards [hsmall, htarget, eventually_ge_atTop 1] with
      n hsmall htarget hn
  have hnpos : (0 : ℝ) < n := by positivity
  have hbank := Asymptotics.rationalPowerThreshold_cast_le
    1 (10000 * (2 * b)) n
  have hface := Asymptotics.rationalPowerThreshold_cast_le
    (10 * (2 * b) - 7) (10 * (2 * b)) n
  have hbank' : (SlowRotationBanks.rotationBankCount (2 * b) n : ℝ) ≤
      (n : ℝ) ^ (1 / (10000 * (2 * b) : ℕ) : ℝ) := by
    simpa [SlowRotationBanks.rotationBankCount] using hbank
  have hface' : (generatorFaceCap (2 * b) n : ℝ) ≤
      (n : ℝ) ^ (((10 * (2 * b) - 7 : ℕ) : ℝ) /
        (10 * (2 * b) : ℕ)) := by
    simpa [generatorFaceCap] using hface
  have hleft :
      (C * SlowRotationBanks.rotationBankCount (2 * b) n *
          generatorFaceCap (2 * b) n : ℕ) ≤
        (Asymptotics.rationalPowerThreshold (3 * b - 1) (3 * b) n : ℝ) := by
    norm_num only [Nat.cast_mul]
    calc
      (C : ℝ) * SlowRotationBanks.rotationBankCount (2 * b) n *
          generatorFaceCap (2 * b) n ≤
        (C : ℝ) * (n : ℝ) ^ (1 / (10000 * (2 * b) : ℕ) : ℝ) *
          (n : ℝ) ^ (((10 * (2 * b) - 7 : ℕ) : ℝ) /
            (10 * (2 * b) : ℕ)) := by
              gcongr
      _ = (C : ℝ) * (n : ℝ) ^ a := by
        dsimp [a]
        rw [Real.rpow_add hnpos]
        ring
      _ ≤ (n : ℝ) ^ target / 2 := by
        have : (2 : ℝ) * C * (n : ℝ) ^ a ≤ (n : ℝ) ^ target := by
          simpa only [Nat.cast_mul, Nat.cast_ofNat] using hsmall
        linarith
      _ ≤ Asymptotics.rationalPowerThreshold (3 * b - 1) (3 * b) n :=
        htarget
  exact_mod_cast hleft

theorem eventually_const_mul_rotationBankCount_mul_sampleDegree_le
    (C b : ℕ) (hb : 0 < b) :
    ∀ᶠ n : ℕ in atTop, ∀ x : ℕ,
      (x : ℝ) ≤ 2 * (n : ℝ) ^
          (((2 * b - 1 : ℕ) : ℝ) / (2 * b : ℕ)) →
      C * SlowRotationBanks.rotationBankCount (2 * b) n * x ≤
        Asymptotics.rationalPowerThreshold (3 * b - 1) (3 * b) n := by
  let a : ℝ := 1 / (10000 * (2 * b) : ℕ) +
    ((2 * b - 1 : ℕ) : ℝ) / (2 * b : ℕ)
  let target : ℝ := ((3 * b - 1 : ℕ) : ℝ) / (3 * b : ℕ)
  have hat : a < target := by
    dsimp [a, target]
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * b),
      Nat.cast_sub (by omega : 1 ≤ 3 * b)]
    push_cast
    field_simp
    nlinarith
  have hsmall := Asymptotics.eventually_const_mul_rpow_le_rpow
    (C := (4 * C : ℕ)) hat (by positivity : (0 : ℝ) ≤ (4 * C : ℕ))
  have htarget := Asymptotics.eventually_half_rpow_le_rationalPowerThreshold
    (E := 3 * b - 1) (d := 3 * b) (by omega) (by positivity)
  filter_upwards [hsmall, htarget, eventually_ge_atTop 1] with
      n hsmall htarget hn
  intro x hx
  have hnpos : (0 : ℝ) < n := by positivity
  have hbank := Asymptotics.rationalPowerThreshold_cast_le
    1 (10000 * (2 * b)) n
  have hbank' : (SlowRotationBanks.rotationBankCount (2 * b) n : ℝ) ≤
      (n : ℝ) ^ (1 / (10000 * (2 * b) : ℕ) : ℝ) := by
    simpa [SlowRotationBanks.rotationBankCount] using hbank
  have hleft :
      (C * SlowRotationBanks.rotationBankCount (2 * b) n * x : ℕ) ≤
        (Asymptotics.rationalPowerThreshold (3 * b - 1) (3 * b) n : ℝ) := by
    norm_num only [Nat.cast_mul]
    calc
      (C : ℝ) * SlowRotationBanks.rotationBankCount (2 * b) n * x ≤
        (C : ℝ) * (n : ℝ) ^ (1 / (10000 * (2 * b) : ℕ) : ℝ) *
          (2 * (n : ℝ) ^ (((2 * b - 1 : ℕ) : ℝ) /
            (2 * b : ℕ))) := by gcongr
      _ = (2 * C : ℝ) * (n : ℝ) ^ a := by
        dsimp [a]
        rw [Real.rpow_add hnpos]
        ring
      _ ≤ (n : ℝ) ^ target / 2 := by
        have : (4 : ℝ) * C * (n : ℝ) ^ a ≤ (n : ℝ) ^ target := by
          simpa only [Nat.cast_mul, Nat.cast_ofNat] using hsmall
        linarith
      _ ≤ Asymptotics.rationalPowerThreshold (3 * b - 1) (3 * b) n :=
        htarget
  exact_mod_cast hleft

theorem eventually_const_mul_intermediateThreshold_le_rootThreshold
    (C b : ℕ) (hb : 0 < b) :
    ∀ᶠ n : ℕ in atTop,
      C * Asymptotics.rationalPowerThreshold (3 * b - 1) (3 * b) n ≤
        Asymptotics.rationalPowerThreshold (4 * b - 1) (4 * b) n := by
  let a : ℝ := ((3 * b - 1 : ℕ) : ℝ) / (3 * b : ℕ)
  let target : ℝ := ((4 * b - 1 : ℕ) : ℝ) / (4 * b : ℕ)
  have hat : a < target := by
    dsimp [a, target]
    rw [Nat.cast_sub (by omega : 1 ≤ 3 * b),
      Nat.cast_sub (by omega : 1 ≤ 4 * b)]
    push_cast
    field_simp
    nlinarith
  have hsmall := Asymptotics.eventually_const_mul_rpow_le_rpow
    (C := (2 * C : ℕ)) hat (by positivity : (0 : ℝ) ≤ (2 * C : ℕ))
  have htarget := Asymptotics.eventually_half_rpow_le_rationalPowerThreshold
    (E := 4 * b - 1) (d := 4 * b) (by omega) (by positivity)
  filter_upwards [hsmall, htarget] with n hsmall htarget
  have hsource := Asymptotics.rationalPowerThreshold_cast_le
    (3 * b - 1) (3 * b) n
  have hreal :
      (C * Asymptotics.rationalPowerThreshold (3 * b - 1) (3 * b) n : ℕ) ≤
        (Asymptotics.rationalPowerThreshold (4 * b - 1) (4 * b) n : ℝ) := by
    norm_num only [Nat.cast_mul]
    calc
      (C : ℝ) * Asymptotics.rationalPowerThreshold (3 * b - 1) (3 * b) n ≤
          (C : ℝ) * (n : ℝ) ^ a := by
            simpa [a] using
              (mul_le_mul_of_nonneg_left hsource (by positivity : (0 : ℝ) ≤ C))
      _ ≤ (n : ℝ) ^ target / 2 := by
        have : (2 : ℝ) * C * (n : ℝ) ^ a ≤ (n : ℝ) ^ target := by
          simpa only [Nat.cast_mul, Nat.cast_ofNat] using hsmall
        linarith
      _ ≤ Asymptotics.rationalPowerThreshold (4 * b - 1) (4 * b) n :=
        htarget
  exact_mod_cast hreal

/-- The complete probabilistic/rotation existence wrapper for the finite
rainbow focusing certificate. -/
theorem eventually_exists_rainbowTwoCapFocusingCertificate
    (k r : ℕ) (hr : 1 < r) (hrk : r < k) :
    let b := sectionSixSampleDen hrk
    let d := 2 * b
    ∀ᶠ n : ℕ in atTop,
      ∀ reserve : Finset (Finset (Fin n)),
        HasReserveProperty n k r reserve →
        ∃ u : ℕ, u ≤ n ^ 2 ∧
          u ≤ sectionSixColorLoadCoefficient hrk *
            SlowRotationBanks.rotationBankCount d n ∧
          ∃ C : RainbowTwoCapFocusingCertificate
            (k.descFactorial r) n k r
            (generatorFaceCap d n) (generatorEdgeCap d n) u hrk reserve,
            IsPowerBounded n r (4 * b) 1 C.decoderRoots ∧
              IsPowerBounded n r (4 * b) 1 C.modular := by
  let E := ExchangeEmbedding.fullExchangeData hrk
  let e₀ := ExchangeEmbedding.fullExchangeRootEdge hrk
  let b := sectionSixSampleDen hrk
  let d := 2 * b
  let mE := E.pattern.freeEdges.card
  let mA := (CoverClique.coverPattern k r).freeEdges.card
  let mX := (E.eliminationPattern e₀).freeEdges.card
  let mR := (CoverClique.coverPattern k r).freeEdges.card
  let mFresh := (remainingBlocks E).card
  obtain ⟨hkd, hmE, hmA2, hmX, hmR, hmRrho, hmSpecial⟩ :=
    sectionSixSampleDen_bounds hr hrk
  have hb : 0 < b := (Nat.choose_pos hrk.le).trans hkd
  have hd : 0 < d := by dsimp [d]; omega
  have hkd' : Nat.choose k r < d := by dsimp [d]; omega
  have hmE' : mE < d := by
    have : mE < b := by simpa [mE, E, b] using hmE
    dsimp [d]; omega
  have hmA2' : 2 * mA < d := by
    have : 2 * mA < b := by simpa [mA, b] using hmA2
    dsimp [d]; omega
  have hmX' : mX < d := by
    have : mX < b := by simpa [mX, E, e₀, b] using hmX
    dsimp [d]; omega
  have hmR' : mR < d := by
    have : mR < b := by simpa [mR, b] using hmR
    dsimp [d]; omega
  have hmRrho' : (3 * rhoDen k r) * mR < d := by
    have : (3 * rhoDen k r) * mR < b := by
      simpa [mR, b] using hmRrho
    dsimp [d]; omega
  have hmSpecial' : Nat.choose k r *
      (Nat.choose k r - 1 + mFresh) < d := by
    have : Nat.choose k r *
        (Nat.choose k r - 1 + mFresh) < b := by
      simpa [mFresh, E, b] using hmSpecial
    dsimp [d]; omega
  have hN : 0 < k.descFactorial r := Nat.descFactorial_pos.mpr hrk.le
  have hsample := eventually_exists_prunedGeneratorSample
    (k.descFactorial r) k r d hN hr hrk hkd'
  have hchoiceE :=
    Erdos722.SlowRotationBanks.eventually_exists_prunedGenerator_rootedRotationCover
      (k.descFactorial r) k r d hr hrk hkd' E.pattern.root
      (by simpa [E] using E.root_card_lt_v hrk)
      (by simpa [mE] using hmE')
      (fun i ↦ (E.pattern.freeEdges.equivFin.symm i).1)
      (freeEdge_card E.pattern) (freeEdge_inter_root_card_lt E.pattern)
  have hchoiceA :=
    Erdos722.SlowRotationBanks.eventually_exists_prunedGenerator_rootedRotationAvoidingCover
      (k.descFactorial r) k r d (2 * k) hr hrk hkd'
      (by simpa [mA] using hmA2')
      (fun i ↦ ((CoverClique.coverPattern k r).freeEdges.equivFin.symm i).1)
      (freeEdge_card (CoverClique.coverPattern k r))
      (freeEdge_inter_root_card_lt (CoverClique.coverPattern k r))
  have hchoiceX :=
    Erdos722.SlowRotationBanks.eventually_exists_prunedGenerator_rootedRotationCover
      (k.descFactorial r) k r d hr hrk hkd'
      (E.eliminationPattern e₀).root
      (by
        simpa [E, e₀] using E.eliminationPattern_root_card_lt_v
          (Nat.zero_lt_of_lt hr) hrk e₀)
      (by simpa [mX] using hmX')
      (fun i ↦ ((E.eliminationPattern e₀).freeEdges.equivFin.symm i).1)
      (freeEdge_card (E.eliminationPattern e₀))
      (freeEdge_inter_root_card_lt (E.eliminationPattern e₀))
  have hchoiceR :=
    Erdos722.SlowRotationBanks.eventually_exists_prunedGenerator_focusCover
      (k.descFactorial r) k r d (rhoDen k r) hr hrk hkd'
      (by simpa [mR] using hmR') (by simpa [mR] using hmRrho')
      (by
        have hchoose : 0 < Nat.choose k r := Nat.choose_pos hrk.le
        simp [rhoDen, cliqueSize, hchoose]
        omega)
  have hfresh :=
    Erdos722.SlowRotationBanks.eventually_exists_prunedGenerator_specialCandidateRotationCover
      (k.descFactorial r) k r d 2 hr hrk hkd' E hmSpecial'
  let colorCoefficient :=
    4 + 2 * mE + 2 * mA + 2 * mX + 2 * mR + mFresh
  let baseLoadCoefficient := 1 + mE + mA + mX + mR
  let colorLoadCoefficient := sectionSixColorLoadCoefficient hrk
  let rootLoadCoefficient := 1 + 3 * 2 ^ k
  have hcolorLarge : ∀ᶠ n : ℕ in atTop, 2 * colorCoefficient + 2 ≤ n :=
    eventually_ge_atTop (2 * colorCoefficient + 2)
  have hbankPos : ∀ᶠ n : ℕ in atTop,
      0 < SlowRotationBanks.rotationBankCount d n := by
    have ht := Asymptotics.rationalPowerThreshold_tendsto_atTop
      (show 0 < (1 : ℕ) by omega) (show 0 < 10000 * d by positivity)
    simpa [SlowRotationBanks.rotationBankCount] using
      ht.eventually (eventually_gt_atTop 0)
  have hcolorFace :=
    eventually_const_mul_rotationBankCount_mul_generatorFaceCap_le
      colorLoadCoefficient b hb
  have hhostDegree :=
    eventually_const_mul_rotationBankCount_mul_sampleDegree_le
      baseLoadCoefficient b hb
  have hrho : 0 < rhoDen k r := by
    have hchoose : 0 < Nat.choose k r := Nat.choose_pos hrk.le
    simp [rhoDen, cliqueSize, hchoose]
  have hrhob : rhoDen k r < 3 * b := by
    have := rhoDen_lt_sectionSixSampleDen hrk
    omega
  have hreserveRebase := eventually_rebase_powerBounded_constant
    (r := r) (rhoDen k r) (3 * b) 2 hrho hrhob
  have hrootAbsorb :=
    eventually_const_mul_intermediateThreshold_le_rootThreshold
      rootLoadCoefficient b hb
  filter_upwards [hsample, hchoiceE, hchoiceA, hchoiceX, hchoiceR,
      hfresh, hcolorLarge, hbankPos, hcolorFace, hhostDegree,
      hreserveRebase, hrootAbsorb] with
      n hsample hchoiceE hchoiceA hchoiceX hchoiceR hfresh hcolorLarge
        hbankPos hcolorFace hhostDegree hreserveRebase hrootAbsorb
  obtain ⟨hn, omegaSample, D, htyp, hDK, _hcard, _hlocal, hmass⟩ := hsample
  intro reserve hreserve
  have hreserveUniform : ∀ e ∈ reserve, e.card = r := by
    intro e he
    exact mem_completeUniform.mp (hreserve.1 he)
  obtain ⟨choiceE, hchoiceE⟩ :=
    hchoiceE hn omegaSample D htyp hDK hmass
  obtain ⟨choiceA, hchoiceA⟩ :=
    hchoiceA hn omegaSample D htyp hDK hmass
  obtain ⟨choiceX, hchoiceX⟩ :=
    hchoiceX hn omegaSample D htyp hDK hmass
  obtain ⟨choiceR, ⟨A⟩⟩ :=
    hchoiceR hn omegaSample D reserve htyp hDK hmass hreserveUniform
      (by
        intro J hJ
        have hmain := hreserve.2.1 J (mem_completeUniform.mpr hJ)
        simpa [localDegree, Reserve.localDegree,
          ReserveFocusingAsymptotic.focusLeaveNum] using hmain)
  let Base := FocusingBaseCoord (SlowRotationBanks.rotationBankCount d n)
    mE mA mX mR
  let Color := FocusingColor (SlowRotationBanks.rotationBankCount d n)
    mE mA mX mR mFresh
  let basePerm : Base → Equiv.Perm (Fin n) :=
    focusingBasePerm choiceE choiceA choiceX choiceR
  let rootPerm : Color → Equiv.Perm (Fin n) := focusingRootPerm basePerm
  let u := Fintype.card Color
  let colorEquiv : Color ≃ Fin u := Fintype.equivFin Color
  let sigmaRoot : Fin u → Equiv.Perm (Fin n) :=
    fun i ↦ rootPerm (colorEquiv.symm i)
  have hbank := SlowRotationBanks.rotationBankCount_le d n hd
  have huFormula : u = 2 +
      2 * SlowRotationBanks.rotationBankCount d n * (mE + mA + mX + mR) +
      SlowRotationBanks.rotationBankCount d n * mFresh := by
    simp [u, Color, FocusingColor, FocusingBaseCoord]
    ring
  have hu : u ≤ n ^ 2 := by
    rw [huFormula]
    dsimp [colorCoefficient] at hcolorLarge
    nlinarith
  have huLoad : u ≤ colorLoadCoefficient *
      SlowRotationBanks.rotationBankCount d n := by
    rw [huFormula]
    let g := SlowRotationBanks.rotationBankCount d n
    let s := mE + mA + mX + mR
    calc
      2 + 2 * g * s + g * mFresh ≤ 2 * g + 2 * g * s + g * mFresh := by
        gcongr
        omega
      _ = (2 + 2 * s + mFresh) * g := by ring
      _ = colorLoadCoefficient * g := by
        simp [colorLoadCoefficient, sectionSixColorLoadCoefficient, s,
          mE, mA, mX, mR, mFresh, E, e₀]
  obtain ⟨fresh, hfresh⟩ :=
    hfresh hn omegaSample D htyp hDK hmass u sigmaRoot hu
  have hfreshRaw :
      ∀ (request : RootRequest E.v n E.pattern.root)
        (color : Erdos722.Exchange.RootEdge k r → Color),
      (∀ e, requestedRootEdge E request e ∈
        Erdos722.Rotations.rotateFamily (rootPerm (color e)) D.Kstar) →
      ∃ (t : Fin (SlowRotationBanks.rotationBankCount d n))
        (phi : Fin E.v ↪ Fin n),
        ExtendsRequest E.pattern.root request phi ∧
        (∀ e, mapEdge phi (E.special e) ∈
          Erdos722.Rotations.rotateFamily (rootPerm (color e))
            (SpecialCliqueRotationAsymptotic.baseUnsaturatedCliques D)) ∧
        ∀ i, Erdos722.Rotations.rotateEdge (fresh t i).symm
            (mapEdge phi (((remainingBlocks E).equivFin.symm i).1)) ∈
          SpecialCliqueRotationAsymptotic.baseUnsaturatedCliques D := by
    intro request color hcolor
    let colorFin : Erdos722.Exchange.RootEdge k r → Fin u :=
      fun e ↦ colorEquiv (color e)
    have hcolorFin : ∀ e, requestedRootEdge E request e ∈
        D.rotatedKstar sigmaRoot (colorFin e) := by
      intro e
      simpa [Erdos722.Rotations.TwoCapPrunedData.rotatedKstar,
        sigmaRoot, colorFin] using hcolor e
    obtain ⟨t, phi, hphi, hremaining⟩ := hfresh request colorFin hcolorFin
    refine ⟨t, phi, specialGoodEmbeddings_extends E request _ hphi, ?_,
      hremaining⟩
    intro e
    have hspecial := specialGoodEmbeddings_special E request _ hphi e
    simpa [SpecialCliqueRotationAsymptotic.specialCliqueFamily,
      sigmaRoot, colorFin] using hspecial
  let Cdata := rainbowTwoCapFocusingCertificateOfRotationBanks
    hr hrk D reserve hreserveUniform choiceE hchoiceE choiceA hchoiceA
      choiceX hchoiceX choiceR A fresh hfreshRaw
  let hC := Cdata.1
  have hhostEq : hC.host = focusingHostOfRotationBanks hrk D
      choiceE choiceA choiceX choiceR := Cdata.2
  refine ⟨u, hu, huLoad, hC, ?_⟩
  let T := Asymptotics.rationalPowerThreshold (3 * b - 1) (3 * b) n
  let Troot := Asymptotics.rationalPowerThreshold (4 * b - 1) (4 * b) n
  have hreservePower : IsPowerBounded n r (3 * b) 1 reserve :=
    hreserveRebase reserve hreserve.2.1
  have hreserveDegree : ∀ J : Finset (Fin n), J.card = r - 1 →
      Reserve.localDegree reserve J ≤ T := by
    intro J hJ
    apply Asymptotics.le_rationalPowerThreshold_of_pow_le
      (3 * b - 1) (3 * b) n _ (by positivity)
    simpa [localDegree, Reserve.localDegree, T] using
      hreservePower J (mem_completeUniform.mpr hJ)
  have hKPower : IsPowerBounded n r d 2 D.K := by
    intro J hJ
    have hmain := Reserve.typical_localDegree_power_bound
      hn hd (Nat.zero_lt_of_lt hr) hrk.le omegaSample htyp J
        (mem_completeUniform.mp hJ)
    simpa [hDK, localDegree, Reserve.localDegree] using hmain
  let x := maxLowerDegree n r D.K
  have hxpow : x ^ d ≤ 2 ^ d * n ^ (d - 1) :=
    maxLowerDegree_pow_le hKPower
  have hxreal : (x : ℝ) ≤ 2 * (n : ℝ) ^
      (((d - 1 : ℕ) : ℝ) / (d : ℕ)) := by
    apply (pow_le_pow_iff_left₀ (by positivity : (0 : ℝ) ≤ x)
      (by positivity : (0 : ℝ) ≤
        2 * (n : ℝ) ^ (((d - 1 : ℕ) : ℝ) / (d : ℕ)))
      hd.ne').mp
    rw [mul_pow, Asymptotics.pow_rationalExponent_eq (d - 1) d n hd]
    exact_mod_cast hxpow
  have hxreal' : (x : ℝ) ≤ 2 * (n : ℝ) ^
      (((2 * b - 1 : ℕ) : ℝ) / (2 * b : ℕ)) := by
    simpa [d] using hxreal
  have hcolorFace' : colorLoadCoefficient *
      SlowRotationBanks.rotationBankCount d n * generatorFaceCap d n ≤ T := by
    simpa only [d, T] using hcolorFace
  have huface : u * generatorFaceCap d n ≤ T :=
    (Nat.mul_le_mul_right _ huLoad).trans hcolorFace'
  have hhost : ∀ J : Finset (Fin n), J.card = r - 1 →
      Reserve.localDegree hC.host J ≤ T := by
    intro J hJ
    let Base := FocusingBaseCoord
      (SlowRotationBanks.rotationBankCount d n) mE mA mX mR
    have hraw : localDegree hC.host J ≤ Fintype.card Base * x := by
      rw [hhostEq]
      exact focusingHost_localDegree_le_mul_maxLowerDegree
        hrk D choiceE choiceA choiceX choiceR J hJ
    have hbaseCard : Fintype.card Base ≤
        baseLoadCoefficient * SlowRotationBanks.rotationBankCount d n := by
      exact focusingBaseCoord_card_le hbankPos
    calc
      Reserve.localDegree hC.host J = localDegree hC.host J := rfl
      _ ≤ Fintype.card Base * x := hraw
      _ ≤ (baseLoadCoefficient *
          SlowRotationBanks.rotationBankCount d n) * x := by gcongr
      _ ≤ T := by
        have hh := hhostDegree x hxreal'
        change baseLoadCoefficient *
          SlowRotationBanks.rotationBankCount d n * x ≤ T at hh
        exact hh
  have hmodularDegree : ∀ J : Finset (Fin n), J.card = r - 1 →
      Reserve.localDegree hC.modular J ≤ 3 * T := by
    intro J hJ
    have hunion : Reserve.localDegree (reserve ∪ hC.host) J ≤ 2 * T := by
      calc
        Reserve.localDegree (reserve ∪ hC.host) J ≤
            Reserve.localDegree reserve J + Reserve.localDegree hC.host J := by
          simpa [localDegree, Reserve.localDegree] using
            localDegree_union_le reserve hC.host J
        _ ≤ T + T := Nat.add_le_add (hreserveDegree J hJ) (hhost J hJ)
        _ = 2 * T := by omega
    calc
      Reserve.localDegree hC.modular J ≤
          u * generatorFaceCap d n +
            Reserve.localDegree (reserve ∪ hC.host) J :=
        hC.localDegree_le (Nat.zero_lt_of_lt hr) J hJ
      _ ≤ T + 2 * T := Nat.add_le_add huface hunion
      _ = 3 * T := by omega
  have hrootDegree : ∀ J : Finset (Fin n), J.card = r - 1 →
      Reserve.localDegree hC.decoderRoots J ≤
        rootLoadCoefficient * T := by
    intro J hJ
    have hres := hreserveDegree J hJ
    have hhostJ := hhost J hJ
    have hunion : Reserve.localDegree (reserve ∪ hC.host) J ≤ 2 * T := by
      calc
        Reserve.localDegree (reserve ∪ hC.host) J ≤
            Reserve.localDegree reserve J + Reserve.localDegree hC.host J := by
          simpa [localDegree, Reserve.localDegree] using
            localDegree_union_le reserve hC.host J
        _ ≤ T + T := Nat.add_le_add hres hhostJ
        _ = 2 * T := by omega
    have hboundary := hC.boundary_localDegree_le (Nat.zero_lt_of_lt hr) J hJ
    have hboundary' : Reserve.localDegree
        (cliqueBoundarySupport hC.modular r) J ≤
          (u * generatorFaceCap d n +
            Reserve.localDegree (reserve ∪ hC.host) J) * 2 ^ k := by
      change Reserve.localDegree (cliqueBoundarySupport hC.modular r) J ≤
        (u * generatorFaceCap d n +
          Reserve.localDegree (reserve ∪ hC.host) J) * 2 ^ k at hboundary
      exact hboundary
    have hboundaryT : Reserve.localDegree
        (cliqueBoundarySupport hC.modular r) J ≤
          (T + 2 * T) * 2 ^ k :=
      hboundary'.trans
        (Nat.mul_le_mul_right _ (Nat.add_le_add huface hunion))
    have hdecoderUnion : Reserve.localDegree hC.decoderRoots J ≤
        Reserve.localDegree reserve J +
          Reserve.localDegree (cliqueBoundarySupport hC.modular r) J := by
      simpa [RainbowTwoCapFocusingCertificate.decoderRoots,
        integralDecoderRoots, localDegree, Reserve.localDegree] using
        localDegree_union_le reserve (cliqueBoundarySupport hC.modular r) J
    calc
      Reserve.localDegree hC.decoderRoots J ≤
          Reserve.localDegree reserve J +
            Reserve.localDegree (cliqueBoundarySupport hC.modular r) J :=
        hdecoderUnion
      _ ≤ T + ((T + 2 * T) * 2 ^ k) :=
        Nat.add_le_add hres hboundaryT
      _ = rootLoadCoefficient * T := by
        dsimp [rootLoadCoefficient]
        ring
  refine ⟨?_, ?_⟩
  · intro J hJ
    have hdeg := hrootDegree J (mem_completeUniform.mp hJ)
    have hrootCap : Reserve.localDegree hC.decoderRoots J ≤ Troot :=
      hdeg.trans (by simpa [T, Troot] using hrootAbsorb)
    calc
      localDegree hC.decoderRoots J ^ (4 * b) ≤ Troot ^ (4 * b) := by
        simpa [localDegree, Reserve.localDegree] using
          Nat.pow_le_pow_left hrootCap _
      _ ≤ n ^ (4 * b - 1) :=
        Asymptotics.rationalPowerThreshold_pow_le _ _ _ (by positivity)
      _ = 1 ^ (4 * b) * n ^ (4 * b - 1) := by simp
  · intro J hJ
    have hdeg := hmodularDegree J (mem_completeUniform.mp hJ)
    have hmodularCap : Reserve.localDegree hC.modular J ≤ Troot := by
      apply hdeg.trans
      apply (show 3 * T ≤ rootLoadCoefficient * T by
        gcongr
        dsimp [rootLoadCoefficient]
        have hpow : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by omega)
        omega).trans
      simpa [T, Troot] using hrootAbsorb
    calc
      localDegree hC.modular J ^ (4 * b) ≤ Troot ^ (4 * b) := by
        simpa [localDegree, Reserve.localDegree] using
          Nat.pow_le_pow_left hmodularCap _
      _ ≤ n ^ (4 * b - 1) :=
        Asymptotics.rationalPowerThreshold_pow_le _ _ _ (by positivity)
      _ = 1 ^ (4 * b) * n ^ (4 * b - 1) := by simp

/-- After installing the separated local decoders, the whole first
exchange root family still has a unit power bound.  The only new constant
comes from the fixed decoder incidence bound and is absorbed by increasing
the denominator from `8b` to `9b`. -/
theorem eventually_rainbowDecoderInput_powerBounded
    (k r b : ℕ) (hr : 0 < r) (hrk : r < k) (hb : 0 < b) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (reserve : Finset (Finset (Fin n))) (faceCap edgeCap u : ℕ)
        (C : RainbowTwoCapFocusingCertificate
          (k.descFactorial r) n k r faceCap edgeCap u hrk reserve)
        (P : BoundedLocalDecoderPlacement n k r
          (LocalDecoderAsymptotic.decoderPathCap (k + r) r (4 * b) n)
          C.decoderRoots C.modular),
        IsPowerBounded n r (4 * b) 1 C.decoderRoots →
        IsPowerBounded n r (4 * b) 1 C.modular →
        IsPowerBounded n r (9 * b) 1 (C.decoderInput P.Z) := by
  let cBoundary := 2 * max 1
    ((CoverClique.coverPattern (k + r) r).freeEdges.card *
      LocalDecoderAsymptotic.decoderPathMultiplier (k + r) r)
  let cDecoder := 2 ^ (k + r) * cBoundary
  let cInput := 2 * max 1 cDecoder
  have hrebase := eventually_rebase_powerBounded_constant
    (r := r) (8 * b) (9 * b) cInput (by positivity) (by omega)
  filter_upwards [hrebase, eventually_ge_atTop 1] with n hrebase hn
  intro reserve faceCap edgeCap u C P hroots hmodular
  let decoders := localDecoderCliques C.decoderRoots P.Z k
  have hinputBoundary : IsPowerBounded n r (8 * b) cBoundary
      (cliqueBoundarySupport (C.modular ∪ decoders) r) := by
    have hmain := P.input_powerBounded (by positivity : 0 < 4 * b) hn hroots
    change IsPowerBounded n r (8 * b)
      (2 * max 1
        ((CoverClique.coverPattern (k + r) r).freeEdges.card *
          LocalDecoderAsymptotic.decoderPathMultiplier (k + r) r))
      (cliqueBoundarySupport
        (C.modular ∪ localDecoderCliques C.decoderRoots P.Z k) r)
    rw [show 8 * b = 2 * (4 * b) by omega]
    exact hmain
  have hdecoderBoundarySubset : cliqueBoundarySupport decoders r ⊆
      cliqueBoundarySupport (C.modular ∪ decoders) r := by
    intro e he
    obtain ⟨Q, hQ, heQ, hecard⟩ := mem_cliqueBoundarySupport.mp he
    exact mem_cliqueBoundarySupport.mpr
      ⟨Q, Finset.mem_union_right _ hQ, heQ, hecard⟩
  have hdecoderBoundary : IsPowerBounded n r (8 * b) cBoundary
      (cliqueBoundarySupport decoders r) :=
    hinputBoundary.mono hdecoderBoundarySubset
  have hdecoderUniform : ∀ Q ∈ decoders, Q.card = k := by
    intro Q hQ
    obtain ⟨e, he, hQe⟩ := mem_localDecoderCliques.mp hQ
    exact (Finset.mem_powersetCard.mp hQe).2
  have hdecoder : IsPowerBounded n r (8 * b) cDecoder decoders := by
    have hmain := isPowerBounded_blocks_of_boundary_and_incidence
      hr hrk hdecoderUniform
        (fun e he ↦ P.decoder_blockIncidenceCount_le e he)
        hdecoderBoundary
    simpa [cDecoder] using hmain
  have hmodular8 : IsPowerBounded n r (8 * b) 1 C.modular := by
    have hmain := hmodular.lift_mul hn (by omega : 0 < 2)
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hmain
  have hcommonModular : IsPowerBounded n r (8 * b)
      (max 1 cDecoder) C.modular :=
    hmodular8.mono_constant (le_max_left _ _)
  have hcommonDecoder : IsPowerBounded n r (8 * b)
      (max 1 cDecoder) decoders :=
    hdecoder.mono_constant (le_max_right _ _)
  have hinput : IsPowerBounded n r (8 * b) cInput
      (C.modular ∪ decoders) := by
    simpa [cInput] using hcommonModular.union hcommonDecoder
  have hrebased := hrebase (C.modular ∪ decoders) hinput
  simpa [RainbowTwoCapFocusingCertificate.decoderInput, decoders] using hrebased

end

end Erdos722
