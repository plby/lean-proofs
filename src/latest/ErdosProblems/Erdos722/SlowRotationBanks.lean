import ErdosProblems.Erdos722.Assembly
import ErdosProblems.Erdos722.RotationAbundance
import ErdosProblems.Erdos722.ReserveFocusingAsymptotic

namespace Erdos722.SlowRotationBanks

open Finset Filter
open Erdos722.Asymptotics
open Erdos722.GeneratorAsymptotic
open Erdos722.Rotations
open Erdos722.RotationAsymptotic
open Erdos722.RootedEmbedding
open Erdos722.Typicality
open Erdos722.Reserve
open Erdos722.CoverClique
open Erdos722.Cover
open Erdos722.ReserveFocusingAsymptotic
open Erdos722.ExchangePattern
open Erdos722.SpecialCliqueCandidates

noncomputable section

/-- A deliberately slow-growing number of independent rotations.  Its
exponent is separated from the edge-load cap of the pruned generator so
that the later multiplicity-flattening budget retains a strict power gap. -/
def rotationBankCount (d n : ℕ) : ℕ :=
  rationalPowerThreshold 1 (10000 * d) n

lemma rotationBankCount_le (d n : ℕ) (hd : 0 < d) :
    rotationBankCount d n ≤ n := by
  calc
    rotationBankCount d n ≤ rotationBankCount d n ^ (10000 * d) :=
      Nat.le_pow (by positivity)
    _ ≤ n ^ 1 := by
      simpa [rotationBankCount] using
        (rationalPowerThreshold_pow_le 1 (10000 * d) n (by positivity))
    _ = n := by simp

/-- Polynomially many tasks are swallowed by a bank growing like
`n^(1/(10000d))`. -/
theorem eventually_polynomial_rotation_amplification_union_bound
    (V d R : ℕ) (hd : 0 < d) (hR : 1 < R) :
    ∀ᶠ n : ℕ in atTop,
      n ^ V * (R - 1) ^ rotationBankCount d n <
        R ^ rotationBankCount d n := by
  let a : ℝ := 1 / (10000 * d : ℕ)
  let b : ℝ := 1 / (2 * R : ℕ)
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hdecay := Erdos722.Reserve.tendsto_pow_mul_exp_neg_rpow_atTop
    V ha hb
  have hnat := hdecay.comp tendsto_natCast_atTop_atTop
  have hsmall : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ V * Real.exp (-b * (n : ℝ) ^ a) < 1 :=
    (tendsto_order.1 hnat).2 _ (by norm_num)
  have hcap := eventually_half_rpow_le_rationalPowerThreshold
    (show 0 < (1 : ℕ) by omega) (show 0 < 10000 * d by positivity)
  filter_upwards [hsmall, hcap] with n hsmall hcap
  let g := rotationBankCount d n
  have hcap' : (n : ℝ) ^ a / 2 ≤ (g : ℝ) := by
    simpa [a, g, rotationBankCount] using hcap
  have hbase :
      (((R - 1 : ℕ) : ℝ) / R) ≤ Real.exp (-(1 / (R : ℝ))) := by
    have hone := Real.one_sub_le_exp_neg (1 / (R : ℝ))
    have hcast : ((R - 1 : ℕ) : ℝ) = R - 1 := by
      simpa using (Nat.cast_sub (R := ℝ) (by omega : 1 ≤ R))
    rw [hcast]
    convert hone using 1 <;> field_simp <;> ring
  have hratioNonneg : (0 : ℝ) ≤ ((R - 1 : ℕ) : ℝ) / R := by positivity
  have hexpBound :
      ((((R - 1 : ℕ) : ℝ) / R) ^ g) ≤
        Real.exp (-b * (n : ℝ) ^ a) := by
    calc
      ((((R - 1 : ℕ) : ℝ) / R) ^ g) ≤
          (Real.exp (-(1 / (R : ℝ)))) ^ g :=
        pow_le_pow_left₀ hratioNonneg hbase g
      _ = Real.exp (-((g : ℝ) / R)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
      _ ≤ Real.exp (-b * (n : ℝ) ^ a) := by
        apply Real.exp_le_exp.mpr
        have hRpos : (0 : ℝ) < R := by exact_mod_cast (by omega : 0 < R)
        have hscaled : b * (n : ℝ) ^ a ≤ (g : ℝ) / R := by
          calc
            b * (n : ℝ) ^ a = ((n : ℝ) ^ a / 2) / R := by
              dsimp [b]
              push_cast
              field_simp
              <;> ring
            _ ≤ (g : ℝ) / R :=
              div_le_div_of_nonneg_right hcap' hRpos.le
        simpa only [neg_mul] using neg_le_neg hscaled
  have hratioSmall :
      (n : ℝ) ^ V * ((((R - 1 : ℕ) : ℝ) / R) ^ g) < 1 :=
    (mul_le_mul_of_nonneg_left hexpBound (by positivity)).trans_lt hsmall
  have hRpowPos : (0 : ℝ) < (R : ℝ) ^ g := by positivity
  have hquot :
      (n : ℝ) ^ V * ((R - 1 : ℕ) : ℝ) ^ g / (R : ℝ) ^ g < 1 := by
    simpa [div_pow, mul_div_assoc] using hratioSmall
  have hcross :
      (n : ℝ) ^ V * ((R - 1 : ℕ) : ℝ) ^ g < (R : ℝ) ^ g := by
    have := (div_lt_iff₀ hRpowPos).mp hquot
    simpa using this
  exact_mod_cast hcross

/-- Root requests form a polynomial task family, so the slow bank also
covers every request. -/
theorem eventually_rotation_amplification_union_bound
    (v d R : ℕ) (hd : 0 < d) (hR : 1 < R) :
    ∀ᶠ n : ℕ in atTop,
      ∀ root : Finset (Fin v),
        Nat.card (RootRequest v n root) *
            (R - 1) ^ rotationBankCount d n <
          R ^ rotationBankCount d n := by
  have hpoly := eventually_polynomial_rotation_amplification_union_bound
    v d R hd hR
  filter_upwards [hpoly] with n hpoly root
  calc
    Nat.card (RootRequest v n root) *
          (R - 1) ^ rotationBankCount d n ≤
        n ^ v * (R - 1) ^ rotationBankCount d n := by
      gcongr
      exact natCard_rootRequest_le_pow root
    _ < R ^ rotationBankCount d n := hpoly

/-- The standard rooted rotation cover, with the amplification count
decoupled from the generator's edge-load cap. -/
theorem eventually_exists_prunedGenerator_rootedRotationCover
    (N q r d : ℕ) (hr : 1 < r) (hrq : r < q)
    (hqd : Nat.choose q r < d)
    {v m : ℕ} (root : Finset (Fin v)) (hroot : root.card < v)
    (hmd : m < d) (edges : Fin m → Finset (Fin v))
    (hedges : ∀ i, (edges i).card = r)
    (hproper : ∀ i, (edges i ∩ root).card < r) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (hn : 0 < n)
        (omega : {e // e ∈ uniformEdges n r} → Bool)
        (D : TwoCapPrunedData N n q r
          (generatorFaceCap d n) (generatorEdgeCap d n)
          (generatorPruneThreshold q r d n)
          (generatorFaceCliqueCap q r d n)
          (generatorEdgeCliqueCap q r d n)),
      (∀ roots, ∀ hroots : roots ∈ rootFamilies n r (Nat.choose q r),
        commonMean n roots (reserveProbabilityIcc n d hn) / 2 <
          Erdos722.Probability.finiteRandomSum
            (fun x ↦ commonNeighborIndicator n r roots (by omega)
              (root_card_of_mem_rootFamilies hroots) x) omega ∧
        Erdos722.Probability.finiteRandomSum
            (fun x ↦ commonNeighborIndicator n r roots (by omega)
              (root_card_of_mem_rootFamilies hroots) x) omega <
          2 * commonMean n roots (reserveProbabilityIcc n d hn)) →
      D.K = sampledEdges n r omega →
      (uniformEdges n (r - 1)).card * generatorDegreeLower d n ≤
        2 * D.Kstar.card * Nat.choose r (r - 1) →
      ∃ choice : Fin (rotationBankCount d n) →
          (Fin m → Equiv.Perm (Fin n)),
        ∀ request : RootRequest v n root,
          ∃ t : Fin (rotationBankCount d n), ∃ phi : Fin v ↪ Fin n,
            ExtendsRequest root request phi ∧
            ∀ i, rotateEdge (choice t i).symm
              (mapEdge phi (edges i)) ∈ D.Kstar := by
  let R := rotationPairConstant r ^ m + 1
  have hR : 1 < R := by
    dsimp [R]
    have hc : 0 < rotationPairConstant r := rotationPairConstant_pos (by omega)
    have : 0 < rotationPairConstant r ^ m := pow_pos hc _
    omega
  have hfailure :=
    Erdos722.RotationAsymptotic.eventually_prunedGenerator_rootedRotation_failure
      N q r d hr hrq hqd root hroot hmd edges hedges hproper
  have hunion := eventually_rotation_amplification_union_bound v d R
    (by have := (Nat.choose_pos hrq.le).trans hqd; omega) hR
  filter_upwards [hfailure, hunion] with n hfailure hunion
  intro hn omega D htyp hDK hmass
  apply Erdos722.Rotations.exists_amplified_rootedRotationCover_of_scaled_bad
    (r := r) (R := R) (g := rotationBankCount d n)
    D.Kstar edges (by omega)
  · intro request
    have hf := hfailure hn omega D htyp hDK hmass request
    have hRsub : R - 1 = rotationPairConstant r ^ m := by
      dsimp [R]
    rw [hRsub]
    simpa [R, Fintype.card_fun] using hf
  · exact hunion root

/-- The abundant version needed by both forbidden-vertex avoidance and
reserve focusing, again using the slow bank. -/
theorem eventually_exists_prunedGenerator_rootedRotationAbundantCover
    (N q r d : ℕ) (hr : 1 < r) (hrq : r < q)
    (hqd : Nat.choose q r < d)
    {v m : ℕ} (root : Finset (Fin v)) (hroot : root.card < v)
    (hmd : m < d) (edges : Fin m → Finset (Fin v))
    (hedges : ∀ i, (edges i).card = r)
    (hproper : ∀ i, (edges i ∩ root).card < r) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (hn : 0 < n)
        (omega : {e // e ∈ uniformEdges n r} → Bool)
        (D : TwoCapPrunedData N n q r
          (generatorFaceCap d n) (generatorEdgeCap d n)
          (generatorPruneThreshold q r d n)
          (generatorFaceCliqueCap q r d n)
          (generatorEdgeCliqueCap q r d n)),
      (∀ roots, ∀ hroots : roots ∈ rootFamilies n r (Nat.choose q r),
        commonMean n roots (reserveProbabilityIcc n d hn) / 2 <
          Erdos722.Probability.finiteRandomSum
            (fun x ↦ commonNeighborIndicator n r roots (by omega)
              (root_card_of_mem_rootFamilies hroots) x) omega ∧
        Erdos722.Probability.finiteRandomSum
            (fun x ↦ commonNeighborIndicator n r roots (by omega)
              (root_card_of_mem_rootFamilies hroots) x) omega <
          2 * commonMean n roots (reserveProbabilityIcc n d hn)) →
      D.K = sampledEdges n r omega →
      (uniformEdges n (r - 1)).card * generatorDegreeLower d n ≤
        2 * D.Kstar.card * Nat.choose r (r - 1) →
      ∃ choice : Fin (rotationBankCount d n) →
          (Fin m → Equiv.Perm (Fin n)),
        ∀ request : RootRequest v n root,
          ∃ t : Fin (rotationBankCount d n),
            (rootedEmbeddings root request).card * D.Kstar.card ^ m ≤
              2 * Erdos722.Probability.finiteSuccessCount
                  (rootedEmbeddings root request)
                  (rootedRotationSuccess D.Kstar edges) (choice t) *
                Nat.choose n r ^ m := by
  let R := 4 * (rotationPairConstant r ^ m + 1)
  have hR : 1 < R := by
    dsimp [R]
    have hc : 0 < rotationPairConstant r := rotationPairConstant_pos (by omega)
    have : 0 < rotationPairConstant r ^ m := pow_pos hc _
    omega
  have hfailure :=
    Erdos722.RotationAbundance.eventually_prunedGenerator_rootedRotation_abundant_failure
      N q r d hr hrq hqd root hroot hmd edges hedges hproper
  have hunion := eventually_rotation_amplification_union_bound v d R
    (by have := (Nat.choose_pos hrq.le).trans hqd; omega) hR
  filter_upwards [hfailure, hunion] with n hfailure hunion
  intro hn omega D htyp hDK hmass
  apply Erdos722.RotationAbundance.exists_amplified_rootedRotationAbundantCover_of_scaled_bad
    (r := r) (R := R) (g := rotationBankCount d n)
    D.Kstar edges (by omega)
  · intro request
    simpa [R] using hfailure hn omega D htyp hDK hmass request
  · exact hunion root

/-- The auxiliary clique bank may additionally avoid every prescribed
vertex set of bounded size. -/
theorem eventually_exists_prunedGenerator_rootedRotationAvoidingCover
    (N q r d C : ℕ) (hr : 1 < r) (hrq : r < q)
    (hqd : Nat.choose q r < d)
    {m : ℕ} (hcross : 2 * m < d) (edges : Fin m → Finset (Fin q))
    (hedges : ∀ i, (edges i).card = r)
    (hproper : ∀ i, (edges i ∩ Erdos722.CoverClique.coverRoot q r).card < r) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (hn : 0 < n)
        (omega : {e // e ∈ uniformEdges n r} → Bool)
        (D : TwoCapPrunedData N n q r
          (generatorFaceCap d n) (generatorEdgeCap d n)
          (generatorPruneThreshold q r d n)
          (generatorFaceCliqueCap q r d n)
          (generatorEdgeCliqueCap q r d n)),
      (∀ roots, ∀ hroots : roots ∈ rootFamilies n r (Nat.choose q r),
        commonMean n roots (reserveProbabilityIcc n d hn) / 2 <
          Erdos722.Probability.finiteRandomSum
            (fun x ↦ commonNeighborIndicator n r roots (by omega)
              (root_card_of_mem_rootFamilies hroots) x) omega ∧
        Erdos722.Probability.finiteRandomSum
            (fun x ↦ commonNeighborIndicator n r roots (by omega)
              (root_card_of_mem_rootFamilies hroots) x) omega <
          2 * commonMean n roots (reserveProbabilityIcc n d hn)) →
      D.K = sampledEdges n r omega →
      (uniformEdges n (r - 1)).card * generatorDegreeLower d n ≤
        2 * D.Kstar.card * Nat.choose r (r - 1) →
      ∃ choice : Fin (rotationBankCount d n) →
          (Fin m → Equiv.Perm (Fin n)),
        ∀ request : RootRequest q n (Erdos722.CoverClique.coverRoot q r),
          ∀ J : Finset (Fin n), J.card ≤ C →
            ∃ (t : Fin (rotationBankCount d n)) (phi : Fin q ↪ Fin n),
              phi ∈ Erdos722.RotationAbundance.successfulRootedEmbeddings
                (Erdos722.CoverClique.coverRoot q r) request D.Kstar
                edges (choice t) ∧
              ¬ OutsideRootTouches
                (Erdos722.CoverClique.coverRoot q r) J phi := by
  have hcover := eventually_exists_prunedGenerator_rootedRotationAbundantCover
    N q r d hr hrq hqd (Erdos722.CoverClique.coverRoot q r) (by
      rw [Erdos722.CoverClique.card_coverRoot hrq.le]
      exact hrq) (by omega) edges hedges hproper
  have hchooseOne : 1 < Nat.choose q r := by
    have hpos : 0 < Nat.choose q r := Nat.choose_pos hrq.le
    have hne : Nat.choose q r ≠ 1 := by
      intro heq
      rcases Nat.choose_eq_one_iff.mp heq with hrzero | hqr
      · omega
      · omega
    omega
  have havoid :=
    Erdos722.RotationAbundance.eventually_outsideRootTouch_lt_of_abundant_rotations
      (q := q) (r := r) (d := d) (m := m) (C := C)
      (by omega) hrq (hchooseOne.trans hqd) hcross
  filter_upwards [hcover, havoid] with n hcover havoid
  intro hn omega D htyp hDK hmass
  obtain ⟨choice, hchoice⟩ := hcover hn omega D htyp hDK hmass
  refine ⟨choice, ?_⟩
  intro request J hJ
  obtain ⟨t, ht⟩ := hchoice request
  let S := Erdos722.RotationAbundance.successfulRootedEmbeddings
    (Erdos722.CoverClique.coverRoot q r) request D.Kstar edges (choice t)
  let bad := (rootedEmbeddings
    (Erdos722.CoverClique.coverRoot q r) request).filter fun phi ↦
      outsideRootTouchHit (Erdos722.CoverClique.coverRoot q r) J [] phi
  have hlt : bad.card < S.card := by
    apply havoid D.Kstar request S.card J (by
      simpa [uniformEdges] using hmass)
    · simpa [S, Erdos722.RotationAbundance.card_successfulRootedEmbeddings]
        using ht
    · exact hJ
  have hexists : ∃ phi ∈ S,
      ¬ OutsideRootTouches (Erdos722.CoverClique.coverRoot q r) J phi := by
    by_contra hnone
    push_neg at hnone
    have hsub : S ⊆ bad := by
      intro phi hphi
      have hSdata := Finset.mem_filter.mp hphi
      apply Finset.mem_filter.mpr
      refine ⟨hSdata.1, ?_⟩
      exact (outsideRootTouchHit_eq_true_iff
        (Erdos722.CoverClique.coverRoot q r) J [] phi).mpr
          (hnone phi hphi)
    exact (Nat.not_le_of_lt hlt) (Finset.card_le_card hsub)
  obtain ⟨phi, hphi, hphiAvoid⟩ := hexists
  exact ⟨t, phi, by simpa [S] using hphi, hphiAvoid⟩

/-- Reserve focusing with slow amplification. -/
theorem eventually_exists_prunedGenerator_focusCover
    (N q r d rho : ℕ) (hr : 1 < r) (hrq : r < q)
    (hqd : Nat.choose q r < d)
    (hmd : (coverPattern q r).freeEdges.card < d)
    (hcross : (3 * rho) * (coverPattern q r).freeEdges.card < d)
    (hrho : 1 < rho) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (hn : 0 < n)
        (omegaSample : {e // e ∈ uniformEdges n r} → Bool)
        (D : TwoCapPrunedData N n q r
          (generatorFaceCap d n) (generatorEdgeCap d n)
          (generatorPruneThreshold q r d n)
          (generatorFaceCliqueCap q r d n)
          (generatorEdgeCliqueCap q r d n))
        (leave : Finset (Finset (Fin n))),
      (∀ roots, ∀ hroots : roots ∈ rootFamilies n r (Nat.choose q r),
        commonMean n roots (reserveProbabilityIcc n d hn) / 2 <
          Erdos722.Probability.finiteRandomSum
            (fun x ↦ commonNeighborIndicator n r roots (by omega)
              (root_card_of_mem_rootFamilies hroots) x) omegaSample ∧
        Erdos722.Probability.finiteRandomSum
            (fun x ↦ commonNeighborIndicator n r roots (by omega)
              (root_card_of_mem_rootFamilies hroots) x) omegaSample <
          2 * commonMean n roots (reserveProbabilityIcc n d hn)) →
      D.K = sampledEdges n r omegaSample →
      (uniformEdges n (r - 1)).card * generatorDegreeLower d n ≤
        2 * D.Kstar.card * Nat.choose r (r - 1) →
      (∀ e ∈ leave, e.card = r) →
      (∀ J : Finset (Fin n), J.card = r - 1 →
        (Reserve.localDegree leave J) ^ rho ≤
          2 ^ rho * n ^ focusLeaveNum rho) →
      ∃ choice : Fin (rotationBankCount d n) →
          Fin (coverPattern q r).freeEdges.card → Equiv.Perm (Fin n),
        Nonempty (CoverAssignment n q r leave
          (Erdos722.RotationAbundance.rotationUnionHost D.Kstar choice \
            leave)) := by
  let root := coverRoot q r
  let m := (coverPattern q r).freeEdges.card
  let edges : Fin m → Finset (Fin q) := fun i ↦
    (coverPattern q r).freeEdges.equivFin.symm i
  have hroot : root.card < q := by
    dsimp [root]
    rw [card_coverRoot hrq.le]
    exact hrq
  have hedges : ∀ i, (edges i).card = r := by
    intro i
    exact (mem_coverPattern_freeEdges_iff hrq.le).mp
      ((coverPattern q r).freeEdges.equivFin.symm i).2 |>.1
  have hproper : ∀ i, ((edges i) ∩ root).card < r := by
    intro i
    have hi := ((coverPattern q r).freeEdges.equivFin.symm i).2
    have hiData := (mem_coverPattern_freeEdges_iff hrq.le).mp hi
    have hinterLe : ((edges i) ∩ root).card ≤ r := by
      exact (Finset.card_le_card Finset.inter_subset_left).trans_eq hiData.1
    by_contra hnot
    have heq : ((edges i) ∩ root).card = r := by omega
    have hsub : edges i ⊆ root := by
      apply Finset.inter_eq_left.mp
      apply Finset.eq_of_subset_of_card_le Finset.inter_subset_left
      rw [heq]
      simpa [edges] using hiData.1.le
    exact hiData.2 (Finset.eq_of_subset_of_card_le hsub (by
      rw [card_coverRoot hrq.le, hiData.1]))
  have habundant :=
    eventually_exists_prunedGenerator_rootedRotationAbundantCover
      N q r d hr hrq hqd root hroot (by simpa [m] using hmd)
      edges hedges hproper
  have hclean :=
    Erdos722.RotationAbundance.eventually_clean_candidate_power_of_abundant_rotations
      (q := q) (r := r) (d := d) (m := m) (rho := rho)
      (Dloss := 3 * rho) (Kloss := 1) (Cdeg := 4)
      (by omega : 0 < r) hrq (by
        have hchoose : 0 < Nat.choose q r := Nat.choose_pos hrq.le
        omega) (by omega : 0 < rho)
      (by
        dsimp [m]
        exact (Nat.mul_le_mul_right (coverPattern q r).freeEdges.card
          (by omega : 2 * rho ≤ 3 * rho)).trans_lt hcross)
      (by simpa [m] using hcross)
      (by exact Nat.mul_pos (by positivity : 0 < 3 * rho) (by omega))
  have hfocus :=
    eventually_exists_focusCoverAssignment_of_power_bounds
      (q := q) (r := r) (rho := rho) (by omega) hrq hrho
  have hdegree := eventually_focusLeave_degree_le hrho
  filter_upwards [habundant, hclean, hfocus, hdegree] with
      n habundant hclean hfocus hdegree
  intro hn omegaSample D leave htyp hDK hmass hleaveUniform hleavePower
  obtain ⟨choice, hchoice⟩ := habundant hn omegaSample D htyp hDK hmass
  refine ⟨choice, ?_⟩
  apply hfocus leave
    (Erdos722.RotationAbundance.rotationUnionHost D.Kstar choice \ leave)
    hleaveUniform
  · intro a ha
    have haUnion := (Finset.mem_sdiff.mp ha).1
    obtain ⟨t, _ht, haGroup⟩ := Finset.mem_biUnion.mp haUnion
    obtain ⟨i, _hi, hai⟩ := Finset.mem_biUnion.mp haGroup
    have hpre : rotateEdge (choice t i).symm a ∈ D.Kstar :=
      mem_rotateFamily.mp hai
    have hcard := D.uniform _ (D.Kstar_subset hpre)
    exact (rotateEdge_card (choice t i).symm a).symm.trans hcard
  · exact hleavePower
  · intro e he
    have hecard := hleaveUniform e he
    have hene : e.Nonempty := Finset.card_pos.mp (by omega)
    let : Nonempty (Fin n) := ⟨hene.choose⟩
    obtain ⟨request, hrequest⟩ := exists_rootRequest_with_image root e (by
      dsimp [root]
      rw [card_coverRoot hrq.le, hecard])
    obtain ⟨t, ht⟩ := hchoice request
    apply hclean (rotationBankCount d n)
      D.Kstar leave choice request e t (focusLeaveCap rho n) (by
        simpa [uniformEdges] using hmass)
    · simpa [m, edges,
        Erdos722.RotationAbundance.card_successfulRootedEmbeddings] using ht
    · exact hleaveUniform
    · intro J hJ
      exact hdegree (Reserve.localDegree leave J) (hleavePower J hJ)
    · exact focusLeaveCap_pow_le (by omega : 0 < rho) n
    · simpa [root] using hrequest

/-- Source-faithful property-(iv) rotations with slow amplification. -/
theorem eventually_exists_prunedGenerator_specialCandidateRotationCover
    (N q r d Uexp : ℕ) (hr : 1 < r) (hrq : r < q)
    (hqd : Nat.choose q r < d)
    (E : RelabeledFullExchange q r)
    (hbudget : Nat.choose q r *
      (Nat.choose q r - 1 + (remainingBlocks E).card) < d) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (hn : 0 < n)
        (omegaSample : {e // e ∈ uniformEdges n r} → Bool)
        (D : TwoCapPrunedData N n q r
          (generatorFaceCap d n) (generatorEdgeCap d n)
          (generatorPruneThreshold q r d n)
          (generatorFaceCliqueCap q r d n)
          (generatorEdgeCliqueCap q r d n)),
      (∀ roots, ∀ hroots : roots ∈ rootFamilies n r (Nat.choose q r),
        commonMean n roots (reserveProbabilityIcc n d hn) / 2 <
          Erdos722.Probability.finiteRandomSum
            (fun x ↦ commonNeighborIndicator n r roots (by omega)
              (root_card_of_mem_rootFamilies hroots) x) omegaSample ∧
        Erdos722.Probability.finiteRandomSum
            (fun x ↦ commonNeighborIndicator n r roots (by omega)
              (root_card_of_mem_rootFamilies hroots) x) omegaSample <
          2 * commonMean n roots (reserveProbabilityIcc n d hn)) →
      D.K = sampledEdges n r omegaSample →
      (uniformEdges n (r - 1)).card * generatorDegreeLower d n ≤
        2 * D.Kstar.card * Nat.choose r (r - 1) →
      ∀ (u : ℕ) (sigma : Fin u → Equiv.Perm (Fin n)),
      u ≤ n ^ Uexp →
      ∃ fresh : Fin (rotationBankCount d n) →
          Fin (remainingBlocks E).card → Equiv.Perm (Fin n),
        ∀ (request : RootRequest E.v n E.pattern.root)
          (color : Erdos722.Exchange.RootEdge q r → Fin u),
        (∀ e, requestedRootEdge E request e ∈
          D.rotatedKstar sigma (color e)) →
        ∃ (t : Fin (rotationBankCount d n)) (phi : Fin E.v ↪ Fin n),
          phi ∈ specialGoodEmbeddings E request
            (Erdos722.SpecialCliqueRotationAsymptotic.specialCliqueFamily
              D sigma color) ∧
          ∀ i, rotateEdge (fresh t i).symm
              (mapEdge phi ((remainingBlocks E).equivFin.symm i).1) ∈
            Erdos722.SpecialCliqueRotationAsymptotic.baseUnsaturatedCliques D := by
  let m := (remainingBlocks E).card
  let blocks : Fin m → Finset (Fin E.v) := fun i ↦
    ((remainingBlocks E).equivFin.symm i).1
  let R := Erdos722.CliqueRotationAsymptotic.cliqueRotationPairConstant
    q r ^ m + 2
  let V := E.v + Uexp * Nat.choose q r
  have hR : 1 < R := by dsimp [R]; omega
  have hfailure :=
    Erdos722.SpecialCliqueRotationAsymptotic.eventually_prunedGenerator_specialCandidateRotation_failure
      N q r d hr hrq hqd E hbudget
  have hunion := eventually_polynomial_rotation_amplification_union_bound
    V d R (by have := (Nat.choose_pos hrq.le).trans hqd; omega) hR
  filter_upwards [hfailure, hunion] with n hfailure hunion
  intro hn omegaSample D htyp hDK hmass u sigma hu
  let Request := RootRequest E.v n E.pattern.root
  let : Fintype Request := Fintype.ofInjective RootRequest.map (by
    intro a b hab
    cases a with
    | mk amap ainj =>
      cases b with
      | mk bmap binj =>
        simp only [Request, RootRequest.map] at hab
        cases hab
        rfl)
  let Task := Request × (Erdos722.Exchange.RootEdge q r → Fin u)
  let : DecidableEq Task := Classical.decEq Task
  let good (task : Task) : Prop :=
    ∀ e, requestedRootEdge E task.1 e ∈
      D.rotatedKstar sigma (task.2 e)
  let tasks : Finset Task := (Finset.univ : Finset Task).filter good
  let embeddings (task : Task) : Finset (Fin E.v ↪ Fin n) :=
    specialGoodEmbeddings E task.1
      (Erdos722.SpecialCliqueRotationAsymptotic.specialCliqueFamily
        D sigma task.2)
  have htaskCard : tasks.card ≤ n ^ V := by
    calc
      tasks.card ≤ Fintype.card Task := by
        rw [← Finset.card_univ]
        exact Finset.card_le_card (Finset.filter_subset _ _)
      _ = Fintype.card Request * u ^ Nat.choose q r := by
        simp [Task, Fintype.card_prod, Fintype.card_fun, card_rootEdge]
      _ ≤ n ^ E.v * (n ^ Uexp) ^ Nat.choose q r := by
        exact Nat.mul_le_mul
          (by
            rw [← Nat.card_eq_fintype_card]
            exact natCard_rootRequest_le_pow E.pattern.root)
          (Nat.pow_le_pow_left hu _)
      _ = n ^ V := by simp [V, pow_mul, pow_add]
  have hscaled : ∀ task ∈ tasks,
      R * ((rotationSamples n m).filter fun fresh ↦
        Erdos722.Probability.finiteSuccessCount (embeddings task)
          (rootedRotationSuccess
            (Erdos722.SpecialCliqueRotationAsymptotic.baseUnsaturatedCliques D)
            blocks) fresh = 0).card ≤
        (R - 1) * Fintype.card (Fin m → Equiv.Perm (Fin n)) := by
    intro task htask
    have hgood : good task := (Finset.mem_filter.mp htask).2
    simpa [R, m, blocks, embeddings, good] using
      hfailure hn omegaSample D htyp hDK hmass u sigma task.1 task.2 hgood
  have htaskUnion : tasks.card * (R - 1) ^ rotationBankCount d n <
      R ^ rotationBankCount d n :=
    (Nat.mul_le_mul_right ((R - 1) ^ rotationBankCount d n)
      htaskCard).trans_lt hunion
  obtain ⟨fresh, hfresh⟩ :=
    Erdos722.CandidateCliqueRotation.exists_amplified_candidateRotationCover_of_scaled_bad
      tasks embeddings
      (Erdos722.SpecialCliqueRotationAsymptotic.baseUnsaturatedCliques D)
      blocks (by omega : 0 < R) hscaled htaskUnion
  refine ⟨fresh, ?_⟩
  intro request color hcolor
  have htask : (request, color) ∈ tasks := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, hcolor⟩
  obtain ⟨t, phi, hphi, hsuccess⟩ := hfresh (request, color) htask
  exact ⟨t, phi, hphi, hsuccess⟩

end

end Erdos722.SlowRotationBanks
