import ErdosProblems.Erdos780.External.ZpTuckerDefs
import ErdosProblems.Erdos780.External.SignedSphereLength
import ErdosProblems.Erdos780.External.PositiveAllowed
import ErdosProblems.Erdos780.External.ReducedLabelEquivariance
import ErdosProblems.Erdos780.External.AllowedDescent

open scoped BigOperators

namespace Erdos780Core

open ZpTuckerScratch

noncomputable section

variable {p n m alpha : ℕ}

abbrev Vertex (p m : ℕ) := ZMod p × Fin m
abbrev Total (p m alpha : ℕ) := TargetOrbits.TotalChain p m alpha

noncomputable local instance targetOrder [NeZero p] : LinearOrder (Vertex p m) :=
  LabelChainMap.targetLinearOrder

theorem map_apply_empty
    {V W : Type*} [Fintype V] [Fintype W]
    [LinearOrder V] [LinearOrder W]
    (f : V → W) (hf : Function.Injective f)
    (c : TargetChains.FullChain ℤ V) :
    TargetChains.map f c ∅ = c ∅ := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simpa only [map_add, Finsupp.add_apply, hc, hd]
  | single s z =>
      by_cases hs : s = ∅
      · subst s
        rw [TargetChains.map_single_empty]
        simp
      · have himage : (s.image f).Nonempty :=
          Finset.image_nonempty.mpr (Finset.nonempty_iff_ne_empty.mpr hs)
        rw [show Finsupp.single s z = z • Finsupp.single s (1 : ℤ) by simp,
          map_smul, TargetChains.map_single_of_injOn f s hf.injOn]
        simp [hs, Finset.nonempty_iff_ne_empty.mp himage]

theorem augmentation_map
    {V W : Type*} [Fintype V] [Fintype W]
    [LinearOrder V] [LinearOrder W]
    (f : V → W) (hf : Function.Injective f)
    (c : PositiveTarget.Chain ℤ V) :
    PositiveTarget.augmentation ℤ W (PositiveTarget.map f c) =
      PositiveTarget.augmentation ℤ V c := by
  change TargetChains.boundary ℤ W
      (TargetChains.positiveInclusion ℤ W
        (TargetChains.projectPositive ℤ W
          (TargetChains.map f
            (TargetChains.positiveInclusion ℤ V c)))) ∅ =
    TargetChains.boundary ℤ V
      (TargetChains.positiveInclusion ℤ V c) ∅
  rw [TargetChains.boundary_projectPositive, ← TargetChains.map_boundary]
  exact map_apply_empty f hf _

theorem augmentation_targetAct [NeZero p] (a : ZMod p)
    (c : PositiveTarget.Chain ℤ (Vertex p m)) :
    PositiveTarget.augmentation ℤ (Vertex p m)
        (SignedTargetOrbits.targetAct a c) =
      PositiveTarget.augmentation ℤ (Vertex p m) c :=
  augmentation_map (LabelChainMap.targetShift a)
    (SignedTargetOrbits.targetShift_injective a) c

noncomputable def liftSphere [NeZero p]
    (hp : p.Prime)
    (lab : NonzeroSignedVector p n → Vertex p m)
    (hadm : IsAlphaAdmissible alpha lab)
    (i : ℕ) (hi : i < n) : Total p m alpha :=
  (AllowedComplex.totalChainEquivPositiveAllowed
    (p := p) (m := m) (alpha := alpha)).symm
      ⟨PositiveTarget.labelLists lab (SignedSphere.y p n i), by
        exact PositiveAllowed.labelLists_mem_allowedPositive_of_supported
          hp lab hadm ((SignedSphere.y_supported_exact hi).mono (by
            intro l hl
            refine ⟨hl.1, ?_⟩
            intro hnil
            subst l
            simp [SignedSphere.ExactStrictFlag] at hl))⟩

theorem totalInclusion_liftSphere [NeZero p]
    (hp : p.Prime)
    (lab : NonzeroSignedVector p n → Vertex p m)
    (hadm : IsAlphaAdmissible alpha lab)
    (i : ℕ) (hi : i < n) :
    SignedTargetOrbits.totalInclusion
        (liftSphere hp lab hadm i hi) =
      PositiveTarget.labelLists lab (SignedSphere.y p n i) := by
  rw [← AllowedDescent.equiv_coe_eq_totalInclusion]
  simp [liftSphere]

theorem totalInclusion_tau_liftSphere [NeZero p]
    (hp : p.Prime)
    (lab : NonzeroSignedVector p n → Vertex p m)
    (heq : IsEquivariant lab)
    (hadm : IsAlphaAdmissible alpha lab)
    (i : ℕ) (hi : i < n) :
    SignedTargetOrbits.totalInclusion
        (SignedTargetOrbits.actualTotalTau (liftSphere hp lab hadm i hi)) =
      PositiveTarget.labelLists lab
        (SignedSphere.tau (SignedSphere.y p n i)) := by
  change SignedTargetOrbits.totalInclusion
      (SignedTargetOrbits.actualTotalAct (liftSphere hp lab hadm i hi) -
        liftSphere hp lab hadm i hi) = _
  rw [map_sub, SignedTargetOrbits.totalInclusion_actualTotalAct,
    totalInclusion_liftSphere]
  rw [SignedSphere.tau]
  simp only [LinearMap.sub_apply, LinearMap.id_apply, map_sub]
  exact congrArg (fun z => z - PositiveTarget.labelLists lab
      (SignedSphere.y p n i))
    (ReducedLabelEquivariance.positiveLabelLists_equivariant
      lab heq 1 (SignedSphere.y p n i)).symm

theorem totalInclusion_norm_liftSphere [NeZero p]
    (hp : p.Prime)
    (lab : NonzeroSignedVector p n → Vertex p m)
    (heq : IsEquivariant lab)
    (hadm : IsAlphaAdmissible alpha lab)
    (i : ℕ) (hi : i < n) :
    SignedTargetOrbits.totalInclusion
        (SignedTargetOrbits.actualTotalNorm hp (liftSphere hp lab hadm i hi)) =
      PositiveTarget.labelLists lab
        (SignedSphere.norm (SignedSphere.y p n i)) := by
  rw [SignedTargetOrbits.actualTotalNorm_eq_geometricTotalNorm hp]
  change SignedTargetOrbits.totalInclusion
      (SignedTargetOrbits.geometricTotalNorm (liftSphere hp lab hadm i hi)) = _
  simp only [SignedTargetOrbits.geometricTotalNorm, SignedSphere.norm,
    LinearMap.sum_apply]
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [SignedTargetOrbits.totalInclusion_targetAct,
    totalInclusion_liftSphere]
  exact (ReducedLabelEquivariance.positiveLabelLists_equivariant
    lab heq a (SignedSphere.y p n i)).symm

theorem boundary_liftSphere_succ [NeZero p]
    (hp : p.Prime)
    (lab : NonzeroSignedVector p n → Vertex p m)
    (heq : IsEquivariant lab)
    (hadm : IsAlphaAdmissible alpha lab)
    (i : ℕ) (hi : i + 1 < n) :
    AllowedDescent.totalBoundary (liftSphere hp lab hadm (i + 1) hi) =
      (AllowedDescent.datum hp).op (i + 1)
        (liftSphere hp lab hadm i (by omega)) := by
  apply SignedTargetOrbits.totalInclusion_injective
  rw [AllowedDescent.totalInclusion_boundary,
    totalInclusion_liftSphere,
    PositiveTarget.labelLists_boundary,
    SignedSphere.boundary_y_succ hi]
  by_cases hodd : Odd (i + 1)
  · rw [PeriodicDescent.Datum.op, if_pos hodd,
      SignedSphere.periodicOp, if_pos (Nat.odd_iff.mp hodd)]
    exact (totalInclusion_tau_liftSphere hp lab heq hadm i (by omega)).symm
  · rw [PeriodicDescent.Datum.op, if_neg hodd,
      SignedSphere.periodicOp, if_neg (by
        intro hmod
        exact hodd (Nat.odd_iff.mpr hmod))]
    exact (totalInclusion_norm_liftSphere hp lab heq hadm i (by omega)).symm

theorem liftSphere_top_eq_zero [NeZero p]
    (hp : p.Prime) (halpha : alpha ≤ m)
    (lab : NonzeroSignedVector p n → Vertex p m)
    (hadm : IsAlphaAdmissible alpha lab)
    (hQn : alpha + (m - alpha) * (p - 1) < n) :
    liftSphere hp lab hadm
        (alpha + (m - alpha) * (p - 1)) hQn = 0 := by
  apply SignedTargetOrbits.totalInclusion_injective
  rw [totalInclusion_liftSphere]
  let Q := alpha + (m - alpha) * (p - 1)
  have hm := PositiveAllowed.labelLists_mem_allowedPositiveDegree_of_supported_exact
    hp lab hadm (SignedSphere.y_supported_exact hQn)
  change TargetChains.positiveInclusion ℤ (Vertex p m)
      (PositiveTarget.labelLists lab (SignedSphere.y p n Q)) ∈
    AllowedFaces.allowedDegreeChains ℤ p m alpha ((Q + 1) - 1) at hm
  have hdeg : (Q + 1) - 1 = Q := by omega
  rw [hdeg, AllowedFaces.allowedDegreeChains_Q_eq_bot halpha] at hm
  have hz : TargetChains.positiveInclusion ℤ (Vertex p m)
      (PositiveTarget.labelLists lab (SignedSphere.y p n Q)) = 0 :=
    (Submodule.mem_bot ℤ).mp hm
  apply Subtype.ext
  exact hz

noncomputable def resolutionSequence [NeZero p]
    (hp : p.Prime)
    (lab : NonzeroSignedVector p n → Vertex p m)
    (hadm : IsAlphaAdmissible alpha lab)
    (hQn : alpha + (m - alpha) * (p - 1) < n) :
    ℕ → Total p m alpha := fun i =>
  if hi : i ≤ alpha + (m - alpha) * (p - 1) then
    liftSphere hp lab hadm i (hi.trans_lt hQn)
  else 0

theorem resolutionSequence_rel [NeZero p]
    (hp : p.Prime) (halpha : alpha ≤ m)
    (lab : NonzeroSignedVector p n → Vertex p m)
    (heq : IsEquivariant lab)
    (hadm : IsAlphaAdmissible alpha lab)
    (hQn : alpha + (m - alpha) * (p - 1) < n) (i : ℕ) :
    (AllowedDescent.datum hp).boundary
        (resolutionSequence hp lab hadm hQn (i + 1)) =
      (AllowedDescent.datum hp).op (i + 1)
        (resolutionSequence hp lab hadm hQn i) := by
  let Q := alpha + (m - alpha) * (p - 1)
  by_cases hs : i + 1 ≤ Q
  · have hi : i ≤ Q := by omega
    have hsucc : resolutionSequence hp lab hadm hQn (i + 1) =
        liftSphere hp lab hadm (i + 1) (hs.trans_lt hQn) := by
      rw [resolutionSequence, dif_pos hs]
    have hcur : resolutionSequence hp lab hadm hQn i =
        liftSphere hp lab hadm i (hi.trans_lt hQn) := by
      rw [resolutionSequence, dif_pos hi]
    rw [hsucc, hcur]
    exact boundary_liftSphere_succ hp lab heq hadm i
      ((show i + 1 ≤ Q from hs).trans_lt hQn)
  · have hsucc : resolutionSequence hp lab hadm hQn (i + 1) = 0 := by
      rw [resolutionSequence, dif_neg hs]
    rw [hsucc, map_zero]
    by_cases hi : i ≤ Q
    · have hiQ : i = Q := by omega
      subst i
      rw [show resolutionSequence hp lab hadm hQn Q =
          liftSphere hp lab hadm Q hQn by
            rw [resolutionSequence, dif_pos (le_refl Q)]]
      rw [liftSphere_top_eq_zero hp halpha lab hadm hQn, map_zero]
    · rw [show resolutionSequence hp lab hadm hQn i = 0 by
          rw [resolutionSequence, dif_neg hi], map_zero]

theorem resolutionSequence_top [NeZero p]
    (hp : p.Prime) (halpha : alpha ≤ m)
    (lab : NonzeroSignedVector p n → Vertex p m)
    (hadm : IsAlphaAdmissible alpha lab)
    (hQn : alpha + (m - alpha) * (p - 1) < n) :
    resolutionSequence hp lab hadm hQn
        (alpha + (m - alpha) * (p - 1)) = 0 := by
  rw [show resolutionSequence hp lab hadm hQn
      (alpha + (m - alpha) * (p - 1)) =
      liftSphere hp lab hadm
        (alpha + (m - alpha) * (p - 1)) hQn by
    rw [resolutionSequence, dif_pos (le_refl _)]]
  exact liftSphere_top_eq_zero hp halpha lab hadm hQn

theorem augmentation_liftSphere_zero [NeZero p]
    (hp : p.Prime)
    (lab : NonzeroSignedVector p n → Vertex p m)
    (hadm : IsAlphaAdmissible alpha lab)
    (hn : 0 < n) :
    PositiveTarget.augmentation ℤ (Vertex p m)
        (SignedTargetOrbits.totalInclusion
          (liftSphere hp lab hadm 0 hn)) = 1 := by
  rw [totalInclusion_liftSphere, SignedSphere.y_zero hn]
  let x : NonzeroSignedVector p n := SignedSphere.unit ⟨0, hn⟩ 0
  change PositiveTarget.augmentation ℤ (Vertex p m)
      (PositiveTarget.labelLists lab (SourceFlags.basis [x])) = 1
  change TargetChains.boundary ℤ (Vertex p m)
      (TargetChains.positiveInclusion ℤ (Vertex p m)
        (PositiveTarget.labelLists lab (SourceFlags.basis [x]))) ∅ = 1
  rw [PositiveTarget.positiveInclusion_labelLists_basis_of_nonempty
    lab [x] (by simp)]
  rw [TargetBridge.boundary_labelList]
  simp [SourceFlags.boundaryBasis, PositiveTarget.labelList_nil_eq_single_empty]

theorem augmentation_totalNorm [NeZero p] (hp : p.Prime)
    (c : Total p m alpha) :
    PositiveTarget.augmentation ℤ (Vertex p m)
        (SignedTargetOrbits.totalInclusion
          (SignedTargetOrbits.actualTotalNorm hp c)) =
      (p : ℤ) * PositiveTarget.augmentation ℤ (Vertex p m)
        (SignedTargetOrbits.totalInclusion c) := by
  rw [SignedTargetOrbits.actualTotalNorm_eq_geometricTotalNorm hp]
  change PositiveTarget.augmentation ℤ (Vertex p m)
      (SignedTargetOrbits.totalInclusion
        (SignedTargetOrbits.geometricTotalNorm c)) = _
  change PositiveTarget.augmentation ℤ (Vertex p m)
      (SignedTargetOrbits.totalInclusion
        ((∑ a : ZMod p, SignedTargetOrbits.totalTargetAct a) c)) = _
  rw [LinearMap.sum_apply, map_sum, map_sum]
  simp_rw [SignedTargetOrbits.totalInclusion_targetAct,
    augmentation_targetAct]
  simp

theorem zpTucker_alpha
    {p n m alpha : ℕ} (hp : p.Prime) (halpha : alpha ≤ m)
    (lab : NonzeroSignedVector p n → ZMod p × Fin m)
    (heq : IsEquivariant lab)
    (hadm : IsAlphaAdmissible alpha lab) :
    n ≤ alpha + (m - alpha) * (p - 1) := by
  by_contra hle
  have hQn : alpha + (m - alpha) * (p - 1) < n := by omega
  letI : NeZero p := ⟨hp.ne_zero⟩
  let seq := resolutionSequence hp lab hadm hQn
  obtain ⟨z₁, z₀, hdecomp⟩ :=
    (AllowedDescent.datum hp).bottom_decomposition seq
      (resolutionSequence_rel hp halpha lab heq hadm hQn)
      (alpha + (m - alpha) * (p - 1))
      (resolutionSequence_top hp halpha lab hadm hQn)
  have haug0 : PositiveTarget.augmentation ℤ (Vertex p m)
      (SignedTargetOrbits.totalInclusion (seq 0)) = 1 := by
    change PositiveTarget.augmentation ℤ (Vertex p m)
      (SignedTargetOrbits.totalInclusion
        (resolutionSequence hp lab hadm hQn 0)) = 1
    rw [show resolutionSequence hp lab hadm hQn 0 =
        liftSphere hp lab hadm 0 (by omega) by
      simp [resolutionSequence]]
    exact augmentation_liftSphere_zero hp lab hadm (by omega)
  have h : (1 : ℤ) = (p : ℤ) *
      PositiveTarget.augmentation ℤ (Vertex p m)
        (SignedTargetOrbits.totalInclusion z₀) := by
    change seq 0 = AllowedDescent.totalBoundary z₁ +
      SignedTargetOrbits.actualTotalNorm hp z₀ at hdecomp
    rw [← haug0, hdecomp, map_add, map_add,
      AllowedDescent.totalInclusion_boundary,
      PositiveTarget.augmentation_boundary,
      zero_add, augmentation_totalNorm hp]
  have hdivZ : (p : ℤ) ∣ 1 := ⟨_, h⟩
  have hdivN : p ∣ 1 := by exact_mod_cast hdivZ
  have hp2 : 2 ≤ p := hp.two_le
  have hple := Nat.le_of_dvd (by decide : 0 < 1) hdivN
  omega

#print axioms zpTucker_alpha

end

end Erdos780Core
