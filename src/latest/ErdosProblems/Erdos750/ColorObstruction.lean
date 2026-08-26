import ErdosProblems.Erdos750.Chains
import ErdosProblems.Erdos780.External.Erdos780Core

/-!
# The coloring obstruction for signed biclique chains

A proper `k`-coloring maps signed biclique faces to the crosspolytope on
`k` colors. The existing integral cyclic-resolution descent applies to its
free antipodal action. Normalization kills every simplex of length `k+1`.
-/

namespace Erdos750.Chains

open SourceFlags SignedSphere
open scoped BigOperators

noncomputable section
universe u
variable {V : Type u} {G : SimpleGraph V} {k : ℕ}

local instance : LinearOrder (ZMod 2 × Fin k) := LabelChainMap.targetLinearOrder

lemma linearMap_mem {A M : Type*} [AddCommGroup M]
    (L : Chain A →ₗ[ℤ] M) (S : Submodule ℤ M) {P : List A → Prop}
    (hL : ∀ l, P l → L (basis l) ∈ S) {c : Chain A} (hc : Supported P c) :
    L c ∈ S := by
  have he : L c = ∑ l ∈ c.support, c l • L (basis l) := by
    calc
      L c = L (c.sum Finsupp.single) := congrArg L (Finsupp.sum_single c).symm
      _ = _ := by
        simp only [Finsupp.sum, map_sum]
        apply Finset.sum_congr rfl
        intro l hl
        rw [show Finsupp.single l (c l) = c l • basis l by simp [basis], map_smul]
  rw [he]
  exact S.sum_mem fun l hl => S.smul_mem _ (hL l (hc l (Finsupp.mem_support_iff.mp hl)))

def colorLabel (C : G.Coloring (Fin k)) : Signed V → ZMod 2 × Fin k :=
  fun x => (x.1, C x.2)

lemma face_same_color {C : G.Coloring (Fin k)} {l : List (Signed V)} (hl : Face G l)
    {a b : Signed V} (ha : a ∈ l) (hb : b ∈ l) (hc : C a.2 = C b.2) : a.1 = b.1 := by
  by_contra hn
  exact C.valid (hl a ha b hb hn) hc

lemma colorFace_allowed (C : G.Coloring (Fin k)) {l : List (Signed V)} (hl : Face G l) :
    AllowedFaces.IsAllowed k (l.map (colorLabel C)).toFinset := by
  intro j
  simp only [AllowedFaces.capacity, if_pos j.isLt]
  apply Finset.card_le_one.mpr
  intro a ha b hb
  obtain ⟨ha, haj⟩ := Finset.mem_filter.mp ha
  obtain ⟨hb, hbj⟩ := Finset.mem_filter.mp hb
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hb)
  have hcol : C x.2 = C y.2 := haj.trans hbj.symm
  exact Prod.ext (face_same_color hl hx hy hcol) hcol

lemma colorList_allowed (C : G.Coloring (Fin k)) {l : List (Signed V)} (hl : Face G l) :
    PositiveTarget.labelLists (colorLabel C) (basis l) ∈ AllowedComplex.PositiveAllowed 2 k k := by
  rw [PositiveTarget.labelLists_basis]
  obtain ⟨z, hz⟩ := AllowedComplex.labelList_eq_smul_single_toFinset (colorLabel C) l
  rw [hz]
  change TargetChains.positiveInclusion ℤ _
    (TargetChains.projectPositive ℤ _ (z • Finsupp.single _ 1)) ∈
      AllowedFaces.allowedChains ℤ 2 k k
  rw [TargetChains.positiveInclusion_projectPositive]
  apply Submodule.sub_mem
  · apply Submodule.smul_mem
    rw [AllowedFaces.mem_allowedChains]
    intro s hs
    have he := ((Finsupp.mem_support_single _ _ _).mp hs).1
    rw [he]
    convert colorFace_allowed C hl using 1
    ext x
    simp only [List.mem_toFinset]
  · exact AllowedDescent.single_empty_mem_allowed _

lemma colorChain_allowed (C : G.Coloring (Fin k)) {c : Chain (Signed V)}
    (hc : Supported (Face G) c) :
    PositiveTarget.labelLists (colorLabel C) c ∈ AllowedComplex.PositiveAllowed 2 k k :=
  linearMap_mem _ _ (fun _ hl => colorList_allowed C hl) hc

def colorLift (C : G.Coloring (Fin k)) (c : Chain (Signed V)) (hc : Supported (Face G) c) :
    TargetOrbits.TotalChain 2 k k :=
  AllowedComplex.totalChainEquivPositiveAllowed.symm
    ⟨PositiveTarget.labelLists (colorLabel C) c, colorChain_allowed C hc⟩

lemma colorLift_inclusion (C : G.Coloring (Fin k)) (c : Chain (Signed V))
    (hc : Supported (Face G) c) :
    SignedTargetOrbits.totalInclusion (colorLift C c hc) =
      PositiveTarget.labelLists (colorLabel C) c := by
  rw [← AllowedDescent.equiv_coe_eq_totalInclusion]
  simp [colorLift]

lemma colorList_eq_zero (C : G.Coloring (Fin k)) {l : List (Signed V)}
    (hl : Face G l) (hk : k < l.length) : TargetBridge.labelList (colorLabel C) l = 0 := by
  apply TargetBridge.labelList_eq_zero_of_repeated
  intro hinj
  have hcinj : Function.Injective (fun i : Fin l.length => C (l.get i).2) := by
    intro i j hij
    apply hinj
    exact Prod.ext (face_same_color hl (List.get_mem ..) (List.get_mem ..) hij) hij
  have hcard := Fintype.card_le_of_injective _ hcinj
  simp only [Fintype.card_fin] at hcard
  omega

lemma colorChain_eq_zero (C : G.Coloring (Fin k)) {n : ℕ} {c : Chain (Signed V)}
    (hc : Supported (Good G n) c) (hn : k < n) :
    PositiveTarget.labelLists (colorLabel C) c = 0 := by
  apply (Submodule.mem_bot ℤ).mp
  refine linearMap_mem _ ⊥ (P := Good G n) ?_ hc
  intro l hl
  rw [PositiveTarget.labelLists_basis,
    colorList_eq_zero C hl.1 (by have he := hl.2; omega), map_zero]
  exact Submodule.zero_mem _

lemma colorList_flip (C : G.Coloring (Fin k)) (l : List (Signed V)) :
    TargetBridge.labelList (colorLabel C) (l.map flip) =
      TargetChains.map (LabelChainMap.targetShift 1) (TargetBridge.labelList (colorLabel C) l) := by
  apply (TargetChains.toExterior ℤ (ZMod 2 × Fin k)).injective
  rw [TargetChains.toExterior_map]
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, TargetBridge.toExterior_labelList_cons, map_mul,
      ExteriorAlgebra.map_apply_ι, TargetChains.vertexMap_single, ih]
    congr 3
    simp [colorLabel, flip, LabelChainMap.targetShift, add_comm]

lemma colorChain_flip (C : G.Coloring (Fin k)) (c : Chain (Signed V)) :
    PositiveTarget.labelLists (colorLabel C) (swap c) =
      SignedTargetOrbits.targetAct 1 (PositiveTarget.labelLists (colorLabel C) c) := by
  have he : TargetBridge.labelLists (colorLabel C) (swap c) =
      TargetChains.map (LabelChainMap.targetShift 1)
        (TargetBridge.labelLists (colorLabel C) c) := by
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add c d hc hd => simp only [map_add, hc, hd]
    | single l z =>
      rw [show Finsupp.single l z = z • basis l by simp [basis]]
      simp only [swap, map_smul, mapVertices_basis, TargetBridge.labelLists_basis, colorList_flip]
  change TargetChains.projectPositive ℤ _ (TargetBridge.labelLists (colorLabel C) (swap c)) = _
  rw [he]
  exact (TargetChains.projectPositive_map_projectPositive
    (LabelChainMap.targetShift 1) (TargetBridge.labelLists (colorLabel C) c)).symm

lemma colorChain_augmentation (C : G.Coloring (Fin k)) {c : Chain (Signed V)}
    (hc : boundary c = basis []) :
    PositiveTarget.augmentation ℤ _ (PositiveTarget.labelLists (colorLabel C) c) = 1 := by
  change TargetChains.boundary ℤ _ (TargetChains.positiveInclusion ℤ _
    (TargetChains.projectPositive ℤ _ (TargetBridge.labelLists (colorLabel C) c))) ∅ = 1
  rw [TargetChains.boundary_projectPositive, TargetBridge.labelLists_boundary, hc,
    TargetBridge.labelLists_basis, PositiveTarget.labelList_nil_eq_single_empty]
  simp

lemma targetAct_zero (y : PositiveTarget.Chain ℤ (ZMod 2 × Fin k)) :
    SignedTargetOrbits.targetAct 0 y = y := by
  have hf : LabelChainMap.targetShift (p := 2) (m := k) 0 = id := by
    funext x
    simp [LabelChainMap.targetShift]
  have hm (z : TargetChains.FullChain ℤ (ZMod 2 × Fin k)) :
      TargetChains.map (id : ZMod 2 × Fin k → _) z = z := by
    apply (TargetChains.toExterior ℤ (ZMod 2 × Fin k)).injective
    rw [TargetChains.toExterior_map]
    have hv : TargetChains.vertexMap (R := ℤ) (id : ZMod 2 × Fin k → _) = LinearMap.id := by
      ext x
      simp [TargetChains.vertexMap]
    rw [hv]
    simp
  change TargetChains.projectPositive ℤ _
    (TargetChains.map (LabelChainMap.targetShift 0) (TargetChains.positiveInclusion ℤ _ y)) = y
  rw [hf, hm, TargetChains.projectPositive_inclusion]

lemma totalInclusion_norm_two (x : TargetOrbits.TotalChain 2 k k) :
    SignedTargetOrbits.totalInclusion (SignedTargetOrbits.actualTotalNorm (by decide) x) =
      SignedTargetOrbits.targetAct 1 (SignedTargetOrbits.totalInclusion x) +
        SignedTargetOrbits.totalInclusion x := by
  rw [SignedTargetOrbits.actualTotalNorm_eq_geometricTotalNorm]
  change SignedTargetOrbits.totalInclusion
    ((∑ a : ZMod 2, SignedTargetOrbits.totalTargetAct a) x) = _
  rw [LinearMap.sum_apply, map_sum]
  simp_rw [SignedTargetOrbits.totalInclusion_targetAct]
  rw [show (Finset.univ : Finset (ZMod 2)) = {0, 1} by decide]
  simp [targetAct_zero, add_comm]

lemma colorLift_op_inclusion (C : G.Coloring (Fin k)) (c : Chain (Signed V))
    (hc : Supported (Face G) c) (i : ℕ) :
    SignedTargetOrbits.totalInclusion
        ((AllowedDescent.datum (p := 2) (m := k) (alpha := k) (by decide)).op i
          (colorLift C c hc)) =
      PositiveTarget.labelLists (colorLabel C) (op i c) := by
  by_cases hi : Odd i
  · change SignedTargetOrbits.totalInclusion
      ((if Odd i then SignedTargetOrbits.actualTotalTau
        else SignedTargetOrbits.actualTotalNorm (by decide)) (colorLift C c hc)) = _
    rw [if_pos hi]
    change SignedTargetOrbits.totalInclusion
      (SignedTargetOrbits.actualTotalAct (colorLift C c hc) - colorLift C c hc) = _
    rw [map_sub, SignedTargetOrbits.totalInclusion_actualTotalAct, colorLift_inclusion]
    simp [op, hi, ← colorChain_flip]
  · change SignedTargetOrbits.totalInclusion
      ((if Odd i then SignedTargetOrbits.actualTotalTau
        else SignedTargetOrbits.actualTotalNorm (by decide)) (colorLift C c hc)) = _
    rw [if_neg hi, totalInclusion_norm_two, colorLift_inclusion]
    simp [op, hi, ← colorChain_flip]

lemma hasResolution_not_colorable {d : ℕ} (h : HasResolution G d) (hkd : k ≤ d) :
    ¬G.Colorable k := by
  rintro ⟨C⟩
  obtain ⟨c, hc, hzero, hrel⟩ := h
  let lift (i : ℕ) (hi : i ≤ d) := colorLift C (c i)
    ((hc i hi).mono (fun _ h => h.1))
  let y : ℕ → TargetOrbits.TotalChain 2 k k := fun i =>
    if hi : i ≤ k then lift i (hi.trans hkd) else 0
  let P := AllowedDescent.datum (p := 2) (m := k) (alpha := k) (by decide)
  have hy (i : ℕ) (hi : i ≤ k) : y i = lift i (hi.trans hkd) := dif_pos hi
  have htop : y k = 0 := by
    rw [hy k le_rfl]
    apply SignedTargetOrbits.totalInclusion_injective
    rw [map_zero, colorLift_inclusion]
    exact colorChain_eq_zero C (hc k hkd) (by omega)
  have hyzero {i : ℕ} (hi : k ≤ i) : y i = 0 := by
    rcases hi.eq_or_lt with rfl | hi
    · exact htop
    · simp [y, show ¬i ≤ k by omega]
  have hyrel (i : ℕ) : P.boundary (y (i + 1)) = P.op (i + 1) (y i) := by
    by_cases hik : i < k
    · rw [hy (i + 1) (by omega), hy i (by omega)]
      apply SignedTargetOrbits.totalInclusion_injective
      change SignedTargetOrbits.totalInclusion
        (AllowedDescent.totalBoundary (lift (i + 1) (by omega))) = _
      rw [AllowedDescent.totalInclusion_boundary, colorLift_inclusion,
        PositiveTarget.labelLists_boundary, hrel i (by omega), colorLift_op_inclusion]
    · rw [hyzero (by omega : k ≤ i + 1), hyzero (by omega : k ≤ i)]
      simp
  obtain ⟨z₁, z₀, hz⟩ := P.bottom_decomposition y hyrel k htop
  have haug : PositiveTarget.augmentation ℤ _
      (SignedTargetOrbits.totalInclusion (y 0)) = 1 := by
    rw [hy 0 (Nat.zero_le _), colorLift_inclusion]
    exact colorChain_augmentation C hzero
  have heq : (1 : ℤ) = 2 * PositiveTarget.augmentation ℤ _
      (SignedTargetOrbits.totalInclusion z₀) := by
    change y 0 = AllowedDescent.totalBoundary z₁ +
      SignedTargetOrbits.actualTotalNorm (by decide) z₀ at hz
    rw [← haug, hz, map_add, map_add, AllowedDescent.totalInclusion_boundary,
      PositiveTarget.augmentation_boundary, zero_add, Erdos780Core.augmentation_totalNorm]
    rfl
  omega

end
end Erdos750.Chains
