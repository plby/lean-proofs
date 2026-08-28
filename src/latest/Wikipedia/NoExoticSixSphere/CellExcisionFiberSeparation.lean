import Wikipedia.NoExoticSixSphere.ManifoldImageDimension

/-!
# Separating projected cell fibers by the actual dimension bound

Two local coordinate maps are evaluated at a common parameter but
independent time coordinates. Their joint image has dimension at most
the parameter dimension plus two. If the sum of the cell dimensions is
larger, its complement is dense. Thus points can be chosen in arbitrary
prescribed open cell-coordinate sets whose fibers have disjoint
projections to the common parameter space.
-/

noncomputable section

open Set Module TopologicalSpace
open scoped ContDiff ENNReal

namespace NoExoticSixSphere.CellExcisionFiberSeparation

variable {E A B : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup A] [NormedSpace ℝ A] [FiniteDimensional ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]

def joint (F : ℝ × E → A) (G : ℝ × E → B) (z : ℝ × (ℝ × E)) : A × B :=
  (F (z.1, z.2.2), G (z.2.1, z.2.2))

def domain (U V : Opens (ℝ × E)) : Opens (ℝ × (ℝ × E)) :=
  ⟨{z | (z.1, z.2.2) ∈ U ∧ (z.2.1, z.2.2) ∈ V},
    (U.isOpen.preimage (continuous_fst.prodMk (continuous_snd.comp continuous_snd))).inter
      (V.isOpen.preimage continuous_snd)⟩

theorem contDiffOn_joint (F : ℝ × E → A) (G : ℝ × E → B)
    (U V : Opens (ℝ × E)) (hF : ContDiffOn ℝ 1 F U) (hG : ContDiffOn ℝ 1 G V) :
    ContDiffOn ℝ 1 (joint F G) (domain U V) :=
  (hF.comp (contDiff_fst.prodMk (contDiff_snd.comp contDiff_snd)).contDiffOn
    (fun _ hz ↦ hz.1)).prodMk
      (hG.comp contDiff_snd.contDiffOn (fun _ hz ↦ hz.2))

theorem dense_compl_joint_image (F : ℝ × E → A) (G : ℝ × E → B)
    (U V : Opens (ℝ × E)) (hF : ContDiffOn ℝ 1 F U) (hG : ContDiffOn ℝ 1 G V)
    (hd : finrank ℝ E + 2 < finrank ℝ A + finrank ℝ B) :
    Dense (joint F G '' (domain U V : Set (ℝ × (ℝ × E))))ᶜ := by
  have hi := dimH_image_le_of_contDiffOn_isOpen (domain U V).isOpen
    (contDiffOn_joint F G U V hF hG)
  have hs : dimH (domain U V : Set (ℝ × (ℝ × E))) ≤
      finrank ℝ (ℝ × (ℝ × E)) :=
    (dimH_mono (subset_univ _)).trans_eq (Real.dimH_univ_eq_finrank _)
  have hdim : finrank ℝ (ℝ × (ℝ × E)) < finrank ℝ (A × B) := by
    simp only [finrank_prod, finrank_self]
    omega
  exact dense_compl_of_dimH_lt_finrank ((hi.trans hs).trans_lt (Nat.cast_lt.mpr hdim))

def projectedFiber (F : ℝ × E → A) (U : Opens (ℝ × E)) (a : A) : Set E :=
  Prod.snd '' ((U : Set (ℝ × E)) ∩ F ⁻¹' {a})

theorem exists_disjoint_projected_fibers
    (F : ℝ × E → A) (G : ℝ × E → B) (U V : Opens (ℝ × E))
    (hF : ContDiffOn ℝ 1 F U) (hG : ContDiffOn ℝ 1 G V)
    (hd : finrank ℝ E + 2 < finrank ℝ A + finrank ℝ B)
    (O : Set A) (W : Set B) (hO : IsOpen O) (hW : IsOpen W)
    (hneO : O.Nonempty) (hneW : W.Nonempty) :
    ∃ a ∈ O, ∃ b ∈ W, Disjoint (projectedFiber F U a) (projectedFiber G V b) := by
  obtain ⟨⟨a, b⟩, ⟨ha, hb⟩, hnot⟩ :=
    (dense_compl_joint_image F G U V hF hG hd).inter_open_nonempty (O ×ˢ W)
      (hO.prod hW) (hneO.prod hneW)
  refine ⟨a, ha, b, hb, Set.disjoint_left.mpr ?_⟩
  intro p hpF hpG
  obtain ⟨⟨s, q⟩, ⟨hs, hFa⟩, hqp⟩ := hpF
  obtain ⟨⟨t, r⟩, ⟨ht, hGb⟩, hrp⟩ := hpG
  change q = p at hqp
  change r = p at hrp
  subst q
  subst r
  exact hnot ⟨(s, t, p), ⟨hs, ht⟩, Prod.ext hFa hGb⟩

end NoExoticSixSphere.CellExcisionFiberSeparation
