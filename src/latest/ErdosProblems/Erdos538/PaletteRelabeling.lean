import Mathlib.GroupTheory.GroupAction.Quotient
import ErdosProblems.Erdos538.AsymptoticPalette
import ErdosProblems.Erdos538.WeightedAveraging

/- Ported from Lean 4.31.0 to 4.33.0; imports, namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos538.IsotropicKernel

noncomputable section

/-- Permutations of the palette ground set act on uniform children by mapping
the underlying finset. -/
instance uniformChildrenSMul (m d : ℕ) :
    SMul (Equiv.Perm (Fin m)) (UniformChildren m d) where
  smul σ S := ⟨S.1.map σ.toEmbedding, by simp [S.2]⟩

instance uniformChildrenMulAction (m d : ℕ) :
    MulAction (Equiv.Perm (Fin m)) (UniformChildren m d) where
  one_smul S := by
    apply Subtype.ext
    change S.1.map (1 : Equiv.Perm (Fin m)).toEmbedding = S.1
    have h : (1 : Equiv.Perm (Fin m)).toEmbedding =
        Function.Embedding.refl (Fin m) := by
      ext x
      simp
    rw [h, Finset.map_refl]
  mul_smul σ τ S := by
    apply Subtype.ext
    change S.1.map (σ * τ).toEmbedding =
      (S.1.map τ.toEmbedding).map σ.toEmbedding
    rw [Finset.map_map]
    congr 1

/-- The permutation action is transitive on one uniform layer. -/
instance uniformChildrenPretransitive (m d : ℕ) :
    MulAction.IsPretransitive (Equiv.Perm (Fin m)) (UniformChildren m d) where
  exists_smul_eq S T := by
    obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_map_finset_eq S.1 T.1
      (S.2.trans T.2.symm)
    refine ⟨σ, ?_⟩
    exact Subtype.ext hσ

/-- A chosen transporter identifies the stabilizer of `x` with every action
fiber over `y`. -/
def stabilizerEquivSmulFiber
    {G C : Type*} [Group G] [MulAction G C]
    (x y : C) (g₀ : G) (hg₀ : g₀ • x = y) :
    MulAction.stabilizer G x ≃ {g : G // g • x = y} where
  toFun h := ⟨g₀ * h.1, by rw [mul_smul, h.2, hg₀]⟩
  invFun g := ⟨g₀⁻¹ * g.1, by
    rw [MulAction.mem_stabilizer_iff, mul_smul, g.2, ← hg₀,
      inv_smul_smul]⟩
  left_inv h := by
    apply Subtype.ext
    simp
  right_inv g := by
    apply Subtype.ext
    simp

/-- In a finite transitive action, every action fiber has the stabilizer's
cardinality. -/
theorem card_smulFiber
    {G C : Type*} [Group G] [MulAction G C]
    [Fintype G] [Fintype C] [DecidableEq C]
    [MulAction.IsPretransitive G C]
    (x y : C) :
    Fintype.card {g : G // g • x = y} =
      Fintype.card (MulAction.stabilizer G x) := by
  obtain ⟨g₀, hg₀⟩ := MulAction.exists_smul_eq G x y
  exact Fintype.card_congr (stabilizerEquivSmulFiber x y g₀ hg₀).symm

/-- The permutations sending `x` into a finite target family are a disjoint
union of one action fiber for each target. -/
def goodSmulEquivSigma
    {G C : Type*} [Group G] [MulAction G C]
    (x : C) (F : Finset C) :
    {g : G // g • x ∈ F} ≃
      Σ y : F, {g : G // g • x = y.1} where
  toFun g := ⟨⟨g.1 • x, g.2⟩, ⟨g.1, rfl⟩⟩
  invFun z := ⟨z.2.1, z.2.2.symm ▸ z.1.2⟩
  left_inv g := Subtype.ext rfl
  right_inv z := by
    rcases z with ⟨⟨y, hy⟩, ⟨g, hg⟩⟩
    simp only
    cases hg
    rfl

/-- Exact cardinality of a good relabeling event. -/
theorem card_good_smul
    {G C : Type*} [Group G] [MulAction G C]
    [Fintype G] [Fintype C] [DecidableEq C]
    [MulAction.IsPretransitive G C]
    (x : C) (F : Finset C) :
    (Finset.univ.filter fun g : G => g • x ∈ F).card =
      F.card * Fintype.card (MulAction.stabilizer G x) := by
  classical
  have hfilter : (Finset.univ.filter fun g : G => g • x ∈ F).card =
      Fintype.card {g : G // g • x ∈ F} :=
    (Fintype.card_subtype _).symm
  rw [hfilter, Fintype.card_congr (goodSmulEquivSigma x F),
    Fintype.card_sigma]
  calc
    (∑ y : F, Fintype.card {g : G // g • x = y.1}) =
        ∑ _y : F, Fintype.card (MulAction.stabilizer G x) := by
      apply Finset.sum_congr rfl
      intro y _
      exact card_smulFiber x y.1
    _ = F.card * Fintype.card (MulAction.stabilizer G x) := by simp

/-- A density inequality on a transitive finite layer gives the corresponding
uniform lower fraction of good group relabelings for every object. -/
theorem group_card_le_mul_good_smul
    {G C : Type*} [Group G] [MulAction G C]
    [Fintype G] [Fintype C] [DecidableEq C]
    [MulAction.IsPretransitive G C]
    (x : C) (F : Finset C) (Q : ℕ)
    (hdense : Fintype.card C ≤ Q * F.card) :
    Fintype.card G ≤
      Q * (Finset.univ.filter fun g : G => g • x ∈ F).card := by
  classical
  have horbit := MulAction.card_orbit_mul_card_stabilizer_eq_card_group G x
  have horbitcard : Fintype.card (MulAction.orbit G x) = Fintype.card C := by
    rw [MulAction.orbit_eq_univ]
    simp
  rw [horbitcard] at horbit
  rw [card_good_smul]
  calc
    Fintype.card G = Fintype.card C *
        Fintype.card (MulAction.stabilizer G x) := horbit.symm
    _ ≤ (Q * F.card) * Fintype.card (MulAction.stabilizer G x) :=
      Nat.mul_le_mul_right _ hdense
    _ = Q * (F.card * Fintype.card (MulAction.stabilizer G x)) := by ring

end

end Erdos538.IsotropicKernel

namespace Erdos538

noncomputable section

/-- Weighted finite incidence averaging with a cleared uniform fraction. -/
theorem exists_weighted_sample_many
    {Ω C : Type*} [Fintype Ω] [Nonempty Ω] [Fintype C]
    (Sel : Ω → C → Prop) [DecidableRel Sel]
    (w : C → ℚ≥0) (Q : ℕ)
    (hcol : ∀ c : C,
      Fintype.card Ω ≤ Q * (Finset.univ.filter fun ω => Sel ω c).card) :
    ∃ ω : Ω, (∑ c, w c) ≤
      Q • ∑ c ∈ Finset.univ.filter (Sel ω), w c := by
  classical
  have hevent (c : C) :
      (Finset.univ.filter fun ω => Sel ω c).card • w c =
        ∑ ω : Ω, if Sel ω c then w c else 0 := by
    simp only [nsmul_eq_mul]
    rw [← Finset.sum_filter]
    simp
  have hdouble :
      ∑ c : C, (Finset.univ.filter fun ω => Sel ω c).card • w c =
        ∑ ω : Ω, ∑ c ∈ Finset.univ.filter (Sel ω), w c := by
    calc
      (∑ c : C, (Finset.univ.filter fun ω => Sel ω c).card • w c) =
          ∑ c : C, ∑ ω : Ω, if Sel ω c then w c else 0 := by
        apply Finset.sum_congr rfl
        intro c _
        exact hevent c
      _ = ∑ ω : Ω, ∑ c : C, if Sel ω c then w c else 0 := by
        rw [Finset.sum_comm]
      _ = ∑ ω : Ω, ∑ c ∈ Finset.univ.filter (Sel ω), w c := by
        apply Finset.sum_congr rfl
        intro ω _
        rw [Finset.sum_filter]
  have hlower : Fintype.card Ω • (∑ c, w c) ≤
      Q • ∑ ω : Ω, ∑ c ∈ Finset.univ.filter (Sel ω), w c := by
    simp only [nsmul_eq_mul]
    rw [Finset.mul_sum]
    calc
      ∑ c : C, (Fintype.card Ω : ℚ≥0) * w c ≤
          ∑ c : C,
            (Q * (Finset.univ.filter fun ω => Sel ω c).card : ℕ) * w c := by
        apply Finset.sum_le_sum
        intro c _
        gcongr
        exact_mod_cast hcol c
      _ = (Q : ℚ≥0) *
          ∑ c : C, (Finset.univ.filter fun ω => Sel ω c).card • w c := by
        simp only [nsmul_eq_mul]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro c _
        push_cast
        ring
      _ = (Q : ℚ≥0) *
          ∑ ω : Ω, ∑ c ∈ Finset.univ.filter (Sel ω), w c := by rw [hdouble]
  by_contra h
  push_neg at h
  have hupper : Q • (∑ ω : Ω,
      ∑ c ∈ Finset.univ.filter (Sel ω), w c) <
      Fintype.card Ω • (∑ c, w c) := by
    calc
      Q • (∑ ω : Ω, ∑ c ∈ Finset.univ.filter (Sel ω), w c) =
          ∑ ω : Ω, Q • (∑ c ∈ Finset.univ.filter (Sel ω), w c) := by
        rw [Finset.sum_nsmul]
      _ < ∑ _ω : Ω, ∑ c, w c := by
        apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
        intro ω _
        exact h ω
      _ = Fintype.card Ω • (∑ c, w c) := by simp
  exact (not_lt_of_ge hlower) hupper

end

end Erdos538
