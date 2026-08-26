/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Released under the Apache 2.0 license. This file has been modified. -/
/-
Erdős Problem 180. Informal proof: Astra (internal OpenAI model).
Formalization: Astra (internal OpenAI model), OpenAI team.
Source: https://www.erdosproblems.com/forum/thread/180#post-8255
https://github.com/openai/ten-proofs/blob/a13547c6be4563746881d0b3b4c9fd03f72f0484/CompactnessAndDegeneracy.lean
Original Lean/Mathlib version: 4.32.0. Ported to 4.33.0.
-/
import ErdosProblems.Erdos180.Foundations

set_option linter.mathlibStandardSet false

namespace Erdos180

section Geometry

open SimpleGraph

section SymplecticGeometry

variable (K : Type*) [Field K]

abbrev SymplecticVector := Fin 4 → K

def standardSymplecticForm
    (u v : SymplecticVector K) : K :=
  u 0 * v 1 - u 1 * v 0 +
    (u 2 * v 3 - u 3 * v 2)

theorem standardSymplecticForm_self
    (u : SymplecticVector K) :
    standardSymplecticForm K u u = 0 := by
  unfold standardSymplecticForm
  ring

lemma standardSymplecticForm_swap
    (u v : SymplecticVector K) :
    standardSymplecticForm K u v =
      -standardSymplecticForm K v u := by
  unfold standardSymplecticForm
  ring

lemma standardSymplecticForm_add_left
    (u v w : SymplecticVector K) :
    standardSymplecticForm K (u + v) w =
      standardSymplecticForm K u w + standardSymplecticForm K v w := by
  simp only [standardSymplecticForm, Pi.add_apply]
  ring

lemma standardSymplecticForm_add_right
    (u v w : SymplecticVector K) :
    standardSymplecticForm K u (v + w) =
      standardSymplecticForm K u v + standardSymplecticForm K u w := by
  simp only [standardSymplecticForm, Pi.add_apply]
  ring

lemma standardSymplecticForm_smul_left
    (a : K) (u v : SymplecticVector K) :
    standardSymplecticForm K (a • u) v =
      a * standardSymplecticForm K u v := by
  simp only [standardSymplecticForm, Pi.smul_apply, smul_eq_mul]
  ring

lemma standardSymplecticForm_smul_right
    (a : K) (u v : SymplecticVector K) :
    standardSymplecticForm K u (a • v) =
      a * standardSymplecticForm K u v := by
  simp only [standardSymplecticForm, Pi.smul_apply, smul_eq_mul]
  ring

theorem standardSymplecticForm_nondegenerate_left
    (u : SymplecticVector K)
    (h : ∀ v : SymplecticVector K,
      standardSymplecticForm K u v = 0) : u = 0 := by
  funext i
  fin_cases i
  · simpa [standardSymplecticForm] using h ![0, 1, 0, 0]
  · simpa [standardSymplecticForm] using h ![1, 0, 0, 0]
  · simpa [standardSymplecticForm] using h ![0, 0, 0, 1]
  · simpa [standardSymplecticForm] using h ![0, 0, 1, 0]

theorem standardSymplecticForm_nondegenerate_right
    (u : SymplecticVector K)
    (h : ∀ v : SymplecticVector K,
      standardSymplecticForm K v u = 0) : u = 0 := by
  apply standardSymplecticForm_nondegenerate_left K u
  intro v
  rw [standardSymplecticForm_swap, h v, neg_zero]

def standardSymplecticBilin :
    LinearMap.BilinForm K (SymplecticVector K) :=
  LinearMap.mk₂ K (standardSymplecticForm K)
    (standardSymplecticForm_add_left K)
    (fun a u v => by
      simpa [smul_eq_mul] using standardSymplecticForm_smul_left K a u v)
    (standardSymplecticForm_add_right K)
    (fun a u v => by
      simpa [smul_eq_mul] using standardSymplecticForm_smul_right K a u v)

theorem standardSymplecticBilin_nondegenerate :
    (standardSymplecticBilin K).Nondegenerate := by
  constructor
  · intro u hu
    exact standardSymplecticForm_nondegenerate_left K u hu
  · intro u hu
    exact standardSymplecticForm_nondegenerate_right K u hu

theorem standardSymplecticBilin_isAlt :
    (standardSymplecticBilin K).IsAlt := by
  intro u
  exact standardSymplecticForm_self K u

abbrev SymplecticPoint :=
  {P : Submodule K (SymplecticVector K) //
    Module.finrank K P = 1}

abbrev SymplecticLine :=
  {L : Submodule K (SymplecticVector K) //
    Module.finrank K L = 2 ∧
      ∀ u ∈ L, ∀ v ∈ L, standardSymplecticForm K u v = 0}

abbrev SymplecticPointOrthogonal (p : SymplecticPoint K) :=
  (standardSymplecticBilin K).orthogonal p.1

lemma symplecticPoint_le_orthogonal (p : SymplecticPoint K) :
    p.1 ≤ SymplecticPointOrthogonal K p := by
  intro x hx
  change ∀ y ∈ p.1, standardSymplecticForm K y x = 0
  intro y hy
  by_cases hx0 : x = 0
  · simp [hx0, standardSymplecticForm]
  · have hxsub : (⟨x, hx⟩ : p.1) ≠ 0 := by
      intro h
      apply hx0
      simpa using congrArg Subtype.val h
    obtain ⟨a, ha⟩ := exists_smul_eq_of_finrank_eq_one
      p.2 hxsub (⟨y, hy⟩ : p.1)
    have hav : a • x = y := congrArg Subtype.val ha
    rw [← hav, standardSymplecticForm_smul_left,
      standardSymplecticForm_self, mul_zero]

lemma symplecticPointOrthogonal_finrank
    (p : SymplecticPoint K) :
    Module.finrank K (SymplecticPointOrthogonal K p) = 3 := by
  change Module.finrank K
    ((standardSymplecticBilin K).orthogonal p.1) = 3
  rw [LinearMap.BilinForm.finrank_orthogonal
    (standardSymplecticBilin_nondegenerate K), p.2]
  simp [SymplecticVector]

abbrev SymplecticPointRadical (p : SymplecticPoint K) :
    Submodule K (SymplecticPointOrthogonal K p) :=
  Submodule.comap (SymplecticPointOrthogonal K p).subtype p.1

lemma symplecticPointRadical_finrank
    (p : SymplecticPoint K) :
    Module.finrank K (SymplecticPointRadical K p) = 1 := by
  exact (Submodule.comapSubtypeEquivOfLe
    (symplecticPoint_le_orthogonal K p)).finrank_eq.trans p.2

abbrev SymplecticPointQuotient (p : SymplecticPoint K) :=
  (SymplecticPointOrthogonal K p) ⧸ (SymplecticPointRadical K p)

lemma symplecticPointQuotient_finrank
    (p : SymplecticPoint K) :
    Module.finrank K (SymplecticPointQuotient K p) = 2 := by
  change Module.finrank K
    (↥(SymplecticPointOrthogonal K p) ⧸
      SymplecticPointRadical K p) = 2
  have h := Submodule.finrank_quotient_add_finrank
    (SymplecticPointRadical K p)
  rw [symplecticPointRadical_finrank K p,
    symplecticPointOrthogonal_finrank K p] at h
  omega

lemma quotient_map_finrank
    {W : Type*} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W]
    (R S : Submodule K W) (hRS : R ≤ S) :
    Module.finrank K (Submodule.map R.mkQ S) +
      Module.finrank K R = Module.finrank K S := by
  have h := LinearMap.finrank_range_add_finrank_ker
    (R.mkQ.domRestrict S)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict,
    Submodule.ker_mkQ,
    (Submodule.comapSubtypeEquivOfLe hRS).finrank_eq] at h
  exact h

lemma symplecticLine_le_pointOrthogonal
    {p : SymplecticPoint K} {L : SymplecticLine K}
    (hpL : p.1 ≤ L.1) : L.1 ≤ SymplecticPointOrthogonal K p := by
  intro x hx
  change ∀ y ∈ p.1, standardSymplecticForm K y x = 0
  intro y hy
  exact L.2.2 y (hpL hy) x hx

lemma symplectic_two_plane_isotropic
    {p : SymplecticPoint K}
    {S : Submodule K (SymplecticVector K)}
    (hdim : Module.finrank K S = 2)
    (hpS : p.1 ≤ S)
    (hSorth : S ≤ SymplecticPointOrthogonal K p) :
    ∀ u ∈ S, ∀ v ∈ S, standardSymplecticForm K u v = 0 := by
  intro u hu v hv
  by_cases huP : u ∈ p.1
  · exact hSorth hv u huP
  · have hle : p.1 ⊔ K ∙ u ≤ S := by
      apply sup_le hpS
      exact (Submodule.span_le).mpr (by simpa using hu)
    have hspan : p.1 ⊔ K ∙ u = S :=
      Submodule.eq_of_le_of_finrank_eq hle (by
        rw [Submodule.finrank_sup_span_singleton huP, p.2, hdim])
    have hvspan : v ∈ p.1 ⊔ K ∙ u := hspan.symm ▸ hv
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hvspan
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hb
    have horth : standardSymplecticForm K a u = 0 :=
      hSorth hu a ha
    have hreverse : standardSymplecticForm K u a = 0 := by
      rw [standardSymplecticForm_swap, horth, neg_zero]
    rw [standardSymplecticForm_add_right,
      standardSymplecticForm_smul_right,
      standardSymplecticForm_self,
      hreverse, mul_zero, add_zero]

abbrev SymplecticLinesOnPoint (p : SymplecticPoint K) :=
  {L : SymplecticLine K // p.1 ≤ L.1}

abbrev SymplecticLineInPointOrthogonal
    (p : SymplecticPoint K) (L : SymplecticLine K) :
    Submodule K (SymplecticPointOrthogonal K p) :=
  Submodule.comap (SymplecticPointOrthogonal K p).subtype L.1

lemma symplecticLineInPointOrthogonal_finrank
    {p : SymplecticPoint K} {L : SymplecticLine K}
    (hpL : p.1 ≤ L.1) :
    Module.finrank K (SymplecticLineInPointOrthogonal K p L) = 2 := by
  exact (Submodule.comapSubtypeEquivOfLe
    (symplecticLine_le_pointOrthogonal K hpL)).finrank_eq.trans L.2.1

lemma symplecticPointRadical_le_lineInPointOrthogonal
    {p : SymplecticPoint K} {L : SymplecticLine K}
    (hpL : p.1 ≤ L.1) :
    SymplecticPointRadical K p ≤
      SymplecticLineInPointOrthogonal K p L :=
  Submodule.comap_mono hpL

noncomputable def symplecticLinesOnPointEquivSubmodule
    (p : SymplecticPoint K) :
    SymplecticLinesOnPoint K p ≃
      {S : Submodule K (SymplecticPointQuotient K p) //
        Module.finrank K S = 1} where
  toFun L :=
    ⟨Submodule.map (SymplecticPointRadical K p).mkQ
       (SymplecticLineInPointOrthogonal K p L.1), by
       change Module.finrank K
         (Submodule.map (SymplecticPointRadical K p).mkQ
           (SymplecticLineInPointOrthogonal K p L.1)) = 1
       have h := quotient_map_finrank K
         (SymplecticPointRadical K p)
         (SymplecticLineInPointOrthogonal K p L.1)
         (symplecticPointRadical_le_lineInPointOrthogonal K L.2)
       rw [symplecticPointRadical_finrank K p,
         symplecticLineInPointOrthogonal_finrank K L.2] at h
       omega⟩
  invFun Q := by
    let T : Submodule K (SymplecticPointOrthogonal K p) :=
      Submodule.comap (SymplecticPointRadical K p).mkQ Q.1
    have hrad : SymplecticPointRadical K p ≤ T :=
      Submodule.le_comap_mkQ (SymplecticPointRadical K p) Q.1
    have hmap :
        Submodule.map (SymplecticPointRadical K p).mkQ T = Q.1 := by
      apply Submodule.map_comap_eq_self
      rw [Submodule.range_mkQ]
      exact le_top
    have hdimT : Module.finrank K T = 2 := by
      have h := quotient_map_finrank K
        (SymplecticPointRadical K p) T hrad
      rw [hmap, Q.2, symplecticPointRadical_finrank K p] at h
      omega
    let S : Submodule K (SymplecticVector K) :=
      Submodule.map (SymplecticPointOrthogonal K p).subtype T
    have hdimS : Module.finrank K S = 2 := by
      exact (Submodule.finrank_map_subtype_eq
        (SymplecticPointOrthogonal K p) T).trans hdimT
    have hSorth : S ≤ SymplecticPointOrthogonal K p := by
      intro x hx
      rcases hx with ⟨y, _, rfl⟩
      exact y.2
    have hpS : p.1 ≤ S := by
      intro x hx
      have hxorth : x ∈ SymplecticPointOrthogonal K p :=
        symplecticPoint_le_orthogonal K p hx
      have hxrad :
          (⟨x, hxorth⟩ : SymplecticPointOrthogonal K p) ∈
            SymplecticPointRadical K p := hx
      exact ⟨⟨x, hxorth⟩, hrad hxrad, rfl⟩
    exact ⟨⟨S, hdimS,
      symplectic_two_plane_isotropic K hdimS hpS hSorth⟩, hpS⟩
  left_inv L := by
    apply Subtype.ext
    apply Subtype.ext
    change Submodule.map (SymplecticPointOrthogonal K p).subtype
      (Submodule.comap (SymplecticPointRadical K p).mkQ
        (Submodule.map (SymplecticPointRadical K p).mkQ
          (SymplecticLineInPointOrthogonal K p L.1))) = L.1.1
    rw [Submodule.comap_map_mkQ,
      sup_eq_right.mpr
        (symplecticPointRadical_le_lineInPointOrthogonal K L.2)]
    change Submodule.map (SymplecticPointOrthogonal K p).subtype
      (Submodule.comap (SymplecticPointOrthogonal K p).subtype
        L.1.1) = L.1.1
    rw [Submodule.map_comap_subtype]
    exact inf_eq_right.mpr
      (symplecticLine_le_pointOrthogonal K L.2)
  right_inv Q := by
    apply Subtype.ext
    change Submodule.map (SymplecticPointRadical K p).mkQ
      (Submodule.comap (SymplecticPointOrthogonal K p).subtype
        (Submodule.map (SymplecticPointOrthogonal K p).subtype
          (Submodule.comap (SymplecticPointRadical K p).mkQ
            Q.1))) = Q.1
    rw [Submodule.comap_map_eq,
      LinearMap.ker_eq_bot.mpr
        (SymplecticPointOrthogonal K p).subtype_injective,
      sup_bot_eq]
    apply Submodule.map_comap_eq_self
    rw [Submodule.range_mkQ]
    exact le_top

noncomputable def symplecticLinesOnPointEquiv
    (p : SymplecticPoint K) :
    SymplecticLinesOnPoint K p ≃
      Projectivization K (SymplecticPointQuotient K p) :=
  (symplecticLinesOnPointEquivSubmodule K p).trans
    (Projectivization.equivSubmodule K
      (SymplecticPointQuotient K p)).symm

lemma symplecticLinesOnPoint_card [Finite K]
    (p : SymplecticPoint K) :
    Nat.card (SymplecticLinesOnPoint K p) = Nat.card K + 1 := by
  rw [Nat.card_congr (symplecticLinesOnPointEquiv K p)]
  exact Projectivization.card_of_finrank_two K
    (SymplecticPointQuotient K p)
    (symplecticPointQuotient_finrank K p)

abbrev SymplecticPointsOnLine (L : SymplecticLine K) :=
  {p : SymplecticPoint K // p.1 ≤ L.1}

noncomputable def symplecticPointsOnLineEquivSubmodule
    (L : SymplecticLine K) :
    SymplecticPointsOnLine K L ≃
      {S : Submodule K L.1 // Module.finrank K S = 1} where
  toFun p :=
    ⟨Submodule.comap L.1.subtype p.1.1,
      (Submodule.comapSubtypeEquivOfLe p.2).finrank_eq.trans p.1.2⟩
  invFun S :=
    ⟨⟨Submodule.map L.1.subtype S.1,
       (Submodule.finrank_map_subtype_eq L.1 S.1).trans S.2⟩,
      by
        intro x hx
        rcases hx with ⟨y, _, rfl⟩
        exact y.2⟩
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    change Submodule.map L.1.subtype
      (Submodule.comap L.1.subtype p.1.1) = p.1.1
    rw [Submodule.map_comap_subtype]
    exact inf_eq_right.mpr p.2
  right_inv S := by
    apply Subtype.ext
    change Submodule.comap L.1.subtype
      (Submodule.map L.1.subtype S.1) = S.1
    rw [Submodule.comap_map_eq,
      LinearMap.ker_eq_bot.mpr L.1.subtype_injective, sup_bot_eq]

noncomputable def symplecticPointsOnLineEquiv
    (L : SymplecticLine K) :
    SymplecticPointsOnLine K L ≃ Projectivization K L.1 :=
  (symplecticPointsOnLineEquivSubmodule K L).trans
    (Projectivization.equivSubmodule K L.1).symm

lemma symplecticPointsOnLine_card [Finite K]
    (L : SymplecticLine K) :
    Nat.card (SymplecticPointsOnLine K L) = Nat.card K + 1 := by
  rw [Nat.card_congr (symplecticPointsOnLineEquiv K L)]
  exact Projectivization.card_of_finrank_two K L.1 L.2.1

lemma symplecticPoint_sup_finrank
    {p q : SymplecticPoint K} (hpq : p ≠ q) :
    Module.finrank K
      (p.1 ⊔ q.1 : Submodule K (SymplecticVector K)) = 2 := by
  have hne : p.1 ≠ q.1 := fun h => hpq (Subtype.ext h)
  have hd : Disjoint p.1 q.1 :=
    (Submodule.isAtom_iff_finrank_eq_one.mpr p.2).disjoint_of_ne
      (Submodule.isAtom_iff_finrank_eq_one.mpr q.2) hne
  have hrank := Submodule.finrank_sup_add_finrank_inf_eq p.1 q.1
  rw [hd.eq_bot, finrank_bot, p.2, q.2] at hrank
  omega

lemma symplecticLine_eq_of_points
    {p q : SymplecticPoint K} (hpq : p ≠ q)
    {L M : SymplecticLine K}
    (hpL : p.1 ≤ L.1) (hqL : q.1 ≤ L.1)
    (hpM : p.1 ≤ M.1) (hqM : q.1 ≤ M.1) : L = M := by
  have hsupL : p.1 ⊔ q.1 ≤ L.1 := sup_le hpL hqL
  have hsupM : p.1 ⊔ q.1 ≤ M.1 := sup_le hpM hqM
  have hL : p.1 ⊔ q.1 = L.1 :=
    Submodule.eq_of_le_of_finrank_eq hsupL
      ((symplecticPoint_sup_finrank K hpq).trans L.2.1.symm)
  have hM : p.1 ⊔ q.1 = M.1 :=
    Submodule.eq_of_le_of_finrank_eq hsupM
      ((symplecticPoint_sup_finrank K hpq).trans M.2.1.symm)
  exact Subtype.ext (hL.symm.trans hM)

lemma symplectic_isotropic_finrank_le_two
    (S : Submodule K (SymplecticVector K))
    (hS : ∀ u ∈ S, ∀ v ∈ S,
      standardSymplecticForm K u v = 0) :
    Module.finrank K S ≤ 2 := by
  have hle : S ≤ (standardSymplecticBilin K).orthogonal S := by
    intro x hx
    change ∀ y ∈ S, standardSymplecticForm K y x = 0
    intro y hy
    exact hS y hy x hx
  have hrank := Submodule.finrank_mono hle
  rw [LinearMap.BilinForm.finrank_orthogonal
    (standardSymplecticBilin_nondegenerate K)] at hrank
  have hambient : Module.finrank K (SymplecticVector K) = 4 := by
    simp [SymplecticVector]
  rw [hambient] at hrank
  omega

lemma symplectic_triangle_points_collinear
    {p q r : SymplecticPoint K} (hpq : p ≠ q)
    {Lpq Lpr Lqr : SymplecticLine K}
    (hpLpq : p.1 ≤ Lpq.1) (hqLpq : q.1 ≤ Lpq.1)
    (hpLpr : p.1 ≤ Lpr.1) (hrLpr : r.1 ≤ Lpr.1)
    (hqLqr : q.1 ≤ Lqr.1) (hrLqr : r.1 ≤ Lqr.1) :
    r.1 ≤ Lpq.1 := by
  let T : Submodule K (SymplecticVector K) :=
    (p.1 ⊔ q.1) ⊔ r.1
  have hiso : ∀ u ∈ T, ∀ v ∈ T,
      standardSymplecticForm K u v = 0 := by
    intro u hu v hv
    obtain ⟨ab, hab, c, hc, rfl⟩ := Submodule.mem_sup.mp hu
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hab
    obtain ⟨de, hde, f, hf, rfl⟩ := Submodule.mem_sup.mp hv
    obtain ⟨d, hd, e, he, rfl⟩ := Submodule.mem_sup.mp hde
    have had := Lpq.2.2 a (hpLpq ha) d (hpLpq hd)
    have hae := Lpq.2.2 a (hpLpq ha) e (hqLpq he)
    have haf := Lpr.2.2 a (hpLpr ha) f (hrLpr hf)
    have hbd := Lpq.2.2 b (hqLpq hb) d (hpLpq hd)
    have hbe := Lpq.2.2 b (hqLpq hb) e (hqLpq he)
    have hbf := Lqr.2.2 b (hqLqr hb) f (hrLqr hf)
    have hcd := Lpr.2.2 c (hrLpr hc) d (hpLpr hd)
    have hce := Lqr.2.2 c (hrLqr hc) e (hqLqr he)
    have hcf := Lpr.2.2 c (hrLpr hc) f (hrLpr hf)
    simp [standardSymplecticForm_add_left,
      standardSymplecticForm_add_right,
      had, hae, haf, hbd, hbe, hbf, hcd, hce, hcf]
  have hbound : Module.finrank K T ≤ 2 :=
    symplectic_isotropic_finrank_le_two K T hiso
  have hspan : p.1 ⊔ q.1 = T :=
    Submodule.eq_of_le_of_finrank_le le_sup_left
      (by simpa [symplecticPoint_sup_finrank K hpq] using hbound)
  exact (show r.1 ≤ T from le_sup_right).trans
    (hspan.symm ▸ sup_le hpLpq hqLpq)

lemma symplectic_triangle_lines_eq
    {p q r : SymplecticPoint K}
    (hpq : p ≠ q) (hqr : q ≠ r)
    {Lpq Lpr Lqr : SymplecticLine K}
    (hpLpq : p.1 ≤ Lpq.1) (hqLpq : q.1 ≤ Lpq.1)
    (hpLpr : p.1 ≤ Lpr.1) (hrLpr : r.1 ≤ Lpr.1)
    (hqLqr : q.1 ≤ Lqr.1) (hrLqr : r.1 ≤ Lqr.1) :
    Lpq = Lqr := by
  have hrLpq : r.1 ≤ Lpq.1 := symplectic_triangle_points_collinear K hpq
    hpLpq hqLpq hpLpr hrLpr hqLqr hrLqr
  exact symplecticLine_eq_of_points K hqr hqLpq hrLpq hqLqr hrLqr

abbrev QuadrangleVertex :=
  SymplecticPoint K ⊕ SymplecticLine K

def quadrangleIncidence :
    QuadrangleVertex K → QuadrangleVertex K → Prop
  | .inl point, .inr line => (point.1 : Submodule K _) ≤ line.1
  | _, _ => False

def symplecticQuadrangle : SimpleGraph (QuadrangleVertex K) :=
  SimpleGraph.fromRel (quadrangleIncidence K)

theorem symplecticQuadrangle_incidence_adj
    (p : SymplecticPoint K) (L : SymplecticLine K) :
    (symplecticQuadrangle K).Adj (.inl p) (.inr L) ↔ p.1 ≤ L.1 := by
  simp [symplecticQuadrangle, SimpleGraph.fromRel_adj, quadrangleIncidence]

theorem symplecticQuadrangle_adjacent_to_point
    {p : SymplecticPoint K} {v : QuadrangleVertex K}
    (h : (symplecticQuadrangle K).Adj (.inl p) v) :
    ∃ L : SymplecticLine K, v = .inr L ∧ p.1 ≤ L.1 := by
  rcases v with q | L
  · simp [symplecticQuadrangle, SimpleGraph.fromRel_adj,
      quadrangleIncidence] at h
  · exact ⟨L, rfl, (symplecticQuadrangle_incidence_adj K p L).mp h⟩

theorem symplecticQuadrangle_adjacent_to_line
    {L : SymplecticLine K} {v : QuadrangleVertex K}
    (h : (symplecticQuadrangle K).Adj (.inr L) v) :
    ∃ p : SymplecticPoint K, v = .inl p ∧ p.1 ≤ L.1 := by
  rcases v with p | M
  · exact ⟨p, rfl,
      (symplecticQuadrangle_incidence_adj K p L).mp h.symm⟩
  · simp [symplecticQuadrangle, SimpleGraph.fromRel_adj,
      quadrangleIncidence] at h

theorem symplecticQuadrangle_common_neighbor_unique
    {u v : QuadrangleVertex K} (huv : u ≠ v)
    {w z : QuadrangleVertex K}
    (huw : (symplecticQuadrangle K).Adj u w)
    (hvw : (symplecticQuadrangle K).Adj v w)
    (huz : (symplecticQuadrangle K).Adj u z)
    (hvz : (symplecticQuadrangle K).Adj v z) : w = z := by
  rcases u with p | L <;>
    rcases v with q | M <;>
    rcases w with r | R <;>
    rcases z with s | S <;>
    simp [symplecticQuadrangle, SimpleGraph.fromRel_adj,
      quadrangleIncidence] at huw hvw huz hvz
  · apply congrArg Sum.inr
    apply symplecticLine_eq_of_points K
      (fun hpq => huv (congrArg Sum.inl hpq))
    · exact huw
    · exact hvw
    · exact huz
    · exact hvz
  · apply congrArg Sum.inl
    by_contra hrs
    have hlines : L = M := symplecticLine_eq_of_points K hrs
      huw huz hvw hvz
    exact huv (congrArg Sum.inr hlines)

theorem symplecticQuadrangle_four_cycle_free :
    (SimpleGraph.cycleGraph 4).Free (symplecticQuadrangle K) := by
  rintro ⟨copy⟩
  have h01 : (symplecticQuadrangle K).Adj (copy 0) (copy 1) :=
    copy.toHom.map_rel (by decide)
  have h21 : (symplecticQuadrangle K).Adj (copy 2) (copy 1) :=
    copy.toHom.map_rel (by decide)
  have h03 : (symplecticQuadrangle K).Adj (copy 0) (copy 3) :=
    copy.toHom.map_rel (by decide)
  have h23 : (symplecticQuadrangle K).Adj (copy 2) (copy 3) :=
    copy.toHom.map_rel (by decide)
  have h02 : copy 0 ≠ copy 2 := fun h =>
    (by decide : (0 : Fin 4) ≠ 2) (copy.injective h)
  have h13 : copy 1 = copy 3 :=
    symplecticQuadrangle_common_neighbor_unique K h02 h01 h21 h03 h23
  exact (by decide : (1 : Fin 4) ≠ 3) (copy.injective h13)

theorem symplecticQuadrangle_six_cycle_free :
    (SimpleGraph.cycleGraph 6).Free (symplecticQuadrangle K) := by
  rintro ⟨copy⟩
  have h01 : (symplecticQuadrangle K).Adj (copy 0) (copy 1) :=
    copy.toHom.map_rel
      (show (SimpleGraph.cycleGraph 6).Adj 0 1 by decide)
  have h12 : (symplecticQuadrangle K).Adj (copy 1) (copy 2) :=
    copy.toHom.map_rel
      (show (SimpleGraph.cycleGraph 6).Adj 1 2 by decide)
  have h23 : (symplecticQuadrangle K).Adj (copy 2) (copy 3) :=
    copy.toHom.map_rel
      (show (SimpleGraph.cycleGraph 6).Adj 2 3 by decide)
  have h34 : (symplecticQuadrangle K).Adj (copy 3) (copy 4) :=
    copy.toHom.map_rel
      (show (SimpleGraph.cycleGraph 6).Adj 3 4 by decide)
  have h45 : (symplecticQuadrangle K).Adj (copy 4) (copy 5) :=
    copy.toHom.map_rel
      (show (SimpleGraph.cycleGraph 6).Adj 4 5 by decide)
  have h50 : (symplecticQuadrangle K).Adj (copy 5) (copy 0) :=
    copy.toHom.map_rel
      (show (SimpleGraph.cycleGraph 6).Adj 5 0 by decide)
  cases h0 : copy 0 with
  | inl p =>
      rw [h0] at h01 h50
      obtain ⟨L, h1, hpL⟩ :=
        symplecticQuadrangle_adjacent_to_point K h01
      rw [h1] at h12
      obtain ⟨q, h2, hqL⟩ :=
        symplecticQuadrangle_adjacent_to_line K h12
      rw [h2] at h23
      obtain ⟨M, h3, hqM⟩ :=
        symplecticQuadrangle_adjacent_to_point K h23
      rw [h3] at h34
      obtain ⟨r, h4, hrM⟩ :=
        symplecticQuadrangle_adjacent_to_line K h34
      rw [h4] at h45
      obtain ⟨N, h5, hrN⟩ :=
        symplecticQuadrangle_adjacent_to_point K h45
      rw [h5] at h50
      have hpN : p.1 ≤ N.1 :=
        (symplecticQuadrangle_incidence_adj K p N).mp h50.symm
      have hpq : p ≠ q := by
        intro heq
        apply (by decide : (0 : Fin 6) ≠ 2)
        apply copy.injective
        change copy 0 = copy 2
        rw [h0, h2, heq]
      have hqr : q ≠ r := by
        intro heq
        apply (by decide : (2 : Fin 6) ≠ 4)
        apply copy.injective
        change copy 2 = copy 4
        rw [h2, h4, heq]
      have hLM : L = M := symplectic_triangle_lines_eq K hpq hqr
        hpL hqL hpN hrN hqM hrM
      apply (by decide : (1 : Fin 6) ≠ 3)
      apply copy.injective
      change copy 1 = copy 3
      rw [h1, h3, hLM]
  | inr L =>
      rw [h0] at h01 h50
      obtain ⟨p, h1, hpL⟩ :=
        symplecticQuadrangle_adjacent_to_line K h01
      rw [h1] at h12
      obtain ⟨M, h2, hpM⟩ :=
        symplecticQuadrangle_adjacent_to_point K h12
      rw [h2] at h23
      obtain ⟨q, h3, hqM⟩ :=
        symplecticQuadrangle_adjacent_to_line K h23
      rw [h3] at h34
      obtain ⟨N, h4, hqN⟩ :=
        symplecticQuadrangle_adjacent_to_point K h34
      rw [h4] at h45
      obtain ⟨r, h5, hrN⟩ :=
        symplecticQuadrangle_adjacent_to_line K h45
      rw [h5] at h50
      have hrL : r.1 ≤ L.1 :=
        (symplecticQuadrangle_incidence_adj K r L).mp h50
      have hpq : p ≠ q := by
        intro heq
        apply (by decide : (1 : Fin 6) ≠ 3)
        apply copy.injective
        change copy 1 = copy 3
        rw [h1, h3, heq]
      have hqr : q ≠ r := by
        intro heq
        apply (by decide : (3 : Fin 6) ≠ 5)
        apply copy.injective
        change copy 3 = copy 5
        rw [h3, h5, heq]
      have hMN : M = N := symplectic_triangle_lines_eq K hpq hqr
        hpM hqM hpL hrL hqN hrN
      apply (by decide : (2 : Fin 6) ≠ 4)
      apply copy.injective
      change copy 2 = copy 4
      rw [h2, h4, hMN]

lemma symplecticPoint_card [Finite K] :
    Nat.card (SymplecticPoint K) =
      (Nat.card K + 1) * ((Nat.card K) ^ 2 + 1) := by
  calc
    Nat.card (SymplecticPoint K) =
        Nat.card (Projectivization K (SymplecticVector K)) :=
      Nat.card_congr
        (Projectivization.equivSubmodule K (SymplecticVector K)).symm
    _ = ∑ i ∈ Finset.range 4, (Nat.card K) ^ i :=
      Projectivization.card_of_finrank K (SymplecticVector K) (by simp)
    _ = (Nat.card K + 1) * ((Nat.card K) ^ 2 + 1) := by
      simp [Finset.sum_range_succ]
      ring

abbrev SymplecticIncidence :=
  {x : SymplecticPoint K × SymplecticLine K // x.1.1 ≤ x.2.1}

def symplecticIncidenceEquivSigmaPoints :
    SymplecticIncidence K ≃
      (Σ p : SymplecticPoint K, SymplecticLinesOnPoint K p) where
  toFun i := ⟨i.1.1, ⟨i.1.2, i.2⟩⟩
  invFun s := ⟨(s.1, s.2.1), s.2.2⟩
  left_inv i := by
    rcases i with ⟨⟨p, L⟩, h⟩
    rfl
  right_inv s := by
    rcases s with ⟨p, ⟨L, h⟩⟩
    rfl

def symplecticIncidenceEquivSigmaLines :
    SymplecticIncidence K ≃
      (Σ L : SymplecticLine K, SymplecticPointsOnLine K L) where
  toFun i := ⟨i.1.2, ⟨i.1.1, i.2⟩⟩
  invFun s := ⟨(s.2.1, s.1), s.2.2⟩
  left_inv i := by
    rcases i with ⟨⟨p, L⟩, h⟩
    rfl
  right_inv s := by
    rcases s with ⟨L, ⟨p, h⟩⟩
    rfl

lemma symplecticIncidence_card_by_points [Finite K] :
    Nat.card (SymplecticIncidence K) =
      Nat.card (SymplecticPoint K) * (Nat.card K + 1) := by
  classical
  let : Fintype (SymplecticPoint K) := Fintype.ofFinite _
  let : Fintype (SymplecticLine K) := Fintype.ofFinite _
  calc
    Nat.card (SymplecticIncidence K) =
        Nat.card (Σ p : SymplecticPoint K,
          SymplecticLinesOnPoint K p) :=
      Nat.card_congr (symplecticIncidenceEquivSigmaPoints K)
    _ = ∑ p : SymplecticPoint K,
          Nat.card (SymplecticLinesOnPoint K p) := by
      simp_rw [Nat.card_eq_fintype_card]
      exact Fintype.card_sigma
    _ = Nat.card (SymplecticPoint K) * (Nat.card K + 1) := by
      simp_rw [symplecticLinesOnPoint_card]
      simp [Nat.card_eq_fintype_card]

lemma symplecticIncidence_card_by_lines [Finite K] :
    Nat.card (SymplecticIncidence K) =
      Nat.card (SymplecticLine K) * (Nat.card K + 1) := by
  classical
  let : Fintype (SymplecticPoint K) := Fintype.ofFinite _
  let : Fintype (SymplecticLine K) := Fintype.ofFinite _
  calc
    Nat.card (SymplecticIncidence K) =
        Nat.card (Σ L : SymplecticLine K,
          SymplecticPointsOnLine K L) :=
      Nat.card_congr (symplecticIncidenceEquivSigmaLines K)
    _ = ∑ L : SymplecticLine K,
          Nat.card (SymplecticPointsOnLine K L) := by
      simp_rw [Nat.card_eq_fintype_card]
      exact Fintype.card_sigma
    _ = Nat.card (SymplecticLine K) * (Nat.card K + 1) := by
      simp_rw [symplecticPointsOnLine_card]
      simp [Nat.card_eq_fintype_card]

lemma symplecticLine_card [Finite K] :
    Nat.card (SymplecticLine K) =
      (Nat.card K + 1) * ((Nat.card K) ^ 2 + 1) := by
  have hcounts :
      Nat.card (SymplecticPoint K) * (Nat.card K + 1) =
        Nat.card (SymplecticLine K) * (Nat.card K + 1) :=
    (symplecticIncidence_card_by_points K).symm.trans
      (symplecticIncidence_card_by_lines K)
  have hline : Nat.card (SymplecticPoint K) =
      Nat.card (SymplecticLine K) :=
    Nat.eq_of_mul_eq_mul_right (Nat.succ_pos _) hcounts
  rw [← hline, symplecticPoint_card]

lemma symplecticIncidence_card [Finite K] :
    Nat.card (SymplecticIncidence K) =
      (Nat.card K + 1) ^ 2 * ((Nat.card K) ^ 2 + 1) := by
  rw [symplecticIncidence_card_by_points, symplecticPoint_card]
  ring

theorem symplecticQuadrangle_vertex_card [Finite K] :
    Nat.card (QuadrangleVertex K) =
      2 * (Nat.card K + 1) * ((Nat.card K) ^ 2 + 1) := by
  rw [Nat.card_sum, symplecticPoint_card, symplecticLine_card]
  ring

def symplecticIncidenceToEdge :
    SymplecticIncidence K → (symplecticQuadrangle K).edgeSet :=
  fun i =>
    ⟨s(Sum.inl i.1.1, Sum.inr i.1.2),
      (symplecticQuadrangle_incidence_adj K i.1.1 i.1.2).mpr i.2⟩

lemma symplecticIncidenceToEdge_injective :
    Function.Injective (symplecticIncidenceToEdge K) := by
  intro i j h
  have hedges := congrArg Subtype.val h
  change s(Sum.inl i.1.1, Sum.inr i.1.2) =
    s(Sum.inl j.1.1, Sum.inr j.1.2) at hedges
  rcases Sym2.eq_iff.mp hedges with ⟨hp, hL⟩ | ⟨hbad, _⟩
  · apply Subtype.ext
    apply Prod.ext
    · exact Sum.inl_injective hp
    · exact Sum.inr_injective hL
  · cases hbad

lemma symplecticIncidenceToEdge_surjective :
    Function.Surjective (symplecticIncidenceToEdge K) := by
  intro e
  obtain ⟨⟨u, v⟩, huv⟩ := Sym2.mk_surjective e.1
  change s(u, v) = e.1 at huv
  have hadj : (symplecticQuadrangle K).Adj u v := by
    apply (symplecticQuadrangle K).mem_edgeSet.mp
    rw [huv]
    exact e.2
  rcases u with p | L <;> rcases v with q | M
  · simp [symplecticQuadrangle, SimpleGraph.fromRel_adj,
      quadrangleIncidence] at hadj
  · refine ⟨⟨(p, M),
        (symplecticQuadrangle_incidence_adj K p M).mp hadj⟩, ?_⟩
    apply Subtype.ext
    exact huv
  · refine ⟨⟨(q, L),
        (symplecticQuadrangle_incidence_adj K q L).mp hadj.symm⟩, ?_⟩
    apply Subtype.ext
    exact Sym2.eq_swap.trans huv
  · simp [symplecticQuadrangle, SimpleGraph.fromRel_adj,
      quadrangleIncidence] at hadj

noncomputable def symplecticIncidenceEquivEdge :
    SymplecticIncidence K ≃ (symplecticQuadrangle K).edgeSet :=
  Equiv.ofBijective (symplecticIncidenceToEdge K)
    ⟨symplecticIncidenceToEdge_injective K,
      symplecticIncidenceToEdge_surjective K⟩

theorem symplecticQuadrangle_edge_card [Finite K] :
    Nat.card (symplecticQuadrangle K).edgeSet =
      (Nat.card K + 1) ^ 2 * ((Nat.card K) ^ 2 + 1) := by
  rw [← Nat.card_congr (symplecticIncidenceEquivEdge K),
    symplecticIncidence_card]

end SymplecticGeometry

section NumericalParameters

def quadrangleVertexCount (q : ℕ) : ℕ :=
  2 * (q + 1) * (q ^ 2 + 1)

def quadrangleEdgeCount (q : ℕ) : ℕ :=
  (q + 1) ^ 2 * (q ^ 2 + 1)

theorem quadrangle_density_certificate (q : ℕ) :
    (quadrangleVertexCount q : ℝ) ^ 4 ≤
      16 * (quadrangleEdgeCount q : ℝ) ^ 3 := by
  have hnonneg :
      0 ≤ 32 * (q : ℝ) * ((q : ℝ) + 1) ^ 4 *
        ((q : ℝ) ^ 2 + 1) ^ 3 := by
    positivity
  have hidentity :
      16 * (quadrangleEdgeCount q : ℝ) ^ 3 -
          (quadrangleVertexCount q : ℝ) ^ 4 =
        32 * (q : ℝ) * ((q : ℝ) + 1) ^ 4 *
          ((q : ℝ) ^ 2 + 1) ^ 3 := by
    simp only [quadrangleVertexCount, quadrangleEdgeCount,
      Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat,
      Nat.cast_one]
    ring
  linarith

theorem quadrangle_rpow_density (q : ℕ) :
    (2 : ℝ) ^ (-((4 : ℝ) / 3)) *
      (quadrangleVertexCount q : ℝ) ^ ((4 : ℝ) / 3) ≤
        (quadrangleEdgeCount q : ℝ) := by
  apply ((by decide : Odd 3).strictMono_pow.le_iff_le).mp
  have hcubed :
      ((2 : ℝ) ^ (-((4 : ℝ) / 3)) *
        (quadrangleVertexCount q : ℝ) ^ ((4 : ℝ) / 3)) ^ 3 =
          (quadrangleVertexCount q : ℝ) ^ 4 / 16 := by
    rw [mul_pow,
      ← Real.rpow_mul_natCast (by norm_num : 0 ≤ (2 : ℝ))
        (-((4 : ℝ) / 3)) 3,
      ← Real.rpow_mul_natCast
        (by exact_mod_cast (Nat.zero_le (quadrangleVertexCount q)))
        ((4 : ℝ) / 3) 3]
    norm_num [Real.rpow_neg, Real.rpow_natCast]
    ring
  rw [hcubed]
  nlinarith [quadrangle_density_certificate q]

theorem quadrangleVertexCount_mul_le
    (q t : ℕ) (ht : 1 ≤ t) :
    quadrangleVertexCount (t * q) ≤
      t ^ 3 * quadrangleVertexCount q := by
  have hfirst : t * q + 1 ≤ t * (q + 1) := by
    nlinarith
  have hsecond : (t * q) ^ 2 + 1 ≤ t ^ 2 * (q ^ 2 + 1) := by
    nlinarith [sq_nonneg (t - 1)]
  unfold quadrangleVertexCount
  calc
    2 * (t * q + 1) * ((t * q) ^ 2 + 1) ≤
        2 * (t * (q + 1)) * (t ^ 2 * (q ^ 2 + 1)) := by
      gcongr
    _ = t ^ 3 * (2 * (q + 1) * (q ^ 2 + 1)) := by
      ring

end NumericalParameters

end Geometry

section Cyclicity

open Finset SimpleGraph

def thetaCycleVertex : Fin 8 → SubdivisionVertex 2 :=
  ![.inl (.inl 0),
    .inr (0, 0),
    .inl (.inr 0),
    .inr (1, 0),
    .inl (.inl 1),
    .inr (1, 1),
    .inl (.inr 1),
    .inr (0, 1)]

def thetaCycleCopy :
    SimpleGraph.Copy (SimpleGraph.cycleGraph 8) thetaGraph := by
  refine ⟨⟨thetaCycleVertex, ?_⟩, ?_⟩
  · intro u v hadj
    fin_cases u <;> fin_cases v <;>
      simp_all [thetaCycleVertex, SubdivisionGraph,
        subdivisionRelation, SimpleGraph.cycleGraph]
    all_goals
      exact (of_decide_eq_false rfl) hadj
  · decide

def jThetaVertex (copy : Fin 2) : SubdivisionVertex 2 → JVertex
  | .inl (.inl base) => .inl (.inl (jBase copy base))
  | .inl (.inr center) => .inl (.inr (copy, center))
  | .inr (base, center) => .inr (.inl (copy, (base, center)))

def jThetaCopy (copy : Fin 2) :
    SimpleGraph.Copy thetaGraph jTemplate := by
  refine ⟨⟨jThetaVertex copy, ?_⟩, ?_⟩
  · intro u v hadj
    rcases (SimpleGraph.fromRel_adj
      (subdivisionRelation 2) u v).mp hadj with
      ⟨hne, hforward | hbackward⟩
    · apply (SimpleGraph.fromRel_adj
        jTemplateRelation (jThetaVertex copy u)
        (jThetaVertex copy v)).mpr
      constructor
      · intro heq
        have hinj : Function.Injective (jThetaVertex copy) := by
          fin_cases copy <;> decide
        exact hne (hinj heq)
      · left
        rcases u with (u | u) | u <;>
          rcases v with (v | v) | v <;>
          simp_all [subdivisionRelation, jTemplateRelation, jThetaVertex]
    · apply (SimpleGraph.fromRel_adj
        jTemplateRelation (jThetaVertex copy u)
        (jThetaVertex copy v)).mpr
      constructor
      · intro heq
        have hinj : Function.Injective (jThetaVertex copy) := by
          fin_cases copy <;> decide
        exact hne (hinj heq)
      · right
        rcases u with (u | u) | u <;>
          rcases v with (v | v) | v <;>
          simp_all [subdivisionRelation, jTemplateRelation, jThetaVertex]
  · fin_cases copy <;> decide

lemma jThetaVertex_mem (copy : Fin 2)
    (v : SubdivisionVertex 2) :
    InJCopy copy (jThetaVertex copy v) := by
  rcases v with (base | center) | pair
  · exact ⟨base, rfl⟩
  · simp [InJCopy, jThetaVertex]
  · simp [InJCopy, jThetaVertex]

def gammaCycleVertex : Fin 8 → SubdivisionVertex 3 :=
  ![.inl (.inl 0),
    .inr (0, 0),
    .inl (.inr 0),
    .inr (1, 0),
    .inl (.inl 1),
    .inr (1, 1),
    .inl (.inr 1),
    .inr (0, 1)]

def gammaCycleCopy :
    SimpleGraph.Copy (SimpleGraph.cycleGraph 8) gammaGraph := by
  refine ⟨⟨gammaCycleVertex, ?_⟩, ?_⟩
  · intro u v hadj
    fin_cases u <;> fin_cases v <;>
      simp_all [gammaCycleVertex, SubdivisionGraph,
        subdivisionRelation, SimpleGraph.cycleGraph]
    all_goals
      exact (of_decide_eq_false rfl) hadj
  · decide

def kGammaVertex (copy : Fin 2)
    (v : SubdivisionVertex 3) : KVertex := (copy, v)

def kGammaCopy (copy : Fin 2) :
    SimpleGraph.Copy gammaGraph kTemplate := by
  refine ⟨⟨kGammaVertex copy, ?_⟩, ?_⟩
  · intro u v hadj
    rcases (SimpleGraph.fromRel_adj
      (subdivisionRelation 3) u v).mp hadj with
      ⟨hne, hforward | hbackward⟩
    · apply (SimpleGraph.fromRel_adj
        kTemplateRelation (kGammaVertex copy u)
        (kGammaVertex copy v)).mpr
      constructor
      · intro heq
        exact hne (congrArg Prod.snd heq)
      · left
        exact Or.inl ⟨rfl, hforward⟩
    · apply (SimpleGraph.fromRel_adj
        kTemplateRelation (kGammaVertex copy u)
        (kGammaVertex copy v)).mpr
      constructor
      · intro heq
        exact hne (congrArg Prod.snd heq)
      · right
        exact Or.inl ⟨rfl, hbackward⟩
  · intro u v h
    exact congrArg Prod.snd h

def copyToQuotient {α β : Type*}
    (source : SimpleGraph β) (target : SimpleGraph α)
    (f : α → α) (copy : SimpleGraph.Copy source target)
    (hinj : Function.Injective (fun v : β => f (copy v))) :
    SimpleGraph.Copy source (quotientGraph target f) := by
  refine ⟨⟨fun v => ⟨f (copy v), ⟨copy v, rfl⟩⟩, ?_⟩, ?_⟩
  · intro u v hadj
    apply (SimpleGraph.fromRel_adj
      (quotientRelation target f) _ _).mpr
    constructor
    · intro heq
      exact hadj.ne (hinj (congrArg Subtype.val heq))
    · left
      exact ⟨copy u, copy v, rfl, rfl, copy.toHom.map_rel hadj⟩
  · intro u v heq
    exact hinj (congrArg Subtype.val heq)

lemma not_acyclic_of_eight_cycle_copy
    {α : Type*} {graph : SimpleGraph α}
    (copy : SimpleGraph.Copy (SimpleGraph.cycleGraph 8) graph) :
    ¬ graph.IsAcyclic := by
  intro hacyclic
  have hcycle : (SimpleGraph.cycleGraph 8).IsAcyclic :=
    hacyclic.comap copy.toHom copy.injective
  exact hcycle (SimpleGraph.cycleGraph.cycle 5)
    (SimpleGraph.cycleGraph.isCycle_cycle)

lemma encodeFiniteGraph_not_acyclic
    {α : Type*} [Fintype α]
    (graph : SimpleGraph α) (h : ¬ graph.IsAcyclic) :
    ¬ (encodeFiniteGraph graph).graph.IsAcyclic := by
  intro hencoded
  apply h
  exact (SimpleGraph.Iso.map (Fintype.equivFin α) graph).isAcyclic_iff.mpr
    hencoded

lemma jTheta_quotient_injective
    {f : JVertex → JVertex} (hf : JAdmissible f)
    (copy : Fin 2) :
    Function.Injective (fun v : SubdivisionVertex 2 =>
      f (jThetaVertex copy v)) := by
  intro u v heq
  have htemplate : jThetaVertex copy u = jThetaVertex copy v :=
    hf.2.2 copy (jThetaVertex_mem copy u)
      (jThetaVertex_mem copy v) heq
  exact (jThetaCopy copy).injective htemplate

theorem jQuotient_not_acyclic
    {f : JVertex → JVertex} (hf : JAdmissible f) :
    ¬ (encodeFiniteGraph (quotientGraph jTemplate f)).graph.IsAcyclic := by
  apply encodeFiniteGraph_not_acyclic
  apply not_acyclic_of_eight_cycle_copy
  exact (copyToQuotient thetaGraph jTemplate f (jThetaCopy 0)
    (jTheta_quotient_injective hf 0)).comp thetaCycleCopy

lemma kGamma_quotient_injective
    {f : KVertex → KVertex} (hf : KAdmissible f)
    (copy : Fin 2) :
    Function.Injective (fun v : SubdivisionVertex 3 =>
      f (kGammaVertex copy v)) := by
  intro u v heq
  have htemplate : kGammaVertex copy u = kGammaVertex copy v :=
    hf.2 copy (show (kGammaVertex copy u).1 = copy from rfl)
      (show (kGammaVertex copy v).1 = copy from rfl) heq
  exact (kGammaCopy copy).injective htemplate

theorem kQuotient_not_acyclic
    {f : KVertex → KVertex} (hf : KAdmissible f) :
    ¬ (encodeFiniteGraph (quotientGraph kTemplate f)).graph.IsAcyclic := by
  apply encodeFiniteGraph_not_acyclic
  apply not_acyclic_of_eight_cycle_copy
  exact (copyToQuotient gammaGraph kTemplate f (kGammaCopy 0)
    (kGamma_quotient_injective hf 0)).comp gammaCycleCopy

theorem four_cycle_not_acyclic :
    ¬ (finiteCycle 4).graph.IsAcyclic := by
  intro h
  exact h (SimpleGraph.cycleGraph.cycle 1)
    SimpleGraph.cycleGraph.isCycle_cycle

theorem six_cycle_not_acyclic :
    ¬ (finiteCycle 6).graph.IsAcyclic := by
  intro h
  exact h (SimpleGraph.cycleGraph.cycle 3)
    SimpleGraph.cycleGraph.isCycle_cycle

theorem proposedFamily_isCyclic : IsCyclicFamily proposedFamily :=
  proposedFamily_induction (P := fun graph => ¬ graph.graph.IsAcyclic)
    four_cycle_not_acyclic six_cycle_not_acyclic
    (fun _ hf => jQuotient_not_acyclic hf)
    (fun _ hf => kQuotient_not_acyclic hf)

end Cyclicity

section CharacteristicAvoidance

open SimpleGraph

section PointClass

variable (K : Type*) [Field K]

def SymplecticPointRelated (p q : SymplecticPoint K) : Prop :=
  p ≠ q ∧ ∃ L : SymplecticLine K, p.1 ≤ L.1 ∧ q.1 ≤ L.1

lemma symplecticPointRelated_symm
    {p q : SymplecticPoint K}
    (h : SymplecticPointRelated K p q) :
    SymplecticPointRelated K q p := by
  obtain ⟨hpq, L, hpL, hqL⟩ := h
  exact ⟨Ne.symm hpq, L, hqL, hpL⟩

lemma symplecticPointRelated_iff_orthogonal
    (p q : SymplecticPoint K) :
    SymplecticPointRelated K p q ↔
      p ≠ q ∧ p.1 ≤ SymplecticPointOrthogonal K q := by
  constructor
  · rintro ⟨hpq, L, hpL, hqL⟩
    refine ⟨hpq, ?_⟩
    intro x hx
    change ∀ y ∈ q.1, standardSymplecticForm K y x = 0
    intro y hy
    exact L.2.2 y (hqL hy) x (hpL hx)
  · rintro ⟨hpq, hporth⟩
    let U : Submodule K (SymplecticVector K) := p.1 ⊔ q.1
    have hdim : Module.finrank K U = 2 :=
      symplecticPoint_sup_finrank K hpq
    have hqU : q.1 ≤ U := le_sup_right
    have hUorth : U ≤ SymplecticPointOrthogonal K q :=
      sup_le hporth (symplecticPoint_le_orthogonal K q)
    exact ⟨hpq,
      ⟨U, hdim, symplectic_two_plane_isotropic K hdim hqU hUorth⟩,
      le_sup_left, le_sup_right⟩

lemma symplecticPointRelated_of_quadrangle_common_neighbor
    {p q : SymplecticPoint K}
    (hpq : p ≠ q) {v : QuadrangleVertex K}
    (hpv : (symplecticQuadrangle K).Adj (.inl p) v)
    (hqv : (symplecticQuadrangle K).Adj (.inl q) v) :
    SymplecticPointRelated K p q := by
  obtain ⟨L, hv, hpL⟩ :=
    symplecticQuadrangle_adjacent_to_point K hpv
  rw [hv] at hqv
  exact ⟨hpq, L, hpL,
    (symplecticQuadrangle_incidence_adj K q L).mp hqv⟩

lemma subdivisionGraph_base_pair_adj
    (k : ℕ) (base : Fin 3) (center : Fin k) :
    (SubdivisionGraph k).Adj
      (.inl (.inl base)) (.inr (base, center)) := by
  simp [SubdivisionGraph, SimpleGraph.fromRel_adj,
    subdivisionRelation]

lemma subdivisionGraph_center_pair_adj
    (k : ℕ) (base : Fin 3) (center : Fin k) :
    (SubdivisionGraph k).Adj
      (.inl (.inr center)) (.inr (base, center)) := by
  simp [SubdivisionGraph, SimpleGraph.fromRel_adj,
    subdivisionRelation]

lemma subdivisionPoint_pair_incidence
    {k : ℕ}
    (copy : SimpleGraph.Copy (SubdivisionGraph k)
      (symplecticQuadrangle K))
    {base : Fin 3} {center : Fin k}
    {p c : SymplecticPoint K}
    (hbase : copy (.inl (.inl base)) = .inl p)
    (hcenter : copy (.inl (.inr center)) = .inl c) :
    ∃ L : SymplecticLine K,
      copy (.inr (base, center)) = .inr L ∧
        p.1 ≤ L.1 ∧ c.1 ≤ L.1 := by
  have hbaseadj := copy.toHom.map_rel
    (subdivisionGraph_base_pair_adj k base center)
  change (symplecticQuadrangle K).Adj
    (copy (.inl (.inl base)))
    (copy (.inr (base, center))) at hbaseadj
  rw [hbase] at hbaseadj
  obtain ⟨L, hpair, hpL⟩ :=
    symplecticQuadrangle_adjacent_to_point K hbaseadj
  have hcenteradj := copy.toHom.map_rel
    (subdivisionGraph_center_pair_adj k base center)
  change (symplecticQuadrangle K).Adj
    (copy (.inl (.inr center)))
    (copy (.inr (base, center))) at hcenteradj
  rw [hcenter, hpair] at hcenteradj
  exact ⟨L, hpair, hpL,
    (symplecticQuadrangle_incidence_adj K c L).mp hcenteradj⟩

lemma subdivisionPoint_center_of_point_base
    {k : ℕ}
    (copy : SimpleGraph.Copy (SubdivisionGraph k)
      (symplecticQuadrangle K))
    {base : Fin 3} {center : Fin k}
    {p : SymplecticPoint K}
    (hbase : copy (.inl (.inl base)) = .inl p) :
    ∃ c : SymplecticPoint K,
      copy (.inl (.inr center)) = .inl c := by
  have hbaseadj := copy.toHom.map_rel
    (subdivisionGraph_base_pair_adj k base center)
  change (symplecticQuadrangle K).Adj
    (copy (.inl (.inl base)))
    (copy (.inr (base, center))) at hbaseadj
  rw [hbase] at hbaseadj
  obtain ⟨L, hpair, _⟩ :=
    symplecticQuadrangle_adjacent_to_point K hbaseadj
  have hcenteradj := copy.toHom.map_rel
    (subdivisionGraph_center_pair_adj k base center)
  change (symplecticQuadrangle K).Adj
    (copy (.inl (.inr center)))
    (copy (.inr (base, center))) at hcenteradj
  rw [hpair] at hcenteradj
  obtain ⟨c, hc, _⟩ :=
    symplecticQuadrangle_adjacent_to_line K hcenteradj.symm
  exact ⟨c, hc⟩

lemma subdivisionPoint_base_of_point_base
    {k : ℕ}
    (copy : SimpleGraph.Copy (SubdivisionGraph k)
      (symplecticQuadrangle K))
    {base otherBase : Fin 3} (center : Fin k)
    {p : SymplecticPoint K}
    (hbase : copy (.inl (.inl base)) = .inl p) :
    ∃ q : SymplecticPoint K,
      copy (.inl (.inl otherBase)) = .inl q := by
  obtain ⟨c, hc⟩ := subdivisionPoint_center_of_point_base K
    copy (center := center) hbase
  have hcenteradj := copy.toHom.map_rel
    (subdivisionGraph_center_pair_adj k otherBase center)
  change (symplecticQuadrangle K).Adj
    (copy (.inl (.inr center)))
    (copy (.inr (otherBase, center))) at hcenteradj
  rw [hc] at hcenteradj
  obtain ⟨L, hpair, _⟩ :=
    symplecticQuadrangle_adjacent_to_point K hcenteradj
  have hotheradj := copy.toHom.map_rel
    (subdivisionGraph_base_pair_adj k otherBase center)
  change (symplecticQuadrangle K).Adj
    (copy (.inl (.inl otherBase)))
    (copy (.inr (otherBase, center))) at hotheradj
  rw [hpair] at hotheradj
  obtain ⟨q, hq, _⟩ :=
    symplecticQuadrangle_adjacent_to_line K hotheradj.symm
  exact ⟨q, hq⟩

lemma subdivisionPoint_base_center_related
    {k : ℕ}
    (copy : SimpleGraph.Copy (SubdivisionGraph k)
      (symplecticQuadrangle K))
    {base : Fin 3} {center : Fin k}
    {p c : SymplecticPoint K}
    (hbase : copy (.inl (.inl base)) = .inl p)
    (hcenter : copy (.inl (.inr center)) = .inl c) :
    SymplecticPointRelated K p c := by
  obtain ⟨L, _, hpL, hcL⟩ :=
    subdivisionPoint_pair_incidence K copy hbase hcenter
  refine ⟨?_, L, hpL, hcL⟩
  intro hpc
  have hvertex :
      (Sum.inl (Sum.inl base) : SubdivisionVertex k) =
        .inl (.inr center) := by
    apply copy.injective
    change copy (.inl (.inl base)) =
      copy (.inl (.inr center))
    rw [hbase, hcenter, hpc]
  cases hvertex

lemma subdivisionPoint_bases_unrelated
    {k : ℕ}
    (copy : SimpleGraph.Copy (SubdivisionGraph k)
      (symplecticQuadrangle K))
    (p : Fin 3 → SymplecticPoint K)
    (c : Fin k → SymplecticPoint K)
    (hbase : ∀ base : Fin 3,
      copy (.inl (.inl base)) = .inl (p base))
    (hcenter : ∀ center : Fin k,
      copy (.inl (.inr center)) = .inl (c center))
    {i j : Fin 3} (hij : i ≠ j) (center : Fin k) :
    ¬ SymplecticPointRelated K (p i) (p j) := by
  obtain ⟨Li, hi_pair, hpiLi, hcLi⟩ :=
    subdivisionPoint_pair_incidence K copy (hbase i)
      (hcenter center)
  obtain ⟨Lj, hj_pair, hpjLj, hcLj⟩ :=
    subdivisionPoint_pair_incidence K copy (hbase j)
      (hcenter center)
  have hic : SymplecticPointRelated K (p i) (c center) :=
    subdivisionPoint_base_center_related K copy (hbase i)
      (hcenter center)
  have hjc : SymplecticPointRelated K (p j) (c center) :=
    subdivisionPoint_base_center_related K copy (hbase j)
      (hcenter center)
  rintro ⟨_, Lij, hpiLij, hpjLij⟩
  have hlines : Li = Lj :=
    symplectic_triangle_lines_eq K hic.1
      (symplecticPointRelated_symm K hjc).1
      hpiLi hcLi hpiLij hpjLij hcLj hpjLj
  have hpair :
      copy (.inr (i, center)) = copy (.inr (j, center)) := by
    rw [hi_pair, hj_pair, hlines]
  have hsource :
      (Sum.inr (i, center) : SubdivisionVertex k) =
        .inr (j, center) := copy.injective hpair
  exact hij (congrArg Prod.fst (Sum.inr.inj hsource))

lemma symplecticPointSpan_orthogonal_finrank
    {y z : SymplecticPoint K} (hyz : y ≠ z) :
    Module.finrank K
      ((standardSymplecticBilin K).orthogonal
        (y.1 ⊔ z.1)) = 2 := by
  rw [LinearMap.BilinForm.finrank_orthogonal
    (standardSymplecticBilin_nondegenerate K),
    symplecticPoint_sup_finrank K hyz]
  simp [SymplecticVector]

lemma symplecticPoint_centers_span_orthogonal
    {y z c d : SymplecticPoint K}
    (hyz : y ≠ z) (hcd : c ≠ d)
    (hcy : c.1 ≤ SymplecticPointOrthogonal K y)
    (hcz : c.1 ≤ SymplecticPointOrthogonal K z)
    (hdy : d.1 ≤ SymplecticPointOrthogonal K y)
    (hdz : d.1 ≤ SymplecticPointOrthogonal K z) :
    c.1 ⊔ d.1 =
      (standardSymplecticBilin K).orthogonal (y.1 ⊔ z.1) := by
  apply Submodule.eq_of_le_of_finrank_eq
  · apply sup_le
    · intro w hw
      change ∀ u ∈ y.1 ⊔ z.1,
        standardSymplecticForm K u w = 0
      intro u hu
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hu
      have haorth : standardSymplecticForm K a w = 0 := by
        have h := hcy hw a ha
        change standardSymplecticForm K a w = 0 at h
        exact h
      have hborth : standardSymplecticForm K b w = 0 := by
        have h := hcz hw b hb
        change standardSymplecticForm K b w = 0 at h
        exact h
      rw [standardSymplecticForm_add_left, haorth, hborth, add_zero]
    · intro w hw
      change ∀ u ∈ y.1 ⊔ z.1,
        standardSymplecticForm K u w = 0
      intro u hu
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hu
      have haorth : standardSymplecticForm K a w = 0 := by
        have h := hdy hw a ha
        change standardSymplecticForm K a w = 0 at h
        exact h
      have hborth : standardSymplecticForm K b w = 0 := by
        have h := hdz hw b hb
        change standardSymplecticForm K b w = 0 at h
        exact h
      rw [standardSymplecticForm_add_left, haorth, hborth, add_zero]
  · rw [symplecticPoint_sup_finrank K hcd,
      symplecticPointSpan_orthogonal_finrank K hyz]

lemma symplecticPoint_mem_span_of_two_centers
    {x y z c d : SymplecticPoint K}
    (hyz : y ≠ z) (hcd : c ≠ d)
    (hcx : c.1 ≤ SymplecticPointOrthogonal K x)
    (hcy : c.1 ≤ SymplecticPointOrthogonal K y)
    (hcz : c.1 ≤ SymplecticPointOrthogonal K z)
    (hdx : d.1 ≤ SymplecticPointOrthogonal K x)
    (hdy : d.1 ≤ SymplecticPointOrthogonal K y)
    (hdz : d.1 ≤ SymplecticPointOrthogonal K z) :
    x.1 ≤ y.1 ⊔ z.1 := by
  have hcenters := symplecticPoint_centers_span_orthogonal K
    hyz hcd hcy hcz hdy hdz
  have hxorth :
      x.1 ≤ (standardSymplecticBilin K).orthogonal (c.1 ⊔ d.1) := by
    intro w hw
    change ∀ u ∈ c.1 ⊔ d.1,
      standardSymplecticForm K u w = 0
    intro u hu
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hu
    rw [standardSymplecticForm_add_left]
    have haorth : standardSymplecticForm K a w = 0 := by
      have h := hcx ha w hw
      change standardSymplecticForm K w a = 0 at h
      rw [standardSymplecticForm_swap, h, neg_zero]
    have hborth : standardSymplecticForm K b w = 0 := by
      have h := hdx hb w hw
      change standardSymplecticForm K w b = 0 at h
      rw [standardSymplecticForm_swap, h, neg_zero]
    rw [haorth, hborth, add_zero]
  rw [hcenters,
    LinearMap.BilinForm.orthogonal_orthogonal
      (standardSymplecticBilin_nondegenerate K)
      (standardSymplecticBilin_isAlt K).isRefl] at hxorth
  exact hxorth

theorem symplecticPoint_point_class_avoidance
    {x x' y z c d c' d' : SymplecticPoint K}
    (hyz : y ≠ z)
    (hyz_unrelated : ¬ SymplecticPointRelated K y z)
    (hxx' : x ≠ x')
    (hcd : c ≠ d) (hc'd' : c' ≠ d')
    (hcx : SymplecticPointRelated K c x)
    (hcy : SymplecticPointRelated K c y)
    (hcz : SymplecticPointRelated K c z)
    (hdx : SymplecticPointRelated K d x)
    (hdy : SymplecticPointRelated K d y)
    (hdz : SymplecticPointRelated K d z)
    (hc'x' : SymplecticPointRelated K c' x')
    (hc'y : SymplecticPointRelated K c' y)
    (hc'z : SymplecticPointRelated K c' z)
    (hd'x' : SymplecticPointRelated K d' x')
    (hd'y : SymplecticPointRelated K d' y)
    (hd'z : SymplecticPointRelated K d' z) :
    ¬ SymplecticPointRelated K x x' := by
  have hxspan : x.1 ≤ y.1 ⊔ z.1 :=
    symplecticPoint_mem_span_of_two_centers K hyz hcd
      ((symplecticPointRelated_iff_orthogonal K c x).mp hcx).2
      ((symplecticPointRelated_iff_orthogonal K c y).mp hcy).2
      ((symplecticPointRelated_iff_orthogonal K c z).mp hcz).2
      ((symplecticPointRelated_iff_orthogonal K d x).mp hdx).2
      ((symplecticPointRelated_iff_orthogonal K d y).mp hdy).2
      ((symplecticPointRelated_iff_orthogonal K d z).mp hdz).2
  have hx'span : x'.1 ≤ y.1 ⊔ z.1 :=
    symplecticPoint_mem_span_of_two_centers K hyz hc'd'
      ((symplecticPointRelated_iff_orthogonal K c' x').mp hc'x').2
      ((symplecticPointRelated_iff_orthogonal K c' y).mp hc'y).2
      ((symplecticPointRelated_iff_orthogonal K c' z).mp hc'z).2
      ((symplecticPointRelated_iff_orthogonal K d' x').mp hd'x').2
      ((symplecticPointRelated_iff_orthogonal K d' y).mp hd'y).2
      ((symplecticPointRelated_iff_orthogonal K d' z).mp hd'z).2
  intro hrelated
  obtain ⟨_, L, hxL, hx'L⟩ := hrelated
  have hspan : x.1 ⊔ x'.1 = y.1 ⊔ z.1 := by
    apply Submodule.eq_of_le_of_finrank_eq (sup_le hxspan hx'span)
    rw [symplecticPoint_sup_finrank K hxx',
      symplecticPoint_sup_finrank K hyz]
  have hyzL : y.1 ⊔ z.1 ≤ L.1 := by
    rw [← hspan]
    exact sup_le hxL hx'L
  exact hyz_unrelated
    ⟨hyz, L, le_sup_left.trans hyzL, le_sup_right.trans hyzL⟩

def colorRespectingQuotientProjectionHom
    {V : Type*} (graph : SimpleGraph V) (color : V → Bool)
    (hproper : ∀ ⦃u v : V⦄, graph.Adj u v → color u ≠ color v)
    (f : V → V) (hf : ColorRespecting color f) :
    graph →g quotientGraph graph f := by
  refine ⟨fun v => ⟨f v, v, rfl⟩, ?_⟩
  intro u v hadj
  apply (SimpleGraph.fromRel_adj
    (quotientRelation graph f)
    (⟨f u, u, rfl⟩ : Set.range f)
    (⟨f v, v, rfl⟩ : Set.range f)).mpr
  constructor
  · intro heq
    exact hproper hadj
      (hf u v (congrArg Subtype.val heq))
  · left
    exact ⟨u, v, rfl, rfl, hadj⟩

lemma jTemplate_adj_color_ne
    {u v : JVertex} (h : jTemplate.Adj u v) :
    jColor u ≠ jColor v := by
  rcases u with (u | u) | (u | u) <;>
    rcases v with (v | v) | (v | v) <;>
    simp_all [jTemplate, SimpleGraph.fromRel_adj,
      jTemplateRelation, jColor]

lemma kTemplate_adj_color_ne
    {u v : KVertex} (h : kTemplate.Adj u v) :
    kColor u ≠ kColor v := by
  rcases u with ⟨u, (u | u) | u⟩ <;>
    rcases v with ⟨v, (v | v) | v⟩ <;>
    fin_cases u <;> fin_cases v <;>
    simp_all [kTemplate, SimpleGraph.fromRel_adj,
      kTemplateRelation, kColor, subdivisionColor,
      subdivisionRelation, kSpecifiedCenter]
  all_goals aesop

def jQuotientProjectionHom
    {f : JVertex → JVertex} (hf : JAdmissible f) :
    jTemplate →g quotientGraph jTemplate f :=
  colorRespectingQuotientProjectionHom jTemplate jColor
    (fun _ _ h => jTemplate_adj_color_ne h) f hf.1

def kQuotientProjectionHom
    {f : KVertex → KVertex} (hf : KAdmissible f) :
    kTemplate →g quotientGraph kTemplate f :=
  colorRespectingQuotientProjectionHom kTemplate kColor
    (fun _ _ h => kTemplate_adj_color_ne h) f hf.1

def jThetaHomCopy
    {V : Type*} {host : SimpleGraph V}
    (hom : jTemplate →g host)
    (hcopies : ∀ copy : Fin 2,
      Set.InjOn hom {v | InJCopy copy v})
    (copy : Fin 2) :
    SimpleGraph.Copy thetaGraph host := by
  refine ⟨hom.comp (jThetaCopy copy).toHom, ?_⟩
  intro u v huv
  change hom (jThetaVertex copy u) =
    hom (jThetaVertex copy v) at huv
  apply (jThetaCopy copy).injective
  exact hcopies copy (jThetaVertex_mem copy u)
    (jThetaVertex_mem copy v) huv

theorem symplecticQuadrangle_no_point_jTemplate
    (hom : jTemplate →g symplecticQuadrangle K)
    (hbase_inj : Function.Injective
      (fun base : Fin 4 => hom (.inl (.inl base))))
    (hcopies : ∀ copy : Fin 2,
      Set.InjOn hom {v | InJCopy copy v})
    (p : Fin 4 → SymplecticPoint K)
    (c : Fin 2 → Fin 2 → SymplecticPoint K)
    (hbase : ∀ base : Fin 4,
      hom (.inl (.inl base)) = .inl (p base))
    (hcenter : ∀ (copy center : Fin 2),
      hom (.inl (.inr (copy, center))) =
        .inl (c copy center)) : False := by
  let θ (copy : Fin 2) := jThetaHomCopy hom hcopies copy
  have hθbase (copy : Fin 2) (base : Fin 3) :
      θ copy (.inl (.inl base)) =
        .inl (p (jBase copy base)) := by
    change hom (jThetaVertex copy (.inl (.inl base))) = _
    simpa [jThetaVertex] using hbase (jBase copy base)
  have hθcenter (copy center : Fin 2) :
      θ copy (.inl (.inr center)) =
        .inl (c copy center) := by
    change hom (jThetaVertex copy (.inl (.inr center))) = _
    simpa [jThetaVertex] using hcenter copy center
  have hcenters_inj (copy : Fin 2) :
      Function.Injective (c copy) := by
    intro i j hij
    have himage :
        θ copy (.inl (.inr i)) =
          θ copy (.inl (.inr j)) := by
      rw [hθcenter copy i, hθcenter copy j, hij]
    have hsource :
        (Sum.inl (Sum.inr i) : SubdivisionVertex 2) =
          .inl (.inr j) := (θ copy).injective himage
    exact Sum.inr.inj (Sum.inl.inj hsource)
  have hpoints_inj : Function.Injective p := by
    intro i j hij
    apply hbase_inj
    change hom (.inl (.inl i)) = hom (.inl (.inl j))
    rw [hbase i, hbase j, hij]
  have hyz : p 2 ≠ p 3 := by
    intro h
    exact (by decide : (2 : Fin 4) ≠ 3) (hpoints_inj h)
  have hxx' : p 0 ≠ p 1 := by
    intro h
    exact (by decide : (0 : Fin 4) ≠ 1) (hpoints_inj h)
  have hyz_unrelated :
      ¬ SymplecticPointRelated K (p 2) (p 3) := by
    have h := subdivisionPoint_bases_unrelated K (θ 0)
      (fun base => p (jBase 0 base)) (c 0)
      (hθbase 0) (hθcenter 0)
      (by decide : (1 : Fin 3) ≠ 2) 0
    simpa [jBase] using h
  have hrelated (copy : Fin 2) (base : Fin 3)
      (center : Fin 2) :
      SymplecticPointRelated K
        (c copy center) (p (jBase copy base)) :=
    symplecticPointRelated_symm K
      (subdivisionPoint_base_center_related K
        (θ copy) (hθbase copy base) (hθcenter copy center))
  have hcd : c 0 0 ≠ c 0 1 := by
    intro h
    exact (by decide : (0 : Fin 2) ≠ 1)
      (hcenters_inj 0 h)
  have hc'd' : c 1 0 ≠ c 1 1 := by
    intro h
    exact (by decide : (0 : Fin 2) ≠ 1)
      (hcenters_inj 1 h)
  have havoid := symplecticPoint_point_class_avoidance K
    (x := p 0) (x' := p 1) (y := p 2) (z := p 3)
    (c := c 0 0) (d := c 0 1)
    (c' := c 1 0) (d' := c 1 1)
    hyz hyz_unrelated hxx' hcd hc'd'
    (by simpa [jBase] using hrelated 0 0 0)
    (by simpa [jBase] using hrelated 0 1 0)
    (by simpa [jBase] using hrelated 0 2 0)
    (by simpa [jBase] using hrelated 0 0 1)
    (by simpa [jBase] using hrelated 0 1 1)
    (by simpa [jBase] using hrelated 0 2 1)
    (by simpa [jBase] using hrelated 1 0 0)
    (by simpa [jBase] using hrelated 1 1 0)
    (by simpa [jBase] using hrelated 1 2 0)
    (by simpa [jBase] using hrelated 1 0 1)
    (by simpa [jBase] using hrelated 1 1 1)
    (by simpa [jBase] using hrelated 1 2 1)
  have hjoin0 : jTemplate.Adj
      (.inl (.inl (0 : Fin 4)))
      (.inr (.inr ())) := by
    simp [jTemplate, SimpleGraph.fromRel_adj, jTemplateRelation]
  have hjoin1 : jTemplate.Adj
      (.inl (.inl (1 : Fin 4)))
      (.inr (.inr ())) := by
    simp [jTemplate, SimpleGraph.fromRel_adj, jTemplateRelation]
  have hleft := hom.map_rel hjoin0
  have hright := hom.map_rel hjoin1
  change (symplecticQuadrangle K).Adj
    (hom (.inl (.inl (0 : Fin 4))))
    (hom (.inr (.inr ()))) at hleft
  change (symplecticQuadrangle K).Adj
    (hom (.inl (.inl (1 : Fin 4))))
    (hom (.inr (.inr ()))) at hright
  rw [hbase 0] at hleft
  rw [hbase 1] at hright
  exact havoid
    (symplecticPointRelated_of_quadrangle_common_neighbor K
      hxx' hleft hright)

theorem symplecticQuadrangle_no_point_jTemplate_of_bases
    (hom : jTemplate →g symplecticQuadrangle K)
    (hbase_inj : Function.Injective
      (fun base : Fin 4 => hom (.inl (.inl base))))
    (hcopies : ∀ copy : Fin 2,
      Set.InjOn hom {v | InJCopy copy v})
    (hpoint : ∀ base : Fin 4,
      ∃ p : SymplecticPoint K,
        hom (.inl (.inl base)) = .inl p) : False := by
  classical
  let p : Fin 4 → SymplecticPoint K :=
    fun base => Classical.choose (hpoint base)
  have hp (base : Fin 4) :
      hom (.inl (.inl base)) = .inl (p base) :=
    Classical.choose_spec (hpoint base)
  let θ (copy : Fin 2) := jThetaHomCopy hom hcopies copy
  have hθbase (copy : Fin 2) :
      θ copy (.inl (.inl (0 : Fin 3))) =
        .inl (p (jBase copy 0)) := by
    change hom (jThetaVertex copy (.inl (.inl 0))) = _
    simpa [jThetaVertex] using hp (jBase copy 0)
  have hcenter_exists (copy center : Fin 2) :
      ∃ q : SymplecticPoint K,
        hom (.inl (.inr (copy, center))) = .inl q := by
    have h := subdivisionPoint_center_of_point_base K
      (θ copy) (center := center) (hθbase copy)
    change ∃ q : SymplecticPoint K,
      hom (jThetaVertex copy (.inl (.inr center))) = .inl q at h
    simpa [jThetaVertex] using h
  let c : Fin 2 → Fin 2 → SymplecticPoint K :=
    fun copy center => Classical.choose (hcenter_exists copy center)
  have hc (copy center : Fin 2) :
      hom (.inl (.inr (copy, center))) =
        .inl (c copy center) :=
    Classical.choose_spec (hcenter_exists copy center)
  exact symplecticQuadrangle_no_point_jTemplate K hom
    hbase_inj hcopies p c hp hc

theorem symplecticQuadrangle_no_point_jTemplate_of_first_base
    (hom : jTemplate →g symplecticQuadrangle K)
    (hbase_inj : Function.Injective
      (fun base : Fin 4 => hom (.inl (.inl base))))
    (hcopies : ∀ copy : Fin 2,
      Set.InjOn hom {v | InJCopy copy v})
    (hfirst : ∃ p : SymplecticPoint K,
      hom (.inl (.inl (0 : Fin 4))) = .inl p) : False := by
  obtain ⟨p₀, hp₀⟩ := hfirst
  let θ (copy : Fin 2) := jThetaHomCopy hom hcopies copy
  have hx : θ 0 (.inl (.inl (0 : Fin 3))) = .inl p₀ := by
    change hom (jThetaVertex 0 (.inl (.inl 0))) = _
    simpa [jThetaVertex, jBase] using hp₀
  have hy : ∃ p : SymplecticPoint K,
      hom (.inl (.inl (2 : Fin 4))) = .inl p := by
    have h := subdivisionPoint_base_of_point_base K (θ 0)
      (otherBase := (1 : Fin 3)) 0 hx
    change ∃ p : SymplecticPoint K,
      hom (jThetaVertex 0 (.inl (.inl (1 : Fin 3)))) = .inl p at h
    simpa [jThetaVertex, jBase] using h
  have hz : ∃ p : SymplecticPoint K,
      hom (.inl (.inl (3 : Fin 4))) = .inl p := by
    have h := subdivisionPoint_base_of_point_base K (θ 0)
      (otherBase := (2 : Fin 3)) 0 hx
    change ∃ p : SymplecticPoint K,
      hom (jThetaVertex 0 (.inl (.inl (2 : Fin 3)))) = .inl p at h
    simpa [jThetaVertex, jBase] using h
  obtain ⟨py, hpy⟩ := hy
  have hy' : θ 1 (.inl (.inl (1 : Fin 3))) = .inl py := by
    change hom (jThetaVertex 1 (.inl (.inl 1))) = _
    simpa [jThetaVertex, jBase] using hpy
  have hx' : ∃ p : SymplecticPoint K,
      hom (.inl (.inl (1 : Fin 4))) = .inl p := by
    have h := subdivisionPoint_base_of_point_base K (θ 1)
      (otherBase := (0 : Fin 3)) 0 hy'
    change ∃ p : SymplecticPoint K,
      hom (jThetaVertex 1 (.inl (.inl (0 : Fin 3)))) = .inl p at h
    simpa [jThetaVertex, jBase] using h
  apply symplecticQuadrangle_no_point_jTemplate_of_bases K
    hom hbase_inj hcopies
  intro base
  fin_cases base
  · exact ⟨p₀, hp₀⟩
  · exact hx'
  · exact ⟨py, hpy⟩
  · exact hz

theorem symplecticQuadrangle_jTemplate_first_base_is_line
    (hom : jTemplate →g symplecticQuadrangle K)
    (hbase_inj : Function.Injective
      (fun base : Fin 4 => hom (.inl (.inl base))))
    (hcopies : ∀ copy : Fin 2,
      Set.InjOn hom {v | InJCopy copy v}) :
    ∃ L : SymplecticLine K,
      hom (.inl (.inl (0 : Fin 4))) = .inr L := by
  cases h : hom (.inl (.inl (0 : Fin 4))) with
  | inl p =>
      exact False.elim
        (symplecticQuadrangle_no_point_jTemplate_of_first_base K
          hom hbase_inj hcopies ⟨p, h⟩)
  | inr L => exact ⟨L, rfl⟩

def kGammaHomCopy
    {V : Type*} {host : SimpleGraph V}
    (hom : kTemplate →g host)
    (hcopies : ∀ copy : Fin 2,
      Set.InjOn hom {v : KVertex | v.1 = copy})
    (copy : Fin 2) :
    SimpleGraph.Copy gammaGraph host := by
  refine ⟨hom.comp (kGammaCopy copy).toHom, ?_⟩
  intro u v huv
  change hom (kGammaVertex copy u) =
    hom (kGammaVertex copy v) at huv
  apply (kGammaCopy copy).injective
  exact hcopies copy (show (kGammaVertex copy u).1 = copy from rfl)
    (show (kGammaVertex copy v).1 = copy from rfl) huv

theorem symplecticQuadrangle_kTemplate_has_line_gamma
    (hom : kTemplate →g symplecticQuadrangle K)
    (hcopies : ∀ copy : Fin 2,
      Set.InjOn hom {v : KVertex | v.1 = copy}) :
    ∃ (i : Fin 2) (L : SymplecticLine K),
      (kGammaHomCopy hom hcopies i) kSpecifiedCenter = .inr L := by
  have hjoin : kTemplate.Adj
      ((0 : Fin 2), kSpecifiedCenter)
      ((1 : Fin 2), kSpecifiedCenter) := by
    simp [kTemplate, SimpleGraph.fromRel_adj,
      kTemplateRelation, kSpecifiedCenter]
  have hadj := hom.map_rel hjoin
  change (symplecticQuadrangle K).Adj
    (hom ((0 : Fin 2), kSpecifiedCenter))
    (hom ((1 : Fin 2), kSpecifiedCenter)) at hadj
  cases hzero : hom ((0 : Fin 2), kSpecifiedCenter) with
  | inl p =>
      rw [hzero] at hadj
      obtain ⟨L, hL, _⟩ :=
        symplecticQuadrangle_adjacent_to_point K hadj
      refine ⟨1, L, ?_⟩
      change hom (kGammaVertex 1 kSpecifiedCenter) = .inr L
      simpa [kGammaVertex] using hL
  | inr L =>
      refine ⟨0, L, ?_⟩
      change hom (kGammaVertex 0 kSpecifiedCenter) = .inr L
      simpa [kGammaVertex] using hzero

end PointClass

end CharacteristicAvoidance

end Erdos180
