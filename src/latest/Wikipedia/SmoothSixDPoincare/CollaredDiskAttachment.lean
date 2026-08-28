import Wikipedia.SmoothSixDPoincare.RadialExtension
import Wikipedia.SmoothSixDPoincare.MorseHandleModel
import Mathlib.Topology.Homeomorph.Quotient

/-!
# The topological model for complementary handle cancellation

Attach `D(E) × D(F)` to `S(E) × I × D(F)` along `S(E) × {0} × D(F)`.
The result is another `D(E) × D(F)`. The old collar occupies radii from
one half to one, and the new handle occupies radii at most one half.
The identification retains every transverse disk coordinate.

This is the explicit product model in the topological part of Wall,
Differential Topology, Lemma 5.4.2. Identifying a general single-intersection
handle pair with this model is a separate geometric obligation.
-/

noncomputable section

open Set Metric Function Topology
open scoped unitInterval

namespace Wikipedia.SmoothSixDPoincare.CollaredDiskAttachment

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F]

abbrev Disk (E : Type*) [NormedAddCommGroup E] := closedBall (0 : E) 1
abbrev Sphere (E : Type*) [NormedAddCommGroup E] := sphere (0 : E) 1
abbrev OldPiece (E F : Type*) [NormedAddCommGroup E] [NormedAddCommGroup F] :=
  Sphere E × (I × Disk F)
abbrev Handle (E F : Type*) [NormedAddCommGroup E] [NormedAddCommGroup F] := Disk E × Disk F

def collarRadius (t : I) : ℝ := (1 + t.val) / 2

theorem collarRadius_zero : collarRadius 0 = 1 / 2 := by norm_num [collarRadius]

theorem collarRadius_one : collarRadius 1 = 1 := by norm_num [collarRadius]

theorem collarRadius_pos (t : I) : 0 < collarRadius t := by
  dsimp [collarRadius]
  linarith [t.property.1]

theorem collarRadius_le_one (t : I) : collarRadius t ≤ 1 := by
  dsimp [collarRadius]
  linarith [t.property.2]

def collarPoint (u : Sphere E) (t : I) : Disk E :=
  ⟨collarRadius t • (u : E), mem_closedBall_zero_iff.mpr (by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (collarRadius_pos t),
      mem_sphere_zero_iff_norm.mp u.property, mul_one]
    exact collarRadius_le_one t)⟩

theorem norm_collarPoint (u : Sphere E) (t : I) : ‖(collarPoint u t : E)‖ = collarRadius t := by
  change ‖collarRadius t • (u : E)‖ = _
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (collarRadius_pos t),
    mem_sphere_zero_iff_norm.mp u.property, mul_one]

def halfPoint (u : Disk E) : Disk E :=
  ⟨(1 / 2 : ℝ) • (u : E), mem_closedBall_zero_iff.mpr (by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have hu := mem_closedBall_zero_iff.mp u.property
    linarith)⟩

theorem norm_halfPoint (u : Disk E) : ‖(halfPoint u : E)‖ = (1 / 2 : ℝ) * ‖(u : E)‖ := by
  change ‖(1 / 2 : ℝ) • (u : E)‖ = _
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]

def oldMap (a : OldPiece E F) : Handle E F := (collarPoint a.1 a.2.1, a.2.2)

def newMap (z : Handle E F) : Handle E F := (halfPoint z.1, z.2)

theorem continuous_oldMap : Continuous (oldMap (E := E) (F := F)) := by
  have ht : Continuous (fun a : OldPiece E F => collarRadius a.2.1) :=
    (continuous_const.add
      (continuous_subtype_val.comp (continuous_fst.comp continuous_snd))).div_const 2
  exact ((ht.smul (continuous_subtype_val.comp continuous_fst)).subtype_mk _).prodMk
    (continuous_snd.comp continuous_snd)

theorem continuous_newMap : Continuous (newMap (E := E) (F := F)) :=
  ((continuous_const.smul (continuous_subtype_val.comp continuous_fst)).subtype_mk _).prodMk
    continuous_snd

theorem oldMap_injective : Injective (oldMap (E := E) (F := F)) := by
  rintro ⟨u, t, v⟩ ⟨u', t', v'⟩ heq
  have hv : v = v' := congrArg Prod.snd heq
  have hn := congrArg (fun z : Handle E F => ‖(z.1 : E)‖) heq
  change ‖(collarPoint u t : E)‖ = ‖(collarPoint u' t' : E)‖ at hn
  rw [norm_collarPoint, norm_collarPoint] at hn
  have htt : t = t' := Subtype.ext (by dsimp [collarRadius] at hn; linarith)
  subst t'
  have hu : (u : E) = (u' : E) := by
    have hh := congrArg (fun z : Handle E F => (collarRadius t)⁻¹ • (z.1 : E)) heq
    simpa only [oldMap, collarPoint, inv_smul_smul₀ (collarRadius_pos t).ne'] using hh
  exact Prod.ext (Subtype.ext hu) (Prod.ext rfl hv)

theorem newMap_injective : Injective (newMap (E := E) (F := F)) := by
  intro z w heq
  have hfirst := congrArg (fun p : Handle E F => (2 : ℝ) • (p.1 : E)) heq
  have hx : (z.1 : E) = (w.1 : E) := by
    simpa only [newMap, halfPoint, smul_smul, show (2 : ℝ) * (1 / 2) = 1 by norm_num,
      one_smul] using hfirst
  have hv : (newMap z).2 = (newMap w).2 := congrArg Prod.snd heq
  exact Prod.ext (Subtype.ext hx) hv

/-- The generating identifications are precisely the whole zero-end sphere-times-disk face. -/
def Rel : OldPiece E F ⊕ Handle E F → OldPiece E F ⊕ Handle E F → Prop
  | .inl a, .inr z => a.2.1 = 0 ∧ (z.1 : E) = (a.1 : E) ∧ z.2 = a.2.2
  | _, _ => False

abbrev Space (E F : Type*) [NormedAddCommGroup E] [NormedAddCommGroup F] :=
  Quot (Rel (E := E) (F := F))

theorem oldMap_eq_newMap_iff (a : OldPiece E F) (z : Handle E F) :
    oldMap a = newMap z ↔ Rel (.inl a) (.inr z) := by
  constructor
  · intro heq
    have hn := congrArg (fun p : Handle E F => ‖(p.1 : E)‖) heq
    change ‖(collarPoint a.1 a.2.1 : E)‖ = ‖(halfPoint z.1 : E)‖ at hn
    rw [norm_collarPoint, norm_halfPoint] at hn
    have ht : a.2.1 = 0 := Subtype.ext (by
      change (a.2.1 : ℝ) = 0
      dsimp [collarRadius] at hn
      linarith [a.2.1.property.1, mem_closedBall_zero_iff.mp z.1.property])
    have hx := congrArg (fun p : Handle E F => (2 : ℝ) • (p.1 : E)) heq
    have hu : (z.1 : E) = (a.1 : E) := by
      simpa only [oldMap, newMap, collarPoint, halfPoint, ht, collarRadius_zero, smul_smul,
        show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_smul] using hx.symm
    exact ⟨ht, hu, (congrArg Prod.snd heq).symm⟩
  · rintro ⟨ht, hu, hv⟩
    apply Prod.ext
    · apply Subtype.ext
      change collarRadius a.2.1 • (a.1 : E) = (1 / 2 : ℝ) • (z.1 : E)
      rw [ht, hu, collarRadius_zero]
    · exact hv.symm

def sumMap : OldPiece E F ⊕ Handle E F → Handle E F := Sum.elim oldMap newMap

theorem continuous_sumMap : Continuous (sumMap (E := E) (F := F)) :=
  continuous_sum_dom.mpr ⟨continuous_oldMap, continuous_newMap⟩

theorem sumMap_respects (a b : OldPiece E F ⊕ Handle E F) (hab : Rel a b) :
    sumMap a = sumMap b := by
  cases a with
  | inl a =>
    cases b with
    | inl b => exact hab.elim
    | inr z => exact (oldMap_eq_newMap_iff a z).mpr hab
  | inr z => cases b <;> exact hab.elim

def quotientMap : Space E F → Handle E F := Quot.lift sumMap sumMap_respects

theorem continuous_quotientMap : Continuous (quotientMap (E := E) (F := F)) :=
  continuous_quot_lift sumMap_respects continuous_sumMap

theorem quotientMap_injective : Injective (quotientMap (E := E) (F := F)) := by
  intro a b
  induction a using Quot.inductionOn with
  | _ a =>
    induction b using Quot.inductionOn with
    | _ b =>
      intro heq
      cases a with
      | inl a =>
        cases b with
        | inl b => exact congrArg (fun z => Quot.mk _ (Sum.inl z)) (oldMap_injective heq)
        | inr z => exact Quot.sound ((oldMap_eq_newMap_iff a z).mp heq)
      | inr z =>
        cases b with
        | inl a => exact (Quot.sound ((oldMap_eq_newMap_iff a z).mp heq.symm)).symm
        | inr w => exact congrArg (fun x => Quot.mk _ (Sum.inr x)) (newMap_injective heq)

theorem quotientMap_surjective : Surjective (quotientMap (E := E) (F := F)) := by
  rintro ⟨x, v⟩
  by_cases hx : ‖(x : E)‖ ≤ (1 / 2 : ℝ)
  · let u : Disk E := ⟨(2 : ℝ) • (x : E), mem_closedBall_zero_iff.mpr (by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith)⟩
    refine ⟨Quot.mk _ (Sum.inr (u, v)), Prod.ext (Subtype.ext ?_) rfl⟩
    change (1 / 2 : ℝ) • ((2 : ℝ) • (x : E)) = (x : E)
    rw [smul_smul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul]
  · have hxpos : 0 < ‖(x : E)‖ := by linarith
    let u : Sphere E := RadialExtension.direction (x : E) (norm_pos_iff.mp hxpos)
    let t : I := ⟨2 * ‖(x : E)‖ - 1, by
      constructor <;> linarith [mem_closedBall_zero_iff.mp x.property]⟩
    have hr : collarRadius t = ‖(x : E)‖ := by dsimp [collarRadius, t]; ring
    refine ⟨Quot.mk _ (Sum.inl (u, t, v)), Prod.ext (Subtype.ext ?_) rfl⟩
    change collarRadius t • (‖(x : E)‖⁻¹ • (x : E)) = (x : E)
    rw [hr, smul_inv_smul₀ hxpos.ne']

variable [NormedSpace ℝ F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- The entire model attachment is one product disk, with no extra identifications. -/
def homeomorph : Space E F ≃ₜ Handle E F :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective quotientMap ⟨quotientMap_injective, quotientMap_surjective⟩)
    continuous_quotientMap

theorem homeomorph_inl (a : OldPiece E F) : homeomorph (Quot.mk _ (Sum.inl a)) = oldMap a := rfl

theorem homeomorph_inr (z : Handle E F) : homeomorph (Quot.mk _ (Sum.inr z)) = newMap z := rfl

/-- The outer sphere-times-disk face is fixed pointwise in the original coordinates. -/
theorem homeomorph_outer_face (u : Sphere E) (v : Disk F) :
    homeomorph (Quot.mk _ (Sum.inl (u, (1 : I), v))) =
      (⟨u, sphere_subset_closedBall u.property⟩, v) := by
  rw [homeomorph_inl]
  apply Prod.ext
  · apply Subtype.ext
    change collarRadius 1 • (u : E) = (u : E)
    rw [collarRadius_one, one_smul]
  · rfl

end Wikipedia.SmoothSixDPoincare.CollaredDiskAttachment
