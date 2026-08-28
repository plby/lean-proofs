import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Sheaves.LocalPredicate

/-!
# The sheaf of actual local analytic square roots

On an open subset `S` of the complex plane, a section over an open `V ⊆ S`
is a function whose zero extension is analytic at every point of `V` and whose
square is the specified ambient function there.  Extension is only a way to
state ambient analyticity: restriction and locality are proved by agreement
on actual open neighborhoods.

No nonvanishing assumption is made on the specified function.  In particular,
the definition does not identify different analytic germs which have the same
value at a zero.
-/

noncomputable section

open CategoryTheory Function Filter Opposite Set TopologicalSpace
open scoped Topology

namespace Wikipedia.HopfProblem.AnalyticRootCover

/-- The actual inclusion of an open subset of `S` into the complex plane. -/
def ambientVal (S : Opens ℂ) (V : Opens S) (x : V) : ℂ := ((x : S) : ℂ)

theorem ambientVal_injective (S : Opens ℂ) (V : Opens S) :
    Injective (ambientVal S V) := Subtype.val_injective.comp Subtype.val_injective

/-- The ambient complex open set corresponding to an open subset of `S`. -/
def ambientOpen (S : Opens ℂ) (V : Opens S) : Opens ℂ :=
  ⟨Subtype.val '' (V : Set S), S.isOpen.isOpenMap_subtype_val _ V.isOpen⟩

theorem ambientVal_mem (S : Opens ℂ) (V : Opens S) (x : V) :
    ambientVal S V x ∈ ambientOpen S V := ⟨(x : S), x.2, rfl⟩

theorem mem_ambientOpen (S : Opens ℂ) (V : Opens S) {z : ℂ} :
    z ∈ ambientOpen S V ↔ ∃ x : V, ambientVal S V x = z := by
  constructor
  · rintro ⟨x, hx, hxz⟩
    exact ⟨⟨x, hx⟩, hxz⟩
  · rintro ⟨x, rfl⟩
    exact ambientVal_mem S V x

@[simp] theorem coe_mem_ambientOpen (S : Opens ℂ) (V : Opens S) (x : S) :
    (x : ℂ) ∈ ambientOpen S V ↔ x ∈ V := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    have he : y = x := Subtype.ext hyx
    subst y
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem ambientOpen_subset (S : Opens ℂ) (V : Opens S) :
    (ambientOpen S V : Set ℂ) ⊆ S := by
  rintro z ⟨x, _, rfl⟩
  exact x.2

theorem ambientOpen_mono (S : Opens ℂ) {U V : Opens S} (i : U ⟶ V) :
    ambientOpen S U ≤ ambientOpen S V := by
  rintro z ⟨x, hx, rfl⟩
  exact ⟨x, i.le hx, rfl⟩

/-- Extend a local function by zero outside its actual domain. -/
def extendSection (S : Opens ℂ) (V : Opens S) (s : V → ℂ) : ℂ → ℂ :=
  Function.extend (ambientVal S V) s 0

@[simp] theorem extendSection_apply (S : Opens ℂ) (V : Opens S)
    (s : V → ℂ) (x : V) :
    extendSection S V s (ambientVal S V x) = s x :=
  (ambientVal_injective S V).extend_apply s 0 x

theorem extendSection_injective (S : Opens ℂ) (V : Opens S) :
    Injective (extendSection S V) := by
  intro s t he
  funext x
  simpa only [extendSection_apply] using congr_fun he (ambientVal S V x)

/-- Extension agrees with any ambient representative on its actual open domain. -/
theorem extendSection_agrees (S : Opens ℂ) (V : Opens S) (s : V → ℂ)
    (f : ℂ → ℂ) (hf : ∀ x, s x = f (ambientVal S V x)) :
    EqOn (extendSection S V s) f (ambientOpen S V) := by
  intro z hz
  obtain ⟨x, rfl⟩ := (mem_ambientOpen S V).mp hz
  rw [extendSection_apply]
  exact hf x

/-- Restriction of an ambient function, followed by extension, agrees with
the original function on the corresponding ambient open set. -/
theorem extension_agreement (S : Opens ℂ) (V : Opens S) (f : ℂ → ℂ) :
    EqOn (extendSection S V (fun x => f (ambientVal S V x))) f (ambientOpen S V) :=
  extendSection_agrees S V _ f (fun _ => rfl)

theorem extendSection_restrict_agrees (S : Opens ℂ) {U V : Opens S}
    (i : U ⟶ V) (s : V → ℂ) :
    EqOn (extendSection S U (fun x => s (Set.inclusion i.le x))) (extendSection S V s)
      (ambientOpen S U) := by
  intro z hz
  obtain ⟨x, rfl⟩ := (mem_ambientOpen S U).mp hz
  rw [extendSection_apply]
  exact (extendSection_apply S V s (Set.inclusion i.le x)).symm

theorem extendSection_restrict_eventuallyEq (S : Opens ℂ) {U V : Opens S}
    (i : U ⟶ V) (s : V → ℂ) (x : U) :
    extendSection S U (fun y => s (Set.inclusion i.le y)) =ᶠ[𝓝 (ambientVal S U x)]
      extendSection S V s := by
  filter_upwards [(ambientOpen S U).isOpen.mem_nhds (ambientVal_mem S U x)] with z hz
  exact extendSection_restrict_agrees S i s hz

/-- The predicate of being an actual analytic square root on an open set. -/
def IsRootSection (S : Opens ℂ) (F : ℂ → ℂ) {V : Opens S} (s : V → ℂ) : Prop :=
  ∀ x : V, AnalyticAt ℂ (extendSection S V s) (ambientVal S V x) ∧
    s x ^ 2 = F (ambientVal S V x)

/-- Analytic-root sections form a local predicate: restriction preserves it,
and validity on a neighborhood of each point implies validity everywhere. -/
def rootLocalPredicate (S : Opens ℂ) (F : ℂ → ℂ) :
    TopCat.LocalPredicate (fun _ : TopCat.of S => ℂ) where
  pred {_} s := IsRootSection S F s
  res {_ _} i s hs := by
    intro x
    refine ⟨?_, (hs (Set.inclusion i.le x)).2⟩
    exact (hs (Set.inclusion i.le x)).1.congr
      (extendSection_restrict_eventuallyEq S i s x).symm
  locality {U} s hs := by
    intro x
    obtain ⟨V, hxV, i, hV⟩ := hs x
    let y : V := ⟨(x : S), hxV⟩
    have hix : Set.inclusion i.le y = x := Subtype.ext rfl
    refine ⟨?_, ?_⟩
    · exact (hV y).1.congr (extendSection_restrict_eventuallyEq S i s y)
    · have hsq : s (Set.inclusion i.le y) ^ 2 = F (ambientVal S U x) := (hV y).2
      rwa [hix] at hsq

/-- The type-valued presheaf of actual analytic square roots. -/
def rootPresheaf (S : Opens ℂ) (F : ℂ → ℂ) :
    (TopCat.of S).Presheaf (Type 0) :=
  TopCat.subpresheafToTypes (rootLocalPredicate S F).toPrelocalPredicate

theorem rootPresheaf_isSheaf (S : Opens ℂ) (F : ℂ → ℂ) :
    (rootPresheaf S F).IsSheaf :=
  TopCat.subpresheafToTypes.isSheaf (rootLocalPredicate S F)

/-- A section is the actual function together with its analytic-root property. -/
abbrev RootSection (S : Opens ℂ) (F : ℂ → ℂ) (V : Opens S) :=
  (rootPresheaf S F).obj (op V)

theorem rootSection_analytic (S : Opens ℂ) (F : ℂ → ℂ) {V : Opens S}
    (s : RootSection S F V) (x : V) :
    AnalyticAt ℂ (extendSection S V s.1) (ambientVal S V x) := (s.2 x).1

theorem rootSection_sq (S : Opens ℂ) (F : ℂ → ℂ) {V : Opens S}
    (s : RootSection S F V) (x : V) :
    s.1 x ^ 2 = F (ambientVal S V x) := (s.2 x).2

@[simp] theorem rootPresheaf_map_apply (S : Opens ℂ) (F : ℂ → ℂ)
    {U V : Opens S} (i : U ⟶ V) (s : RootSection S F V) (x : U) :
    ((rootPresheaf S F).map i.op s).1 x = s.1 (Set.inclusion i.le x) := rfl

theorem rootSection_ext (S : Opens ℂ) (F : ℂ → ℂ) {V : Opens S}
    {s t : RootSection S F V}
    (he : extendSection S V s.1 = extendSection S V t.1) : s = t :=
  Subtype.ext ((extendSection_injective S V) he)

namespace RootSection

variable {S : Opens ℂ} {F : ℂ → ℂ} {V : Opens S}

/-- A root section gives a genuine ambient analytic function on its ambient
open domain. -/
theorem analyticOnNhd_extend (s : RootSection S F V) :
    AnalyticOnNhd ℂ (extendSection S V s.1) (ambientOpen S V) := by
  intro z hz
  obtain ⟨x, rfl⟩ := (mem_ambientOpen S V).mp hz
  exact rootSection_analytic S F s x

/-- The extended section satisfies the square-root equation on its whole
ambient open domain. -/
theorem square_eq (s : RootSection S F V) {z : ℂ} (hz : z ∈ ambientOpen S V) :
    extendSection S V s.1 z ^ 2 = F z := by
  obtain ⟨x, rfl⟩ := (mem_ambientOpen S V).mp hz
  rw [extendSection_apply]
  exact rootSection_sq S F s x

@[ext] theorem ext {s t : RootSection S F V} (he : ∀ x, s.1 x = t.1 x) : s = t :=
  Subtype.ext (funext he)

end RootSection

/-- Package an ambient analytic square root into the actual root presheaf. -/
def rootSectionOfAnalytic (S : Opens ℂ) (F : ℂ → ℂ) {V : Opens S}
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (ambientOpen S V))
    (hsq : ∀ x : V, f (ambientVal S V x) ^ 2 = F (ambientVal S V x)) :
    RootSection S F V := by
  refine ⟨fun x => f (ambientVal S V x), fun x => ⟨?_, hsq x⟩⟩
  apply (hf _ (ambientVal_mem S V x)).congr
  filter_upwards [(ambientOpen S V).isOpen.mem_nhds (ambientVal_mem S V x)] with z hz
  exact (extension_agreement S V f hz).symm

@[simp] theorem rootSectionOfAnalytic_apply (S : Opens ℂ) (F : ℂ → ℂ) {V : Opens S}
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (ambientOpen S V))
    (hsq : ∀ x : V, f (ambientVal S V x) ^ 2 = F (ambientVal S V x)) (x : V) :
    (rootSectionOfAnalytic S F f hf hsq).1 x = f (ambientVal S V x) := rfl

theorem extend_rootSectionOfAnalytic_eqOn (S : Opens ℂ) (F : ℂ → ℂ) {V : Opens S}
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (ambientOpen S V))
    (hsq : ∀ x : V, f (ambientVal S V x) ^ 2 = F (ambientVal S V x)) :
    EqOn (extendSection S V (rootSectionOfAnalytic S F f hf hsq).1) f
      (ambientOpen S V) := extension_agreement S V f

end Wikipedia.HopfProblem.AnalyticRootCover
