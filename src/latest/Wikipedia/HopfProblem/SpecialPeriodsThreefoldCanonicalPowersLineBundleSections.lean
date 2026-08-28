import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPowersLineBundleBasic

/-!
# Powers of sections of the original holomorphic line bundles

The fibrewise polynomial `v ↦ v ^ n` maps the original cocycle bundle to
the bundle with powered transition functions.  Its expression in every
pair of original bundle charts is exactly the same polynomial, so this
is a holomorphic map of the native total spaces.  In particular it sends
actual holomorphic sections to actual holomorphic sections.  No change
of topology or atlas is used, and the map is not asserted to be linear.
-/

noncomputable section

open Bundle Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.CanonicalGlobalLineBundle.Powers

open HolomorphicCharacterBundle

variable {M ι : Type*} [TopologicalSpace M] (A : TransitionData M ι)

/-- The actual section power in the native bundle with power cocycle. -/
def sectionPower (n : ℕ) (s : ∀ x, A.core.Fiber x) (x : M) :
    (A.power n).core.Fiber x :=
  (id (α := ℂ) (s x)) ^ n

/-- The polynomial power map between the original native total spaces. -/
def powerMap (n : ℕ) (p : A.core.TotalSpace) : (A.power n).core.TotalSpace :=
  ⟨p.proj, (id (α := ℂ) p.2) ^ n⟩

@[simp] theorem sectionPower_apply (n : ℕ) (s : ∀ x, A.core.Fiber x) (x : M) :
    sectionPower A n s x = (id (α := ℂ) (s x)) ^ n := rfl

@[simp] theorem powerMap_proj (n : ℕ) (p : A.core.TotalSpace) :
    (powerMap A n p).proj = p.proj := rfl

@[simp] theorem powerMap_mk (n : ℕ) (x : M) (v : A.core.Fiber x) :
    powerMap A n ⟨x, v⟩ = ⟨x, (id (α := ℂ) v) ^ n⟩ := rfl

theorem powerMap_section (n : ℕ) (s : ∀ x, A.core.Fiber x) (x : M) :
    powerMap A n ⟨x, s x⟩ = ⟨x, sectionPower A n s x⟩ := rfl

/-- In every original chart, the new coefficient is the power of the
old coefficient.  The formula is valid for all total-space points. -/
theorem powerMap_localTriv (n : ℕ) (i : ι) (p : A.core.TotalSpace) :
    (A.power n).core.localTriv i (powerMap A n p) =
      (p.proj, ((A.core.localTriv i p).2) ^ n) := by
  apply Prod.ext
  · rfl
  · exact (mul_pow (A.transition (A.indexAt p.proj) i p.proj : ℂ)
      (id (α := ℂ) p.2) n).symm

theorem sectionPower_localCoefficient (n : ℕ) (s : ∀ x, A.core.Fiber x)
    (i : ι) (x : M) :
    (A.power n).localCoefficient (sectionPower A n s) i x =
      (A.localCoefficient s i x) ^ n :=
  congrArg Prod.snd (powerMap_localTriv A n i ⟨x, s x⟩)

@[simp] theorem sectionPower_zero (s : ∀ x, A.core.Fiber x) (x : M) :
    sectionPower A 0 s x = (1 : ℂ) := by
  change (id (α := ℂ) (s x)) ^ 0 = (1 : ℂ)
  exact pow_zero _

@[simp] theorem sectionPower_one (s : ∀ x, A.core.Fiber x) (x : M) :
    sectionPower A 1 s x = s x := by
  change (id (α := ℂ) (s x)) ^ 1 = id (α := ℂ) (s x)
  exact pow_one _

theorem sectionPower_comp (m n : ℕ) (s : ∀ x, A.core.Fiber x) (x : M) :
    sectionPower (A.power m) n (sectionPower A m s) x =
      sectionPower A (m * n) s x := by
  change ((id (α := ℂ) (s x)) ^ m) ^ n = (id (α := ℂ) (s x)) ^ (m * n)
  exact (pow_mul _ m n).symm

@[simp] theorem powerMap_zero (p : A.core.TotalSpace) :
    powerMap A 0 p = ⟨p.proj, (1 : ℂ)⟩ := by
  cases p
  simp only [powerMap, pow_zero]

@[simp] theorem powerMap_one (p : A.core.TotalSpace) :
    powerMap A 1 p = p := by
  cases p
  simp only [powerMap, pow_one]
  rfl

theorem powerMap_comp (m n : ℕ) (p : A.core.TotalSpace) :
    powerMap (A.power m) n (powerMap A m p) = powerMap A (m * n) p := by
  cases p
  simp only [powerMap, id_eq, pow_mul]
  rfl

/-- Scalar multiplication is homogeneous of degree `n`. -/
theorem sectionPower_smul (n : ℕ) (f : M → ℂ) (s : ∀ x, A.core.Fiber x) (x : M) :
    sectionPower A n (fun y => f y • s y) x =
      f x ^ n • sectionPower A n s x :=
  mul_pow (f x) (id (α := ℂ) (s x)) n

theorem sectionPower_ne_zero (n : ℕ) (s : ∀ x, A.core.Fiber x) {x : M}
    (hs : s x ≠ 0) : sectionPower A n s x ≠ 0 := by
  change (id (α := ℂ) (s x)) ^ n ≠ 0
  exact pow_ne_zero n hs

theorem sectionPower_nowhere_zero (n : ℕ) (s : ∀ x, A.core.Fiber x)
    (hs : ∀ x, s x ≠ 0) : ∀ x, sectionPower A n s x ≠ 0 :=
  fun x => sectionPower_ne_zero A n s (hs x)

theorem sectionPower_eq_zero_iff {n : ℕ} (hn : 0 < n)
    (s : ∀ x, A.core.Fiber x) (x : M) :
    sectionPower A n s x = 0 ↔ s x = 0 := by
  change (id (α := ℂ) (s x)) ^ n = 0 ↔ id (α := ℂ) (s x) = 0
  exact pow_eq_zero_iff (Nat.ne_of_gt hn)

theorem sectionPower_ne_zero_iff {n : ℕ} (hn : 0 < n)
    (s : ∀ x, A.core.Fiber x) (x : M) :
    sectionPower A n s x ≠ 0 ↔ s x ≠ 0 :=
  not_congr (sectionPower_eq_zero_iff A hn s x)

section Holomorphic

variable (n : ℕ) {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace H] [ChartedSpace H M] (I : ModelWithCorners ℂ E H)
    [A.IsHolomorphic I]

local notation "I₁" => modelWithCornersSelf ℂ ℂ

/-- Holomorphicity is proved using the two original bundle atlases and
their exact polynomial local-coordinate formula. -/
theorem powerMap_holomorphic :
    ContMDiff (I.prod I₁) (I.prod I₁) ω (powerMap A n) := by
  intro p
  let i := A.indexAt p.proj
  have hp : p.proj ∈ A.baseSet i := A.mem_baseSet_at p.proj
  have hp' : powerMap A n p ∈ ((A.power n).core.localTriv i).source := hp
  apply (((A.power n).core.localTriv i).contMDiffAt_iff hp').mpr
  refine ⟨Bundle.contMDiffAt_proj A.core.Fiber, ?_⟩
  have he : ContMDiffAt (I.prod I₁) (I.prod I₁) ω (A.core.localTriv i) p :=
    (A.core.localTriv i).contMDiffOn.contMDiffAt
      ((A.core.localTriv i).open_source.mem_nhds hp)
  have hcoeff : (fun q : A.core.TotalSpace =>
      ((A.power n).core.localTriv i (powerMap A n q)).2) =
      (fun q => ((A.core.localTriv i q).2) ^ n) := by
    funext q
    exact congrArg Prod.snd (powerMap_localTriv A n i q)
  rw [hcoeff]
  exact he.snd.pow n

theorem sectionPower_holomorphic (s : ∀ x, A.core.Fiber x)
    (hs : ContMDiff I (I.prod I₁) ω (fun x => (⟨x, s x⟩ : A.core.TotalSpace))) :
    ContMDiff I (I.prod I₁) ω
      (fun x => (⟨x, sectionPower A n s x⟩ : (A.power n).core.TotalSpace)) :=
  (powerMap_holomorphic A n I).comp hs

theorem sectionPower_holomorphicOn (s : ∀ x, A.core.Fiber x) (U : Set M)
    (hs : ContMDiffOn I (I.prod I₁) ω
      (fun x => (⟨x, s x⟩ : A.core.TotalSpace)) U) :
    ContMDiffOn I (I.prod I₁) ω
      (fun x => (⟨x, sectionPower A n s x⟩ : (A.power n).core.TotalSpace)) U := by
  intro x hx
  exact (powerMap_holomorphic A n I ⟨x, s x⟩).comp_contMDiffWithinAt x (hs x hx)

/-- The power of a genuine bundled holomorphic section, in the native
power bundle rather than a scalar proxy. -/
def holomorphicSectionPower (s : ContMDiffSection I ℂ ω A.core.Fiber) :
    ContMDiffSection I ℂ ω (A.power n).core.Fiber where
  toFun := sectionPower A n s
  contMDiff_toFun := sectionPower_holomorphic A n I s s.contMDiff

@[simp] theorem holomorphicSectionPower_apply
    (s : ContMDiffSection I ℂ ω A.core.Fiber) (x : M) :
    holomorphicSectionPower A n I s x = sectionPower A n s x := rfl

theorem holomorphicSectionPower_localCoefficient
    (s : ContMDiffSection I ℂ ω A.core.Fiber) (i : ι) (x : M) :
    (A.power n).localCoefficient (holomorphicSectionPower A n I s) i x =
      (A.localCoefficient s i x) ^ n :=
  sectionPower_localCoefficient A n s i x

theorem holomorphicSectionPower_nowhere_zero
    (s : ContMDiffSection I ℂ ω A.core.Fiber) (hs : ∀ x, s x ≠ 0) :
    ∀ x, holomorphicSectionPower A n I s x ≠ 0 :=
  sectionPower_nowhere_zero A n s hs

/-- A section that is not identically zero has a nonzero power for every
exponent, including exponent zero. -/
theorem holomorphicSectionPower_ne_zero
    (s : ContMDiffSection I ℂ ω A.core.Fiber) (hs : s ≠ 0) :
    holomorphicSectionPower A n I s ≠ 0 := by
  intro h
  apply hs
  ext x
  by_contra hx
  have hval := DFunLike.congr_fun h x
  exact sectionPower_ne_zero A n s hx hval

theorem holomorphicSectionPower_eq_zero_iff (hn : 0 < n)
    (s : ContMDiffSection I ℂ ω A.core.Fiber) :
    holomorphicSectionPower A n I s = 0 ↔ s = 0 := by
  constructor
  · intro h
    by_contra hs
    exact holomorphicSectionPower_ne_zero A n I s hs h
  · intro h
    ext x
    apply (sectionPower_eq_zero_iff A hn s x).mpr
    exact DFunLike.congr_fun h x

end Holomorphic

end Wikipedia.HopfProblem.CanonicalGlobalLineBundle.Powers
