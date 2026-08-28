import Wikipedia.NoExoticSixSphere.OrthogonalColumnHomotopy
import Wikipedia.NoExoticSixSphere.OrthogonalGroupOperations

/-!
# Exact lifting of compact column homotopies

Finite interval subdivision and local rotations lift every intermediate slice
of a column homotopy, not merely its endpoint. Clamped time maps make each
extension globally continuous. Parameters with stationary columns retain their
initial orthogonal operator throughout the lift.
-/

open Set unitInterval

namespace NoExoticSixSphere.OrthogonalPaths

open GLOrthonormalization

variable {n : ℕ} {X : Type*} [TopologicalSpace X]

theorem localRotations_self_at (f g : C(X, UnitSphere (Vector n)))
    (h : ∀ x, dist (g x : Vector n) (f x : Vector n) < 1) (x : X) (hx : f x = g x) :
    localRotations f g h x = identity n := by
  apply Subtype.ext
  apply Subtype.ext
  change localRotationOperator (f x : Vector n) (g x : Vector n) = 1
  rw [hx, localRotationOperator_self]

namespace ColumnLift

/-- Clamp the time to a single closed subdivision interval. -/
def clip (s u t : I) : I := min (max t s) u

theorem clip_mem {s u : I} (hsu : s ≤ u) (t : I) : clip s u t ∈ Icc s u :=
  ⟨le_min (le_max_right _ _) hsu, min_le_right _ _⟩

theorem clip_of_le {s u t : I} (hsu : s ≤ u) (ht : t ≤ s) : clip s u t = s := by
  rw [clip, max_eq_right ht, min_eq_left hsu]

theorem clip_of_ge {s u t : I} (ht : s ≤ t) : clip s u t = min t u := by
  rw [clip, max_eq_left ht]

def stopMap (s : I) : C(I × X, I × X) :=
  ⟨fun p ↦ (min p.1 s, p.2), (continuous_fst.min continuous_const).prodMk continuous_snd⟩

def clipMap (s u : I) : C(I × X, I × X) :=
  ⟨fun p ↦ (clip s u p.1, p.2),
    ((continuous_fst.max continuous_const).min continuous_const).prodMk continuous_snd⟩

variable (H : C(I × X, UnitSphere (Vector n))) (s u : I)

def startColumn : C(I × X, UnitSphere (Vector n)) :=
  H.comp ⟨fun p ↦ (s, p.2), continuous_const.prodMk continuous_snd⟩

def clippedColumn : C(I × X, UnitSphere (Vector n)) := H.comp (clipMap s u)

variable (hsu : s ≤ u)
variable (hclose : ∀ t ∈ Icc s u, ∀ x,
  dist (H (t, x) : Vector n) (H (s, x) : Vector n) < 1)

noncomputable def rotations : C(I × X, OrthogonalOperators n) :=
  localRotations (startColumn H s) (clippedColumn H s u)
    (fun p ↦ hclose (clip s u p.1) (clip_mem hsu p.1) p.2)

theorem rotations_before (t : I) (x : X) (ht : t ≤ s) :
    rotations H s u hsu hclose (t, x) = identity n := by
  apply localRotations_self_at
  change H (s, x) = H (clip s u t, x)
  rw [clip_of_le hsu ht]

noncomputable def step (a : C(I × X, OrthogonalOperators n)) :
    C(I × X, OrthogonalOperators n) :=
  mulMap (rotations H s u hsu hclose) (a.comp (stopMap s))

theorem step_apply (a : C(I × X, OrthogonalOperators n)) (t : I) (x : X) :
    step H s u hsu hclose a (t, x) =
      mul (rotations H s u hsu hclose (t, x)) (a (min t s, x)) := rfl

theorem step_before (a : C(I × X, OrthogonalOperators n)) (t : I) (x : X) (ht : t ≤ s) :
    step H s u hsu hclose a (t, x) = a (t, x) := by
  rw [step_apply, rotations_before H s u hsu hclose t x ht, min_eq_left ht, identity_mul]

theorem step_column_family (a : C(I × X, OrthogonalOperators n))
    (v : X → UnitSphere (Vector n))
    (ha : ∀ t x, (a (t, x)).1.1 (v x : Vector n) = (H (min t s, x) : Vector n)) :
    ∀ t x, (step H s u hsu hclose a (t, x)).1.1 (v x : Vector n) =
      (H (min t u, x) : Vector n) := by
  intro t x
  by_cases ht : t ≤ s
  · rw [step_before H s u hsu hclose a t x ht, ha,
      min_eq_left ht, min_eq_left (ht.trans hsu)]
  · have hst : s ≤ t := le_of_not_ge ht
    rw [step_apply, mul_apply, ha, min_eq_right hst, min_self]
    have hr := localRotations_apply (startColumn H s) (clippedColumn H s u)
      (fun p ↦ hclose (clip s u p.1) (clip_mem hsu p.1) p.2) (t, x)
    change (rotations H s u hsu hclose (t, x)).1.1 (H (s, x) : Vector n) =
      (H (clip s u t, x) : Vector n) at hr
    simpa only [clip_of_ge hst] using hr

theorem step_column (a : C(I × X, OrthogonalOperators n)) (v : UnitSphere (Vector n))
    (ha : ∀ t x, (a (t, x)).1.1 (v : Vector n) = (H (min t s, x) : Vector n)) :
    ∀ t x, (step H s u hsu hclose a (t, x)).1.1 (v : Vector n) =
      (H (min t u, x) : Vector n) :=
  step_column_family H s u hsu hclose a (fun _ ↦ v) ha

theorem step_stationary (a : C(I × X, OrthogonalOperators n)) (a₀ : C(X, OrthogonalOperators n))
    (x : X) (hH : ∀ t, H (t, x) = H (0, x)) (ha : ∀ t, a (t, x) = a₀ x) :
    ∀ t, step H s u hsu hclose a (t, x) = a₀ x := by
  intro t
  have hr : rotations H s u hsu hclose (t, x) = identity n := by
    apply localRotations_self_at
    change H (s, x) = H (clip s u t, x)
    exact (hH s).trans (hH (clip s u t)).symm
  rw [step_apply, hr, identity_mul, ha]

end ColumnLift

variable [CompactSpace X]

/-- A compact column family admits a finite time subdivision uniformly close to each left end. -/
theorem exists_columnSubdivision (H : C(I × X, UnitSphere (Vector n))) :
    ∃ t : ℕ → I, t 0 = 0 ∧ Monotone t ∧ (∃ N, ∀ i ≥ N, t i = 1) ∧
      ∀ i, ∀ u ∈ Icc (t i) (t (i + 1)), ∀ x,
        dist (H (u, x) : Vector n) (H (t i, x) : Vector n) < 1 := by
  let U (s : I) : Set I := {t | ∀ x,
    dist (H (t, x) : Vector n) (H (s, x) : Vector n) < (1 : ℝ) / 2}
  have hU : ∀ s, IsOpen (U s) := by
    intro s
    have h₁ := continuous_subtype_val.comp H.continuous
    have h₂ : Continuous (fun p : I × X ↦ (H (s, p.2) : Vector n)) :=
      continuous_subtype_val.comp
      (H.continuous.comp (continuous_const.prodMk continuous_snd))
    exact isOpen_forall_compact (isOpen_lt (h₁.dist h₂) continuous_const)
  have hcover : univ ⊆ ⋃ s, U s := by
    intro t _
    refine mem_iUnion.mpr ⟨t, ?_⟩
    intro x
    simp only [dist_self]
    norm_num
  obtain ⟨t, ht0, hmono, hend, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hU hcover
  refine ⟨t, ht0, hmono, hend, ?_⟩
  intro i u hu x
  obtain ⟨s, hs⟩ := hsub i
  have hu' := hs hu x
  have ht' := hs ⟨le_rfl, hmono i.le_succ⟩ x
  have htri := dist_triangle (H (u, x) : Vector n) (H (s, x) : Vector n)
    (H (t i, x) : Vector n)
  rw [dist_comm (H (s, x) : Vector n) (H (t i, x) : Vector n)] at htri
  linarith

/-- The initial column may vary with the parameter; no global lift of that column
to an orthogonal frame is needed. -/
theorem exists_exactColumnLiftFamily (H : C(I × X, UnitSphere (Vector n)))
    (v : X → UnitSphere (Vector n)) (a₀ : C(X, OrthogonalOperators n))
    (ha₀ : ∀ x, (a₀ x).1.1 (v x : Vector n) = (H (0, x) : Vector n)) :
    ∃ G : C(I × X, OrthogonalOperators n),
      (∀ x, G (0, x) = a₀ x) ∧
      (∀ t x, (G (t, x)).1.1 (v x : Vector n) = (H (t, x) : Vector n)) ∧
      ∀ x, (∀ t, H (t, x) = H (0, x)) → ∀ t, G (t, x) = a₀ x := by
  obtain ⟨t, ht0, hmono, ⟨N, hN⟩, hclose⟩ := exists_columnSubdivision H
  have hex : ∀ i, ∃ G : C(I × X, OrthogonalOperators n),
      (∀ x, G (0, x) = a₀ x) ∧
      (∀ u x, (G (u, x)).1.1 (v x : Vector n) = (H (min u (t i), x) : Vector n)) ∧
      ∀ x, (∀ u, H (u, x) = H (0, x)) → ∀ u, G (u, x) = a₀ x := by
    intro i
    induction i with
    | zero =>
      refine ⟨a₀.comp ⟨Prod.snd, continuous_snd⟩, fun x ↦ rfl, ?_, fun x _ u ↦ rfl⟩
      intro u x
      change (a₀ x).1.1 (v x : Vector n) = _
      rw [ht0, min_eq_right (show (0 : I) ≤ u from bot_le)]
      exact ha₀ x
    | succ i ih =>
      obtain ⟨G, hG0, hGcol, hGfix⟩ := ih
      refine ⟨ColumnLift.step H (t i) (t (i + 1)) (hmono i.le_succ) (hclose i) G,
        ?_, ColumnLift.step_column_family H (t i) (t (i + 1))
          (hmono i.le_succ) (hclose i) G v hGcol, ?_⟩
      · intro x
        rw [ColumnLift.step_before H (t i) (t (i + 1)) (hmono i.le_succ) (hclose i) G 0 x bot_le]
        exact hG0 x
      · intro x hx
        exact ColumnLift.step_stationary H (t i) (t (i + 1))
          (hmono i.le_succ) (hclose i) G a₀ x hx (hGfix x hx)
  obtain ⟨G, hG0, hGcol, hGfix⟩ := hex N
  refine ⟨G, hG0, ?_, hGfix⟩
  intro u x
  simpa only [hN N le_rfl, min_eq_left (show u ≤ (1 : I) from le_top)] using hGcol u x

/-- Lift every slice of a compact sphere-column homotopy to actual orthogonal operators,
preserving the prescribed initial family and every stationary parameter. -/
theorem exists_exactColumnLift (H : C(I × X, UnitSphere (Vector n)))
    (v : UnitSphere (Vector n)) (a₀ : C(X, OrthogonalOperators n))
    (ha₀ : ∀ x, (a₀ x).1.1 (v : Vector n) = (H (0, x) : Vector n)) :
    ∃ G : C(I × X, OrthogonalOperators n),
      (∀ x, G (0, x) = a₀ x) ∧
      (∀ t x, (G (t, x)).1.1 (v : Vector n) = (H (t, x) : Vector n)) ∧
      ∀ x, (∀ t, H (t, x) = H (0, x)) → ∀ t, G (t, x) = a₀ x :=
  exists_exactColumnLiftFamily H (fun _ ↦ v) a₀ ha₀

/-- Transport a varying initial column along a compact homotopy, starting at the
identity and staying the identity at each stationary parameter. -/
theorem exists_columnTransport (H : C(I × X, UnitSphere (Vector n))) :
    ∃ G : C(I × X, OrthogonalOperators n),
      (∀ x, G (0, x) = identity n) ∧
      (∀ t x, (G (t, x)).1.1 (H (0, x) : Vector n) = (H (t, x) : Vector n)) ∧
      ∀ x, (∀ t, H (t, x) = H (0, x)) → ∀ t, G (t, x) = identity n :=
  exists_exactColumnLiftFamily H (fun x ↦ H (0, x))
    (ContinuousMap.const X (identity n)) (fun _ ↦ rfl)

/-- Native relative homotopies of sphere columns lift to native relative orthogonal homotopies.
No closedness assumption on the fixed parameter set is needed. -/
theorem exists_exactColumnHomotopyRel {f g : C(X, UnitSphere (Vector n))} {S : Set X}
    (H : f.HomotopyRel g S) (v : UnitSphere (Vector n)) (a : C(X, OrthogonalOperators n))
    (ha : ∀ x, (a x).1.1 (v : Vector n) = (f x : Vector n)) :
    ∃ b : C(X, OrthogonalOperators n), ∃ G : a.HomotopyRel b S,
      ∀ t x, (G (t, x)).1.1 (v : Vector n) = (H (t, x) : Vector n) := by
  have hstart : ∀ x, (a x).1.1 (v : Vector n) =
      (H.toHomotopy.toContinuousMap (0, x) : Vector n) := by
    intro x
    exact (ha x).trans (congrArg Subtype.val (H.apply_zero x)).symm
  obtain ⟨F, hF0, hFcol, hFfix⟩ := exists_exactColumnLift H.toHomotopy.toContinuousMap v a hstart
  let b : C(X, OrthogonalOperators n) :=
    ⟨fun x ↦ F (1, x), F.continuous.comp (continuous_const.prodMk continuous_id)⟩
  let G : a.HomotopyRel b S :=
    { toContinuousMap := F
      map_zero_left := hF0
      map_one_left := fun x ↦ rfl
      prop' := fun t x hx ↦ hFfix x
        (fun u ↦ (H.eq_fst u hx).trans (H.eq_fst 0 hx).symm) t }
  exact ⟨b, G, hFcol⟩

end NoExoticSixSphere.OrthogonalPaths
