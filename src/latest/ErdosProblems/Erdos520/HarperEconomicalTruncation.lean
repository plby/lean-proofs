import ErdosProblems.Erdos520.HarperBlockAvailability

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Erdos
namespace Problem520

/-!
# Economical vertical truncation

For a cutoff `y`, write `A` for its available twice-logarithmic block scale.
We keep only the first `A / 8` unit vertical shells.  This is already enough
for the Parseval tail to be smaller than the target scale, while the
logarithmic height shift of every retained shell consumes at most one quarter
of `A`.  Hence the economical schedule retains a path comparable with all of
`A`, uniformly over the retained shells.
-/

/-- Linear vertical truncation in the available block scale. -/
def harperEconomicalVerticalTruncation (y : ℕ) : ℕ :=
  harperAvailableLogScale y / 8

/-- Elementary exponential domination used to bound a base-two ceiling
logarithm by its argument. -/
theorem harper_self_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      have hone : 1 ≤ 2 ^ n := one_le_pow₀ (by norm_num)
      omega

theorem harper_clog_two_le_self (n : ℕ) : Nat.clog 2 n ≤ n := by
  exact Nat.clog_le_of_le_pow (harper_self_le_two_pow n)

/-- Every retained shell has a logarithmic height shift bounded by one
quarter of the available scale, once the fixed analytic threshold fits with
absolute slack. -/
theorem harperEconomical_shellShift_le_quarter
    {y J shell : ℕ}
    (hlarge : 8 * (J + 2) ≤ harperAvailableLogScale y)
    (hshell : shell < harperEconomicalVerticalTruncation y) :
    J + Nat.clog 2 (shell + 2) ≤ harperAvailableLogScale y / 4 := by
  let A := harperAvailableLogScale y
  have hclog : Nat.clog 2 (shell + 2) ≤ shell + 2 :=
    harper_clog_two_le_self (shell + 2)
  have hshell' : shell < A / 8 := by
    simpa only [A, harperEconomicalVerticalTruncation] using! hshell
  have hlarge' : 8 * (J + 2) ≤ A := by simpa only [A] using! hlarge
  omega

/-- In particular the economical start lies in the first half of the
available scale. -/
theorem harperEconomical_shellShift_le_half
    {y J shell : ℕ}
    (hlarge : 8 * (J + 2) ≤ harperAvailableLogScale y)
    (hshell : shell < harperEconomicalVerticalTruncation y) :
    J + Nat.clog 2 (shell + 2) ≤ harperAvailableLogScale y / 2 := by
  have hquarter := harperEconomical_shellShift_le_quarter hlarge hshell
  omega

/-- There is room for a nonempty path after the shell-dependent start. -/
theorem harperEconomical_shell_room
    {y J shell : ℕ}
    (hlarge : 8 * (J + 2) ≤ harperAvailableLogScale y)
    (hshell : shell < harperEconomicalVerticalTruncation y) :
    J + Nat.clog 2 (shell + 2) + 5 ≤ harperAvailableLogScale y := by
  have hquarter := harperEconomical_shellShift_le_quarter hlarge hshell
  have hA : 16 ≤ harperAvailableLogScale y := by
    have hJ : 16 ≤ 8 * (J + 2) := by omega
    omega
  omega

/-- Canonical start for the unit shell with index `shell`.  Its natural
height bound is `shell + 1`, hence the shift uses `clog 2 (shell + 2)`. -/
def harperEconomicalShellStart (J shell : ℕ) : ℕ :=
  harperEconomicalStart J (Nat.clog 2 (shell + 2))

/-- Canonical path length paired with `harperEconomicalShellStart`. -/
def harperEconomicalShellPathLength (y J shell : ℕ) : ℕ :=
  harperEconomicalPathLength y J (Nat.clog 2 (shell + 2))

theorem harperEconomicalShellPathLength_pos
    {y J shell : ℕ}
    (hlarge : 8 * (J + 2) ≤ harperAvailableLogScale y)
    (hshell : shell < harperEconomicalVerticalTruncation y) :
    0 < harperEconomicalShellPathLength y J shell := by
  exact harperEconomicalPathLength_pos
    (harperEconomical_shell_room hlarge hshell)

/-- The final scheduled endpoint of a retained shell path lies below `y`. -/
theorem harperBlockEndpoint_economicalShellStart_add_path_le
    {y J shell : ℕ} (hy : y ≠ 0)
    (hlarge : 8 * (J + 2) ≤ harperAvailableLogScale y)
    (hshell : shell < harperEconomicalVerticalTruncation y) :
    harperBlockEndpoint
        (harperEconomicalShellStart J shell +
          harperEconomicalShellPathLength y J shell) ≤ y := by
  unfold harperEconomicalShellStart harperEconomicalShellPathLength
  apply harperBlockEndpoint_economicalStart_add_le hy
  · have hroom := harperEconomical_shell_room hlarge hshell
    unfold harperEconomicalStart
    omega
  · exact le_rfl

/-- The retained path controls the real log-log scale uniformly in the shell
index. -/
theorem one_add_logLogNat_le_two_mul_economicalShellPathLength_add_ten
    {y J shell : ℕ}
    (hlarge : 8 * (J + 2) ≤ harperAvailableLogScale y)
    (hshell : shell < harperEconomicalVerticalTruncation y) :
    1 + logLogNat y ≤
      2 * (harperEconomicalShellPathLength y J shell : ℝ) + 10 := by
  unfold harperEconomicalShellPathLength
  apply one_add_logLogNat_le_two_mul_economicalPathLength_add_ten
  · have hroom := harperEconomical_shell_room hlarge hshell
    omega
  · exact harperEconomical_shellShift_le_half hlarge hshell

/-- The truncation itself is a fixed positive fraction of the available
integer scale. -/
theorem availableLogScale_le_sixteen_mul_economicalVerticalTruncation
    {y : ℕ} (hlarge : 16 ≤ harperAvailableLogScale y) :
    harperAvailableLogScale y ≤
      16 * harperEconomicalVerticalTruncation y := by
  unfold harperEconomicalVerticalTruncation
  omega

/-! ## The same allocation for shrinking central bands -/

/-- The dyadic central-band depth uses the same linear truncation. -/
def harperEconomicalCentralDepth (y : ℕ) : ℕ :=
  harperAvailableLogScale y / 8

def harperEconomicalCentralStart (J depth : ℕ) : ℕ :=
  harperEconomicalStart J depth

def harperEconomicalCentralPathLength (y J depth : ℕ) : ℕ :=
  harperEconomicalPathLength y J depth

theorem harperEconomical_centralShift_le_half
    {y J depth : ℕ}
    (hlarge : 8 * (J + 2) ≤ harperAvailableLogScale y)
    (hdepth : depth < harperEconomicalCentralDepth y) :
    J + depth ≤ harperAvailableLogScale y / 2 := by
  unfold harperEconomicalCentralDepth at hdepth
  omega

theorem harperEconomical_central_room
    {y J depth : ℕ}
    (hlarge : 8 * (J + 2) ≤ harperAvailableLogScale y)
    (hdepth : depth < harperEconomicalCentralDepth y) :
    J + depth + 5 ≤ harperAvailableLogScale y := by
  unfold harperEconomicalCentralDepth at hdepth
  omega

theorem harperEconomicalCentralPathLength_pos
    {y J depth : ℕ}
    (hlarge : 8 * (J + 2) ≤ harperAvailableLogScale y)
    (hdepth : depth < harperEconomicalCentralDepth y) :
    0 < harperEconomicalCentralPathLength y J depth := by
  exact harperEconomicalPathLength_pos
    (harperEconomical_central_room hlarge hdepth)

theorem harperBlockEndpoint_economicalCentralStart_add_path_le
    {y J depth : ℕ} (hy : y ≠ 0)
    (hlarge : 8 * (J + 2) ≤ harperAvailableLogScale y)
    (hdepth : depth < harperEconomicalCentralDepth y) :
    harperBlockEndpoint
        (harperEconomicalCentralStart J depth +
          harperEconomicalCentralPathLength y J depth) ≤ y := by
  unfold harperEconomicalCentralStart harperEconomicalCentralPathLength
  apply harperBlockEndpoint_economicalStart_add_le hy
  · have hroom := harperEconomical_central_room hlarge hdepth
    unfold harperEconomicalStart
    omega
  · exact le_rfl

theorem one_add_logLogNat_le_two_mul_economicalCentralPathLength_add_ten
    {y J depth : ℕ}
    (hlarge : 8 * (J + 2) ≤ harperAvailableLogScale y)
    (hdepth : depth < harperEconomicalCentralDepth y) :
    1 + logLogNat y ≤
      2 * (harperEconomicalCentralPathLength y J depth : ℝ) + 10 := by
  unfold harperEconomicalCentralPathLength
  apply one_add_logLogNat_le_two_mul_economicalPathLength_add_ten
  · have hroom := harperEconomical_central_room hlarge hdepth
    omega
  · exact harperEconomical_centralShift_le_half hlarge hdepth

end Problem520
end Erdos
