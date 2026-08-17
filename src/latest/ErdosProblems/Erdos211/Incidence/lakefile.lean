import Lake

open Lake DSL

package erdos211Incidence

require unit_distance_upper_bound from git
  "https://github.com/wpegden/unitdistance_challenge.git" @
    "fe9deb3c76358cbaa9149129d1552ebe929b84cc"

/-!
The upstream incidence formalization was written against Lean 4.32.  This hook
applies the small, checked source-level compatibility patch needed by Lean 4.33.
It is deliberately idempotent: an already-patched checkout is left untouched.
-/
post_update pkg do
  let rootPkg ← getRootPackage
  let depDir := rootPkg.dir / ".lake" / "packages" / "unit_distance_upper_bound"
  let patchFile := pkg.dir / "unitdistance-lean433.patch"
  let reverseCheck ← IO.Process.output {
    cmd := "git"
    args := #["-C", depDir.toString, "apply", "--reverse", "--check", patchFile.toString]
  }
  if reverseCheck.exitCode == 0 then
    return
  let applyResult ← IO.Process.output {
    cmd := "git"
    args := #["-C", depDir.toString, "apply", "--check", patchFile.toString]
  }
  if applyResult.exitCode != 0 then
    error s!"{pkg.prettyName}: incidence compatibility patch does not apply:\n{applyResult.stderr}"
  let applied ← IO.Process.output {
    cmd := "git"
    args := #["-C", depDir.toString, "apply", patchFile.toString]
  }
  if applied.exitCode != 0 then
    error s!"{pkg.prettyName}: failed to apply incidence compatibility patch:\n{applied.stderr}"
