import LeanestEllipse

/-!
# Transitive axiom audit

Check every declaration, including private and generated declarations, in every imported
`LeanestEllipse` module, including the supporting mathematical modules. Fail on any
transitive axiom dependency other than
`propext`, `Classical.choice`, and `Quot.sound`. In particular, `sorryAx` is rejected.
First check that the root import reaches every project source file, so an unimported module
cannot silently escape the declaration audit.

Run `lake env lean scripts/Audit.lean`. The output is a TSV declaration inventory followed
by a `PASS` line. This checks proof trust; the README separately records statement fidelity.
-/

open Lean Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let sourceFiles ← (System.FilePath.mk "LeanestEllipse").walkDir
  for path in sourceFiles.push (System.FilePath.mk "LeanestEllipse.lean") do
    unless path.extension == some "lean" do continue
    let mod := (path.withExtension "").components.foldl Name.str Name.anonymous
    unless env.header.moduleNames.contains mod do
      throwError "Project source is not imported by LeanestEllipse: {path} (module {mod})"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut out : Array String := #[]
  let mut modules := 0
  for mod in env.header.moduleNames, data in env.header.moduleData do
    unless (`LeanestEllipse).isPrefixOf mod do continue
    modules := modules + 1
    for n in data.constNames do
      let some ci := env.find? n | throwError "Missing declaration: {n}"
      let kind := match ci with
        | .thmInfo _ => "theorem"
        | .defnInfo _ => "def"
        | .axiomInfo _ => "axiom"
        | .opaqueInfo _ => "opaque"
        | _ => "other"
      let axs ← collectAxioms n
      let unexpected := axs.filter fun ax => !allowed.contains ax
      unless unexpected.isEmpty do
        throwError "Unexpected axioms in {n}: {unexpected.toList}"
      let visibility := if n.isInternal then "internal" else "public"
      out := out.push s!"AUDIT\t{mod}\t{kind}\t{n}\t{visibility}\t{axs.toList}"
  IO.println (String.intercalate "\n" out.toList)
  IO.println s!"PASS\t{out.size} declarations in {modules} modules checked"
