/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
-- NOT a `module`-header file (deliberately): this is exe tooling, not library
-- API, and it consumes the legacy (non-module) LeanArchitect package, whose
-- declarations the module system imports privately/`meta`-walled. Legacy mode
-- has no such wall. The expose-section rule (test_router) governs
-- `module`-header files only.
import Architect

/-!
# `blueprint_export` — blueprint JSON with *inferred* dependency edges

LeanArchitect's own `--json` facet serializes nodes without running
`Node.inferUses` — only its LaTeX path carries `\uses{…}` — so the JSON has
empty edge sets (upstream gap as of `v4.30.0-rc2`). This exe closes the gap by
consuming the package's public API: enumerate the module's blueprint nodes
(`getBlueprintContents`), run the transitive proof-term dependency inference
(`Node.inferUses`, a `collectAxioms`-style walk that stops at blueprint-tagged
constants — so edges pass *through* untagged intermediates), and emit one JSON
array that `tools/blueprint_render.py` turns into the mermaid spine of
`docs/blueprint.md`. The graph is generated ground truth, never hand-drawn.

Run inside the verify container (after `lake build MathFin.Blueprint`):

  `lake exe blueprint_export MathFin.Blueprint`
-/

open Lean Architect

def main (args : List String) : IO Unit := do
  let module := ((args.head?).map (·.toName)).getD `MathFin.Blueprint
  runEnvOfImports #[module] {} do
    let contents ← getBlueprintContents module
    let mut out : Array Json := #[]
    for c in contents do
      if let .node node := c then
        -- `InferredUses.uses` is already an array of blueprint *labels*
        -- (collectUsed's transitive walk, resolved + explicit `uses :=`
        -- merged, excludes applied).
        let (stmtUses, proofUses) ← node.toNode.inferUses
        let usesLabels :=
          (stmtUses.uses ++ proofUses.uses).toList.eraseDups.filter
            (· ≠ node.latexLabel)
        out := out.push <| Json.mkObj [
          ("name", Json.str node.name.toString),
          ("label", Json.str node.latexLabel),
          ("title", node.title.map Json.str |>.getD Json.null),
          ("latexEnv", Json.str node.statement.latexEnv),
          ("text", Json.str node.statement.text),
          ("module", Json.str (node.location.map (·.module.toString) |>.getD "")),
          ("line", Json.num (node.location.map (·.range.pos.line) |>.getD 0)),
          ("file", Json.str (node.file.map (·.toString) |>.getD "")),
          ("leanOk", Json.bool (stmtUses.leanOk && proofUses.leanOk)),
          ("uses", Json.arr (usesLabels.toArray.map Json.str))
        ]
    IO.println (Json.arr out).pretty
