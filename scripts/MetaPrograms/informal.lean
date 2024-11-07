/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import Batteries.Lean.HashSet
import Lean
import Mathlib.Lean.Expr.Basic
import Mathlib.Lean.CoreM
import HepLean.Meta.Informal
import ImportGraph.RequiredModules
/-!

# Extracting information about informal definitions and lemmas

To make the dot file for the dependency graph run:
- lake exe informal mkDot
- dot -Tsvg -o ./Docs/graph.svg ./Docs/InformalDot.dot
- or dot -Tpng  -Gdpi=300 -o ./Docs/graph.png ./Docs/InformalDot.dot
-/

open Lean System Meta

def getConst (imp : Import) : IO (Array (Import × ConstantInfo)) := do
  let mFile ← findOLean imp.module
  let (modData, _) ← readModuleData mFile
  pure (modData.constants.map (fun c => (imp, c)))

def getLineNumber (c : Name) : MetaM Nat := do
  match ← findDeclarationRanges? c  with
  | some decl => pure decl.range.pos.line
  | none => panic! s!"{c} is a declaration without position"

def getModule (c : Name) : MetaM Name := do
  match Lean.Environment.getModuleFor? (← getEnv) c with
  | some mod => pure mod
  | none => panic! s!"{c} is a declaration without position"

def getConstInfo (n : Name) : MetaM ConstantInfo := do
  match (← getEnv).find? n  with
  | some c => pure c
  | none => panic! s!"{n} is not a constant"

/-- Gets the docstring from a name, if it exists, otherwise the string "No docstring."-/
def getDocString (n : Name) : MetaM String := do
  match ← Lean.findDocString? (← getEnv) n with
  | some doc => pure doc
  | none => pure "No docstring."

def depToString (d : Name) : MetaM String := do
  let lineNo ← getLineNumber d
  let mod ← getModule d
  pure s!"    * {d}: ./{mod.toString.replace "." "/" ++ ".lean"}:{lineNo}"

def depToWebString (d : Name) : MetaM String := do
  let lineNo ← getLineNumber d
  let mod ← getModule d
  let webPath := "https://github.com/HEPLean/HepLean/blob/master/"++
    (mod.toString.replace "." "/") ++ ".lean"
  pure s!"    * [{d}]({webPath}#L{lineNo})"

/-- Takes a `ConstantInfo` corresponding to a `InformalLemma` and returns
  the corresponding `InformalLemma`. -/
unsafe def constantInfoToInformalLemma (c : ConstantInfo) : MetaM InformalLemma := do
  match c with
  | ConstantInfo.defnInfo c =>
      Lean.Meta.evalExpr' InformalLemma ``InformalLemma c.value
  | _ => panic! "Passed constantInfoToInformalLemma a `ConstantInfo` that is not a `InformalLemma`"

/-- Takes a `ConstantInfo` corresponding to a `InformalDefinition` and returns
  the corresponding `InformalDefinition`. -/
unsafe def constantInfoToInformalDefinition (c : ConstantInfo) : MetaM InformalDefinition := do
  match c with
  | ConstantInfo.defnInfo c =>
      Lean.Meta.evalExpr' InformalDefinition ``InformalDefinition c.value
  | _ => panic! "Passed constantInfoToInformalDefinition a
    `ConstantInfo` that is not a `InformalDefinition`"

unsafe def informalDependencies (c : ConstantInfo) : MetaM (Array Name) := do
  if Informal.isInformalLemma c then
    let informal ← constantInfoToInformalLemma c
    pure informal.dependencies.toArray
  else if Informal.isInformalDef c then
    let informal ← constantInfoToInformalDefinition c
    pure informal.dependencies.toArray
  else
    pure #[]

unsafe def informalLemmaToString (c : Import × ConstantInfo) : MetaM String := do
  let lineNo ← getLineNumber c.2.name
  let informalLemma ← constantInfoToInformalLemma c.2
  let dep ← informalLemma.dependencies.mapM fun d => depToString d
  pure s!"
Informal lemma: {informalLemma.name}
- ./{c.1.module.toString.replace "." "/" ++ ".lean"}:{lineNo}
- Math description: {informalLemma.math}
- Physics description: {informalLemma.physics}
- Proof description: {informalLemma.proof}
- References: {informalLemma.ref}
- Dependencies:\n{String.intercalate "\n" dep}"

unsafe def informalLemmaToWebString (c : Import × ConstantInfo) : MetaM String := do
  let lineNo ← getLineNumber c.2.name
  let informalLemma ← constantInfoToInformalLemma c.2
  let dep ← informalLemma.dependencies.mapM fun d => depToWebString d
  let webPath := "https://github.com/HEPLean/HepLean/blob/master/"++
    (c.1.module.toString.replace "." "/") ++ ".lean"
  pure s!"
**Informal lemma**: [{informalLemma.name}]({webPath}#L{lineNo}) :=
  *{informalLemma.math}*
- Physics description: {informalLemma.physics}
- Proof description: {informalLemma.proof}
- References: {informalLemma.ref}
- Dependencies:\n{String.intercalate "\n" dep}"

unsafe def informalDefToString (c : Import × ConstantInfo) : MetaM String := do
  let lineNo ← getLineNumber c.2.name
  let informalDef ← constantInfoToInformalDefinition c.2
  let dep ← informalDef.dependencies.mapM fun d => depToString d
  pure s!"
Informal def: {informalDef.name}
- ./{c.1.module.toString.replace "." "/" ++ ".lean"}:{lineNo}
- Math description: {informalDef.math}
- Physics description: {informalDef.physics}
- References: {informalDef.ref}
- Dependencies:\n{String.intercalate "\n" dep}"

unsafe def informalDefToWebString (c : Import × ConstantInfo) : MetaM String := do
  let lineNo ← getLineNumber c.2.name
  let informalDef ← constantInfoToInformalDefinition c.2
  let dep ← informalDef.dependencies.mapM fun d => depToWebString d
  let webPath := "https://github.com/HEPLean/HepLean/blob/master/"++
    (c.1.module.toString.replace "." "/") ++ ".lean"
  pure s!"
**Informal def**: [{informalDef.name}]({webPath}#L{lineNo}) :=
  *{informalDef.math}*
- Physics description: {informalDef.physics}
- References: {informalDef.ref}
- Dependencies:\n{String.intercalate "\n" dep}"

unsafe def informalToString (c : Import × ConstantInfo) : MetaM String := do
  if Informal.isInformalLemma c.2 then
    informalLemmaToString c
  else if Informal.isInformalDef c.2 then
    informalDefToString c
  else
    pure ""

unsafe def informalToWebString (c : Import × ConstantInfo) : MetaM String := do
  if Informal.isInformalLemma c.2 then
    informalLemmaToWebString c
  else if Informal.isInformalDef c.2 then
    informalDefToWebString c
  else
    pure ""

def informalFileHeader : String := s!"
# Informal definitions and lemmas

See [informal definitions and lemmas as a dependency graph](https://heplean.github.io/HepLean/graph.svg).

This file is automatically generated using `informal_lemma` and `informal_definition` commands
appearing in the raw Lean code of HepLean.

There is an implicit invitation to the reader to contribute to the formalization of
 informal definitions and lemmas. You may also wish to contribute to HepLean by including
 informal definitions and lemmas in the raw Lean code, especially if you do not have a
 background in Lean.

"

/-- Takes an import and outputs the list of `ConstantInfo` corresponding
  to an informal definition or lemma in that import, sorted by line number. -/
def importToInformal (i : Import) : MetaM (Array (Import × ConstantInfo)) := do
  let constants ← getConst i
  let constants := constants.filter (fun c => ¬ Lean.Name.isInternalDetail c.2.name)
  let informalConst := constants.filter fun c => Informal.isInformal c.2
  let informalConstLineNo ← informalConst.mapM fun c => getLineNumber c.2.name
  let informalConstWithLineNo := informalConst.zip informalConstLineNo
  let informalConstWithLineNoSort := informalConstWithLineNo.qsort (fun a b => a.2 < b.2)
  return informalConstWithLineNoSort.map (fun c => c.1)

unsafe def importToString (i : Import) : MetaM String := do
  let informalConst ← importToInformal i
  let informalPrint ← (informalConst.mapM informalToString).run'
  if informalPrint.isEmpty then
    pure ""
  else
    pure ("\n\n" ++ i.module.toString ++ "\n" ++ String.intercalate "\n\n" informalPrint.toList)

unsafe def importToWebString (i : Import) : MetaM String := do
  let informalConst ← importToInformal i
  let informalPrint ← (informalConst.mapM informalToWebString).run'
  if informalPrint.isEmpty then
    pure ""
  else
    pure ("\n\n## " ++ i.module.toString ++ "\n" ++ String.intercalate "\n\n" informalPrint.toList)

section dotFile
/-!

## Making the dot file for dependency graph.

-/

/-- Turns a formal definition or lemma into a node of a dot graph. -/
def formalToNode (nameSpaces : Array Name) (d : Name) : MetaM String := do
  let lineNo ← getLineNumber d
  let mod ← getModule d
  let webPath := "https://github.com/HEPLean/HepLean/blob/master/"++
    (mod.toString.replace "." "/") ++ ".lean"
  let docstring ← getDocString d
  let prefixName := if nameSpaces.contains d then d else
    d.getPrefix
  let nodeStr := s!"\"{d}\"[label=\"{d}\", shape=box, style=filled, fillcolor=steelblue,
     tooltip=\"{docstring}\"]"
  if prefixName = Lean.Name.anonymous then
    pure nodeStr
  else
    pure ("subgraph cluster_" ++ prefixName.toString.replace "." "_" ++ " { " ++ nodeStr ++ "; }")

unsafe def informalLemmaToNode (nameSpaces : Array Name) (c : Import × ConstantInfo) : MetaM String := do
  let lineNo ← getLineNumber c.2.name
  let webPath := "https://github.com/HEPLean/HepLean/blob/master/"++
    (c.1.module.toString.replace "." "/") ++ ".lean"
  let informalLemma ← (constantInfoToInformalLemma c.2)
  let prefixName := if nameSpaces.contains c.2.name then c.2.name else
    c.2.name.getPrefix
  let nodeStr := s!"\"{c.2.name}\"[label=\"{c.2.name}\", shape=ellipse, style=filled, fillcolor=lightgray,
    tooltip=\"{informalLemma.math}\"]"
  if prefixName = Lean.Name.anonymous then
    pure nodeStr
  else
    pure ("subgraph cluster_" ++ prefixName.toString.replace "." "_" ++ " { " ++ nodeStr ++ "; }")

unsafe def informalDefToNode (nameSpaces : Array Name) (c : Import × ConstantInfo) : MetaM String := do
  let lineNo ← getLineNumber c.2.name
  let webPath := "https://github.com/HEPLean/HepLean/blob/master/"++
    (c.1.module.toString.replace "." "/") ++ ".lean"
  let informalDef ← (constantInfoToInformalDefinition c.2)
  let prefixName := if nameSpaces.contains c.2.name then c.2.name else
    c.2.name.getPrefix
  let nodeStr := s!"\"{c.2.name}\"[label=\"{c.2.name}\", shape=box, style=filled, fillcolor=lightgray,
    tooltip=\"{informalDef.math}\"]"
  if prefixName = Lean.Name.anonymous then
    pure nodeStr
  else
    pure ("subgraph cluster_" ++ prefixName.toString.replace "." "_" ++ " { " ++ nodeStr ++ "; }")


unsafe def informalToNode (nameSpaces : Array Name) (c : Import × ConstantInfo) : MetaM String := do
  if Informal.isInformalLemma c.2 then
    informalLemmaToNode nameSpaces c
  else if Informal.isInformalDef c.2 then
    informalDefToNode nameSpaces c
  else
    pure ""

unsafe def informalLemmaToEdges (c : Import × ConstantInfo) : MetaM (String) := do
  let informalLemma ← constantInfoToInformalLemma c.2
  let deps := informalLemma.dependencies
  let edge := deps.map (fun d => s!"\"{d}\" -> \"{c.2.name}\"")
  pure (String.intercalate "\n" edge)

unsafe def informalDefToEdges (c : Import × ConstantInfo) : MetaM (String) := do
  let informalDef ← constantInfoToInformalDefinition c.2
  let deps := informalDef.dependencies
  let edge := deps.map (fun d => s!"\"{d}\" -> \"{c.2.name}\"")
  pure (String.intercalate "\n" edge)

unsafe def informalToEdges (c : Import × ConstantInfo) : MetaM (String) := do
  if Informal.isInformalLemma c.2 then
    informalLemmaToEdges c
  else if Informal.isInformalDef c.2 then
    informalDefToEdges c
  else
    pure ""

unsafe def namespaceToCluster (name : Name) : MetaM String := do
  let nameUnder := name.toString.replace "." "_"
  if name = Lean.Name.anonymous then
    pure ""
  else
    pure ("subgraph cluster_" ++ nameUnder ++ "
      {
          label=\"" ++ name.toString ++ "\";
          color=steelblue;
              }")

unsafe def mkDot (imports : Array Import) : MetaM String := do
  let informal ← imports.mapM importToInformal
  let informal := informal.flatten
  let deps ← (informal.map (fun c => c.2)).mapM informalDependencies
  let deps := deps.flatten
  let informal_name := informal.map (fun c => c.2.name)
  let informalNameSpaces := informal.map fun c => c.2.name.getPrefix
  let clusters ← informalNameSpaces.mapM fun c => namespaceToCluster c
  let clusters := String.intercalate "\n" clusters.toList.eraseDups
  let formal_deps := deps.filter (fun d => d ∉ informal_name)
  let formal_nodes ← formal_deps.mapM (formalToNode informalNameSpaces)
  let nodes := String.intercalate "\n" formal_nodes.toList

  let informalNodes ← informal.mapM (informalToNode informalNameSpaces)
  let informalNodes := String.intercalate "\n" informalNodes.toList
  let edges ← informal.mapM informalToEdges
  let edges := String.intercalate "\n" edges.toList
  let header := "strict digraph G {
    graph [
    pack=true;
    packmode=\"array1\";
    ];
    tooltip = \"Informal HepLean graph\";
    node [margin=\"0.2,0.05\";  fontsize=10;  fontname=\"Georgia\", height=0.1];
    bgcolor=\"white\";
    labelloc=\"t\";
    labeljust=\"l\";
    edge [arrowhead=vee];"
  let footer := "}"
  pure (header ++ "\n" ++clusters ++ "\n" ++ nodes ++ "\n" ++
    informalNodes ++ "\n" ++ edges ++ "\n" ++ footer)

end dotFile

section htmlFile

/-!

## Making the html file for dependency graph.

-/

def formalToHTML (d : Name) : MetaM String := do
  let lineNo ← getLineNumber d
  let mod ← getModule d
  let webPath := "https://github.com/HEPLean/HepLean/blob/master/"++
    (mod.toString.replace "." "/") ++ ".lean"
  let docstring ← getDocString d
  pure s!"
<div id=\"{d}\" class=\"node-text\">
<b><a href=\"{webPath ++ "#L" ++ toString lineNo}\">{d}</a></b><br>
<b>Docstring: </b>{docstring}

</div>"

unsafe def informalLemmaToHTML (c : Import × ConstantInfo) : MetaM String := do
  let lineNo ← getLineNumber c.2.name
  let webPath := "https://github.com/HEPLean/HepLean/blob/master/"++
    (c.1.module.toString.replace "." "/") ++ ".lean"
  let informalLemma ← (constantInfoToInformalLemma c.2)
  pure s!"
<div id=\"{c.2.name}\" class=\"node-text\">
<b><a href=\"{webPath ++ "#L" ++ toString lineNo}\">{c.2.name}</a></b><br>
<b>Math description: </b>{informalLemma.math}<br>
<b>Physics description: </b>{informalLemma.physics}<br>
</div>"

unsafe def informalDefToHTML (c : Import × ConstantInfo) : MetaM String := do
  let lineNo ← getLineNumber c.2.name
  let webPath := "https://github.com/HEPLean/HepLean/blob/master/"++
    (c.1.module.toString.replace "." "/") ++ ".lean"
  let informalDef ← (constantInfoToInformalDefinition c.2)
  pure s!"
<div id=\"{c.2.name}\" class=\"node-text\">
<b><a href=\"{webPath ++ "#L" ++ toString lineNo}\">{c.2.name}</a></b><br>
<b>Math description: </b>{informalDef.math}<br>
<b>Physics description: </b>{informalDef.physics}<br>
</div>"

unsafe def informalToHTML (c : Import × ConstantInfo) : MetaM String := do
  if Informal.isInformalLemma c.2 then
    informalLemmaToHTML c
  else if Informal.isInformalDef c.2 then
    informalDefToHTML c
  else
    pure ""

unsafe def toHTML (imports : Array Import) : MetaM String := do
  let informal ← imports.mapM importToInformal
  let informal := informal.flatten
  let deps ← (informal.map (fun c => c.2)).mapM informalDependencies
  let deps := deps.flatten
  let informal_name := informal.map (fun c => c.2.name)
  let formal_deps := deps.filter (fun d => d ∉ informal_name)
  let formal_nodes ← formal_deps.mapM (formalToHTML)
  let nodes := String.intercalate "\n" formal_nodes.toList
  let informalNodes ← informal.mapM (informalToHTML)
  let informalNodes := String.intercalate "\n" informalNodes.toList
  let header := "---
layout: default
---
<!DOCTYPE html>
<html>
<head>
    <title>Informal dependency graph for HepLean</title>
    <style>
        /* Optional styling for the message display */
        #message {
            margin-top: 20px;
            font-size: 1.2em;
            color: #333;
        }

        /* Optional: Hide the text content divs */
        .node-text {
            display: none;
            font-family: 'Times New Roman', Times, serif;
        }
    </style>
</head>
<body>
    <!-- Include D3.js -->
    <script src=\"https://d3js.org/d3.v5.min.js\"></script>
    <!-- Include hpcc-js/wasm for Graphviz layout -->
    <script src=\"https://unpkg.com/@hpcc-js/wasm@0.3.11/dist/index.min.js\"></script>
    <!-- Include d3-graphviz for rendering Graphviz graphs -->
    <script src=\"https://unpkg.com/d3-graphviz@3.0.5/build/d3-graphviz.js\"></script>

    <!-- Add a title to the page -->
    <h1 style=\"text-align: center;\">Informal dependency graph for HepLean</h1>
    <p style=\"text-align: center;\">Click on a node to display the text associated with it.</p>
    <p style=\"text-align: center;\">This graph only shows informal results (gray) and their direct formal dependencies (blue).
    It does not show all results formalised into HepLean.</p>
    <!-- Div to display the graph -->
    <div id=\"graph\" style=\"width: 75vw; height: 75vh; border: 1px solid black\"></div>

    <!-- Hidden divs containing the text to display when nodes are clicked -->

    <!-- Add more divs for other nodes as needed, each with id equal to the node name -->
    <div id=\"includedContent\"></div>
    <!-- Div to display the message when a node is clicked -->
    <div id=\"message\"></div>"
  let footer := "
  <script type=\"text/javascript\">
        // Load the DOT file and render the graph
        d3.text(\"InformalDot.dot\").then(function(dotSrc) {
            var width = 0.75 * window.innerWidth;
            var height = 0.75 * window.innerHeight;

            // Initialize the graphviz renderer
            var graphviz = d3.select(\"#graph\")
                .graphviz()
                .width(width)
                .height(height)
                .fit(true);

            // Render the graph and attach event listeners
            graphviz.renderDot(dotSrc).on(\"end\", function() {
                // Attach click event to nodes
                d3.selectAll('.node').on('click', function() {
                    // Get the node's name from the title element
                    var nodeName = d3.select(this).select('title').text();

                    // Get the text associated with the nodeName
                    var nodeTextElement = document.getElementById(nodeName);

                    if (nodeTextElement) {
                        var nodeText = nodeTextElement.innerHTML;
                        // Display the text in the #message div
                        document.getElementById('message').innerHTML = nodeText;
                    } else {
                        // If no element with the nodeName ID exists
                        document.getElementById('message').innerHTML = 'No information available for node: ' + nodeName;
                    }
                });
            });
        });
    </script>
</body>
</html>
"
  pure (header ++ "\n" ++ nodes ++ "\n" ++
    informalNodes ++  "\n" ++ footer)

end htmlFile
/-!

## Main function

-/
unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let mods : Name := `HepLean
  let imp : Import := {module := mods}
  let mFile ← findOLean imp.module
  unless (← mFile.pathExists) do
        throw <| IO.userError s!"object file '{mFile}' of module {imp.module} does not exist"
  let (hepLeanMod, _) ← readModuleData mFile
  let imports := hepLeanMod.imports.filter (fun c => c.module ≠ `Init)
  let importString ← CoreM.withImportModules #[`HepLean] (imports.mapM importToString).run'
  IO.println (String.intercalate "" importString.toList)
  /- Writing out informal file. -/
  let fileOut : System.FilePath := {toString := "./docs/Informal.md"}
  if "mkFile" ∈ args then
    let importWebString ← CoreM.withImportModules #[`HepLean] (imports.mapM importToWebString).run'
    let out := String.intercalate "\n" importWebString.toList
    IO.println (s!"Informal file made.")
    IO.FS.writeFile fileOut (informalFileHeader ++ out)
  /- Making the dot file. -/
  if "mkDot" ∈ args then
    let dot ← CoreM.withImportModules #[`HepLean] (mkDot imports).run'
    let dotFile : System.FilePath := {toString := "./docs/InformalDot.dot"}
    IO.FS.writeFile dotFile dot
    IO.println (s!"Dot file made.")
  /- Making the html file. -/
  if "mkHTML" ∈ args then
    let html ← CoreM.withImportModules #[`HepLean] (toHTML imports).run'
    let htmlFile : System.FilePath := {toString := "./docs/InformalGraph.html"}
    IO.FS.writeFile htmlFile html
    IO.println (s!"HTML file made.")
  pure 0
