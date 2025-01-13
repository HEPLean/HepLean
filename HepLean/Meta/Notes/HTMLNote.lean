/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import HepLean.Meta.Notes.NoteFile
import HepLean.Meta.Informal.Post
/-!

## Turns a delaration into a html note structure.

-/

namespace HepLean
open Lean System Meta

/-- A `HTMLNote` is a structure containing the html information from
  individual contributions (commands, informal commands, note ..) etc. to a note file. -/
structure HTMLNote where
  /-- The name of the file the contribution came from. -/
  fileName : Name
  /-- The html contribution of the content. -/
  content : String
  /-- The line in the file where the contribution came from. -/
  line : Nat

/-- Converts a note infor into a HTMLNote. -/
def HTMLNote.ofNodeInfo (ni : NoteInfo) : MetaM HTMLNote := do
  let line := ni.line
  let decl := ni.content
  let fileName := ni.fileName
  pure { content := decl, fileName := fileName, line := line }

/-- An formal definition or lemma to html for a note. -/
def HTMLNote.ofFormal (name : Name) : MetaM HTMLNote := do
  let line ← Name.lineNumber name
  let decl ← Name.getDeclString name
  let fileName ← Name.fileName name
  let webAddress : String ← Name.toGitHubLink fileName line
  let content :=
    "<div class=\"code-block-container\">"
    ++ "<a href=\"" ++ webAddress ++ "\" class=\"code-button\">View/Improve</a>"
    ++"<pre><code>"
    ++ decl ++
    "</code></pre></div>"
  pure { content := content, fileName := fileName, line := line }

/-- An informal definition or lemma to html for a note. -/
unsafe def HTMLNote.ofInformal (name : Name) : MetaM HTMLNote := do
  let line ← Name.lineNumber name
  let fileName ← Name.fileName name
  let constInfo ← getConstInfo name
  let webAddress : String ← Name.toGitHubLink fileName line
  let mut content := ""
  if Informal.isInformalDef constInfo then
    let X ← Informal.constantInfoToInformalDefinition constInfo
    content := "<div class=\"informal-def\">"
      ++ "<a href=\"" ++ webAddress ++ "\" class=\"button\">Improve/Formalize</a>"
      ++"<b>Informal definition:</b> " ++ name.toString ++ "<br>"
      ++ X.math.replace "\n" "<br>"
      ++ "</div>"
  else if Informal.isInformalLemma constInfo then
    let X ← Informal.constantInfoToInformalLemma constInfo
    content := "<div class=\"informal-def\">"
      ++ "<a href=\"" ++ webAddress ++ "\" class=\"button\">Improve/Formalize</a>"
      ++"<b>Informal lemma:</b> " ++ name.toString ++ "<br>"
      ++ X.math.replace "\n" "<br>"
      ++ "</div>"
  pure { content := content, fileName := fileName, line := line }

end HepLean
