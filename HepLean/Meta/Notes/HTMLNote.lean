/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import HepLean.Meta.Notes.NoteFile
import HepLean.Meta.Basic
import HepLean.Meta.Informal
/-!

## Turns a delaration into a html note structure.

-/

namespace HepLean
open Lean System Meta

/-- A `HTMLNote` is a structure containing the html information from
  invidual contributions (commands, informal commands, note ..) etc. to a note file. -/
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
  let content := "<pre><code>" ++ decl ++ "</code></pre>"
  pure { content := content, fileName := fileName, line := line }

/-- An informal definition or lemma to html for a note. -/
unsafe def HTMLNote.ofInformal (name : Name) : MetaM HTMLNote := do
  let line ← Name.lineNumber name
  let fileName ← Name.fileName name
  let constInfo ← getConstInfo name
  let mut content := ""
  if Informal.isInformalDef constInfo then
    let X ← Informal.constantInfoToInformalDefinition constInfo
    content := "<div class=\"informal-def\">"
      ++ "<a href=\"https://example.com\" class=\"button\">Improve/Formalize</a>"
      ++"<b>Informal definition:</b> " ++ name.toString ++ "<br>"
      ++ X.math.replace "\n" "<br>"
      ++ "</div>"
  else if Informal.isInformalLemma constInfo then
    let X ← Informal.constantInfoToInformalLemma constInfo
    content := "Informal definition: " ++ name.toString ++ "\n" ++ X.math
    content := "Informal lemma: " ++ name.toString
  pure { content := content, fileName := fileName, line := line }

end HepLean
