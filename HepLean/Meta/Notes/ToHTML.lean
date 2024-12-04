/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import HepLean.Meta.Notes.HTMLNote
import HepLean.Meta.Basic
/-!

## Turns a delaration into a html note structure.

-/

namespace HepLean
open Lean System Meta

namespace NoteFile
variable (N : NoteFile)

/-- Sorts `NoteInfo`'s by file name then by line number. -/
def sortLE (ni1 ni2 : HTMLNote) : Bool :=
  if  N.files.indexOf ni1.fileName ≠  N.files.indexOf ni2.fileName
  then N.files.indexOf ni1.fileName ≤ N.files.indexOf ni2.fileName
  else
  ni1.line ≤ ni2.line

/-- Returns a sorted list of NodeInfos for a file system. -/
unsafe def getNodeInfo : MetaM (List HTMLNote) := do
  let env ← getEnv
  let allNotes := (noteExtension.getState env)
  let allDecl := (noteDeclExtension.getState env)
  let allInformalDecl := noteInformalDeclExtension.getState env
  let allNoteInfo := (← allNotes.mapM noteInfoToHTMLNote) ++ (← allDecl.mapM formalToHTMLNote)
    ++ (← allInformalDecl.mapM informalToHTMLNote)
  let noteInfo := allNoteInfo.filter (fun x => x.fileName ∈ N.files)
  let noteInfoSort := noteInfo.toList.mergeSort N.sortLE
  pure noteInfoSort

def codeBlockHTML : String := "
<meta charset=\"UTF-8\">
    <meta name=\"viewport\" content=\"width=device-width, initial-scale=1.0\">
    <!-- Include Highlight.js CSS -->
    <link rel=\"stylesheet\" href=\"https://cdnjs.cloudflare.com/ajax/libs/highlight.js/11.8.0/styles/default.min.css\">
    <!-- Include Highlight.js -->
    <script src=\"https://cdnjs.cloudflare.com/ajax/libs/highlight.js/11.8.0/highlight.min.js\"></script>
    <!-- Enable Highlight.js -->
    <script>hljs.highlightAll();</script>
    <script>
      hljs.registerLanguage('lean', function(hljs) {
          return {
              keywords: 'def theorem axiomatic structure lemma informal_definition_note informal_lemma_note',
              contains: [
                  hljs.COMMENT('--', '$'),
                  hljs.C_NUMBER_MODE,
                  // Operators (custom definition)
                {
                    className: 'operator', // Define a class for styling
                    begin: /[:=+\\-*/<>|&!~^{}]/ // Regex for operators
                }

              ]
          };
      });
      hljs.highlightAll();
      </script>
"

def informalDefStyle : String :=
"
<style>
        .informal-def {
            position: relative; /* Establish a relative positioning context for the button */
            background-color: #f8d7da; /* Light red background */
            border: 2px solid #dc3545; /* Solid darker red border */
            margin: 10px; /* Space outside the block */
            padding: 20px; /* Space inside the block */
        }

        .informal-def .button {
            position: absolute; /* Position relative to the parent */
            top: 5px; /* Distance from the top of the block */
            right: 5px; /* Distance from the right of the block */
            background-color: rgba(220, 53, 69, 0.4);
            color: white; /* White text */
            border: none; /* No border for the button */
            padding: 5px 10px; /* Padding for the button */
            text-decoration: none; /* Remove underline from the link */
            border-radius: 5px; /* Rounded corners for the button */
            font-size: 12px; /* Smaller font size */
            cursor: pointer; /* Pointer cursor on hover */
        }

        .informal-def .button:hover {
            background-color: #0056b3; /* Darker blue on hover */
        }
    body {
            color: #000000; /* Change the default text color to dark gray */
        }
</style>
"

def headerHTML : String  :=
"---
layout: default
---
<!DOCTYPE html>
<html>
<head>" ++ codeBlockHTML ++ informalDefStyle ++ "</head>
</head>
<body>"

def titleHTML : String :=
"<center><h1 style=\"font-size: 50px;\">" ++ N.title ++ "</h1></center>
<center><b>Authors:</b> " ++ String.intercalate ", " N.authors ++ "</center>
<center><b>Abstract:</b> " ++ N.abstract ++ "</center>"

def footerHTML : String :=
"</body>
</html>"

unsafe def toHTMLString : MetaM String := do
  let string := String.intercalate "\n" ((← N.getNodeInfo).map (fun x => x.content))
  pure (headerHTML ++ N.titleHTML ++  string ++ footerHTML)

end NoteFile
end HepLean
