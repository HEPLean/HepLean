import Lean

open Lean Elab System

structure InformalDefinition where
  name : Name
  math_t : String
  physics_t : String

structure InformalLemma where
  name : Name
  math_t : String
  physics_t : String

namespace InformalDefinition

declare_syntax_cat assignment

syntax (name := physics_assignment) "physics := " str : assignment
syntax (name := math_assignment) "math := " str : assignment

syntax (name := informal_definition) "informal_definition " ident " where " (colGt assignment)* : command


macro "informal_definition " name:ident " where " assignments:assignment* : command => do
  let mut math_def? : Option (TSyntax `term) := none
  let mut physics_def? : Option (TSyntax `term) := none
  for assignment in assignments do
    match assignment with
    | `(assignment| physics := $val:str) =>
      let some strVal := val.raw.isStrLit? | Macro.throwError "Expected string literal for physics"
      physics_def? := some (← `($(Lean.quote strVal)))
    | `(assignment| math := $val:str) =>
      let some strVal := val.raw.isStrLit? | Macro.throwError "Expected string literal for math"
      math_def? := some (← `($(Lean.quote strVal)))
    | _ => Macro.throwError "invalid assignment syntax"

  unless physics_def?.isSome && math_def?.isSome do
    Macro.throwError "Both 'physics' and 'math' assignments are required"

  `(
    def $name : InformalDefinition := {
      name := $(Lean.quote name.getId),
      physics_t := $(physics_def?.getD (panic! "physics not assigned")),
      math_t := $(math_def?.getD (panic! "math not assigned"))
    }
  )

syntax (name := informal_lemma) "informal_lemma " ident " where " (colGt assignment)* : command

macro "informal_lemma " name:ident " where " assignments:assignment* : command => do
  let mut math_def? : Option (TSyntax `term) := none
  let mut physics_def? : Option (TSyntax `term) := none
  for assignment in assignments do
    match assignment with
    | `(assignment| physics := $val:str) =>
      let some strVal := val.raw.isStrLit? | Macro.throwError "Expected string literal for physics"
      physics_def? := some (← `($(Lean.quote strVal)))
    | `(assignment| math := $val:str) =>
      let some strVal := val.raw.isStrLit? | Macro.throwError "Expected string literal for math"
      math_def? := some (← `($(Lean.quote strVal)))
    | _ => Macro.throwError "invalid assignment syntax"

  unless physics_def?.isSome && math_def?.isSome do
    Macro.throwError "Both 'physics' and 'math' assignments are required"

  `(
    def $name : InformalDefinition := {
      name := $(Lean.quote name.getId),
      physics_t := $(physics_def?.getD (panic! "physics not assigned")),
      math_t := $(math_def?.getD (panic! "math not assigned"))
    }
  )

end InformalDefinition
