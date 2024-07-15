/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import Batteries.Lean.HashSet
import Lean
import Mathlib.Lean.Expr.Basic
import Mathlib.Lean.CoreM
import HepLean
/-!

# HepLean Stats

This file concerns with statistics of HepLean.

-/

open Lean System Meta

structure FileStats where
  numDefs : Nat
  numLemsWithoutDocString : Nat
  numLemsWithDocString : Nat

def FileStats.add (a b : FileStats) : FileStats where
  numDefs := a.numDefs + b.numDefs
  numLemsWithoutDocString := a.numLemsWithoutDocString + b.numLemsWithoutDocString
  numLemsWithDocString := a.numLemsWithDocString + b.numLemsWithDocString

def FileStats.zero : FileStats where
  numDefs := 0
  numLemsWithoutDocString := 0
  numLemsWithDocString := 0

instance : ToString FileStats where
  toString fs := s!"Number of definitions: {fs.numDefs}\n" ++
    s!"Number of lemmas without doc string: {fs.numLemsWithoutDocString}\n" ++
    s!"Number of lemmas with doc string: {fs.numLemsWithDocString}"

def getConstantDoc (constName : Array ConstantInfo) : MetaM (FileStats) := do
  let env ← getEnv
  let mut numDefs := 0
  let mut numLemsWithoutDocString := 0
  let mut numLemsWithDocString := 0
  for c in constName do
    if ¬ Lean.Name.isInternalDetail c.name then
      if c.isDef then
        numDefs := numDefs + 1
      if c.isThm then
        let doc ← Lean.findDocString? env c.name
        if doc == none then
          numLemsWithoutDocString := numLemsWithoutDocString + 1
        else
          numLemsWithDocString := numLemsWithDocString + 1
  return {numDefs := numDefs,
          numLemsWithoutDocString := numLemsWithoutDocString,
          numLemsWithDocString := numLemsWithDocString}

def getStats (imp : Import) : MetaM FileStats := do
  if imp.module == `Init then
    return {numDefs := 0,
            numLemsWithoutDocString := 0,
            numLemsWithDocString := 0}
  let mFile ← findOLean imp.module
  let (modData, _) ← readModuleData mFile
  let cons := modData.constants
  let out ← (getConstantDoc cons)
  return out

def getStatsArray (a : Array Import) : MetaM (Array FileStats) := do
  return ← a.mapM getStats

def main (_ : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let mods : Name :=  `HepLean
  let imp :  Import := {module := mods}
  let mFile ← findOLean imp.module
  unless (← mFile.pathExists) do
        throw <| IO.userError s!"object file '{mFile}' of module {imp.module} does not exist"
  let (hepLeanMod, _) ← readModuleData mFile
  let noFiles := hepLeanMod.imports.size - 1
  let fileStats ← CoreM.withImportModules #[`HepLean] (getStatsArray hepLeanMod.imports).run'
  let totalStats := Array.foldl FileStats.add FileStats.zero fileStats
  IO.println s!"Total number of files: {noFiles}"
  IO.println totalStats
  pure 0
