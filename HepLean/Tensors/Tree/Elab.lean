/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Tensors.Tree.Basic
import Lean.Elab.Term
/-!

## Elaboration of tensor trees

This file turns

-/
open Lean
open Lean.Elab.Term

open Lean
open Lean.Meta
open Lean.Elab
open Lean.Elab.Term

declare_syntax_cat tensorExpr

syntax ident (ppSpace term)* : tensorExpr

syntax tensorExpr "⊗" tensorExpr : tensorExpr
