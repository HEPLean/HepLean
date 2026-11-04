/-
Copyright (c) 2026 Andrea Pari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrea Pari
-/
module

public import Physlib.Mathematics.Tensors.Metric
/-!

# Index notation

Tensor expressions with named indices, such as `{T | μ ν ⊗ U | ν ρ}ᵀ` for `T^μ_ν U^ν_ρ`.

## i. Overview

Take the species `S` of real Lorentz tensors in `3 + 1` dimensions. An upper index has the color
`⟨vec, up⟩`, whose space `S.V ⟨vec, up⟩ = ℝ⁴` holds the vectors `v^μ`, and a lower index has the
color `⟨vec, down⟩`.
A tensor `T` with colors `![⟨vec, up⟩, ⟨vec, down⟩]` has the components `T^μ_ν`. In index notation
it is written `T | μ ν`, with one name per slot. The heights of the indices are not written, since
the colors of `T` fix them.

An expression `{…}ᵀ` is a tensor, an element of `S.Tensor ![…]`, or a proposition if it is an
equation. For a second tensor `U` with the same colors as `T`, `{T | μ ν ⊗ U | ν ρ}ᵀ` is the tensor
`T^μ_ν U^ν_ρ`, with colors `![⟨vec, up⟩, ⟨vec, down⟩]`. For an upper color `c`, the forms
`S.formTensor c = g^μν` and `S.formTensor c.dual = g_μν` are inverse, `g^μν g_νρ = δ^μ_ρ`:

  `{S.formTensor c | μ ν ⊗ S.formTensor c.dual | ν ρ = S.deltaTensor c.dual | μ ρ}ᵀ`.

This is `contr_formTensor_formTensor`, whose relabeling `ColorEquiv.matMul` agrees slot by slot with
the one the notation generates (section C).

The names are bound only inside the braces. The notation elaborates to the operations of a species.

- `A ⊗ B` is the product `S.tmulEquiv _ _ (A ⊗ₜ B)`.
- In a product, every name written twice is contracted, all pairs in one `Tensor.contr σ`. The
  relabeling `σ` is generated from the names, and its color proof checks that the two slots of
  each pair have dual colors. The first occurrence of a name is the first argument of `S.contr`.
- The remaining slots are numbered `0, 1, …` in the order written, so the result is a tensor on
  `Fin m` with a literal list of colors `![…]`.
- `A + B` and `A = B` relabel `B` by `S.reindex` when its names come in another order. Each name
  must have the same color on both sides.
- `T | ↓μ` lowers the upper index at that slot and `T | ↑μ` raises a lower one, by `S.toDualAt`.
  For a vector `v`, `{v | ↓ν}ᵀ` is `v_ν = v^μ g_μν`. This needs an instance `S.WithInvariantForm`.
  The arrow is checked against the color of the slot, so its variance must be visible, as in
  `⟨κ, .up⟩` for a kind `κ`.
- A scalar `r : k`, a group element `Λ : G` and negation are ordinary terms in front of `|`, as in
  `r • T | μ ν`, `Λ • T | μ ν` and `-T | μ ν`. A compound expression is scaled by nesting it,
  `r • {T | μ ν ⊗ U | ν ρ}ᵀ | μ ρ`.

An expression in parentheses, each side of a sum, and a nested `{…}ᵀ` are contracted first, before
they enter an enclosing product. The names they contract are free again outside:
`{(T | μ μ) ⊗ U | μ ρ}ᵀ` is `(T^λ_λ) U^μ_ρ`, and `{(T | μ μ + U | μ μ) ⊗ T | μ ν}ᵀ` is
`(T^λ_λ + U^λ_λ) T^μ_ν`. Within one product chain a name may appear at most twice.

The slots of each tensor must be labeled by a type built from `Fin n` and `⊕` with a literal `n`.
Its colors must be a literal list `![a, b, …]` or `prodColors` of such lists. A tensor with a
variable family of colors cannot be written, so general lemmas are stated without the notation.
A tensor with no slots is written `s |` with a space after the bar, since Mathlib reads `|`
followed directly by a term as an absolute value `|x|`. An equation with such a tensor can also be
written outside the braces, `{T | μ μ}ᵀ = s`.

## ii. Key results

- `{…}ᵀ` : index notation, elaborated by `elabTensorIndex`.

## iii. Table of contents

- A. Syntax
- B. Elaboration
  - B.1. Slot types
  - B.2. The steps of an expression
  - B.3. The elaborator
- C. Examples

## iv. References

-/

public meta section

open Lean Meta Elab Term

namespace Tensors.Notation

/-!

## A. Syntax

-/

/-- An index of a tensor in index notation. -/
declare_syntax_cat tensorIndex
/-- A named index. -/
syntax ident : tensorIndex
/-- A named upper index lowered with the invariant form, as `v_μ` from `v^μ`. -/
syntax "↓" ident : tensorIndex
/-- A named lower index raised with the invariant form, as `α^μ` from `α_μ`. -/
syntax "↑" ident : tensorIndex

/-- A tensor expression in index notation. -/
declare_syntax_cat tensorIndexExpr
/-- A tensor with a name on each slot. -/
syntax term "|" (ppSpace tensorIndex)* : tensorIndexExpr
/-- An equation. -/
syntax:40 tensorIndexExpr "=" tensorIndexExpr:41 : tensorIndexExpr
/-- A product. -/
syntax:70 tensorIndexExpr "⊗" tensorIndexExpr:71 : tensorIndexExpr
/-- A sum. -/
syntax:65 tensorIndexExpr "+" tensorIndexExpr:66 : tensorIndexExpr
/-- Parentheses. -/
syntax "(" tensorIndexExpr ")" : tensorIndexExpr

/-- Index notation. -/
syntax (name := tensorIndexSyntax) "{" tensorIndexExpr "}ᵀ" : term

/-!

## B. Elaboration

### B.1. Slot types

-/

/-- A slot type built from `Fin n`, `Unit` and `⊕`. -/
inductive Slots where
  /-- `Fin n`. -/
  | fin (n : Nat)
  /-- `Unit`. -/
  | unit
  /-- `a ⊕ b`. -/
  | sum (a b : Slots)
deriving BEq

/-- A slot of a slot type: the path of `Sum.inl` (`false`) and `Sum.inr` (`true`) to a leaf, and
the position in that leaf. -/
abbrev Addr := List Bool × Nat

/-- The slots of a slot type, in order. -/
def Slots.addrs : Slots → List Addr
  | .fin n => (List.range n).map (([], ·))
  | .unit => [([], 0)]
  | .sum a b => a.addrs.map (fun (p, i) => (false :: p, i)) ++
      b.addrs.map (fun (p, i) => (true :: p, i))

/-- The slot type as a term. -/
def Slots.type : Slots → TermElabM Term
  | .fin n => `(Fin $(quote n))
  | .unit => `(Unit)
  | .sum a b => do `($(← a.type) ⊕ $(← b.type))

/-- A slot as a term. -/
def Slots.elem : Slots → Addr → TermElabM Term
  | .fin n, (_, i) => `(($(quote i) : Fin $(quote n)))
  | .unit, _ => `(())
  | .sum a _, (false :: p, i) => do `(Sum.inl $(← a.elem (p, i)))
  | .sum _ b, (true :: p, i) => do `(Sum.inr $(← b.elem (p, i)))
  | .sum _ _, ([], _) => throwError "index notation: bad slot"

/-- The function on a slot type with the values `img`, as vector literals on `Fin n`, constants on
`Unit`, and `comb` on `⊕`. -/
def Slots.fn (comb : Name) (img : Addr → TermElabM Term) : Slots → TermElabM Term
  | .fin n => do `(![$((← (List.range n).mapM fun i => img ([], i)).toArray),*])
  | .unit => do `(fun _ : Unit => $(← img ([], 0)))
  | .sum a b => do
    `($(mkIdent comb) $(← a.fn comb fun (p, i) => img (false :: p, i))
      $(← b.fn comb fun (p, i) => img (true :: p, i)))

/-- The slot type of a type built from `Fin n` and `⊕` with a literal `n`. -/
partial def Slots.ofType? (ι : Expr) : MetaM (Option Slots) := do
  let ι ← whnfR ι
  if ι.isAppOfArity ``Fin 1 then
    return (← (evalNat ι.appArg!).run).map .fin
  else if ι.isAppOfArity ``Sum 2 then
    let some a ← Slots.ofType? (ι.getArg! 0) | return none
    let some b ← Slots.ofType? (ι.getArg! 1) | return none
    return some (.sum a b)
  else return none

/-- The bijection from `dom` to `cod` sending the `i`-th slot of `dom` to `img[i]`, with its
inverse laws checked slot by slot by `fin_cases`. `decide` would need a `DecidableEq` instance on
the whole slot type, which exceeds the instance size limit from four contracted pairs on. -/
def slotEquiv (dom cod : Slots) (img : List Addr) : TermElabM Term := do
  let table := dom.addrs.zip img
  let toFun ← dom.fn ``Sum.elim fun x => match table.find? (·.1 == x) with
    | some (_, y) => cod.elem y
    | none => throwError "index notation: a slot has no image"
  let invFun ← cod.fn ``Sum.elim fun y => match table.find? (·.2 == y) with
    | some (x, _) => dom.elem x
    | none => throwError "index notation: a slot has no preimage"
  `(({ toFun := $toFun, invFun := $invFun,
       left_inv := (by intro x; fin_cases x <;> rfl),
       right_inv := (by intro x; fin_cases x <;> rfl) } :
      $(← dom.type) ≃ $(← cod.type)))

/-- The entries of a literal color family `![a, b, …]`, or of `prodColors` of literal families. -/
partial def colorList? (c : Expr) : MetaM (Option (List Expr)) := do
  if c.isAppOfArity ``Tensors.prodColors 5 then
    return (· ++ ·) <$> (← colorList? (c.getArg! 3)) <*> (← colorList? (c.getArg! 4))
  let (cs, _, tail) ← Matrix.matchVecConsPrefix (mkNatLit 0) c
  return if tail.isAppOfArity ``Matrix.vecEmpty 1 then some cs else none

/-- The literal color family `![a, b, …]`. -/
def colorsTerm (cs : List Expr) : TermElabM Term := do
  `(![$((← cs.toArray.mapM exprToSyntax)),*])

/-!

### B.2. The steps of an expression

-/

/-- A partly elaborated expression: the name and color of each slot, the slot type, the tensor
and its species. -/
structure Node where
  /-- The index name of each slot. -/
  names : List Name
  /-- The color of each slot. -/
  colors : List Expr
  /-- The slot type. -/
  slots : Slots
  /-- The tensor. -/
  tm : Term
  /-- The species. -/
  species : Expr

/-- The expression relabeled to `Fin n`, its slots numbered in order. -/
def Node.toFin (a : Node) : TermElabM Node := do
  let n := a.names.length
  if a.slots == .fin n then return a
  let σ ← slotEquiv a.slots (.fin n) ((List.range n).map ([], ·))
  let tm ← `(Tensors.Species.reindex $(← exprToSyntax a.species)
    (Tensors.ColorEquiv.mk (c₂ := $(← colorsTerm a.colors)) $σ) $a.tm)
  return { a with slots := .fin n, tm }

/-- The tensor `T | i₁ i₂ …` with its slots named, lowered at each `↓μ` and raised at each `↑μ`. -/
def leaf (T : Term) (idxs : Array (TSyntax `tensorIndex)) : TermElabM Node := do
  let e ← instantiateMVars (← elabTerm T none)
  if e.hasSyntheticSorry then throwAbortTerm
  let ty ← whnfR (← instantiateMVars (← inferType e))
  unless ty.isAppOf ``Tensors.Species.Tensor do
    throwError "index notation: {T} is not a tensor"
  let args := ty.getAppArgs
  let some slots ← Slots.ofType? args[args.size - 2]!
    | throwError "index notation: the slots of {T} must be `Fin n` and `⊕`"
  let some colors ← colorList? args[args.size - 1]!
    | throwError "index notation: the colors of {T} must be a literal list"
  unless colors.length = idxs.size do
    throwError "index notation: {T} has {colors.length} slots, {idxs.size} indices given"
  -- Each index with whether its slot moves to the dual color, after checking the arrow.
  let kinds ← (idxs.toList.zip colors).mapM fun (i, col) => do
    let isUp ← whnfD (← mkAppM ``Tensors.Variance.isUp #[← mkAppM ``Tensors.Color.variance #[col]])
    let check (x : Ident) (up : Bool) (arrow : String) : TermElabM (Name × Bool) := do
      unless isUp.isConstOf (if up then ``Bool.true else ``Bool.false) do
        throwError "index notation: {arrow}{x.getId} needs a visibly \
          {if up then "upper" else "lower"} index"
      pure (x.getId, true)
    match i with
    | `(tensorIndex| $x:ident) => pure (x.getId, false)
    | `(tensorIndex| ↓$x:ident) => check x true "↓"
    | `(tensorIndex| ↑$x:ident) => check x false "↑"
    | _ => throwError "index notation: unsupported index {i}"
  let mut a : Node := ⟨kinds.map (·.1), colors, slots, ← exprToSyntax e, args[args.size - 3]!⟩
  if kinds.all (!·.2) then return a
  a ← a.toFin
  let n := colors.length
  for ((_, d), i) in kinds.zipIdx do
    if d then
      let colors := a.colors.set i (← mkAppM ``Tensors.Color.dual #[a.colors[i]!])
      -- The proof at `i` is `id rfl`, of type `c' i = (c i).dual` as in the lemmas on `toDualAt`.
      -- A bare `rfl` has the type `c' i = c' i`, which `rw` matches only by unfolding `![…] i`.
      -- The new colors agree with the old ones away from `i`, by cases on the slot.
      let tm ← `(Tensors.Species.toDualAt $(← exprToSyntax a.species)
        (c' := $(← colorsTerm colors)) ($(quote i) : Fin $(quote n)) (id rfl)
        (by intro x hx; fin_cases x <;> first | rfl | exact absurd rfl hx) $a.tm)
      a := { a with colors, tm }
  return a

/-- Contracts every repeated name in one `Tensor.contr`, and numbers the remaining slots in the
order written. -/
def contract (a : Node) : TermElabM Node := do
  let idx := a.names.zipIdx
  let mut free : List Nat := []
  let mut pairs : List (Nat × Nat) := []
  for (nm, i) in idx do
    match idx.filter (·.1 == nm) with
    | [_] => free := free ++ [i]
    | [(_, i₁), (_, i₂)] =>
      if i == i₁ then
        unless ← isDefEq a.colors[i₂]! (← mkAppM ``Tensors.Color.dual #[a.colors[i₁]!]) do
          throwError "index notation: {nm} joins the colors {a.colors[i₁]!} and \
            {a.colors[i₂]!}, which are not dual"
        pairs := pairs ++ [(i₁, i₂)]
    | _ => throwError "index notation: {nm} appears more than twice"
  if pairs.isEmpty then return ← a.toFin
  let m := free.length
  -- The pairs are labeled by `Unit` for one pair, as in `ColorEquiv.matMul`, and by
  -- `(… ⊕ Unit) ⊕ Unit` for more, as `ColorEquiv.chain` combines two contractions in sequence.
  let J := (List.range (pairs.length - 1)).foldl (fun J _ => Slots.sum J .unit) .unit
  -- A remaining slot goes to `inl k`, the pair `j` to `inr (inl j)` and `inr (inr j)`.
  let img : List Addr := (List.range a.names.length).map fun i =>
    match free.idxOf? i, pairs.findIdx? (·.1 == i), pairs.findIdx? (·.2 == i) with
    | some k, _, _ => ([false], k)
    | _, some j, _ => (true :: false :: (J.addrs[j]!).1, 0)
    | _, _, some j => (true :: true :: (J.addrs[j]!).1, 0)
    | _, _, _ => ([], 0)
  let σ ← slotEquiv a.slots (.sum (.fin m) (.sum J J)) img
  let pairColors ← J.fn ``Tensors.prodColors fun (p, _) =>
    exprToSyntax a.colors[(pairs[J.addrs.idxOf (p, 0)]!).1]!
  let tm ← `(Tensors.Species.Tensor.contr (S := $(← exprToSyntax a.species))
    (Tensors.ColorEquiv.mk
      (c₂ := Tensors.contrColors $(← colorsTerm (free.map (a.colors[·]!))) $pairColors) $σ)
    $a.tm)
  return ⟨free.map (a.names[·]!), free.map (a.colors[·]!), .fin m, tm, a.species⟩

/-- The right side relabeled to the order of the left side's names, after checking that each name
has the same color on both sides. -/
def reorder (l r : Node) : TermElabM Term := do
  unless l.names.length == r.names.length && l.names.all (r.names.contains ·) do
    throwError "index notation: the two sides have different free indices"
  for (nm, c) in r.names.zip r.colors do
    let c' := l.colors[l.names.idxOf nm]!
    unless ← isDefEq c c' do
      throwError "index notation: {nm} has the color {c'} on the left and {c} on the right"
  if l.names == r.names then return r.tm
  let m := l.names.length
  let σ ← slotEquiv (.fin m) (.fin m) (r.names.map fun nm => ([], l.names.idxOf nm))
  `(Tensors.Species.reindex $(← exprToSyntax l.species)
    (Tensors.ColorEquiv.mk (c₂ := $(← colorsTerm l.colors)) $σ) $r.tm)

/-!

### B.3. The elaborator

-/

mutual

/-- An expression before its outer contraction. A product chain `A ⊗ B` is
`S.tmulEquiv _ _ (A ⊗ₜ B)` with its repeated names not yet contracted. An expression in
parentheses and each side of a sum are contracted first. -/
partial def uncontracted (stx : Syntax) : TermElabM Node := do
  match stx with
  | `(tensorIndexExpr| $T:term | $ids:tensorIndex*) => leaf T ids
  | `(tensorIndexExpr| $a:tensorIndexExpr ⊗ $b:tensorIndexExpr) => do
    let a ← uncontracted a
    let b ← uncontracted b
    let tm ← `(Tensors.Species.tmulEquiv $(← exprToSyntax a.species) _ _
      (TensorProduct.tmul _ $a.tm $b.tm))
    return ⟨a.names ++ b.names, a.colors ++ b.colors, .sum a.slots b.slots, tm, a.species⟩
  | `(tensorIndexExpr| ($a:tensorIndexExpr)) => build a
  | `(tensorIndexExpr| $a:tensorIndexExpr + $b:tensorIndexExpr) => do
    let l ← build a
    return { l with tm := ← `($l.tm + $(← reorder l (← build b))) }
  | `(tensorIndexExpr| $_:tensorIndexExpr = $_:tensorIndexExpr) =>
    throwError "index notation: an equation is allowed only at the top"
  | _ => throwError "index notation: unsupported expression {stx}"

/-- An expression, contracted. -/
partial def build (stx : Syntax) : TermElabM Node := do contract (← uncontracted stx)

end

/-- Elaborates index notation. An equation is allowed only at the top, possibly in parentheses. -/
@[term_elab tensorIndexSyntax] def elabTensorIndex : TermElab := fun stx expectedType? => do
  match stx with
  | `({ ($e:tensorIndexExpr) }ᵀ) => elabTerm (← `({ $e:tensorIndexExpr }ᵀ)) expectedType?
  | `({ $l:tensorIndexExpr = $r:tensorIndexExpr }ᵀ) =>
    let l ← build l
    elabTerm (← `($l.tm = $(← reorder l (← build r)))) none
  | `({ $e:tensorIndexExpr }ᵀ) => elabTerm (← build e).tm expectedType?
  | _ => throwUnsupportedSyntax

end Tensors.Notation

end

/-!

## C. Examples

-/

namespace Tensors.Notation

open Species

variable {k : Type} [CommRing k] {K : Type} {G : Type} [Group G] {basisIdx : K → Type}
    [∀ κ, Fintype (basisIdx κ)] [∀ κ, DecidableEq (basisIdx κ)] {S : Species k G K basisIdx}
    (a c : Color K) (T U W : S.Tensor ![a, a.dual]) (T' : S.Tensor ![a.dual, a])
    (κ : K) (v : S.Tensor ![⟨κ, .up⟩]) (r : k) (Λ : G)

/-- info: T : S.Tensor ![a, a.dual] -/
#guard_msgs in
#check {T | μ ν}ᵀ

/-- The matrix product `T^μ_ν U^ν_ρ`. -/
noncomputable example : S.Tensor ![a, a.dual] := {T | μ ν ⊗ U | ν ρ}ᵀ

/-- A product written as a term, with the colors `prodColors ![a, a.dual] ![a, a.dual]`, is the
product written in the notation. -/
example : {S.tmulEquiv _ _ (T ⊗ₜ U) | μ ν ν ρ = T | μ ν ⊗ U | ν ρ}ᵀ := rfl

/-- An equation with a tensor `s` with no slots, `T^μ_μ = s`. The space after the bar keeps
Mathlib's absolute value `|x|` from reading it. -/
example (s : S.Tensor (![] : Fin 0 → Color K)) : {T | μ μ = s | }ᵀ ↔ {T | μ μ}ᵀ = s := Iff.rfl

/-- An equation in parentheses is the same equation. -/
example : {(T | μ ν = U | μ ν)}ᵀ ↔ {T | μ ν = U | μ ν}ᵀ := Iff.rfl

/-- An equation whose right side lists its indices in the other order, `T^μ_ν = T'_ν^μ`. -/
example : Prop := {T | μ ν = T' | ν μ}ᵀ

/-- The trace of a product of four matrices, `T^μ_ν U^ν_ρ T^ρ_σ U^σ_μ`. -/
noncomputable example : S.Tensor (![] : Fin 0 → Color K) :=
  {T | μ ν ⊗ U | ν ρ ⊗ T | ρ σ ⊗ U | σ μ}ᵀ

/-- The trace of a product of five matrices, `T^μ_ν U^ν_ρ W^ρ_σ T^σ_τ U^τ_μ`. -/
noncomputable example : S.Tensor (![] : Fin 0 → Color K) :=
  {T | μ ν ⊗ U | ν ρ ⊗ W | ρ σ ⊗ T | σ τ ⊗ U | τ μ}ᵀ

/-- Sums, negatives and scalar multiples, `-T^μ_ν + r U^μ_ν`. -/
example : {-T | μ ν + r • U | μ ν}ᵀ = -T + r • U := rfl

/-- A scalar multiple of a contraction, `r T^μ_ν U^ν_ρ`. -/
example : {r • {T | μ ν ⊗ U | ν ρ}ᵀ | μ ρ}ᵀ = r • {T | μ ν ⊗ U | ν ρ}ᵀ := rfl

/-- Each side of a sum is contracted first, so `μ` is free again in the product,
`(T^λ_λ + U^λ_λ) T^μ_ν`. -/
example : {(T | μ μ + U | μ μ) ⊗ T | μ ν}ᵀ = {({T | μ μ}ᵀ + {U | μ μ}ᵀ) | ⊗ T | μ ν}ᵀ := rfl

-- The two sides of a sum or an equation must agree in the colors of each name.
/-- error: index notation: ν has the color a.dual on the left and a on the right -/
#guard_msgs in
#check {T | μ ν = T | ν μ}ᵀ

-- A term that is not a tensor is rejected.
/-- error: index notation: r is not a tensor -/
#guard_msgs in
#check {r | μ}ᵀ

/-- An expression in parentheses is contracted first, so `μ` is free again in the product,
`(T^λ_λ) U^μ_ρ`. -/
example : {(T | μ μ) ⊗ U | μ ρ}ᵀ = {{T | μ μ}ᵀ | ⊗ U | μ ρ}ᵀ := rfl

-- A name appearing three times in one product chain is rejected.
/-- error: index notation: μ appears more than twice -/
#guard_msgs in
#check {T | μ μ ⊗ U | μ ρ}ᵀ

-- A tensor whose colors are not a literal list is rejected.
/-- error: index notation: the colors of t must be a literal list -/
#guard_msgs in
example (f : Fin 2 → Color K) (t : S.Tensor f) : S.Tensor f := {t | μ ν}ᵀ

-- A pair of slots whose colors are not dual is rejected.
/-- error: index notation: μ joins the colors a and a, which are not dual -/
#guard_msgs in
#check {T | μ ν ⊗ T | μ ρ}ᵀ

/-- Contracting `ν` and then `ρ` is contracting both at once, `(T U)^μ_ρ W^ρ_τ = T^μ_ν U^ν_ρ W^ρ_τ`,
by `tmulEquiv_contr` and `contr_contr`. The two choices of pairs agree slot by slot. -/
example : {{T | μ ν ⊗ U | ν ρ}ᵀ | μ ρ ⊗ W | ρ τ = T | μ ν ⊗ U | ν ρ ⊗ W | ρ τ}ᵀ := by
  rw [Tensor.tmulEquiv_contr, Tensor.contr_contr]
  congr 2
  ext x
  fin_cases x <;> rfl

section Metric

variable [S.WithInvariantForm]

/-- Lowering and then raising an index gives the vector back, `(v_μ)^μ = v^μ`. -/
example : {{v | ↓μ}ᵀ | ↑μ}ᵀ = v := toDualAt_toDualAt _ _ _ _

-- An arrow that does not match the variance of the slot is rejected.
/-- error: index notation: ↑μ needs a visibly lower index -/
#guard_msgs in
#check {v | ↑μ}ᵀ

/-- Lowering commutes with the group action, `(Λ v)_μ = Λ (v_μ)`. The lemmas on `toDualAt` apply
by `rw` and `simp`. -/
example : {(Λ • v) | ↓μ}ᵀ = Λ • {v | ↓μ}ᵀ := by rw [toDualAt_smul]

/-- Lowering both indices commutes with the group action, `(Λ M)_μν = Λ (M_μν)`. -/
example (M : S.Tensor ![⟨κ, .up⟩, ⟨κ, .up⟩]) : {(Λ • M) | ↓μ ↓ν}ᵀ = Λ • {M | ↓μ ↓ν}ᵀ := by
  simp only [toDualAt_smul]

/-- A trace commutes with the group action, `(Λ T)^μ_μ = Λ (T^μ_μ)`, by `rw [Tensor.contr_smul]`. -/
example : {(Λ • T) | μ μ}ᵀ = Λ • {T | μ μ}ᵀ := by rw [Tensor.contr_smul]

/-- `g^μν g_νρ = δ^μ_ρ`, by `contr_formTensor_formTensor`. The notation generates the pairs of
`ColorEquiv.matMul` slot by slot. -/
example : {S.formTensor c | μ ν ⊗ S.formTensor c.dual | ν ρ = S.deltaTensor c.dual | μ ρ}ᵀ := by
  rw [← contr_formTensor_formTensor]
  congr 2
  ext x
  fin_cases x <;> rfl

end Metric

end Tensors.Notation
