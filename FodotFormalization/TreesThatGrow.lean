import Mathlib.Data.Real.Basic

def hello := "world"

namespace NonExtensible

  inductive Exp where
  | Literal (n : ℕ)
  | Variable (name : String)
  | LambdaArrow (name : String) (exp : Exp)
  | Application (exp₁ exp₂ : Exp)

  open Exp
  def exmp := Application (LambdaArrow "x" (Variable "x")) (Literal 5)


end NonExtensible

namespace Extensible

  -- Structure to store associated extension type for each Expression
  structure Extensions where
    XLiteral      : Type
    XVariable     : Type
    XLambdaArrow  : Type
    XApplication  : Type
    XOther        : Type

  -- Essentially the same as Exp, except each constructor takes a field of the associated
  -- type given by the Extensions record
  inductive ExpX {exts : Extensions} where
  | Literal (ext: exts.XLiteral) (n : ℕ)
  | Variable (ext: exts.XVariable) (name : String)
  | LambdaArrow (ext: exts.XLambdaArrow) (name : String) (exp : ExpX (exts := exts))
  | Application (ext: exts.XApplication) (exp₁ exp₂ : ExpX (exts := exts))
  | Other (ext : exts.XOther)

  open ExpX

  instance (exts : Extensions) : Coe exts.XOther (ExpX (exts := exts)) where
    coe := Other

  instance {α: Type} {β}: Coe α (α ⊕ β) where
    coe := Sum.inl

  instance {α: Type} {β: Type}: Coe β (α ⊕ β) where
    coe := Sum.inr

  instance {α: Type}: Coe α (Unit × α) where
    coe := (Prod.mk () ·)

  instance {α β: Type}: Coe (β × α) (α × β) where
    coe := Prod.swap


  -- Example of no extension at all
  abbrev PlainExtensions : Extensions :=
  { XLiteral := Unit
  , XVariable := Unit
  , XLambdaArrow := Unit
  , XApplication := Unit
  , XOther := Empty
  }
  abbrev PlainExp := ExpX (exts := PlainExtensions)

  def examplePlain: PlainExp := Application () (LambdaArrow () "x" (Variable () "x")) (Literal () 5)

  -- Silly TypeInfo type purely for demonstration purposes
  inductive TypeInfo where
  | WellTyped
  | BadlyTyped
  | Number (n : ℕ)
  open TypeInfo

  abbrev TypedExtensions (base: Extensions): Extensions :=
  { XLiteral := TypeInfo × base.XLiteral
  , XVariable := TypeInfo × base.XVariable
  , XLambdaArrow := TypeInfo × base.XLambdaArrow
  , XApplication := TypeInfo × base.XApplication
  , XOther := base.XOther
  }

  abbrev TypedExp := ExpX (exts := TypedExtensions PlainExtensions)

  def exampleTyped: TypedExp := Application (WellTyped) (LambdaArrow (WellTyped) "x" (Variable (BadlyTyped) "x")) (Literal (Number 5) 5)

  -- Example of adding new kinds of expressions, with a different set of extensions for pre-existing expressions
  inductive Builtin where
  | ReadLine
  | Print
  | Random

  inductive Error where
  | SyntaxError (errorStart errorEnd : ℕ) (name : String)

  abbrev BuiltinResolvedExtensions (defaultExt : Extensions) : Extensions :=
  { XLiteral := defaultExt.XLiteral
  , XVariable := defaultExt.XVariable
  , XLambdaArrow := defaultExt.XLambdaArrow
  , XApplication := defaultExt.XApplication
  , XOther := defaultExt.XOther ⊕ Builtin ⊕ Error
  }

  abbrev BuiltinExp := ExpX (exts := BuiltinResolvedExtensions (TypedExtensions PlainExtensions))

  def exampleBuiltin: BuiltinExp := Application (WellTyped) (LambdaArrow (WellTyped) "x" (Variable (BadlyTyped) "x")) (Error.SyntaxError 1 4 "gaming")

end Extensible
