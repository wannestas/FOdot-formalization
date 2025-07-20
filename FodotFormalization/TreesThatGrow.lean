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

  -- Example of no extension at all
  def PlainExtensions : Extensions :=
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

  def TypedExtensions : Extensions :=
  { XLiteral := TypeInfo
  , XVariable := TypeInfo
  , XLambdaArrow := TypeInfo
  , XApplication := TypeInfo
  , XOther := Empty
  }

  abbrev TypedExp := ExpX (exts := TypedExtensions)

  def exampleTyped: TypedExp := Application (WellTyped) (LambdaArrow (WellTyped) "x" (Variable (BadlyTyped) "x")) (Literal (Number 5) 5)

  -- Example of adding new kinds of expressions, with a different set of extensions for pre-existing expressions
  inductive Builtin where
  | ReadLine
  | Print
  | Random

  inductive Error where
  | SyntaxError (errorStart errorEnd : ℕ) (name : String)

  def BuiltinResolvedExtensions (defaultExt : Extensions) : Extensions :=
  { XLiteral := defaultExt.XLiteral
  , XVariable := defaultExt.XVariable
  , XLambdaArrow := defaultExt.XLambdaArrow
  , XApplication := defaultExt.XApplication
  , XOther := Builtin ⊕ Error
  }

  -- Coercion so we don't need to do the stupid `Sum.inl` every time we want to construct a Builtin or Other node
  instance : Coe Builtin ((BuiltinResolvedExtensions TypedExtensions).XOther) where
    coe := Sum.inl

  instance : Coe Error ((BuiltinResolvedExtensions TypedExtensions).XOther) where
    coe := Sum.inr

  abbrev BuiltinExp := ExpX (exts := BuiltinResolvedExtensions TypedExtensions)

  def exampleBuiltin: BuiltinExp := Application (WellTyped) (LambdaArrow (WellTyped) "x" (Variable (BadlyTyped) "x")) (Error.SyntaxError 1 4 "gaming")

end Extensible
