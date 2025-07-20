import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Fin
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.FinCases

-- open Lean Elab Tactic

structure Context where
  Domain: Type
  DomainFin: Fintype Domain
  DomainDecEq : DecidableEq Domain
  PropVars: Type

inductive Formula {ctx: Context} where
  | Top
  | Var (n: ctx.PropVars)
  | Not (φ: Formula (ctx := ctx))
  | And (φ₁ φ₂: Formula (ctx := ctx))
  | Dia (φ: Formula (ctx := ctx))

inductive LanguageExtension where
  | ID
  | Types
deriving DecidableEq

instance : Fintype LanguageExtension where
  elems := {LanguageExtension.ID, LanguageExtension.Types}
  complete := by
    intro x
    cases x
    · simp
    · simp


-- inductive ParametrizedFormula {ctx: Context} {exts: Finset LanguageExtension}
--   | Top
--   | Var (n: ctx.PropVars)
--   | Not (φ: ParametrizedFormula (ctx := ctx) (exts := exts))
--   | And (φ₁ φ₂: ParametrizedFormula (ctx := ctx) (exts := exts) )
--   | UntypedQuantification
--       (proof : autoParam (LanguageExtension.Types ∉ exts) (by decide))
--       (φ : ParametrizedFormula)
--       : ParametrizedFormula
--   | TypedQuantification (φ : ParametrizedFormula (ctx := ctx) (exts := exts)) [proof : LanguageExtension.Types ∈ exts]

def Formula.Box {ctx: Context} (φ: Formula (ctx := ctx)) : Formula (ctx := ctx) :=
  Formula.Not <| Formula.Dia <| Formula.Not φ

def Formula.Or {ctx: Context} (φ₁ φ₂: Formula (ctx := ctx)) : Formula (ctx := ctx) :=
  Formula.Not <| Formula.And (Formula.Not φ₁) (Formula.Not φ₂)

def Formula.Imp {ctx: Context} (φ₁ φ₂: Formula (ctx := ctx)) : Formula (ctx := ctx) :=
  Formula.Or (Formula.Not φ₁) φ₂

structure Model where
  ctx: Context
  relation: ctx.Domain × ctx.Domain → Prop
  relationDec: DecidablePred relation
  valuation: ctx.PropVars → Finset ctx.Domain

def satisfies (M: Model) (w: M.ctx.Domain) : Formula (ctx := M.ctx) → Prop
  | Formula.Top       => True
  | Formula.Var n     => w ∈ (M.valuation n)
  | Formula.Not φ     => ¬ (satisfies M w φ)
  | Formula.And φ₁ φ₂ => (satisfies M w φ₁) ∧ (satisfies M w φ₂)
  | Formula.Dia φ     => ∃ v : M.ctx.Domain, M.relation (w, v) ∧ satisfies M v φ

def satisfiesDecidable {M: Model} {w: M.ctx.Domain} (φ: Formula): Decidable (satisfies M w φ) := by
  cases φ
  case Top => exact Decidable.isTrue True.intro
  case Var n => exact Finset.decidableMem (_h := M.ctx.DomainDecEq) w (M.valuation n)
  case Not φ =>
    unfold satisfies
    suffices Decidable (satisfies M w φ) from instDecidableNot
    have h := satisfiesDecidable (M := M) (w := w) φ
    unfold DecidablePred at h
    exact h
  case And φ₁ φ₂ =>
    unfold satisfies
    have h₁ := satisfiesDecidable (M := M) (w := w) φ₁
    have h₂ := satisfiesDecidable (M := M) (w := w) φ₂
    exact instDecidableAnd
  case Dia φ =>
    unfold satisfies
    let prop := λ v ↦ M.relation (w, v) ∧ satisfies M v φ
    have p : DecidablePred prop := by
      unfold DecidablePred
      intro v
      have hₗ : Decidable (M.relation (w, v)) := M.relationDec (w, v)
      have hᵣ : Decidable (satisfies M v φ) := satisfiesDecidable φ
      exact instDecidableAnd
    exact M.ctx.DomainFin.decidableExistsFintype

instance {M: Model} {w: M.ctx.Domain} (φ: Formula) : Decidable (satisfies M w φ) := by
  exact satisfiesDecidable φ

instance {M: Model} {w: M.ctx.Domain} : DecidablePred (satisfies M w) := by
  unfold DecidablePred
  intro a
  exact satisfiesDecidable a

namespace Example

def Ctx := Context.mk (Fin 4) (Fin.fintype 4) (instDecidableEqFin 4) Unit
def p : Formula (ctx := Ctx) := Formula.Var ()

def Rel: Ctx.Domain × Ctx.Domain → Bool := λ (a, b) ↦ match (a.val, b.val) with
  | (0, 2) | (0, 3) | (1, 0) | (3, 1) | (3, 3) => true
  | _ => false

def Val : Ctx.PropVars → Finset Ctx.Domain := λ n ↦ Finset.attachFin {0, 1} (by trivial)

def M := Model.mk Ctx (λ φ => Rel φ) (by infer_instance) Val

def Deci := satisfiesDecidable (M := M) (w := (Fin.ofNat 4 1)) p

#eval satisfies M (Fin.ofNat 4 0) (Formula.Dia <| Formula.Box <| Formula.Dia p)
#eval satisfies M (Fin.ofNat 4 1) (Formula.Dia <| Formula.Box <| Formula.Dia p)
#eval satisfies M (Fin.ofNat 4 2) (Formula.Dia <| Formula.Box <| Formula.Dia p)

end Example

namespace ParamExample

-- open ParametrizedFormula
-- def Ctx := Context.mk (Fin 4) (Fin.fintype 4) (instDecidableEqFin 4) Unit
-- def exts: Finset LanguageExtension := { LanguageExtension.Types }
-- -- Default falue is set in inductive but can't figure out how to not pass it
-- def p : ParametrizedFormula (ctx := Ctx) (exts := exts) := UntypedQuantification Top
-- def q : ParametrizedFormula (ctx := Ctx) (exts := exts) := TypedQuantification Top
-- #check UntypedQuantification

end ParamExample
