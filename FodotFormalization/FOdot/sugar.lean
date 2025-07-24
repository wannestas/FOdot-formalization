import FodotFormalization.FOdot.Extensional
import FodotFormalization.FOdot.FO

namespace FOsugar
  open Extensional

  abbrev FOSugarVoc (base : VocabularyExtensions) : VocabularyExtensions := base

  inductive SugarFormulas {vocExts : VocabularyExtensions} (voc : Vocabulary vocExts) (exts: Extensions vocExts) where
  | Or (φ₁ φ₂ : FormulaX voc exts)

  abbrev FOSugar {baseVoc : VocabularyExtensions} (base : Extensions baseVoc): Extensions (FOSugarVoc baseVoc) :=
  { TermExtensions := base.TermExtensions
  , FormulaExtensions := {base.FormulaExtensions with
        XOtherFormula := λ voc => ((SugarFormulas voc base) ⊕ base.FormulaExtensions.XOtherFormula voc)
      }
  }

end FOsugar
